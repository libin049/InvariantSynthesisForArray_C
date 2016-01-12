#ifndef _AtomVariableAnalysis_H
#define _AtomVariableAnalysis_H
#include <vector>
#include "clang/AST/Expr.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/Analysis/CFG.h"
#include "z3++.h"
using namespace z3;

extern  bool occurError;

class AtomVariabla : public Property{
public:
	context &c;
	Z3Coding &z3coding;
	const clang::Stmt *indexInitStmt;
	vector<const clang::Stmt*>* indexUpdateStmts; //may be more than one updateStatement, however step is same
	expr scalaVarz3coding;
	expr stepz3coding;
	expr indexInitStmtz3coding;
	expr initz3coding;
	expr indexUpdateStmtz3coding;
	bool isIn(const clang::Stmt* s,vector<const clang::Stmt*>* vs){
		for(const clang::Stmt* ele:*vs){
			if(ele==s){
				return true;
			}
		}
		return false;
	}
	

	AtomVariabla(context &ctx,Z3Coding &coding, const clang::Stmt *indexInitStmt):c(ctx),z3coding(coding),scalaVarz3coding(c)
				,stepz3coding(c),indexInitStmtz3coding(c),initz3coding(c),indexUpdateStmtz3coding(c){
		this->indexInitStmt=indexInitStmt;
		indexUpdateStmts=new vector<const clang::Stmt*>();
		vector<expr> * tmp=z3coding.boolSortFiltering(z3coding.clangStmtToZ3Expr(indexInitStmt));
		indexInitStmtz3coding=tmp->front();
		scalaVarz3coding=z3coding.unprime(indexInitStmtz3coding.arg(0));
		initz3coding=indexInitStmtz3coding.arg(1);
		
	}
	bool hasStep(){
		if(indexUpdateStmts->size()==0){
			return false;
		}
		return true;
	}
	void addIndexUpdateStmt(const clang::Stmt* indexUpdateStmt){
		if(indexUpdateStmts->size()!=0){
			if(!isIn(indexUpdateStmt,indexUpdateStmts)){
				indexUpdateStmts->push_back(indexUpdateStmt);
			}
		}
		else{
			indexUpdateStmts->push_back(indexUpdateStmt);
			vector<expr> *tmp=z3coding.clangStmtToZ3Expr(indexUpdateStmt);
			tmp=z3coding.boolSortFiltering(tmp);
			this->indexUpdateStmtz3coding=tmp->at(0);
			stepz3coding=getStepFromIndexUpdate(indexUpdateStmtz3coding);
		}
	}
		expr getStepFromIndexUpdate(expr stmt){
			if(stmt.arg(1).decl().name().str()=="+"){
				return stmt.arg(1).arg(1);
			}
			else if(stmt.arg(1).decl().name().str()=="-"){
				return -stmt.arg(1).arg(1);
			}
			else{
				std::cerr<<"getStepFromIndexUpdate: something is wrong!"<<std::endl;
				return z3coding._error;
			}
		}
//	/**
//	 * @brief check weather stmt update step
//	 * @param stmt
//	 * @return 
//	 */
//	bool checkIndexUpdateStmt(const clang::Stmt* stmt){
//		if(isIn(stmt,indexUpdateStmts)){
//			return true;	
//		}
//		else{
//			
//		}
//	}
	bool checkScalaVaribale(expr scalaVaribale){
		return z3coding.equal(scalaVarz3coding,scalaVaribale);
	}
	bool checkUpdateStmt(expr updateStmt){
		expr scalaVar=z3coding.unprime(updateStmt.arg(0));
		if(checkScalaVaribale(scalaVar)){
			if(z3coding.morePower_equal(this->indexUpdateStmtz3coding,updateStmt)){
				return true;
			}
		}
		return false;
	}
	bool isStepEqual(const clang::Stmt *InitStmt){
		return indexInitStmt==InitStmt;
	}
	bool equal(Property *p){
		AtomVariabla * av=(AtomVariabla *)p;
		if(this->indexInitStmt!=av->indexInitStmt){
			return false;
		}
		if(hasStep()!=av->hasStep()){
			return false;
		}
		if(hasStep()){
			if(!z3coding.equal(this->stepz3coding,av->stepz3coding)){
				return false;
			}
		}
		return true;
	}
	std::string toString(){
		std::string ret="init Stmt: ";
		ret+=Z3_ast_to_string(c,indexInitStmtz3coding);
		if(hasStep()){
			std::string stepStr=Z3_ast_to_string(c,stepz3coding);
			ret+=", step: "+stepStr; 
		}
		return ret;
	}
	AtomVariabla* clone(){
		/*AtomVariabla* ret=new AtomVariabla(c,z3coding,indexInitStmt);
		for(const clang::Stmt* s: *this->indexUpdateStmts){
			ret->indexUpdateStmts->push_back(s);
		}
		ret->indexUpdateStmtz3coding=this->indexUpdateStmtz3coding;
		ret->stepz3coding=this->stepz3coding;
		return ret;*/
		return this;
	}
	
};

class AtomVariablaAnalysis: public IntraDataFlowAnalysis{
	ValueListSet universalSet;
	context &c;
	Z3Coding &z3coding;
public:
	map<const clang::Stmt*, FlowSet*> mapToStmtIn;
	map<const clang::Stmt*, FlowSet*> mapToStmtOut;
	
	void pre_init(){
		for(CFG::iterator it=cfg->begin();it!=cfg->end();++it){
			CFGBlock* n=*it;
			for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
				CFGElement element=(*iterblock);
				if(element.getKind()==CFGElement::Kind::Statement){
					const Stmt* it=((CFGStmt*)&element)->getStmt();
					mapToStmtIn.insert(std::pair<const clang::Stmt*, FlowSet*>(it,new ValueListSet()));
					mapToStmtOut.insert(std::pair<const clang::Stmt*, FlowSet*>(it,new ValueListSet()));
				}
			}
			if(n->succ_size()==2){
				Stmt* T=n->getTerminatorCondition();
				if(mapToStmtIn.count(T)<=0){
					mapToStmtIn.insert(std::pair<const clang::Stmt*, FlowSet*>(T,new ValueListSet()));
					mapToStmtOut.insert(std::pair<const clang::Stmt*, FlowSet*>(T,new ValueListSet()));
				}
			}
		}
	}
	AtomVariablaAnalysis(clang::CFG* cfg,context &ctx,Z3Coding &coding):IntraDataFlowAnalysis(cfg),c(ctx),z3coding(coding){
		pre_init();
		doAnalysis();
	}
	~AtomVariablaAnalysis(){}
	FlowSet * newinitialFlow(){
		return &universalSet; 
	}
	FlowSet * entryInitialFlow(){return new ValueListSet();}
	
	void merge(FlowSet  * &in1,FlowSet  *&in2,FlowSet  *&out){
		if(in1==&universalSet&&in2==&universalSet) {
		#ifdef _DEBUG
			std::cout<<"universalSet merge universalSet"<<std::endl;
		#endif
			out=&universalSet;
			return;
		}
		if(in1==&universalSet){
		#ifdef _DEBUG
			std::cout<<"universalSet merge "<<in2->toString()<<std::endl;
		#endif
			out=in2->clone();
			return;
		}
		if(in2==&universalSet) {
		#ifdef _DEBUG
			std::cout<<"universalSet merge "<<in1->toString()<<std::endl;
		#endif
			out=in1->clone();
			return;
		}
	#ifdef _DEBUG
		std::cout<<in1->toString()<<"--- merge---"<<in2->toString()<<std::endl;
	#endif
		out=new ValueListSet();
		ValueListSet* vlsIn1=(ValueListSet*)in1;
		ValueListSet* vlsIn2=(ValueListSet*)in2;
		for(Property * p1: vlsIn1->elements){
			for(Property * p2: vlsIn2->elements){
				AtomVariabla* r=meet((AtomVariabla*)p1,(AtomVariabla*)p2);
				if(r!=nullptr){
					out->add(r);
				}
			}
		}
		return;
	}
	AtomVariabla* meet(AtomVariabla* in1,AtomVariabla* in2){
		if(in1->indexInitStmt!=in2->indexInitStmt){
			return nullptr;
		}
		if(!in1->hasStep()){
			return in2->clone();
		}
		if(!in2->hasStep()){
			return in1->clone();
		}
		if(!z3coding.equal(in1->stepz3coding,in2->stepz3coding)){
			return nullptr;
		}
		else{
			return in1->clone();
		}
	}
	bool isAssigndToScaleVariable(expr stmt){
			if(stmt.is_app()){
				if(stmt.decl().name().str()=="="){
					expr lhs=stmt.arg(0);
					return z3coding.isPrimedVariable(lhs);
				}
			}
			return false;
	}
	bool isAtomInitStmt(expr stmt){
		if(isAssigndToScaleVariable(stmt)){
			expr scalaVar=z3coding.unprime(stmt.arg(0));
			if(!z3coding.isIn(scalaVar,z3coding.getConsts(stmt.arg(1)))){
				return true;
			}
			return false;
		}
		return false;
	}
	bool isAtomUpdateStmt(expr stmt){
		if(isAssigndToScaleVariable(stmt)){
			expr scalaVar=z3coding.unprime(stmt.arg(0));
			if(!z3coding.isIn(scalaVar,z3coding.getConsts(stmt.arg(1)))){
				return false;
			}
			return true;
		}
		return false;
	}
	FlowSet * GenAndKill(FlowSet * Pre,const Stmt* s){
		FlowSet * ret=new ValueListSet();
		vector<expr> * tmp=z3coding.clangStmtToZ3Expr(s);
		tmp=z3coding.boolSortFiltering(tmp);
		if(tmp->size()<=0){
			return ret;
		}
		expr z3Stmt=tmp->at(0);
		//kill
		ValueListSet* vlsPre=(ValueListSet*) Pre;
		if(isAssigndToScaleVariable(z3Stmt)){
			expr scalaVar=z3coding.unprime(z3Stmt.arg(0));
			for(Property *p:vlsPre->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				vector<expr>* initStmtConsts=z3coding.getConsts(z3coding.unprimedDecline((av->indexInitStmtz3coding)));
				vector<expr>* updateStmtConsts=new vector<expr>();
				if(av->hasStep()){
					updateStmtConsts=z3coding.getConsts(z3coding.unprimedDecline((av->indexUpdateStmtz3coding)));
				}
				if(z3coding.isIn(scalaVar,initStmtConsts)||z3coding.isIn(scalaVar,updateStmtConsts)){
					//kill p
					//do nothing
				}
				else{
					ret->add(av->clone());
				}
			}
		}
		else{
			ret=Pre->clone();
		}
		
		//gen
		if(isAssigndToScaleVariable(z3Stmt)){
			expr scalaVar=z3coding.unprime(z3Stmt.arg(0));
			if(isAtomInitStmt(z3Stmt)){
				AtomVariabla* av=new AtomVariabla(c,z3coding,s);
			#ifdef _DEBUG	
				std::cout<<"gen: "<< av->toString()<<std::endl;
			#endif
				ret->add(av);
			}
			else if(isAtomUpdateStmt(z3Stmt)){
				for(Property *p:vlsPre->elements){
					AtomVariabla *av=(AtomVariabla *)p;
					if(av->checkScalaVaribale(scalaVar)){
						if(av->hasStep()){
							if(av->checkUpdateStmt(z3Stmt)){
								ret->add(av->clone());
							#ifdef _DEBUG	
								std::cout<<"gen: "<< av->toString()<<std::endl;
							#endif
								return ret;
							}
						}
						else{
							av=av->clone();
							av->addIndexUpdateStmt(s);
							ret->add(av);
						#ifdef _DEBUG	
							std::cout<<"gen: "<< av->toString()<<std::endl;
						#endif
							return ret;
						}
					}
				}
			}
		}
		return ret;
	}
	void flowThrouth(CFGBlock*&n, FlowSet *&in, list<pair<CFGBlock*,FlowSet*>*> *&outs){
		for(auto it=outs->begin();it != outs->end(); it++){
			pair<CFGBlock*,FlowSet*>* ele=*it;
			 if(ele->second==&universalSet){
				 ele->second=new ValueListSet();
			 }
		}
		FlowSet * Pre=in->clone();
		for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
			CFGElement element=(*iterblock);
			if(element.getKind()==CFGElement::Kind::Statement){
				const Stmt* it=((CFGStmt*)&element)->getStmt();
			#ifdef _DEBUG
				std::cout<<"Pre is: "<< Pre->toString()<<std::endl;
				std::cout<<"stmt is: "<< z3coding.toString(it)<<std::endl;
			#endif
				FlowSet* pin=mapToStmtIn.at(it);
				pin->clear();
				pin->Union(Pre);
				Pre=GenAndKill(Pre,it);
				FlowSet* pout=mapToStmtOut.at(it);
				pout->clear();
				pout->Union(Pre);
				
			#ifdef _DEBUG
				std::cout<<"Pos is: "<< Pre->toString()<<std::endl;
			#endif
			
			}
		}
		if(outs->size()==2){
			Stmt* T=n->getTerminatorCondition();
			FlowSet* pin=mapToStmtIn.at(T);
			pin->clear();
			pin->Union(Pre);
			FlowSet* pout=mapToStmtOut.at(T);
			pout->clear();
			pout->Union(Pre);
			
			pair<CFGBlock*,FlowSet*>* tureBranch=outs->front();
			ValueListSet *tureFlow=(ValueListSet*)tureBranch->second;
			pair<CFGBlock*,FlowSet*>* falseBranch=outs->back();
			ValueListSet *falseFlow=(ValueListSet*)falseBranch->second;
			tureFlow->Union(Pre->clone());
			falseFlow->Union(Pre->clone());
			
		}
		else if(outs->size()==1){
			pair<CFGBlock*,FlowSet*>* out=outs->front();
			ValueListSet *outFlow=(ValueListSet*)out->second;
			outFlow->Union(Pre->clone());
		}
				
	}
	void copy(FlowSet  *&from,FlowSet  *&to){
		if(from==&universalSet) {
			to=&universalSet;
		}
		else {
			to=from->clone();
		}
		
	}
//	FlowSet* clone(FlowSet  * from){
//		ValueListSet* vls=new ValueListSet();
//		ValueListSet* vlsFrom=(ValueListSet*)from;
//		for(Property* p: vlsFrom->elements){
//			
//			vls->add()
//		}
//	}
	void printStmtAnalysis(){
		for (map<const clang::Stmt*, FlowSet*>::iterator it=mapToStmtIn.begin(); it!=mapToStmtIn.end(); ++it){
			std::cout <<z3coding.toString(it->first) << " in :"; it->second->print();
			FlowSet * out=mapToStmtOut.at(it->first);
			std::cout <<z3coding.toString(it->first) << " out :";out->print();
		}

	}
};

#endif