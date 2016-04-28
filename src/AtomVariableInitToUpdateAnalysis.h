#ifndef _AtomVariablaInitToUpdateAnalysis_H
#define _AtomVariablaInitToUpdateAnalysis_H
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
#include "AtomVariableAnalysis.h"
using namespace z3;

extern  bool occurError;

class AtomVariablaInitToUpdate : public Property{
public:
	
	AtomVariabla* av;

	AtomVariablaInitToUpdate(AtomVariabla* av){
		this->av=av;
	}
	
	bool equal(Property *p){
		AtomVariablaInitToUpdate * avi=(AtomVariablaInitToUpdate *)p;
		return avi->av==av;
	}
	std::string toString(){
		
		std::string ret=Z3_ast_to_string(av->c,av->scalaVarz3coding);
		return ret;
	}
	AtomVariablaInitToUpdate* clone(){
		return new AtomVariablaInitToUpdate(av);
	}
	
};

class AtomVariablaInitToUpdateAnalysis: public IntraDataFlowAnalysis{
	ValueListSet universalSet;
	Z3Coding &z3coding;
	AtomVariablaAnalysis* ava;
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
	AtomVariablaInitToUpdateAnalysis(clang::CFG* cfg,Z3Coding &coding,AtomVariablaAnalysis* ava):IntraDataFlowAnalysis(cfg),z3coding(coding){
		
		this->ava=ava;
		pre_init();
		doAnalysis();
	}
	~AtomVariablaInitToUpdateAnalysis(){}
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
				AtomVariablaInitToUpdate* r=meet((AtomVariablaInitToUpdate*)p1,(AtomVariablaInitToUpdate*)p2);
				if(r!=nullptr){
					out->add(r);
				}
			}
		}
		return;
	}
	AtomVariablaInitToUpdate* meet(AtomVariablaInitToUpdate* in1,AtomVariablaInitToUpdate* in2){
		if(in1->equal(in2)){
			return in1->clone();
		}
		return nullptr;
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
	/**
	 * @brief check index is atom variable in after clangStmt
	 * @param clangStmt
	 * @param index
	 * @return 
	 */
	bool isAtomAvriableAfterInitStmt(const clang::Stmt* clangStmt){
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return false;
			}
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->indexInitStmt==clangStmt){
					if(av->hasStep()){
						return true;
					}
				}
			}
			return false;
	}
	bool isAtomAvriableAfterUpdateStmt(const clang::Stmt* clangStmt){
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return false;
			}
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->isIn(clangStmt,av->indexUpdateStmts)){
					if(av->hasStep()){
						return true;
					}
				}
			}
			return false;
	}
	AtomVariabla * getAtomAvriableAfterInitStmt(const clang::Stmt* clangStmt){
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return nullptr;
			}
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->indexInitStmt==clangStmt){
					if(av->hasStep()){
						return av;
					}
				}
			}
			return nullptr;
	}
	FlowSet * GenAndKill(FlowSet * Pre,const Stmt* s){
		FlowSet * ret=new ValueListSet();
		vector<expr> * tmp=z3coding.clangStmtToZ3Expr(s);
		if(tmp==nullptr){
			return ret;
		}
		tmp=z3coding.boolSortFiltering(tmp);
		if(tmp->size()<=0){
			ret->Union(Pre);
			return ret;
		}
		for(unsigned i=0;i<tmp->size();i++){
			expr z3Stmt=tmp->at(i);
		
			ValueListSet* vlsPre=(ValueListSet*) Pre;
			ret->Union(vlsPre);
		
			//gen&&kill
			if(isAssigndToScaleVariable(z3Stmt)){
				expr scalaVar=z3coding.unprime(z3Stmt.arg(0));
				if(isAtomInitStmt(z3Stmt)){
					if(isAtomAvriableAfterInitStmt(s)){
						AtomVariablaInitToUpdate* avi=new AtomVariablaInitToUpdate(getAtomAvriableAfterInitStmt(s));
						#ifdef _DEBUG	
							std::cout<<"gen: "<< scalaVar <<" is init"<<std::endl;
						#endif
						if(!ret->isIn(avi)){
							ret->add(avi);
						}
					}
				}
				else if(isAtomUpdateStmt(z3Stmt)){
					if(isAtomAvriableAfterUpdateStmt(s)){
						for(Property *p:vlsPre->elements){
							AtomVariablaInitToUpdate *avi=(AtomVariablaInitToUpdate *)p;
							if(avi->av->checkScalaVaribale(scalaVar)){
								ret->remove(avi);
								#ifdef _DEBUG	
									std::cout<<"kill: "<<scalaVar <<" is to update"<<std::endl;
								#endif
								break;	
							}
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
	bool equal(FlowSet  *&from,FlowSet  *&to){
		if(from==&universalSet) {
			return to==&universalSet;
		}
		if(to==&universalSet) {
			return from==&universalSet;
		}
		return from->equal(to);
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