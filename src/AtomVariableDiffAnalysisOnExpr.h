#ifndef _AtomVariableDiffAnalysisOnExpr_H
#define _AtomVariableDiffAnalysisOnExpr_H
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
#include "AtomVariableAnalysisOnExpr.h"
#include "AtomVariableInitToUpdateAnalysisOnExpr.h"
using namespace z3;

extern  bool occurError;


class AtomVariableDiffAnalysisOnExpr: public IntraDataFlowAnalysis{
	ValueListSet universalSet;
	Z3Coding &z3coding;
	CFGZ3Code* cfgZ3Code;  
public:
	map<const clang::Stmt*, FlowSet*> mapToStmtIn;
	map<const clang::Stmt*, FlowSet*> mapToStmtOut;
	AtomVariableAnalysisOnExpr* ava;
	AtomVariableInitToUpdateAnalysisOnExpr* avi;
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
	AtomVariableDiffAnalysisOnExpr(clang::CFG* cfg,Z3Coding &coding,AtomVariableAnalysisOnExpr* ava,AtomVariableInitToUpdateAnalysisOnExpr* avi,
	CFGZ3Code* cfgZ3Code):
	IntraDataFlowAnalysis(cfg),z3coding(coding){
		this->cfgZ3Code=cfgZ3Code;
		this->ava=ava;
		this->avi=avi;
		pre_init();
		doAnalysis();
	}
	~AtomVariableDiffAnalysisOnExpr(){}
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
				AtomVariablaDiff* r=meet((AtomVariablaDiff*)p1,(AtomVariablaDiff*)p2);
				if(r!=nullptr){
					out->add(r);
				}
			}
		}
		return;
	}
	AtomVariablaDiff* meet(AtomVariablaDiff* in1,AtomVariablaDiff* in2){
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
	
	
	bool isAtomAvriableAfterUpdateStmt(const clang::Stmt* clangStmt,expr e,CFGBlock* n){
		if(clangStmt!=nullptr){
			
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return false;
			}
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->isIn(clangStmt,av->indexUpdateStmts)&&z3coding.equal(av->scalaVarz3coding,e)){
					if(av->hasStep()){
						return true;
					}
				}
			}
			return false;
		}
		else{
			if(ava->getMapToBlockOut()->count(n)<=0){
				return false;
			}
			FlowSet* out=ava->getMapToBlockOut()->at(n)->front()->second;
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(z3coding.equal(av->scalaVarz3coding,e)){
					if(av->hasStep()){
						return true;
					}
				}
			}
			return false;
		}
	}
	AtomVariabla* getAtomAvriableAfterUpdateStmt(const clang::Stmt* clangStmt,expr e,CFGBlock* n){
		if(clangStmt!=nullptr){
			
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return nullptr;
			}
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->isIn(clangStmt,av->indexUpdateStmts)&&z3coding.equal(av->scalaVarz3coding,e)){
					if(av->hasStep()){
						return av;
					}
				}
			}
			return nullptr;
		}
		else{
			if(ava->getMapToBlockOut()->count(n)<=0){
				return nullptr;
			}
			FlowSet* out=ava->getMapToBlockOut()->at(n)->front()->second;
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(z3coding.equal(av->scalaVarz3coding,e)){
					if(av->hasStep()){
						return av;
					}
				}
			}
			return nullptr;
		}
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
	vector<AtomVariablaInitToUpdate*>* getInitAtomVariabla(const clang::Stmt* clangStmt){
		vector<AtomVariablaInitToUpdate*>* result=new vector<AtomVariablaInitToUpdate*>();
		if(avi->mapToStmtOut.count(clangStmt)<=0){
				return result;
			}
			FlowSet* out=avi->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariablaInitToUpdate * av=(AtomVariablaInitToUpdate *)p;
				result->push_back(av);
			}
			return result;
	}
	FlowSet * GenAndKill(FlowSet * Pre,const Stmt* s,vector<expr> * z3codes,CFGBlock* n){
		FlowSet * ret=new ValueListSet();
		vector<expr> * tmp=z3codes;
		if(tmp==nullptr){
			return ret;
		}
		cout<<"z3codes is: "<<z3coding.toString(z3codes)<<std::endl;
		tmp=z3coding.boolSortFiltering(tmp);
		if(tmp->size()<=0){
			ret->Union(Pre);
			return ret;
		}
		ValueListSet* vlsPre=(ValueListSet*) Pre;
		ret=Pre->clone();
		for(unsigned i=0;i<tmp->size();i++){
			expr z3Stmt=tmp->at(i);
			//kill
			if(isAssigndToScaleVariable(z3Stmt)){
				expr scalaVar=z3coding.unprime(z3Stmt.arg(0));
				for(Property *p:vlsPre->elements){
					AtomVariablaDiff * avdiff=(AtomVariablaDiff *)p;
					AtomVariabla* av1=avdiff->av1;
					vector<expr>* initStmtConsts1=z3coding.getConsts(z3coding.unprimedDecline((av1->indexInitStmtz3coding)));
					vector<expr>* updateStmtConsts1=new vector<expr>();
					if(av1->hasStep()){
						updateStmtConsts1=z3coding.getConsts(z3coding.unprimedDecline((av1->indexUpdateStmtz3coding)));
					}
					AtomVariabla* av2=avdiff->av2;
					vector<expr>* initStmtConsts2=z3coding.getConsts(z3coding.unprimedDecline((av2->indexInitStmtz3coding)));
					vector<expr>* updateStmtConsts2=new vector<expr>();
					if(av2->hasStep()){
						updateStmtConsts2=z3coding.getConsts(z3coding.unprimedDecline((av2->indexUpdateStmtz3coding)));
					}
					
					if(z3coding.isIn(scalaVar,initStmtConsts1)||z3coding.isIn(scalaVar,updateStmtConsts1)
					||z3coding.isIn(scalaVar,initStmtConsts2)||z3coding.isIn(scalaVar,updateStmtConsts2)){
						//kill p
						ret->remove(avdiff);
					}
				}
			}
			else{
				ret=ret->clone();
			}
		
			//gen
			if(isAssigndToScaleVariable(z3Stmt)){
				expr scalaVar=z3coding.unprime(z3Stmt.arg(0));
				if(isAtomInitStmt(z3Stmt)){
					if(isAtomAvriableAfterInitStmt(s)){
						vector<AtomVariablaInitToUpdate*>* initAtomVariabla=getInitAtomVariabla(s);
						AtomVariabla* curInitAtomVariabla=getAtomAvriableAfterInitStmt(s);
						for(AtomVariablaInitToUpdate* initAtom: *initAtomVariabla){
							//cout<<"initAtom: "<<initAtom->toString()<<std::endl;
							if(!initAtom->av->equal(curInitAtomVariabla)){
								AtomVariablaDiff* avd=new AtomVariablaDiff(curInitAtomVariabla,initAtom->av,0);
								if(!ret->isIn(avd)){
									#ifdef _DEBUG	
									std::cout<<"gen: "<< avd->toString()<<std::endl;
									#endif
									ret->add(avd);
								}
							}
						}
					}
				}
				else if(isAtomUpdateStmt(z3Stmt)){
					if(isAtomAvriableAfterUpdateStmt(s,scalaVar,n)){
						AtomVariabla* curAtomVariabla=getAtomAvriableAfterUpdateStmt(s,scalaVar,n);
						cout<<curAtomVariabla->scalaVarz3coding<<std::endl;
						for(Property *p:vlsPre->elements){
							AtomVariablaDiff *avd=(AtomVariablaDiff *)p;
							cout<<avd->av1->scalaVarz3coding<<std::endl;
							if(avd->av1->equal(curAtomVariabla)){
								AtomVariablaDiff* tmp=avd->clone();
								tmp->diff=tmp->diff+1;
								#ifdef _DEBUG	
									std::cout<<"diff update: "<<tmp->toString()<<std::endl;
								#endif
								ret->add(tmp);
							}
							cout<<avd->av2->scalaVarz3coding<<std::endl;
							if(avd->av2->equal(curAtomVariabla)){
								AtomVariablaDiff* tmp=avd->clone();
								tmp->diff=tmp->diff-1;
								#ifdef _DEBUG	
									std::cout<<"diff update: "<<tmp->toString()<<std::endl;
								#endif
								ret->add(tmp);
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
		vector<vector<expr>*>* blockZ3code=cfgZ3Code->cfgGhostZ3Codes->at(n);
		if(n->size()==0&&blockZ3code->size()!=0){
			#ifdef _DEBUG
			std::cout<<"-------------------------------------"<<std::endl;
				std::cout<<"Pre is: "<< Pre->toString()<<std::endl;
				std::cout<<"stmt is empty "<<std::endl;
			#endif
			Pre=GenAndKill(Pre,nullptr,blockZ3code->at(0),n);
			#ifdef _DEBUG
			std::cout<<"Pos is: "<< Pre->toString()<<std::endl;
			#endif
		}
		else{
			int count=0;
		for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
			CFGElement element=(*iterblock);
			if(element.getKind()==CFGElement::Kind::Statement){
				const Stmt* it=((CFGStmt*)&element)->getStmt();
			#ifdef _DEBUG
				std::cout<<"-------------------------------------"<<std::endl;
				std::cout<<"Pre is: "<< Pre->toString()<<std::endl;
				std::cout<<"stmt is: "<< z3coding.toString(it)<<std::endl;
			#endif
				FlowSet* pin=mapToStmtIn.at(it);
				pin->clear();
				pin->Union(Pre);
				vector<expr>* stmtZ3codes=blockZ3code->at(count);
				Pre=GenAndKill(Pre,it,stmtZ3codes,n);
				FlowSet* pout=mapToStmtOut.at(it);
				pout->clear();
				pout->Union(Pre);
				
			#ifdef _DEBUG
				std::cout<<"Pos is: "<< Pre->toString()<<std::endl;
			#endif
			count++;
			}
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