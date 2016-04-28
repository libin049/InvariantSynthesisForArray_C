#ifndef _NormalizationAnalysis_H
#define _NormalizationAnalysis_H
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
#include "AtomVariableInitToUpdateAnalysis.h"
#include "AtomVariableDiffAnalysisOnExpr.h"

using namespace z3;


class NormalizationAnalysis{
	Z3Coding &z3coding;
	clang::CFG* cfg;
	AtomVariableDiffAnalysisOnExpr *avd;
	CFGZ3Code* cfgZ3Code;  
	
	void Normalizate(){
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			vector<vector<expr>*>* tmp=cfgZ3Code->cfgGhostZ3Codes->at(block);
			vector<vector<expr>*>* backblockZ3codes=NormalizateZ3Codes->at(block);
			
			for(vector<expr>* stmtz3code:*tmp){
				vector<expr>* newstmtz3code;
				if(stmtz3code!=nullptr){
					newstmtz3code=new vector<expr>();
					z3coding.pushAToB(stmtz3code,newstmtz3code);
				}
				else{
					newstmtz3code=nullptr;
				}
				backblockZ3codes->push_back(newstmtz3code);
			}
			
		}
		
		cout<<"------------mildle result----------------"<<std::endl;
		print();
		cout<<"------------mildle result--end--------------"<<std::endl;
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			if(block->getBlockID()==3){
				std::cout <<"-----------process [B"<< block->getBlockID()<<"]-------------"<<std::endl;
			}
			vector<vector<expr>*>* blockZ3code=NormalizateZ3Codes->at(block);
			int count=0;
			for(CFGBlock::iterator iterblock=block->begin();iterblock!=block->end();++iterblock){
				
				CFGElement element=(*iterblock);
				if(element.getKind()==CFGElement::Kind::Statement){
					const Stmt* it=((CFGStmt*)&element)->getStmt();
					vector<expr>* stmtZ3code=blockZ3code->at(count);
					FlowSet* Pre=avd->mapToStmtIn.at(it);
					ValueListSet* vlsPre=(ValueListSet*)Pre;
					for(Property* p: vlsPre->elements){
						
						vector<expr>* oldstmtZ3code=new vector<expr>();
						z3coding.pushAToB(stmtZ3code,oldstmtZ3code);
						stmtZ3code->clear();
						AtomVariablaDiff * avdiff=(AtomVariablaDiff *)p;
						expr index1=avdiff->av1->scalaVarz3coding;
						expr index2=avdiff->av2->scalaVarz3coding;
						if(z3coding.isIn(index1,cfgZ3Code->ghostExpr)&&z3coding.isPointerIndex(index2)){
							expr e=avdiff->generateEquation2();
							cout<<"------Equation is: -"<<e<<std::endl;
							expr from=e.arg(0);
							expr to=e.arg(1);
							vector<expr>* tmp=replace(oldstmtZ3code,from,to);
							z3coding.pushAToB(tmp,stmtZ3code);
						}
						else if(z3coding.isIn(index2,cfgZ3Code->ghostExpr)&&z3coding.isPointerIndex(index1)){
							expr e=avdiff->generateEquation1();
							cout<<"------Equation is: -"<<e<<std::endl;
							expr from=e.arg(0);
							expr to=e.arg(1);
							vector<expr>* tmp=replace(oldstmtZ3code,from,to);
							z3coding.pushAToB(tmp,stmtZ3code);
						}
						else{
							z3coding.pushAToB(oldstmtZ3code,stmtZ3code);
						}
					}
				}
				count++;
			}
		}
	}
	
	vector<expr>* replace(vector<expr>* formulas,expr from,expr to){
		vector<expr>* result=new vector<expr>();
		for(expr f:*formulas){
			expr tmp=z3coding.substitute(f,from,to);
			cout<<"------replace -"<<f<<"---to---"<< tmp<<std::endl;
			result->push_back(tmp);
		}
		return result;
	}
	/*void Normalizate(){
		vector<AtomVariablaDiff*> *theReplace=new vector<AtomVariablaDiff*>();
		vector<expr> *theReplaceCode=new vector<expr>();
		vector<expr> *theTargeInitCode=new vector<expr>();
		vector<expr> *theTargeUpdateCode=new vector<expr>();
		for(CFGBlock* b:*cfgZ3Code->ghostBlocks){
			list<pair<CFGBlock*,FlowSet*>*>* out=avd->getMapToBlockOut()->at(b);
			if(out->size()!=1){
				std::cerr<<"NormalizationAnalysis::Normalizate error"<<std::endl;
				return;
			}
			else{
				vector<vector<expr>*>* blockZ3code=cfgZ3Code->cfgGhostZ3Codes->at(b);
				vector<expr>* blockLastStmtZ3codes=blockZ3code->back();
				
				expr lastcode=blockLastStmtZ3codes->back();
				expr theIndex=z3coding.unprime(lastcode.arg(0));
				cout<<"is gost update stmt:: "<<lastcode<<std::endl;
				for(auto it=out->begin(); it!=out->end(); ++it){
					ValueListSet* vlsOut=(ValueListSet*)(*it)->second;
					for(Property* p: vlsOut->elements){
						AtomVariablaDiff * avdiff=(AtomVariablaDiff *)p;
						expr index1=avdiff->av1->scalaVarz3coding;
						expr index2=avdiff->av2->scalaVarz3coding;
						if(z3coding.equal(theIndex,index1)){
							expr e=avdiff->generateEquation2();
							theReplaceCode->push_back(e);
							theReplace->push_back(avdiff);
							theTargeInitCode->push_back(avdiff->av2->indexInitStmtz3coding);
							theTargeUpdateCode->push_back(avdiff->av2->indexUpdateStmtz3coding);
						}
						else if(z3coding.equal(theIndex,index2)){
							expr e=avdiff->generateEquation1();
							theReplaceCode->push_back(e);
							theReplace->push_back(avdiff);
							theTargeInitCode->push_back(avdiff->av1->indexInitStmtz3coding);
							theTargeUpdateCode->push_back(avdiff->av1->indexUpdateStmtz3coding);
						}
						
					}
				}
			}
		}
		cout<<"replace code::"<<z3coding.toString(theReplaceCode)<<std::endl;
		cout<<"taget init code::"<<z3coding.toString(theTargeInitCode)<<std::endl;
		cout<<"taget update code::"<<z3coding.toString(theTargeUpdateCode)<<std::endl;
		
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			vector<vector<expr>*>* tmp=cfgZ3Code->cfgGhostZ3Codes->at(block);
			vector<vector<expr>*>* backblockZ3codes=NormalizateZ3Codes->at(block);
			
			for(vector<expr>* stmtz3code:*tmp){
				vector<expr>* newstmtz3code;
				if(stmtz3code!=nullptr){
					newstmtz3code=new vector<expr>();
					z3coding.pushAToB(stmtz3code,newstmtz3code);
				}
				else{
					newstmtz3code=nullptr;
				}
				backblockZ3codes->push_back(newstmtz3code);
			}
			
		}
		cout<<"------------------------midle---------------"<<std::endl;
		print();
		for(unsigned i=0;i<theReplaceCode->size();i++){
			expr left=theReplaceCode->at(i).arg(0);
			expr right=theReplaceCode->at(i).arg(1);
			for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
				CFGBlock* block=*iter;
				vector<vector<expr>*>* blockZ3codes=NormalizateZ3Codes->at(block);
				vector<vector<expr>*>* oldblockZ3codes=new vector<vector<expr>*>();
				pushAToB(blockZ3codes,oldblockZ3codes);
				blockZ3codes->clear();
				for(vector<expr>* stmtz3code:*oldblockZ3codes){
					vector<expr>* newstmtz3code;
					if(stmtz3code!=nullptr){
						newstmtz3code=new vector<expr>();
						for(expr e:*stmtz3code){
							if(z3coding.equal(e,theTargeInitCode->at(i))||z3coding.equal(e,theTargeUpdateCode->at(i))){
								
							}
							else{
								newstmtz3code->push_back(z3coding.substitute(e,left,right));
							}
						}
					}
					else{
						newstmtz3code=nullptr;
					}
					blockZ3codes->push_back(newstmtz3code);
				}
				
			}
		}
		
		
	}*/
	void pushAToB(vector<vector<expr>*>* A,vector<vector<expr>*>* B){
		for(vector<expr>* Aa:*A){
			if(Aa!=nullptr){
				vector<expr>* tmp=new vector<expr>();
				z3coding.pushAToB(Aa,tmp);
				B->push_back(tmp);
			}
			else{
				B->push_back(nullptr);
			}
		}
	}
public:
	
	
	map<CFGBlock*,vector<vector<expr>*>*>* NormalizateZ3Codes;
	NormalizationAnalysis(clang::CFG* cfg,Z3Coding &coding,AtomVariableDiffAnalysisOnExpr* avd,
	CFGZ3Code* cfgZ3Code):z3coding(coding){
		this->cfg=cfg;
		this->cfgZ3Code=cfgZ3Code;
		this->avd=avd;
		NormalizateZ3Codes=new map<CFGBlock*,vector<vector<expr>*>*>();
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			vector<vector<expr>*>* blockZ3coding=new vector<vector<expr>*>();
			NormalizateZ3Codes->insert(std::pair<CFGBlock*,vector<vector<expr>*>*>(block,blockZ3coding));
		}
		Normalizate();
	}
	~NormalizationAnalysis(){}
	
	void print(){
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			std::cout <<"----------------------------------------------"<<std::endl;
			std::cout <<"[B"<< block->getBlockID ()<<"]::"<<std::endl;;
			vector<vector<expr>*>* blockZ3codes=NormalizateZ3Codes->at(block);
			for(vector<expr>* stmtcode:*blockZ3codes){
				if(stmtcode==nullptr){
					cout<<"null"<<std::endl;
				}
				else{
					cout<<z3coding.toString(stmtcode)<<std::endl;
				}
			}
		}
	}
};

#endif