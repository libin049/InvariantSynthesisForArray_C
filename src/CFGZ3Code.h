#ifndef _CFGZ3Code_H
#define _CFGZ3Code_H
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
using namespace z3;


class CFGZ3Code{
	context &c;
	Z3Coding &z3coding;
	clang::CFG* cfg;
	vector<CFGBlock*>* blocksOfHasAssignToPointer;
	bool isPointToBack(CFGBlock* n){
		const Stmt *looptarget =n->getLoopTarget();
		if(looptarget!=nullptr){
			if(n->succ_size()==1){
				return true;
			}
			else{
				std::cerr<<"CFGZ3Code::I think something is wrong,block not point to back!"<<std::endl;	
				return true;
			}
		}
		else{
			return false;
		}
	}
	bool isIn(CFGBlock* b,vector<CFGBlock*>* blocks){
		for(CFGBlock* t:*blocks){
			if(t==b){
				return true;
			}
		}
		return false;
	}
	
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
	
	void Ghosting(){
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			
			if(isPointToBack(block)){
				CFGBlock* theBackBlock=block;
				
				unsigned backB=theBackBlock->getBlockID();
				vector<vector<expr>*>* tmp=cfgZ3Codes->at(theBackBlock);
				vector<vector<expr>*>* backblockZ3codes=cfgGhostZ3Codes->at(theBackBlock);
				pushAToB(tmp,backblockZ3codes);
				cout<<backB<<std::endl;
				if(block->size()==0){
					backblockZ3codes->push_back(new vector<expr>());
				}
				vector<expr>* backblockLastStmtZ3codes=backblockZ3codes->back();
				for(CFGBlock* theb:*blocksOfHasAssignToPointer){
					tmp=cfgZ3Codes->at(theb);
					vector<vector<expr>*>* initblockZ3codes=cfgGhostZ3Codes->at(theb);
					if(initblockZ3codes->size()==0){
						pushAToB(tmp,initblockZ3codes);
					}
					vector<expr>* initblockFirstStmtZ3codes=initblockZ3codes->front();
					
					unsigned initB=theb->getBlockID();
					std::string indexName="i";
					indexName+=std::to_string(initB)+"_"+std::to_string(backB);
					expr ghostIndexInit=z3coding.prime(c.int_const(indexName.c_str()))==0;
					expr ghostIndexUpdate=z3coding.prime(c.int_const(indexName.c_str()))==c.int_const(indexName.c_str())+1;
					initblockFirstStmtZ3codes->push_back(ghostIndexInit);
					backblockLastStmtZ3codes->push_back(ghostIndexUpdate);
					ghostExpr->push_back(c.int_const(indexName.c_str())); 
				}
				if(blocksOfHasAssignToPointer->size()>0){
					ghostBlocks->push_back(block);
				}
			}
			else{
				vector<vector<expr>*>* tmp=cfgZ3Codes->at(block);
				vector<vector<expr>*>* backblockZ3codes=cfgGhostZ3Codes->at(block);
				if(backblockZ3codes->size()==0){
					pushAToB(tmp,backblockZ3codes);
				}
				
			}
		}
	}
	void CFGToZ3Coding(clang::CFG* cfg){
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			vector<vector<expr>*>* blockZ3coding=new vector<vector<expr>*>();
			Stmt* T=block->getTerminatorCondition();
			for(CFGBlock::iterator iterblock=block->begin();iterblock!=block->end();++iterblock){
				CFGElement element=(*iterblock);
				if(element.getKind()==CFGElement::Kind::Statement){
					vector<expr>* stmtZ3coding=new vector<expr>();
					const Stmt* it=((CFGStmt*)&element)->getStmt();
					//cout<<"stmt is::---------"+z3coding.toString(it)<<std::endl;
					if(T!=nullptr){
						if(it==T) break;
					}
					z3coding.isAssignedToPointer=false;
					vector<expr> * tmp=z3coding.clangStmtToZ3Expr(it);
					if(tmp!=nullptr){
						z3coding.pushAToB(tmp,stmtZ3coding);
						blockZ3coding->push_back(stmtZ3coding);
						if(z3coding.isAssignedToPointer){
							if(!isIn(block,blocksOfHasAssignToPointer)){
								blocksOfHasAssignToPointer->push_back(block);
							}
						}
					}
					else{
						blockZ3coding->push_back(nullptr);
					}
				}
			}
			if(T!=nullptr){
				vector<expr>* stmtZ3coding=new vector<expr>();
				z3coding.isAssignedToPointer=false;
				vector<expr> * tmp=z3coding.clangStmtToZ3Expr(T);
				if(tmp!=nullptr){
					z3coding.pushAToB(tmp,stmtZ3coding);
					blockZ3coding->push_back(stmtZ3coding);
					if(z3coding.isAssignedToPointer){
						if(!isIn(block,blocksOfHasAssignToPointer)){
							blocksOfHasAssignToPointer->push_back(block);
						}
					}
				}
				else{
					blockZ3coding->push_back(nullptr);
				}	
			}
			cfgZ3Codes->insert(std::pair<CFGBlock*,vector<vector<expr>*>*>(block,blockZ3coding));
		}
		
	}
	
	
	Preprocess* preprocess;
	public:
	map<CFGBlock*,vector<vector<expr>*>*>* cfgZ3Codes;
	map<CFGBlock*,vector<vector<expr>*>*>* cfgGhostZ3Codes;
	vector<CFGBlock*>* ghostBlocks;//we add update z3code in this block, the blocks point back 
	vector<expr>* ghostExpr;
	
	CFGZ3Code(clang::CFG* cfg,Z3Coding &coding,context &ctx,Preprocess* preprocess):c(ctx),z3coding(coding){
		this->cfg=cfg;
		this->preprocess=preprocess;
		cfgZ3Codes=new map<CFGBlock*,vector<vector<expr>*>*>;
		cfgGhostZ3Codes=new map<CFGBlock*,vector<vector<expr>*>*>;
		ghostBlocks=new vector<CFGBlock*>();
		ghostExpr=new vector<expr>();
		blocksOfHasAssignToPointer=new vector<CFGBlock*>();
		
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			vector<vector<expr>*>* blockZ3coding=new vector<vector<expr>*>();
			cfgGhostZ3Codes->insert(std::pair<CFGBlock*,vector<vector<expr>*>*>(block,blockZ3coding));
			
		}
		
		CFGToZ3Coding(cfg);
		if(preprocess->isNeedToGhost){
			Ghosting();
			z3coding.addMemoryUnits(ghostExpr);
		}
	}
	~CFGZ3Code(){}
	void printcfgZ3Codes(){
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			std::cout <<"----------------------------------------------"<<std::endl;
			std::cout <<"[B"<< block->getBlockID ()<<"]::"<<std::endl;;
			vector<vector<expr>*>* blockZ3codes=cfgZ3Codes->at(block);
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
	void printcfgGhostZ3Codes(){
		for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
			CFGBlock* block=*iter;
			std::cout <<"----------------------------------------------"<<std::endl;
			std::cout <<"[B"<< block->getBlockID ()<<"]::"<<std::endl;;
			vector<vector<expr>*>* blockZ3codes=cfgGhostZ3Codes->at(block);
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
