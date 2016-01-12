#ifndef _PATHGUIDE_H
#define _PATHGUIDE_H
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


#include <vector>
#include <map>
#include <string>
#include <list>


using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;

/*
		 * loop path guide, loop has one entry,that is for/while condition stmt; exit has three situations
		 * 			situation 1: one exit, which is the entry--for/while condition stmt
		 * 			situation 2: two exit, 1). for/while condition stmt, and the CFGBlock which is pointed by for/while condition stmt false edge
		 * 			situation 3: others, more than  and equal to two exit,  one of them must be for/while condition stmt,  
		 * 						  and one of them must not be for/while condition stmt or the CFGBlock which is pointed by for/while condition stmt 
		 * 						  false edge
*/
class PathGuide{
private:		
		clang::CFG* cfg;
		map<const Stmt*,vector<CFGBlock*>*> LoopStmtToCFGBolck;
		
		
		
		vector<CFGBlock*> * getAllLoopEntryCFGBlock(vector<const Stmt*> * loopCondition){
			vector<CFGBlock*> * loopEntryCFGBlocks=new vector<CFGBlock*>();
			for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter)
			{
				CFGBlock* block=*iter;
				const Stmt *Tcond =block->getTerminatorCondition();
				if(Tcond!=nullptr){
					if(isIn(Tcond,loopCondition)){
						loopEntryCFGBlocks->push_back(block);
					}
				}
			}
			return loopEntryCFGBlocks;
		}
		
		vector<const Stmt*> * getAllLoopStmt(){
			vector<const Stmt*> *ret=new vector<const Stmt*>();
			for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter)
			{
				CFGBlock* block=*iter;
				const Stmt *looptarget =block->getLoopTarget();
				if(looptarget!=nullptr){
					if(!isIn(looptarget,ret)){
						ret->push_back(looptarget);
					}
				}
			}
			return ret;
		}
		vector<const Stmt*> * getAllLoopCondition(vector<const Stmt*> * loopStmts){
			vector<const Stmt*> * conditions=new vector<const Stmt*>();
			for(const Stmt* loop: *loopStmts){
				switch (loop->getStmtClass()) {
					default:
						std::cerr<<"PathGuide:getAllLoopCondition, something is wrong!"<<std::endl;break;
					case Stmt::WhileStmtClass:
					{	
						const WhileStmt* whileLoop=(const WhileStmt*)loop;
						conditions->push_back(whileLoop->getCond());
						break;
					}
					case Stmt::ForStmtClass:
					{
						const ForStmt* forLoop=(const ForStmt*)loop;
						conditions->push_back(forLoop->getCond());
						break;
					}
				}
			}
			return conditions;
		}
		bool isIn(const Stmt* s, vector<const Stmt*> * stmts){
			for(const Stmt* t: *stmts){
				if(t==s){
					return true;
				}
			}
			return false;
		}
		
		vector<CFGBlock*> * getAllLoopEntryCFGBlock(){
			return getAllLoopEntryCFGBlock(getAllLoopCondition(getAllLoopStmt()));
		}
		vector<CFGBlock*> * loopEntryCFGBlocks;
		
		bool isIn(CFGBlock * n,list<CFGBlock*> &blocks){
			for (std::list<CFGBlock*>::iterator it = blocks.begin(); it != blocks.end(); it++){
				CFGBlock *ele=*it;
				if(ele==n){
					return true;
				}
			}
			return false;
		}
		bool isIn(CFGBlock * n,vector<CFGBlock*>* &blocks){
			for (std::vector<CFGBlock*>::iterator it = blocks->begin(); it != blocks->end(); it++){
				CFGBlock *ele=*it;
				if(ele==n){
					return true;
				}
			}
			return false;
		}
public:
		PathGuide(clang::CFG* cfg){
			this->cfg=cfg;
			loopEntryCFGBlocks=getAllLoopEntryCFGBlock();
		}
		vector<CFGBlock*> * getLoopEntryCFGBlocks(){
			return loopEntryCFGBlocks;
		}
		void makeMaxPriorityFirst(CFGBlock* lastn,list<CFGBlock*> &queue){
			if(isIn(lastn,loopEntryCFGBlocks)){
				CFGBlock::succ_iterator succ_iter=lastn->succ_begin();
				CFGBlock* trueSucc=*succ_iter;
				++succ_iter;
				CFGBlock* falseSucc=*succ_iter;
				if(isIn(trueSucc,queue)){
					queue.remove(trueSucc);
					queue.push_front(trueSucc);
				}
				else if(isIn(falseSucc,queue)){
					queue.remove(falseSucc);
					queue.push_front(falseSucc);
				}
			}
			return;
		}
		
//		map<CFGBlock*,vector<CFGBlock*>*> LoopEntryDominateCFGBolck;		
//		map<CFGBlock*,vector<CFGBlock*>*>* getLoopEntryDominateCFGBlockSet(){
//			map<CFGBlock*,vector<CFGBlock*>*>*  ret=new map<CFGBlock*,vector<CFGBlock*>*>();
//			vector<CFGBlock*> * loopEntrys=getAllLoopEntryCFGBlock();
//			for(CFGBlock* entry: *loopEntrys){
//				CFGBlock::succ_iterator succ_iter=entry->succ_begin();
//				CFGBlock* trueSucc=*succ_iter;
//				std::pair<CFGBlock*,CFGBlock*>* edge=new std::pair<CFGBlock*,CFGBlock*>(entry,trueSucc);
//				DominateAnalysis domAna(cfg,edge);
//				vector<CFGBlock*>* dominateSet=domAna.getDominateSet();
//				ret->insert(std::pair<CFGBlock*,vector<CFGBlock*>*>(entry,dominateSet));
//			}
//			return ret;
//		}
		
//		std::string toString(map<CFGBlock*,vector<CFGBlock*>*>* loopEntryDominateCFGBlockSet){
//			std::string ret="";
//			for(std::pair<CFGBlock*,vector<CFGBlock*>*> p: *loopEntryDominateCFGBlockSet){
//				CFGBlock* b=p.first;
//				vector<CFGBlock*>* domSet=p.second;
//				ret+="B["+std::to_string(b->getBlockID())+"]"+" Dominate : ";
//				for(CFGBlock* ele: *domSet){
//					ret+="B["+std::to_string(ele->getBlockID())+"]"+"; ";
//				}
//				ret+="\n";
//			}
//			return ret;
//		}
		std::string toString(vector<CFGBlock*> * CFGBlocks){
			std::string ret="";
			for(CFGBlock* b:*CFGBlocks){
				ret+=std::to_string(b->getBlockID())+"; ";
			}
			return ret;
		}

};

#endif
