#ifndef _PropertyCollectUtil_H
#define _PropertyCollectUtil_H
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
#include "FlowSet.h"
#include <vector>
#include "Formula.h"
class PropertyCollectUtil{
private:
	vector<unsigned>* focusBlocks;
	map<unsigned, vector<FlowSet*>*>* focusBlocksIn;
	//map<CFGBlock*, list<pair<CFGBlock*,vector<FlowSet*>*>*>*>* focusBlocksOut;
	bool isIn(CFGBlock* b,vector<unsigned>* blocks){
		for(unsigned ele:*blocks){
			if(b->getBlockID()==ele){
				return true;
			}
		}
		return false;
	}
	bool isIn(FlowSet* f,vector<FlowSet*>* flows){
		for(FlowSet* ele:*flows){
			if(f->equal(ele)){
				return true;
			}
		}
		return false;
	}
	
public:
	
	PropertyCollectUtil(){
		focusBlocks=new vector<unsigned>();
		focusBlocksIn=new map<unsigned, vector<FlowSet*>*>();
	}
	void addFocusBlock(CFGBlock* focusBlock){
		if(!isIn(focusBlock,focusBlocks)){
			this->focusBlocks->push_back(focusBlock->getBlockID());
			focusBlocksIn->insert(std::pair<unsigned, vector<FlowSet*>*>(focusBlock->getBlockID(),new vector<FlowSet*>()));
		}
	}
	void addFocusBlock(vector<CFGBlock*>* focusBlocks){
		for(CFGBlock* b:*focusBlocks){
			addFocusBlock(b);
		}
	}
	bool trigger(CFGBlock* b){
		return isIn(b,focusBlocks);
	}

	void addBlockIn(CFGBlock* b,FlowSet* in){
		if(trigger(b)){
			vector<FlowSet*>* c=focusBlocksIn->at(b->getBlockID());
			
			if(!isIn(in,c)){
				c->push_back(in);
			}
		}
	}
	vector<FlowSet*>* getFocusBlockIn(CFGBlock* b){
		if(isIn(b,focusBlocks)){
			return focusBlocksIn->at(b->getBlockID());
		}
		return nullptr;
	}
	
	vector<unsigned>* getFocusBlocks(){
		return focusBlocks;
	}
};

#endif