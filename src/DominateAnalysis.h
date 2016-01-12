#ifndef _DOMINATEANALYSIS_H
#define _DOMINATEANALYSIS_H

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
#include "DataFlowAnalysis.h"
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;

class IsDominate: public Property{
public:	
	bool isDominate;
	IsDominate(bool isDominate){
		this->isDominate=isDominate;
	}
	bool equal(Property *p){
		IsDominate * node=(IsDominate *)p;
		return this->isDominate==node->isDominate;
	}
	std::string toString(){
		if(isDominate){
			return "Dominate";
		}
		else{
			return "unDominate";
		}
	}
};
/**
 * @class DominateAnalysis
 * @author ubuntu15.10_x64
 * @date 26/12/15
 * @file DominateAnalysis.h
 * @brief get the  Dominate CFGBlock by edge
 */
class DominateAnalysis : public IntraDataFlowAnalysis{
private:
	std::pair<CFGBlock*,CFGBlock*>* edge;
public:
	DominateAnalysis(clang::CFG* cfg,std::pair<CFGBlock*,CFGBlock*>* edge):IntraDataFlowAnalysis(cfg){
		this->edge=edge;
		doAnalysis();
	}
	~DominateAnalysis(){}
	
	FlowSet * newinitialFlow(){
		ValueListSet* ret= new ValueListSet();
		ret->add(new IsDominate(true));
		return ret;
	}
	FlowSet * entryInitialFlow(){
		ValueListSet* ret= new ValueListSet();
		ret->add(new IsDominate(false));
		return ret;
	}
	void merge(FlowSet  * &in1,FlowSet  *&in2,FlowSet  *&out){
		ValueListSet* vin1= (ValueListSet*)in1;
		ValueListSet* vin2= (ValueListSet*)in2;
		Property * p1=vin1->elements.front();
		IsDominate * isdomp1=(IsDominate *)p1;
		Property * p2=vin2->elements.front();
		IsDominate * isdomp2=(IsDominate *)p2;
		out->clear();
		if(isdomp1->isDominate&&isdomp2->isDominate){
			out->add(new IsDominate(true));
		}
		else{
			out->add(new IsDominate(false));
		}
		return;
	}
	void flowThrouth(CFGBlock*&n, FlowSet *&in, list<pair<CFGBlock*,FlowSet*>*> *&outs){
		ValueListSet* vin= (ValueListSet*)in;
		IsDominate * inp=(IsDominate *)(vin->elements.front());
		if(!inp->isDominate){
			CFGBlock* src=edge->first;
			CFGBlock* des=edge->second;
			if(n==src){
				for(auto it=outs->begin();it != outs->end(); it++){
					pair<CFGBlock*,FlowSet*>* ele=*it;
					CFGBlock* b=ele->first;
					if(des==b){
						ValueListSet *outFlow=(ValueListSet*)ele->second;
						outFlow->clear();
						outFlow->add(new IsDominate(true));
					}
					else{
						ValueListSet *outFlow=(ValueListSet*)ele->second;
						outFlow->clear();
						outFlow->add(new IsDominate(false));
					}
				}
			}
			else{
				for(auto it=outs->begin();it != outs->end(); it++){
					pair<CFGBlock*,FlowSet*>* ele=*it;
					ValueListSet *outFlow=(ValueListSet*)ele->second;
					outFlow->clear();
					outFlow->add(new IsDominate(false));
				}
			}
		}
		else{
			for(auto it=outs->begin();it != outs->end(); it++){
				pair<CFGBlock*,FlowSet*>* ele=*it;
				ValueListSet *outFlow=(ValueListSet*)ele->second;
				outFlow->clear();
				outFlow->add(new IsDominate(true));
			}
		}
		
		
	}
	void copy(FlowSet  *&from,FlowSet  *&to){
		to=from->clone();
	}
	
	vector<CFGBlock*>* getDominateSet(){
		vector<CFGBlock*>* ret=new vector<CFGBlock*>();
		map<CFGBlock*, FlowSet*>* isDomMap=getMapToBlockIn();
		for(std::pair<CFGBlock*, FlowSet*> p: *isDomMap){
			ValueListSet *flow=(ValueListSet*)p.second;
			IsDominate * isDom=(IsDominate *)(flow->elements.front());
			if(isDom->isDominate){
				ret->push_back(p.first);
			}
		}
		return ret;
	}

};

#endif
