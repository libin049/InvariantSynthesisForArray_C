#ifndef _VALUELISTSET_H
#define _VALUELISTSET_H
#include "FlowSet.h"
#include <list>
using namespace std;
//template <typename T>
class ValueListSet: public FlowSet{
public:
	list<Property *> elements;
	ValueListSet(){}
	//static ConditionValueListSet *UniversalSet;
	~ValueListSet(){} 
	FlowSet * clone(){
		ValueListSet* newSet=new ValueListSet();
		for(auto it=elements.begin();it != elements.end(); it++){
			Property *t=*it;
			newSet->elements.push_back(t->clone());
		}
		return newSet;
	}
	bool equal(FlowSet * flow){
		if(flow->size()!=this->size()) return false;
		for(auto it=elements.begin();it != elements.end(); it++){
			Property *t=*it;
			if(!flow->isIn(t)){
				return false;
			}
		}
		return true;
	}
	bool isIn(Property *ele){
		for(auto it=elements.begin();it != elements.end(); it++){
			Property *t=*it;
			if(ele->equal(t)){
				return true;
			}
		}
		return false;
	}
	
	void intersection(FlowSet * flow){
		list<Property*> newelements;
		for(auto it=elements.begin();it != elements.end(); it++){
			Property *t=*it;
			if(flow->isIn(t)){
				newelements.push_back(t);
			}
		}
		this->elements.clear();
		for(auto it=newelements.begin();it != newelements.end(); it++){
			Property *t=*it;
			this->elements.push_back(t);
		}
	}
	void clear(){
		elements.clear();
	}
	bool remove(Property *ele){
		for(auto it=elements.begin();it != elements.end(); it++){
			Property *t=*it;
			if(ele->equal(t)){
				elements.remove(t);
				return true;
			}
		}
		return false;
	}
	bool add(Property *ele){
		if(!isIn(ele)){
			elements.push_back(ele);
			return true;
		}
		return false;
	}
	std::string toString(){
		std::string ret="";
		for(auto it=elements.begin();it != elements.end(); it++){
			Property *t=*it;
			ret+="["+t->toString()+"] ";
		}
		return ret;
	}
	void print(){std::cout<<toString()<<std::endl;}
	int size(){
		return elements.size();
	}
	void Union(FlowSet *flow){
		ValueListSet *listSet=(ValueListSet *)flow;
		for(auto it=listSet->elements.begin();it != listSet->elements.end(); it++){
			Property *t=*it;
			this->add(t);
		}
	}
};

#endif