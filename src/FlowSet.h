#ifndef _FLOWSET_H
#define _FLOWSET_H
#include "Property.h"
//template <typename T>
class FlowSet{
public :
	virtual ~FlowSet(){}
	virtual FlowSet * clone(){return nullptr;}
	virtual bool equal(FlowSet * flow){return false;}
	virtual void intersection(FlowSet * flow){}
	virtual void clear(){}
	virtual void print(){std::cout<<"flowSet"<<std::endl;}
	virtual int size(){return -1;}
	virtual bool add(Property *t){return false;}
	virtual bool remove(Property *t){return false;}
	virtual void Union(FlowSet * flow){}
	virtual bool isIn(Property *t){return false;}
	//virtual bool equal(T *t1,T *t2){return t1==t2;}
	virtual std::string toString(){return "";}
	//virtual std::string toString(T *t){return "";}
	
};
#endif