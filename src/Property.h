#ifndef _PROPERTY_H
#define _PROPERTY_H
#include <string>
class Property{
public:
	virtual ~Property(){} 
	virtual bool equal(Property* p){return false;}
	virtual std::string toString(){return "";}
	virtual Property* clone(){return this;}
};
#endif