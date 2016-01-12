#ifndef _Formula_H
#define _Formula_H

#include "z3++.h"
class Formula : public Property{
	public:
		z3::expr formula;
		Formula(z3::expr f): formula(f){}
		bool equal(Property *p){
			Formula* f=(Formula*)(p);
			return z3::eq(formula,f->formula);
		}
		std::string toString(){
			
			std::string ret=Z3_ast_to_string(formula.ctx(),formula);
			if(formula.is_quantifier()){
				ret="\n"+ret+"\n";
			}
			return ret;
		}

};
#endif