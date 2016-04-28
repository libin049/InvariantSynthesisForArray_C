#ifndef _Z3Coding_H
#define _Z3Coding_H
#include <vector>
#include "z3++.h"
#include <string>
#include <iostream>
#include <vector>
#include <map>
#include "clang/AST/Expr.h"
#include "Preprocess.h"
using namespace z3;
using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
extern  bool occurError;
enum proved_result {
	proved, unproved,unknown
};
class Sort{
		public:
		z3::sort type; 
		Sort(z3::sort ty):type(ty){
		}
		
};
class Z3Coding{
	
	private:
		context &c;
		//map c++ name to z3 name
		//it is used to process nest scope
		//e.g. int i=1;...{int i=10;...}..
		//we map the second i to new name:i_varNameCount(i)
		map<const ValueDecl*,expr> varDeclToZ3Expr;
		map<std::string,const ValueDecl*> Z3ExprNameToVarDecl;
		//the Decl of var is dofferent, it record the same name of var but different decl 
		map<std::string,int> varNameCount;
		
		//all varDeclToZ3Expr.second is memoryUnit
		//all A([i])* ocurs in formula is memoryUnit
		map<std::string,expr> memoryUnits;
		
		bool setRet=false;
		expr _ret;
		
		map<const ValueDecl*,std::pair<expr,expr>> pointerVariable2pointerArray_PointerArrayIndex;
		
		
		void addMemoryUnit(expr memoryUnit){
			std::string memoryUnitName=Z3_ast_to_string(c,memoryUnit);
			if(memoryUnits.count(memoryUnitName)<=0){
				memoryUnits.insert(std::pair<std::string,z3::expr>(memoryUnitName,memoryUnit));
			}
		}
		bool check_formula(expr forallFormula){
			if(!forallFormula.is_quantifier()) return true;
			expr body=forallFormula.body();
			if(!(body.is_app()&&body.decl().name().str()=="=>")) return false;
			expr interval=body.arg(0);
			if(!(interval.is_app()&&interval.decl().name().str()=="and")) return false;
			expr extendIndexAndbeginEndFormula=interval.arg(0);
			
			if(!(extendIndexAndbeginEndFormula.is_app()&&extendIndexAndbeginEndFormula.decl().name().str()=="and")) return false;
			expr extendIndexAndbeginFormula=extendIndexAndbeginEndFormula.arg(0); 
			expr endFormula=extendIndexAndbeginEndFormula.arg(1);
			if(!(extendIndexAndbeginFormula.is_app()
				&&(extendIndexAndbeginFormula.decl().name().str()=="<"||extendIndexAndbeginFormula.decl().name().str()=="<=")
				&&endFormula.is_app()
				&&(endFormula.decl().name().str()=="<"||endFormula.decl().name().str()=="<="))) return false;
			expr stepformula=interval.arg(1);
			if(!(stepformula.decl().name().str()=="="&&stepformula.arg(0).decl().name().str()=="mod")) return false;
			expr p=body.arg(1);
			return check_formula(p);
		}
		
		vector<expr> * toSet(vector<expr> * exprs){
			vector<expr> * set= new vector<expr>();
			for(expr e:*exprs){
				if(!isIn(e,set)){
					set->push_back(e);
				}
			}
			return set;
		}
		bool _isOrFormula(expr f){
			if(f.is_quantifier()){
				//std::cerr<<"I do not consider ForAll Formula!"<<std::endl;	
				return false;
			}
			else if(f.is_app()){
				if(f.decl().name().str()=="or"){
					return true;
				}
				for(unsigned i=0;i<f.num_args();i++){
					if(_isOrFormula(f.arg(i))){
						return true;
					}
				}
				return false;
			}
			return false;
		}
		/**
		 * @brief simplify not (a<=b) to (a>b) and so on
		 * @param e
		 * @return 
		 */
		expr mySimplify(expr e){
			if(e.is_app()&&e.decl().name().str()=="not"){
				if(e.arg(0).is_app()){
					if(e.arg(0).decl().name().str()=="<"){
						return e.arg(0).arg(0)>=e.arg(0).arg(1);
					}
					else if(e.arg(0).decl().name().str()=="<="){
						return e.arg(0).arg(0)>e.arg(0).arg(1);
					}
					else if(e.arg(0).decl().name().str()==">"){
						return e.arg(0).arg(0)<=e.arg(0).arg(1);
					}
					else if(e.arg(0).decl().name().str()==">="){
						return e.arg(0).arg(0)<e.arg(0).arg(1);
					}
					else{
						return e;
					}
				}
				else{
					return e;
				}
			}
			else{
				return e;
			}
		}
		
		
		vector<expr> * _DNF(expr f){
			vector<expr> * ret=new vector<expr>();
			goal g(c);
			 g.add(f);
			tactic split_all = repeat(tactic(c, "split-clause") | tactic(c, "skip"));
			apply_result r = split_all(g);
			for (unsigned i = 0; i < r.size(); i++) {
				goal result_goal=r[i];
				ret->push_back(result_goal.as_expr());
//				std::cout << "subgoal " << i << "\n" << result_goal.as_expr() << "\n";
			}
			return ret;
		}
public:
		bool isAssignedToPointer;
		bool isPosIncOrDec;
		bool isPreIncOrDec;
		Preprocess* preprocess;
		expr _error;
		expr _nil;//represent no z3coding
		expr TRUE;
		expr FALSE;
		func_decl _phi;
		func_decl LtDecl;
		func_decl LeDecl;
		func_decl GtDecl;
		func_decl GeDecl;
		func_decl EqDecl;
		vector<expr>* pointers;
		map<std::string,vector<expr>*> arrayVariable2arrayLength;
		Z3Coding(context& ctx,Preprocess * preprocess):c(ctx),_ret(c),_error(c),_nil(c),TRUE(c),FALSE(c),_phi(c)
		,LtDecl(c),LeDecl(c),GtDecl(c),GeDecl(c),EqDecl(c)
		{
			this->preprocess=preprocess;
			pointers=new vector<expr>();
			_error=c.int_const("_error");
			_nil=c.bool_const("_nil");
			TRUE=c.bool_val(true);
			FALSE=c.bool_val(false);
			_phi=c.function("phi",c.int_sort(),c.int_sort(),c.int_sort(),c.bool_sort());
			expr i=c.int_const("i");
			expr le=i<=i;
			expr lt=i<i;
			expr ge=i>=i;
			expr gt=i>i;
			expr eq=i==i;
			LeDecl=le.decl();
			LtDecl=lt.decl();
			GtDecl=gt.decl();
			GeDecl=ge.decl();
			EqDecl=eq.decl();
			
		}
		map<std::string,expr> * getMemoryUnits(){
			if(setRet==true){
				addMemoryUnit(_ret);
			}
			if(preprocess->isNeedToGhost){
				for(expr e:*pointers){
					expr tmp=getPointerBase(e);
					addMemoryUnit(tmp);
					tmp=getPointerIndex(e);
					addMemoryUnit(tmp);
				}
			}
			
			return &memoryUnits;	
			
			
		}
		std::string toStringMemoryUnits(){
			std::string ret="";
			for(auto it=memoryUnits.begin();it!=memoryUnits.end();it++){
				std::pair<std::string,z3::expr> p=(std::pair<std::string,z3::expr>) *it;
				std::string memoryUnitName=Z3_ast_to_string(c,p.second);
				ret+=memoryUnitName+";";
			}
			return ret;
		}
		/**
		 * @brief cons is const, if old isin cons, return new name ;else return old
		 * @param cons 
		 * @param old
		 * @return 
		 */
		expr rename(vector<expr> *cons,expr old){
			expr tmp=old;
			while(isIn(tmp,cons)){
				std::string oldname=tmp.decl().name().str();
				z3::sort ty=tmp.get_sort();
				std::string newname=oldname+"_new";
				tmp=c.constant(newname.c_str(),ty);
			}
			return tmp;
		}
		bool isIn(expr e,vector<expr> * exprs){
//			std::string ename=Z3_ast_to_string(c,e);
			for(expr ele: *exprs){
//				std::string name=Z3_ast_to_string(c,ele);
				if(equal(e,ele)){
					return true;
				}
			}
			return false;
		}
		/**
		  \brief Simple function that tries to prove the given conjecture using the following steps:
		  1- create a solver
		  2- assert the negation of the conjecture
		  3- checks if the result is unsat.
		  */
		proved_result prove(expr conjecture) {
			solver s(c);
			s.add(!conjecture);
			check_result r=s.check();
			if(r==check_result::unsat){
				return proved_result::proved;
			}
			else if(r==check_result::sat){
				return proved_result::unproved;
			}
			else{
				return proved_result::unknown;
			}
			/*std::cout << "conjecture:\n" << conjecture << "\n";
			  if (s.check() == unsat) {
			  std::cout << "proved" << "\n";
			  return unsat;
			  }
			  else {
			  std::cout << "failed to prove" << "\n";
			  std::cout << "counterexample:\n" << s.get_model() << "\n";
			  }*/
		}
		/**
		 * @brief tries to prove the given assert under the pre_state Pre
		 * @param Pre
		 * @param assert
		 */
		proved_result prove(vector<expr> *Pre,expr assert) {
			expr conjecture(c);
			conjecture=!assert;
			for(auto it=Pre->begin();it!=Pre->end();it++){
				expr e=*it;
				conjecture=e&&conjecture;
			}
			solver s(c);
			s.add(conjecture);
//			std::cout<<conjecture<<std::endl;
			check_result r=s.check();
			
			if(r==check_result::unsat){
				return proved_result::proved;
			}
			else if(r==check_result::sat){
				return proved_result::unproved;
			}
			else{
				return proved_result::unknown;
			}
		}
		
		check_result satisfy(expr conjecture) {
			solver s(c);
			s.add(conjecture);
			return s.check();
		}
		check_result satisfy(vector<expr> *Pre,expr assert) {
			expr conjecture(c);
			conjecture=assert;
			for(auto it=Pre->begin();it!=Pre->end();it++){
				expr e=*it;
				conjecture=e&&conjecture;
			}
			return satisfy(conjecture);
		}
		expr substitute(expr &e, expr from, expr to){
			expr new_e(c);
			Z3_ast _from[] = { from };
			Z3_ast _to[]   = { to };
			new_e = to_expr(c, Z3_substitute(c, e, 1, _from, _to));
			return new_e;
		}
		expr substitute_var(context &c,expr e, expr to){
			expr new_e(c);
			Z3_ast _to[]   = { to };
			new_e = to_expr(c, Z3_substitute_vars(c, e, 1, _to));
			return new_e;
		}
		/*expr meet(expr e1,expr e2){
			tactic qe(c, "ctx-solver-simplify");
			goal g(c);
			g.add(e1||e2);
			//expr res(c);
			apply_result result_of_elimination = qe.apply(g);
			goal result_goal = result_of_elimination[0];
			return result_goal.as_expr();
		}*/
		expr meet(expr e1,expr e2){
			vector<expr> * tmp=new vector<expr>();
			tmp->push_back(e1);
			//e1=>e2
			if(prove(tmp,e2)==proved_result::proved){
				return e2;
			}
			tmp->clear();
			tmp->push_back(e2);
			//e2=>e1
			if(prove(tmp,e1)==proved_result::proved){
				return e1;
			}
			return _error;
		}
		
		bool imply(expr e1,expr e2){
			vector<expr> * tmp=new vector<expr>();
			tmp->push_back(e1);
			//e1=>e2
			if(prove(tmp,e2)==proved_result::proved){
				return true;
			}
			return false;
		}
		bool morePower_equal(expr e1,expr e2){
			tactic qe(c, "ctx-solver-simplify");
			goal g(c);
			g.add(e1==e2);
			//expr res(c);
			apply_result result_of_elimination = qe.apply(g);
			goal result_goal = result_of_elimination[0];
			expr result=result_goal.as_expr();
			if(eq(result,c.bool_val(true))){
				return true;
			}
			return false;
		}
		bool power_equal(expr e1,expr e2){
			expr result=(e1==e2).simplify();
			if(eq(result,c.bool_val(true))){
				return true;
			}
			return false;
		}
		bool isIdenticalEquation(expr formula){
			tactic qe(c, "ctx-solver-simplify");
			goal g(c);
			
			if(formula.is_quantifier()){
				expr forallBody=getQuantifierFormulaBody(formula);
				expr tmp=simplify(forallBody);
//				std::string str=Z3_ast_to_string(c,tmp);
				if(equal(tmp,TRUE) /*str=="true"*/){
					return true;
				}
				return false;
			}
			g.add(formula);
			apply_result result_of_elimination = qe.apply(g);
			goal result_goal = result_of_elimination[0];
			expr ret=result_goal.as_expr();
//			std::string str=Z3_ast_to_string(c,ret);
			if(equal(ret,TRUE)){
				return true;
			}
			return false;
		}
		expr simplify_simple(expr e){
			
			if(e.is_quantifier()){
				expr forallBody=getQuantifierFormulaBody(e);
				expr tmp=simplify_simple(forallBody);
				if(equal(tmp,TRUE)){
					return c.bool_val("true");
				}
				else if(equal(tmp,TRUE)/*str=="false"*/){
					return c.bool_val("false");
				}
				return e;
			}
			
			expr ret=e.simplify();
			if(equal(ret,TRUE)/*str=="true"*/){
				return c.bool_val("true");
			}
			else if(equal(ret,TRUE)/*str=="false"*/){
				return c.bool_val("false");
			}
		
			if(ret.is_app()&&ret.decl().name().str()=="not"){
				ret=mySimplify(ret);
				if(ret.is_app()&&ret.decl().name().str()=="not"){
					if(!(ret.arg(0).is_app()&&ret.arg(0).decl().name().str()=="=")){
						std::cerr<<"Z3Coding:simplify_simple: we can not simplify "<<e<<std::endl;
					}
					return e;
				}
				else{
					return ret;
				}
			}
			else{
				return ret;
			}
		}
		
		expr simplify(expr e){
			if(!e.is_bool()) return e;
			tactic qe(c, "ctx-solver-simplify");
			goal g(c);
			if(isPhiFormula(e)){
				return e;
			}
			
			if(isForAllFormula(e)){
				expr forallBody=getQuantifierFormulaBody(e);
				expr tmp=simplify(forallBody);
//				std::string str=Z3_ast_to_string(c,tmp);
				if(equal(tmp,TRUE)/*str=="true"*/){
					return c.bool_val("true");
				}
				else if(equal(tmp,TRUE)/*str=="false"*/){
					return c.bool_val("false");
				}
				expr begin=getQuantifierBegin(e);
				expr end=getQuantifierEnd(e);
				if(equal(begin,end)) return c.bool_val("true");
				
				return e;
			}
			
			g.add(e);
			//expr res(c);
			apply_result result_of_elimination = qe.apply(g);
			goal result_goal = result_of_elimination[0];
			expr ret=result_goal.as_expr();
//			std::string str=Z3_ast_to_string(c,ret);
			if(equal(ret,TRUE)/*str=="true"*/){
				return c.bool_val("true");
			}
			else if(equal(ret,TRUE)/*str=="false"*/){
				return c.bool_val("false");
			}
		
			/*if(ret.is_app()&&ret.decl().name().str()=="not"){
				ret=mySimplify(ret);
				if(ret.is_app()&&ret.decl().name().str()=="not"){
					if(!(ret.arg(0).is_app()&&ret.arg(0).decl().name().str()=="=")){
						//std::cerr<<"Z3Coding:simplify: we can not simplify "<<e<<std::endl;
					}
					return e;
				}
				else{
					return ret;
				}
			}
			else{
				return ret;
				
			}*/
			if(e.is_app()&&e.decl().name().str()=="not"){
				ret=mySimplify(e);
				if(ret.is_app()&&ret.decl().name().str()=="not"){
					if(!(ret.arg(0).is_app()&&ret.arg(0).decl().name().str()=="=")){
						//std::cerr<<"Z3Coding:simplify: we can not simplify "<<e<<std::endl;
					}
					return e;
				}
				else{
					return ret;
				}
			}
			else{
				return e;
				
			}
			cout<<"end------------"<<std::endl;
		}
		
		bool allIsBoolSort(vector<expr> * formulas){
			for(expr f: *formulas){
				if(!f.is_bool()){
					return false;
				}
			}
			return true;
		}
		bool mostPower_equal(expr e1,expr e2){
			expr e=e1==e2;
			vector<expr> *tmp=new vector<expr>();
			if(prove(tmp,e)==proved_result::proved){
				return true;
			}
			return false;
		}
		/**
		 * @brief pre: f and all element of formulas is bool sort
		 * @param f
		 * @param formulas
		 * @return 
		 */
		bool formulaIsIn(expr f, vector<expr> * formulas){
			/*for(expr ele: * formulas){
				expr eq=f==ele;
				if(equal(simplify(eq),TRUE)){
					return true;
				}
			}
			return false;*/
			
			if(isForAllFormula(f)){
				if(isIn(f,formulas)){
					return true;
				}
			}
			for(expr ele: * formulas){
				if(isForAllFormula(f)&&isSimpleFormula(ele)) return false;
				if(isForAllFormula(ele)&&isSimpleFormula(f)) return false;
				if(isForAllFormula(f)&&isForAllFormula(ele)){
					if(equal(f.body().arg(0),ele.body().arg(0))){
						if(mostPower_equal(getQuantifierFormulaBody(f),getQuantifierFormulaBody(ele))){
							return true;
						}
					}
					return false;
				}
				if(mostPower_equal(f,ele)){
					return true;
				}
			}
			return false;
		}
		/**
		 * @brief element of formulas must be bool sort,elimination of equivalent formula in formulas
		 * @param formulas
		 * @return 
		 */
		vector<expr> * simplify(vector<expr> * formulas){
			if(!allIsBoolSort(formulas)){
				std::cerr<<"Z3Coding:simplify: somethging is wrong"<<std::endl;
				return formulas;
			}
			
			vector<expr> *simplifyformulas1=new vector<expr>();
			for(expr ele: * formulas){
				ele=simplify(ele);

//				std::string str=Z3_ast_to_string(c,ele);
				if(!equal(ele,TRUE) /*!(str=="true")*/){
					simplifyformulas1->push_back(ele);
				}
			}
			vector<expr> *simplifyformulas2=new vector<expr>();
			for(expr f: *simplifyformulas1){
				if(!isIn(f,simplifyformulas2)/*!formulaIsIn(f,simplifyformulas2)*/){
					simplifyformulas2->push_back(f);
				}
			}
			return simplifyformulas2;
			
		}
		
		
			/**
		 * @brief element of formulas must be bool sort,elimination of equivalent formula in formulas
		 * @param formulas
		 * @return 
		 */
		vector<expr> * morePower_simplify(vector<expr> * formulas){
			if(!allIsBoolSort(formulas)){
				std::cerr<<"Z3Coding:simplify: somethging is wrong"<<std::endl;
				return formulas;
			}
			
			vector<expr> *simplifyformulas1=new vector<expr>();
			for(expr ele: * formulas){

				ele=simplify(ele);

//				std::string str=Z3_ast_to_string(c,ele);
				if(!equal(ele,TRUE)){
					simplifyformulas1->push_back(ele);
				}
			}
			vector<expr> *simplifyformulas2=new vector<expr>();
			for(expr f: *simplifyformulas1){
				if(!formulaIsIn(f,simplifyformulas2)){
					simplifyformulas2->push_back(f);
				}
			}
			return simplifyformulas2;
			
		}
		
		std::string toString(const clang::Stmt* clangStmt){
			LangOptions LO;
			LO.CPlusPlus=1; 
			std::string buffer;
			llvm::raw_string_ostream strout(buffer);
			clangStmt->printPretty(strout, nullptr, PrintingPolicy(LO));
			return strout.str();
		}
		std::string toString(const QualType qt){
			LangOptions LO;
			LO.CPlusPlus=1; 
			std::string buffer;
			llvm::raw_string_ostream strout(buffer);
			qt.print(strout,PrintingPolicy(LO));
			return strout.str();
		}
		
		std::string toString(vector<z3::expr>* exprs){
			if(exprs==nullptr) return "";
			std::string ret="";
			for(auto it=exprs->begin();it!=exprs->end();it++){
				z3::expr e=(z3::expr) *it;
				std::string eName=Z3_ast_to_string(c,e);
				ret+=eName+"; ";
				if(e.is_quantifier()){
					ret+="\n";
				}
			}
			return ret;
		}
		/**
		 * @brief define the format of our quantifier_formula
		 * 			forall i, extendFormula&&begin<=i&&i<end&&end%step=0 => p(i) 
		 * 			p can be simple formula or quantifier_formula
		 * 			extendFormula may be nil
		 * @param forallFormula
		 * @return 
		 */
		bool check_quantifier_formula(expr forallFormula){
			return forallFormula.is_quantifier()&&check_formula(forallFormula);
		}
		/**
		 * @brief define the format of our phi_formula
		 * 			phiFormula: phi_index
		 * @param phiFormula
		 * @return 
		 */
		bool check_phi_formula(expr phiFormula){
			if(phiFormula.is_app()){
//				std::string str=Z3_ast_to_string(c,phiFormula);
//				std::size_t found=str.find("phi_");
//				if (found!=std::string::npos){
//					return true;
//				}
				if(Z3_is_eq_func_decl(c,phiFormula.decl(),_phi)){
					return true;
				}
			}
			return false;
		}
		
		expr constructPhiFormula(expr index,expr init,expr step){
			return _phi(index,init,step);
		}
		
//		expr constructForAllFormula(expr quantifier, expr beginFormula,expr endFormula, expr step, expr body){
//			return forall(quantifier,implies(beginFormula&&endFormula&&to_expr(c,Z3_mk_mod(c,quantifier,step))==0,body));
//		}
//		expr constructForAllFormula(expr quantifier, expr extendFormula,expr beginFormula,expr endFormula, expr step, expr body){
//			
//			return forall(quantifier,implies(extendFormula&&beginFormula&&endFormula&&to_expr(c,Z3_mk_mod(c,quantifier,step))==0,body));
//		}
		expr constructForAllFormula(expr quantifier, expr beginFormula,expr endFormula, expr stepFormula, expr body){
			return forall(quantifier,implies(beginFormula&&endFormula&&stepFormula,body));
		}
		expr constructForAllFormula(expr quantifier, expr extendFormula,expr beginFormula,expr endFormula, expr stepFormula, expr body){
			
			return forall(quantifier,implies(extendFormula&&beginFormula&&endFormula&&stepFormula,body));
		}
		expr constructForAllFormula_step(expr quantifier, expr extendFormula,expr beginFormula,expr endFormula, expr step,expr indexinit, expr body){		
			return forall(quantifier,implies(extendFormula&&beginFormula&&endFormula&&to_expr(c,Z3_mk_mod(c,quantifier-indexinit,step))==0,body));
		}
		expr constructForAllFormula_step(expr quantifier,expr beginFormula,expr endFormula, expr step,expr indexinit, expr body){		
			return forall(quantifier,implies(beginFormula&&endFormula&&to_expr(c,Z3_mk_mod(c,quantifier-indexinit,step))==0,body));
		}
		expr getPhiIndex(expr phiFormula){
			if(check_phi_formula(phiFormula)){
//				std::string str=Z3_ast_to_string(c,phiFormula);
//				std::string indexName=str.substr(4,str.size()-4);
//				return c.int_const(indexName.c_str());
				return phiFormula.arg(0);
			}
			std::cerr<<"Z3Coding:getPhiIndex: somethging is wrong"<<std::endl;
			return c.int_const("__error");
		}
		
		expr getPhiIndexInit(expr phiFormula){
			if(check_phi_formula(phiFormula)){
				return phiFormula.arg(1);
			}
			std::cerr<<"Z3Coding:getPhiIndexInit: somethging is wrong"<<std::endl;
			return _error;
		}
		expr getPhiIndexStep(expr phiFormula){
			if(check_phi_formula(phiFormula)){
				return phiFormula.arg(2);
			}
			std::cerr<<"Z3Coding:getPhiIndexStep: somethging is wrong"<<std::endl;
			return _error;
		}
		
		
//		/**
//		 * @brief after indexupdate stmt , constructForAllFormula
//		 * 			indexupdate has been regularization as index=index+step
//		 * @param indexUpdateStmt
//		 * @param init
//		 * @param body: forallformula body
//		 * @return ForAllFormula: step<0 => (forall x. init<=x&&x<index&&index%step=0=>)
//		 */
//		expr constructForAllFormula(vector<expr> * Pre,expr indexUpdateStmt,expr init, expr body){
//			
//		}
		
		expr getQuantifierFormulaBody(expr forallFormula){
			expr quantifier=getQuantifier(forallFormula);
			expr body=forallFormula.body();
			expr newbody=substitute_var(c,body,quantifier);
			expr mybody=newbody.arg(1);//interval formula => mybody
			return mybody;
		}
		
		expr getQuantifierStep(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierStep: can not get QuantifierStep from " <<forallFormula<<std::endl;
				return _error;
			}
			expr body=forallFormula.body();
			expr interval=body.arg(0);
			expr stepformula=interval.arg(1);
			expr step=stepformula.arg(0).arg(1);
			return step;
		}
		expr getQuantifierStepFormula(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierStep: can not get QuantifierStep from " <<forallFormula<<std::endl;
				return _error;
			}
			expr quantifier=getQuantifier(forallFormula);
			expr body=substitute_var(c,forallFormula.body(),quantifier);
			expr interval=body.arg(0);
			expr stepformula=interval.arg(1);
			return stepformula;
		}
		
		vector<expr>* getAllQuantifierStep(expr forallFormula){
			vector<expr>* steps=new vector<expr>();
			expr tmp=forallFormula;
			while(tmp.is_quantifier()){
				expr step=getQuantifierStep(tmp);
				steps->push_back(step);
				tmp=getQuantifierFormulaBody(tmp);
			}
			return steps;
		}
	
		expr getQuantifierEnd(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierStep: can not get End from " <<forallFormula<<std::endl;
				return _error;
			}
			expr body=forallFormula.body();
			expr interval=body.arg(0);
			expr extendIndexAndbeginEndformula=interval.arg(0);
			expr endFormula=extendIndexAndbeginEndformula.arg(1); 
			expr end=endFormula.arg(1);
			return end;
		}
		expr getQuantifierEndFormula(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierStep: can not get EndFormula from " <<forallFormula<<std::endl;
				return _error;
			}
			expr quantifier=getQuantifier(forallFormula);
			expr body=substitute_var(c,forallFormula.body(),quantifier);
			expr interval=body.arg(0);
			expr extendIndexAndbeginEndformula=interval.arg(0);
			expr endFormula=extendIndexAndbeginEndformula.arg(1); 
			return endFormula;
		}
		/*vector<expr>* getAllQuantifierEnd(expr forallFormula){
			vector<expr>* ends=new vector<expr>();
			expr tmp=forallFormula;
			while(tmp.is_quantifier()){
				expr end=getQuantifierEnd(tmp);
				ends->push_back(end);
				tmp=getQuantifierFormulaBody(tmp);
			}
			return ends;
		}*/
		
		vector<expr>* getAllQuantifierEndFormula(expr forallFormula){
			vector<expr>* endformulas=new vector<expr>();
			expr tmp=forallFormula;
			while(tmp.is_quantifier()){
				expr endformula=getQuantifierEndFormula(tmp);
				endformulas->push_back(endformula);
				tmp=getQuantifierFormulaBody(tmp);
			}
			return endformulas;
		}
		
		
		expr getQuantifierBegin(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierStep: can not get Begin from " <<forallFormula<<std::endl;
				return _error;
			}
			expr body=forallFormula.body();
			expr interval=body.arg(0);
			expr extendIndexAndbeginEndformula=interval.arg(0);
			expr extendIndexAndBeginFormula=extendIndexAndbeginEndformula.arg(0); 
			if(extendIndexAndBeginFormula.decl().name().str()=="and"){
				expr beginFormula=extendIndexAndBeginFormula.arg(1);
				expr begin=beginFormula.arg(0);
				return begin;
			}
			else {
				expr begin=extendIndexAndBeginFormula.arg(0);
				return begin;
			}
		}
		expr getQuantifierBeginFormula(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierStep: can not get BeginFormula from " <<forallFormula<<std::endl;
				return _error;
			}
			expr quantifier=getQuantifier(forallFormula);
			expr body=substitute_var(c,forallFormula.body(),quantifier);
			
			expr interval=body.arg(0);
			expr extendIndexAndbeginEndformula=interval.arg(0);
			expr extendIndexAndBeginFormula=extendIndexAndbeginEndformula.arg(0); 
			if(extendIndexAndBeginFormula.decl().name().str()=="and"){
				expr beginFormula=extendIndexAndBeginFormula.arg(1);
				return beginFormula;
			}
			else {
				return extendIndexAndBeginFormula;
			}
		}
		
		expr getQuantifierExtendFormula(expr forallFormula){
			if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifierExtendFormula: can not get ExtendFormula from " <<forallFormula<<std::endl;
				return _error;
			}
			expr quantifier=getQuantifier(forallFormula);
			expr body=substitute_var(c,forallFormula.body(),quantifier);
			
			expr interval=body.arg(0);
			expr extendIndexAndbeginEndformula=interval.arg(0);
			expr extendIndexAndBeginFormula=extendIndexAndbeginEndformula.arg(0); 
			if(extendIndexAndBeginFormula.decl().name().str()=="and"){
				expr extendFormula=extendIndexAndBeginFormula.arg(0);
				return extendFormula;
			}
			else {
				//std::cerr<<"Z3Coding:getQuantifierExtendFormula: can not get ExtendFormula from " <<forallFormula<<std::endl;
				return _error;
			}
		}
		/**
		 * @brief check if e is valid
		 * @param e
		 * @return 
		 */
		bool checkError(expr e){
			std::string ename=Z3_ast_to_string(c,e);
			std::string errorname=Z3_ast_to_string(c,_error);
			return ename==errorname;
		}
		/*vector<expr>* getAllQuantifierBegin(expr forallFormula){
			vector<expr>* begins=new vector<expr>();
			expr tmp=forallFormula;
			while(tmp.is_quantifier()){
				expr begin=getQuantifierEnd(tmp);
				begins->push_back(begin);
				tmp=getQuantifierFormulaBody(tmp);
			}
			return begins;
		}*/
		vector<expr>* getAllQuantifierBeginFormula(expr forallFormula){
			vector<expr>* beginFormulas=new vector<expr>();
			expr tmp=forallFormula;
			while(tmp.is_quantifier()){
				expr beginFormula=getQuantifierBeginFormula(tmp);
				beginFormulas->push_back(beginFormula);
				tmp=getQuantifierFormulaBody(tmp);
			}
			return beginFormulas;
		}
		z3::symbol getQuantifier_name(expr forallFormula){
			/*if(!check_quantifier_formula(forallFormula)){
				std::cerr<<"Z3Coding:getQuantifier: can not get quantifier from " <<forallFormula<<std::endl;
				return c.int_const("_error");
			}
			expr body=forallFormula.body();
			expr interval=body.arg(0);
			expr beginEndformula=interval.arg(0);
			expr beginFormula=beginEndformula.arg(0); 
			expr quantifier=beginFormula.arg(1);
			if(!quantifier.is_var()){
				std::cerr<<"Z3Coding:getQuantifier: "<<quantifier<< "is not var"<<std::endl;
				return c.int_const("_error");
			}
			return quantifier;*/
			if(!forallFormula.is_quantifier()){
				std::cerr<<"Z3Coding:getQuantifier_name: can not get quantifier from " <<forallFormula<<std::endl;
				return c.str_symbol("_error");
			}
			z3::symbol sym(c,Z3_get_quantifier_bound_name(c,forallFormula,0));
			return sym;
		}
		
		z3::sort getQuantifier_sort(expr forallFormula){
			if(!forallFormula.is_quantifier()){
				std::cerr<<"Z3Coding:getQuantifier_sort: can not get quantifier from " <<forallFormula<<std::endl;
				return c.int_sort();
			}
			z3::sort s(c,Z3_get_quantifier_bound_sort(c,forallFormula,0));
			return s;
		}
		expr getQuantifier(expr forallFormula){
			if(!forallFormula.is_quantifier()){
				std::cerr<<"Z3Coding:getQuantifier: can not get quantifier from " <<forallFormula<<std::endl;
				return _error;
			}
			z3::symbol sym(c,Z3_get_quantifier_bound_name(c,forallFormula,0));
			z3::sort s(c,Z3_get_quantifier_bound_sort(c,forallFormula,0));
			return c.constant(sym,s);
		}
		vector<expr>* getAllQuantifier(expr forallFormula){
			vector<expr>* quantifiers=new vector<expr>();
			expr tmp=forallFormula;
			while(tmp.is_quantifier()){
				expr quantifier=getQuantifier(tmp);
				quantifiers->push_back(quantifier);
				tmp=getQuantifierFormulaBody(tmp);
			}
			return quantifiers;
		}
		
		void maintainMemoryUnits(){
			for(auto it=varDeclToZ3Expr.begin();it!=varDeclToZ3Expr.end();it++){
				std::pair<const ValueDecl *,z3::expr> p=*it;
				std::string memoryUnitName=Z3_ast_to_string(c,p.second);
				if(memoryUnits.count(memoryUnitName)<=0){
					memoryUnits.insert(std::pair<std::string,z3::expr>(memoryUnitName,p.second));
				}
			}
		}
		/**
		 * @brief 
		 * @param e
		 * @return true if e is Array([exp])+
		 */
		/*bool isArrayAcess(expr &e){
		  std::string s=Z3_ast_to_string(c,e);
		  return s.compare(0,7,"(select")==0;
		  }*/
		bool isArrayAcess(expr &e){
			if(e.is_app()){
				return e.decl().name().str()=="select";
			}
			return false;
		}

		/*bool isSimpleFormula(expr formula){
			return !formula.is_quantifier();
		}*/
		bool isForAllFormula(expr formula){
			return formula.is_quantifier();
		}
		bool isPhiFormula(expr phiFormula){
			return check_phi_formula(phiFormula);
		}
		bool isSimpleFormula(expr simpleFormula){
			return !isPhiFormula(simpleFormula)&&!isForAllFormula(simpleFormula)&&!isOrFormula(simpleFormula);
		}
		/**
		 * @brief 
		 * @param e must be array acess
		 * @return 
		 */
		expr getArrayBase(expr &e){
			if(e.is_const()&&e.is_array()){
				//std::cout <<e << " is_array \n";
				return e;
			}
			else if(isArrayAcess(e)){
				//std::cout <<e << " is_array acess \n";
				expr arg0=e.arg(0);
				return getArrayBase(arg0);
			}
			else {
				std::cerr<<"Z3Coding:abstractArrayBase: can not abstract array base from " <<e<<std::endl;
				return _error;
			}
		}
		/**
		 * @brief abstract all MemoryUnits from formula
		 * @param formula
		 * @return 
		 */
		vector<expr> * getMemoryUnits(expr e){
			vector<expr> * memoryUnits=new vector<expr>();
			if(e.is_const()){
				memoryUnits->push_back(e);
				return memoryUnits;
			}
			else if(isArrayAcess(e)){
				memoryUnits->push_back(e);
				vector<expr> * argmemoryUnits=getMemoryUnits(e.arg(0));
				pushAToB(argmemoryUnits,memoryUnits);
				argmemoryUnits=getMemoryUnits(e.arg(1));
				pushAToB(argmemoryUnits,memoryUnits);
				return memoryUnits;
			}
			else if(e.is_quantifier()){
				std::cerr<<"Z3Coding:abstractMemoryUnits: we can not abstract memoryUnits from quantifier formula"<<std::endl;
				return memoryUnits;
			}
			else if(e.is_var()){
				return memoryUnits;
			}
			for(unsigned i=0;i<e.num_args();i++){
				vector<expr> * argmemoryUnits=getMemoryUnits(e.arg(i));
				pushAToB(argmemoryUnits,memoryUnits);
			}
			return memoryUnits;
		}
		
		/**
		 * @brief abstract all ArrayAcess from formula
		 * 			index of ArrayAcess may be var
		 * @param e
		 * @return 
		 */
		vector<expr> * getArrayAcess(expr e){
			vector<expr> * arrayAcesses=new vector<expr>();
			if(e.is_const()){
				return arrayAcesses;
			}
			else if(isArrayAcess(e)){
				arrayAcesses->push_back(e);
				vector<expr> * argmemoryUnits=getArrayAcess(e.arg(0));
				pushAToB(argmemoryUnits,arrayAcesses);
				argmemoryUnits=getArrayAcess(e.arg(1));
				pushAToB(argmemoryUnits,arrayAcesses);
				return arrayAcesses;
			}
			else if(e.is_quantifier()){
				z3::symbol quantifier_name=getQuantifier_name(e);
				z3::sort quantifier_type=getQuantifier_sort(e);
				expr quantifier=c.constant(quantifier_name,quantifier_type);
				
				expr body=e.body();
				expr newbody=substitute_var(c,body,quantifier);
				arrayAcesses=getArrayAcess(newbody);
				return arrayAcesses;
			}
			else if(e.is_var()){
				return arrayAcesses;
			}
			for(unsigned i=0;i<e.num_args();i++){
				vector<expr> * argmemoryUnits=getArrayAcess(e.arg(i));
				pushAToB(argmemoryUnits,arrayAcesses);
			}
			return toSet(arrayAcesses);
		}
		void addMemoryUnits(vector<expr>* memoryUnits){
			for(expr e:*memoryUnits){
				addMemoryUnit(e);
			}
		}
		
		/**
		 * @brief such as: A[A[i]]+B[i+j][k]>0, return A[A[i]],B[i+j][k]
		 * @param e
		 * @return 
		 */
		vector<expr> * getArrayAcessMemoryUnit(expr e){
			vector<expr> * arrayAcesses=new vector<expr>();
			if(e.is_const()){
				return arrayAcesses;
			}
			else if(isArrayAcess(e)){
				arrayAcesses->push_back(e);
				return arrayAcesses;
			}
			else if(e.is_quantifier()){
				z3::symbol quantifier_name=getQuantifier_name(e);
				z3::sort quantifier_type=getQuantifier_sort(e);
				expr quantifier=c.constant(quantifier_name,quantifier_type);
				
				expr body=e.body();
				expr newbody=substitute_var(c,body,quantifier);
				arrayAcesses=getArrayAcessMemoryUnit(newbody);
				return arrayAcesses;
			}
			else if(e.is_var()){
				return arrayAcesses;
			}
			for(unsigned i=0;i<e.num_args();i++){
				vector<expr> * argmemoryUnits=getArrayAcessMemoryUnit(e.arg(i));
				pushAToB(argmemoryUnits,arrayAcesses);
			}
			return toSet(arrayAcesses);
		}
		
		/**
		 * @brief get consts and Quantifier
		 * @param f
		 * @return 
		 */
		vector<expr>* getConstsWithQuantifier(expr e){
			vector<expr> *consts=new vector<expr>();
			map<unsigned,expr> *constsMap=new map<unsigned,expr>();
			if(e.is_const()){
				if(e.is_numeral()){
					return consts;
				}
				consts->push_back(e);
//				std::string eName=Z3_ast_to_string(c,e);
				constsMap->insert(std::pair<unsigned,expr>(e.hash(),e));
				return consts;
			}
			else if(e.is_quantifier()){
				expr quantifier=getQuantifier(e);
				expr body=substitute_var(c,e.body(),quantifier);
				consts=getConstsWithQuantifier(body);
				return consts;
			}
			if(e.is_var()){
				return consts;
			}
			for(unsigned i=0;i<e.num_args();i++){
				vector<expr> *argconsts=getConstsWithQuantifier(e.arg(i));
				for(auto it=argconsts->begin();it!=argconsts->end();it++){
					expr con=*it;
//					std::string conName=Z3_ast_to_string(c,con);
					if(constsMap->count(con.hash())<=0){
						consts->push_back(con);
						constsMap->insert(std::pair<unsigned,expr>(con.hash(),con));
					}
				}
			}
			return consts;
		}
		
		vector<expr> * getAllCons(vector<expr> *exprs){
			vector<expr> * ret=new vector<expr>();
			for(expr e: *exprs){
				vector<expr> * tmp=getConsts(e);
				pushAToB(tmp,ret);
			}
			return toSet(ret);
		}
		/**
		 * @brief arrayAcess must be array acess
		 * @param arrayAcess
		 * @param k
		 * @return 
		 */
		expr getFormerKDimension(expr arrayAcess,int k){
			if(isArrayAcess(arrayAcess)){
				int d=getArrayAcessDimension(arrayAcess);
				if(d<k){
					std::cerr<<"Z3Coding:getArrayAcessKthIdx: can not get the former"<<k<<" dimension expr of "<<arrayAcess<<std::endl;
					return _error;
				}
				expr formerKDimExpr=arrayAcess;
				for(int i=0;i<d-k;i++){
					formerKDimExpr=arrayAcess.arg(0);
				}
				return formerKDimExpr;
			}
			else{
				std::cerr<<"Z3Coding:abstractFormerKDimension: "<<arrayAcess<<" must be arrayAcess"<<std::endl;
				return _error;
			}
		}
		vector<expr> * eliminateNotFormula(vector<expr> * formulas){
			vector<expr>* result=new  vector<expr>();
			for(expr f: *formulas){
				result->push_back(eliminateNotSimpleFormula(f));
			}
			return result;
		}
		/**
		 * @brief if e is not array acess,return 0;else return the Dimension of ArrayAcess e
		 * @param e
		 * @return 
		 */
		int getArrayAcessDimension(expr e){
			if(isArrayAcess(e)){
				return 1+getArrayAcessDimension(e.arg(0));	
			}
			else{
				return 0;
			}
		}
		vector<expr> * getArrayAcessIdxes(expr arrayAcess){
			vector<expr> * idxes=new vector<expr>();
			int d=getArrayAcessDimension(arrayAcess);
			expr formerarrayAcess=arrayAcess;
			std::vector<expr>::iterator it;
			for(int i=0;i<d;i++){
				it = idxes->begin();
				idxes->insert(it,formerarrayAcess.arg(1));
				formerarrayAcess=formerarrayAcess.arg(0);
			}
			return idxes;
		}
		expr getArrayAcessKthIdx(expr arrayAcess,int kth){
			vector<expr> * idxes=getArrayAcessIdxes(arrayAcess);
			if(idxes->size()<((unsigned long)kth)){
				std::cerr<<"Z3Coding:getArrayAcessKthIdx: can not get the "<<kth<<" dimension index of "<<arrayAcess<<std::endl;
				return _error;
			}
			return idxes->at(kth);
		}
		vector<expr>* getConsts(expr e){
			vector<expr> *consts=new vector<expr>();
			map<unsigned,expr> *constsMap=new map<unsigned,expr>();
			if(e.is_const()){
				if(e.is_numeral()){
					return consts;
				}
				consts->push_back(e);
//				std::string eName=Z3_ast_to_string(c,e);
				constsMap->insert(std::pair<unsigned,expr>(e.hash(),e));
				return consts;
			}
			else if(e.is_quantifier()){
				consts=getConsts(e.body());
				return consts;
			}
			if(e.is_var()){
				return consts;
			}
			for(unsigned i=0;i<e.num_args();i++){
				vector<expr> *argconsts=getConsts(e.arg(i));
				for(auto it=argconsts->begin();it!=argconsts->end();it++){
					expr con=*it;
//					std::string conName=Z3_ast_to_string(c,con);
					if(constsMap->count(con.hash())<=0){
						consts->push_back(con);
						constsMap->insert(std::pair<unsigned,expr>(con.hash(),con));
					}
				}
			}
			return consts;

		}
		/**
		 * @brief 
		 * @param e
		 * @return if e is const: x, return x'; if e is ArrayAcess:(select A exp), return (select A' exp) 
		 */
		expr prime(expr e){
			if(e.is_numeral()){
				return e;
			}
			if(e.is_const()){
				std::string e_prime_name=e.decl().name().str()+"__prime";
				expr e_prime=c.constant(e_prime_name.c_str(),e.get_sort());
				return substitute(e,e,e_prime);
			}
			else if(isArrayAcess(e)){
				expr arrayBase=getArrayBase(e);
				std::string arrayBase_prime_name=arrayBase.decl().name().str()+"__prime";
				expr arrayBase_prime=c.constant(arrayBase_prime_name.c_str(),arrayBase.get_sort());
				return substitute(e,arrayBase,arrayBase_prime);
			}
			else {
				std::cerr<<"Z3Coding:prime: We do not consider prime: "<<e<<std::endl;
				return _error;
			}
		}
		expr unprime(expr e){
			if(e.is_const()){
				std::size_t found = e.decl().name().str().find("__prime");
				if (found!=std::string::npos){
					int size=e.decl().name().str().size();
					int length=size-7;
					std::string name=e.decl().name().str().substr(0,length);
					return c.constant(name.c_str(),e.get_sort());
				}
				return e;
				
			}
			else if(isArrayAcess(e)){
				expr ret=e;
				vector<expr> *cons=getConsts(ret);
				for(expr con: *cons){
					if(isPrimedVariable(con)){
						ret=substitute(ret,con,unprime(con));
					}
				}
				return ret;
			}
			else {
				std::cerr<<"Z3Coding:unprime: We do not consider prime: "<<e<<std::endl;
				return e;
			}
		}
		
		/**
		 * @brief e.g. canonical simple formula not (a>b) to a<=b 
		 * @param exprs
		 * @return 
		 */
		vector<expr>* canonical(vector<expr>* formulas){
			vector<expr>* canonicalformulas=new vector<expr>();
			for(expr ele: *formulas){
				canonicalformulas->push_back(simplify(ele));
			}
			return canonicalformulas;
		}
		vector<expr>* eliminateIdenticalEquation(vector<expr>* formulas){
			vector<expr>* ret=new vector<expr>();
			for(expr f: *formulas){
				if(!isIdenticalEquation(f)){
					ret->push_back(f);
				}
			}
			return ret;
		}
		expr eliminateNotSimpleFormula(expr e){
			expr ret=mySimplify(e);
			return ret;
		}
		/**
		 * @brief 
		 * @param e
		 * @return true if e is x__prime
		 */
		bool isPrimedVariable(expr e){
			if(e.is_const()){ 
				std::size_t found = e.decl().name().str().rfind("__prime");
				if (found!=std::string::npos){
					return true;
				}
			}
			return false;
		}
		bool hasPrimedVariable(expr e){
			if(e.is_numeral()){
				return false;
			}
			if(e.is_const()){
				return isPrimedVariable(e);
			}
			if(e.is_quantifier()){
				return hasPrimedVariable(e.body());
			}
			if(e.is_var()){
				return false;
			}
			if(e.is_app()){
				int atrgsNum=e.num_args();
				if(atrgsNum>0){
					for(int i=0;i<atrgsNum;i++){
						expr arg=e.arg(i);
						if(hasPrimedVariable(arg)){
							return true;
						}
					}
					return false;
				}
				return false;
			}
			else{
				std::cerr<<"Z3Coding:hasPrimedVariable: something is wrong! "<<std::endl;
				return false;
			}
		}
		bool hasUnPrimedVariable(expr e){
			if(e.is_numeral()){
				return false;
			}
			if(e.is_const()){
				return !isPrimedVariable(e);
			}
			if(e.is_quantifier()){
				return hasUnPrimedVariable(e.body());
			}
			if(e.is_var()){
				return false;
			}
			if(e.is_app()){
				int atrgsNum=e.num_args();
				if(atrgsNum>0){
					for(int i=0;i<atrgsNum;i++){
						expr arg=e.arg(i);
						if(hasUnPrimedVariable(arg)){
							return true;
						}
					}
					return false;
				}
				return false;
			}
			else{
				std::cerr<<"Z3Coding:hasUnPrimedVariable: something is wrong! "<<std::endl;
				return false;
			}
		}
		void pushAToB(vector<expr> * & A,vector<expr> * & B){
			for(auto it=A->begin();it != A->end(); it++){
				expr t=*it;
				B->push_back(t);
			}
		}
		void addPointers(expr e){
			if(!isIn(e,pointers)){
				pointers->push_back(e);
			}
		}
		vector<expr> * clangBinaryOperatorToZ3Expr(clang::BinaryOperator * binaryOperator){
			vector<expr>* exprs=new vector<expr>();
			vector<expr>* lhss=clangExprToZ3Expr(binaryOperator->getLHS());
			vector<expr>* rhss=clangExprToZ3Expr(binaryOperator->getRHS());
			if(lhss==nullptr||rhss==nullptr||lhss->size()==0||rhss->size()==0){
				return nullptr;
			}
			
			expr lhs=lhss->back();lhss->pop_back();
			expr rhs=rhss->back();rhss->pop_back();
			if(!Z3_is_eq_sort(c,lhs.get_sort(),rhs.get_sort())){
				return nullptr;
			}
			//memoryUnits,just add select memory unit
			if(isArrayAcess(lhs)){
				addMemoryUnit(lhs);
			}
			if(isArrayAcess(rhs)){
				addMemoryUnit(rhs);
			}
			pushAToB(lhss,exprs);
			pushAToB(rhss,exprs);
			expr tmp(c);
			//std::cout<<lhs<<":"<<lhs.get_sort()<<" , "<<rhs<<":"<<rhs.get_sort()<<std::endl;
			switch(binaryOperator->getOpcode()){
				default:	
					std::cerr<<"Z3Coding:clangBinaryOperatorToZ3Expr: We do not consider processing binaryOperator: "<<binaryOperator->getOpcodeStr().data()<<std::endl;
					return nullptr;
				case BO_Mul 	://*
				    if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs*rhs);
					break;
				case BO_Div 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs/rhs);
					break;
				case BO_Rem	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(to_expr(c,Z3_mk_mod(c,lhs,rhs)));
					break;
				case BO_Add 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs+rhs);
					break;
				case BO_Sub 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs-rhs);
					break;
				case BO_LT 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs<rhs);
					break;
				case BO_GT 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs>rhs);
					break;
				case BO_LE 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs<=rhs);
					break;
				case BO_GE 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs>=rhs);
					break;
				case BO_EQ 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs==rhs);
					break;
				case BO_NE 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					exprs->push_back(lhs!=rhs);
					break;
				/*case BO_And 	:
					exprs->push_back(lhs&rhs);
					break;*/
				/*case BO_Or 	:
					exprs->push_back(lhs|rhs);
					break;*/
				case BO_LAnd 	:
					//exprs->push_back(lhs&&rhs);
					if(!(lhs.is_bool()||lhs.is_int())||!(rhs.is_bool()||rhs.is_int())) return nullptr;
					if(lhs.is_int()){
						lhs=lhs==0;
					}
					if(rhs.is_int()){
						rhs=rhs==0;
					}
					exprs->push_back(lhs&&rhs);
					break;
				case BO_LOr 	:
					if(!(lhs.is_bool()||lhs.is_int())||!(rhs.is_bool()||rhs.is_int())) return nullptr;
					if(lhs.is_int()){
						lhs=lhs==0;
					}
					if(rhs.is_int()){
						rhs=rhs==0;
					}
					exprs->push_back(lhs||rhs);
					break;
				case BO_Assign 	:
					if(isPointerType(binaryOperator->getLHS()->getType())){
						//isAssignedToPointer=true;
						if(preprocess->isNeedToGhost){
							if(isPointerType(binaryOperator->getRHS()->getType())){
								expr lhsBase=getPointerBase(lhs);
								expr rhsBase=getPointerBase(lhs);
								exprs->push_back(prime(lhsBase)==rhsBase);
								expr lhsIndex=getPointerIndex(lhs);
								expr rhsIndex=getPointerIndex(lhs);
								exprs->push_back(prime(lhsIndex)==rhsIndex);
								exprs->push_back(rhs);
								addPointers(lhs);
								addPointers(rhs);
							}
							else{
								return nullptr;
							}
						}
						else{
							exprs->push_back(prime(lhs)==rhs);
							exprs->push_back(rhs);
						}
					}
					else{
						exprs->push_back(prime(lhs)==rhs);
						exprs->push_back(rhs);
					}
					break;
				case BO_MulAssign 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					tmp=lhs*rhs;
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;
				case BO_DivAssign 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					tmp=lhs/rhs;
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;
				case BO_RemAssign		:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					tmp=to_expr(c,Z3_mk_mod(c,lhs,rhs));
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;
				case BO_AddAssign 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					tmp=lhs+rhs;
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;
				case BO_SubAssign 	:
					if(!lhs.is_int()||!rhs.is_int()) return nullptr;
					tmp=lhs-rhs;
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;
				/*case BO_AndAssign 	:
					tmp=lhs&rhs;
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;
				case BO_OrAssign 	:
					tmp=lhs|rhs;
					exprs->push_back(prime(lhs)==tmp);
					exprs->push_back(tmp);
					break;*/
			}
			return exprs;
		}
		expr getPointerBase(expr e){
			if(isPrimedVariable(e)){
				e=unprime(e);
				std::string eName=Z3_ast_to_string(c,e);
				std::string baseName=eName+"_initbase";
				expr arraybase=c.constant(baseName.c_str(),e.get_sort());
				return prime(arraybase);
			}
			else{
				std::string eName=Z3_ast_to_string(c,e);
				std::string baseName=eName+"_initbase";
				expr arraybase=c.constant(baseName.c_str(),e.get_sort());
				return arraybase;
			}
								
		}
		expr getPointerIndex(expr e){
			if(isPrimedVariable(e)){
				e=unprime(e);
				std::string eName=Z3_ast_to_string(c,e);
				std::string indexName=eName+"_index";
				expr arrayindex=c.int_const(indexName.c_str());
				return prime(arrayindex);
			}
			else{
				std::string eName=Z3_ast_to_string(c,e);
				std::string indexName=eName+"_index";
				expr arrayindex=c.int_const(indexName.c_str());
				return arrayindex;					
			}
		}
		bool isPointerIndex(expr e){
			if(e.is_const()){ 
				std::size_t found = e.decl().name().str().rfind("_index");
				if (found!=std::string::npos){
					return true;
				}
			}
			return false;
		}
		
		Sort* clangTypeToZ3Sort(QualType qt){
			QualType canonicalType=qt.getTypePtr()->getCanonicalTypeInternal();
			//std::cout<<" Type is: "<<toString(qt)<<std::endl;
			//std::cout<<" CanonicalType is: "<<toString(canonicalType)<<std::endl;
			if(canonicalType.getTypePtr()->isIntegerType()){
				return new Sort(c.int_sort());
			}
			if(canonicalType.getTypePtr()->isCharType()){
				return new Sort(c.int_sort());
			}
			else if(canonicalType.getTypePtr()->isBooleanType()){
				return new Sort(c.bool_sort());
			}
			else if(canonicalType.getTypePtr()->isArrayType()){
				const ArrayType * arraytype=(const ArrayType *)canonicalType.getTypePtr();
				
				Sort* tmp=clangTypeToZ3Sort(arraytype->getElementType());
				if(tmp!=nullptr){
					z3::sort elementSort=tmp->type;
					return new Sort(c.array_sort(c.int_sort(),elementSort));
				}
				return nullptr;
			}
			else if(canonicalType.getTypePtr()->isPointerType()){
				//we regard pointer type as array
				const PointerType * pt =(const PointerType *)canonicalType.getTypePtr();
				Sort* tmp=clangTypeToZ3Sort(pt->getPointeeType());
				if(tmp!=nullptr){
					z3::sort pointeeSort=tmp->type;
					return new Sort(c.array_sort(c.int_sort(),pointeeSort));
				}
				return nullptr;
				/*
				return nullptr;
				*/
			}
			else {
				std::cerr<<"Z3Coding:clangTypeToZ3Sort: We do not process type : "<<toString(qt)<<std::endl;
				return nullptr;
			}
		}
		
		
		expr clangCallExprToZ3Expr(clang::CallExpr * callexpr){
			return _error;
		}
		
		bool setArrayVariable2ArrayLength(std::string varName,QualType qt){
			QualType canonicalType=qt.getTypePtr()->getCanonicalTypeInternal();
			const Type * arraytype=canonicalType.getTypePtr();
			if(!arraytype->isArrayType()) return false;
			vector<expr>* sizes=getArrayTypeLength(arraytype);
			if(sizes==nullptr) return false;
			arrayVariable2arrayLength.insert(std::pair<std::string,vector<expr>*>(varName,sizes));	
			return true;
		}
		vector<expr>* getArrayTypeLength(const Type * t){
			vector<expr>* result=new vector<expr>();
			if(!t->isArrayType()) return result;
			const ArrayType * arraytype=(const ArrayType *)t;
			if(arraytype->isConstantArrayType()){
				const ConstantArrayType  * constantarraytype=(const ConstantArrayType *)arraytype;
				expr size=c.int_val((__int64)constantarraytype->getSize().getSExtValue());
				result->push_back(size);
			}
			if(arraytype->isVariableArrayType()){
				const VariableArrayType * variablearraytype=(const VariableArrayType *)arraytype;
				vector<expr> * tmp=this->clangExprToZ3Expr(variablearraytype->getSizeExpr());
				if(tmp==nullptr||tmp->size()==0) return nullptr;
				expr size=tmp->back();
				result->push_back(size);
			}
			if(arraytype->isIncompleteArrayType()){
				return nullptr;
			}
			vector<expr>* tmp=getArrayTypeLength(arraytype->getElementType().getCanonicalType().getTypePtr());
			if(tmp==nullptr) return nullptr;
			pushAToB(tmp,result);
			return result;
		}
		expr clangDeclRefExprToZ3Expr(clang::DeclRefExpr* clangDeclRefExpr){
			const ValueDecl*  valueDecl=clangDeclRefExpr->getDecl();
			LangOptions LO;
			LO.CPlusPlus=1; 
			if (!valueDecl){
				std::string buffer;
				llvm::raw_string_ostream strout(buffer);
				clangDeclRefExpr->printPretty(strout, nullptr, PrintingPolicy(LO));
				std::cerr<<"Z3Coding:clangDeclRefExprToZ3Expr: We do not process clangDeclRefExpr: "<<strout.str()<<std::endl;
				return _error;
			}
			std::string buffer;
			llvm::raw_string_ostream strout(buffer);
			valueDecl->printName(strout);
			std::string varName=strout.str();

			QualType declQT = valueDecl->getType();
			std::string buffer2;
			llvm::raw_string_ostream strout2(buffer2);
			declQT.print(strout2,PrintingPolicy(LO));
			std::string typeName=strout2.str();

			//record the valueDecl
			if(varDeclToZ3Expr.count(valueDecl)>0){
				//alread exist
				//get varDecl's z3 name
				expr z3expr=varDeclToZ3Expr.at(valueDecl);
				return z3expr;
			}
			else{
				//not exists
				//set the z3Name
				//if varName exists? getThe count
				if(varNameCount.count(varName)<=0){
					std::string z3Name=varName;
					Sort* tmpTy=clangTypeToZ3Sort(declQT);
					
					if(tmpTy==nullptr) return _error;
					
					z3::sort ty=tmpTy->type;
					
					expr z3expr=c.constant(z3Name.c_str(),ty);
					varDeclToZ3Expr.insert(std::pair<const ValueDecl *,z3::expr>(valueDecl,z3expr));
					
					#ifdef _CHECK_ARRAY_SIZE_VALID
					if(declQT.getTypePtr()->isArrayType()){
						if(!setArrayVariable2ArrayLength(z3Name,declQT)){
							return _error;
						}
					}
					#endif
					
					Z3ExprNameToVarDecl[z3Name]=valueDecl;
					varNameCount[varName]=1;
					return z3expr;
				}
				else{
					int count=varNameCount.at(varName);
					std::string z3Name=varName+std::to_string(count+1);
					Sort* tmpTy=clangTypeToZ3Sort(declQT);
					
					if(tmpTy==nullptr) return _error;
					
					z3::sort ty=tmpTy->type;
					
					expr z3expr=c.constant(z3Name.c_str(),ty);
					varDeclToZ3Expr.insert(std::pair<const ValueDecl *,z3::expr>(valueDecl,z3expr));
					
					#ifdef _CHECK_ARRAY_SIZE_VALID
					if(declQT.getTypePtr()->isArrayType()){
						if(!setArrayVariable2ArrayLength(z3Name,declQT)){
							return _error;
						}
					}
					#endif
					Z3ExprNameToVarDecl[z3Name]=valueDecl;
					varNameCount[varName]=count+1;
					return z3expr;
				}
			}
			return _error;
		}
		vector<expr>* clangArraySubscriptExprToZ3Expr(clang::ArraySubscriptExpr * arraySubscriptExpr){
			vector<expr>* exprs=new vector<expr>();
			const clang::Expr * base=arraySubscriptExpr->getBase();
			const clang::Expr * idx=arraySubscriptExpr->getIdx();			
			vector<expr>* baseZ3Exprs=clangExprToZ3Expr(base);
			vector<expr>* idxZ3Exprs=clangExprToZ3Expr(idx);
			if(baseZ3Exprs==nullptr||idxZ3Exprs==nullptr){
				return nullptr;
			}
			expr baseZ3Expr=baseZ3Exprs->back();baseZ3Exprs->pop_back();
			expr idxZ3Expr=idxZ3Exprs->back();idxZ3Exprs->pop_back();
			pushAToB(baseZ3Exprs,exprs);
			pushAToB(idxZ3Exprs,exprs);
			expr arrayAcess=select(baseZ3Expr,idxZ3Expr);
			exprs->push_back(arrayAcess);
			return exprs;

		}
		expr  clangCharacterLiteralToZ3Expr(clang::CharacterLiteral * charLiteral){
			expr   e=c.int_val(charLiteral->getValue());
			return e;
		}
		expr  clangCXXBoolLiteralExprToZ3Expr(clang::CXXBoolLiteralExpr * boolLiteral){
			if(boolLiteral->getValue()){
				return c.int_val(1);
			}
			else {
				return c.int_val(0);
			}

		}
		/*expr  clangFloatingLiteralToZ3Expr(clang::FloatingLiteral * floatingLiteral){
		/*SmallVectorImpl<char> str;
		floatingLiteral->getValue().toString(str);
		expr    e=c.real_val((__uint64)(floatingLiteral->getValue().convertDoubleAPFloatToAPInt().getLimitedValue()));
		return e;
		return c.int_const("_error");

		}*/
		expr  clangIntegerLiteralToZ3Expr(clang::IntegerLiteral * integerLiteral){
			expr   e=c.int_val((__uint64)(integerLiteral->getValue().getLimitedValue()));
			return e;
		}
		/*expr  clangOffsetOfExprToZ3Expr(clang::OffsetOfExpr * offsetOfExpr){

		  }
		  expr  clangStringLiteralToZ3Expr(clang::StringLiteral * stringLiteral){

		  }*/
		bool isPointerType(QualType qt){
			QualType canonicalType=qt.getTypePtr()->getCanonicalTypeInternal();
			const Type * ty=canonicalType.getTypePtr();
			if(ty->isPointerType()) return true;
			return false;
		}
		vector<expr>*  clangUnaryOperatorToZ3Expr(clang::UnaryOperator * unaryOperator){
			vector<expr>* exprs=new vector<expr>();
			vector<expr>* subExprs=clangExprToZ3Expr(unaryOperator->getSubExpr());
			if(subExprs==nullptr){
				std::cerr<<"Z3Coding:clangUnaryOperatorToZ3Expr: subExprs is null"<<std::endl;
				return nullptr;
			}
			expr subExpr=subExprs->back();subExprs->pop_back();
			
			//memoryUnits,just add select memory unit
			if(isArrayAcess(subExpr)){
				addMemoryUnit(subExpr);
			}
			pushAToB(subExprs,exprs);
			expr tmp(c);
			//std::cout<<subExpr<<":"<<subExpr.get_sort()<<std::endl;
			switch(unaryOperator->getOpcode()){
				default:	
					std::cerr<<"Z3Coding:clangUnaryOperatorToZ3Expr: We do not consider processing unaryOperator: "<<unaryOperator->getOpcodeStr(unaryOperator->getOpcode()).str()<<std::endl;
					return nullptr;
				case UO_PostInc 	://i++
					if(checkError(subExpr)||!(subExpr.is_int()||isPointerType(unaryOperator->getSubExpr()->getType()))) return nullptr;
					isPosIncOrDec=true;
					if(isPointerType(unaryOperator->getSubExpr()->getType())){
						if(preprocess->isNeedToGhost){
							tmp=subExpr;
							expr arrayIndex=getPointerIndex(subExpr);
							exprs->push_back(prime(arrayIndex)==arrayIndex+1);
							exprs->push_back(tmp);
							addPointers(subExpr);
						}
						else{
							return nullptr;
						}
					}
					else{
						tmp=subExpr;
						exprs->push_back(prime(subExpr)==subExpr+1);
						exprs->push_back(tmp);
					}
					break;
				case UO_PostDec 	://i--;
					if(checkError(subExpr)||!(subExpr.is_int()||isPointerType(unaryOperator->getSubExpr()->getType()))) return nullptr;
					isPosIncOrDec=true;
					if(isPointerType(unaryOperator->getSubExpr()->getType())){
						if(preprocess->isNeedToGhost){
							tmp=subExpr;
							expr arrayIndex=getPointerIndex(subExpr);
							exprs->push_back(prime(arrayIndex)==arrayIndex-1);
							exprs->push_back(tmp);
							addPointers(subExpr);
						}
						else{
							return nullptr;
						}
					}
					else{
						tmp=subExpr;
						exprs->push_back(prime(subExpr)==subExpr-1);
						exprs->push_back(tmp);
					}
					break;
				case UO_PreInc 	://++i
					if(checkError(subExpr)||!(subExpr.is_int()||isPointerType(unaryOperator->getSubExpr()->getType()))) return nullptr;
					isPreIncOrDec=true;
					if(isPointerType(unaryOperator->getSubExpr()->getType())){
						if(preprocess->isNeedToGhost){
							tmp=prime(subExpr);
							expr arrayIndex=getPointerIndex(subExpr);
							exprs->push_back(prime(arrayIndex)==arrayIndex+1);
							exprs->push_back(tmp);
							addPointers(subExpr);
						}
						else{
							return nullptr;
						}
					}
					else{
						tmp=prime(subExpr);
						exprs->push_back(tmp==subExpr+1);
						exprs->push_back(tmp);
					}
					break;
				case UO_PreDec 	://--i;
					if(checkError(subExpr)||!(subExpr.is_int()||isPointerType(unaryOperator->getSubExpr()->getType()))) return nullptr;
					isPreIncOrDec=true;
					if(preprocess->isNeedToGhost){
							tmp=prime(subExpr);
							expr arrayIndex=getPointerIndex(subExpr);
							exprs->push_back(prime(arrayIndex)==arrayIndex-1);
							exprs->push_back(tmp);
							addPointers(subExpr);
					}
					else{
						tmp=prime(subExpr);
						exprs->push_back(tmp==subExpr-1);
						exprs->push_back(tmp);
					}
					break;
				case UO_Plus 	://+i
					if(!subExpr.is_int()||checkError(subExpr)) return nullptr;
					exprs->push_back(subExpr);
					break;
				case UO_Minus 	://-i;
					if(!subExpr.is_int()||checkError(subExpr)) return nullptr;
					exprs->push_back(-subExpr);
					break;
				case UO_Not 	://~i;
					if(!subExpr.is_int()||checkError(subExpr)) return nullptr;
					exprs->push_back(~subExpr);
					break;
				case UO_LNot 	://!i
					if(!(subExpr.is_bool()||subExpr.is_int())||checkError(subExpr)) return nullptr;
					if(subExpr.is_int()){
						exprs->push_back(!(subExpr!=0));
					}
					else{
						exprs->push_back(!subExpr);
					}
					break;
				case UO_Deref 	:
					if(preprocess->isNeedToGhost){
						if(isPointerType(unaryOperator->getSubExpr()->getType())){
							expr arraybase=getPointerBase(subExpr);
							expr arrayindex=getPointerIndex(subExpr);
							exprs->push_back(select(arraybase,arrayindex));
							addPointers(subExpr);
						}
						else{
							return nullptr;
						}
					}
					else {
						return nullptr;
					}
			}
			return exprs;
		}
		vector<expr> * filteringLeftNonForAllFormula(vector<expr> * formulas){
			vector<expr> * result=new vector<expr>();
			for(expr e:*formulas){
				if(!isForAllFormula(e)){
					result->push_back(e);
				}
			}
			return result;
		}
		vector<expr> * filteringLeftSimpleFormula(vector<expr> * formulas){
			vector<expr> * result=new vector<expr>();
			for(expr e:*formulas){
				if(isSimpleFormula(e)){
					result->push_back(e);
				}
			}
			return result;
		}
		vector<expr> * filteringLeftNonSimpleFormula(vector<expr> * formulas){
			vector<expr> * result=new vector<expr>();
			for(expr e:*formulas){
				if(!isSimpleFormula(e)){
					result->push_back(e);
				}
			}
			return result;
		}
		vector<expr>*  clangExprToZ3Expr(const clang::Expr * clangexpr){
			vector<expr>* exprs=new vector<expr>();
			expr tmp(c);
			switch (clangexpr->getStmtClass()) {
				default:
					std::cerr<<"Z3Coding:clangExprToZ3Expr: We do not consider processing "<<clangexpr->getStmtClassName()<<std::endl;
					return nullptr;
				case clang::Stmt::BinaryOperatorClass:
					exprs=clangBinaryOperatorToZ3Expr((clang::BinaryOperator*)clangexpr);
					break;
				case clang::Stmt::ArraySubscriptExprClass:
					exprs=clangArraySubscriptExprToZ3Expr((clang::ArraySubscriptExpr*)clangexpr);
					break;
				case clang::Stmt::CharacterLiteralClass:
					tmp=clangCharacterLiteralToZ3Expr((clang::CharacterLiteral*)clangexpr);
					if(checkError(tmp)) return nullptr;
					exprs->push_back(tmp);
					break;
				case clang::Stmt::CXXBoolLiteralExprClass:
					tmp=clangCXXBoolLiteralExprToZ3Expr((clang::CXXBoolLiteralExpr*)clangexpr);
					if(checkError(tmp)) return nullptr;
					exprs->push_back(tmp);
					break;
				case clang::Stmt::IntegerLiteralClass:
					tmp=clangIntegerLiteralToZ3Expr((clang::IntegerLiteral*)clangexpr);
					if(checkError(tmp)) return nullptr;
					exprs->push_back(tmp);
					break;
				case clang::Stmt::DeclRefExprClass:
					tmp=clangDeclRefExprToZ3Expr((clang::DeclRefExpr*)clangexpr);
					if(checkError(tmp)) return nullptr;
					exprs->push_back(tmp);
					break;
				case clang::Stmt::UnaryOperatorClass:
					exprs=clangUnaryOperatorToZ3Expr((clang::UnaryOperator*)clangexpr);
					break;
				case clang::Stmt::ImplicitCastExprClass:
					{
						const CastExpr * castExpr=(const CastExpr *)clangexpr;
						/*std::cout<<"SubExpr is: "<<toString(castExpr->getSubExpr())<<std::endl;
						  std::cout<<"SubExpr type is: "<<toString(castExpr->getSubExpr()->getType())<<std::endl;
						  std::cout<<"SubExprAsWritten is: "<<toString(castExpr->getSubExprAsWritten())<<std::endl;
						  std::cout<<"SubExprAsWritten type is: "<<toString(castExpr->getSubExprAsWritten()->getType())<<std::endl;
						  std::cout<<"CastKindName is: "<<castExpr->getCastKindName()<<std::endl;*/
						exprs=clangExprToZ3Expr(castExpr->getSubExpr());
						break;
					}
				case clang::Stmt::ParenExprClass:
					{
						const ParenExpr * parenExpr=(const ParenExpr *)clangexpr;
						/*std::cout<<"SubExpr is: "<<toString(castExpr->getSubExpr())<<std::endl;
						  std::cout<<"SubExpr type is: "<<toString(castExpr->getSubExpr()->getType())<<std::endl;
						  std::cout<<"SubExprAsWritten is: "<<toString(castExpr->getSubExprAsWritten())<<std::endl;
						  std::cout<<"SubExprAsWritten type is: "<<toString(castExpr->getSubExprAsWritten()->getType())<<std::endl;
						  std::cout<<"CastKindName is: "<<castExpr->getCastKindName()<<std::endl;*/
						exprs=clangExprToZ3Expr(parenExpr->getSubExpr());
						break;
					}
			}
			return  exprs;
		}
		vector<expr>*  clangDeclStmtToZ3Expr(const clang::DeclStmt * clangDeclStmt){
			vector<expr>* exprs=new vector<expr>();
			if(!clangDeclStmt->isSingleDecl()){
				std::cerr<<"Z3Coding:clangDeclStmtToZ3Expr: We do not consider DeclGroup: "<<toString(clangDeclStmt)<<std::endl;
				return nullptr;
			}
			const Decl* decl=clangDeclStmt->getSingleDecl(); 
			if(!decl->classofKind(Decl::Kind::Var)){
				std::cerr<<"Z3Coding:clangDeclStmtToZ3Expr: We do not consider the DeclKind: "<<decl->getDeclKindName()<<std::endl;
				return nullptr;
			}
			LangOptions LO;
			LO.CPlusPlus=1; 
			const  VarDecl * varDecl=(const  VarDecl *)decl;
			const  ValueDecl * valueDecl=(const  ValueDecl *)decl;
			std::string buffer;
			llvm::raw_string_ostream strout(buffer);
			valueDecl->printName(strout);
			std::string varName=strout.str();
			//std::cout<<"varName: "<<varName;
			QualType declQT = valueDecl->getType();
			std::string buffer2;
			llvm::raw_string_ostream strout2(buffer2);
			declQT.print(strout2,PrintingPolicy(LO));
			std::string typeName=strout2.str();
			//std::cout<<", typeName: "<<typeName<<std::endl;

			expr varZ3Expr(c);


			//record the valueDecl
			if(varDeclToZ3Expr.count(valueDecl)>0){
				//alread exist
				//get varDecl's z3 name
				varZ3Expr=varDeclToZ3Expr.at(valueDecl);

			}
			else{
				//not exists
				//set the z3Name
				//if varName exists? get the count
				if(varNameCount.count(varName)<=0){
					std::string z3Name=varName;
					Sort* tmpTy=clangTypeToZ3Sort(declQT);
					if(tmpTy==nullptr) return nullptr;
					z3::sort ty=tmpTy->type;
					varZ3Expr=c.constant(z3Name.c_str(),ty);
					varDeclToZ3Expr.insert(std::pair<const ValueDecl *,z3::expr>(valueDecl,varZ3Expr));
					
					#ifdef _CHECK_ARRAY_SIZE_VALID
					if(declQT.getTypePtr()->isArrayType()){
						if(!setArrayVariable2ArrayLength(z3Name,declQT)){
							return nullptr;
						}
					}
					#endif
					//std::cout<<varZ3Expr<<":"<<varZ3Expr.get_sort()<<std::endl;
					Z3ExprNameToVarDecl[z3Name]=valueDecl;
					varNameCount[varName]=1;
				}
				else{
					int count=varNameCount.at(varName);
					std::string z3Name=varName+std::to_string(count+1);;
					Sort* tmpTy=clangTypeToZ3Sort(declQT);
					if(tmpTy==nullptr) return nullptr;
					z3::sort ty=tmpTy->type;
					varZ3Expr=c.constant(z3Name.c_str(),ty);
					varDeclToZ3Expr.insert(std::pair<const ValueDecl *,z3::expr>(valueDecl,varZ3Expr));
					
					#ifdef _CHECK_ARRAY_SIZE_VALID
					if(declQT.getTypePtr()->isArrayType()){
						if(!setArrayVariable2ArrayLength(z3Name,declQT)){
							return nullptr;
						}
					}
					#endif
					
					Z3ExprNameToVarDecl[z3Name]=valueDecl;
					varNameCount[varName]=count+1;
				}
			}
			if(varDecl->hasInit()){
				vector<expr> * initZ3Exprs=clangExprToZ3Expr(varDecl->getInit()); 
				if(initZ3Exprs==nullptr) return nullptr;
				expr initZ3Expr=initZ3Exprs->back();initZ3Exprs->pop_back();
				pushAToB(initZ3Exprs,exprs);
				//std::cout<<varZ3Expr<<":"<<varZ3Expr.get_sort()<<"=="<<initZ3Expr<<":"<<initZ3Expr.get_sort()<<std::endl;
				if(!Z3_is_eq_sort(c,varZ3Expr.get_sort(),initZ3Expr.get_sort())) return nullptr;
				
				if(isPointerType(declQT)){
						if(preprocess->isNeedToGhost){
							expr lhsBase=getPointerBase(varZ3Expr);
							expr rhsBase=getPointerBase(initZ3Expr);
							exprs->push_back(prime(lhsBase)==rhsBase);
							expr lhsIndex=getPointerIndex(varZ3Expr);
							expr rhsIndex=getPointerIndex(initZ3Expr);
							exprs->push_back(prime(lhsIndex)==rhsIndex);
							addPointers(varZ3Expr);
							addPointers(initZ3Expr);
						}
				}
				else{
					exprs->push_back(prime(varZ3Expr)==initZ3Expr);
				}
			}
			else{
				if(preprocess->isNeedToGhost){
						if(isPointerType(declQT)){
							expr lhsIndex=getPointerIndex(varZ3Expr);
							addPointers(varZ3Expr);
							isAssignedToPointer=true;
							exprs->push_back(prime(lhsIndex)==0);
						}
						
				}
			}

			return exprs;
		}
		vector<expr>* boolSortFiltering(vector<expr>* exprs){
			vector<expr> * formulas=new vector<expr>();
			for(expr e: *exprs){
				if(e.is_bool()){
					formulas->push_back(e);
				}
			}
			return formulas;
		}
		bool equal(expr e1,expr e2){
//			std::string e1name=Z3_ast_to_string(c,e1);
//			std::string e2name=Z3_ast_to_string(c,e2);
			return eq(e1,e2);
		}
		/**
		 * @brief check if every element of disjunctionForms is valid. return all valid elements  
		 * @param Pre
		 * @param disjunctionForms: every element is  conjunction Form
		 * @return 
		 */
		vector<expr>* reduction(vector<expr> *Pre,vector<expr> *disjunctionForms){
			vector<expr>* ret=new vector<expr>();
			for(expr conjunction:*disjunctionForms){
				if(satisfy(Pre,conjunction)!=check_result::unsat){
					ret->push_back(conjunction);
				}
			}
			return ret;
		}
		
		vector<expr>* DNF(expr f){
			f=CNF(f);
			return _DNF(f);
		}
		expr CNF(expr f){
			vector<expr> * tmp=new vector<expr>();
			goal g(c);
			g.add(f);
			tactic split_all = repeat(tactic(c, "tseitin-cnf") | tactic(c, "skip"));
			apply_result r = split_all(g);
			for (unsigned i = 0; i < r.size(); i++) {
				goal result_goal=r[i];
				tmp->push_back(result_goal.as_expr());
//				std::cout << "subgoal " << i << "\n" << result_goal.as_expr() << "\n";
			}
			expr ret=tmp->at(0);
			for (unsigned i = 1; i < tmp->size(); i++) {
				ret=ret&&tmp->at(i);
			}
			return ret;
		}
		/**
		 * @brief for f in formulas, if f is a&&b, remove f ,add a,b
		 * @param formulas
		 * @return 
		 */
		vector<expr>* splitLANDFormulas(vector<expr>* formulas){
			vector<expr>* result=new vector<expr>();
			for(expr f:*formulas){
				vector<expr>* tmp=splitLANDFormula(f);
				pushAToB(tmp,result);
			}
			return result;
		}
		vector<expr>* splitLANDFormula(expr f){
			vector<expr>* result=new vector<expr>();
			if(f.is_app()&&f.decl().name().str()=="and"){
				vector<expr>* left=splitLANDFormula(f.arg(0));
				vector<expr>* right=splitLANDFormula(f.arg(1));
				pushAToB(left,result);
				pushAToB(right,result);
			}
			else{
				result->push_back(f);
			}
			return result;
		}
		vector<expr> * filteringOrFormula(vector<expr>* formulas){
			vector<expr>* ret=new vector<expr>();
			for(expr f:* formulas){
				if(!isOrFormula(f)){
					ret->push_back(f);
				}
			}
			return ret;
		}
		bool isOrFormula(expr f){
			//std::cout<<f<<std::endl;
			//std::cout<<CNF(f)<<std::endl;
			return _isOrFormula(f)||_isOrFormula(CNF(f));
		}
		expr getRet(expr retValue){
			_ret=c.constant("_ret",retValue.get_sort());
			//addMemoryUnit(_ret);
			setRet=true;
			return _ret;
		}
	vector<expr> * clangStmtToZ3Expr(const clang::Stmt* stmt){
			vector<expr> * exprs=new vector<expr>();
			switch (stmt->getStmtClass()) {
				case clang::Stmt::DeclStmtClass:
					exprs=clangDeclStmtToZ3Expr((const clang::DeclStmt*)stmt);
					break;
				case clang::Stmt::BinaryOperatorClass:
					exprs=clangBinaryOperatorToZ3Expr((clang::BinaryOperator*)stmt);
					break;
				case clang::Stmt::UnaryOperatorClass:
					exprs=clangUnaryOperatorToZ3Expr((clang::UnaryOperator*)stmt);
					break;
				case clang::Stmt::ImplicitCastExprClass:
					{
						const CastExpr * castExpr=(const CastExpr *)stmt;
						exprs=clangExprToZ3Expr(castExpr->getSubExpr());
						break;
					}
				case clang::Stmt::ReturnStmtClass:
					{
						const ReturnStmt * returnStmt=(const ReturnStmt *)stmt;
						const Expr* retValue=returnStmt->getRetValue();
						if(retValue!=nullptr){
							exprs=clangExprToZ3Expr(retValue);
							if(exprs==nullptr) return nullptr;
							expr returnExpr=exprs->back();exprs->pop_back();
							exprs->push_back(getRet(returnExpr)==returnExpr);
						}
						break;
					}
				default:{
					std::cerr<<"Z3Coding:clangStmtToZ3Expr: We do not consider processing "<<stmt->getStmtClassName()<<std::endl;	
					occurError=true;
				}
			}
			return exprs;
	}
	
	expr unprimedDecline(expr primedformula){
			vector<expr> * cons=getConsts(primedformula);
			expr unprimedformula=primedformula;
			for(expr con:*cons){
				if(isPrimedVariable(con)){
					expr unprimedcon=unprime(con);
					unprimedformula=substitute(unprimedformula,con,unprimedcon);
				}
			}
			return unprimedformula;
	}
	expr primedLift(expr unprimedformula){
			vector<expr> * cons=getConsts(unprimedformula);
			expr primedformula=unprimedformula;
			for(expr con:*cons){
				if(!isPrimedVariable(con)){
					expr primedcon=prime(con);
					primedformula=substitute(primedformula,con,primedcon);
				}
			}
			return primedformula;
	}
	std::string toString(expr p){
			std::string ret;
			if(isSimpleFormula(p)){
				ret=Z3_ast_to_string(c,p);
				return ret;
			}
			else if(isForAllFormula(p)){
				std::string quantifierStr=Z3_ast_to_string(c,getQuantifier(p));
				std::string beginStr=Z3_ast_to_string(c,getQuantifierBegin(p));
				expr beginFormula=getQuantifierBeginFormula(p);
				std::string endStr=Z3_ast_to_string(c,getQuantifierEnd(p));
				expr endFormula=getQuantifierEndFormula(p);
				std::string stepStr=Z3_ast_to_string(c,getQuantifierStep(p));
				expr body=getQuantifierFormulaBody(p);

				std::string ret="forall "+quantifierStr+ " in ";
				if(beginFormula.decl().name().str()=="<="){
					ret+="[";
				}
				else{
					ret+="(";
				}
				ret+=beginStr+","+stepStr+","+endStr;
				if(endFormula.decl().name().str()=="<="){
					ret+="]";
				}
				else{
					ret+=")";
				}
				ret+=",";
				std::string bodyStr=toString(body);
				ret+=bodyStr;
				return ret;
			}
			
			else if(isPhiFormula(p)){
				return "";
			}
			return "error";
		}
};

#endif
