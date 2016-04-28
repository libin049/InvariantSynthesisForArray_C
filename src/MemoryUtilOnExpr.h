#ifndef _MemoryUtilOnExpr_H
#define _MemoryUtilOnExpr_H

#include "Z3Coding.h"
#include "Formula.h"
#include "AtomVariableAnalysis.h"
#include "AtomVariableDiffAnalysis.h"
#include "AtomVariableDiffAnalysisOnExpr.h"
#include "MemoryUtil.h"
/***
 * forany formula  that statement stmt generates, it is a simple formula
 * befor stmt, a set of formulas Pre holds
 * after stmt, we need computing Pos, which is a set of formulas holds after stmt
 * note that: we regard stmt as formula, it will generate formula about fresh value of 
 * 	variable(we call it primed varibale); there exists not primed varibale in Pre;
 * 	all varibales who exist in Pos is primed variable
 * 	then we substitute primed variable by unprimed variable in Pos, we call it unprimed(Pos)
 *  unprimed(Pos) as Pre of next statement, then repeat
 * 
 ***/


class MemoryUtilOnExpr{
	private:
		Z3Coding &z3Coding;
		context &c;
		//map<std::string,expr> indexNameToInit;
		//map<std::string,expr> indexNameToStep;
		void pushAToB(vector<expr> * & A,vector<expr> * & B){
			for(auto it=A->begin();it != A->end(); it++){
				expr t=*it;
				B->push_back(t);
			}
		}

		//vector<expr> initStmts;
		//vector<expr> updateStmts;
		AtomVariableAnalysisOnExpr* ava;
		AtomVariableDiffAnalysisOnExpr* avdiff;
		/**
		 * @brief 
		 * @param Pre
		 * @param primedformulas
		 * @param stmt is indexUpdateStmt: index__prime=index+step
		 * @param isKillPhi tell caller weather phi will be killded
		 * @return 
		 */
		vector<expr> * closureIndexUpdate(const clang::Stmt * clangStmt,vector<expr> * Pre,
		vector<expr> * primedformulas, expr stmt, bool* isKillPhi,CFGBlock* n){
			vector<expr> * closureformulas=new vector<expr>();
			
			vector<expr> * formulas=new vector<expr>();
			pushAToB(Pre,formulas);
			pushAToB(primedformulas,formulas);
			formulas->push_back(stmt);
			time_t start,stop;
			start = time(NULL);
			closureformulas=closure(closure_preprocess(Pre,primedformulas,stmt)/*formulas*/);
			stop=time(NULL);
//			std::cout<<"clourse1 Time:"<<stop-start<<std::endl;
			//std::cout<<"**111111**********closureformulas is: "<<toString(closureformulas)<<std::endl;
			//std::cout<<"**111111***end*************************"<<std::endl;

			/*primedformulas has no index__prime=index since stmt is indexUpdateStmt
			  so, closureformulas has no arrayacess container index__prime  
			 * */
			pushAToB(Pre,closureformulas);
			start = time(NULL);
			closureformulas=closurePhi(clangStmt,closureformulas,stmt,isKillPhi,n);
			stop=time(NULL);
//			std::cout<<"clourse2 Time:"<<stop-start<<std::endl;
			//std::cout<<"**222222**********closureformulas is: "<<toString(closureformulas)<<std::endl;
			//std::cout<<"**222222***end*************************"<<std::endl;
			//forall formula update
			start = time(NULL);
			vector<expr> *forallFormulas=getAllForAllFormula(closureformulas);

			
			//std::cout<<"**333333**********closureformulas is: "<<toString(closureformulas)<<std::endl;
			//std::cout<<"**333333***end*************************"<<std::endl;
			vector<expr> *unprimedforallFormulas=unprimedFiltering(forallFormulas);
			for(expr unprimedforallFormula: *unprimedforallFormulas){
				if(update_check(closureformulas,unprimedforallFormula,stmt)){
					unprimedforallFormula=update(closureformulas,unprimedforallFormula,stmt);
					expr primedforallFormula=primedLift(unprimedforallFormula);
					closureformulas->push_back(primedforallFormula);
				}
			}
			
			//add index=>init or index<=init
			/*expr primedindex=stmt.arg(0);
			expr primedinit=primedLift(getInitFromIndex(clangStmt,z3Coding.unprime(primedindex)));
			expr primedstep=primedLift(getStepFromIndex(clangStmt,z3Coding.unprime(primedindex)));
			if(z3Coding.prove(Pre,primedstep>0)==proved_result::proved) closureformulas->push_back(primedindex>=primedinit);
			if(z3Coding.prove(Pre,primedstep<0)==proved_result::proved) closureformulas->push_back(primedindex<=primedinit);*/
			//synthesis forall formula from some forall formula
			//synthesis forall formula from some forall formula
			
			stop=time(NULL);
			//std::cout<<"clourse3 Time:"<<stop-start<<std::endl;
			
			
			
			return closureformulas;
		}
		vector<expr> * closureIndexInit(const clang::Stmt* clangStmt,vector<expr> * Pre,vector<expr> * primedformulas, expr stmt){
			vector<expr> * closureformulas=new vector<expr>();
			vector<expr> * formulas=new vector<expr>();
			pushAToB(Pre,formulas);
			pushAToB(primedformulas,formulas);
			formulas->push_back(stmt);
			closureformulas=closure(closure_preprocess(Pre,primedformulas,stmt)/*formulas*/);
			//generate phi formula
			//stmt: index=init
			expr primedindex=stmt.arg(0);
			expr index=unprimedDecline(primedindex);
			
			expr primedinit=primedLift(stmt.arg(1));
			expr step=primedLift(getStepFromIndex(clangStmt,index));
			expr primedphi=constructPhiFormula(primedindex,primedinit,step);
			
			closureformulas->push_back(primedphi);
			
			//if(z3Coding.prove(Pre,step>0)==proved_result::proved) closureformulas->push_back(primedindex>=primedinit);
			//if(z3Coding.prove(Pre,step<0)==proved_result::proved) closureformulas->push_back(primedindex<=primedinit);
			return closureformulas;
		}
		vector<expr> * closureAssigndToArrayAcess(const clang::Stmt* clangStmt,vector<expr> * Pre,vector<expr> * primedformulas, expr stmt){
			vector<expr> * closureformulas=new vector<expr>();
			expr left=stmt.arg(0);
			#ifdef _CHECK_ARRAY_SIZE_VALID
			if(!isArrayAcessExpLtArrayLength(clangStmt,Pre,left)) return closureformulas;
			#endif
			vector<expr> * formulas=new vector<expr>();
			pushAToB(Pre,formulas);
			pushAToB(primedformulas,formulas);
			formulas->push_back(stmt);
			//closure will generate all non-forallFormula closure
			
//			std::cout<<"primedformulas: "<<toString(primedformulas)<<std::endl;
//			std::cout<<"Pre: "<<toString(Pre)<<std::endl;
//			std::cout<<"stmt: "<<stmt<<std::endl;
			closureformulas=closure(closure_preprocess(Pre,primedformulas,stmt)/*formulas*/);
			
			map<unsigned,expr> *closureformulasMap=exprVectorToExprMap(closureformulas);
			
			//transfer forall formula
			for(expr f: *Pre){
				if(z3Coding.isForAllFormula(f)){
					expr unprimedLeft=unprimedDecline(left);
//					std::cout<<"closure formulas: "<<toString(closureformulas)<<std::endl;
//					std::cout<<"Pre: "<<toString(Pre)<<std::endl;
//					std::cout<<"unprimedLeft: "<<unprimedLeft<<std::endl;
//					std::cout<<"formula: "<<f<<std::endl;
					
					if(!mayMemoryUnitIsInFormula(Pre,unprimedLeft,f)){
						expr fprimed=primedLift(f);
						if(!isIn(fprimed,closureformulasMap)){
							closureformulas->push_back(fprimed);
							
							exprMapAdd(fprimed,closureformulasMap);
						}
					}
					else{
						//split
						split(Pre,left,f);
					}
				}
			}
			return closureformulas;
		}
		/**
		 * @brief construct forall formula according to phi
		 * @param Pos
		 * @param stmt is indexUpdateStmt: index__prime=index+step
		 * @param isKillPhi, as output, tell caller phi is used or not? if used, caller will kill phi
		 * @return 
		 */
		vector<expr> * closurePhi(const clang::Stmt * clangStmt,vector<expr> * closureformulas, 
		expr stmt,bool *isKillPhi,CFGBlock *n){
			
			//std::cout<<"closureformulas is: "<<toString(closureformulas)<<std::endl;
			expr primedindex=stmt.arg(0);
			expr primedstep=primedLift(getStepFromIndexUpdate(stmt));
			expr init=getInitFromIndex(clangStmt,z3Coding.unprime(primedindex),n);
			expr primedinit=primedLift(init);/*expr primedinit=z3Coding.prime(init);*/
			if(existPhiFormula(closureformulas)){
				vector<expr> *allPhiFormula=getAllPhiFormula(closureformulas);
				//std::cout<<"allPhiFormula is: "<<toString(allPhiFormula)<<std::endl;
				
				bool isIndexStepGtZeroFlag=isIndexStepGtZero(closureformulas,stmt);
				bool isIndexStepLtZeroFlag=isIndexStepLtZero(closureformulas,stmt);
				//std::cout<<"6666666666666isIndexStepLtZeroFlag end: "<<std::endl;
				for(expr phi: *allPhiFormula){
					expr phiIndex=getPhiIndex(phi);
					//std::cout<<"phiIndex is: "<<phiIndex<<std::endl;
					//std::cout<<"z3Coding.unprime(primedindex) is: "<<z3Coding.unprime(primedindex)<<std::endl;
					if(equal(phiIndex,z3Coding.unprime(primedindex))){
						/*	get RelatedArrayAcessFormula of phiIndex not primedphiIndex,
						 * because closureformulas has no arrayacess container index__prime  
						 * */
						// std::cout<<toString(closureformulas)<<std::endl;
						//  std::cout<<phiIndex<<std::endl;
						vector<expr> *phiIndexRelatedArrayAcessFormula=getAllIndexRelatedArrayAcessFormula(closureformulas,phiIndex);
						//std::cout<<"phiIndexRelatedArrayAcessFormula is: "<<toString(phiIndexRelatedArrayAcessFormula)<<std::endl;
						for(expr body : *phiIndexRelatedArrayAcessFormula){
							//generate forall formula
							//	std::cout<<"5555555555"<<body<<std::endl;
							vector<expr> * cons=z3Coding.getConstsWithQuantifier(body);
							vector<expr> * initcons=z3Coding.getConstsWithQuantifier(init);
							pushAToB(initcons,cons);
							cons->push_back(phiIndex);
							
							expr quantifier=constructNewQuantifierName(cons);
							
							//std::cout<<quantifier<<std::endl;
							//std::cout<<toString(cons)<<std::endl;
							expr primedindexBeginFormula(c);
							expr primedindexEndFormula(c);
							if(isIndexStepGtZeroFlag/*isIndexStepGtZero(closureformulas,stmt)*/){
								//init<=q&&q<primedindex
								primedindexBeginFormula=primedinit<=quantifier;
								primedindexEndFormula=quantifier<primedindex;
							}


							if(isIndexStepLtZeroFlag/*isIndexStepLtZero(closureformulas,stmt)*/){
								primedindexBeginFormula=primedindex<quantifier;
								primedindexEndFormula=quantifier<=primedinit;
							}

							expr quantifierbody=z3Coding.substitute(body,phiIndex,quantifier);
							//std::cout<<"primedstep is: "<<primedstep<<std::endl;
							expr primedqf=primedLift(z3Coding.constructForAllFormula_step(quantifier,primedindexBeginFormula,primedindexEndFormula,
									primedstep,primedinit,quantifierbody));
							closureformulas->push_back(primedqf);
							*isKillPhi=true;
						}
					}
				}
			}
			//std::cout<<"44444444444444444"<<std::endl;
			return closureformulas;
		}
		
		void exprMapAdd(expr e,map<unsigned,expr> * & exprmap){
//			std::string ename=Z3_ast_to_string(c,e);
			exprmap->insert(std::pair<unsigned,expr>(e.hash(),e));
			return;
		}
		void exprMapRemove(expr e,map<unsigned,expr> * & exprmap){
//			std::string ename=Z3_ast_to_string(c,e);
			exprmap->erase(e.hash());
			return;
		}
		map<unsigned,expr> * exprMapClone(map<unsigned,expr> *  exprmap){
			map<unsigned,expr> * ret=new map<unsigned,expr>();
			for(std::pair<unsigned,expr> em: *exprmap){
				ret->insert(em);
			}
			return ret;
		}
	public:
		map<unsigned,expr> * exprVectorToExprMap(vector<expr> *exprvector){
			map<unsigned,expr> * exprmap=new map<unsigned,expr>();
			for(expr e:*exprvector){
				exprmap->insert(std::pair<unsigned,expr>(e.hash(),e));
			}
			return exprmap;
		}
	

		MemoryUtilOnExpr(Z3Coding &coding,context &ctx,AtomVariableAnalysisOnExpr* ava,AtomVariableDiffAnalysisOnExpr* avdiff):z3Coding(coding),c(ctx){
			this->ava=ava;
			this->avdiff=avdiff;
		}

//		bool isIndexUpdate(expr stmt){
//			//std::string str2=Z3_ast_to_string(c,stmt);
//			for(expr e:updateStmts){
//				//std::string str1=Z3_ast_to_string(c,e);
//				if(equal(e,stmt)){
//					return true;
//				}
//			}
//			return false;
//		}
		bool isIndexUpdate(const clang::Stmt* clangStmt, expr stmt){
			if(clangStmt==nullptr){
				return true;
			}
			
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return false;
			}
			expr scalar=z3Coding.unprime(stmt.arg(0));
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(equal(av->indexUpdateStmtz3coding,stmt)&&av->checkScalaVaribale(scalar)){
					return true;
				}
			}
			return false;
		}


		/**
		 * @brief 
		 * @param Pre
		 * @param indexUpdateStmt is indexUpdate Stmt: index__prime=index+step
		 * @return 
		 */
		bool isIndexStepGtZero(vector<expr> * Pre, expr indexUpdateStmt){
			expr primedIndex=indexUpdateStmt.arg(0);
			expr right=indexUpdateStmt.arg(1);
			expr index=z3Coding.unprime(primedIndex);
			expr assert=index<right;
			//std::cout<<"assert is :"<<assert<<std::endl;
			//std::cout<<"Pre is  :"<<toString(Pre)<<std::endl;
			if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
				return true;
			}
			return false;
		}
		bool isIndexStepLtZero(vector<expr> * Pre, expr indexUpdateStmt){
			expr primedIndex=indexUpdateStmt.arg(0);
			expr right=indexUpdateStmt.arg(1);
			expr index=z3Coding.unprime(primedIndex);
			expr assert=index>right;
			//std::cout<<"assert is :"<<assert<<std::endl;
			//std::cout<<"Pre is  :"<<toString(Pre)<<std::endl;
			if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
				return true;
			}
			return false;
		}
		
		/**
		 * @brief stmt: primedIndex=index+step
		 * @param stmt
		 * @return 
		 */
		expr getStepFromIndexUpdate(expr stmt){
			if(stmt.arg(1).decl().name().str()=="+"){
				return stmt.arg(1).arg(1);
			}
			else if(stmt.arg(1).decl().name().str()=="-"){
				return -stmt.arg(1).arg(1);
			}
			else{
				std::cerr<<"getStepFromIndexUpdate: something is wrong!"<<std::endl;
				return z3Coding._error;
			}
		}
//		expr getStepFromIndex(expr index){
//			std::string indexname=Z3_ast_to_string(c,index);
//			return indexNameToStep.at(indexname);
//		}
//		bool isIndexInit(expr stmt){
////			std::string str2=Z3_ast_to_string(c,stmt);
//			for(expr e: initStmts){
////				std::string str1=Z3_ast_to_string(c,e);
//				if(equal(stmt,e)){
//					return true;
//				}
//			}
//			return false;
//		}
		bool isIndexInit(const clang::Stmt* clangStmt,expr stmt){
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return false;
			}
			expr scalar=z3Coding.unprime(stmt.arg(0));
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->indexInitStmt==clangStmt&&av->hasStep()&&av->checkScalaVaribale(scalar)){
					return true;
				}
			}
			return false;
		}
		/**
		 * @brief stmt: primedIndex=init
		 * @param stmt
		 * @return 
		 */
		expr getInitFromIndexInit(expr stmt){
			return stmt.arg(1);
		}
//		expr getInitFromIndex(expr index){
//			std::string indexname=Z3_ast_to_string(c,index);
//			return indexNameToInit.at(indexname);
//		}
		expr getInitFromIndex(const clang::Stmt *clangStmt,expr index,CFGBlock *n){
			if(clangStmt!=nullptr){
				if(ava->mapToStmtOut.count(clangStmt)<=0) return z3Coding._error;
				FlowSet* out=ava->mapToStmtOut.at(clangStmt);
				ValueListSet* vlsOut=(ValueListSet*)out;
				for(Property* p: vlsOut->elements){
					AtomVariabla * av=(AtomVariabla *)p;
					if(equal(av->scalaVarz3coding,index)){
						return av->initz3coding;
					}
				}
				return z3Coding._error;
			
			}
			else{
				if(ava->getMapToBlockOut()->count(n)<=0){
					return z3Coding._error;
				}
				FlowSet* out=ava->getMapToBlockOut()->at(n)->front()->second;
				ValueListSet* vlsOut=(ValueListSet*)out;
				for(Property* p: vlsOut->elements){
					AtomVariabla * av=(AtomVariabla *)p;
					cout<<av->scalaVarz3coding<<" ==? "<<index<<std::endl;
					if(equal(av->scalaVarz3coding,index)){
						return av->initz3coding;
					}
				}
				return z3Coding._error;
			}
				
			
		}
		expr getStepFromIndex(const clang::Stmt *clangStmt,expr index){
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(equal(av->scalaVarz3coding,index)){
					if(av->hasStep()){
						return av->stepz3coding;
					}
					else{
						return z3Coding._error;
					}
				}
			}
			return z3Coding._error;
		}
		bool isAssignment(expr stmt){
			return isAssigndToArrayAcess(stmt)||isAssigndToScaleVariable(stmt);
		}
		bool isAssigndToArrayAcess(expr stmt){
			if(stmt.is_app()){
				if(stmt.decl().name().str()=="="){
					expr lhs=stmt.arg(0);
					if(lhs.decl().name().str()=="select"){
						expr base=z3Coding.getArrayBase(lhs);
						return z3Coding.isPrimedVariable(base);
					}
				}
			}
			return false;
		}
		bool isAssigndToScaleVariable(expr stmt){
			if(stmt.is_app()){
				if(stmt.decl().name().str()=="="){
					expr lhs=stmt.arg(0);
					return z3Coding.isPrimedVariable(lhs);
				}
			}
			return false;
		}

		/**
		 * @brief 
		 * @param Pre: pre-state of stmt
		 * @param stmt  
		 * @param scopeMemoryUnits: the MemoryUnits of stmt can acess( or we can call it still live MemoryUnits)
		 * @return unprimed(pos-state of stmt) 
		 */
		vector<expr> * Pos(const clang::Stmt* clangStmt,vector<expr> * Pre, 
		expr stmt, map<std::string,expr> * scopeMemoryUnits,CFGBlock* n){
			//std::cout<<"stmt is: "<<stmt<<std::endl;
			//std::cout<<"MemoryUnits is: "<<toString(scopeMemoryUnits)<<std::endl;
			vector<expr> * primedformulas=generatePrimed(Pre,stmt,scopeMemoryUnits);
			//std::cout<<"primedformulas is: "<<toString(primedformulas)<<std::endl;
			
			//cout<<"closure: "<<stmt<<std::endl;
			vector<expr> * closureformulas=closure(clangStmt,Pre,primedformulas,stmt,n);
			//std::cout<<"closureformulas is: "<<toString(closureformulas)<<std::endl;
			vector<expr> * unprimedPos=unprimedDecline(primedFiltering(closureformulas));
			//std::cout<<"unprimedPos is: "<<toString(unprimedPos)<<std::endl;
			
			vector<expr> * ret=phiFiltering(clangStmt,unprimedPos);
			//std::cout<<"ret is: "<<toString(ret)<<std::endl;
			return ret;

		}
		std::string toString(map<std::string,expr> * scopeMemoryUnits){
			std::string ret="";
			for(auto it=scopeMemoryUnits->begin();it!=scopeMemoryUnits->end();it++){
				std::pair<std::string,z3::expr> p=(std::pair<std::string,z3::expr>) *it;
				std::string memoryUnitName=Z3_ast_to_string(c,p.second);
				ret+=memoryUnitName+";";
			}
			return ret;
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
		 * @brief forallFormula: forall q. extendFormula&& init<=q&&q<end&&end%step=0 => body
		 * @param Pre
		 * @param forallFormula
		 * @return  
		 */
		bool update_check(vector<expr> * Pre, expr forallFormula,expr indexUpdateStmt){
			//std::cout<<forallFormula<<":"<<indexUpdateStmt<<std::endl;
			expr primedindex=indexUpdateStmt.arg(0);
			expr right=indexUpdateStmt.arg(1);
			expr index=unprimedDecline(primedindex);
			expr init=z3Coding.getQuantifierBegin(forallFormula);
			
			expr end=z3Coding.getQuantifierEnd(forallFormula);
			expr forallBody=z3Coding.getQuantifierFormulaBody(forallFormula);
			expr quantifier=z3Coding.getQuantifier(forallFormula);
			vector<expr> *initCons=z3Coding.getConsts(init);
			vector<expr> *endCons=z3Coding.getConsts(end);
			if(isIn(index,initCons)&&!isIn(index,endCons)){
				expr newinit=z3Coding.substitute(init,index,right);
				expr assert=newinit>init;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become smaller, forallFormula is still valid
					return true;
				}
				assert=newinit<init;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become bigger
					expr beginFormula=z3Coding.getQuantifierBeginFormula(forallFormula);
					expr newForAllBody(c);
					if(beginFormula.decl().name().str()=="<"){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,init);
					}
					else if(beginFormula.decl().name().str()=="<="){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,newinit);
					}

					if(merge_check(newForAllBody,Pre)){
						return true;
					}

				}
			}
			if(!isIn(index,initCons)&&isIn(index,endCons)){
				expr newend=z3Coding.substitute(end,index,right);
				expr assert=newend<end;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become smaller, forallFormula is still valid
					return true;
				}
				assert=newend>end;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become bigger
					expr endFormula=z3Coding.getQuantifierEndFormula(forallFormula);
					expr newForAllBody(c);
					if(endFormula.decl().name().str()=="<"){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,end);
					}
					else if(endFormula.decl().name().str()=="<="){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,newend);
					}

					if(merge_check(newForAllBody,Pre)){
						return true;
					}

				}
			}
			return false;
		}
		/**
		 * @brief exist the meet result of f and formulas
		 * @param f
		 * @param formulas
		 * @return 
		 */
		bool merge_check(expr f,vector<expr> * formulas){
			
			if(isIn(f,formulas)){
				return true;
			}
			for(expr ele:*formulas){
				
				expr meet_result=meet(new vector<expr>,f,ele);
				if(!z3Coding.checkError(meet_result)){
					return true;
				}
			}
			return false;
		}
		
		expr merge(expr f,vector<expr> * formulas){
			if(isIn(f,formulas)){
				return f;
			}
			for(expr ele:*formulas){
				expr meet_result=meet(new vector<expr>,f,ele);
				if(!z3Coding.checkError(meet_result)){
					return meet_result;
				}
			}
			return z3Coding._error;
		}
		expr update(vector<expr> * Pre, expr forallFormula,expr indexUpdateStmt){
			expr primedindex=indexUpdateStmt.arg(0);
			expr right=indexUpdateStmt.arg(1);
			expr index=unprimedDecline(primedindex);
			expr init=z3Coding.getQuantifierBegin(forallFormula);
			expr end=z3Coding.getQuantifierEnd(forallFormula);
			expr forallBody=z3Coding.getQuantifierFormulaBody(forallFormula);
			expr quantifier=z3Coding.getQuantifier(forallFormula);
			expr beginFormula=z3Coding.getQuantifierBeginFormula(forallFormula);
			expr endFormula=z3Coding.getQuantifierEndFormula(forallFormula);
			expr step=z3Coding.getQuantifierStep(forallFormula);
			expr stepFormula=z3Coding.getQuantifierStepFormula(forallFormula);
			//std::cout<<beginFormula<<":"<<endFormula<<":"<<step<<std::endl;
			vector<expr> *initCons=z3Coding.getConsts(init);
			vector<expr> *endCons=z3Coding.getConsts(end);
			if(isIn(index,initCons)&&!isIn(index,endCons)){
				expr newinit=z3Coding.substitute(init,index,right);
				expr assert=newinit>init;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become smaller, forallFormula is still valid
					return forallFormula;
				}
				assert=newinit<init;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become bigger
					
					expr newForAllBody(c);
					if(beginFormula.decl().name().str()=="<"){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,init);
					}
					else if(beginFormula.decl().name().str()=="<="){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,newinit);
					}

					if(merge_check(newForAllBody,Pre)){
						expr bodymeetResult=merge(newForAllBody,Pre);
						if(equal(bodymeetResult,newForAllBody)){
							return forallFormula;
						}
						else{
							expr body=z3Coding.substitute(bodymeetResult,index,quantifier);
							expr extendFormula=z3Coding.getQuantifierExtendFormula(forallFormula);
							if(z3Coding.checkError(extendFormula)){
								return z3Coding.constructForAllFormula(quantifier,beginFormula,endFormula,stepFormula,body);
							}
							else{
								return z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,endFormula,stepFormula,body);
							}
						}
					}

				}
			}
			if(!isIn(index,initCons)&&isIn(index,endCons)){
				expr newend=z3Coding.substitute(end,index,right);
				expr assert=newend<end;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become smaller, forallFormula is still valid
					return forallFormula;
				}
				assert=newend>end;
				if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert)==proved_result::proved){
					//interval become bigger
					
					expr newForAllBody(c);
					if(endFormula.decl().name().str()=="<"){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,end);
					}
					else if(endFormula.decl().name().str()=="<="){
						newForAllBody=z3Coding.substitute(forallBody,quantifier,newend);
					}

					if(merge_check(newForAllBody,Pre)){
						expr bodymeetResult=merge(newForAllBody,Pre);
						if(equal(bodymeetResult,newForAllBody)){
							return forallFormula;
						}
						else{
							expr body=z3Coding.substitute(bodymeetResult,index,quantifier);
							expr extendFormula=z3Coding.getQuantifierExtendFormula(forallFormula);
							if(z3Coding.checkError(extendFormula)){
								return z3Coding.constructForAllFormula(quantifier,beginFormula,endFormula,stepFormula,body);
							}
							else{
								return z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,endFormula,stepFormula,body);
							}
						}
					}

				}
			}
			return c.int_const("__error");
		}
		/**
		 * @brief 
		 * @param Pre
		 * @param arrayAcess
		 * @param forAllFormula
		 * @return 
		 */
		vector<expr>* split(vector<expr>* Pre,expr arrayAcess,expr forAllFormula){
			return nullptr;
		}

		/**
		 * @brief synthesis forall formula from some forall formula
		 * @param formulas
		 * @return 
		 */
		vector<expr>* synthesisForAllFormula(vector<expr>* formulas){
			return nullptr;
		}
		/**
		 * @brief e1[e2],check e2 < e1.length
		 * @param Pre
		 * @param arrayAcess e1[e2]
		 * @return check e2 < e1.length
		 */
		bool isArrayAcessExpLtArrayLength(vector<expr> * Pre,expr arrayAcess){
			arrayAcess=unprimedDecline(arrayAcess);
			if(z3Coding.isArrayAcess(arrayAcess)){
				expr base=z3Coding.getArrayBase(arrayAcess);
				std::string arrayName=Z3_ast_to_string(c,base);
				if(z3Coding.arrayVariable2arrayLength.count(arrayName)>0){
					vector<expr> * arrayLengths=z3Coding.arrayVariable2arrayLength.at(arrayName);
					unsigned d=z3Coding.getArrayAcessDimension(arrayAcess);
					if(d>arrayLengths->size()) return false;
					for(unsigned i=0;i<d;i++){
						expr idxk=z3Coding.getArrayAcessKthIdx(arrayAcess,i);
						expr idxAssert=(/*idxk>=0&&*/idxk<arrayLengths->at(i));
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),idxAssert);
						if(r==proved_result::proved){
							return true;	
						}
						else {
							return false;
						}
					}
				}
				else{
					return false;
				}
			}
			return false;
		}
		
		vector<expr>* getIndexAndInitProperty(vector<expr>* Pre,const clang::Stmt* clangStmt){
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return new vector<expr>();
			}
			vector<expr>* result=new vector<expr>();
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(av->hasStep()){
					expr step=av->stepz3coding;
					if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),step>0)==proved_result::proved){
						result->push_back(av->scalaVarz3coding >= av->initz3coding);
					}
					else if(z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),step<0)==proved_result::proved){
						result->push_back(av->scalaVarz3coding <= av->initz3coding);
					}
				}
			}
			return result;
		}
		bool isArrayAcessExpLtArrayLength(const clang::Stmt* clangStmt,vector<expr> * Pre,expr arrayAcess){
			vector<expr>* extendPre=new  vector<expr>();
			pushAToB(Pre,extendPre);
			vector<expr>* tmp=getIndexAndInitProperty(Pre,clangStmt);
			pushAToB(tmp,extendPre);
			arrayAcess=unprimedDecline(arrayAcess);
			if(z3Coding.isArrayAcess(arrayAcess)){
				expr base=z3Coding.getArrayBase(arrayAcess);
				std::string arrayName=Z3_ast_to_string(c,base);
				if(z3Coding.arrayVariable2arrayLength.count(arrayName)>0){
					vector<expr> * arrayLengths=z3Coding.arrayVariable2arrayLength.at(arrayName);
					unsigned d=z3Coding.getArrayAcessDimension(arrayAcess);
					if(d>arrayLengths->size()) return false;
					for(unsigned i=0;i<d;i++){
						expr idxk=z3Coding.getArrayAcessKthIdx(arrayAcess,i);
						expr idxAssert=(idxk>=0&&idxk<arrayLengths->at(i));
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(extendPre),idxAssert);
						if(r==proved_result::proved){
							return true;	
						}
						else {
							return false;
						}
					}
				}
				else{
					return false;
				}
			}
			return false;
		}
		
		/*bool mayMemoryUnitIsInPatch(vector<expr> * Pre,expr memoryunit1,expr memoryunit2){
			if(z3Coding.isArrayAcess(memoryunit1)){
				if(isArrayAcessExpLtArrayLength(Pre,memoryunit1)){
					return false;
				}
				else{
					return true;
				}
			}
			if(z3Coding.isArrayAcess(memoryunit2)){
				if(isArrayAcessExpLtArrayLength(Pre,memoryunit2)){
					return false;
				}
				else{
					return true;
				}
			}
			return false;
		}*/
		/**
		 * @brief memoryunit1's memory may isin constsMemory set of memoryunit2 
		 * @param Pre
		 * @param memoryunit1
		 * @param memoryunit2
		 * @return  
		 */
		bool mayMemoryUnitIsIn(vector<expr> * Pre,expr memoryunit1,expr memoryunit2){
			
			//if(mayMemoryUnitIsInPatch(Pre,memoryunit1,memoryunit2)) return true;
			
			if(memoryunit1.is_const()&&memoryunit2.is_const()){
				return memoryunit1.decl().name().str()==memoryunit2.decl().name().str();
			}
			else if(z3Coding.isArrayAcess(memoryunit1)&&memoryunit2.is_const()){
				//memoryunit1:A[i]  memoryunit2:A
				expr base1=z3Coding.getArrayBase(memoryunit1);
				return base1.decl().name().str()==memoryunit2.decl().name().str();
			}
			else if(memoryunit1.is_const()&&z3Coding.isArrayAcess(memoryunit2)){
				vector<expr>* consts=z3Coding.getConsts(memoryunit2);
				for(auto it=consts->begin();it!=consts->end();it++){
					expr con=*it;
					if(memoryunit1.decl().name().str()==con.decl().name().str()){
						return true;
					}
				}
				return false;
			}
			else if(z3Coding.isArrayAcess(memoryunit1)&&z3Coding.isArrayAcess(memoryunit2)){
				//A[B[exp]][exp]
				expr base1=z3Coding.getArrayBase(memoryunit1);
				expr base2=z3Coding.getArrayBase(memoryunit2);
				if(base1.decl().name().str()!=base2.decl().name().str()){
					return false;
				}
				else{
					int d1=z3Coding.getArrayAcessDimension(memoryunit1);
					int d2=z3Coding.getArrayAcessDimension(memoryunit2);
					expr idxEqualAssert(c);
					//A[e11][e21]..[en1]  A[e12][e22]..[en2]
					if(d1==d2){
						expr idx1k=z3Coding.getArrayAcessKthIdx(memoryunit1,0);
						expr idx2k=z3Coding.getArrayAcessKthIdx(memoryunit2,0);
						idxEqualAssert= (idx1k==idx2k);
						for(int i=1;i<d1;i++){
							idx1k=z3Coding.getArrayAcessKthIdx(memoryunit1,i);
							idx2k=z3Coding.getArrayAcessKthIdx(memoryunit2,i);
							idxEqualAssert= idxEqualAssert&&(idx1k==idx2k);
						}
						check_result r=z3Coding.satisfy(Pre,idxEqualAssert);
						if(r==check_result::sat||r==check_result::unknown){
							return true;	
						}
						else {
							return false;
						}
					}
					//A[e11][e21]..[en1]...e[m1]  A[e12][e22]..[en2]
					else if(d1>d2){
						expr formerKDimension=z3Coding.getFormerKDimension(memoryunit1,d2);
						expr idx1k=z3Coding.getArrayAcessKthIdx(formerKDimension,0);
						expr idx2k=z3Coding.getArrayAcessKthIdx(memoryunit2,0);
						idxEqualAssert= (idx1k==idx2k);
						for(int i=1;i<d2;i++){
							idx1k=z3Coding.getArrayAcessKthIdx(formerKDimension,i);
							idx2k=z3Coding.getArrayAcessKthIdx(memoryunit2,i);
							idxEqualAssert= idxEqualAssert&&(idx1k==idx2k);
						}
						check_result r=z3Coding.satisfy(Pre,idxEqualAssert);
						if(r==check_result::sat||r==check_result::unknown){
							return true;	
						}
						else {
							return false;
						}
					}
					//A[e11][e21]..[en1]  A[e12][e22]..[en2]...e[m1]
					else{
						expr formerKDimension=z3Coding.getFormerKDimension(memoryunit2,d1);
						expr idx1k=z3Coding.getArrayAcessKthIdx(memoryunit1,0);
						expr idx2k=z3Coding.getArrayAcessKthIdx(formerKDimension,0);
						idxEqualAssert= (idx1k==idx2k);
						for(int i=1;i<d1;i++){
							idx1k=z3Coding.getArrayAcessKthIdx(memoryunit1,i);
							idx2k=z3Coding.getArrayAcessKthIdx(formerKDimension,i);
							idxEqualAssert= idxEqualAssert&&(idx1k==idx2k);
						}
						check_result r=z3Coding.satisfy(Pre,idxEqualAssert);
						if(r==check_result::sat||r==check_result::unknown){
							return true;	
						}
						else {
							return false;
						}
					}
				}
			}
			else{

				std::cerr<<"Z3Coding:mayMemoryEqual: something is wrong!"<<std::endl;
				return true;
			}
			return true;
		}
		/*bool mayMemoryUnitIsInFormulaPatch(vector<expr> * Pre,expr memoryunit1){
			if(z3Coding.isArrayAcess(memoryunit1)){
				if(isArrayAcessExpLtArrayLength(Pre,memoryunit1)){
					return false;
				}
				else{
					return true;
				}
			}
			return false;
		}*/

		bool mayMemoryUnitIsInFormula(vector<expr> * Pre,expr memoryunit1,expr formula){
			
			//if(mayMemoryUnitIsInFormulaPatch(Pre,memoryunit1)) return true;
			if(memoryunit1.is_const()){
				vector<expr>* consts=z3Coding.getConsts(formula);
				for(auto it=consts->begin();it!=consts->end();it++){
					expr con=*it;
					if(memoryunit1.decl().name().str()==con.decl().name().str()){
						return true;
					}
				}
				return false;
			}
			else if(z3Coding.isArrayAcess(memoryunit1)){
				if(formula.is_quantifier()){
					expr memoryunitbase=z3Coding.getArrayBase(memoryunit1);
					int  memoryunitDim=z3Coding.getArrayAcessDimension(memoryunit1);
					vector<expr> * allsteps=z3Coding.getAllQuantifierStep(formula);
					vector<expr> * allbeginformulas=z3Coding.getAllQuantifierBeginFormula(formula);
					vector<expr> * allendformulas=z3Coding.getAllQuantifierEndFormula(formula);
					vector<expr> * allquantifiers=z3Coding.getAllQuantifier(formula);
					vector<expr> * arrayAcesses=z3Coding.getArrayAcessMemoryUnit(formula);
					//std::cout<<toString(arrayAcesses)<<std::endl;
					for(expr arrayAcess:*arrayAcesses){
						
						expr arrayAcessBase=z3Coding.getArrayBase(arrayAcess);
						if(mayMemoryUnitIsIn(Pre,memoryunitbase,arrayAcessBase)){
							//if exist any quantifier is in arrayAcess
							vector<expr> * arrayAcessCons=z3Coding.getConsts(arrayAcess);
							bool quantifierIsInArrayAcess=false;
							for(expr quantifier: *allquantifiers){
								if(isIn(quantifier,arrayAcessCons)){
									quantifierIsInArrayAcess=true;
									break;
								}
							}
							if(quantifierIsInArrayAcess){
								// 	determine which dim of quantifier occur
								//	get the max and min
								//	determine the dim index of memoryunit1 is in the min..max
								int arrayAcessDim=z3Coding.getArrayAcessDimension(arrayAcess);
								bool allArrayAcessDimMayEqual=true;
								for(int i=0;i<arrayAcessDim&&i<memoryunitDim;i++){
									expr arrayAcessKthIdx=z3Coding.getArrayAcessKthIdx(arrayAcess,i);
									expr memoryunitKthIdx=z3Coding.getArrayAcessKthIdx(memoryunit1,i);
									vector<expr> *ithidxCons=z3Coding.getConsts(arrayAcessKthIdx);
									vector<int> *isInQuantifierIndex=new vector<int>();
									for(unsigned i=0;i<allquantifiers->size();i++){
										expr quantifier=allquantifiers->at(i);
										if(isIn(quantifier,ithidxCons)){
											isInQuantifierIndex->push_back(i);
										}
									}
									if(isInQuantifierIndex->size()>0){
										//get the max and min of index(x,y...), x and y is the quantifier
										//determine the dim index of memoryunit1 is in the min..max
										vector<expr> *quantifierFormulas= new vector<expr>();
										//expr *parrayAcessKthIdx=&arrayAcessKthIdx;
										for(int quantifierIndex:*isInQuantifierIndex){
											//quantifier is not in Pre
											expr quantifier=allquantifiers->at(quantifierIndex);
											expr beginformula=allbeginformulas->at(quantifierIndex);
											expr begin=beginformula.arg(0);
											expr endformula=allendformulas->at(quantifierIndex);
											expr step=allsteps->at(quantifierIndex);
											if(!isIn(quantifier,Pre)){
												//beginformula&&endformula&&quantifier%step=0
												expr qi=beginformula&&endformula&&to_expr(c,Z3_mk_mod(c,quantifier-begin,step))==0;
												quantifierFormulas->push_back(qi);
											}
											else{
												std::cerr<<"Z3Coding:mayMemoryUnitIsInFormula: something is wrong!"<<std::endl;
												/*//quantifier is in Pre, rename quantifier
												expr newquantifier=z3Coding.rename(z3Coding.getAllCons(Pre),quantifier);
												arrayAcessKthIdx=z3Coding.substitute(arrayAcessKthIdx,quantifier,newquantifier);
												//beginformula&&endformula&&quantifier%step=0
												expr qi=beginformula&&endformula&&to_expr(c,Z3_mk_mod(c,newquantifier,step))==0;
												quantifierFormulas->push_back(qi);*/
											}
										}
										expr satisfyFormula=arrayAcessKthIdx==memoryunitKthIdx;
										vector<expr> * Pres=new vector<expr>();
										pushAToB(Pre,Pres);
										pushAToB(quantifierFormulas,Pres);
										//std::cout<<satisfyFormula<<std::endl;
										//std::cout<<toString(Pres)<<std::endl;
										if(z3Coding.satisfy(Pres,satisfyFormula)==check_result::unsat){
											//continue next arrayAcess
											allArrayAcessDimMayEqual=false;
											break;
										}
									}
									else{
										//quantifier not in kthidx
										expr satisfyFormula=arrayAcessKthIdx==memoryunitKthIdx;
										if(z3Coding.satisfy(Pre,satisfyFormula)==check_result::unsat){
											allArrayAcessDimMayEqual=false;
											break;
										}
									}
								}
								if(allArrayAcessDimMayEqual==true){
									return true;
								}
							}
							else{
								//else direct check whether arrayAcess is equal to memoryunit1
								if(mayMemoryUnitIsIn(Pre,memoryunit1,arrayAcess)){
									return true;
								}
							}
						}
						else{
							//do nothing
							continue;
						}
					}
					return false;
				}
				else{
					vector<expr> * formulaMemoryUnits=z3Coding.getMemoryUnits(formula);
					for(expr memoryUnit: *formulaMemoryUnits){
						if(mayMemoryUnitIsIn(Pre,memoryunit1,memoryUnit)){
							return true;
						}
					}
					return false;
				}
			}
			else{
				std::cerr<<"Z3Coding:mayMemoryUnitIsInFormula: we can not process "<<memoryunit1<<std::endl;
				return true;
			}
		}
		/**
		 * @brief 
		 * @param Pre: we need Pre to compute primed formulas
		 * @param stmt
		 * @param scopeMemoryUnits : MemoryUnits is unprimed variable
		 * @return primed formulas: primed=unprimed
		 */
		vector<expr> * generatePrimed(vector<expr> * Pre,expr stmt, map<std::string,expr> * scopeMemoryUnits){
			vector<expr> * primedformulas=new vector<expr>();
			if(isAssignment(stmt)){
				expr primedlhs=stmt.arg(0);
				expr lhs=z3Coding.unprime(primedlhs);

				map<std::string,expr> * differents=new map<std::string,expr>();
				for(auto it=scopeMemoryUnits->begin();it!=scopeMemoryUnits->end();it++){
					std::pair<std::string,expr> p=*it;
					//std::cout<<lhs <<" mayMemoryUnitIsIn "<<p.second<<std::endl;
					if(!mayMemoryUnitIsIn(Pre,lhs,p.second)){
						differents->insert(p);
					}
				}
				// generate 
				for(auto it=differents->begin();it!=differents->end();it++){
					std::pair<std::string,expr> p=*it;
					expr memoryUnit=p.second;
					expr primedMemoryUnit=z3Coding.prime(memoryUnit);
					primedformulas->push_back(primedMemoryUnit==memoryUnit);
				}

			}
			else{
				// generate 
				for(auto it=scopeMemoryUnits->begin();it!=scopeMemoryUnits->end();it++){
					std::pair<std::string,expr> p=*it;
					expr memoryUnit=p.second;
					expr primedMemoryUnit=z3Coding.prime(memoryUnit);
					primedformulas->push_back(primedMemoryUnit==memoryUnit);
				}
			}
			return primedformulas;
		}
		bool equal(expr e1,expr e2){
			return eq(e1,e2);
		}

		compared_result compare(vector<expr>* Pre, expr e1, expr e2){
			expr assert=e1<e2;
			proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
			if(r==proved_result::proved){
				return compared_result::LT;
			}
			assert=e1>e2;
			r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
			if(r==proved_result::proved){
				return compared_result::GT;
			}
			assert=e1==e2;
			r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
			if(r==proved_result::proved){
				return compared_result::EQ;
			}
			assert=e1<=e2;
			r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
			if(r==proved_result::proved){
				return compared_result::LE;
			}
			assert=e1>=e2;
			r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
			if(r==proved_result::proved){
				return compared_result::GE;
			}
			return compared_result::Unknown;
		}
		vector<expr>* getAllIndexRelatedArrayAcessFormula(vector<expr> * formulas,expr phiIndex){
			/*std::cout<<"phiIndex is: "<<phiIndex<<std::endl;
			  std::cout<<"formulas is: "<<toString(formulas)<<std::endl;*/
			vector<expr> * allIndexRelatedArrayAcessFormula=new vector<expr>();
			for(expr f: *formulas){
				vector<expr> * arrayAcesses=z3Coding.getArrayAcess(f);
				for(expr ac: * arrayAcesses){
					if(isIn(phiIndex,z3Coding.getConsts(ac))){
						allIndexRelatedArrayAcessFormula->push_back(f);
						break;
					}
				}
			}
			return allIndexRelatedArrayAcessFormula;
		}
		vector<expr> * getAllForAllFormula(vector<expr> * formulas){
			vector<expr> * allForAllFormula=new vector<expr>();
			for(expr f: *formulas){
				if(f.is_quantifier()){
					allForAllFormula->push_back(f);
				}
			}
			return allForAllFormula;
		}

		bool existPhiFormula(vector<expr> * formulas){
			for(expr f: *formulas){
				if(z3Coding.isPhiFormula(f)){
					return true;
				}
			}
			return false;
		}
		vector<expr> * getAllPhiFormula(vector<expr> * formulas){
			vector<expr> * allPhiFormula=new vector<expr>();
			for(expr f: *formulas){
				if(z3Coding.isPhiFormula(f)){
					allPhiFormula->push_back(f);
				}
			}
			return allPhiFormula;
		}
		expr getPhiIndex(expr phiFormula){
			return z3Coding.getPhiIndex(phiFormula);
		}

		expr constructNewQuantifierName(vector<expr> * cons){
			int size=1000;
			map<unsigned,expr> *consMap=exprVectorToExprMap(cons);
			for(int i=0;i<size;i++){
				std::string quantifierName="_i"+std::to_string(i);
				expr quantifier=c.constant(quantifierName.c_str(),c.int_sort());
				if(!isIn(quantifier,consMap)){
				//if(!isIn(quantifier,cons)){
					return quantifier;
				}
			}
			std::cerr<<"Z3Coding:constructNewQuantifierName: something is wrong!"<<std::endl;
			return c.int_const("__error");
		}
		expr constructPhiFormula(expr index,expr init,expr step){
			return z3Coding.constructPhiFormula(index,init,step);
		}
		/**
		 * @brief closure preprocess, call before function: closure(formulas)
		 * @param Pre
		 * @param primedformulas
		 * @param stmt
		 * @return  
		 */
		vector<expr> * closure_preprocess(vector<expr> * Pre,vector<expr> * primedformulas, expr stmt){
			vector<expr> * ret=new vector<expr>();
			vector<expr> * new_Pre=new vector<expr>();
			pushAToB(Pre,new_Pre);
			new_Pre->push_back(stmt);
			for(expr e:*new_Pre){
				expr new_e=e;
				for(expr p: *primedformulas){
					new_e=z3Coding.substitute(new_e,p.arg(1),primedLift(p.arg(0)));
					new_e=z3Coding.substitute(new_e,z3Coding.simplify(p.arg(1)),primedLift(z3Coding.simplify(p.arg(0))));
				}
				if(!z3Coding.hasUnPrimedVariable(new_e)){
					ret->push_back(new_e);
				}
			}
			return ret;
		}
		
		vector<expr> * hasExprs(vector<expr> * formulas,expr e1,expr e2){
			vector<expr> * result=filtering(formulas,e1);
			result=filtering(result,e2);
			return result;
		}
		
		vector<expr> * closureMultiIndexRelationSubstitute(vector<expr>* formulas,expr from,expr to){
			vector<expr>* result=new vector<expr>();
			pushAToB(formulas,result);
			for(expr e:*formulas){
				if(!z3Coding.isForAllFormula(e)){
					expr subexpr=z3Coding.substitute(e,from,to);
					if(!z3Coding.isIn(subexpr,result)){
						result->push_back(subexpr);
					}
				}
			}
			return result;
		}
		vector<expr> * closureMultiIndexRelation(const clang::Stmt* clangStmt,vector<expr> * formulas){
			vector<expr> * result=new vector<expr>();
			pushAToB(formulas,result);
			if(avdiff->mapToStmtOut.count(clangStmt)>0){
				FlowSet* out=avdiff->mapToStmtOut.at(clangStmt);
				ValueListSet* vlsOut=(ValueListSet*)out;
				for(Property* p: vlsOut->elements){
					AtomVariablaDiff * avdiff=(AtomVariablaDiff *)p;
					expr index1=avdiff->av1->scalaVarz3coding;
					expr index2=avdiff->av2->scalaVarz3coding;
					expr equation1=avdiff->generateEquation1();
					expr equation2=avdiff->generateEquation2();
					vector<expr>* tmp=hasExprs(formulas,primedLift(index1),primedLift(index2));
					vector<expr>* newExprs=closureMultiIndexRelationSubstitute(tmp,primedLift(equation1.arg(0)),primedLift(equation1.arg(1)));
					for(expr e:*newExprs){
						if(!z3Coding.isIn(e,result)){
							result->push_back(e);
						}
					}
					newExprs=closureMultiIndexRelationSubstitute(tmp,primedLift(equation2.arg(0)),primedLift(equation2.arg(1)));
					for(expr e:*newExprs){
						if(!z3Coding.isIn(e,result)){
							result->push_back(e);
						}
					}
				/*	if(!z3Coding.isIn(primedLift(equation1),result)){
						result->push_back(primedLift(equation1));
					}
					if(!z3Coding.isIn(primedLift(equation2),result)){
						result->push_back(primedLift(equation2));
					}*/
				}
			}
			return result; 
		}
		/**
		 * @brief generate closure(primedformulas and Pre) 
		 * @param Pre
		 * @param primedformulas
		 * @param stmt
		 * @return 
		 */
		vector<expr> * closure(const clang::Stmt* clangStmt,vector<expr> * Pre,
		vector<expr> * primedformulas, expr stmt,CFGBlock* n){
			vector<expr> * closureformulas=new vector<expr>();
			if(isAssigndToScaleVariable(stmt)||!isAssignment(stmt)){
				if(isIndexUpdate(clangStmt,stmt)){
					//generate forall formula from phi formula
					//forall formula updated
					//synthesis forall formula from some forall formula
					bool isKillPhi=false;;
					closureformulas=closureIndexUpdate(clangStmt,Pre,primedformulas,stmt,&isKillPhi,n);
					
					
					//transfer phi
					vector<expr> *allPhi=getAllPhiFormula(closureformulas);
					expr index=z3Coding.unprime(stmt.arg(0));
					expr thephi=z3Coding._error;
					for(expr phi:* allPhi){
						expr phiIndex=getPhiIndex(phi);
						if(!equal(index,phiIndex)){
							//closureformulas->push_back(z3Coding.constructPhiFormula(z3Coding.prime(phiIndex)));
							closureformulas->push_back(primedLift(phi));
						}
						else{
							thephi=phi;
						}
					}
					#ifdef _NON_PATHGUIDE_VERSION
					if(!isKillPhi){
						//expr phi=z3Coding.constructPhiFormula(index);
						if(!z3Coding.checkError(thephi)&&isIn(thephi,allPhi)){
							//closureformulas->push_back(z3Coding.constructPhiFormula(z3Coding.prime(index)));
							closureformulas->push_back(primedLift(thephi));
						}
					}
					#endif
					
				}
				else if(isIndexInit(clangStmt,stmt)){
					closureformulas=closureIndexInit(clangStmt,Pre,primedformulas,stmt);
					
					//transfer phi
					vector<expr> *allPhi=getAllPhiFormula(closureformulas);
					vector<expr> *allPrimedPhi=primedLift(allPhi);
					pushAToB(allPrimedPhi,closureformulas);
				}
				else{
					//other AssigndToScaleVariable or non-Assignment
					vector<expr> * formulas=new vector<expr>();
					pushAToB(Pre,formulas);
					pushAToB(primedformulas,formulas);
					formulas->push_back(stmt);
						time_t start,stop;
						start = time(NULL);
					
					closureformulas=closure(closure_preprocess(Pre,primedformulas,stmt)/*formulas*/);
						stop = time(NULL);
//						std::cout<<"closure Time:"<<stop-start<<std::endl;
					//transfer phi
					vector<expr> *allPhi=getAllPhiFormula(closureformulas);
					vector<expr> *allPrimedPhi=primedLift(allPhi);
					pushAToB(allPrimedPhi,closureformulas);
				}
			}
			else if(isAssigndToArrayAcess(stmt)){
				closureformulas=closureAssigndToArrayAcess(clangStmt,Pre,primedformulas,stmt);
				//transfer phi
				vector<expr> *allPhi=getAllPhiFormula(closureformulas);
				vector<expr> *allPrimedPhi=primedLift(allPhi);
				pushAToB(allPrimedPhi,closureformulas);
			}
			//process mitil index relations
			closureformulas=closureMultiIndexRelation(clangStmt,closureformulas);
			return closureformulas;
		}

		bool isIn(expr e,vector<expr> * exprs){
			for(expr ele: *exprs){
				if(equal(e,ele)){
					return true;
				}
			}
			return false;
		}

		bool isIn(expr e,map<unsigned,expr> * exprsMap){
			if(exprsMap->count(e.hash())>0){
				return true;
			}
			return false;
		}
		
		time_t start,stop;
		/**
		 * @brief 
		 * @param formulas
		 * @return 
		 */
		vector<expr> * closure(vector<expr> * formulas){
			//std::cout<<"----------------formulas-----------------------"<<std::endl;
//			std::cout<<toString(formulas)<<std::endl;
			vector<expr> * canonicalformulas=z3Coding.canonical(formulas);
			vector<expr> * queue=new vector<expr>();
			vector<expr> * closureformulas=new vector<expr>();
			pushAToB(canonicalformulas,closureformulas);
			pushAToB(canonicalformulas,queue);
			vector<expr> *  dequeue=new vector<expr>();
			
			map<unsigned,expr> *closureformulasMap=exprVectorToExprMap(closureformulas);
			
			
			while(!queue->empty()){
				
				//std::cout<<queue->size()<<":"<<closureformulas->size()<<std::endl;
				//std::cout<<"----------------closureformulas-----------------------"<<std::endl;
				//std::cout<<toString(closureformulas)<<std::endl;
				//std::cout<<"----------------queue-----------------------"<<std::endl;
				//std::cout<<toString(queue)<<std::endl;*/
				
				expr formula=queue->front(); queue->erase (queue->begin()); dequeue->push_back(formula);
				
				//std::cout<<queue->size()<<":"<<closureformulas->size()<<std::endl;
				
				
				
				if(z3Coding.isSimpleFormula(formula)){
					if(formula.is_app()){
						
						if(formula.decl().name().str()=="="){
							//std::cout<<"closureEq..."<<std::endl;
			
							vector<expr> * freshformulas=closureEq(formula,closureformulas,closureformulasMap);
							
							//printf("two Use Time:%ld\n",(stop-start));
							//std::cout<<"closureEq..."<<std::endl;
							//std::cout<<toString(freshformulas)<<std::endl;
							for(expr freshform: *freshformulas){
								//if(!isIn(freshform,queue)&&!isIn(freshform,dequeue)){
									if(!freshform.is_quantifier()){
										queue->push_back(freshform);
									}
									if(z3Coding.equal((2>=c.int_const("i__prime")),freshform)||z3Coding.equal((c.int_const("i__prime")>=2),freshform)){
										std::cout<<toString(freshformulas)<<std::endl;
									}
									closureformulas->push_back(freshform);
									exprMapAdd(freshform,closureformulasMap);
								//}
								/*if(!isIn(freshform,closureformulas)){
									closureformulas->push_back(freshform);
								}*/
							}
						}
						//else if(formula.decl().name().str()=="!="){
						//	vector<expr> * freshformulas=closureNeq(formula,closureformulas);
						//	for(expr freshform: *freshformulas){
						//		if(!isIn(freshform,queue)){
						//			queue->push_back(freshform);
						//		}
						//	}
						//}
						else if(formula.decl().name().str()==">="){
							//std::cout<<"closureGe..."<<std::endl;
							vector<expr> * freshformulas=closureGe(formula,closureformulas,closureformulasMap);
							//std::cout<<"closureGe..."<<std::endl;
							//std::cout<<toString(freshformulas)<<std::endl;
							for(expr freshform: *freshformulas){
								//freshformulas disjoint closureformulas
								//queue+dequeue is include in  closureformulas
								//if(!isIn(freshform,queue)&&!isIn(freshform,dequeue)){   
									if(!freshform.is_quantifier()){
										queue->push_back(freshform);
									}
									if(z3Coding.equal((2>=c.int_const("i__prime")),freshform)||z3Coding.equal((c.int_const("i__prime")>=2),freshform)){
										std::cout<<toString(freshformulas)<<std::endl;
									}
									closureformulas->push_back(freshform);
									exprMapAdd(freshform,closureformulasMap);
								//}
//								if(!isIn(freshform,closureformulas)){
//									closureformulas->push_back(freshform);
//								}
							}
						}
						else if(formula.decl().name().str()=="<="){
							//std::cout<<"closureLe..."<<std::endl;
							vector<expr> * freshformulas=closureLe(formula,closureformulas,closureformulasMap);
							//std::cout<<"closureLe..."<<std::endl;
							//std::cout<<toString(freshformulas)<<std::endl;
							for(expr freshform: *freshformulas){
								if(!freshform.is_quantifier()){
										queue->push_back(freshform);
								}
								if(z3Coding.equal((2>=c.int_const("i__prime")),freshform)||z3Coding.equal((c.int_const("i__prime")>=2),freshform)){
										std::cout<<toString(freshformulas)<<std::endl;
								}
								closureformulas->push_back(freshform);
								exprMapAdd(freshform,closureformulasMap);
//								if(!isIn(freshform,closureformulas)){
//									closureformulas->push_back(freshform);
//								}
							}
						}
						else if(formula.decl().name().str()==">"){
							//std::cout<<"closureGt..."<<std::endl;
							vector<expr> * freshformulas=closureGt(formula,closureformulas,closureformulasMap);
							//std::cout<<"closureGt..."<<std::endl;
							//std::cout<<toString(freshformulas)<<std::endl;
							for(expr freshform: *freshformulas){
								if(!freshform.is_quantifier()){
										queue->push_back(freshform);
								}
								if(z3Coding.equal((2>=c.int_const("i__prime")),freshform)||z3Coding.equal((c.int_const("i__prime")>=2),freshform)){
										std::cout<<toString(freshformulas)<<std::endl;
								}
								closureformulas->push_back(freshform);
								exprMapAdd(freshform,closureformulasMap);
//								if(!isIn(freshform,closureformulas)){
//									closureformulas->push_back(freshform);
//								}
							}
						}
						else if(formula.decl().name().str()=="<"){
							//std::cout<<"closureLt..."<<std::endl;
							vector<expr> * freshformulas=closureLt(formula,closureformulas,closureformulasMap);
							//std::cout<<"closureLt..."<<std::endl;
							//std::cout<<toString(freshformulas)<<std::endl;
							for(expr freshform: *freshformulas){
								if(!freshform.is_quantifier()){
										queue->push_back(freshform);
								}
								if(z3Coding.equal((2>=c.int_const("i__prime")),freshform)||z3Coding.equal((c.int_const("i__prime")>=2),freshform)){
										std::cout<<toString(freshformulas)<<std::endl;
								}
								closureformulas->push_back(freshform);
								exprMapAdd(freshform,closureformulasMap);
//								if(!isIn(freshform,closureformulas)){
//									closureformulas->push_back(freshform);
//								}
							}
						}
					}
				}

			}
			//std::cout<<"----------------closureformulas-----------------------"<<std::endl;
			//std::cout<<toString(closureformulas)<<std::endl;*/
			return closureformulas;
		}
		
		
		bool isRecurrenceEquation(expr formula){
			if(formula.decl().name().str()=="="){
				expr left=formula.arg(0);
				expr right=formula.arg(1);
				expr newLeft=z3Coding.substitute(left,right,left);
				expr newright=z3Coding.substitute(right,left,right);
				if(equal(left,newLeft)&&equal(right,newright)){
					return false;
				}
				return true;
			}
			return false;
		}
		vector<expr> * unrecurrenceFormulaFiltering(vector<expr> *formulas){
			vector<expr> * ret=new vector<expr>();
			for(expr f: *formulas){
				if(!isRecurrenceEquation(f)){
					ret->push_back(f);
				}
			}
			return ret;
		}
		bool flag=false;
		
		expr closureEqSubstitute(expr e,expr from,expr to){
			expr Eq=from==to;
			
			if(e.is_app()&&e.decl().name().str()=="="){
				expr eleft=e.arg(0);
				expr eright=e.arg(1);
				if(equal(eleft,from)){
					return to==eright;
				}
				if(equal(eright,from)){
					return eleft==to;
				}
			}
			
			/*else if(!isRecurrenceEquation(Eq)){
				return z3Coding.substitute(e,from,to);
			}*/
			else if(e.is_quantifier()){
				expr quantifier=z3Coding.getQuantifier(e);
				expr beginFormula=z3Coding.getQuantifierBeginFormula(e);
				expr endFormula=z3Coding.getQuantifierEndFormula(e);
				expr extendFormula=z3Coding.getQuantifierExtendFormula(e);
				expr body=z3Coding.getQuantifierFormulaBody(e);
				expr step=z3Coding.getQuantifierStep(e);
				expr stepFormula=z3Coding.getQuantifierStepFormula(e);
				expr newbeginFormula=closureEqSubstitute(beginFormula,from,to);
				expr newendFormula=closureEqSubstitute(endFormula,from,to);
				expr newbody=closureEqSubstitute(body,from,to);
				if(!z3Coding.checkError(extendFormula)){
					expr newextendFormula=closureEqSubstitute(extendFormula,from,to);
					return z3Coding.constructForAllFormula(quantifier,newextendFormula,newbeginFormula,newendFormula,stepFormula,newbody);
				}
				else{
					return z3Coding.constructForAllFormula(quantifier,newbeginFormula,newendFormula,stepFormula,newbody);
				}

//				if(!equal(newbeginFormula,beginFormula)){
//					if(z3Coding.checkError(extendFormula)){
//						return z3Coding.constructForAllFormula(quantifier,newbeginFormula,endFormula,step,body);
//					}
//					else{
//						return z3Coding.constructForAllFormula(quantifier,extendFormula,newbeginFormula,endFormula,step,body);
//					}
//				}
//				
//				expr newendFormula=closureEqSubstitute(endFormula,from,to);
//				if(!equal(newendFormula,endFormula)){
//					if(z3Coding.checkError(extendFormula)){
//						return z3Coding.constructForAllFormula(quantifier,beginFormula,newendFormula,step,body);
//					}
//					else{
//						return z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,newendFormula,step,body);
//					}
//				}
//				if(!z3Coding.checkError(extendFormula)){
//					expr newextendFormula=closureEqSubstitute(extendFormula,from,to);
//					if(!equal(newextendFormula,extendFormula)){
//						return z3Coding.constructForAllFormula(quantifier,newextendFormula,beginFormula,endFormula,step,body);
//					}
//				}
//				expr newbody=closureEqSubstitute(body,from,to);
//				if(!equal(newbody,body)){
//					if(z3Coding.checkError(extendFormula)){
//						return z3Coding.constructForAllFormula(quantifier,beginFormula,endFormula,step,newbody);
//					}
//					else{
//						return z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,endFormula,step,newbody);
//					}
//				}
				
			}
			else if(e.is_app()&&e.decl().name().str()=="<"){
				expr eleft=e.arg(0);
				expr eright=e.arg(1);
				if(equal(eleft,from)){
					return to<eright;
				}
				if(equal(eright,from)){
					return eleft<to;
				}
			}
			else if(e.is_app()&&e.decl().name().str()=="<="){
				expr eleft=e.arg(0);
				expr eright=e.arg(1);
				if(equal(eleft,from)){
					return to<=eright;
				}
				if(equal(eright,from)){
					return eleft<=to;
				}
			}
			else if(e.is_app()&&e.decl().name().str()==">"){
				expr eleft=e.arg(0);
				expr eright=e.arg(1);
				if(equal(eleft,from)){
					return to>eright;
				}
				if(equal(eright,from)){
					return eleft>to;
				}
			}
			else if(e.is_app()&&e.decl().name().str()==">="){
				expr eleft=e.arg(0);
				expr eright=e.arg(1);
				if(equal(eleft,from)){
					return to>=eright;
				}
				if(equal(eright,from)){
					return eleft>=to;
				}
			}
			
			return e;
		}
		/**
		 * @brief note: Eq may be in formulas, return new formulas that disjoint  (Eq+formulas) 
		 * 			closureEq(Eq,newformulas)==newformulas, that means closure 
		 * @param Eq
		 * @param formulas
		 * @return new formulas that disjoint  (Eq+formulas), and closureEq(Eq,newformulas)==newformulas
		 */
		vector<expr> * closureEq(expr Eq,vector<expr> * formulas,map<unsigned,expr> *formulasMap){
			if(!(Eq.is_app()&&Eq.decl().name().str()=="=")) {
				std::cerr<<"Z3Coding:closureEq: something is wrong!"<<std::endl;
				return nullptr;
			}
			//std::cout<<toString(formulas)<<std::endl;
			expr left=Eq.arg(0);
			expr right=Eq.arg(1);
			vector<expr> * oldformulas=new vector<expr>();
			pushAToB(formulas,oldformulas);
			oldformulas->push_back(Eq);
			vector<expr> * newFormulas=new vector<expr>();
			vector<expr> * queue=new vector<expr>();
			pushAToB(formulas,queue);
			
			//just for optimization
			
			map<unsigned,expr> *oldformulasMap=exprMapClone(formulasMap);
			exprMapAdd(Eq,oldformulasMap); 
			map<unsigned,expr> *queueMap=exprMapClone(formulasMap);
			map<unsigned,expr> *newFormulasMap=exprVectorToExprMap(newFormulas);
			
			while(!queue->empty()){
				if(queue->size()%500==0){
					//std::cout<<queue->size()<<std::endl;
				}
				expr f=queue->front(); queue->erase(queue->begin()); exprMapRemove(f,queueMap);
				
				expr newf=closureEqSubstitute(f,left,right);/*z3Coding.substitute(f,left,right);*/
				
				//if(!equal(newf,f)){
					if(!isIn(newf,oldformulasMap)&&!isIn(newf,queueMap)&&!isIn(newf,newFormulasMap)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
						
						exprMapAdd(newf,newFormulasMap);
						exprMapAdd(newf,queueMap);
					}
				//}
				
				newf=closureEqSubstitute(f,right,left);/*z3Coding.substitute(f,right,left);*/
				//if(!equal(newf,f)){
					if(!isIn(newf,oldformulasMap)&&!isIn(newf,queueMap)&&!isIn(newf,newFormulasMap)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
						
						exprMapAdd(newf,newFormulasMap);
						exprMapAdd(newf,queueMap);
					}
				//}
				
			}
			return z3Coding.eliminateIdenticalEquation(newFormulas);
		}
		
		
		
		vector<expr> * closureEqStar(Formula* Eq,vector<Formula*> * formulas){
			if(!(Eq->formula.is_app()&&Eq->formula.decl().name().str()=="=")) {
				std::cerr<<"Z3Coding:closureEq: something is wrong!"<<std::endl;
				return nullptr;
			}
			//std::cout<<toString(eliminateStar(formulas))<<std::endl;
			expr left=Eq->formula.arg(0);
			expr right=Eq->formula.arg(1);
			vector<Formula*> * oldformulas=new vector<Formula*>();
			pushAToBStar(formulas,oldformulas);
			oldformulas->push_back(Eq);
			vector<Formula*> * newFormulas=new vector<Formula*>();
			vector<Formula*> * queue=new vector<Formula*>();
			pushAToBStar(formulas,queue);
			while(!queue->empty()){
				if(queue->size()%500==0){
					//std::cout<<queue->size()<<std::endl;
				}
				
				Formula* f=queue->front(); queue->erase(queue->begin());
				expr ff=f->formula;
				Formula* newf=new Formula(z3Coding.substitute(ff,left,right));
				if(!equal(newf->formula,ff)){
					if(!isInStar(newf,oldformulas)&&!isInStar(newf,queue)&&!isInStar(newf,newFormulas)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
					}
				}
				//Formula* newf=new Formula(c.int_const("a")==c.int_const("b")); 
				//std::cout<<toString(eliminateStar(oldformulas))<<std::endl;
				//std::cout<<toString(eliminateStar(queue))<<std::endl;
				//std::cout<<toString(eliminateStar(newFormulas))<<std::endl;
				
				
				newf=new Formula(z3Coding.substitute(ff,right,left));
				if(!equal(newf->formula,ff)){
					if(!isInStar(newf,oldformulas)&&!isInStar(newf,queue)&&!isInStar(newf,newFormulas)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
					}
				}
				//newf=new Formula(c.int_const("a")==c.int_const("b"));
				
			}
			return z3Coding.eliminateIdenticalEquation(eliminateStar(newFormulas));
			
		}
		
		bool isInStar(Formula* e,vector<Formula*> * exprs){
			
			std::string ename=Z3_ast_to_string(c,e->formula);
			for(Formula *ele: *exprs){
				//std::cout<<*ele<<std::endl;
				std::string name=Z3_ast_to_string(c,ele->formula);
				if(name==ename){
					return true;
				}
			}
			return false;
		}
		
//		bool isInStar(Formula* e,vector<Formula*> * exprs){
//			
//			std::string ename=Z3_ast_to_string(c,e->formula);
//			std::string name=ename+"wwww";
//			int i=0;
//			for(Formula *ele: *exprs){
//				//std::cout<<*ele<<std::endl;
////				std::string name=Z3_ast_to_string(c,ele->formula);
////				if(name==ename){
////					return true;
////				}
//				std::string name=std::to_string(i);
//				if(name==ename){
//					return true;
//				}
//				i++;
//			}
//			return true;
//		}
		vector<expr> * eliminateStar(vector<Formula*> * stars){
			vector<expr> * newFormulas=new vector<expr>();
			for(Formula *ele: *stars){
				newFormulas->push_back(ele->formula);
			}
			return newFormulas;
		}
		vector<Formula*> * addStar(vector<expr> * nostars){
			vector<Formula*> * newFormulas=new vector<Formula*>();
			for(expr ele: *nostars){
				newFormulas->push_back(new Formula(ele));
			}
			return newFormulas;
		}
		void pushAToBStar(vector<Formula*> * & A,vector<Formula*> * & B){
			for(auto it=A->begin();it != A->end(); it++){
				Formula* t=*it;
				B->push_back(t);
			}
		}

		//		/**
		//		 * @brief note: Eq may be in formulas, return new formulas that disjoint  (Eq+formulas) 
		//		 * @param Neq
		//		 * @param formulas
		//		 * @return 
		//		 */
		//		// has no process forall formula
		//		vector<expr> * closureNeq(expr Neq,vector<expr> * formulas){
		//			if(!(Neq.is_app()&&Neq.decl().name().str()=="!=")) {
		//				std::cerr<<"Z3Coding:closureNeq: something is wrong!"<<std::endl;
		//				return nullptr;
		//			}
		//			vector<expr> * newFormulas=new vector<expr>();
		//			return newFormulas;
		//		}

		vector<expr>* closureLtForAllFormula(expr Lt,expr forallFromula){
			//a<=b
			expr left=Lt.arg(0);
			expr right=Lt.arg(1);
			//forall x. extendFormula&&init<=|<x&&x<|<=end,body

			vector<expr>* queue=new vector<expr>();
			vector<expr>* newFormulas=new vector<expr>();
			queue->push_back(forallFromula);
			
			map<unsigned,expr> *queueMap=exprVectorToExprMap(queue);
			map<unsigned,expr> *newFormulasMap=exprVectorToExprMap(newFormulas);
			
			while(!queue->empty()){
				expr f=queue->front(); queue->erase (queue->begin()); exprMapRemove(f,queueMap);
				if(f.is_quantifier()){
					expr quantifier=z3Coding.getQuantifier(f);
					expr init=z3Coding.getQuantifierBegin(f);
					expr end=z3Coding.getQuantifierEnd(f);
					expr step=z3Coding.getQuantifierStep(f);
					expr stepFormula=z3Coding.getQuantifierStepFormula(f);
					expr beginFormula=z3Coding.getQuantifierBeginFormula(forallFromula);
					expr endFormula=z3Coding.getQuantifierEndFormula(forallFromula);
					expr extendFormula=z3Coding.getQuantifierExtendFormula(forallFromula);
					expr forallBody=z3Coding.getQuantifierFormulaBody(f);
					// if init==a
					// gen: forall x. extendFormula&&b<=|<x&&x<|<=end,body
					expr newForAllFormula(c);
					if(equal(init,left)){
						expr newbeginFormula(c);
						if(beginFormula.decl().name().str()=="<="){
							newbeginFormula=z3Coding.substitute(beginFormula,init,right);
						}
						else if(beginFormula.decl().name().str()=="<") {
							newbeginFormula=right<=quantifier;
						}
						if(z3Coding.checkError(extendFormula)){
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,newbeginFormula,endFormula,stepFormula,forallBody);
						}
						else{
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,extendFormula,newbeginFormula,endFormula,stepFormula,forallBody);
						}
						if(!isIn(newForAllFormula,queueMap)&&!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,f)){
							queue->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,queueMap);
						}
						if(!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,forallFromula)){
							newFormulas->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,newFormulasMap);
						}
					}

					// if end==b
					// gen: forall x. extendFormula&&init<=|<x&&x<|<=b,body
					if(equal(end,right)){
						expr newendFormula(c);
						if(endFormula.decl().name().str()=="<="){
							newendFormula=z3Coding.substitute(endFormula,end,left);
						}
						else if(endFormula.decl().name().str()=="<"){
							newendFormula=quantifier<left;
						}
						if(z3Coding.checkError(extendFormula)){
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,beginFormula,newendFormula,stepFormula,forallBody);
						}
						else{
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,newendFormula,stepFormula,forallBody);
						}
						if(!isIn(newForAllFormula,queueMap)&&!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,f)){
							queue->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,queueMap);
						}
						if(!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,forallFromula)){
							newFormulas->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,newFormulasMap);
						}
					}

					vector<expr> *tmp=new vector<expr>();
					tmp->push_back(forallBody);
					map<unsigned,expr> *tmpMap=exprVectorToExprMap(tmp);
					vector<expr> *newtmps=closureLt(Lt,tmp,tmpMap);
					vector<expr> *newforallBodys=filteringWithQuantifier(newtmps,quantifier);
					for(expr newbody:*newforallBodys){
						if(z3Coding.checkError(extendFormula)){
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,beginFormula,endFormula,stepFormula,newbody);
						}
						else{
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,endFormula,stepFormula,newbody);
						}
						if(!isIn(newForAllFormula,queueMap)&&!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,f)){
							queue->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,queueMap);
						}
						if(!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,forallFromula)){
							newFormulas->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,newFormulasMap);
						}
					}

				}
			}
			return newFormulas;
		}
		
		
		
		vector<expr> * closureLt(expr Lt,vector<expr> * formulas,map<unsigned,expr> *formulasMap){
			if(!(Lt.is_app()&&Lt.decl().name().str()=="<")) {
				std::cerr<<"Z3Coding:closureLt: something is wrong!"<<std::endl;
				return nullptr;
			}
			expr left=Lt.arg(0);
			expr right=Lt.arg(1);
//			std::string rightName=Z3_ast_to_string(c,right);
//			std::string leftName=Z3_ast_to_string(c,left);
			vector<expr> * oldformulas=new vector<expr>();
			pushAToB(formulas,oldformulas);
			oldformulas->push_back(Lt);
			vector<expr> * newFormulas=new vector<expr>();
			vector<expr> * queue=new vector<expr>();
			pushAToB(formulas,queue);
			
			
			map<unsigned,expr> *oldformulasMap=exprMapClone(formulasMap);
			exprMapAdd(Lt,oldformulasMap);
			map<unsigned,expr> *queueMap=exprMapClone(formulasMap);
			map<unsigned,expr> *newFormulasMap=exprVectorToExprMap(newFormulas);
			
			
			
			
			while(!queue->empty()){
//				if(flag){
//					std::cout<<queue->size()<<std::endl;
//				}
				expr f=queue->front(); queue->erase (queue->begin());exprMapRemove(f,queueMap);
				expr newf=f;
				if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.LtDecl)/*f.decl().name().str()=="<"*/){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					
					if(equal(f.arg(0),right)){
						newf=left<f.arg(1);
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.LeDecl)/*f.decl().name().str()=="<="*/){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					
					if(equal(f.arg(0),right)){
						newf=left<f.arg(1);
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.GtDecl)/*f.decl().name().str()==">"*/){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
	
					if(equal(f.arg(1),right)){
						newf=right<f.arg(0);
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.GeDecl)/*f.decl().name().str()==">="*/){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
			
					if(equal(f.arg(1),right)){
						newf=right<f.arg(0);
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.EqDecl)/*f.decl().name().str()=="="*/){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
			
					if(equal(f.arg(0),right)){
						newf=left<f.arg(1);
					}
					else if(equal(f.arg(1),right)){
						newf=left<f.arg(0);
					}
				}
				if(!equal(newf,f)){
					if(!isIn(newf,oldformulasMap)&&!isIn(newf,queueMap)&&!isIn(newf,newFormulasMap)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
						
						exprMapAdd(newf,newFormulasMap);
						exprMapAdd(newf,queueMap);
					}
				}
				


				if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.LtDecl)/*f.decl().name().str()=="<"*/){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
			
					if(equal(f.arg(1),left)/*frightName==leftName*/){
						newf=f.arg(0)<right;
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.LeDecl)/*f.decl().name().str()=="<="*/){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					
					if(equal(f.arg(1),left)/*frightName==leftName*/){
						newf=f.arg(0)<right;
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.GtDecl)/*f.decl().name().str()==">"*/){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					
					if(equal(f.arg(0),left)/*fleftName==leftName*/){
						newf=right>f.arg(1);
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.GeDecl)/*f.decl().name().str()==">="*/){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					
					if(equal(f.arg(0),left)/*fleftName==leftName*/){
						newf=right>f.arg(1);
					}
				}
				else if(f.is_app()&&Z3_is_eq_func_decl(c,f.decl(),z3Coding.EqDecl)/*f.decl().name().str()=="="*/){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
				
					if(equal(f.arg(0),left)/*fleftName==leftName*/){
						newf=f.arg(1)<right;
					}
					else if(equal(f.arg(1),left)/*frightName==leftName*/){
						newf=f.arg(0)<right;
					}
				}
				if(!equal(newf,f)){
					if(!isIn(newf,oldformulasMap)&&!isIn(newf,queueMap)&&!isIn(newf,newFormulasMap)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
						
						exprMapAdd(newf,newFormulasMap);
						exprMapAdd(newf,queueMap);
					}
				}

				
				if(f.is_quantifier()){
					vector<expr> * newForAllFormulas=closureLtForAllFormula(Lt,f);
					for(expr newForAllF: *newForAllFormulas){
						if(!isIn(newForAllF,oldformulasMap)&&!isIn(newForAllF,queueMap)&&!isIn(newForAllF,newFormulasMap)){
							newFormulas->push_back(newForAllF);
							//newForAllF will not add to queue to compute closure
							
							exprMapAdd(newf,newFormulasMap);
						}
					}
				}
			}
			return z3Coding.eliminateIdenticalEquation(newFormulas);
		}
		/**
		 * @brief return new formulas that disjoint  (Le+forallFromula) 
		 * @param Le
		 * @param forallFromula
		 * @return 
		 */
		vector<expr>* closureLeForAllFormula(expr Le,expr forallFromula){
			//a<=b
			expr left=Le.arg(0);
			expr right=Le.arg(1);
			//forall x. extendFormula&&init<=|<x&&x<|<=end,body

			vector<expr>* queue=new vector<expr>();
			vector<expr>* newFormulas=new vector<expr>();
			queue->push_back(forallFromula);
			
		
			map<unsigned,expr> *queueMap=exprVectorToExprMap(queue);
			map<unsigned,expr> *newFormulasMap=exprVectorToExprMap(newFormulas);
			
			
			while(!queue->empty()){
				expr f=queue->front(); queue->erase (queue->begin()); exprMapRemove(f,queueMap);
				if(f.is_quantifier()){
					expr quantifier=z3Coding.getQuantifier(f);
					expr init=z3Coding.getQuantifierBegin(f);
					expr end=z3Coding.getQuantifierEnd(f);
					expr step=z3Coding.getQuantifierStep(f);
					expr stepFormula=z3Coding.getQuantifierStepFormula(f);
					expr beginFormula=z3Coding.getQuantifierBeginFormula(forallFromula);
					expr endFormula=z3Coding.getQuantifierEndFormula(forallFromula);
					expr extendFormula=z3Coding.getQuantifierExtendFormula(forallFromula);
					expr forallBody=z3Coding.getQuantifierFormulaBody(f);
					// if init==a
					// gen: forall x. extendFormula&&b<=|<x&&x<|<=end,body
					expr newForAllFormula(c);
					if(equal(init,left)){
						expr newbeginFormula=z3Coding.substitute(beginFormula,init,right);
						if(z3Coding.checkError(extendFormula)){
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,newbeginFormula,endFormula,stepFormula,forallBody);
						}
						else{
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,extendFormula,newbeginFormula,endFormula,stepFormula,forallBody);
						}
//						if(!equal(newForAllFormula,f)){
							if(!isIn(newForAllFormula,queueMap)&&!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,f)){
								queue->push_back(newForAllFormula);
								
								exprMapAdd(newForAllFormula,queueMap);
							}
							if(!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,forallFromula)){
								newFormulas->push_back(newForAllFormula);
								
								exprMapAdd(newForAllFormula,newFormulasMap);
							}
//						}
					}

					// if end==b
					// gen: forall x. extendFormula&&init<=|<x&&x<|<=b,body
					if(equal(end,right)){
						expr newendFormula=z3Coding.substitute(endFormula,end,left);
						if(z3Coding.checkError(extendFormula)){
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,beginFormula,newendFormula,stepFormula,forallBody);
						}
						else{
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,newendFormula,stepFormula,forallBody);
						}
//						if(!equal(newForAllFormula,f)){
							if(!isIn(newForAllFormula,queueMap)&&!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,f)){
								queue->push_back(newForAllFormula);
								
								exprMapAdd(newForAllFormula,queueMap);
							}
							if(!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,forallFromula)){
								newFormulas->push_back(newForAllFormula);
								
								exprMapAdd(newForAllFormula,newFormulasMap);
							}
//						}
					}

					vector<expr> *tmp=new vector<expr>();
					tmp->push_back(forallBody);
					map<unsigned,expr> *tmpMap=exprVectorToExprMap(tmp);
					vector<expr> *newtmps=closureLe(Le,tmp,tmpMap);
					vector<expr> *newforallBodys=filteringWithQuantifier(newtmps,quantifier);
					for(expr newbody:*newforallBodys){
						if(z3Coding.checkError(extendFormula)){
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,beginFormula,endFormula,stepFormula,newbody);
						}
						else{
							newForAllFormula=z3Coding.constructForAllFormula(quantifier,extendFormula,beginFormula,endFormula,stepFormula,newbody);
						}
						if(!isIn(newForAllFormula,queueMap)&&!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,f)){
							queue->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,queueMap);
						}
						if(!isIn(newForAllFormula,newFormulasMap)&&!equal(newForAllFormula,forallFromula)){
							newFormulas->push_back(newForAllFormula);
							
							exprMapAdd(newForAllFormula,newFormulasMap);
						}
					}

				}
			}
			return newFormulas;

		}
		//vector<std::string> * formulasStr,
		vector<expr> * closureLe(expr Le,vector<expr> * formulas,map<unsigned,expr> *formulasMap){
			if(!(Le.is_app()&&Le.decl().name().str()=="<=")) {
				std::cerr<<"Z3Coding:closureLe: something is wrong!"<<std::endl;
				return nullptr;
			}
			expr left=Le.arg(0);
			expr right=Le.arg(1);
//			std::string rightName=Z3_ast_to_string(c,right);
//			std::string leftName=Z3_ast_to_string(c,left);
			vector<expr> * oldformulas=new vector<expr>();
			pushAToB(formulas,oldformulas);
			oldformulas->push_back(Le);
			vector<expr> * newFormulas=new vector<expr>();
			vector<expr> * queue=new vector<expr>();
			pushAToB(formulas,queue);
			
			
			map<unsigned,expr> *oldformulasMap=exprMapClone(formulasMap);
			exprMapAdd(Le,oldformulasMap);
			map<unsigned,expr> *queueMap=exprMapClone(formulasMap);
			map<unsigned,expr> *newFormulasMap=exprVectorToExprMap(newFormulas);
			
			
			while(!queue->empty()){
				expr f=queue->front(); queue->erase (queue->begin()); exprMapRemove(f,queueMap);
				expr newf=f;
				if(f.is_app()&&f.decl().name().str()=="<"){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					if(equal(f.arg(0),right)/*fleftName==rightName*/){
						newf=left<f.arg(1);
					}
				}
				else if(f.is_app()&&f.decl().name().str()=="<="){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					if(equal(f.arg(0),right)/*fleftName==rightName*/){
						newf=left<=f.arg(1);
					}
				}
				else if(f.is_app()&&f.decl().name().str()==">"){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					if(equal(f.arg(1),right)/*frightName==rightName*/){
						newf=right<f.arg(0);
					}
				}
				else if(f.is_app()&&f.decl().name().str()==">="){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					if(equal(f.arg(1),right)/*frightName==rightName*/){
						newf=right<=f.arg(0);
					}
				}
				else if(f.is_app()&&f.decl().name().str()=="="){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					if(equal(f.arg(0),right)/*fleftName==rightName*/){
						newf=left<=f.arg(1);
					}
					else if(equal(f.arg(1),right)/*frightName==rightName*/){
						newf=left<=f.arg(0);
					}
				}
				//if(!equal(newf,f)){
					if(!isIn(newf,oldformulasMap)&&!isIn(newf,queueMap)&&!isIn(newf,newFormulasMap)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
						
						exprMapAdd(newf,newFormulasMap);
						exprMapAdd(newf,queueMap);
					}
				//}
				


				if(f.is_app()&&f.decl().name().str()=="<"){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					
					if(equal(f.arg(1),left)/*frightName==leftName*/){
						newf=f.arg(0)<right;
					}
				}
				else if(f.is_app()&&f.decl().name().str()=="<="){
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					if(equal(f.arg(1),left)/*frightName==leftName*/){
						newf=f.arg(0)<=right;
					}
				}
				else if(f.is_app()&&f.decl().name().str()==">"){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					if(equal(f.arg(0),left)/*fleftName==leftName*/){
						newf=right>f.arg(1);
					}
				}
				else if(f.is_app()&&f.decl().name().str()==">="){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
					if(equal(f.arg(0),left)/*fleftName==leftName*/){
						newf=right>=f.arg(1);
					}
				}
				else if(f.is_app()&&f.decl().name().str()=="="){
//					std::string fleftName=Z3_ast_to_string(c,f.arg(0));
//					std::string frightName=Z3_ast_to_string(c,f.arg(1));
					if(equal(f.arg(0),left)/*fleftName==leftName*/){
						newf=f.arg(1)<=right;
					}
					else if(equal(f.arg(1),left)/*frightName==leftName*/){
						newf=f.arg(0)<=right;
					}
				}
				//if(!equal(newf,f)){
					if(!isIn(newf,oldformulasMap)&&!isIn(newf,queueMap)&&!isIn(newf,newFormulasMap)){
						newFormulas->push_back(newf);
						queue->push_back(newf);
						
						
						exprMapAdd(newf,newFormulasMap);
						exprMapAdd(newf,queueMap);
					}
				//}
				if(f.is_quantifier()){
					vector<expr> * newForAllFormulas=closureLeForAllFormula(Le,f);
					for(expr newForAllF: *newForAllFormulas){
						if(!isIn(newForAllF,oldformulasMap)&&!isIn(newForAllF,queueMap)&&!isIn(newForAllF,newFormulasMap)){
							newFormulas->push_back(newForAllF);
							//newForAllF will not add to queue to compute closure
							
							exprMapAdd(newf,newFormulasMap);
						}
					}
				}
			}
			return z3Coding.eliminateIdenticalEquation(newFormulas);
		}

		vector<expr> * closureGt(expr Gt,vector<expr> * formulas,map<unsigned,expr> *formulasMap){
			if(!(Gt.is_app()&&Gt.decl().name().str()==">")) {
				std::cerr<<"Z3Coding:closureGt: something is wrong!"<<std::endl;
				return nullptr;
			}
			expr left=Gt.arg(0);
			expr right=Gt.arg(1);
			expr newLt=right<left;
			return closureLt(newLt,formulas,formulasMap);
		}
		vector<expr> * closureGe(expr Ge,vector<expr> * formulas,map<unsigned,expr> *formulasMap){
			if(!(Ge.is_app()&&Ge.decl().name().str()==">=")) {
				std::cerr<<"Z3Coding:closureGe: something is wrong!"<<std::endl;
				return nullptr;
			}
			expr left=Ge.arg(0);
			expr right=Ge.arg(1);
			expr newLe=right<=left;
			return closureLe(newLe,formulas,formulasMap);
		}
		vector<expr> * primedFiltering(vector<expr> * formulas){
			vector<expr> * primeds=new vector<expr>();
			for(expr f: *formulas){
				if(!z3Coding.hasUnPrimedVariable(f)){
					primeds->push_back(f);
				}
				
			}
			return primeds;
		}
		/**
		 * @brief erase phi(0) and phi(exp) in which exp is not index
		 * @param formulas
		 * @return 
		 */
		vector<expr> * phiFiltering(const clang::Stmt* clangStmt,vector<expr> * formulas){
			vector<expr> * ret=new vector<expr>();
			for(expr f: *formulas){
				if(z3Coding.isPhiFormula(f)){
					if(isValidPhi(clangStmt,f)){
						ret->push_back(f);
					}
				}
				else{
					ret->push_back(f);
				}
				
			}
			return ret;
		}
		/**
		 * @brief phiFormula must be phi
		 * @param phiFormula
		 * @return 
		 */
		bool isValidPhi(const clang::Stmt* clangStmt,expr phiFormula){
			if(ava->mapToStmtOut.count(clangStmt)<=0){
				return false;
			}
			expr index=phiFormula.arg(0);
			FlowSet* out=ava->mapToStmtOut.at(clangStmt);
			ValueListSet* vlsOut=(ValueListSet*)out;
			for(Property* p: vlsOut->elements){
				AtomVariabla * av=(AtomVariabla *)p;
				if(equal(index,av->scalaVarz3coding)&&av->hasStep()){
					return true;
				}
			}
			return false;
		}
		
		vector<expr> * unprimedFiltering(vector<expr> * formulas){
			vector<expr> * unprimeds=new vector<expr>();
			for(expr f: *formulas){
				if(!z3Coding.hasPrimedVariable(f)){
					unprimeds->push_back(f);
				}
			}
			return unprimeds;
		}
		vector<expr> * unprimedDecline(vector<expr> * primedformulas){
			vector<expr> * unprimedDeclineformulas=new vector<expr>();
			for(expr pf:*primedformulas){
				unprimedDeclineformulas->push_back(unprimedDecline(pf));
			}
			return unprimedDeclineformulas;
		}
		expr unprimedDecline(expr primedformula){
			vector<expr> * cons=z3Coding.getConsts(primedformula);
			expr unprimedformula=primedformula;
			for(expr con:*cons){
				if(z3Coding.isPrimedVariable(con)){
					expr unprimedcon=z3Coding.unprime(con);
					unprimedformula=z3Coding.substitute(unprimedformula,con,unprimedcon);
				}
			}
			return unprimedformula;
		}
		vector<expr> * primedLift(vector<expr> * unprimedformulas){
			vector<expr> * primedLiftformulas=new vector<expr>();
			for(expr upf:*unprimedformulas){
				primedLiftformulas->push_back(primedLift(upf));
			}
			return primedLiftformulas;
		}
		expr primedLift(expr unprimedformula){
			vector<expr> * cons=z3Coding.getConsts(unprimedformula);
			expr primedformula=unprimedformula;
			for(expr con:*cons){
				if(!z3Coding.isPrimedVariable(con)){
					expr primedcon=z3Coding.prime(con);
					primedformula=z3Coding.substitute(primedformula,con,primedcon);
				}
			}
			return primedformula;
		}
		/**
		 * @brief return all formula which container e
		 * @param formulas
		 * @param e
		 * @return 
		 */
		vector<expr> * filteringWithQuantifier(vector<expr> * formulas, expr e){
			vector<expr> * filteringResult=new vector<expr>();
			for(expr f: *formulas){
				vector<expr> * consWithquantifier=z3Coding.getConstsWithQuantifier(f);
				if(isIn(e,consWithquantifier)){
					filteringResult->push_back(f);
				}
			}
			return filteringResult;
		}
		vector<expr> * filtering(vector<expr> * formulas, expr e){
			vector<expr> * filteringResult=new vector<expr>();
			for(expr f: *formulas){
				vector<expr> * cons=z3Coding.getConsts(f);
				if(isIn(e,cons)){
					filteringResult->push_back(f);
				}
			}
			return filteringResult;
		}
		expr meet(vector<expr> *Pre,expr e1,expr e2){

			if(z3Coding.isPhiFormula(e1)&&z3Coding.isPhiFormula(e2)){
				if(z3Coding.equal(e1,e2)){
					return e1;
				}
				return z3Coding._error;
			}
			else if(z3Coding.isPhiFormula(e1)&&z3Coding.isForAllFormula(e2)){
				return meetPhiFormula_ForAllFormula(Pre,e1,e2);
			}
			else if(z3Coding.isPhiFormula(e1)&&z3Coding.isSimpleFormula(e2)){
				return z3Coding._error;
			}
			else if(z3Coding.isSimpleFormula(e1)&&z3Coding.isPhiFormula(e2)){
				return z3Coding._error;
			}
			else if(z3Coding.isSimpleFormula(e1)&&z3Coding.isForAllFormula(e2)){
				return z3Coding._error;
			}
			else if(z3Coding.isSimpleFormula(e1)&&z3Coding.isSimpleFormula(e2)){
				return meetSimpleFormula_SimpleFormula(e1,e2);
			}
			else if(z3Coding.isForAllFormula(e1)&&z3Coding.isPhiFormula(e2)){
				return meetPhiFormula_ForAllFormula(Pre,e2,e1);
			}
			else if(z3Coding.isForAllFormula(e1)&&z3Coding.isForAllFormula(e2)){
				return meetForAllFormula_ForAllFormula(Pre,e1,e2);
			}
			else if(z3Coding.isForAllFormula(e1)&&z3Coding.isSimpleFormula(e2)){
				return z3Coding._error;
			}
			return z3Coding._error;
		}
		
		/**
		 * @brief layer-by-layer meet 
		 * @param forAllFormula1
		 * @param forAllFormula2
		 * @return 
		 */
		expr meetForAllFormula_ForAllFormula(vector<expr> *Pre,expr forAllFormula1,expr forAllFormula2){

			expr forallBody1=z3Coding.getQuantifierFormulaBody(forAllFormula1);
			expr forallBody2=z3Coding.getQuantifierFormulaBody(forAllFormula2);
			expr bodyMeetResult=meet(Pre,forallBody1,forallBody2);
			//12.30 body can not be or
			if(bodyMeetResult.is_app()&&bodyMeetResult.decl().name().str()=="or"){
				return z3Coding._error;
			}

			if(z3Coding.checkError(bodyMeetResult)){
				return z3Coding._error;
			}


			expr quantifier1=z3Coding.getQuantifier(forAllFormula1);
			expr step1=z3Coding.getQuantifierStep(forAllFormula1);
			expr step1Formula=z3Coding.getQuantifierStepFormula(forAllFormula1);
			expr quantifierBegin1=z3Coding.getQuantifierBegin(forAllFormula1);
			expr quantifierEnd1=z3Coding.getQuantifierEnd(forAllFormula1);
			expr quantifierBeginFormula1=z3Coding.getQuantifierBeginFormula(forAllFormula1);
			expr quantifierEndFormula1=z3Coding.getQuantifierEndFormula(forAllFormula1);
			expr quantifierExtendFormula1=z3Coding.getQuantifierExtendFormula(forAllFormula1);

			expr quantifier2=z3Coding.getQuantifier(forAllFormula2);
			expr step2=z3Coding.getQuantifierStep(forAllFormula2);
			expr quantifierBegin2=z3Coding.getQuantifierBegin(forAllFormula2);
			expr quantifierEnd2=z3Coding.getQuantifierEnd(forAllFormula2);
			expr quantifierBeginFormula2=z3Coding.getQuantifierBeginFormula(forAllFormula2);
			expr quantifierEndFormula2=z3Coding.getQuantifierEndFormula(forAllFormula2);
			expr quantifierExtendFormula2=z3Coding.getQuantifierExtendFormula(forAllFormula2);

			if(quantifierBegin1.is_var()||quantifierBegin2.is_var()
					||quantifierEnd1.is_var()||quantifierEnd2.is_var()){
				return z3Coding._error;
			}

			if(!z3Coding.equal(step1,step2)){
				return z3Coding._error;
			}
			if(!z3Coding.checkError(quantifierExtendFormula1)||!z3Coding.checkError(quantifierExtendFormula2)){
				expr quantifierExtendFormula2To1=z3Coding.substitute(quantifierExtendFormula2,quantifier2,quantifier1);
				if(!z3Coding.equal(quantifierExtendFormula2To1,quantifierExtendFormula1)){
					return z3Coding._error;
				}
			}
			expr meetQuantifierBeginFormula(c);
			expr meetQuantifierEndFormula(c);
			if(z3Coding.equal(step1,c.int_val(1))||z3Coding.equal(step1,c.int_val(-1))){
				/*
				 * newbegin=max(begin1,begin2)
				 * newend=max(end1,end2)
				 * 
				 */


				if(quantifierBeginFormula1.decl().name().str()=="<"&&quantifierBeginFormula2.decl().name().str()=="<"){
					expr assert1=quantifierBegin1<=quantifierBegin2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierBegin2<=quantifierBegin1;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					if(r1==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin2<quantifier1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
					}
					else{
						meetQuantifierBeginFormula=z3Coding._error;
					}
				}
				else if(quantifierBeginFormula1.decl().name().str()=="<"&&quantifierBeginFormula2.decl().name().str()=="<="){
					expr assert1=quantifierBegin1<quantifierBegin2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierBegin1<=quantifierBegin2;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					expr assert3=quantifierBegin2<=quantifierBegin1;
					proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
					if(r1==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin2<=quantifier1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin2<quantifier1;
					}
					else if(r3==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
					}
					else{
						meetQuantifierBeginFormula=z3Coding._error;
					}
				}
				else if(quantifierBeginFormula1.decl().name().str()=="<="&&quantifierBeginFormula2.decl().name().str()=="<"){
					expr assert1=quantifierBegin1<=quantifierBegin2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierBegin2<quantifierBegin1;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					expr assert3=quantifierBegin2<=quantifierBegin1;
					proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
					if(r1==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin2<quantifier1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin1<=quantifier1;
					}
					else if(r3==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
					}
					else{
						meetQuantifierBeginFormula=z3Coding._error;
					}
				} 
				else if(quantifierBeginFormula1.decl().name().str()=="<="&&quantifierBeginFormula2.decl().name().str()=="<="){
					expr assert1=quantifierBegin1<=quantifierBegin2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierBegin2<=quantifierBegin1;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					if(r1==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin2<=quantifier1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierBeginFormula=quantifierBegin1<=quantifier1;
					}
					else{
						meetQuantifierBeginFormula=z3Coding._error;
					}
				}


				if(quantifierEndFormula1.decl().name().str()=="<"&&quantifierEndFormula2.decl().name().str()=="<"){
					expr assert1=quantifierEnd1<=quantifierEnd2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierEnd2<=quantifierEnd1;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					if(r1==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<quantifierEnd1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<quantifierEnd2;
					}
					else{
						meetQuantifierEndFormula=z3Coding._error;
					}
				}
				else if(quantifierEndFormula1.decl().name().str()=="<"&&quantifierEndFormula2.decl().name().str()=="<="){
					expr assert1=quantifierEnd1<=quantifierEnd2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierEnd2<quantifierEnd1;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					expr assert3=quantifierEnd2<quantifierEnd1;
					proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
					if(r1==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<quantifierEnd1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<=quantifierEnd2;
					}
					else if(r3==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<quantifierEnd2;
					}
					else{
						meetQuantifierEndFormula=z3Coding._error;
					}
				}
				else if(quantifierEndFormula1.decl().name().str()=="<="&&quantifierEndFormula2.decl().name().str()=="<"){
					expr assert1=quantifierEnd1<quantifierEnd2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierEnd1<=quantifierEnd2;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					expr assert3=quantifierEnd2<=quantifierEnd1;
					proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
					if(r1==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<=quantifierEnd1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<quantifierEnd1;
					}
					else if(r3==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<quantifierEnd2;
					}
					else{
						meetQuantifierEndFormula=z3Coding._error;
					}
				} 
				else if(quantifierEndFormula1.decl().name().str()=="<="&&quantifierEndFormula2.decl().name().str()=="<="){
					expr assert1=quantifierEnd1<=quantifierEnd2;
					proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
					expr assert2=quantifierEnd2<=quantifierEnd1;
					proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
					if(r1==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<=quantifierEnd1;
					}
					else if(r2==proved_result::proved){
						meetQuantifierEndFormula=quantifier1<=quantifierEnd2;
					}
					else{
						meetQuantifierEndFormula=z3Coding._error;
					}
				}


				if(!z3Coding.checkError(bodyMeetResult)&&!z3Coding.checkError(meetQuantifierBeginFormula)
						&&!z3Coding.checkError(meetQuantifierEndFormula)){
					if(!z3Coding.checkError(quantifierExtendFormula1)&&!z3Coding.checkError(quantifierExtendFormula2)){
						return z3Coding.constructForAllFormula(quantifier1,quantifierExtendFormula1,meetQuantifierBeginFormula,
						meetQuantifierEndFormula,step1Formula,bodyMeetResult);
					}
					else{

						return z3Coding.constructForAllFormula(quantifier1,meetQuantifierBeginFormula,meetQuantifierEndFormula,
						step1Formula,bodyMeetResult);
					}
				}
				else{
					return z3Coding._error;
				}
			}
			else{
				expr assert=step1>0;
				if(z3Coding.prove(assert)==proved_result::proved){
					if(!z3Coding.equal(quantifierBegin1,quantifierBegin2)){
						return z3Coding._error;
					}
					
					if(quantifierBeginFormula1.decl().name().str()=="<"||quantifierBeginFormula2.decl().name().str()=="<"){
						meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
					}
					else{
					
						meetQuantifierBeginFormula=quantifierBegin1<=quantifier1;
					}
					
					if(quantifierEndFormula1.decl().name().str()=="<"&&quantifierEndFormula2.decl().name().str()=="<"){
						expr assert1=quantifierEnd1<=quantifierEnd2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierEnd2<=quantifierEnd1;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						if(r1==proved_result::proved){
							
							meetQuantifierEndFormula=quantifier1<quantifierEnd1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<quantifierEnd2;
						}
						else{
							meetQuantifierEndFormula=z3Coding._error;
						}
					}
					else if(quantifierEndFormula1.decl().name().str()=="<"&&quantifierEndFormula2.decl().name().str()=="<="){
						expr assert1=quantifierEnd1<=quantifierEnd2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierEnd2<quantifierEnd1;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						expr assert3=quantifierEnd2<quantifierEnd1;
						proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
						if(r1==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<quantifierEnd1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<=quantifierEnd2;
						}
						else if(r3==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<quantifierEnd2;
						}
						else{
							meetQuantifierEndFormula=z3Coding._error;
						}
					}
					else if(quantifierEndFormula1.decl().name().str()=="<="&&quantifierEndFormula2.decl().name().str()=="<"){
						expr assert1=quantifierEnd1<quantifierEnd2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierEnd1<=quantifierEnd2;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						expr assert3=quantifierEnd2<=quantifierEnd1;
						proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
						if(r1==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<=quantifierEnd1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<quantifierEnd1;
						}
						else if(r3==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<quantifierEnd2;
						}
						else{
							meetQuantifierEndFormula=z3Coding._error;
						}
					} 
					else if(quantifierEndFormula1.decl().name().str()=="<="&&quantifierEndFormula2.decl().name().str()=="<="){
						expr assert1=quantifierEnd1<=quantifierEnd2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierEnd2<=quantifierEnd1;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						if(r1==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<=quantifierEnd1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierEndFormula=quantifier1<=quantifierEnd2;
						}
						else{
							meetQuantifierEndFormula=z3Coding._error;
						}
					}

				}
				assert=step1<0;
				if(z3Coding.prove(assert)==proved_result::proved){
					if(!z3Coding.equal(quantifierEnd1,quantifierEnd2)){
						return z3Coding._error;
					}
					
					if(quantifierEndFormula1.decl().name().str()=="<"||quantifierEndFormula2.decl().name().str()=="<"){
						meetQuantifierEndFormula=quantifier1<quantifierEnd1;
					}
					else{
						meetQuantifierEndFormula=quantifier1<=quantifierEnd1;
					}
					
					if(quantifierBeginFormula1.decl().name().str()=="<"&&quantifierBeginFormula2.decl().name().str()=="<"){
						expr assert1=quantifierBegin1<=quantifierBegin2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierBegin2<=quantifierBegin1;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						if(r1==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin2<quantifier1;
							
						}
						else if(r2==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
						}
						else{
							meetQuantifierBeginFormula=z3Coding._error;
						}
					}
					else if(quantifierBeginFormula1.decl().name().str()=="<"&&quantifierBeginFormula2.decl().name().str()=="<="){
						expr assert1=quantifierBegin1<quantifierBegin2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierBegin1<=quantifierBegin2;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						expr assert3=quantifierBegin2<=quantifierBegin1;
						proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
						if(r1==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin2<=quantifier1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin2<quantifier1;
						}
						else if(r3==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
						}
						else{
							meetQuantifierBeginFormula=z3Coding._error;
						}
					}
					else if(quantifierBeginFormula1.decl().name().str()=="<="&&quantifierBeginFormula2.decl().name().str()=="<"){
						expr assert1=quantifierBegin1<=quantifierBegin2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierBegin2<quantifierBegin1;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						expr assert3=quantifierBegin2<=quantifierBegin1;
						proved_result r3=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert3);
						if(r1==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin2<quantifier1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin1<=quantifier1;
						}
						else if(r3==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin1<quantifier1;
						}
						else{
							meetQuantifierBeginFormula=z3Coding._error;
						}
					} 
					else if(quantifierBeginFormula1.decl().name().str()=="<="&&quantifierBeginFormula2.decl().name().str()=="<="){
						expr assert1=quantifierBegin1<=quantifierBegin2;
						proved_result r1=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert1);
						expr assert2=quantifierBegin2<=quantifierBegin1;
						proved_result r2=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert2);
						if(r1==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin2<=quantifier1;
						}
						else if(r2==proved_result::proved){
							meetQuantifierBeginFormula=quantifierBegin1<=quantifier1;
						}
						else{
							meetQuantifierBeginFormula=z3Coding._error;
						}
					}
				}
				if(!z3Coding.checkError(bodyMeetResult)&&!z3Coding.checkError(meetQuantifierBeginFormula)
						&&!z3Coding.checkError(meetQuantifierEndFormula)){
					if(!z3Coding.checkError(quantifierExtendFormula1)&&!z3Coding.checkError(quantifierExtendFormula2)){
						return z3Coding.constructForAllFormula(quantifier1,quantifierExtendFormula1,meetQuantifierBeginFormula,
						meetQuantifierEndFormula,step1Formula,bodyMeetResult);
					}
					else{
						return z3Coding.constructForAllFormula(quantifier1,meetQuantifierBeginFormula,meetQuantifierEndFormula,
						step1Formula,bodyMeetResult);
					}
				}
				else{
					return z3Coding._error;
				}
			}
		}

		bool isLtZero(vector<expr>* Pre,expr e){
			if(!e.is_int()){
				std::cerr<<"isLtZero: "<< e <<" must be int type!"<<std::endl;	
				return false;
			}
			else{
				expr assert=e<0;
				proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
				if(r==proved_result::proved){
					return true;
				}
				return false;
			}
		}
		expr meetPhiFormula_ForAllFormula(vector<expr> *Pre,expr phiFormula,expr forAllFormula){
			expr index=z3Coding.getPhiIndex(phiFormula);
			
			expr indexStep=z3Coding.getPhiIndexStep(phiFormula);
			
			index=unprimedDecline(index);
			expr step=z3Coding.getQuantifierStep(forAllFormula);
			expr stepFormula=z3Coding.getQuantifierStepFormula(forAllFormula);			
			
			bool stepLtZeroFlag=false;
			if(isLtZero(Pre,indexStep)){
				stepLtZeroFlag=true;
			}
			//std::cout<<indexStep<<":"<<step<<std::endl;
			if(!z3Coding.equal(step,indexStep)){
				return z3Coding._error;
			}

			
			expr indexInit=z3Coding.getPhiIndexInit(phiFormula);
			

			expr quantifier=z3Coding.getQuantifier(forAllFormula);
			expr quantifierBegin=z3Coding.getQuantifierBegin(forAllFormula);
			expr quantifierEnd=z3Coding.getQuantifierEnd(forAllFormula);

			expr quantifierBeginFormula=z3Coding.getQuantifierBeginFormula(forAllFormula);
			expr quantifierEndFormula=z3Coding.getQuantifierEndFormula(forAllFormula);

			
			if(!stepLtZeroFlag){
				expr meetResultQuantifierBeginFormula(c);
				bool isBeginProved=false;
				if(quantifierBeginFormula.decl().name().str()=="<"){

					if(!isBeginProved){
						//[indexInit,...  (quantifierbegin,... 

						expr assert=indexInit<=quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(quantifierbegin,...
							meetResultQuantifierBeginFormula=quantifierBeginFormula;
						}
					}
					if(!isBeginProved){
						expr assert=indexInit>quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//[indexInit,...
							meetResultQuantifierBeginFormula= indexInit<=quantifier;
						}
					}
					if(!isBeginProved){
						expr assert=indexInit>=quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(indexInit,...
							meetResultQuantifierBeginFormula= indexInit<quantifier;
						}
					}
				}
				else if(quantifierBeginFormula.decl().name().str()=="<="){
					//[indexInit,...  [quantifierbegin,... 
					if(!isBeginProved){
						//[indexInit,...  [quantifierbegin,... 
						expr assert=indexInit<=quantifierBegin;
						//std::cout<<assert<<std::endl;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(quantifierbegin,...
							meetResultQuantifierBeginFormula=quantifierBeginFormula;
						}
					}
					if(!isBeginProved){
						expr assert=indexInit>=quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(indexInit,...
							meetResultQuantifierBeginFormula= indexInit<=quantifier;
						}
					}

				}
				
				expr meetResultQuantifierEndFormula(c);
				bool isEndProved=false;
				if(quantifierEndFormula.decl().name().str()=="<"){
					//...,index)  ..., quantifierEnd)
					if(!isEndProved){
						//...,index)  ..., quantifierEnd) 
						expr assert=index>=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							// ..., quantifierEnd) 
							meetResultQuantifierEndFormula=quantifierEndFormula;
						}
					}
					if(!isEndProved){
						expr assert=index<=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							//...,index)
							meetResultQuantifierEndFormula= quantifier<index;
						}
					}
				}
				else if(quantifierEndFormula.decl().name().str()=="<="){
					//...,index)  ..., quantifierEnd]
					if(!isEndProved){
						//...,index)  ..., quantifierEnd] 
						expr assert=index>quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							// ..., quantifierEnd] 
							meetResultQuantifierEndFormula=quantifierEndFormula;
						}
					}
					if(!isEndProved){
						//...,index)  ..., quantifierEnd] 
						expr assert=index>=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							// ..., quantifierEnd] 
							meetResultQuantifierEndFormula=quantifier<quantifierEnd;
						}
					}
					if(!isEndProved){
						expr assert=index<=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							//...,index)
							meetResultQuantifierEndFormula= quantifier<index;
						}
					}
				}
				if(isBeginProved&&isEndProved){
				// construct forall formula
					expr forallBody=z3Coding.getQuantifierFormulaBody(forAllFormula);
					expr extendFormula=z3Coding.getQuantifierExtendFormula(forAllFormula);
					if(!z3Coding.checkError(extendFormula)&&!z3Coding.checkError(meetResultQuantifierBeginFormula)
						&&!z3Coding.checkError(meetResultQuantifierEndFormula)){
						return z3Coding.constructForAllFormula(quantifier,extendFormula,meetResultQuantifierBeginFormula,meetResultQuantifierEndFormula,
						stepFormula,forallBody);
					}
					else{
						return z3Coding.constructForAllFormula(quantifier,meetResultQuantifierBeginFormula,meetResultQuantifierEndFormula,stepFormula,forallBody);
					}
				}
				else{
					return z3Coding._error;
				}
				return z3Coding._error;
			}
			//stepLtZeroFlag=true, step <0
			else{
				expr meetResultQuantifierBeginFormula(c);
				bool isBeginProved=false;
				if(quantifierBeginFormula.decl().name().str()=="<"){

					if(!isBeginProved){
						//[indexInit,...  (quantifierbegin,... 

						expr assert=index<=quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(quantifierbegin,...
							meetResultQuantifierBeginFormula=quantifierBeginFormula;
						}
					}
					if(!isBeginProved){
						expr assert=index>quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//[indexInit,...
							meetResultQuantifierBeginFormula= index<=quantifier;
						}
					}
					if(!isBeginProved){
						expr assert=index>=quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(indexInit,...
							meetResultQuantifierBeginFormula= index<quantifier;
						}
					}
				}
				else if(quantifierBeginFormula.decl().name().str()=="<="){
					//[indexInit,...  [quantifierbegin,... 
					if(!isBeginProved){
						//[indexInit,...  [quantifierbegin,... 
						expr assert=index<=quantifierBegin;
						//std::cout<<assert<<std::endl;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(quantifierbegin,...
							meetResultQuantifierBeginFormula=quantifierBeginFormula;
						}
					}
					if(!isBeginProved){
						expr assert=index>=quantifierBegin;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isBeginProved=true;
							//(indexInit,...
							meetResultQuantifierBeginFormula= index<=quantifier;
						}
					}

				}
				
				expr meetResultQuantifierEndFormula(c);
				bool isEndProved=false;
				if(quantifierEndFormula.decl().name().str()=="<"){
					//...,index)  ..., quantifierEnd)
					if(!isEndProved){
						//...,index)  ..., quantifierEnd) 
						expr assert=indexInit>=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							// ..., quantifierEnd) 
							meetResultQuantifierEndFormula=quantifierEndFormula;
						}
					}
					if(!isEndProved){
						expr assert=indexInit<=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							//...,index)
							meetResultQuantifierEndFormula= quantifier<indexInit;
						}
					}
				}
				else if(quantifierEndFormula.decl().name().str()=="<="){
					//...,index)  ..., quantifierEnd]
					if(!isEndProved){
						//...,index)  ..., quantifierEnd] 
						expr assert=indexInit>quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							// ..., quantifierEnd] 
							meetResultQuantifierEndFormula=quantifierEndFormula;
						}
					}
					if(!isEndProved){
						//...,index)  ..., quantifierEnd] 
						expr assert=indexInit>=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							// ..., quantifierEnd] 
							meetResultQuantifierEndFormula=quantifier<=quantifierEnd;
						}
					}
					if(!isEndProved){
						expr assert=indexInit<=quantifierEnd;
						proved_result r=z3Coding.prove(z3Coding.filteringLeftNonForAllFormula(Pre),assert);
						if(r==proved_result::proved){
							isEndProved=true;
							//...,index)
							meetResultQuantifierEndFormula= quantifier<=indexInit;
						}
					}
				}
				if(isBeginProved&&isEndProved){
				// construct forall formula
					expr forallBody=z3Coding.getQuantifierFormulaBody(forAllFormula);
					expr extendFormula=z3Coding.getQuantifierExtendFormula(forAllFormula);
					if(!z3Coding.checkError(extendFormula)&&!z3Coding.checkError(meetResultQuantifierBeginFormula)
						&&!z3Coding.checkError(meetResultQuantifierEndFormula)){
						return z3Coding.constructForAllFormula(quantifier,extendFormula,meetResultQuantifierBeginFormula,meetResultQuantifierEndFormula,
						stepFormula,forallBody);
					}
					else{
						return z3Coding.constructForAllFormula(quantifier,meetResultQuantifierBeginFormula,meetResultQuantifierEndFormula,stepFormula,forallBody);
					}
				}
				else{
					return z3Coding._error;
				}
				return z3Coding._error;
			}
		}
		expr meetSimpleFormula_SimpleFormula(expr simpleFormula1,expr simpleFormula2){
			expr result=z3Coding.meet(simpleFormula1,simpleFormula2);
			//std::cout<<result<<std::endl;
			//12.30 modify
			if(!z3Coding.isOrFormula(simpleFormula1)&&!z3Coding.isOrFormula(simpleFormula2)){
				if(result.is_app()&&result.decl().name().str()=="or"){
					return z3Coding._error;
				}
				return z3Coding.simplify(result);
			}
			else{
				if(z3Coding.morePower_equal(result,simpleFormula1)||z3Coding.morePower_equal(result,simpleFormula2)){
					return z3Coding.simplify(result);
				}
				else{
					return z3Coding._error;
				}
			}
		}
		
		
};
#endif

