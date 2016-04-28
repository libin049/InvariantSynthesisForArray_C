#ifndef _ArrayInvAnalysis_FeasiblePathOnExpr_H
#define _ArrayInvAnalysis_FeasiblePathOnExpr_H
#include "Formula.h"
#include "MemoryUtilOnExpr.h"
#include "FlowSet.h"
#include "Property.h"
#include "DataFlowAnalysis_FeasiblePath.h"
#include "CFGZ3Code.h"
#include "NormalizationAnalysis.h"
extern  bool occurError;

class ArrayInvAnalysis_FeasiblePathOnExpr: public IntraDataFlowAnalysis_FeasiblePath{
	private:
		MemoryUtilOnExpr &mu;
		Z3Coding &z3coding;
		context &c;
		ValueListSet universalSet;
		CFGZ3Code* cfgZ3Code;
		NormalizationAnalysis* nor;
		FlowSet* simplify(FlowSet* flowSet){
			vector<expr>* exprSet=flowSetToExprSet(flowSet);
			return exprSetToFlowSet(z3coding.morePower_simplify(exprSet));
		}
		void simplifyResult(){
			for (std::map<CFGBlock*, FlowSet*>::iterator it=mapToBlockIn.begin(); it!=mapToBlockIn.end(); ++it){
				it->second=simplify(it->second);
				list<pair<CFGBlock*,FlowSet*>*> * outs=mapToBlockOut.at(it->first);
				for (std::list<pair<CFGBlock*,FlowSet*>*>::iterator outsIt = outs->begin(); 
						outsIt != outs->end(); outsIt++){
					pair<CFGBlock*,FlowSet*> *ele=*outsIt;
					ele->second=simplify(ele->second);
				}
			}
		}
		/**
		 * @brief when reach this path, there are path assertions on the path, if they are unsatisfiable, the path is unfeasible;
		 * 			otherwise , the path is unfeasible
		 * @param pathAssertions
		 * @return 
		 */
		bool isFeasiblePath(vector<expr>* pathAssertions){
			expr conjecture(c);
			conjecture=c.bool_val(true);
			for(auto it=pathAssertions->begin();it!=pathAssertions->end();it++){
				expr e=*it;
				conjecture=e&&conjecture;
			}
			check_result r=z3coding.satisfy(conjecture);
			if(r==check_result::unsat){
				return false;
			}
			else{
				return true;
			}
		}
		
		expr reduce(vector<expr> * Pre,expr f){
			vector<expr>* disjunctionForms=z3coding.DNF(f);
			vector<expr>* satDisjunctionForms=z3coding.reduction(Pre,disjunctionForms);
			if(satDisjunctionForms->size()==0){
				return c.bool_val(false);
			}
			else{
				expr ret=satDisjunctionForms->at(0);
				for(unsigned i=1;i<satDisjunctionForms->size();i++){
					ret=ret||satDisjunctionForms->at(i);
				}
				return ret;
			}
		}
		/**
		 * @brief 
		 * @param Pre
		 * @param formulas
		 * @return 
		 */
		vector<expr>* reduce(vector<expr> * Pre,vector<expr>* conjunctiveForms){
			vector<expr>* ret=new vector<expr>();
			for(expr f:*conjunctiveForms){
				expr reducef=reduce(Pre,f);
				if(eq(reducef,c.bool_val(false))){
					ret=new vector<expr>();
					ret->push_back(c.bool_val(false));
					return ret;
				}
				else{
					ret->push_back(reducef);
				}
			}
			return ret;
		}
		FlowSet* merge(vector<FlowSet*>* ins){
				if(ins->size()==0) return new ValueListSet();
				FlowSet  *pred_out=ins->at(0);
				//FlowSet  *merge_result=pred_out->clone();
				FlowSet  *merge_result=newinitialFlow();
				copy(pred_out,merge_result);
				for(unsigned i=1;i<ins->size();i++){
					pred_out=ins->at(i);
					FlowSet *newFlowSet=newinitialFlow();
					
					merge(merge_result,pred_out,newFlowSet);
					merge_result=newFlowSet;
				}
				return merge_result;
		}
		
	public:
		ArrayInvAnalysis_FeasiblePathOnExpr(clang::CFG* cfg,MemoryUtilOnExpr& memoryUtil,Z3Coding &z3c,context &ctx,CFGZ3Code* cfgZ3Code
		,NormalizationAnalysis* nor):IntraDataFlowAnalysis_FeasiblePath(cfg),mu(memoryUtil),z3coding(z3c),
		c(ctx){
			#ifdef _PROPERTYCOLLECT
			CFGBlock exit=cfg->getExit();
			propertyCollecter.addFocusBlock(&exit);
			#endif
			this->cfgZ3Code=cfgZ3Code;
			this->nor=nor;
			doAnalysis();
			simplifyResult();
		}
		vector<expr> * GenAndKill(vector<expr> * Pre,const clang::Stmt* stmt,
		vector<expr> * z3codes,CFGBlock* n){
			vector<expr> * exprs=z3codes;
			if(exprs==nullptr){
				return new vector<expr>();
			}
			cout<<"z3codes is: "<<z3coding.toString(z3codes)<<std::endl;
			z3coding.maintainMemoryUnits();
			map<std::string,expr> * memoryUnitsMap=z3coding.getMemoryUnits();
			
			vector<expr> *formulas=z3coding.boolSortFiltering(exprs);
			vector<expr> * _Pre=Pre;
			for(expr f: *formulas){
#if  defined _DEBUG || defined _PERFORMANCE_DEBUG
			if(!isInFlowThrouth2){
				std::cout<<"------------------------------------"<<std::endl;
				std::cout<<"stmt is: "<<f<<std::endl;
			}
#endif

#ifdef _DEBUG
			if(!isInFlowThrouth2){
				std::cout<<"Pre is: "<<toString(_Pre)<<std::endl;
			}
#endif
#ifdef _PERFORMANCE_DEBUG
				time_t start,stop;
				start = time(NULL);
#endif

				_Pre=mu.Pos(stmt,_Pre,f,memoryUnitsMap,n);

#ifdef _PERFORMANCE_DEBUG
				stop = time(NULL);
				std::cout<<"Flow Time1:"<<stop-start<<std::endl;
				start =time(NULL);
#endif
				//std::cout<<"befor simplify is: "<<toString(_Pre)<<std::endl;
				_Pre=z3coding.simplify(_Pre);
				//std::cout<<"after simplify is: "<<toString(_Pre)<<std::endl;
#ifdef _PERFORMANCE_DEBUG
				stop = time(NULL);
				std::cout<<"Flow Time2:"<<stop-start<<std::endl;
#endif

#ifdef _DEBUG
			if(!isInFlowThrouth2){
				std::cout<<"Pos is: "<<toString(_Pre)<<std::endl;
			}
#endif
			}
			return _Pre;
		}
		
		vector<vector<expr>*>* getZ3CodeOf(CFGBlock* n){
			return nor->NormalizateZ3Codes->at(n);
		}
		bool isInFlowThrouth2=false;
		
		vector<expr> * GenAndKillTerminator(vector<expr> * Pre,const clang::Stmt* T, bool trueOrFalse,vector<expr> * z3codes){
			
			vector<expr> * exprs=z3codes;
			if(exprs==nullptr){
				return new vector<expr>();
			}
			cout<<"z3codes is: "<<z3coding.toString(z3codes)<<std::endl;
			z3coding.maintainMemoryUnits();
			map<std::string,expr> * memoryUnitsMap=z3coding.getMemoryUnits();
			vector<expr> *formulas=z3coding.boolSortFiltering(exprs);
			//when T is a&&b,formulas's size will be more than 1
			//otherwise,formulas's size is equal to 1
			
			if(formulas->size()<1){
				if(exprs->size()==1) {
					if(exprs->at(0).is_int()){
						formulas->push_back(exprs->at(0)!=0);
					}
				}
				else{
					std::cerr<<"GenAndKillTerminator: something is wrong! "<<std::endl;	
					return new vector<expr>();
				}
			}
			
			if(trueOrFalse==false){
				vector<expr> * conditionFormulas=z3coding.splitLANDFormula(formulas->back());formulas->pop_back();
				expr ori_formula=conditionFormulas->at(0);
				for(unsigned i=1;i<conditionFormulas->size();i++){
					ori_formula=ori_formula&&conditionFormulas->at(i);
				}
				formulas->push_back(!ori_formula);
			}
			//reduce formulas
			
			vector<expr> * reduceFormulas=reduce(filteringLeftNonForAllFormula(Pre),formulas);

			
			if(reduceFormulas->size()==1){
				if(eq(reduceFormulas->at(0),c.bool_val(false))){
					return reduceFormulas;
				}
			}
			formulas=reduceFormulas;

			vector<expr> * _Pre=Pre;
			for(expr f: *formulas){
#if  defined _DEBUG || defined _PERFORMANCE_DEBUG
				if(!isInFlowThrouth2){
					std::cout<<"------------------------------------"<<std::endl;
					std::cout<<"stmt is: "<<f<<std::endl;
				}
#endif
#ifdef _DEBUG
				if(!isInFlowThrouth2){
					std::cout<<"Pre is: "<<toString(_Pre)<<std::endl;
				}
#endif

#ifdef _PERFORMANCE_DEBUG
				time_t start,stop;
				start = time(NULL);
#endif

				_Pre=mu.Pos(T,_Pre,f,memoryUnitsMap,nullptr);

#ifdef _PERFORMANCE_DEBUG
				stop = time(NULL);
				std::cout<<"Flow Time1:"<<stop-start<<std::endl;
				start =time(NULL);
#endif

				_Pre=/*z3coding.canonical(*/z3coding.simplify(_Pre)/*)*/;

#ifdef _PERFORMANCE_DEBUG
				stop = time(NULL);
				std::cout<<"Flow Time2:"<<stop-start<<std::endl;
#endif

#ifdef _DEBUG
				if(!isInFlowThrouth2){
					std::cout<<"Pos is: "<<toString(_Pre)<<std::endl;
				}
#endif
			}
			return _Pre;
		}
		std::string toString(vector<z3::expr>* exprs){
			std::string ret="";
			if(exprs==nullptr) return "";
			for(auto it=exprs->begin();it!=exprs->end();it++){
				z3::expr e=(z3::expr) *it;
				std::string eName=Z3_ast_to_string(c,e);
				ret+=eName+"; ";
			}
			return ret;
		}
		std::string toString(vector<FlowSet*>* ins){
			std::string ret="";
			if(ins!=nullptr){
				for(FlowSet* f:*ins){
					f=simplify(f);
					ret+=f->toString()+"\n";
					ret+="--------------------||----------------------";
				}
			}
			return ret;
		}

		FlowSet * newinitialFlow(){
			return &universalSet; 
		}
		FlowSet * entryInitialFlow(){return new ValueListSet();}

		void merge(FlowSet  * &in1,FlowSet  *&in2,FlowSet  *&out){
#ifdef _PERFORMANCE_DEBUG
			time_t start,stop;
			start = time(NULL);
#endif
			if(in1==&universalSet&&in2==&universalSet) {
#ifdef _DEBUG
			if(!isInFlowThrouth2){
				std::cout<<"universalSet merge universalSet"<<std::endl;
			}
#endif
				out=&universalSet;
				return;
			}
			if(in1==&universalSet){
#ifdef _DEBUG
			if(!isInFlowThrouth2){
				std::cout<<"universalSet merge "<<in2->toString()<<std::endl;
			}
#endif
				out=in2->clone();
				return;
			}
			if(in2==&universalSet) {
#ifdef _DEBUG
			if(!isInFlowThrouth2){
				std::cout<<"universalSet merge "<<in1->toString()<<std::endl;
			}
#endif
				out=in1->clone();
				return;
			}
#ifdef _DEBUG
		if(!isInFlowThrouth2){
			std::cout<<in1->toString() << " ---merge--- "<<in2->toString()<<std::endl;
		}
#endif
			out=meet(in1,in2);

#ifdef _PERFORMANCE_DEBUG
			stop = time(NULL);
			std::cout<<"Merge Time:"<<stop-start<<std::endl;
#endif
			//std::cout<<"---------------------meet end--------------"<<std::endl;
			return;
		}
		void flowThrouth(CFGBlock*&n, FlowSet *&in, list<pair<CFGBlock*,FlowSet*>*> *&outs){
#ifdef _PERFORMANCE_DEBUG
			time_t start,stop;
			start = time(NULL);
#endif
			for(auto it=outs->begin();it != outs->end(); it++){
				pair<CFGBlock*,FlowSet*>* ele=*it;
				if(ele->second==&universalSet){
					ele->second=new ValueListSet();
				}
			}
			vector<expr> * Pre=flowSetToExprSet(in);
						
			//refinement
			Pre=refinementOrformula(Pre);
			if(outs->size()==2){
				Stmt* T=n->getTerminatorCondition();
				if(T==nullptr){
					std::cerr<<"flowThrouth: TerminatorCondition can not be null! "<<std::endl;	
				}
				unsigned count=0;
				vector<vector<expr>*>* blockZ3code=getZ3CodeOf(n);
				for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
					CFGElement element=(*iterblock);
					if(element.getKind()==CFGElement::Kind::Statement){
						const Stmt* it=((CFGStmt*)&element)->getStmt();
						if(it==T) break;
						//std::cout<<"---------------------------------------"<<std::endl;
						//std::cout<<"stmt is: "<<toString(it)<<std::endl;
						//the condition expression will appear within the set of statements in the block (usually the last statement) 
						if(count==n->size()-1){
							break;
						}
						
						vector<expr>* stmtZ3codes=blockZ3code->at(count);
						Pre=GenAndKill(Pre,it,stmtZ3codes,n);
						count++;
					}
				}
				vector<expr>* stmtZ3codes=blockZ3code->at(count);
				vector<expr> * truePos=GenAndKillTerminator(Pre,T,true,stmtZ3codes);

				vector<expr> * falsePos=GenAndKillTerminator(Pre,T,false,stmtZ3codes);

				pair<CFGBlock*,FlowSet*>* tureBranch=outs->front();
				ValueListSet *tureFlow=(ValueListSet*)tureBranch->second;
				pair<CFGBlock*,FlowSet*>* falseBranch=outs->back();
				ValueListSet *falseFlow=(ValueListSet*)falseBranch->second;
				if(isFeasiblePath(filteringLeftNonForAllFormula(truePos) )){
					//12.30 modify 
					if(isPointToBack(n)){
						truePos=backEdgeFilteringOrformula(truePos);
					}
					FlowSet * trueFlowSet=exprSetToFlowSet(truePos);
					tureFlow->Union(trueFlowSet);
				}
				else{
					tureBranch->second=&universalSet;
				}
				if(isFeasiblePath(filteringLeftNonForAllFormula(falsePos))){
					//12.30 modify 
					if(isPointToBack(n)){
						falsePos=backEdgeFilteringOrformula(falsePos);
					}
					FlowSet * falseFlowSet=exprSetToFlowSet(falsePos);
					falseFlow->Union(falseFlowSet);
				}
				else{
					falseBranch->second=&universalSet;
				}
			}
			else if(outs->size()==1){
				Stmt* T=n->getTerminatorCondition();
				if(T!=nullptr){
					std::cerr<<"flowThrouth: TerminatorCondition must be null! "<<std::endl;	
				}
				vector<vector<expr>*>* blockZ3code=getZ3CodeOf(n);
				if(n->size()==0&&blockZ3code->size()!=0){
					Pre=GenAndKill(Pre,nullptr,blockZ3code->at(0),n);
				}
				else{
					int count=0;
				for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
					CFGElement element=(*iterblock);
					if(element.getKind()==CFGElement::Kind::Statement){
						const Stmt* it=((CFGStmt*)&element)->getStmt();
						//std::cout<<"---------------------------------------"<<std::endl;
						//std::cout<<"stmt is: "<<toString(it)<<std::endl;
						vector<expr>* stmtZ3codes=blockZ3code->at(count);
						Pre=GenAndKill(Pre,it,stmtZ3codes,n);
						count++;
					}
				}
				}
				pair<CFGBlock*,FlowSet*>* out=outs->front();
				ValueListSet *outFlow=(ValueListSet*)out->second;
				
				if(isPointToBack(n)){
					Pre=backEdgeFilteringOrformula(Pre);
				}
				
				FlowSet * flowSet=exprSetToFlowSet(Pre);
				outFlow->Union(flowSet);
			}
#ifdef _PERFORMANCE_DEBUG
			stop = time(NULL);
			std::cout<<"Flow Time:"<<stop-start<<std::endl;
#endif
		}
		vector<expr> * filteringLeftNonForAllFormula(vector<expr> * formulas){
			vector<expr> * result=new vector<expr>();
			for(expr e:*formulas){
				if(!z3coding.isForAllFormula(e)){
					result->push_back(e);
				}
			}
			return result;
		}
		void flowThrouth(CFGBlock *&n, list<FlowSet*> *&ins, list<pair<CFGBlock*,FlowSet*>*> *&outs){
			isInFlowThrouth2=true;
#ifdef _PERFORMANCE_DEBUG
			time_t start,stop;
			start = time(NULL);
#endif
			
			for(auto it=outs->begin();it != outs->end(); it++){
				pair<CFGBlock*,FlowSet*>* ele=*it;
				if(ele->second==&universalSet){
					ele->second=new ValueListSet();
				}
			}
			if(outs->size()==2){
				vector<FlowSet*>*trueFeasibleIns=new vector<FlowSet*>();
				vector<FlowSet*>*falseFeasibleIns=new vector<FlowSet*>();
				for(FlowSet* in: *ins){
					vector<expr> * Pre=flowSetToExprSet(in);
					//refinement
					Pre=refinementOrformula(Pre);
				
					Stmt* T=n->getTerminatorCondition();
					if(T==nullptr){
						std::cerr<<"flowThrouth: TerminatorCondition can not be null! "<<std::endl;	
					}
					unsigned count=0;
					vector<vector<expr>*>* blockZ3code=getZ3CodeOf(n);
					for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
						CFGElement element=(*iterblock);
						if(element.getKind()==CFGElement::Kind::Statement){
							const Stmt* it=((CFGStmt*)&element)->getStmt();
							if(it==T) break;
							//std::cout<<"---------------------------------------"<<std::endl;
							//std::cout<<"stmt is: "<<toString(it)<<std::endl;
							//the condition expression will appear within the set of statements in the block (usually the last statement) 
							if(count==n->size()-1){
								break;
							}
							vector<expr>* stmtZ3codes=blockZ3code->at(count);
							Pre=GenAndKill(Pre,it,stmtZ3codes,n);
							count++;
						}
					}
					vector<expr>* stmtZ3codes=blockZ3code->at(count);
					vector<expr> * truePos=GenAndKillTerminator(Pre,T,true,stmtZ3codes);
					vector<expr> * falsePos=GenAndKillTerminator(Pre,T,false,stmtZ3codes);
					if(isFeasiblePath(filteringLeftNonForAllFormula(truePos))){
						trueFeasibleIns->push_back(in);
					}
					if(isFeasiblePath(filteringLeftNonForAllFormula(falsePos))){
						falseFeasibleIns->push_back(in);
					}
				}
				FlowSet* trueIn;
				FlowSet* falseIn;
				if(trueFeasibleIns->size()==ins->size()){
					trueIn=mapToBlockIn.at(n);
				}
				else{
					trueIn=merge(trueFeasibleIns);
				}
				if(falseFeasibleIns->size()==ins->size()){
					falseIn=mapToBlockIn.at(n);
				}
				else{
					falseIn=merge(falseFeasibleIns);
				}
				isInFlowThrouth2=false;
				//process true branch
				//std::cout<<"-----------process true branch---------------"<<std::endl;
				{
					vector<expr> * Pre=flowSetToExprSet(trueIn);
					//refinement
					Pre=refinementOrformula(Pre);
				
					Stmt* T=n->getTerminatorCondition();
					if(T==nullptr){
						std::cerr<<"flowThrouth: TerminatorCondition can not be null! "<<std::endl;	
					}
					unsigned count=0;
					vector<vector<expr>*>* blockZ3code=getZ3CodeOf(n);
					for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
						CFGElement element=(*iterblock);
						if(element.getKind()==CFGElement::Kind::Statement){
							const Stmt* it=((CFGStmt*)&element)->getStmt();
							if(it==T) break;
							//std::cout<<"---------------------------------------"<<std::endl;
							//std::cout<<"stmt is: "<<toString(it)<<std::endl;
							//the condition expression will appear within the set of statements in the block (usually the last statement) 
							if(count==n->size()-1){
								break;
							}
							vector<expr>* stmtZ3codes=blockZ3code->at(count);
							Pre=GenAndKill(Pre,it,stmtZ3codes,n);
							count++;
						}
					}
					vector<expr>* stmtZ3codes=blockZ3code->at(count);
					vector<expr> * truePos=GenAndKillTerminator(Pre,T,true,stmtZ3codes);
					pair<CFGBlock*,FlowSet*>* tureBranch=outs->front();
					ValueListSet *tureFlow=(ValueListSet*)tureBranch->second;
					if(isFeasiblePath(filteringLeftNonForAllFormula(truePos))){
						if(isPointToBack(n)){
							truePos=backEdgeFilteringOrformula(truePos);
						}
						FlowSet * trueFlowSet=exprSetToFlowSet(truePos);
						tureFlow->Union(trueFlowSet);
					}
					else{
						tureBranch->second=&universalSet;
					}
				}
				//process false branch
				//std::cout<<"-----------process false branch---------------"<<std::endl;
				{
					vector<expr> * Pre=flowSetToExprSet(falseIn);
					//refinement
					Pre=refinementOrformula(Pre);
				
					Stmt* T=n->getTerminatorCondition();
					if(T==nullptr){
						std::cerr<<"flowThrouth: TerminatorCondition can not be null! "<<std::endl;	
					}
					unsigned count=0;
					vector<vector<expr>*>* blockZ3code=getZ3CodeOf(n);
					for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
						CFGElement element=(*iterblock);
						if(element.getKind()==CFGElement::Kind::Statement){
							const Stmt* it=((CFGStmt*)&element)->getStmt();
							if(it==T) break;
							//std::cout<<"---------------------------------------"<<std::endl;
							//std::cout<<"stmt is: "<<toString(it)<<std::endl;
							//the condition expression will appear within the set of statements in the block (usually the last statement) 
							if(count==n->size()-1){
								break;
							}
							vector<expr>* stmtZ3codes=blockZ3code->at(count);
							Pre=GenAndKill(Pre,it,stmtZ3codes,n);
							count++;
						}
					}
					vector<expr>* stmtZ3codes=blockZ3code->at(count);
					vector<expr> * falsePos=GenAndKillTerminator(Pre,T,false,stmtZ3codes);
					pair<CFGBlock*,FlowSet*>* falseBranch=outs->back();
					ValueListSet *falseFlow=(ValueListSet*)falseBranch->second;
				
					if(isFeasiblePath(filteringLeftNonForAllFormula(falsePos))){
						if(isPointToBack(n)){
							falsePos=backEdgeFilteringOrformula(falsePos);
						}
						FlowSet * falseFlowSet=exprSetToFlowSet(falsePos);
						falseFlow->Union(falseFlowSet);
					}
					else{
						falseBranch->second=&universalSet;
					}
				}
			}
			
			else {
				std::cerr<<"flowThrouth2: "<<n->getBlockID()<<"must be two flow out edge!"<<std::endl;	
			}	
			
			
#ifdef _PERFORMANCE_DEBUG
			stop = time(NULL);
			std::cout<<"Flow Time:"<<stop-start<<std::endl;
#endif
		
		}
		void copy(FlowSet  *&from,FlowSet  *&to){
			if(from==&universalSet) {

				to=&universalSet;
			}
			else {
				to=from->clone();
			}

		}
		//used in dataflow analysis
	bool equal(FlowSet  *&from,FlowSet  *&to){
		if(from==&universalSet) {
			return to==&universalSet;
		}
		if(to==&universalSet) {
			return from==&universalSet;
		}
		return from->equal(to);
	}
		FlowSet * exprSetToFlowSet(vector<expr> * exprSet){
			FlowSet * flowSet=new ValueListSet();
			for(expr e: *exprSet){
				flowSet->add(new Formula(e));
			}
			return flowSet;
		}
		vector<expr> * flowSetToExprSet(FlowSet * flowSet){
			vector<expr> * exprSet=new vector<expr>();
			ValueListSet *listSet=(ValueListSet *)flowSet;
			for(Property* p: listSet->elements){
				Formula *f=(Formula *)p;
				exprSet->push_back(f->formula);
			}
			return exprSet;
		}
		std::string toString(const Stmt* stmt){
			std::string buffer1;

			LangOptions LO;
			LO.CPlusPlus=1; 
			llvm::raw_string_ostream strout1(buffer1);

			stmt->printPretty(strout1, nullptr, PrintingPolicy(LO));
			return strout1.str();
		}
		void ppp(expr e1,expr e2,unsigned time){
			if(z3coding.isSimpleFormula(e1)&&z3coding.isSimpleFormula(e2)){
				std::cout<<"simple meet simple Time:"<<time<<std::endl;
			}
			//			else if(z3coding.isSimpleFormula(e1)&&e2.is_quantifier()){
			//				std::cout<<"simple meet forall Time:"<<time<<std::endl;
			//			}
			//			else if(z3coding.isSimpleFormula(e2)&&e1.is_quantifier()){
			//				std::cout<<"forall meet simple Time:"<<time<<std::endl;
			//			}
			//			else if(z3coding.isSimpleFormula(e1)&&z3coding.isPhiFormula(e2)){
			//				std::cout<<"simple meet phi Time:"<<time<<std::endl;
			//			}
			//			else if(z3coding.isSimpleFormula(e2)&&z3coding.isPhiFormula(e1)){
			//				std::cout<<"phi meet simple Time:"<<time<<std::endl;
			//			}
			else if(e1.is_quantifier()&&z3coding.isPhiFormula(e2)){
				std::cout<<"forall meet phi Time:"<<time<<std::endl;
			}
			else if(e2.is_quantifier()&&z3coding.isPhiFormula(e1)){
				std::cout<<"phi meet forall Time:"<<time<<std::endl;
			}
			else if(e1.is_quantifier()&&e2.is_quantifier()){
				std::cout<<"forall meet forall Time:"<<time<<std::endl;
			}

		}
		vector<expr>* meet(vector<expr>* in1,vector<expr>* in2){
#ifdef _PERFORMANCE_DEBUG
						std::cout<<in1->size()<<"-------------meet---------"<<in2->size()<<std::endl;

#endif
			vector<expr>* out=new vector<expr>();
			int count=0;
			
			
/*			for(expr expr1: *in1){
				for(expr expr2: *in2){
					count++;
					//					if(in1->size()==74&&in2->size()==113&&count==245){
					//						std::cout<<in1->size()<<"-------------meet---------"<<in2->size()<<std::endl;
					//					}

										std::cout<<expr1<<"-------------meet---------"<<expr2<<std::endl;
#ifdef _PERFORMANCE_DEBUG
					time_t start,stop;
					start = time(NULL);
#endif

					expr r=mu.meet(new vector<expr>(),expr1,expr2);
					std::cout<<"-------------done---------"<<count<<std::endl;
					//std::cout<<"meetResult:--------------------"<<std::endl;
#ifdef _PERFORMANCE_DEBUG
					stop = time(NULL);
					//ppp(expr1,expr2,stop-start);
#endif
					if(!z3coding.checkError(r)){
						if(!z3coding.isIn(r,out)){
							out->push_back(r);
							if(z3coding.isForAllFormula(expr1)&&z3coding.isForAllFormula(expr2)&&!z3coding.equal(r,z3coding.TRUE)&&!z3coding.equal(r,z3coding.FALSE)){
								break;
							}
						}
					}
				}
			}*/
			
			vector<expr>* in1Simples=z3coding.filteringLeftSimpleFormula(in1);
			vector<expr>* in2Simples=z3coding.filteringLeftSimpleFormula(in2);
			for(expr expr1: *in1Simples){
				for(expr expr2: *in2Simples){
					count++;
					//std::cout<<expr1<<"-------------meet---------"<<expr2<<std::endl;
					expr r=mu.meet(new vector<expr>(),expr1,expr2);
					std::cout<<"-------------done---------"<<count<<std::endl;
					if(!z3coding.checkError(r)){
						if(!z3coding.isIn(r,out)){
							out->push_back(r);
						}
					}
				}
			}
			
			vector<expr>* in1NonSimples=z3coding.filteringLeftNonSimpleFormula(in1);
			vector<expr>* in2NonSimples=z3coding.filteringLeftNonSimpleFormula(in2);
			for(expr expr1: *in1NonSimples){
				for(expr expr2: *in2NonSimples){
					count++;
					//std::cout<<expr1<<"-------------meet---------"<<expr2<<std::endl;
					expr r=mu.meet(new vector<expr>(),expr1,expr2);
					std::cout<<"-------------done---------"<<count<<std::endl;
					if(!z3coding.checkError(r)){
						if(!z3coding.isIn(r,out)){
							out->push_back(r);
							if(z3coding.isForAllFormula(expr1)&&z3coding.isForAllFormula(expr2)&&!z3coding.equal(r,z3coding.TRUE)&&!z3coding.equal(r,z3coding.FALSE)){
								break;
							}
						}
					}
				}
			}
			
			return out;
		}
		FlowSet * meet(FlowSet * in1, FlowSet *in2){
			vector<expr>* outexpr=meet(flowSetToExprSet(in1),flowSetToExprSet(in2));
			return exprSetToFlowSet(outexpr);
		}
		/*Formula* meet(vector<expr> *Pre, Formula *f1,Formula *f2){
			expr e1=f1->formula;
			expr e2=f2->formula;

			expr meetResult=mu.meet(Pre,e1,e2);

			if(z3coding.checkError(meetResult)){
				return nullptr;
			}
			return new Formula(meetResult);
		}*/

		
		
		
		/**
		 * @brief 
		 * @param n
		 * @return 
		 */
		bool isPointToBack(CFGBlock* n){
			const Stmt *looptarget =n->getLoopTarget();
			if(looptarget!=nullptr){
				if(n->succ_size()==1){
					return true;
				}
				else{
					std::cerr<<"I think something is wrong!"<<std::endl;	
					return true;
				}
			}
			else{
				return false;
			}
		}
		vector<expr>* backEdgeFilteringOrformula(vector<expr> * formulas){
			return z3coding.filteringOrFormula(formulas);
		}
		/**
		 * @brief according to formulas refinement or formula in formulas, e.g.:Pre a>b,a<b||c>d, orFormula:a<b||c>d=>c>d 
		 * @param Pre
		 * @param formulas
		 * @return 
		 */
		vector<expr>* refinementOrformula(vector<expr>* formulas){
			vector<expr>* ret=new vector<expr>();
			for(expr f: *formulas){
				if(z3coding.isOrFormula(f)){
					if(f.is_quantifier()){
						std::cerr<<"refinementOrformula: or can not occur in forall Formula!"<<std::endl;	
						return ret;
					}
					else{
						ret->push_back(reduce(formulas,f));
					}
				}
				else{
					ret->push_back(f);
				}
			}
			return ret;
		}
		#ifdef _PROPERTYCOLLECT
		PropertyCollectUtil* getPropertyCollecter(){
			return &propertyCollecter;
		}
		#endif
};
#endif
