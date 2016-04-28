
#define _TEST_VERSION
bool occurError;
#include <sstream>
#include <string>
#include <iostream>
#include "time.h"
#include <sys/time.h>
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
#include "Property.h"
#include "ValueListSet.h"
#include "DataFlowAnalysis.h"
#include "ArrayInvAnalysis_FeasiblePath.h"
#include "clang/AST/DeclarationName.h"
#include "AtomVariableAnalysis.h"
#include "AtomVariableInitToUpdateAnalysis.h"
#include "Check.h"
#include "AtomVariableDiffAnalysis.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;

void meetTest1(z3::context& c,
	Z3Coding& z3coding,
	MemoryUtil& mu){
	/*(forall ((_i0 Int))
  (let ((a!1 (and (<= 1 _i0) (< _i0 100000) (= (mod (- _i0 1) 4) 0)))
        (a!2 (= (select a (div (+ (- 1) _i0) 4)) (select b _i0))))
    (=> a!1 a!2)))-------------meet---------(forall ((_i0 Int))
  (let ((a!1 (and (<= 1 _i0) (< _i0 100000) (= (mod (- _i0 1) 4) 0)))
        (a!2 (= (select a (div (+ (- 1) _i0) 4)) (select b _i0))))
    (=> a!1 a!2)))
	*/
	expr _i0=c.int_const("_i0");
	z3::sort arraytype=c.array_sort(c.int_sort(),c.int_sort());
	expr a=c.constant("a",arraytype);
	expr b=c.constant("b",arraytype);
	expr IndexF=1<=_i0&&_i0<100000&&to_expr(c,Z3_mk_mod(c,_i0-1,c.int_val(4)))==0;
	expr body=select(a,(_i0-1)/4)==select(b,_i0);
	expr F=forall(_i0,implies(IndexF,body));
	cout<<mu.meet(new vector<expr>(),F,F)<<std::endl;
}

int main(int argc, const char **argv) {
	z3::context c;
	Z3Coding z3coding(c);
	MemoryUtil mu(z3coding,c,nullptr,nullptr);
	meetTest1(c,z3coding,mu);
	
	
	z3coding.isForAllFormula()	}






