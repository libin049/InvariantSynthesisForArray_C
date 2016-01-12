//------------------------------------------------------------------------------
// Tooling sample. Demonstrates:
//
// * How to write a simple source tool using libTooling.
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <sstream>
#include <string>
#include <iostream>
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
#include "NewConditionFlowSet.h"
#include "ConditionDataFlowAnalysis.h"
#include "ConditionDataFlowAnalysis2.h"
#include "ConditionDataFlowAnalysis3.h"
#include "Z3Coding.h"
#include "MemoryUtil.h"
#include "clang/AST/DeclarationName.h"
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;
void print(vector<z3::expr>* exprs){
			if(exprs==nullptr) return;
			std::cout<<"z3 coding is: ";
			for(auto it=exprs->begin();it!=exprs->end();it++){
				z3::expr e=(z3::expr) *it;
				std::cout<<" "<<e<<"\n ";
			}
			std::cout<<std::endl;
}
z3::expr meet(z3::context &c,z3::expr &e1,z3::expr &e2){
		
		z3::tactic qe(c, "ctx-solver-simplify");
		z3::goal g(c);
		g.add(e1||e2);
		//expr res(c);
		z3::apply_result result_of_elimination = qe.apply(g);
		z3::goal result_goal = result_of_elimination[0];
		return result_goal.as_expr();
}
z3::expr simplify1(z3::context &c,z3::expr &e){
    z3::goal g(c);
    g.add(e);
    z3::tactic t1(c, "simplify");
    z3::tactic t2(c, "solve-eqs");
    z3::tactic t = t1 & t2;
    z3::apply_result r = t(g);
	 return r[0].as_expr();
    
}
z3::expr simplify2(z3::context &c,z3::expr &e){
   z3::tactic qe(c, "ctx-solver-simplify");
	z3::goal g(c);
	g.add(e);
	//expr res(c);
	z3::apply_result result_of_elimination = qe.apply(g);
	z3::goal result_goal = result_of_elimination[0];
	return result_goal.as_expr();
}

static llvm::cl::OptionCategory ToolingSampleCategory("Tooling Sample");


// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
	public:
		MyASTVisitor(Rewriter &R) : TheRewriter(R) {}
		CFG::BuildOptions cfgBuildOptions;
		bool VisitStmt(Stmt *s) {
			// Only care about If statements.
			//if (isa<IfStmt>(s)) {
			//IfStmt *IfStatement = cast<IfStmt>(s);
			//	Stmt *Then = IfStatement->getThen();
				//Stmt *Else = IfStatement->getElse();	
			//}
			return true;
		}
		void initCFGBuildOptions(){
			//init CFGBuildOptions;
		}
		std::string QualTypeToString(QualType qt){
			LangOptions LO;
			LO.CPlusPlus=1; 
			std::string buffer5;
			llvm::raw_string_ostream strout5(buffer5);
			qt.print(strout5,PrintingPolicy(LO));
			return strout5.str();
		}
		std::string ToString(const Type* ty){
			return QualTypeToString(ty-> getCanonicalTypeInternal());
		}
		std::string ToString(const Stmt* stmt){
			std::string buffer1;
		
			LangOptions LO;
			LO.CPlusPlus=1; 
			llvm::raw_string_ostream strout1(buffer1);
			
			stmt->printPretty(strout1, nullptr, PrintingPolicy(LO));
			return strout1.str();
		}
		z3::sort clangTypeToZ3Sort(z3::context &c,QualType qt){
			if(qt.getTypePtr()->isIntegerType()){
				return c.int_sort();
			}
			else if(qt.getTypePtr()->isBooleanType()){
				return c.bool_sort();
			}
			else if(qt.getTypePtr()->isArrayType()){
				const ArrayType * arraytype=(const ArrayType *)qt.getTypePtr();
				z3::sort elementSort=clangTypeToZ3Sort(c,arraytype->getElementType());
				return c.array_sort(c.int_sort(),elementSort);
			}
			else {
				LangOptions LO;
				LO.CPlusPlus=1; 
				std::string buffer;
				llvm::raw_string_ostream strout(buffer);
				qt.print(strout,PrintingPolicy(LO));
				std::string clangTypeName=strout.str();
				std::cerr<<"We do not process type : "<<clangTypeName<<std::endl;
				return c.int_sort();
			}
		}
		
		bool VisitFunctionDecl(FunctionDecl *f) {
			LangOptions LO;
			LO.CPlusPlus=1; 
			
			context c;
			Z3Coding z3coding(c);
			
			
			// Only function definitions (with bodies), not declarations.
			//DeclarationName DeclName = f->getNameInfo().getName();
			
			//std::string FuncName = DeclName.getAsString();
			//std::cout<<"begin function  "<<FuncName <<"\n";			
			if(f->hasBody()){
				std::unique_ptr<clang::CFG> myCFG=CFG::buildCFG(f, f->getBody(), &f->getASTContext(), cfgBuildOptions);
				myCFG->dump(LO,true);
				std::cout<<"------------my visit begin---------------------"<<std::endl;
				for(CFG::iterator iter=myCFG->begin();iter!=myCFG->end();++iter)
				{
					CFGBlock* block=*iter;
					std::cout<<"block id:"<<block->getBlockID()<<std::endl;
					for(CFGBlock::iterator iterblock=block->begin();iterblock!=block->end();++iterblock)
					{
						CFGElement element=(*iterblock);
						if(element.getKind()==CFGElement::Kind::Statement){
							const Stmt* it=((CFGStmt*)&element)->getStmt();
						//	std::cout<<it->getStmtClassName()<<std::endl; 
						std::cout<<"---------------------------------------"<<std::endl;
							std::cout<<"stmt is: "<<ToString(it);
							vector<z3::expr> *exprs;
							switch (it->getStmtClass()) {
								case clang::Stmt::DeclStmtClass:
									//std::cout<<"DeclStmtClass"<<std::endl;
									exprs=z3coding.clangDeclStmtToZ3Expr((const clang::DeclStmt*)it);
									print(exprs);
									z3coding.maintainMemoryUnits();
									std::cout<<"MemoryUnits is: "<<z3coding.toStringMemoryUnits()<<std::endl;
									break;
								case clang::Stmt::BinaryOperatorClass:
									//std::cout<<"BinaryOperatorClass"<<std::endl;
									std::cout<<std::endl;
									exprs=z3coding.clangBinaryOperatorToZ3Expr((clang::BinaryOperator*)it);
									z3coding.maintainMemoryUnits();
									std::cout<<"MemoryUnits is: "<<z3coding.toStringMemoryUnits()<<std::endl;
									print(exprs);
									break;
								case clang::Stmt::UnaryOperatorClass:
									//std::cout<<"UnaryOperatorClass"<<std::endl;
									std::cout<<std::endl;
									exprs=z3coding.clangUnaryOperatorToZ3Expr((clang::UnaryOperator*)it);
									z3coding.maintainMemoryUnits();
									std::cout<<"MemoryUnits is: "<<z3coding.toStringMemoryUnits()<<std::endl;
									print(exprs);
									break;
								default:
									//std::cout<<std::endl;
									std::cerr<<"tooling_sample: We do not consider processing "<<it->getStmtClassName()<<std::endl;
								/*case clang::Stmt::DeclStmtClass:
									const clang::DeclStmt* declStmt=(const clang::DeclStmt*)it;
									const  Decl* decl=declStmt->getSingleDecl();
									std::cout<<"decl->getDeclKindName(): "<<decl->getDeclKindName()<<std::endl;
									if(decl->classofKind(Decl::Kind::Var)){
										const  VarDecl * varDecl=(const  VarDecl *)decl;
										std::string buffer;
										llvm::raw_string_ostream strout(buffer);
										varDecl->printName(strout);
										std::string varName=strout.str();
										std::cout<<"varName: "<<varName;
										QualType declQT = varDecl->getType();
										std::string buffer2;
										llvm::raw_string_ostream strout2(buffer2);
										declQT.print(strout2,PrintingPolicy(LO));
										std::string typeName=strout2.str();
										std::cout<<", typeName: "<<typeName;
										if(varDecl->hasInit()){
											std::cout<<" init :"<<ToString(varDecl->getInit())<<std::endl;
										}
										else{
											std::cout<<std::endl;
										}
									}
									break;*/
								/*case clang::Stmt::ArraySubscriptExprClass:
									
									const clang::ArraySubscriptExpr* arrayacess=(const clang::ArraySubscriptExpr*)it;
									const Expr* base=arrayacess->getBase();
									std::string buffer1;
									llvm::raw_string_ostream strout1(buffer1);
									base->printPretty(strout1, nullptr, PrintingPolicy(LO));
									std::cout<<"base: "<<strout1.str()<<std::endl;
									std::string buffer2;
									llvm::raw_string_ostream strout2(buffer2);
									const Expr* idx=arrayacess->getIdx();
									idx->printPretty(strout2, nullptr, PrintingPolicy(LO));
									std::cout<<"idx: "<<strout2.str()<<std::endl;
									
									
									
									break;*/
									
								/*case clang::Stmt::DeclRefExprClass	:
									const clang::DeclRefExpr * var=
									(const clang::DeclRefExpr *)it;
									std::string buffer4;
									llvm::raw_string_ostream strout4(buffer4);
									var->printPretty(strout4, nullptr, PrintingPolicy(LO));
									std::cout<<strout4.str()<<std::endl;
									//var->printPretty()
									DeclarationNameInfo dec=var->getNameInfo();
									std::string buffer3;
									llvm::raw_string_ostream strout3(buffer3);
									dec.printName(strout3);
									std::cout<<strout3.str()<<std::endl;
									
								
									
									
									const ValueDecl*  valueDecl=var->getDecl();
									if (valueDecl){
										
										
										std::string buffer7;
										llvm::raw_string_ostream strout7(buffer7);
										valueDecl->printName(strout7);
										std::cout<<"Name: "<<strout7.str()<<std::endl;
										QualType declQT = valueDecl->getType();
										
										// now call QualType.getAsString(PrintingPolicy &Policy)
										std::string buffer5;
										llvm::raw_string_ostream strout5(buffer5);
										declQT.print(strout5,PrintingPolicy(LO));
										std::cout<<"type: "<<strout5.str();
										
										
										std::cout<<" is array ? "<<declQT.getTypePtr()->isArrayType()<<std::endl;
										std::cout<<"type: "<<strout5.str();
										std::cout<<" is int ? "<<declQT.getTypePtr()->isIntegerType()<<std::endl;
										z3::context c;
										std::cout<<"z3 sort: "<<clangTypeToZ3Sort(c,declQT)<<std::endl;				
										if(declQT.getTypePtr()->isArrayType()){
											const ArrayType * arraytype=(const ArrayType *)declQT.getTypePtr();
											std::cout<<"ElementType: "<<QualTypeToString(arraytype->getElementType())<<std::endl;
											std::cout<<"BaseElementType: "<<ToString(arraytype->getBaseElementTypeUnsafe())<<std::endl;
										}
										if(declQT.getBaseTypeIdentifier()){
											std::cout<<declQT.getBaseTypeIdentifier()->getName().data()<<std::endl;
										}
										if(declQT.getQualifiers()){
											std::string buffer6;
											llvm::raw_string_ostream strout6(buffer6);
											declQT.getQualifiers().print(strout6,PrintingPolicy(LO));
											std::cout<<strout6.str()<<std::endl;
										}
										
										
									}
									break;*/
								
								
							}
						}
					}
				}
				std::cout<<"------------my visit end -----------------------"<<std::endl;
				/*FlowSet* set= new ValueListSet();
				FlowSet* set2=new ValueListSet();
				FlowSet* set3=new ValueListSet();
				for(CFG::iterator iter=myCFG->begin();iter!=myCFG->end();++iter)
				{
					CFGBlock* block=*iter;
					std::cout<<"block id:"<<block->getBlockID()<<std::endl;
					for(CFGBlock::iterator iterblock=block->begin();iterblock!=block->end();++iterblock)
					{
						CFGElement element=(*iterblock);
						if(element.getKind()==CFGElement::Kind::Statement){
							const Stmt* it=((CFGStmt*)&element)->getStmt();
							set->add(new Condition(false,it));
							set2->add(new Condition(false,it));
							set2->add(new Condition(true,it));
							set3=set2->clone();
							std::cout<<"set3 is ";
							set3->print();
							set3->intersection(set);
							
							//it->dump();
							std::string buffer1;
							llvm::raw_string_ostream strout1(buffer1);
							it->printPretty(strout1, nullptr, PrintingPolicy(LO));
							//it->dumpPretty(f->getASTContext());
							std::cout<<"stmt is :"<<strout1.str()<<"\n";
							std::cout<<"set is ";
							set->print();
							std::cout<<"set2 is ";
							set2->print();
							std::cout<<"after intersection, set3 is ";
							set3->print();
						}
					}
					
					 * 
					 * 
					 * 
					 * 
					 * 
					 * 
					 * 
					 * 
					 * 
					 * 
					std::cout<<"set1 == set2 ?"<<set->equal(set2)<<std::endl;*/
					/*
					Stmt* s=block->getTerminatorCondition();
					if(s!=nullptr){
						std::string buffer1;
						llvm::raw_string_ostream strout1(buffer1);
						s->printPretty(strout1, nullptr, PrintingPolicy(LO));
						std::cout<<"Condition is:"<<strout1.str()<<"\n";
						
					}
					
				}
					std::cout<<"------------my visit end -----------------------"<<std::endl;*/
			  
			/*std::cout<<"------------union -----------------------"<<std::endl;
			  ConditionDataFlowAnalysis2 conditionAnalysis2(myCFG.get());
			  conditionAnalysis2.print();
			  
		    std::cout<<"------------intersection right-----------------------"<<std::endl;

			  ConditionDataFlowAnalysis conditionAnalysis(myCFG.get());
			  
			  conditionAnalysis.print();
			std::cout<<"------------intersection error-----------------------"<<std::endl;

			   ConditionDataFlowAnalysis3 conditionAnalysis3(myCFG.get());
			  
			  conditionAnalysis3.print();
			*/  //list<CFGBlock*> worklist; 
			  //conditionAnalysis.initAndSortWorkList(worklist);
			  //conditionAnalysis.printWorkList(&worklist);			  
			  
			}
			
			
			return true;
		}


	private:
		Rewriter &TheRewriter;
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
	public:
		MyASTConsumer(Rewriter &R) : Visitor(R) {}
		// Override the method that gets called for each parsed top-level
		// declaration.
		bool HandleTopLevelDecl(DeclGroupRef DR) override {
			for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
				// Traverse the declaration using our AST visitor.
				Visitor.TraverseDecl(*b);
				//(*b)->dump();
			}
			return true;
		}

	private:
		MyASTVisitor Visitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
	public:
		MyFrontendAction() {}
		void EndSourceFileAction() override {
			/*	SourceManager &SM = TheRewriter.getSourceMgr();
				llvm::errs() << "** EndSourceFileAction for: "
				<< SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";

			// Now emit the rewritten buffer.
			TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
			*/	
		}

		std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
				StringRef file) override {
			/*	llvm::errs() << "** Creating AST consumer for: " << file << "\n";
				TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());*/
			return llvm::make_unique<MyASTConsumer>(TheRewriter);

		}

	private:
		Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
	
	
	/*CommonOptionsParser op(argc, argv, ToolingSampleCategory);
	ClangTool Tool(op.getCompilations(), op.getSourcePathList());

	// ClangTool::run accepts a FrontendActionFactory, which is then used to
	// create new objects implementing the FrontendAction interface. Here we use
	// the helper newFrontendActionFactory to create a default factory that will
	// return a new MyFrontendAction object every time.
	// To further customize this, we could create our own factory class.
	Tool.run(newFrontendActionFactory<MyFrontendAction>().get());*/
	/*try {
		z3::context c;
		z3::expr  a     = c.int_const("x");
		z3::expr  b     = c.int_const("y");
		z3::expr  e1=a+2>b;
		z3::expr  e2=a+1>b;
		z3::expr  e3=e1||e2;
		z3::expr  r=meet(c,e1,e2);
		std::cout <<"("<< e1<< ") meet ("<<e2<<") is: "<< r << "\n";
		z3::expr  r2=simplify1(c,e3);
		std::cout<<"simplify1 ("<<e3<<") is: "<<r2<<  "\n";
		e1=a-2>0;
		e2=a-1>0;
		r=meet(c,e1,e2);
		std::cout <<"("<< e1<< ") meet ("<<e2<<") is: "<< r << "\n";
		r2=simplify1(c,r);
		std::cout<<"simplify1 ("<<r<<") is: "<<r2<<  "\n";
		r2=simplify2(c,r);
		std::cout<<"simplify2 ("<<r<<") is: "<<r2<<  "\n";
		
		e1=a==2;
		e2=a==1;
		r=meet(c,e1,e2);
		std::cout <<"("<< e1<< ") meet ("<<e2<<") is: "<< r << "\n";
		
		z3::expr  i     = c.int_const("i");
		z3::expr  j     = c.int_const("j");
		z3::expr  n     = c.int_const("n");
		z3::expr  k     = c.int_const("k");
		z3::expr  x     = c.int_const("x");
		z3::expr  e		= i==2 && i<=n && j==i-1 && (j<1 || k<=x) ;
		r2=simplify1(c,e);
		std::cout<<"simplify1 ("<<e<<") is: "<<r2<<  "\n";
		r2=simplify2(c,e);
		std::cout<<"simplify2 ("<<e<<") is: "<<r2<<  "\n";
		r=simplify2(c,r2);
		std::cout<<"simplify2 ("<<r2<<") is: "<<r<<  "\n";
		e1=i<j;
		e2=i>j;
		r=meet(c,e1,e2);
		std::cout <<"("<< e1<< ") meet ("<<e2<<") is: "<< r << "\n";
		r2=simplify1(c,r);
		std::cout<<"simplify1 ("<<r<<") is: "<<r2<<  "\n";
		r2=simplify2(c,r);
		std::cout<<"simplify2 ("<<r<<") is: "<<r2<<  "\n";
    }
    catch (z3::exception & ex) {
        std::cout << "unexpected error: " << ex << "\n";
    } 
	*/
	/*try {
		z3::context c;
		z3::sort   intArray     = c.array_sort(c.int_sort(),c.int_sort());
		z3::sort	intintArray	=c.array_sort(c.int_sort(),intArray);
		expr A=c.constant("A",intArray);
		expr A2=c.constant("A2",intintArray);
		expr i=c.int_const("i");
		expr j=c.int_const("j");
		expr A_i=select(A,i);
		expr A_Ai=select(A,A_i);
		expr A2_i_j=select(select(A2,i),j);
		expr A2_Ai_j=select(select(A2,A_i),j);
		expr A2_Ai_A2Aij=select(select(A2,A_i),A2_Ai_j);
		Z3Coding z3coding(c);
		std::cout<<A_i;
		print(z3coding.getArrayAcessIdxes(A_i));
		std::cout<<A_Ai;
		print(z3coding.getArrayAcessIdxes(A_Ai));
		std::cout<<A2_i_j;
		print(z3coding.getArrayAcessIdxes(A2_i_j));
		std::cout<<A2_Ai_j;
		print(z3coding.getArrayAcessIdxes(A2_Ai_j));
		std::cout<<A2_Ai_A2Aij;
		print(z3coding.getArrayAcessIdxes(A2_Ai_A2Aij));
		std::cout<<A2_Ai_A2Aij<<std::endl;
		std::cout<<z3coding.getArrayAcessKthIdx(A2_Ai_A2Aij,1)<<std::endl;
		std::cout<<z3coding.abstractFormerKDimension(A2_Ai_A2Aij,1)<<std::endl;
		print(z3coding.abstractConst(A_i));
		print(z3coding.abstractConst(A_Ai));
		print(z3coding.abstractConst(A2_i_j));
		print(z3coding.abstractConst(A2_Ai_j));
		print(z3coding.abstractConst(A2_Ai_A2Aij));
		
	}
    catch (z3::exception & ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }*/
  /*try {
		z3::context ctx;
		std::vector<expr>* exprs=new std::vector<expr>();
		z3::expr a=ctx.int_const("a");
		z3::expr b=ctx.int_const("b");
		z3::expr c=ctx.int_const("c");
		z3::expr d=ctx.int_const("d");
		z3::expr e=ctx.int_const("e");
		z3::expr gt=(e>a);
		z3::expr lt=(a<e);
		z3::expr f1=(a<d);
		z3::expr f2=(a>=b);
		z3::expr f3=(a>c);
		z3::expr f4=(a==10);
		//z3::expr f5=(d==10);
		exprs->push_back(f1);
		exprs->push_back(f2);
		exprs->push_back(f3);
		exprs->push_back(f4);
		//exprs->push_back(f5);
		Z3Coding z3Coding(ctx);
		MemoryUtil mu(z3Coding,ctx);
		//print(mu.closureGt(gt,exprs));
//		/print(mu.closureLt(lt,exprs));
		exprs->push_back(lt);
		exprs->push_back(gt);
		print(mu.closure(exprs));
		print(z3Coding.simplify(mu.closure(exprs)));
		z3Coding
	}
    catch (z3::exception & ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }*/
//	try {
//		context c;
//		expr a = c.int_const("a");
//		expr b = c.int_const("b");
//		expr x = c.int_const("x");
//		z3::sort intarray=c.array_sort(c.int_sort(),c.int_sort());
//		z3::sort intintarray	=c.array_sort(c.int_sort(),intarray);
//		expr A=c.constant("A",intarray);
//		expr A2=c.constant("A2",intintarray);
//		expr A_x=select(A,x);
//		expr A2_x_A_x=select(select(A2,x),A_x);
//		expr one=c.int_val(1);
//		expr two=c.int_val(2);
//		expr f = implies(b <= x&&x <= a&&to_expr(c,Z3_mk_mod(c,a,one))==0, A_x < A2_x_A_x);
//		expr qf = forall(x, f);
//		std::cout << qf << "\n";
//		
//		Z3Coding z3Coding(c);
//		
//		print(z3Coding.getArrayAcess(qf));
//		
//		
//		
//		
//		/*expr y = c.int_const("y");
//		f = implies(b <= y&&y <= a&&to_expr(c,Z3_mk_mod(c,a,one))==0, A_x < A2_x_A_x);
//		expr qf1 = forall(y, f);
//		expr v2=z3Coding.getQuantifier(qf1);
//		std::cout << " "<<" "<<v1.get_sort() << "\n";
//		std::cout << " "<<" "<<v2.get_sort() << "\n";
//		std::cout <<Z3_get_quantifier_num_bound(c,qf)<< "\n";
//		std::cout <<to_expr(c,Z3_get_quantifier_body(c,qf))<< "\n";
//		z3::symbol sym(c,Z3_get_quantifier_bound_name(c,qf,0));
//		std::cout <<sym.str()<< "\n";
//		z3::sort t(c,Z3_get_quantifier_bound_sort(c,qf,0));
//		std::cout <<t<< "\n";
//		expr e=c.constant(sym,t);
//		std::cout <<e<<"is var? "<<e.is_var()<< "\n";
//	
//		expr A2_x_y=select(select(A2,x),y);
//		expr f1 =implies(0<=y&&y<b&&to_expr(c,Z3_mk_mod(c,b,one))==0,A2_x_y==0);
//		expr qf3 = forall(y, f1);
//		std::cout << qf3 << "\n";
//		expr f2 =implies(1<=x&&x<a&&to_expr(c,Z3_mk_mod(c,a,two))==0,qf3);
//		expr qf4 = forall(x, f2);
//		std::cout << qf4.simplify() << "\n";
//		z3::symbol sym1(c,Z3_get_quantifier_bound_name(c,qf4,0));
//		std::cout <<sym1.str()<< "\n";
//		z3::sort t1(c,Z3_get_quantifier_bound_sort(c,qf4,0));
//		std::cout <<t1<< "\n";
//		expr body=qf4.body();
//		std::cout <<body<< "\n";
//		z3::symbol sym2(c,Z3_get_quantifier_bound_name(c,body,0));
//		std::cout <<sym2.str()<< "\n";
//		z3::sort t2(c,Z3_get_quantifier_bound_sort(c,body,0));
//		std::cout <<t2<< "\n";*/
//		
//		
//	} 
//	catch (z3::exception & ex) {
//        std::cout << "unexpected error: " << ex << "\n";
//    }
	/*try {
		context c;
		expr a = c.int_const("a");
		expr b = c.int_const("b");
		expr x = c.int_const("x");
		expr y = c.int_const("y");
		z3::sort intarray=c.array_sort(c.int_sort(),c.int_sort());
		z3::sort intintarray	=c.array_sort(c.int_sort(),intarray);
		expr A=c.constant("A",intarray);
		expr A2=c.constant("A2",intintarray);
		expr one=c.int_val(1);
		expr two=c.int_val(2);
		Z3Coding z3Coding(c);
		expr A2_x_y=select(select(A2,x),y);
		expr f1 =implies(0<=y&&y<b&&to_expr(c,Z3_mk_mod(c,b,one))==0,A2_x_y==0);
		expr qf3 = forall(y, f1);
		std::cout << qf3 << "\n";
		
		expr f2 =implies(1<=x&&x<a&&to_expr(c,Z3_mk_mod(c,a,two))==0,qf3);
		expr qf4 = forall(x, f2);
		std::cout << qf4 << "\n";
		
		z3::symbol sym1(c,Z3_get_quantifier_bound_name(c,qf4,0));
		std::cout <<sym1.str()<< "\n";
		z3::sort t1(c,Z3_get_quantifier_bound_sort(c,qf4,0));
		std::cout <<t1<< "\n";
		
		expr body=qf4.body();
		std::cout <<body.decl().name().str()<< "\n";
		std::cout <<body.arg(0)<< "\n";
		std::cout <<body.arg(1)<< "\n";
		
		z3::symbol sym2(c,Z3_get_quantifier_bound_name(c,body.arg(1),0));
		std::cout <<sym2.str()<< "\n";
		z3::sort t2(c,Z3_get_quantifier_bound_sort(c,body.arg(1),0));
		std::cout <<t2<< "\n";
		Z3_sort ty = Z3_mk_int_sort(c);
		Z3_symbol   s  = Z3_mk_string_symbol(c, "sss");
		expr sss=to_expr(c,Z3_mk_const(c, s, ty));
		
		std::cout <<sss<<" is var? "<<sss.is_var()<< "\n";
		Z3_ast to[1] = { sss };
		Z3_ast r=Z3_substitute_vars(c,qf4.body(),1,to);
		expr sssppp=to_expr(c,r);
		std::cout <<qf4.body()<< "\n";
		std::cout <<sssppp<< "\n";
		
	} 
	catch (z3::exception & ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }*/
	
//	try {
//		//test getallQuantifier getallBeginFormula getallEndFormula
//		context c;
//		expr a = c.int_const("a");
//		expr b = c.int_const("b");
//		expr z = c.int_const("z");
//		expr x = c.int_const("x");
//		expr y = c.int_const("y");
//		z3::sort intarray=c.array_sort(c.int_sort(),c.int_sort());
//		z3::sort intintarray	=c.array_sort(c.int_sort(),intarray);
//		expr A=c.constant("A",intarray);
//		expr A2=c.constant("A2",intintarray);
//		expr one=c.int_val(1);
//		expr two=c.int_val(2);
//		Z3Coding z3Coding(c);
//		expr A2_x_y=select(select(A2,x),y);
//		expr f1 =implies(0<=y&&y<b&&to_expr(c,Z3_mk_mod(c,b,one))==0,A2_x_y==0);
//		expr qf3 = forall(y, f1);
//		std::cout << qf3 << "\n";
//		expr f2 =implies(1<=x&&x<a&&to_expr(c,Z3_mk_mod(c,a,two))==0,qf3);
//		expr qf4 = forall(x, f2);
//		std::cout << qf4 << "\n";
//		print(z3Coding.getAllQuantifier(qf4));	
//		print(z3Coding.getAllQuantifierBeginFormula(qf4));	
//		print(z3Coding.getAllQuantifierEndFormula(qf4));
//		print(z3Coding.getAllQuantifierStep(qf4));
//		print(z3Coding.getArrayAcess(qf4));
//		std::cout << z3Coding.getQuantifierFormulaBody(qf4)<< "\n";
//	} 
//	catch (z3::exception & ex) {
//        std::cout << "unexpected error: " << ex << "\n";
//    }
	
	try {
		//test mayMemoryUnitIsIn mayMemoryUnitIsInFormula 
		context c;
		expr a = c.int_const("a");
		expr b = c.int_const("b");
		expr i = c.int_const("i");
		expr j = c.int_const("j");
		expr x = c.int_const("x");
		expr y = c.int_const("y");
		z3::sort intarray=c.array_sort(c.int_sort(),c.int_sort());
		z3::sort intintarray	=c.array_sort(c.int_sort(),intarray);
		expr A=c.constant("A",intarray);
		expr A2=c.constant("A2",intintarray);
		expr one=c.int_val(1);
		expr two=c.int_val(2);
		Z3Coding z3Coding(c);
		expr A_x=select(A,x);
		expr A2_x_y=select(select(A2,x),y);
		expr f1 =implies(0<=y&&y<b&&to_expr(c,Z3_mk_mod(c,b,one))==0,A2_x_y==0);
		expr qf3 = forall(y, f1);
		std::cout << qf3 << "\n";
		expr f2 =implies(1<=x&&x<a&&to_expr(c,Z3_mk_mod(c,a,two))==0,qf3);
		expr qf4 = forall(x, f2);
		std::cout << qf4 << "\n";
		vector<expr>* Pre=new vector<expr>();
		Pre->push_back(i<j);
		Pre->push_back(1<=i);
		Pre->push_back(j<b);
		Pre->push_back(i<=j);
		MemoryUtil mu(z3Coding,c);
		expr A_i=select(A,i);
		expr A_j=select(A,j);
		std::cout<<A_i<<" memory may is in "<<A_j<<" ? "<< mu.mayMemoryUnitIsIn(Pre,A_i,A_j)<< "\n";
		
		
		expr f0 =implies(0<=y&&y<b&&to_expr(c,Z3_mk_mod(c,b,one))==0,A_x==0);
		expr qf0 = forall(y, f0);
		std::cout<<A_i<<" ------------memory may is in "<<qf0<<" ? "<< mu.mayMemoryUnitIsInFormula(Pre,A_i,qf0)<< "\n";
		
		expr i1 = c.int_const("i1");
		expr j1 = c.int_const("j1");
		
		Pre=new vector<expr>();
		Pre->push_back(i<a);
		Pre->push_back(0<=i);
		Pre->push_back(j<b);
		Pre->push_back(1<=j);
		
		Pre->push_back(i1<a);
		Pre->push_back(0<=i1);
		Pre->push_back(j1<b);
		Pre->push_back(1<=j1);
		
	
		expr A2_i_j=select(select(A2,i),j);
		expr A2_i1_j1=select(select(A2,i1),j1);
		std::cout<<A2_i1_j1<<" memory may is in "<<A2_i_j<<" ? "<< mu.mayMemoryUnitIsIn(Pre,A2_i1_j1,A2_i_j)<< "\n";
		std::cout<<A2_i1_j1<<" memory may is in "<<qf4<<" ? "<< mu.mayMemoryUnitIsInFormula(Pre,A2_i1_j1,qf4)<< "\n";
	} 
	catch (z3::exception & ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }
	
	
}
