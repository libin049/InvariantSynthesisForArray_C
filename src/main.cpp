//#define _CHECK_ARRAY_SIZE_VALID
//#define _PERFORMANCE_DEBUG
//#define _DEBUG
#define _NON_PATHGUIDE_VERSION
#define _NON_QUICKSORT
#define _FEASIBLEPATH
//#define _PROPERTYCOLLECT


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
#include "AtomVariableAnalysisOnExpr.h"
#include "Preprocess.h"
#include "AtomVariableInitToUpdateAnalysisOnExpr.h"
#include "AtomVariableDiffAnalysisOnExpr.h"
#include "MemoryUtilOnExpr.h"
#include "ArrayInvAnalysis_FeasiblePathOnExpr.h"
#include "NormalizationAnalysis.h"
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;


bool occurError;
std::string getAsString(DeclarationName &DeclName)
{
	std::string Result;
	llvm::raw_string_ostream OS(Result);
	OS << DeclName;
	return OS.str();
}
static llvm::cl::OptionCategory ToolingSampleCategory("Tooling Sample");



// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.

int blockCount=0;
int forallFormulaCount=0;
int simpleFormulaCount=0;

double meetTime=0;
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
	public:
		MyASTVisitor(Rewriter &R) : TheRewriter(R) {}
		CFG::BuildOptions cfgBuildOptions;
		
		
		void initCFGBuildOptions(){
			//init CFGBuildOptions;
		}
		void printlnZ3Code(Z3Coding &z3coding,clang::CFG* cfg){
			for(CFG::iterator iter=cfg->begin();iter!=cfg->end();++iter){
				CFGBlock* block=*iter;
				Stmt* T=block->getTerminatorCondition();
				for(CFGBlock::iterator iterblock=block->begin();iterblock!=block->end();++iterblock){
					CFGElement element=(*iterblock);
					if(element.getKind()==CFGElement::Kind::Statement){
						const Stmt* it=((CFGStmt*)&element)->getStmt();
						if(T!=nullptr){
							if(it==T) break;
						}
						std::cout<<"stmt is: "<< z3coding.toString(it)<<std::endl;
						vector<expr> * tmp=z3coding.clangStmtToZ3Expr(it);
						if(tmp!=nullptr){
							std::cout<<"z3 code is: "<<z3coding.toString(tmp)<<std::endl;
						}
						else{
							std::cout<<"z3 code is empty "<<std::endl;
						}
					}
				}
				if(T!=nullptr){
					std::cout<<"stmt is: "<< z3coding.toString(T)<<std::endl;
					vector<expr> * tmp=z3coding.clangStmtToZ3Expr(T);
					if(tmp!=nullptr){
						std::cout<<"z3 code is: "<<z3coding.toString(tmp)<<std::endl;
					}
					else{
						std::cout<<"z3 code is empty "<<std::endl;
					}	
				}
			}
		}
		bool VisitFunctionDecl(FunctionDecl *f) {
			LangOptions LO;
			LO.CPlusPlus=1; 

			context c;
			

			// Only function definitions (with bodies), not declarations.
			DeclarationName DeclName = f->getNameInfo().getName();
			std::string FuncName = getAsString(DeclName);
			if(f->hasBody()){

				struct timeval start, end;
				gettimeofday( &start, NULL );

				//std::cout<<"*******************process function::  "<<FuncName <<"***************"<<"\n";
				//if(FuncName=="setup_format_params"){
				//	std::cout<<"*******************process function::  "<<FuncName <<"***************"<<"\n";
				//}
				//occurError=false;
				std::unique_ptr<clang::CFG> myCFG=CFG::buildCFG(f, f->getBody(), &f->getASTContext(), cfgBuildOptions);
				myCFG->dump(LO,true);
				clang::CFG* cfg=myCFG.get();
				//printlnZ3Code(z3coding,cfg);
				/*Check check(cfg);
				  if(occurError==true){
				  return false;
				  }*/
				Preprocess *preprocess=new Preprocess(cfg);
				Z3Coding z3coding(c,preprocess);
				CFGZ3Code* cfgz3code=new CFGZ3Code(cfg,z3coding,c,preprocess);
				if(preprocess->isNeedToGhost){
//					std::cout<<"--------------------printcfgZ3Codes result--------------------"<<std::endl;
//					cfgz3code->printcfgZ3Codes();
//					std::cout<<"--------------------printcfgGhostZ3Codes result--------------------"<<std::endl;
//					cfgz3code->printcfgGhostZ3Codes();
					
					
					
					
					AtomVariableAnalysisOnExpr* ava=new AtomVariableAnalysisOnExpr(cfg,c,z3coding,cfgz3code);
//					std::cout<<"--------------------Atom result--------------------"<<std::endl;
//					ava->print();
					AtomVariableInitToUpdateAnalysisOnExpr* avi=new AtomVariableInitToUpdateAnalysisOnExpr(cfg,z3coding,ava,cfgz3code);
					//std::cout<<"--------------------avinit result--------------------"<<std::endl;
					//avi->print();
//					std::cout<<"--------------------stmt avinit analysis result--------------------"<<std::endl;
//					avi->printStmtAnalysis();
					
					AtomVariableDiffAnalysisOnExpr* avdiff=new AtomVariableDiffAnalysisOnExpr(cfg,z3coding,ava,avi,cfgz3code);
//					std::cout<<"--------------------AtomDiff result--------------------"<<std::endl;
//					avdiff->print();
					//std::cout<<"--------------------stmt AtomDiff analysis result--------------------"<<std::endl;
					//avdiff->printStmtAnalysis();
					
					NormalizationAnalysis* nor=new NormalizationAnalysis(cfg,z3coding,avdiff,cfgz3code);
//					std::cout<<"--------------------Normalization result--------------------"<<std::endl;
//					nor->print();
					
					
					
					
//					MemoryUtilOnExpr mu(z3coding,c,ava,avdiff);
//
//					ArrayInvAnalysis_FeasiblePathOnExpr aia_fp(cfg,mu,z3coding,c,cfgz3code,nor);
//					if(occurError==false){
//						std::cout<<"*******************process function end::  "<<FuncName <<"***************"<<"\n";	
//						std::cout<<"--------------------result--------------------"<<std::endl;
//						aia_fp.print();
//						
//					}
				}
				else{
					AtomVariablaAnalysis* ava=new AtomVariablaAnalysis(cfg,c,z3coding);
					//std::cout<<"--------------------Atom result--------------------"<<std::endl;
					//ava->print();
//					std::cout<<"--------------------stmt analysis result--------------------"<<std::endl;
//					ava->printStmtAnalysis();
//					std::cout<<"------------------------------------------------------------------"<<std::endl;
					AtomVariablaInitToUpdateAnalysis* avi=new AtomVariablaInitToUpdateAnalysis(cfg,z3coding,ava);
					//std::cout<<"--------------------avinit result--------------------"<<std::endl;
					//avi->print();
					//std::cout<<"--------------------stmt avinit analysis result--------------------"<<std::endl;
					//avi->printStmtAnalysis();
					//				std::cout<<"------------------------------------------------------------------"<<std::endl;

					AtomVariablaDiffAnalysis* avdiff=new AtomVariablaDiffAnalysis(cfg,z3coding,ava,avi);
					//				std::cout<<"--------------------AtomDiff result--------------------"<<std::endl;
					//				avdiff->print();
					//std::cout<<"--------------------stmt AtomDiff analysis result--------------------"<<std::endl;
					//avdiff->printStmtAnalysis();
					//				std::cout<<"------------------------------------------------------------------"<<std::endl;
					MemoryUtil mu(z3coding,c,ava,avdiff);

					ArrayInvAnalysis_FeasiblePath aia_fp(cfg,mu,z3coding,c);
					if(occurError==false){
						std::cout<<"*******************process function end::  "<<FuncName <<"***************"<<"\n";	
						std::cout<<"--------------------result--------------------"<<std::endl;
						aia_fp.print();
						blockCount+=aia_fp.blockCount;
						forallFormulaCount+=aia_fp.forAllFormulaCount;
						simpleFormulaCount+=aia_fp.simpleFormulaCount;
						//printf("%f s\n", aia_fp.meetTimeuse /1000000);
						meetTime+=aia_fp.meetTimeuse;
					}

				}
				gettimeofday( &end, NULL );
				//double timeuse = 1000000 * ( end.tv_sec - start.tv_sec ) + end.tv_usec -start.tv_usec;
				//printf("%f s\n", timeuse/1000000);

				

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


	time_t start,stop;
	start = time(NULL);
	CommonOptionsParser op(argc, argv, ToolingSampleCategory);
	ClangTool Tool(op.getCompilations(), op.getSourcePathList());

	// ClangTool::run accepts a FrontendActionFactory, which is then used to
	// create new objects implementing the FrontendAction interface. Here we use
	// the helper newFrontendActionFactory to create a default factory that will
	// return a new MyFrontendAction object every time.
	// To further customize this, we could create our own factory class.
	Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
	stop = time(NULL);
	printf("%.0f  ", difftime(stop,start)) ;
	printf("%f ", meetTime/1000000);
	printf("%d  ", blockCount) ;
	printf("%d  ", forallFormulaCount) ;
	printf("%d  \n", simpleFormulaCount) ;

}

