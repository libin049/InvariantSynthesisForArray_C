
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
#include "Check.h"
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

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
	public:
		MyASTVisitor(Rewriter &R) : TheRewriter(R) {}
		CFG::BuildOptions cfgBuildOptions;
		
		void initCFGBuildOptions(){
			//init CFGBuildOptions;
		}
		
		bool VisitFunctionDecl(FunctionDecl *f) {
			LangOptions LO;
			LO.CPlusPlus=1; 
			
			context c;
			Z3Coding z3coding(c);
			
			// Only function definitions (with bodies), not declarations.
			DeclarationName DeclName = f->getNameInfo().getName();
			std::string FuncName = getAsString(DeclName);
			if(f->hasBody()){
				
				struct timeval start, end;
				gettimeofday( &start, NULL );
    
				std::cout<<"*******************process function::  "<<FuncName <<"***************"<<"\n";	
				occurError=false;
				std::unique_ptr<clang::CFG> myCFG=CFG::buildCFG(f, f->getBody(), &f->getASTContext(), cfgBuildOptions);
				myCFG->dump(LO,true);
				clang::CFG* cfg=myCFG.get();
				
				Check check(cfg);
				if(occurError==true){
					return false;
				}
				AtomVariablaAnalysis* ava=new AtomVariablaAnalysis(cfg,c,z3coding);
				MemoryUtil mu(z3coding,c,ava);
				//std::cout<<"--------------------Atom result--------------------"<<std::endl;
				//ava->print();
				//std::cout<<"--------------------stmt analysis result--------------------"<<std::endl;
				//ava->printStmtAnalysis();
				//std::cout<<"------------------------------------------------------------------"<<std::endl;
				ArrayInvAnalysis_FeasiblePath aia_fp(cfg,mu,z3coding,c);
				if(occurError==false){
					std::cout<<"*******************process function end::  "<<FuncName <<"***************"<<"\n";	
					std::cout<<"--------------------result--------------------"<<std::endl;
					aia_fp.print();
				}
				gettimeofday( &end, NULL );
				double timeuse = 1000000 * ( end.tv_sec - start.tv_sec ) + end.tv_usec -start.tv_usec;
				printf("time: %f s\n", timeuse/1000000);
			
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
	printf("time: %.0f s\n", difftime(stop,start)) ;

}

