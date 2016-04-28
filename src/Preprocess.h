#ifndef _Preprocess_H
#define _Preprocess_H
#include <vector>
#include "clang/AST/Expr.h"
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


class Preprocess{
	clang::CFG* cfg;
	
	void process(){
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
					clangStmtToZ3Expr(it);

				}
				if(T!=nullptr){
					clangStmtToZ3Expr(T);
				}

			}
		}
	}
	void clangBinaryOperatorToZ3Expr(clang::BinaryOperator * binaryOperator){
		clangExprToZ3Expr(binaryOperator->getLHS());
		clangExprToZ3Expr(binaryOperator->getRHS());
		switch(binaryOperator->getOpcode()){
			default:	
				return;
			case BO_Assign 	:
				if(isPointerType(binaryOperator->getLHS()->getType())){
					//isAssignedToPointer=true;
				}
				break;
		}
		return;
	}


	bool isPointerType(QualType qt){
		QualType canonicalType=qt.getTypePtr()->getCanonicalTypeInternal();
		const Type * ty=canonicalType.getTypePtr();
		if(ty->isPointerType()) return true;
		return false;
	}
	void  clangUnaryOperatorToZ3Expr(clang::UnaryOperator * unaryOperator){
		clangExprToZ3Expr(unaryOperator->getSubExpr());
		switch(unaryOperator->getOpcode()){
			default:	
				return;
			case UO_PostInc 	://i++
				if(isPointerType(unaryOperator->getSubExpr()->getType())){
					hasPointerIncOrDec=true;
				}
				break;
			case UO_PostDec 	://i--;
				if(isPointerType(unaryOperator->getSubExpr()->getType())){
					hasPointerIncOrDec=true;
				}
				break;
			case UO_PreInc 	://++i
				if(isPointerType(unaryOperator->getSubExpr()->getType())){
					hasPointerIncOrDec=true;
				}
				break;
			case UO_PreDec 	://--i;
				if(isPointerType(unaryOperator->getSubExpr()->getType())){
					hasPointerIncOrDec=true;
				}
				break;
		}
	}
	void clangExprToZ3Expr(const clang::Expr * clangexpr){
		switch (clangexpr->getStmtClass()) {
			default:
				return ;
			case clang::Stmt::BinaryOperatorClass:
				clangBinaryOperatorToZ3Expr((clang::BinaryOperator*)clangexpr);
				break;
			case clang::Stmt::ArraySubscriptExprClass:
				clangArraySubscriptExprToZ3Expr((clang::ArraySubscriptExpr*)clangexpr);
				break;
			case clang::Stmt::UnaryOperatorClass:
				clangUnaryOperatorToZ3Expr((clang::UnaryOperator*)clangexpr);
				break;
			case clang::Stmt::ImplicitCastExprClass:
				{
					const CastExpr * castExpr=(const CastExpr *)clangexpr;
					clangExprToZ3Expr(castExpr->getSubExpr());
					break;
				}
			case clang::Stmt::ParenExprClass:
				{
					const ParenExpr * parenExpr=(const ParenExpr *)clangexpr;
					clangExprToZ3Expr(parenExpr->getSubExpr());
					break;
				}
		}
		return ;
	}
	void clangDeclStmtToZ3Expr(const clang::DeclStmt * clangDeclStmt){
		if(!clangDeclStmt->isSingleDecl()){
			return;
		}
		const Decl* decl=clangDeclStmt->getSingleDecl(); 
		if(!decl->classofKind(Decl::Kind::Var)){
			return;
		}
		const  VarDecl * varDecl=(const  VarDecl *)decl;
		const  ValueDecl * valueDecl=(const  ValueDecl *)decl;
		QualType declQT = valueDecl->getType();
		if(varDecl->hasInit()){
			if(isPointerType(declQT)){
				hasAssignedToPointer=true;

			}
			clangExprToZ3Expr(varDecl->getInit()); 
		}
		return;
	}
	void clangArraySubscriptExprToZ3Expr(clang::ArraySubscriptExpr * arraySubscriptExpr){

		const clang::Expr * base=arraySubscriptExpr->getBase();
		const clang::Expr * idx=arraySubscriptExpr->getIdx();			
		clangExprToZ3Expr(base);
		clangExprToZ3Expr(idx);


	}

	void clangStmtToZ3Expr(const clang::Stmt* stmt){
		switch (stmt->getStmtClass()) {
			case clang::Stmt::DeclStmtClass:
				clangDeclStmtToZ3Expr((const clang::DeclStmt*)stmt);
				break;
			case clang::Stmt::BinaryOperatorClass:
				clangBinaryOperatorToZ3Expr((clang::BinaryOperator*)stmt);
				break;
			case clang::Stmt::UnaryOperatorClass:
				clangUnaryOperatorToZ3Expr((clang::UnaryOperator*)stmt);
				break;
			case clang::Stmt::ImplicitCastExprClass:
				{
					const CastExpr * castExpr=(const CastExpr *)stmt;
					clangExprToZ3Expr(castExpr->getSubExpr());
					break;
				}
			case clang::Stmt::ReturnStmtClass:
				{
					const ReturnStmt * returnStmt=(const ReturnStmt *)stmt;
					const Expr* retValue=returnStmt->getRetValue();
					if(retValue!=nullptr){
						clangExprToZ3Expr(retValue);
					}
					break;
				}
			default:{
					return;
				}
		}
		return;
	}

	public:
	bool hasPointerIncOrDec;
	bool hasAssignedToPointer=false;
	bool isNeedToGhost;
	Preprocess(clang::CFG* cfg){
		this->cfg=cfg;
		hasAssignedToPointer=false;
		hasPointerIncOrDec=false;
		isNeedToGhost=false;
		process();
		if(hasPointerIncOrDec){
			isNeedToGhost=true;
		}
	}
	~Preprocess(){}

};

#endif
