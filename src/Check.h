#ifndef _CHECK_H
#define _CHECK_H
extern bool occurError;
class Check{
public:
	Check(clang::CFG* cfg){
		for(CFG::iterator it=cfg->begin();it!=cfg->end();++it){
			CFGBlock* n=*it;
			for(CFGBlock::iterator iterblock=n->begin();iterblock!=n->end();++iterblock){
				CFGElement element=(*iterblock);
				if(element.getKind()==CFGElement::Kind::Statement){
					const Stmt* it=((CFGStmt*)&element)->getStmt();
					check(it);
				}
			}
		}
	}
	void check(const clang::Stmt* stmt){
			switch (stmt->getStmtClass()) {
				case clang::Stmt::DeclStmtClass:
					clangDeclStmtCheck((const clang::DeclStmt*)stmt);
					break;
				case clang::Stmt::BinaryOperatorClass:
					clangBinaryOperatorCheck((clang::BinaryOperator*)stmt);
					break;
				case clang::Stmt::UnaryOperatorClass:
					clangUnaryOperatorCheck((clang::UnaryOperator*)stmt);
					break;
				case clang::Stmt::ImplicitCastExprClass:
					{
						const CastExpr * castExpr=(const CastExpr *)stmt;
						clangExprCheck(castExpr->getSubExpr());
						break;
					}
				case clang::Stmt::ReturnStmtClass:
					{
						const ReturnStmt * returnStmt=(const ReturnStmt *)stmt;
						const Expr* retValue=returnStmt->getRetValue();
						if(retValue!=nullptr){
							clangExprCheck(retValue);
						}
						break;
					}
				default:{
					std::cerr<<"Check:check: We do not consider processing "<<stmt->getStmtClassName()<<std::endl;	
					occurError=true;
				}
			}
			return;
	}
	bool  clangDeclStmtCheck(const clang::DeclStmt * clangDeclStmt){
			if(!clangDeclStmt->isSingleDecl()){
				std::cerr<<"Check:clangDeclStmtCheck: We do not consider DeclGroup "<<std::endl;
				occurError=true;
				return false;
			}
			const Decl* decl=clangDeclStmt->getSingleDecl(); 
			
			if(!decl->classofKind(Decl::Kind::Var)){
				std::cerr<<"Check:clangDeclStmtCheck: We do not consider the DeclKind: "<<decl->getDeclKindName()<<std::endl;
				occurError=true;
				return false;
			}
			const  VarDecl * varDecl=(const  VarDecl *)decl;
			if(varDecl->hasInit()){
				clangExprCheck(varDecl->getInit()); 
			}
			return true;
	}
	bool clangBinaryOperatorCheck(clang::BinaryOperator * binaryOperator){
			clangExprCheck(binaryOperator->getLHS());
			clangExprCheck(binaryOperator->getRHS());
			switch(binaryOperator->getOpcode()){
				default:	
					std::cerr<<"Check:clangBinaryOperatorCheck: We do not consider processing binaryOperator: "<<binaryOperator->getOpcodeStr().data()<<std::endl;
					occurError=true;
					return false;
				case BO_Mul 	://*
					
					break;
				case BO_Div 	:
					
					break;
				case BO_Rem	:
					
					break;
				case BO_Add 	:
					
					break;
				case BO_Sub 	:
					
					break;
				case BO_LT 	:
					
					break;
				case BO_GT 	:
					
					break;
				case BO_LE 	:
					
					break;
				case BO_GE 	:
					
					break;
				case BO_EQ 	:
					
					break;
				case BO_NE 	:
					
					break;
				case BO_And 	:
					
					break;
				case BO_Or 	:
					
					break;
				case BO_LAnd 	:
					break;
				case BO_LOr 	:
					
					break;
				case BO_Assign 	:
					break;
				case BO_MulAssign 	:
					break;
				case BO_DivAssign 	:
					break;
				case BO_RemAssign		:
					break;
				case BO_AddAssign 	:
					break;
				case BO_SubAssign 	:
					break;
				case BO_AndAssign 	:
					break;
				case BO_OrAssign 	:
					break;
			}
			return true;
		}
		bool  clangUnaryOperatorCheck(clang::UnaryOperator * unaryOperator){
			clangExprCheck(unaryOperator->getSubExpr());
			switch(unaryOperator->getOpcode()){
				default:	
					std::cerr<<"Check:clangUnaryOperatorCheck: We do not consider processing unaryOperator: "<<unaryOperator->getOpcodeStr(unaryOperator->getOpcode()).str()<<std::endl;
					occurError=true;
					return false;
				case UO_PostInc 	://i++
					
					break;
				case UO_PostDec 	://i--;
					break;
				case UO_PreInc 	://++i
					break;
				case UO_PreDec 	://--i;
					break;
				case UO_Plus 	://+i
					break;
				case UO_Minus 	://-i;
					break;
				case UO_Not 	://~i;
					break;
				case UO_LNot 	://!i
					break;
			}
			return true;
		}
		
		bool  clangExprCheck(const clang::Expr * clangexpr){
			switch (clangexpr->getStmtClass()) {
				default:
					std::cerr<<"Check:clangExprCheck: We do not consider processing "<<clangexpr->getStmtClassName()<<std::endl;
					occurError=true;
					return false;
				case clang::Stmt::BinaryOperatorClass:
					clangBinaryOperatorCheck((clang::BinaryOperator*)clangexpr);
					break;
				case clang::Stmt::ArraySubscriptExprClass:
					
					break;
				case clang::Stmt::CharacterLiteralClass:
					break;
				case clang::Stmt::CXXBoolLiteralExprClass:
					break;
				case clang::Stmt::IntegerLiteralClass:
					break;
				case clang::Stmt::DeclRefExprClass:
					break;
				case clang::Stmt::UnaryOperatorClass:
					clangUnaryOperatorCheck((clang::UnaryOperator*)clangexpr);
					break;
				case clang::Stmt::ImplicitCastExprClass:
					{
						const CastExpr * castExpr=(const CastExpr *)clangexpr;
						clangExprCheck(castExpr->getSubExpr());
						break;
					}
			}
			return  true;
		}

};
#endif