#include "Substitute.h"

namespace AST {

ExprPtr Substitute::visit(const ConstantVar *expr){
    auto replacement = replacements.find(expr->name);
    if (replacement != replacements.end()){
        return std::make_shared<ConstantVar>(replacement->second);
    }
    return std::make_shared<ConstantVar>(expr->name);
}

ExprPtr Substitute::visit(const Var *expr){
    auto replacement = replacements.find(expr->name);
    if (replacement != replacements.end()){
        return std::make_shared<Var>(replacement->second);
    }
    return std::make_shared<Var>(expr->name);
}

} // namespace AST