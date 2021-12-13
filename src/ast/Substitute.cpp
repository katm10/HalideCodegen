#include "ast/Substitute.h"
#include <sstream>

namespace AST {

ExprPtr Substitute::visit(const ConstantVar *expr){
    auto replacement = replacements.find(expr->name);
    if (replacement != replacements.end()) {
        // TODO: fix this jankiness
        std::ostringstream stream;
        replacement->second->print(stream);
        return std::make_shared<ConstantVar>(stream.str());
    }
    return std::make_shared<ConstantVar>(expr->name);
}

ExprPtr Substitute::visit(const Var *expr){
    auto replacement = replacements.find(expr->name);
    if (replacement != replacements.end()){
        // TODO: fix this jankiness
        std::ostringstream stream;
        replacement->second->print(stream);
        return std::make_shared<Var>(stream.str());
    }
    return std::make_shared<Var>(expr->name);
}

} // namespace AST