#include "ast/Substitute.h"
#include <sstream>

namespace AST {

struct Substitute : public Mutator {

    Substitute(const VarScope &_replacements) : replacements(_replacements) {}

    ExprPtr visit(const ConstantVar *expr) override {
        auto replacement = replacements.find(expr->name);
        if (replacement != replacements.end()) {
            // TODO: fix this jankiness
            std::ostringstream stream;
            replacement->second->print(stream);
            return std::make_shared<ConstantVar>(stream.str());
        }
        return std::make_shared<ConstantVar>(expr->name);
    }

    ExprPtr visit(const Var *expr) override {
        auto replacement = replacements.find(expr->name);
        if (replacement != replacements.end()){
            // TODO: fix this jankiness
            std::ostringstream stream;
            replacement->second->print(stream);
            return std::make_shared<Var>(stream.str());
        }
        return std::make_shared<Var>(expr->name);
    }

private: 
    const VarScope &replacements;
};

AST::ExprPtr substitute(const AST::ExprPtr &expr, const VarScope &scope) {
    AST::Substitute substitute(scope);
    return expr->mutate(&substitute);
}

} // namespace AST