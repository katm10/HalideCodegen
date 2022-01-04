#include "ast/Substitute.h"
#include <sstream>

namespace AST {

struct Substitute : public Mutator {

    Substitute(const VarScope &_replacements) : replacements(_replacements) {}

    ExprPtr visit(const ConstantVar *expr) override {
        auto replacement = replacements.find(expr->name);
        if (replacement != replacements.end()) {
            return std::make_shared<IdWrapper>(replacement->second, /* is_const */true);
        }
        return std::make_shared<ConstantVar>(expr->name);
    }

    ExprPtr visit(const Var *expr) override {
        auto replacement = replacements.find(expr->name);
        if (replacement != replacements.end()){
            return std::make_shared<IdWrapper>(replacement->second, /* is_const */false);
        }
        return std::make_shared<Var>(expr->name);
    }

    ExprPtr visit(const IdWrapper *expr) override {
        const IdPtr new_id = substitute(expr->id, replacements);
        return std::make_shared<IdWrapper>(new_id, expr->is_const);
    }

private: 
    const VarScope &replacements;
};

AST::ExprPtr substitute(const AST::ExprPtr &expr, const VarScope &scope) {
    AST::Substitute substitute(scope);
    return expr->mutate(&substitute);
}

} // namespace AST