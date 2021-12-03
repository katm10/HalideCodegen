#pragma once

#include "ast/Mutator.h"
#include "VarScope.h"
#include <map>
#include <string>

namespace AST {
    struct Substitute : public Mutator {

        Substitute(const VarScope &_replacements) : replacements(_replacements) {}

        ExprPtr visit(const ConstantVar *) override;
        ExprPtr visit(const Var *) override;

        private: 
        const VarScope &replacements;
    };
} // namespace AST