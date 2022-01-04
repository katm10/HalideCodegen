#pragma once

#include "ast/Mutator.h"
#include "Identifier.h"

#include <map>
#include <string>

namespace AST {

    AST::ExprPtr substitute(const AST::ExprPtr &expr, const VarScope &scope);

} // namespace AST
