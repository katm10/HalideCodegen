#include "ast/Visitor.h"
#include "cfir/Nodes.h"
#include "ast/Types.h"

#include <stack>
#include <string>
#include <vector>

namespace AST {
    ExprPtr linearize_fold(const Fold *node, VarScope &scope);
}
