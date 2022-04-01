#pragma once

#include "ast/Types.h"

namespace AST {

struct Mutator {
    virtual ExprPtr visit(const ConstantInt *);
    virtual ExprPtr visit(const ConstantVar *);
    virtual ExprPtr visit(const Var *);
    virtual ExprPtr visit(const Add *);
    virtual ExprPtr visit(const Sub *);
    virtual ExprPtr visit(const Mod *);
    virtual ExprPtr visit(const Mul *);
    virtual ExprPtr visit(const Div *);
    virtual ExprPtr visit(const Min *);
    virtual ExprPtr visit(const Max *);
    virtual ExprPtr visit(const EQ *);
    virtual ExprPtr visit(const NE *);
    virtual ExprPtr visit(const LT *);
    virtual ExprPtr visit(const LE *);
    virtual ExprPtr visit(const GT *);
    virtual ExprPtr visit(const GE *);
    virtual ExprPtr visit(const And *);
    virtual ExprPtr visit(const Or *);
    virtual ExprPtr visit(const Not *);
    virtual ExprPtr visit(const Select *);
    virtual ExprPtr visit(const Ramp *);
    virtual ExprPtr visit(const Broadcast *);

    virtual ExprPtr visit(const Fold *);
    virtual ExprPtr visit(const FoldBlock *);
    virtual ExprPtr visit(const FoldCall *);

    virtual ExprPtr visit(const CanProve *);
    virtual ExprPtr visit(const Call *);

    virtual ExprPtr visit(const IdWrapper *);
};

}  // namsepace AST
