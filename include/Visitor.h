#pragma once

#include "AST.h"

namespace AST {

struct Visitor {
    virtual void visit(const ConstantInt *);
    virtual void visit(const ConstantVar *);
    virtual void visit(const Var *);
    virtual void visit(const Add *);
    virtual void visit(const Sub *);
    virtual void visit(const Mod *);
    virtual void visit(const Mul *);
    virtual void visit(const Div *);
    virtual void visit(const Min *);
    virtual void visit(const Max *);
    virtual void visit(const EQ *);
    virtual void visit(const NE *);
    virtual void visit(const LT *);
    virtual void visit(const LE *);
    virtual void visit(const GT *);
    virtual void visit(const GE *);
    virtual void visit(const And *);
    virtual void visit(const Or *);
    virtual void visit(const Not *);
    virtual void visit(const Select *);
    virtual void visit(const Ramp *);
    virtual void visit(const Broadcast *);
};

}  // namsepace AST
