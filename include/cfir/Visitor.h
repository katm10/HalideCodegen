#pragma once

namespace CFIR {

struct Node;
struct Add;
struct Sub;
struct Mod;
struct Mul;
struct Div;
struct Min;
struct Max;
struct EQ;
struct NE;
struct LT;
struct LE;
struct GT;
struct GE;
struct And;
struct Or;
struct Not;
struct Select;
struct ConstantInt;
struct Broadcast;
struct Ramp;
struct Call;
struct Fold;
struct CanProve;
struct Equality;
struct Return;
struct Condition;
struct IsConstant;
struct Predicate;
struct Sequence;

struct Visitor {
    virtual void visit(const Node *);
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
    virtual void visit(const ConstantInt *);
    virtual void visit(const Broadcast *);
    virtual void visit(const Ramp *);
    virtual void visit(const Call *);
    virtual void visit(const Fold *);
    virtual void visit(const CanProve *);
    virtual void visit(const Equality *);
    virtual void visit(const Return *);
    virtual void visit(const Condition *);
    virtual void visit(const IsConstant *);
    virtual void visit(const Predicate *);
    virtual void visit(const Sequence *);
};

}  // namsepace CFIR
