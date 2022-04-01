#pragma once

#include <memory>

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
struct Fold;
struct CanProve;
struct Equality;
struct Return;
struct Condition;
struct IsConstant;
struct Predicate;
struct Sequence;
struct Declaration;
struct FoldBlock;

struct Mutator {
    virtual std::shared_ptr<Node> visit(const Add *);
    virtual std::shared_ptr<Node> visit(const Sub *);
    virtual std::shared_ptr<Node> visit(const Mod *);
    virtual std::shared_ptr<Node> visit(const Mul *);
    virtual std::shared_ptr<Node> visit(const Div *);
    virtual std::shared_ptr<Node> visit(const Min *);
    virtual std::shared_ptr<Node> visit(const Max *);
    virtual std::shared_ptr<Node> visit(const EQ *);
    virtual std::shared_ptr<Node> visit(const NE *);
    virtual std::shared_ptr<Node> visit(const LT *);
    virtual std::shared_ptr<Node> visit(const LE *);
    virtual std::shared_ptr<Node> visit(const GT *);
    virtual std::shared_ptr<Node> visit(const GE *);
    virtual std::shared_ptr<Node> visit(const And *);
    virtual std::shared_ptr<Node> visit(const Or *);
    virtual std::shared_ptr<Node> visit(const Not *);
    virtual std::shared_ptr<Node> visit(const Select *);
    virtual std::shared_ptr<Node> visit(const ConstantInt *);
    virtual std::shared_ptr<Node> visit(const Broadcast *);
    virtual std::shared_ptr<Node> visit(const Ramp *);
    virtual std::shared_ptr<Node> visit(const Equality *);
    virtual std::shared_ptr<Node> visit(const Return *);
    virtual std::shared_ptr<Node> visit(const Condition *);
    virtual std::shared_ptr<Node> visit(const IsConstant *);
    virtual std::shared_ptr<Node> visit(const Predicate *);
    virtual std::shared_ptr<Node> visit(const Sequence *);
    virtual std::shared_ptr<Node> visit(const Declaration *);
};

}  // namsepace CFIR
