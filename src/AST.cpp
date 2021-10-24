#include "AST.h"
#include "Mutator.h"
#include "Visitor.h"


namespace AST {

void ConstantInt::accept(Visitor *v) const {
    v->visit(this);
}

void ConstantVar::accept(Visitor *v) const {
    v->visit(this);
}

void Var::accept(Visitor *v) const {
    v->visit(this);
}

void Add::accept(Visitor *v) const {
    v->visit(this);
}

void Sub::accept(Visitor *v) const {
    v->visit(this);
}

void Mod::accept(Visitor *v) const {
    v->visit(this);
}

void Mul::accept(Visitor *v) const {
    v->visit(this);
}

void Div::accept(Visitor *v) const {
    v->visit(this);
}

void Min::accept(Visitor *v) const {
    v->visit(this);
}

void Max::accept(Visitor *v) const {
    v->visit(this);
}

void EQ::accept(Visitor *v) const {
    v->visit(this);
}

void NE::accept(Visitor *v) const {
    v->visit(this);
}

void LT::accept(Visitor *v) const {
    v->visit(this);
}

void LE::accept(Visitor *v) const {
    v->visit(this);
}

void GT::accept(Visitor *v) const {
    v->visit(this);
}

void GE::accept(Visitor *v) const {
    v->visit(this);
}

void And::accept(Visitor *v) const {
    v->visit(this);
}

void Or::accept(Visitor *v) const {
    v->visit(this);
}

void Not::accept(Visitor *v) const {
    v->visit(this);
}

void Select::accept(Visitor *v) const {
    v->visit(this);
}

void Ramp::accept(Visitor *v) const {
    v->visit(this);
}

void Broadcast::accept(Visitor *v) const {
    v->visit(this);
}

void Fold::accept(Visitor *v) const {
    v->visit(this);
}

void CanProve::accept(Visitor *v) const {
    v->visit(this);
}

void Call::accept(Visitor *v) const {
    v->visit(this);
}

ExprPtr ConstantInt::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr ConstantVar::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Var::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Add::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Sub::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Mod::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Mul::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Div::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Min::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Max::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr EQ::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr NE::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr LT::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr LE::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr GT::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr GE::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr And::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Or::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Not::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Select::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Ramp::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Broadcast::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Fold::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr CanProve::mutate(Mutator *m) const {
    return m->visit(this);
}

ExprPtr Call::mutate(Mutator *m) const {
    return m->visit(this);
}

}  // namsepace AST
