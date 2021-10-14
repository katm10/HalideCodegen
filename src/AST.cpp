#include "AST.h"
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

}  // namsepace AST
