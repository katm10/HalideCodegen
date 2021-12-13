#include "ast/Types.h"
#include "ast/Mutator.h"
#include "ast/Visitor.h"


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

void IdWrapper::accept(Visitor *v) const {
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

ExprPtr IdWrapper::mutate(Mutator *m) const {
    return m->visit(this);
}


bool ConstantInt::equals(const ExprPtr expr) const {
    if (const ConstantInt *as = expr->as<ConstantInt>()) {
        return value == as->value;
    } else {
        return false;
    }
}

bool Select::equals(const ExprPtr expr) const {
    if (const Select *as = expr->as<Select>()) {
        return cond->equals(as->cond) && a->equals(as->a) && b->equals(as->b);
    } else {
        return false;
    }
}

bool Ramp::equals(const ExprPtr expr) const {
    if (const Ramp *as = expr->as<Ramp>()) {
        return base->equals(as->base) && stride->equals(as->stride) && lanes->equals(as->lanes);
    } else {
        return false;
    }
}

bool Broadcast::equals(const ExprPtr expr) const {
    if (const Broadcast *as = expr->as<Broadcast>()) {
        return value->equals(as->value) && lanes->equals(as->lanes);
    } else {
        return false;
    }
}

bool Fold::equals(const ExprPtr expr) const {
    if (const Fold *as = expr->as<Fold>()) {
        return value->equals(as->value);
    } else {
        return false;
    }
}

bool CanProve::equals(const ExprPtr expr) const {
    if (const CanProve *as = expr->as<CanProve>()) {
        return value->equals(as->value);
    } else {
        return false;
    }
}

bool Call::equals(const ExprPtr expr) const {
    if (const Call *as = expr->as<Call>()) {
        if (name != as->name || args.size() != as->args.size()) {
            return false;
        }
        for (size_t i = 0; i < args.size(); i++) {
            if (!args[i]->equals(as->args[i])) {
                return false;
            }
        }
        return true;
    } else {
        return false;
    }
}

bool IdWrapper::equals(const ExprPtr expr) const {
    if (const IdWrapper *as = expr->as<IdWrapper>()) {
        return (is_const == as->is_const) && id->equals(as->id);
    } else {
        return false;
    }
}

}  // namsepace AST
