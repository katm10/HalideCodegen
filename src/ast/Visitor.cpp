#include "ast/Visitor.h"
#include "ast/Types.h"

namespace AST {

void Visitor::visit(const ConstantInt *expr) {

}

void Visitor::visit(const ConstantVar *expr) {

}

void Visitor::visit(const Var *expr) {

}

void Visitor::visit(const Add *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Sub *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Mod *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Mul *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Div *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Min *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Max *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const EQ *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const NE *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const LT *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const LE *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const GT *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const GE *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const And *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Or *expr) {
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Not *expr) {
    expr->a->accept(this);
}

void Visitor::visit(const Select *expr) {
    expr->cond->accept(this);
    expr->a->accept(this);
    expr->b->accept(this);
}

void Visitor::visit(const Ramp *expr) {
    expr->base->accept(this);
    expr->stride->accept(this);
    expr->lanes->accept(this);
}

void Visitor::visit(const Broadcast *expr) {
    expr->value->accept(this);
    expr->lanes->accept(this);
}

void Visitor::visit(const Fold *expr) {
    expr->value->accept(this);
}

void Visitor::visit(const CanProve *expr) {
    expr->value->accept(this);
}

void Visitor::visit(const Call *expr) {
    for (const auto &arg : expr->args) {
        arg->accept(this);
    }
}

}  // namespace AST
