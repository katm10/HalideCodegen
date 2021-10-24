#include "Mutator.h"

namespace AST {

ExprPtr Mutator::visit(const ConstantInt *expr) {
    return std::make_shared<ConstantInt>(expr->value);
}

ExprPtr Mutator::visit(const ConstantVar *expr) {
    return std::make_shared<ConstantVar>(expr->name);
}

ExprPtr Mutator::visit(const Var *expr) {
    return std::make_shared<Var>(expr->name);
}

template<typename T>
ExprPtr mutate_binop(Mutator *mutator, const T *expr) {
    auto a = expr->a->mutate(mutator);
    auto b = expr->b->mutate(mutator);
    return std::make_shared<T>(std::move(a), std::move(b));
}

ExprPtr Mutator::visit(const Add *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Sub *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Mod *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Mul *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Div *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Min *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Max *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const EQ *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const NE *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const LT *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const LE *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const GT *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const GE *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const And *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Or *expr) {
    return mutate_binop(this, expr);
}

ExprPtr Mutator::visit(const Not *expr) {
    auto a = expr->a->mutate(this);
    return std::make_shared<Not>(std::move(a));
}

ExprPtr Mutator::visit(const Select *expr) {
    auto cond = expr->cond->mutate(this);
    auto a = expr->a->mutate(this);
    auto b = expr->b->mutate(this);
    return std::make_shared<Select>(std::move(cond), std::move(a), std::move(b));
}

ExprPtr Mutator::visit(const Ramp *expr) {
    auto base = expr->base->mutate(this);
    auto stride = expr->stride->mutate(this);
    auto lanes = expr->lanes->mutate(this);
    return std::make_shared<Ramp>(std::move(base), std::move(stride), std::move(lanes));
}

ExprPtr Mutator::visit(const Broadcast *expr) {
    auto value = expr->value->mutate(this);
    auto lanes = expr->lanes->mutate(this);
    return std::make_shared<Broadcast>(std::move(value), std::move(lanes));
}

ExprPtr Mutator::visit(const Fold *expr) {
    auto value = expr->value->mutate(this);
    return std::make_shared<Fold>(std::move(value));
}

ExprPtr Mutator::visit(const CanProve *expr) {
    auto value = expr->value->mutate(this);
    return std::make_shared<CanProve>(std::move(value));
}

ExprPtr Mutator::visit(const Call *expr) {
    const size_t size = expr->args.size();
    std::vector<const ExprPtr> args;
    for (size_t i = 0; i < size; i++) {
        const auto &arg = expr->args[i];
        args.emplace_back(arg->mutate(this));
    }
    return std::make_shared<Call>(args, expr->name);
}

}  // namespace AST
