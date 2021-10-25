#pragma once

#include "Visitor.h"

#include <iostream>
#include <string>

namespace AST {

struct ConstantCheck final : public Visitor {
    bool _is_const = true;

    bool is_const(const ExprPtr expr){
        expr->accept(this);
        return _is_const;
    }

    void visit(const ConstantInt *expr) override {}
    void visit(const ConstantVar *expr) override {}

    void visit(const Var *expr) override {
        _is_const = false;
    }

    template <typename T>
    void visit(const BinaryOp<T> *expr) {
        expr->a->accept(this);
        expr->b->accept(this);
    }
    
    template <typename T>
    void visit(const UnaryOp<T> *expr) {
        expr->a->accept(this);
    }

    void visit(const Select *expr) {
        expr->a->accept(this);
        expr->b->accept(this);
        expr->cond->accept(this);
    }
    
    void visit(const Ramp *expr) {
        expr->base->accept(this);
        expr->lanes->accept(this);
        expr->stride->accept(this);
    }
    void visit(const Broadcast *expr) {
        expr->lanes->accept(this);
        expr->value->accept(this);
    }
    void visit(const Fold *expr) {
        expr->value->accept(this);
    }
    void visit(const CanProve *expr) {
        expr->value->accept(this);
    }
};

}  // namsepace AST
