#pragma once

#include "Visitor.h"

#include <iostream>
#include <string>
#include <map>

namespace AST
{

    struct Printer final : public Visitor
    {
        Printer(std::ostream &_stream) : stream(_stream) {}
        std::ostream &stream;

        static std::string make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name);
        static std::string make_new_unique_name();

        static std::string build_expr(const ExprPtr &expr, const VarScope &scope);

        void visit(const ConstantInt *) override;
        void visit(const ConstantVar *) override;
        void visit(const Var *) override;

        template <typename T>
        void print_binary_op_inner(const T *bop, const std::string &bop_symbol);
        template <typename T>
        void print_binary_op_outer(const T *bop, const std::string &bop_symbol);

        template <typename T>
        void print_unary_op(const T *uop, const std::string &uop_symbol);

        void visit(const Add *) override;
        void visit(const Sub *) override;
        void visit(const Mod *) override;
        void visit(const Mul *) override;
        void visit(const Div *) override;
        void visit(const Min *) override;
        void visit(const Max *) override;
        void visit(const EQ *) override;
        void visit(const NE *) override;
        void visit(const LT *) override;
        void visit(const LE *) override;
        void visit(const GT *) override;
        void visit(const GE *) override;
        void visit(const And *) override;
        void visit(const Or *) override;
        void visit(const Not *) override;
        void visit(const Select *) override;
        void visit(const Ramp *) override;
        void visit(const Broadcast *) override;

        void visit(const Fold *) override;
        void visit(const CanProve *) override;
        void visit(const Call *) override;
    };

    void print(std::ostream &os, ExprPtr expr);

    std::string pretty_print(const ExprPtr &expr);

}  // namsepace AST
