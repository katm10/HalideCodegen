#include "ast/Printer.h"
#include "ast/Types.h"
#include "ast/Substitute.h"
#include <sstream>

namespace AST {
void Printer::visit(const ConstantInt *expr) {
    stream << expr->value;
}

void Printer::visit(const ConstantVar *expr) {
    stream << expr->name;
}

void Printer::visit(const Var *expr) {
    stream << expr->name;
}

template<typename T>
void Printer::print_binary_op_inner(const T *bop, const std::string &bop_symbol) {
    stream << "(";
    bop->a->accept(this);
    stream << " " << bop_symbol << " ";
    bop->b->accept(this);
    stream << ")";
}

template<typename T>
void Printer::print_binary_op_outer(const T *bop, const std::string &bop_symbol) {
    stream << bop_symbol << "(";
    bop->a->accept(this);
    stream << ", ";
    bop->b->accept(this);
    stream << ")";
}

template<typename T>
void Printer::print_unary_op(const T *uop, const std::string &uop_symbol) {
    stream << uop_symbol << "(";
    uop->a->accept(this);
    stream << ")";
}

void Printer::visit(const Add *expr) {
    print_binary_op_inner(expr, "+");
}

void Printer::visit(const Sub *expr) {
    print_binary_op_inner(expr, "-");
}

void Printer::visit(const Mod *expr) {
    print_binary_op_inner(expr, "%");
}

void Printer::visit(const Mul *expr) {
    print_binary_op_inner(expr, "*");
}

void Printer::visit(const Div *expr) {
    print_binary_op_inner(expr, "/");
}

void Printer::visit(const Min *expr) {
    print_binary_op_outer(expr, "min");
}

void Printer::visit(const Max *expr) {
    print_binary_op_outer(expr, "max");
}

void Printer::visit(const EQ *expr) {
    print_binary_op_inner(expr, "==");
}

void Printer::visit(const NE *expr) {
    print_binary_op_inner(expr, "!=");
}

void Printer::visit(const LT *expr) {
    print_binary_op_inner(expr, "<");
}

void Printer::visit(const LE *expr) {
    print_binary_op_inner(expr, "<=");
}

void Printer::visit(const GT *expr) {
    print_binary_op_inner(expr, ">");
}

void Printer::visit(const GE *expr) {
    print_binary_op_inner(expr, ">=");
}

void Printer::visit(const And *expr) {
    print_binary_op_inner(expr, "&&");
}

void Printer::visit(const Or *expr) {
    print_binary_op_inner(expr, "||");
}

void Printer::visit(const Not *expr) {
    print_unary_op(expr, "!");
}

void Printer::visit(const Select *expr) {
    stream << "select(";
    expr->cond->accept(this);
    stream << ", ";
    expr->a->accept(this);
    stream << ", ";
    expr->b->accept(this);
    stream << ")";
}

void Printer::visit(const Ramp *expr) {
    stream << "ramp(";
    expr->base->accept(this);
    stream << ", ";
    expr->stride->accept(this);
    stream << ", ";
    expr->lanes->accept(this);
    stream << ")";
}

void Printer::visit(const Broadcast *expr) {
    stream << "broadcast(";
    expr->value->accept(this);
    stream << ", ";
    expr->lanes->accept(this);
    stream << ")";
}

void Printer::visit(const Fold *expr) {
    stream << "fold(";
    expr->value->accept(this);
    stream << ")";
}

void Printer::visit(const FoldBlock *expr) {
    for (const auto &call : expr->intermediates){
        call.accept(this);
    }

    stream << indent << "return make_const(";
    expr->out_name->print(stream);
    stream << ", ";
    expr->out_type->print(stream);
    stream << ");\n";
}

void Printer::visit(const FoldCall *expr) {
    // TODO this is pretty bad
    stream << indent << "halide_scalar_value_t ";
    expr->out_name->print(stream);
    stream << ";\n" << indent << "halide_type_t ";
    expr->out_type->print(stream);
    stream << ";\n";

    stream << indent << "fold_" << expr->fold_type << "( ";
    expr->out_name->print(stream);
    stream << ", ";
    expr->out_type->print(stream);
    stream << ", ";

    for (size_t i = 0; i < expr->args.size(); i++){
        expr->args[i]->print(stream);
        if ( i < expr->args.size() - 1 ){
            stream << ", ";
        }
    } 

    stream << ");\n";
}

void Printer::visit(const CanProve *expr) {
    stream << "can_prove(";
    expr->value->accept(this);
    stream << ", simplifier)";
}

void Printer::visit(const Call *expr) {
    stream << expr->name << "(";
    const size_t size = expr->args.size();
    size_t index = 0;
    for (const auto &arg : expr->args) {
        arg->accept(this);
        index++;
        if (index != size) {
            stream << ", ";
        }
    }
    stream << ")";
}

void Printer::visit(const IdWrapper *expr) {
    expr->id->print(stream);
}

void print(std::ostream &os, ExprPtr expr, std::string indent) {
    Printer printer(os, indent);
    expr->accept(&printer);
}

std::string pretty_print(const ExprPtr &expr, std::string indent) {
    std::ostringstream os;
    Printer printer(os, indent);
    expr->accept(&printer);
    return os.str();
}

}  // namespace AST
