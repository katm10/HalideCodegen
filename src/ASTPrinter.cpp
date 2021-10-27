#include "ASTPrinter.h"
#include "AST.h"
#include "Substitute.h"
#include <sstream>

namespace AST {

std::string Printer::make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name) {
    return "const " + type_name + " *" + output_name + " = " + var_name + "->as<" + type_name + ">()";
}

std::string Printer::make_new_unique_name() {
    static int counter = 0;
    return "a" + std::to_string(counter++);
}


std::string Printer::build_expr(const ExprPtr &expr, const VarScope &scope) {
    std::map<std::string, std::string> replacements;
    for (const auto &p : scope) {
        // should only ever be ConstantVar or Var
        assert(p.second.type == NodeType::ConstantVar || p.second.type == NodeType::Var);
        replacements[p.first] = p.second.name;
    }
    // TODO: the old method asserted that all variables that exist in `expr` have a match in `scope`,
    //       we should do that here too.
    Substitute substitute(replacements);
    ExprPtr new_expr = expr->mutate(&substitute);
    return pretty_print(new_expr);
}

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

void Printer::visit(const CanProve *expr) {
    stream << "can_prove(";
    expr->value->accept(this);
    stream << ")";
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

void print(std::ostream &os, ExprPtr expr) {
    Printer printer(os);
    expr->accept(&printer);
}

std::string pretty_print(const ExprPtr &expr) {
    std::ostringstream os;
    Printer printer(os);
    expr->accept(&printer);
    return os.str();
}

}  // namespace AST
