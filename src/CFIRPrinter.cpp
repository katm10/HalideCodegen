#include "CFIRPrinter.h"
#include "Substitute.h"
#include "ASTPrinter.h"
#include <cassert>

std::string make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name) {
    return "const " + type_name + " *" + output_name + " = " + var_name + ".as<" + type_name + ">()";
}

std::string make_new_unique_name() {
    static int counter = 0;
    return "a" + std::to_string(counter++);
}

std::string build_expr(const AST::ExprPtr &expr, const VarScope &scope) {
    AST::Substitute substitute(scope);
    AST::ExprPtr new_expr = expr->mutate(&substitute);
    return pretty_print(new_expr);
}
