#include "CFIRPrinter.h"
#include "Substitute.h"
#include "ASTPrinter.h"
#include <cassert>

// std::string make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name) {
//     return "const " + type_name + " *" + output_name + " = " + var_name + ".as<" + type_name + ">()";
// }

// TODO: Stop typing these now, pre-declare them.
void print_type_checker_condition(std::ostream &stream, const std::shared_ptr<CFIR::Identifier> &current_id, const std::string &type_name, const std::shared_ptr<CFIR::Identifier> &output_id) {
    if (!output_id->pre_declared) {
        stream << "const " << type_name << " *";
    }
    output_id->print(stream);
    stream << " = ";
    current_id->print(stream);
    // TODO: force the identifier to do the cast?
    stream << ".as<" << type_name << ">()";
}

IdPtr make_new_unique_name() {
    static int counter = 0;
    const std::string name = "a" + std::to_string(counter++);
    return make_name(name);
}

AST::ExprPtr substitute(const AST::ExprPtr &expr, const VarScope &scope) {
    AST::Substitute substitute(scope);
    return expr->mutate(&substitute);
}
