#include "cfir/Printer.h"
#include "ast/Substitute.h"
#include "ast/Printer.h"
#include <cassert>

// TODO: Stop typing these now, pre-declare them.
void print_type_checker_condition(std::ostream &stream, const IdPtr &current_id, const std::string &type_name, const IdPtr &output_id) {
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