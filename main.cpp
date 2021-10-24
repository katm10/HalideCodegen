#include "AST.h"
#include "ASTPrinter.h"
#include "Parser.h"

#include <iostream>
#include <memory>

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        std::cout << "Usage: ./bin/Parser <input filename>\n";
        return 1;
    }
    std::string filename = argv[1];
    std::vector<Rule *> rules = parse_rules_from_file(filename);

    std::cout << "AST printed as: ";
    print(std::cout, times_c0);
    std::cout << "\n";

    const std::vector<AST::ExprPtr> args = {one, a};
    auto call = std::make_shared<AST::Call>(args, "foo");
    print(std::cout, call);
    std::cout << "\n";
}
