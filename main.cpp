#include "AST.h"
#include "ASTPrinter.h"
#include "Parser.h"

#include <iostream>
#include <memory>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        std::cout << "Usage: ./bin/Parser <input filename>\n";
        return 1;
    }
    std::string filename = argv[1];
    std::vector<Rule *> rules = parse_rules_from_file(filename);

    // Small example of building an AST
    auto one = std::make_shared<AST::ConstantInt>(1);
    auto a = std::make_shared<AST::Var>("a");
    auto c0 = std::make_shared<AST::ConstantVar>("c0");
    auto a_plus_one = std::make_shared<AST::Add>(a, one);
    auto times_c0 = std::make_shared<AST::Mul>(a_plus_one, c0);

    std::cout << "AST printed as: ";
    print(std::cout, times_c0);
    std::cout << "\n";
}
