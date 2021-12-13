#include "ast/Types.h"
#include "ast/Printer.h"
#include "Parser.h"

#include <iostream>
#include <memory>

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        std::cout << "Usage: ./main.out <input filename>\n";
        return 1;
    }
    std::string filename = argv[1];
    std::vector<Rule *> rules = parse_rules_from_file(filename);

    for (auto rule : rules)
    {
        std::cout << "Rule:";
        print(std::cout, rule->before);
        std::cout << ", ";
        print(std::cout, rule->after);

        if (rule->pred != nullptr)
        {
            std::cout << ", ";
            print(std::cout, rule->pred);
        }
        std::cout << std::endl;

        std::cout << "Allowed types: " << rule->types << std::endl;
    }
}
