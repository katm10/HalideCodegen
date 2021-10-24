#include "AST.h"
#include "ASTPrinter.h"

#include <iostream>
#include <memory>

int main(void) {
    // Small example of building an AST
    auto one = std::make_shared<AST::ConstantInt>(1);
    auto a = std::make_shared<AST::Var>("a");
    auto c0 = std::make_shared<AST::ConstantVar>("c0");
    auto a_plus_one = std::make_shared<AST::Add>(a, one);
    auto times_c0 = std::make_shared<AST::Mul>(a_plus_one, c0);

    std::cout << "AST printed as: ";
    print(std::cout, times_c0);
    std::cout << "\n";

    const std::vector<AST::ExprPtr> args = {one, a};
    auto call = std::make_shared<AST::Call>(args, "foo");
    print(std::cout, call);
    std::cout << "\n";
}
