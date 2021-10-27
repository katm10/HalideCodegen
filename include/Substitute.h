#include "Mutator.h"
#include <map>
#include <string>

namespace AST {
    struct Substitute : public Mutator {

        Substitute(const std::map<std::string, std::string> _replacements) : replacements(_replacements) {}

        ExprPtr visit(const ConstantVar *) override;
        ExprPtr visit(const Var *) override;

        private: 
        std::map<std::string, std::string> replacements; 
    };
} // namespace AST