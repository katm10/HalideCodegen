#ifndef TRS_CODEGEN_RULE
#define TRS_CODEGEN_RULE

#include "AST.h"
#include <string>
#include <vector>

using namespace AST;

enum NumericType {
    UINT,
    INT,
    FLOAT,
    NO_OVERFLOW,
    NO_OVERFLOW_INT,
    BOOL, 
    NO_OVERFLOW_SCALAR_INT,
    INVALID
    // TODO almost certainly missing a lot here
};

class Rule {
public:
    // TODO: this should not all be public
    const ExprPtr before;
    const ExprPtr after;
    const ExprPtr pred;
    // TODO fix this
    std::vector<NumericType> allowed_types;
    std::vector<NumericType> disallowed_types;

    ~Rule() = default;
    Rule(){}
    Rule(const ExprPtr _before, const ExprPtr _after)
        : before(_before), after(_after) {}

    Rule(const ExprPtr _before, const ExprPtr _after, const ExprPtr _pred)
        : before(_before), after(_after), pred(_pred) {}

    void set_allowed_types(std::vector<NumericType> _allowed_types);
    std::vector<NumericType> get_allowed_types();

    void set_disallowed_types(std::vector<NumericType> _disallowed_types);
    std::vector<NumericType> get_disallowed_types();
};

#endif