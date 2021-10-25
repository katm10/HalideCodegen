#ifndef TRS_CODEGEN_RULE
#define TRS_CODEGEN_RULE

#include "AST.h"
#include <string>
#include <vector>

using namespace AST;

enum class NumericType : uint16_t {
    // INVALID = 1 << 0,
    // ANY = 1 << 1,
    UINT = 1 << 2,
    INT = 1 << 3,
    FLOAT = 1 << 4,
    NO_OVERFLOW_SCALAR_INT = 1 << 5,
    NO_OVERFLOW_INT = 1 << 6,
    NO_OVERFLOW = 1 << 7,
    BOOL = 1 << 8,
    OPERAND_UINT = 1 << 9,
    OPERAND_INT = 1 << 10,
    OPERAND_FLOAT = 1 << 11,
    OPERAND_NO_OVERFLOW_SCALAR_INT = 1 << 12,
    OPERAND_NO_OVERFLOW_INT = 1 << 13,
    OPERAND_NO_OVERFLOW = 1 << 14,
    ALLOWED_OVERFLOW = 1 << 15
};

class Rule {
public:
    const ExprPtr before;
    const ExprPtr after;
    const ExprPtr pred;
    uint16_t types = 0;

    ~Rule() = default;
    Rule(){}
    Rule(const ExprPtr _before, const ExprPtr _after)
        : before(_before), after(_after) {}

    Rule(const ExprPtr _before, const ExprPtr _after, const ExprPtr _pred)
        : before(_before), after(_after), pred(_pred) {}

    void add_type(bool allowed, uint16_t type);
    void set_types(uint16_t _types);
    uint16_t get_types();
};

#endif