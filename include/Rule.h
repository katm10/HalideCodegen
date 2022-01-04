#ifndef TRS_CODEGEN_RULE
#define TRS_CODEGEN_RULE

#include "ast/Types.h"
#include <string>
#include <vector>

using namespace AST;

enum class NumericType : uint16_t
{
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

const std::map<std::string, NumericType, std::greater<std::string>> typeStrings{
    {"uint", NumericType::UINT},
    {"int", NumericType::INT},
    {"float", NumericType::FLOAT},
    {"no_overflow_scalar_int", NumericType::NO_OVERFLOW_SCALAR_INT},
    {"no_overflow_int", NumericType::NO_OVERFLOW_INT},
    {"no_overflow", NumericType::NO_OVERFLOW},
    {"bool", NumericType::BOOL},
    {"operand_uint", NumericType::OPERAND_UINT},
    {"operand_int", NumericType::OPERAND_INT},
    {"operand_float", NumericType::OPERAND_FLOAT},
    {"operand_no_overflow_scalar_int", NumericType::OPERAND_NO_OVERFLOW_SCALAR_INT},
    {"operand_no_overflow_int", NumericType::OPERAND_NO_OVERFLOW_INT},
    {"operand_no_overflow", NumericType::OPERAND_NO_OVERFLOW}};

class Rule
{
public:
    const ExprPtr before;
    const ExprPtr after;
    const ExprPtr pred;
    uint16_t types = 0;

    ~Rule() = default;
    Rule() {}
    Rule(const ExprPtr _before, const ExprPtr _after)
        : before(_before), after(_after) {}

    Rule(const ExprPtr _before, const ExprPtr _after, const ExprPtr _pred)
        : before(_before), after(_after), pred(_pred) {}

    void add_type(bool allowed, uint16_t type);
    void set_types(uint16_t _types);
    uint16_t get_types();
    std::string generate_condition(const std::string &type_name) const;
};

#endif