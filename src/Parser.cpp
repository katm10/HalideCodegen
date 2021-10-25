#include "Parser.h"
#include "ConstantCheck.h"

#include <fstream>
#include <stdio.h>
#include <memory>
#include <map>

using std::map;
using std::ostringstream;
using std::string;
using std::vector;
using namespace AST;

/**
 * TODO:
 * - IRMatcher::Overflow <- ignore
 * - overflows(thing), is_const, is_float, is_max_value, is_min_value <- use generic Call AST node
 * - intrin <- ignore for now
 */

size_t get_filesize(const std::string &filename)
{
    std::ifstream file(filename, std::ios::binary | std::ios::ate);
    size_t filesize = file.tellg();
    file.close();

    return filesize;
}

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
    {"operand_no_overflow", NumericType::OPERAND_NO_OVERFLOW},
    {"allowed_overflow", NumericType::ALLOWED_OVERFLOW}};

void report_error(const char **cursor, const char *debug_info)
{
    printf(debug_info);
    printf("Parsing failed at %s\n", *cursor);
    abort();
}

bool is_whitespace(char c)
{
    return c == ' ' || c == '\n' || c == '\t';
}

void consume_whitespace(const char **cursor, const char *end)
{
    while (*cursor < end && is_whitespace(**cursor))
    {
        (*cursor)++;
    }
}

bool consume(const char **cursor, const char *end, const char *expected)
{
    const char *tmp = *cursor;
    while (*tmp == *expected && tmp < end && *expected)
    {
        tmp++;
        expected++;
    }
    if ((*expected) == 0)
    {
        *cursor = tmp;
        return true;
    }
    else
    {
        return false;
    }
}

void expect(const char **cursor, const char *end, const char *pattern)
{
    if (!consume(cursor, end, pattern))
    {
        printf("Parsing failed. Expected %s, got %s\n",
               pattern, *cursor);
        abort();
    }
}

bool check(const char **cursor, const char *end, const char *pattern)
{
    const char *tmp_cursor = *cursor;
    return consume(&tmp_cursor, end, pattern);
}

string consume_token(const char **cursor, const char *end)
{
    size_t sz = 0;
    while (*cursor + sz < end &&
           (std::isalnum((*cursor)[sz]) ||
            (*cursor)[sz] == '!' ||
            (*cursor)[sz] == '.' ||
            (*cursor)[sz] == '$' ||
            (*cursor)[sz] == '_'))
        sz++;
    string result{*cursor, sz};
    *cursor += sz;
    return result;
}

string consume_op(const char **cursor, const char *end)
{
    size_t sz = 0;
    while ((*cursor)[sz] == '+' || (*cursor)[sz] == '-' || (*cursor)[sz] == '*' || (*cursor)[sz] == '%' || (*cursor)[sz] == '/' || (*cursor)[sz] == '>' || (*cursor)[sz] == '<' || (*cursor)[sz] == '=' || (*cursor)[sz] == '!')
    {
        sz++;
    }
    string result{*cursor, sz};
    *cursor += sz;
    return result;
}

string consume_name(const char **cursor, const char *end)
{
    size_t sz = 0;
    while (*cursor + sz < end &&
           std::isalnum((*cursor)[sz]))
    {
        sz++;
    }
    string result{*cursor, sz};
    *cursor += sz;
    return result;
}

int64_t consume_int(const char **cursor, const char *end)
{
    bool negative = consume(cursor, end, "-");
    int64_t n = 0;
    while (*cursor < end && **cursor >= '0' && **cursor <= '9')
    {
        n *= 10;
        n += (**cursor - '0');
        (*cursor)++;
    }
    return negative ? -n : n;
}

class Parser
{
    const char *cursor, *end;

    void report_error(const char *debug_info)
    {
        ::report_error(&cursor, debug_info);
    }

    void consume_whitespace()
    {
        ::consume_whitespace(&cursor, end);
    }

    bool consume(const char *str)
    {
        return ::consume(&cursor, end, str);
    }

    void expect(const char *str)
    {
        ::expect(&cursor, end, str);
    }

    int64_t consume_int()
    {
        return ::consume_int(&cursor, end);
    }

    string consume_token()
    {
        return ::consume_token(&cursor, end);
    }

    string consume_name()
    {
        return ::consume_name(&cursor, end);
    }

    string consume_op()
    {
        return ::consume_op(&cursor, end);
    }

    char peek() const
    {
        return *cursor;
    }

    bool check(const char *pattern)
    {
        return ::check(&cursor, end, pattern);
    }

    // Unit ::= Var | ConstantVar | ConstantInt | Call | "(" Expr ")"
    ExprPtr parse_unit()
    {
        ExprPtr call = parse_call();
        if (call != nullptr)
        {
            return call;
        }

        // TODO: should probably have a better solution for "lanes" here
        if (peek() == 'c' || check("lanes"))
        {
            // This is a ConstantVar
            std::string name = consume_name();
            return std::make_shared<ConstantVar>(name);
        }
        else if (std::isalpha(peek()))
        {
            // This is a Var
            std::string name = consume_name();
            return std::make_shared<Var>(name);
        }
        else if (std::isdigit(peek()))
        {
            // This is a ConstantInt
            int64_t val = consume_int();
            return std::make_shared<ConstantInt>(val);
        }
        else if (consume("("))
        {
            ExprPtr a = parse_expr();
            expect(")");
            return a;
        }
        else
        {
            report_error("parse_unit() could not find a variable, int, call, or parenthesised expr.");
            return nullptr;
        }
    }

    // Call ::= <function name>'(' Expr (',' Expr)* ')'
    ExprPtr parse_call()
    {
        if (consume("min("))
        {
            ExprPtr a = parse_expr();
            expect(",");
            ExprPtr b = parse_expr();
            expect(")");
            return std::make_shared<Min>(a, b);
        }
        if (consume("max("))
        {
            ExprPtr a = parse_expr();
            expect(",");
            ExprPtr b = parse_expr();
            expect(")");
            return std::make_shared<Min>(a, b);
        }
        if (consume("select("))
        {
            ExprPtr a = parse_expr();
            expect(",");
            ExprPtr b = parse_expr();
            expect(",");
            ExprPtr c = parse_expr();
            expect(")");
            return std::make_shared<Select>(a, b, c);
        }
        if (consume("ramp("))
        {
            ExprPtr base = parse_expr();
            expect(",");
            ExprPtr stride = parse_expr();
            expect(",");
            ExprPtr lanes = parse_expr();
            expect(")");

            // TODO this should not be here
            ConstantCheck cc;
            bool const_lanes = cc.is_const(lanes);
            if (!const_lanes)
            {
                std::cerr << "Ramp expects lanes to be constant." << std::endl;
                assert(false);
                exit(1);
            }

            return std::make_shared<Ramp>(base, stride, lanes);
        }
        if (consume("broadcast("))
        {
            ExprPtr val = parse_expr();
            expect(",");
            ExprPtr lanes = parse_expr();
            expect(")");

            // TODO this should not be here
            ConstantCheck cc;
            bool const_lanes = cc.is_const(lanes);
            if (!const_lanes)
            {
                std::cerr << "Broadcast expects lanes to be constant." << std::endl;
                assert(false);
                exit(1);
            }

            return std::make_shared<Broadcast>(val, lanes);
        }
        if (consume("fold("))
        {
            ExprPtr val = parse_expr();
            expect(")");
            return std::make_shared<Fold>(val);
        }
        if (consume("can_prove("))
        {
            ExprPtr val = parse_expr();
            expect(",this)"); // Do we ever expect another simplifier?
            return std::make_shared<CanProve>(val);
        }
        return nullptr;
    }

    // Product ::= Unit ( ('*' | '/' | '%') Unit)*
    ExprPtr parse_product()
    {
        ExprPtr a = parse_unit();

        while (peek() == '*' || peek() == '/' || peek() == '%')
        {
            // TODO this would probably be better as a const char*. Then I could use switch statements instead of if else too.
            string op = consume_op();
            ExprPtr b = parse_unit();

            if (op == "*")
            {
                a = std::make_shared<Mul>(a, b);
            }
            else if (op == "/")
            {
                a = std::make_shared<Div>(a, b);
            }
            else if (op == "%")
            {
                a = std::make_shared<Mod>(a, b);
            }
            else
            {
                report_error("parse_product() could not find matching op.");
            }
        }
        return a;
    }

    // Arithmetic ::= Product ( ('+' | '-') Product)*
    ExprPtr parse_arithmetic()
    {
        ExprPtr a = parse_product();

        while (peek() == '+' || peek() == '-')
        {
            string op = consume_op();
            ExprPtr b = parse_product();

            if (op == "+")
            {
                a = std::make_shared<Add>(a, b);
            }
            else if (op == "-")
            {
                a = std::make_shared<Sub>(a, b);
            }
            else
            {
                report_error("parse_arithmetic() could not find matching op.");
            }
        }
        return a;
    }

    // BoolUnit ::= '!'? Predicate
    ExprPtr parse_boolunit()
    {
        if (!check("!=") && consume("!"))
        {
            ExprPtr a = parse_pred();

            return std::make_shared<Not>(a);
        }

        if (consume("-"))
        {
            ExprPtr a = std::make_shared<ConstantInt>(0);
            ExprPtr b = parse_pred();
            return std::make_shared<Sub>(a, b);
        }

        return parse_pred();
    }

    // Predicate ::= Arithmetic ( ('<' | '>' | '<=' | '>='| '==' | '!=') Arithmetic)?
    ExprPtr parse_pred()
    {
        ExprPtr a = parse_arithmetic();
        while (peek() == '<' || peek() == '>' || peek() == '=' || peek() == '!')
        {
            string op = consume_op();
            ExprPtr b = parse_arithmetic();

            if (op == "<=")
            {
                a = std::make_shared<LE>(a, b);
            }
            else if (op == ">=")
            {
                a = std::make_shared<GE>(a, b);
            }
            else if (op == "<")
            {
                a = std::make_shared<LT>(a, b);
            }
            else if (op == ">")
            {
                a = std::make_shared<GT>(a, b);
            }
            else if (op == "==")
            {
                a = std::make_shared<EQ>(a, b);
            }
            else if (op == "!=")
            {
                a = std::make_shared<NE>(a, b);
            }
            else
            {
                report_error("parse_pred() could not find matching op.");
            }
        }
        return a;
    }

    // Conjunction ::= BoolUnit ('&&' BoolUnit)*
    ExprPtr parse_conjunction()
    {
        ExprPtr a = parse_boolunit();

        while (consume("&&"))
        {
            ExprPtr b = parse_boolunit();
            a = std::make_shared<And>(a, b);
        }
        return a;
    }

    // Expr ::= Conjunction ( '||' Conjunction )*
    ExprPtr parse_expr()
    {
        ExprPtr a = parse_conjunction();

        while (consume("||"))
        {
            ExprPtr b = parse_conjunction();
            a = std::make_shared<Or>(a, b);
        }
        return a;
    }

    Rule *parse_r()
    {
        // TODO Pointer or reference?
        expect("rewrite(");
        ExprPtr lhs = parse_expr();
        expect(",");
        ExprPtr rhs = parse_expr();
        ExprPtr pred = nullptr;
        if (consume(","))
        {
            pred = parse_expr();
        }
        expect(")");
        return new Rule(lhs, rhs, pred);
    }

    NumericType parse_type()
    {
        for (const auto typePair : typeStrings)
        {
            if (consume(typePair.first.c_str()))
            {
                return typePair.second;
            }
        }
        report_error("parse_type() found no type matches.");
    }

    uint16_t parse_types()
    {
        bool allowed = true;

        if (consume("!"))
        {
            allowed = false;
            expect("(");
        }

        uint16_t types = (uint16_t)parse_type();
        // TODO this isnt great
        while (!check(",rewrite") && !check(",(") && consume(","))
        {
            NumericType t = parse_type();
            types |= (uint16_t)t;
        }

        if (!allowed)
        {
            types = ~types;
            expect(")");
        }

        return types;
    }

public:
    std::vector<Rule *> parse_rules()
    {
        std::vector<Rule *> rules;

        while (cursor < end)
        {
            // Parse R
            if (consume("("))
            {
                // Parse G
                std::vector<Rule *> inner_rules;
                inner_rules.push_back(parse_r());
                while (consume(","))
                {
                    inner_rules.push_back(parse_r());
                    consume_whitespace();
                }
                expect(")");
                expect("|-");

                uint16_t types = parse_types();

                for (const auto rule : inner_rules)
                {
                    rule->set_types(types);
                    rules.push_back(rule);
                }
            }
            else
            {
                Rule *r(parse_r());
                if (consume("|-"))
                {
                    uint16_t types = parse_types();
                    r->set_types(types);
                }
                else
                {
                    r->set_types(UINT16_MAX); // set all bits to 1
                }
                rules.push_back(r);
            }
            consume(",");
            consume_whitespace();
        }
        return rules;
    }

    Parser(const char *c, const char *e)
        : cursor(c), end(e)
    {
    }
};

std::vector<Rule *> parse_rules_from_file(const std::string &filename)
{
    size_t filesize = get_filesize(filename);

    char byte = 0;
    char cfile[filesize];

    std::ifstream input_file(filename);
    assert(input_file.is_open());

    bool is_comment = false;

    size_t i = 0;
    while (input_file.get(byte))
    {
        if (byte == '/' && input_file.peek() == '/')
        {
            is_comment = true;
        }
        else if (byte == '\n' && is_comment)
        {
            is_comment = false;
        }
        else if (!(byte == ' ' || byte == '\t' || byte == '\n') && !is_comment)
        {
            cfile[i] = byte;
            i++;
        }
    }
    const char *cursor = cfile;
    const char *end = cfile + i;

    Parser parser(cursor, end);
    std::vector<Rule *> rules = parser.parse_rules();
    return rules;
}