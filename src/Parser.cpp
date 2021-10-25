#include "Parser.h"

#include <fstream>
#include <stdio.h>
#include <string.h>
#include <memory>
#include <map>

using std::map;
using std::ostringstream;
using std::string;
using std::vector;
using namespace AST;

/**
 * TODO:
 * - fix parser
 * - overflows
 * - IRMatcher::Overflow <= match for this case specifically, will deal with Call::<blah> later
 * - handle is_const, can_prove
 * - check whitespaces work properly
 * - remove Halide dependency
 *      - create Expr class
 */

void debug(std::string s){
    std::cout << s << std::endl;
}

// TODO: how portable is this?
size_t get_filesize(const std::string &filename)
{
    std::ifstream file(filename, std::ios::binary | std::ios::ate);
    size_t filesize = file.tellg();
    file.close();

    return filesize;
}

// TODO: I don't like this solution very much, also probably missing a significant number of possible types
// switch to flags, refer to CodeGen_ARM ~l200
const std::map<std::string, NumericType> typeStrings{
    {"uint", NumericType::UINT},
    {"int", NumericType::INT},
    {"float", NumericType::FLOAT},
    {"no_overflow", NumericType::NO_OVERFLOW},
    {"no_overflow_int", NumericType::NO_OVERFLOW_INT},
    {"bool", NumericType::BOOL},
    {"no_overflow_scalar_int", NumericType::NO_OVERFLOW_SCALAR_INT}};

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

/**
 * For debugging purposes, it prints the remaining rules to parse. 
 */
void debug_remainder(const char **cursor, const char *end)
{
    string line(*cursor);
    std::cerr << line << std::endl;
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
    while ((*cursor)[sz] == '+' || (*cursor)[sz] == '-' || (*cursor)[sz] == '*' || (*cursor)[sz] == '%' || (*cursor)[sz] == '/' || (*cursor)[sz] == '>' || (*cursor)[sz] == '<' || (*cursor)[sz] == '=' ){
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

/* 
Expr consume_float(const char **cursor, const char *end)
{
    bool negative = consume(cursor, end, "-");
    int64_t integer_part = consume_int(cursor, end);
    int64_t fractional_part = 0;
    int64_t denom = 1;
    if (consume(cursor, end, "."))
    {
        while (*cursor < end && **cursor >= '0' && **cursor <= '9')
        {
            denom *= 10;
            fractional_part *= 10;
            fractional_part += (**cursor - '0');
            (*cursor)++;
        }
    }
    double d = integer_part + double(fractional_part) / denom;
    if (negative)
    {
        d = -d;
    }
    if (consume(cursor, end, "h"))
    {
        return Halide::Internal::make_const(Float(16), d);
    }
    else if (consume(cursor, end, "f"))
    {
        return Halide::Internal::make_const(Float(32), d);
    }
    else
    {
        return Halide::Internal::make_const(Float(64), d);
    }
}
*/

class Parser
{
    const char *cursor, *end;
    // std::vector<std::pair<Expr, int>> stack;
    // map<string, Type> var_types;

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

    // Expr consume_float()
    // {
    //     return ::consume_float(&cursor, end);
    // }

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

public:
    // Unit ::= Var | ConstantVar | ConstantInt | Call | "(" Expr ")"
    ExprPtr parse_unit()
    {
        // Assume we can only get a ConstantVar, Var, or ConstantInt here
        if (peek() == 'c')
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
            return parse_call();
        }
    }

    // Call ::= <function name>'(' Expr (',' Expr)* ')'
    // TODO add nullptr checks
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
            return std::make_shared<Ramp>(base, stride, lanes);
        }
        if (consume("broadcast("))
        {
            ExprPtr val = parse_expr();
            expect(",");
            ExprPtr lanes = parse_expr();
            expect(")");
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
        if (a == nullptr)
        {
            return nullptr;
        }

        while (peek() == '*' || peek() == '/' || peek() == '%')
        {
            // TODO this would probably be better as a const char*. Then I could use switch statements instead of if else too.
            string op = consume_op();
            ExprPtr b = parse_unit();
            if (b == nullptr)
            {
                return nullptr;
            }

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
                assert(0);
            }
        }
        return a;
    }

    // Arithmetic ::= Product ( ('+' | '-') Product)*
    ExprPtr parse_arithmetic()
    {
        ExprPtr a = parse_product();
        if (a == nullptr)
        {
            return nullptr;
        }

        while (peek() == '+' || peek() == '-')
        {
            string op = consume_op();
            ExprPtr b = parse_product();
            if (b == nullptr)
            {
                return nullptr;
            }

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
                return nullptr;
            }
        }
        return a;
    }

    // BoolUnit ::= '!'? Predicate
    ExprPtr parse_boolunit()
    {
        if (consume("!"))
        {
            ExprPtr a = parse_pred();
            if (a == nullptr)
            {
                return nullptr;
            }

            return std::make_shared<Not>(a);
        }

        return parse_pred();
    }

    // Predicate ::= Arithmetic ( ('<' | '>' | '<=' | '>='| '==') Arithmetic)?
    ExprPtr parse_pred()
    {
        ExprPtr a = parse_arithmetic();
        if (a == nullptr)
        {
            return nullptr;
        }

        while (peek() == '<' || peek() == '>' || peek() == '=')
        {
            string op = consume_op();
            ExprPtr b = parse_arithmetic();
            if (b == nullptr)
            {
                return nullptr;
            }

            if (op == "<=")
            {
                a = std::make_shared<LE>(a, b);
            }
            else if (op == ">=")
            {
                a = std::make_shared<GE>(a, b);
            }
            else if (consume("<"))
            {
                a = std::make_shared<LT>(a, b);
            }
            else if (consume(">"))
            {
                a = std::make_shared<GT>(a, b);
            }
            else if (consume("=="))
            {
                a = std::make_shared<EQ>(a, b);
            }
            else if (consume("!="))
            {
                a = std::make_shared<NE>(a, b);
            }
            else
            {
                return nullptr;
            }
        }
        return a;
    }

    // Conjunction ::= BoolUnit ('&&' BoolUnit)*
    ExprPtr parse_conjunction()
    {
        ExprPtr a = parse_boolunit();
        if (a == nullptr)
        {
            return nullptr;
        }

        while (consume("&&"))
        {
            ExprPtr b = parse_boolunit();
            if (b == nullptr)
            {
                return nullptr;
            }
            a = std::make_shared<And>(a, b);
        }
        return a;
    }

    // Expr ::= Conjunction ( '||' Conjunction )*
    ExprPtr parse_expr()
    {
        ExprPtr a = parse_conjunction();
        if (a == nullptr)
        {
            return nullptr;
        }

        while (consume("||"))
        {
            ExprPtr b = parse_conjunction();
            if (b == nullptr)
            {
                return nullptr;
            }
            a = std::make_shared<Or>(a, b);
        }
        return a;
    }

    // TODO: this needs to parse much more finely
    Rule *parse_r()
    {
        // TODO Pointer or reference?

        expect("rewrite(");
        ExprPtr lhs = parse_expr();
        expect(",");
        ExprPtr rhs = parse_expr();
        // if (lhs.type().is_bool())
        // {
        //     rhs = reparse_as_bool(rhs);
        // }
        // if (rhs.type().is_bool())
        // {
        //     lhs = reparse_as_bool(lhs);
        // }
        // Expr predicate = Halide::Internal::const_true();
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
        return NumericType::INVALID;
    }

    std::tuple<bool, std::vector<NumericType>> parse_types()
    {
        bool allowed = true;
        std::vector<NumericType> types;

        if (consume("!"))
        {
            allowed = false;
            expect("(");
        }

        // is there a more efficient way to do this?
        types.push_back(parse_type());
        while (consume(","))
        {
            NumericType t = parse_type();
            if (t != NumericType::INVALID)
            {
                types.push_back(t);
            }
        }

        if (!allowed)
        {
            expect(")");
        }
        else
        {
            // TODO I don't like this
            // Oops we consumed an extra comma, add it back
            *(cursor)--;
        }

        return std::tuple<bool, std::vector<NumericType>>(allowed, types);
    }

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
                std::tuple<bool, std::vector<NumericType>> types_tuple = parse_types();

                for (const auto rule : inner_rules)
                {
                    if (std::get<0>(types_tuple))
                    { // these are allowed types
                        rule->set_allowed_types(std::get<1>(types_tuple));
                    }
                    else
                    {
                        rule->set_disallowed_types(std::get<1>(types_tuple));
                    }
                    rules.push_back(rule);
                }
            }
            else
            {
                Rule *r(parse_r()); // TODO I need a lot of error checking oops
                if (consume("|-"))
                {
                    // TODO this could be more modular

                    std::tuple<bool, std::vector<NumericType>> types_tuple = parse_types();
                    bool allowed = std::get<0>(types_tuple);
                    std::vector<NumericType> types = std::get<1>(types_tuple);
                    if (allowed)
                    { // these are allowed types
                        r->set_allowed_types(types);
                    }
                    else
                    {
                        r->set_disallowed_types(types);
                    }
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

// int main(int argc, char *argv[]) {
//     if (argc != 2) {
//         std::cout << "Usage: ./bin/Parser <input filename>\n";
//         return 1;
//     }
//     std::string filename = argv[1];
//     std::vector<Rule *> rules = parse_rules_from_file(filename);
//     return 0;
// }