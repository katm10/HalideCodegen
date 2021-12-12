#ifndef TRS_CODEGEN_PARSER_H
#define TRS_CODEGEN_PARSER_H

#include <string>

#include "AST.h"
#include "Rule.h"

// Helper routines for writing a parser and routines for parsing
// Halide rewrite rules.

// Print an error and the remaining chars to be parsed, then abort.
void report_error(const char **cursor, const char *debug_info);

// Move the input cursor past any whitespace, but not beyond the end
// pointer.
void consume_whitespace(const char **cursor, const char *end);

// If the input cursor starts with the expected string, update it to
// point to the end of the string and return true. Otherwise, return
// false and don't modify the input cursor.
bool consume(const char **cursor, const char *end, const char *expected);

// Calls consume and asserts that it succeeded.
void expect(const char **cursor, const char *end, const char *pattern);

// Returns if the input cursor starts with the expected string.
// Will not move the cursor regardless of the result.
bool check(const char **cursor, const char *end, const char *pattern);

// Consume and return a legal Halide identifier.
std::string consume_token(const char **cursor, const char *end);

// Consume and return a legal Halide variable identifier.
std::string consume_name(const char **cursor, const char *end);

// Consume and return an operator token.
std::string consume_op(const char **cursor, const char *end);

// Consume and return a constant integer.
int64_t consume_int(const char **cursor, const char *end);

// Parse a list of Halide rewrite rules.
std::vector<Rule *> parse_rules_from_file(const std::string &filename);
#endif