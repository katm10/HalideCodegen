#pragma once

#include <string>
#include <map>
#include "AST.h"

std::string make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name);
std::string make_new_unique_name();
std::string build_expr(const AST::ExprPtr &expr, const VarScope &scope);
