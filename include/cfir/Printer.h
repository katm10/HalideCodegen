#pragma once

#include <iostream>
#include <map>
#include <string>
#include "ast/Types.h"
#include "Identifier.h"


// std::string make_type_checker_condition(const std::string &var_name, const std::string &type_name, const std::string &output_name);
void print_type_checker_condition(std::ostream &stream, const IdPtr &current_id, const std::string &type_name, const IdPtr &output_id);

IdPtr make_new_unique_name();
