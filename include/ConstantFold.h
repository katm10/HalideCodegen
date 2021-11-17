#pragma once
#include "Halide.h"
#include <iostream>

void recursive_fold(const Halide::Expr &expr, halide_scalar_value_t &val, halide_type_t &ty);