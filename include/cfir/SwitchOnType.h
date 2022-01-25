#pragma once

#include <memory>

namespace CFIR {

struct Node;

std::shared_ptr<Node> switch_on_type(const std::shared_ptr<Node> &root);

}  // namespace CFIR
