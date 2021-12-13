#pragma once

#include <memory>

namespace CFIR {

struct Node;

std::shared_ptr<Node> do_reuse_analysis(const std::shared_ptr<Node> &root);

}  // namespace CFIR
