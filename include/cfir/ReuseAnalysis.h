#pragma once

#include <memory>

namespace CFIR {

struct Node;

struct ReuseResult {
    std::shared_ptr<Node> node = nullptr;
    size_t n_declarations = 0;
};

ReuseResult do_reuse_analysis(std::shared_ptr<Node> &root);

}  // namespace CFIR
