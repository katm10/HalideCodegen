#include "Expr.h"
#include "Type.h"
#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"

namespace Halide {
namespace Internal {
namespace CodeGen {
Expr Simplify_Add(const Add *expr, Simplify *simplifier) {
  if (is_const_int(expr->b, 0)) {
    return expr->a;
  }
  if (is_const_int(expr->a, 0)) {
    return expr->b;
  }
  if (is_const(expr->a)) {
    if (is_const(expr->b)) {
      return fold((expr->a + expr->b));
    }
  }
  if (equal(expr->a, expr->b)) {
    return (expr->a * 2);
  }
  if (const Ramp *a2 = expr->a.as<Ramp>()) {
    if (is_const(a2->lanes)) {
      if (const Ramp *a3 = expr->b.as<Ramp>()) {
        if (equal(a2->lanes, a3->lanes)) {
          return ramp((a2->base + a3->base), (a2->stride + a3->stride), a2->lanes);
        }
      }
      if (const Broadcast *a5 = expr->b.as<Broadcast>()) {
        if (equal(a2->lanes, a5->lanes)) {
          return ramp((a2->base + a5->value), a2->stride, a2->lanes);
        }
      }
    }
    if (const Broadcast *a45 = a2->base.as<Broadcast>()) {
      if (is_const(a45->lanes)) {
        if (is_const(a2->lanes)) {
          if (const Broadcast *a46 = expr->b.as<Broadcast>()) {
            if (is_const(a46->lanes)) {
              if (evaluate_predicate(fold((a46->lanes == (a45->lanes * a2->lanes))))) {
                return ramp(broadcast((a45->value + a46->value), a45->lanes), a2->stride, a2->lanes);
              }
            }
          }
        }
      }
    }
    if (const Ramp *a48 = a2->base.as<Ramp>()) {
      if (is_const(a48->lanes)) {
        if (is_const(a2->lanes)) {
          if (const Broadcast *a49 = expr->b.as<Broadcast>()) {
            if (is_const(a49->lanes)) {
              if (evaluate_predicate(fold((a49->lanes == (a48->lanes * a2->lanes))))) {
                return ramp(ramp((a48->base + a49->value), a48->stride, a48->lanes), a2->stride, a2->lanes);
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a6 = expr->a.as<Broadcast>()) {
    if (is_const(a6->lanes)) {
      if (const Broadcast *a7 = expr->b.as<Broadcast>()) {
        if (is_const(a7->lanes)) {
          if (evaluate_predicate(fold(((a7->lanes % a6->lanes) == 0)))) {
            return broadcast((a6->value + broadcast(a7->value, fold((a7->lanes / a6->lanes)))), a6->lanes);
          }
          if (evaluate_predicate(fold(((a6->lanes % a7->lanes) == 0)))) {
            return broadcast((a7->value + broadcast(a6->value, fold((a6->lanes / a7->lanes)))), a7->lanes);
          }
        }
      }
    }
  }
  if (const Add *a10 = expr->a.as<Add>()) {
    if (const Broadcast *a11 = a10->b.as<Broadcast>()) {
      if (is_const(a11->lanes)) {
        if (const Broadcast *a12 = expr->b.as<Broadcast>()) {
          if (is_const(a12->lanes)) {
            if (evaluate_predicate(fold(((a12->lanes % a11->lanes) == 0)))) {
              return (a10->a + broadcast((a11->value + broadcast(a12->value, fold((a12->lanes / a11->lanes)))), a11->lanes));
            }
            if (evaluate_predicate(fold(((a11->lanes % a12->lanes) == 0)))) {
              return (a10->a + broadcast((a12->value + broadcast(a11->value, fold((a11->lanes / a12->lanes)))), a12->lanes));
            }
          }
        }
      }
    }
    if (const Broadcast *a17 = a10->a.as<Broadcast>()) {
      if (is_const(a17->lanes)) {
        if (const Broadcast *a18 = expr->b.as<Broadcast>()) {
          if (is_const(a18->lanes)) {
            if (evaluate_predicate(fold(((a18->lanes % a17->lanes) == 0)))) {
              return (a10->b + broadcast((a17->value + broadcast(a18->value, fold((a18->lanes / a17->lanes)))), a17->lanes));
            }
            if (evaluate_predicate(fold(((a17->lanes % a18->lanes) == 0)))) {
              return (a10->b + broadcast((a18->value + broadcast(a17->value, fold((a17->lanes / a18->lanes)))), a18->lanes));
            }
          }
        }
      }
    }
    if (is_const(a10->b)) {
      if (is_const(expr->b)) {
        return (a10->a + fold((a10->b + expr->b)));
      }
      return ((a10->a + expr->b) + a10->b);
    }
    if (const Sub *a89 = a10->a.as<Sub>()) {
      if (equal(a89->b, expr->b)) {
        return (a89->a + a10->b);
      }
    }
    if (const Sub *a91 = a10->b.as<Sub>()) {
      if (equal(a91->b, expr->b)) {
        return (a10->a + a91->a);
      }
    }
  }
  if (const Sub *a22 = expr->a.as<Sub>()) {
    if (const Broadcast *a23 = a22->b.as<Broadcast>()) {
      if (is_const(a23->lanes)) {
        if (const Broadcast *a24 = expr->b.as<Broadcast>()) {
          if (is_const(a24->lanes)) {
            if (evaluate_predicate(fold(((a24->lanes % a23->lanes) == 0)))) {
              return (a22->a + broadcast((broadcast(a24->value, fold((a24->lanes / a23->lanes))) - a23->value), a23->lanes));
            }
            if (evaluate_predicate(fold(((a23->lanes % a24->lanes) == 0)))) {
              return (a22->a + broadcast((a24->value - broadcast(a23->value, fold((a23->lanes / a24->lanes)))), a24->lanes));
            }
          }
        }
      }
    }
    if (const Broadcast *a29 = a22->a.as<Broadcast>()) {
      if (is_const(a29->lanes)) {
        if (const Broadcast *a30 = expr->b.as<Broadcast>()) {
          if (is_const(a30->lanes)) {
            if (evaluate_predicate(fold(((a30->lanes % a29->lanes) == 0)))) {
              return (broadcast((a29->value + broadcast(a30->value, fold((a30->lanes / a29->lanes)))), a29->lanes) - a22->b);
            }
            if (evaluate_predicate(fold(((a29->lanes % a30->lanes) == 0)))) {
              return (broadcast((a30->value + broadcast(a29->value, fold((a29->lanes / a30->lanes)))), a30->lanes) - a22->b);
            }
          }
        }
      }
    }
    if (is_const(a22->a)) {
      if (is_const(expr->b)) {
        return (fold((a22->a + expr->b)) - a22->b);
      }
      return ((expr->b - a22->b) + a22->a);
    }
    if (equal(a22->b, expr->b)) {
      return a22->a;
    }
    if (const Sub *a98 = expr->b.as<Sub>()) {
      if (equal(a22->b, a98->a)) {
        return (a22->a - a98->b);
      }
      if (equal(a22->a, a98->b)) {
        return (a98->a - a22->b);
      }
    }
    if (const Add *a102 = expr->b.as<Add>()) {
      if (equal(a22->b, a102->a)) {
        return (a22->a + a102->b);
      }
      if (equal(a22->b, a102->b)) {
        return (a22->a + a102->a);
      }
    }
    if (const Sub *a108 = a22->a.as<Sub>()) {
      if (equal(a108->b, expr->b)) {
        return (a108->a - a22->b);
      }
      if (is_const_int(a108->a, 0)) {
        return (expr->b - (a108->b + a22->b));
      }
      if (is_const(a108->a)) {
        if (is_const(expr->b)) {
          return ((fold((a108->a + expr->b)) - a22->b) - a108->b);
        }
      }
    }
    if (const Add *a114 = a22->b.as<Add>()) {
      if (equal(a114->a, expr->b)) {
        return (a22->a - a114->b);
      }
      if (equal(a114->b, expr->b)) {
        return (a22->a - a114->a);
      }
    }
  }
  if (const Select *a34 = expr->a.as<Select>()) {
    if (const Select *a35 = expr->b.as<Select>()) {
      if (equal(a34->condition, a35->condition)) {
        return select(a34->condition, (a34->true_value + a35->true_value), (a34->false_value + a35->false_value));
      }
    }
    if (is_const(a34->true_value)) {
      if (is_const(a34->false_value)) {
        if (is_const(expr->b)) {
          return select(a34->condition, fold((a34->true_value + expr->b)), fold((a34->false_value + expr->b)));
        }
      }
      if (const Add *a40 = a34->false_value.as<Add>()) {
        if (is_const(a40->b)) {
          if (is_const(expr->b)) {
            return select(a34->condition, fold((a34->true_value + expr->b)), (a40->a + fold((a40->b + expr->b))));
          }
        }
      }
    }
    if (const Add *a38 = a34->true_value.as<Add>()) {
      if (is_const(a38->b)) {
        if (is_const(a34->false_value)) {
          if (is_const(expr->b)) {
            return select(a34->condition, (a38->a + fold((a38->b + expr->b))), fold((a34->false_value + expr->b)));
          }
        }
        if (const Add *a43 = a34->false_value.as<Add>()) {
          if (is_const(a43->b)) {
            if (is_const(expr->b)) {
              return select(a34->condition, (a38->a + fold((a38->b + expr->b))), (a43->a + fold((a43->b + expr->b))));
            }
          }
        }
      }
    }
    if (const Add *a51 = expr->b.as<Add>()) {
      if (const Select *a52 = a51->a.as<Select>()) {
        if (equal(a34->condition, a52->condition)) {
          return (select(a34->condition, (a34->true_value + a52->true_value), (a34->false_value + a52->false_value)) + a51->b);
        }
      }
      if (const Select *a55 = a51->b.as<Select>()) {
        if (equal(a34->condition, a55->condition)) {
          return (select(a34->condition, (a34->true_value + a55->true_value), (a34->false_value + a55->false_value)) + a51->a);
        }
      }
    }
    if (const Sub *a57 = expr->b.as<Sub>()) {
      if (const Select *a58 = a57->a.as<Select>()) {
        if (equal(a34->condition, a58->condition)) {
          return (select(a34->condition, (a34->true_value + a58->true_value), (a34->false_value + a58->false_value)) - a57->b);
        }
      }
      if (const Select *a61 = a57->b.as<Select>()) {
        if (equal(a34->condition, a61->condition)) {
          return (select(a34->condition, (a34->true_value - a61->true_value), (a34->false_value - a61->false_value)) + a57->a);
        }
      }
    }
    if (const Sub *a63 = a34->true_value.as<Sub>()) {
      if (is_const(a63->a)) {
        if (is_const(a34->false_value)) {
          if (is_const(expr->b)) {
            return select(a34->condition, (fold((a63->a + expr->b)) - a63->b), fold((a34->false_value + expr->b)));
            return (fold((a63->a + expr->b)) - select(a34->condition, a63->b, fold((a63->a - a34->false_value))));
          }
        }
      }
    }
    if (const Add *a65 = a34->false_value.as<Add>()) {
      if (is_const(a65->b)) {
        if (is_const(expr->b)) {
          if (evaluate_predicate(fold(((a65->b + expr->b) == 0)))) {
            return select(a34->condition, (a34->true_value + expr->b), a65->a);
          }
        }
      }
    }
  }
  if (const Mul *a68 = expr->b.as<Mul>()) {
    if (const Sub *a69 = a68->b.as<Sub>()) {
      if (is_const_int(a69->a, 0)) {
        if (is_const_int(a69->b, 1)) {
          return (expr->a - a68->a);
        }
      }
    }
  }
  if (const Mul *a72 = expr->a.as<Mul>()) {
    if (const Sub *a73 = a72->b.as<Sub>()) {
      if (is_const_int(a73->a, 0)) {
        if (is_const_int(a73->b, 1)) {
          return (expr->b - a72->a);
        }
      }
    }
    if (const Mul *a126 = expr->b.as<Mul>()) {
      if (equal(a72->b, a126->b)) {
        return ((a72->a + a126->a) * a72->b);
      }
      if (equal(a72->b, a126->a)) {
        return ((a72->a + a126->b) * a72->b);
      }
      if (equal(a72->a, a126->b)) {
        return (a72->a * (a72->b + a126->a));
      }
      if (equal(a72->a, a126->a)) {
        return (a72->a * (a72->b + a126->b));
      }
    }
    if (is_const(a72->b)) {
      if (const Mul *a134 = expr->b.as<Mul>()) {
        if (is_const(a134->b)) {
          if (evaluate_predicate(fold(((a134->b % a72->b) == 0)))) {
            return ((a72->a + (a134->a * fold((a134->b / a72->b)))) * a72->b);
          }
          if (evaluate_predicate(fold(((a72->b % a134->b) == 0)))) {
            return (((a72->a * fold((a72->b / a134->b))) + a134->a) * a134->b);
          }
        }
      }
    }
  }
  if (const Add *a78 = expr->b.as<Add>()) {
    if (is_const(a78->b)) {
      return ((expr->a + a78->a) + a78->b);
    }
    if (const Sub *a93 = a78->a.as<Sub>()) {
      if (equal(expr->a, a93->b)) {
        return (a93->a + a78->b);
      }
    }
    if (const Sub *a95 = a78->b.as<Sub>()) {
      if (equal(expr->a, a95->b)) {
        return (a78->a + a95->a);
      }
    }
  }
  if (const Max *a81 = expr->a.as<Max>()) {
    if (const Add *a82 = a81->b.as<Add>()) {
      if (const Mul *a83 = a82->a.as<Mul>()) {
        if (is_const(a83->b)) {
          if (const Mul *a84 = expr->b.as<Mul>()) {
            if (const Sub *a85 = a84->a.as<Sub>()) {
              if (equal(a83->a, a85->b)) {
                if (equal(a83->b, a84->b)) {
                  return (max((a81->a - (a83->a * a83->b)), a82->b) + (a85->a * a83->b));
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Sub *a87 = expr->b.as<Sub>()) {
    if (equal(expr->a, a87->b)) {
      return a87->a;
    }
    if (is_const(a87->a)) {
      return ((expr->a - a87->b) + a87->a);
    }
    if (const Sub *a106 = a87->a.as<Sub>()) {
      if (equal(expr->a, a106->b)) {
        return (a106->a - a87->b);
      }
      if (is_const_int(a106->a, 0)) {
        return (expr->a - (a106->b + a87->b));
      }
    }
    if (const Add *a110 = a87->b.as<Add>()) {
      if (equal(expr->a, a110->a)) {
        return (a87->a - a110->b);
      }
      if (equal(expr->a, a110->b)) {
        return (a87->a - a110->a);
      }
    }
  }
  if (is_no_overflow(expr)) {
    if (const Mul *a137 = expr->b.as<Mul>()) {
      if (equal(expr->a, a137->a)) {
        return (expr->a * (a137->b + 1));
      }
      if (equal(expr->a, a137->b)) {
        return ((a137->a + 1) * expr->a);
      }
    }
    if (const Mul *a139 = expr->a.as<Mul>()) {
      if (equal(a139->a, expr->b)) {
        return (a139->a * (a139->b + 1));
      }
      if (equal(a139->b, expr->b)) {
        if (evaluate_predicate(fold(!(is_const(a139->b))))) {
          return ((a139->a + 1) * a139->b);
        }
      }
    }
    if (const Div *a141 = expr->a.as<Div>()) {
      if (const Add *a142 = a141->a.as<Add>()) {
        if (is_const(a142->b)) {
          if (is_const(a141->b)) {
            if (is_const(expr->b)) {
              if (evaluate_predicate(fold((a141->b != 0)))) {
                return ((a142->a + fold((a142->b + (a141->b * expr->b)))) / a141->b);
              }
            }
          }
        }
        if (is_const(a141->b)) {
          if (equal(a142->a, expr->b)) {
            if (evaluate_predicate(fold((a141->b != 0)))) {
              return (((fold((a141->b + 1)) * a142->a) + a142->b) / a141->b);
            }
          }
          if (equal(a142->b, expr->b)) {
            if (evaluate_predicate(fold((a141->b != 0)))) {
              return ((a142->a + (fold((a141->b + 1)) * a142->b)) / a141->b);
            }
          }
        }
      }
      if (const Sub *a150 = a141->a.as<Sub>()) {
        if (is_const(a150->a)) {
          if (is_const(a141->b)) {
            if (is_const(expr->b)) {
              if (evaluate_predicate(fold(((a150->a != 0) && (a141->b != 0))))) {
                return ((fold((a150->a + (a141->b * expr->b))) - a150->b) / a141->b);
              }
            }
          }
        }
        if (is_const(a141->b)) {
          if (equal(a150->a, expr->b)) {
            if (evaluate_predicate(fold((a141->b != 0)))) {
              return (((fold((a141->b + 1)) * a150->a) - a150->b) / a141->b);
            }
          }
          if (equal(a150->b, expr->b)) {
            if (evaluate_predicate(fold((a141->b != 0)))) {
              return ((a150->a + (fold((a141->b - 1)) * a150->b)) / a141->b);
            }
          }
        }
      }
    }
    if (const Add *a143 = expr->a.as<Add>()) {
      if (const Div *a144 = a143->b.as<Div>()) {
        if (const Add *a145 = a144->a.as<Add>()) {
          if (is_const(a145->b)) {
            if (is_const(a144->b)) {
              if (is_const(expr->b)) {
                if (evaluate_predicate(fold((a144->b != 0)))) {
                  return (a143->a + ((a145->a + fold((a145->b + (a144->b * expr->b)))) / a144->b));
                }
              }
            }
          }
        }
      }
      if (const Div *a147 = a143->a.as<Div>()) {
        if (const Add *a148 = a147->a.as<Add>()) {
          if (is_const(a148->b)) {
            if (is_const(a147->b)) {
              if (is_const(expr->b)) {
                if (evaluate_predicate(fold((a147->b != 0)))) {
                  return (a143->b + ((a148->a + fold((a148->b + (a147->b * expr->b)))) / a147->b));
                }
              }
            }
          }
        }
      }
    }
    if (const Div *a151 = expr->b.as<Div>()) {
      if (const Add *a152 = a151->a.as<Add>()) {
        if (equal(expr->a, a152->a)) {
          if (is_const(a151->b)) {
            if (evaluate_predicate(fold((a151->b != 0)))) {
              return (((fold((a151->b + 1)) * expr->a) + a152->b) / a151->b);
            }
          }
        }
        if (equal(expr->a, a152->b)) {
          if (is_const(a151->b)) {
            if (evaluate_predicate(fold((a151->b != 0)))) {
              return (((fold((a151->b + 1)) * expr->a) + a152->a) / a151->b);
            }
          }
        }
      }
      if (const Sub *a156 = a151->a.as<Sub>()) {
        if (equal(expr->a, a156->b)) {
          if (is_const(a151->b)) {
            if (evaluate_predicate(fold((a151->b != 0)))) {
              return (((fold((a151->b - 1)) * expr->a) + a156->a) / a151->b);
            }
          }
        }
        if (equal(expr->a, a156->a)) {
          if (is_const(a151->b)) {
            if (evaluate_predicate(fold((a151->b != 0)))) {
              return (((fold((a151->b + 1)) * expr->a) - a156->b) / a151->b);
            }
          }
        }
      }
    }
    if (const Min *a167 = expr->a.as<Min>()) {
      if (const Sub *a168 = a167->b.as<Sub>()) {
        if (equal(a168->b, expr->b)) {
          return min((a167->a + a168->b), a168->a);
        }
      }
      if (const Sub *a170 = a167->a.as<Sub>()) {
        if (equal(a170->b, expr->b)) {
          return min(a170->a, (a167->b + a170->b));
        }
      }
      if (const Add *a172 = a167->b.as<Add>()) {
        if (is_const(a172->b)) {
          if (is_const(expr->b)) {
            if (evaluate_predicate(fold(((a172->b + expr->b) == 0)))) {
              return min((a167->a + expr->b), a172->a);
            }
          }
        }
        if (const Mul *a197 = a172->b.as<Mul>()) {
          if (is_const(a197->b)) {
            if (const Mul *a198 = expr->b.as<Mul>()) {
              if (equal(a197->a, a198->a)) {
                if (is_const(a198->b)) {
                  if (evaluate_predicate(fold(((a197->b + a198->b) == 0)))) {
                    return min((a167->a + (a197->a * a198->b)), a172->a);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a201 = a172->a.as<Mul>()) {
          if (is_const(a201->b)) {
            if (const Mul *a202 = expr->b.as<Mul>()) {
              if (equal(a201->a, a202->a)) {
                if (is_const(a202->b)) {
                  if (evaluate_predicate(fold(((a201->b + a202->b) == 0)))) {
                    return min((a167->a + (a201->a * a202->b)), a172->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a174 = a167->a.as<Add>()) {
        if (is_const(a174->b)) {
          if (is_const(expr->b)) {
            if (evaluate_predicate(fold(((a174->b + expr->b) == 0)))) {
              return min(a174->a, (a167->b + expr->b));
            }
          }
        }
        if (const Mul *a208 = a174->b.as<Mul>()) {
          if (is_const(a208->b)) {
            if (const Mul *a209 = expr->b.as<Mul>()) {
              if (equal(a208->a, a209->a)) {
                if (is_const(a209->b)) {
                  if (evaluate_predicate(fold(((a208->b + a209->b) == 0)))) {
                    return min(((a208->a * a209->b) + a167->b), a174->a);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a212 = a174->a.as<Mul>()) {
          if (is_const(a212->b)) {
            if (const Mul *a213 = expr->b.as<Mul>()) {
              if (equal(a212->a, a213->a)) {
                if (is_const(a213->b)) {
                  if (evaluate_predicate(fold(((a212->b + a213->b) == 0)))) {
                    return min(a174->b, ((a212->a * a213->b) + a167->b));
                  }
                }
              }
            }
          }
        }
      }
      if (const Mul *a204 = a167->b.as<Mul>()) {
        if (is_const(a204->b)) {
          if (const Mul *a205 = expr->b.as<Mul>()) {
            if (equal(a204->a, a205->a)) {
              if (is_const(a205->b)) {
                if (evaluate_predicate(fold(((a204->b + a205->b) == 0)))) {
                  return min((a167->a + (a204->a * a205->b)), 0);
                }
              }
            }
          }
        }
      }
      if (const Mul *a215 = a167->a.as<Mul>()) {
        if (is_const(a215->b)) {
          if (const Mul *a216 = expr->b.as<Mul>()) {
            if (equal(a215->a, a216->a)) {
              if (is_const(a216->b)) {
                if (evaluate_predicate(fold(((a215->b + a216->b) == 0)))) {
                  return min(((a215->a * a216->b) + a167->b), 0);
                }
              }
            }
          }
        }
      }
    }
    if (const Min *a175 = expr->b.as<Min>()) {
      if (const Sub *a176 = a175->b.as<Sub>()) {
        if (equal(expr->a, a176->b)) {
          return min((expr->a + a175->a), a176->a);
        }
      }
      if (const Sub *a178 = a175->a.as<Sub>()) {
        if (equal(expr->a, a178->b)) {
          return min(a178->a, (expr->a + a175->b));
        }
      }
    }
    if (const Max *a179 = expr->b.as<Max>()) {
      if (const Sub *a180 = a179->b.as<Sub>()) {
        if (equal(expr->a, a180->b)) {
          return max((expr->a + a179->a), a180->a);
        }
      }
      if (const Sub *a182 = a179->a.as<Sub>()) {
        if (equal(expr->a, a182->b)) {
          return max(a182->a, (expr->a + a179->b));
        }
      }
    }
    if (const Max *a183 = expr->a.as<Max>()) {
      if (const Sub *a184 = a183->b.as<Sub>()) {
        if (equal(a184->b, expr->b)) {
          return max((a183->a + a184->b), a184->a);
        }
      }
      if (const Sub *a186 = a183->a.as<Sub>()) {
        if (equal(a186->b, expr->b)) {
          return max(a186->a, (a183->b + a186->b));
        }
      }
      if (const Add *a188 = a183->b.as<Add>()) {
        if (is_const(a188->b)) {
          if (is_const(expr->b)) {
            if (evaluate_predicate(fold(((a188->b + expr->b) == 0)))) {
              return max((a183->a + expr->b), a188->a);
            }
          }
        }
        if (const Mul *a219 = a188->b.as<Mul>()) {
          if (is_const(a219->b)) {
            if (const Mul *a220 = expr->b.as<Mul>()) {
              if (equal(a219->a, a220->a)) {
                if (is_const(a220->b)) {
                  if (evaluate_predicate(fold(((a219->b + a220->b) == 0)))) {
                    return max((a183->a + (a219->a * a220->b)), a188->a);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a223 = a188->a.as<Mul>()) {
          if (is_const(a223->b)) {
            if (const Mul *a224 = expr->b.as<Mul>()) {
              if (equal(a223->a, a224->a)) {
                if (is_const(a224->b)) {
                  if (evaluate_predicate(fold(((a223->b + a224->b) == 0)))) {
                    return max((a183->a + (a223->a * a224->b)), a188->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a190 = a183->a.as<Add>()) {
        if (is_const(a190->b)) {
          if (is_const(expr->b)) {
            if (evaluate_predicate(fold(((a190->b + expr->b) == 0)))) {
              return max(a190->a, (a183->b + expr->b));
            }
          }
        }
        if (const Mul *a230 = a190->b.as<Mul>()) {
          if (is_const(a230->b)) {
            if (const Mul *a231 = expr->b.as<Mul>()) {
              if (equal(a230->a, a231->a)) {
                if (is_const(a231->b)) {
                  if (evaluate_predicate(fold(((a230->b + a231->b) == 0)))) {
                    return max(a190->a, ((a230->a * a231->b) + a183->b));
                  }
                }
              }
            }
          }
        }
        if (const Mul *a234 = a190->a.as<Mul>()) {
          if (is_const(a234->b)) {
            if (const Mul *a235 = expr->b.as<Mul>()) {
              if (equal(a234->a, a235->a)) {
                if (is_const(a235->b)) {
                  if (evaluate_predicate(fold(((a234->b + a235->b) == 0)))) {
                    return max(((a234->a * a235->b) + a183->b), a190->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a192 = expr->b.as<Min>()) {
        if (equal(a183->a, a192->a)) {
          if (equal(a183->b, a192->b)) {
            return (a183->a + a183->b);
          }
        }
        if (equal(a183->b, a192->a)) {
          if (equal(a183->a, a192->b)) {
            return (a183->a + a183->b);
          }
        }
      }
      if (const Mul *a226 = a183->b.as<Mul>()) {
        if (is_const(a226->b)) {
          if (const Mul *a227 = expr->b.as<Mul>()) {
            if (equal(a226->a, a227->a)) {
              if (is_const(a227->b)) {
                if (evaluate_predicate(fold(((a226->b + a227->b) == 0)))) {
                  return max((a183->a + (a226->a * a227->b)), 0);
                }
              }
            }
          }
        }
      }
      if (const Mul *a237 = a183->a.as<Mul>()) {
        if (is_const(a237->b)) {
          if (const Mul *a238 = expr->b.as<Mul>()) {
            if (equal(a237->a, a238->a)) {
              if (is_const(a238->b)) {
                if (evaluate_predicate(fold(((a237->b + a238->b) == 0)))) {
                  return max(((a237->a * a238->b) + a183->b), 0);
                }
              }
            }
          }
        }
      }
    }
  }
  if (is_no_overflow_int(expr)) {
    if (const Mul *a239 = expr->a.as<Mul>()) {
      if (const Div *a240 = a239->b.as<Div>()) {
        if (equal(a239->a, a240->b)) {
          if (const Mod *a241 = expr->b.as<Mod>()) {
            if (equal(a240->a, a241->a)) {
              if (equal(a239->a, a241->b)) {
                return select((a239->a == 0), 0, a240->a);
              }
            }
          }
          if (const Add *a287 = expr->b.as<Add>()) {
            if (const Mod *a288 = a287->a.as<Mod>()) {
              if (equal(a240->a, a288->a)) {
                if (equal(a239->a, a288->b)) {
                  return (select((a239->a == 0), 0, a240->a) + a287->b);
                }
              }
            }
            if (const Mod *a304 = a287->b.as<Mod>()) {
              if (equal(a240->a, a304->a)) {
                if (equal(a239->a, a304->b)) {
                  return (select((a239->a == 0), 0, a240->a) + a287->a);
                }
              }
            }
          }
          if (const Sub *a295 = expr->b.as<Sub>()) {
            if (const Mod *a296 = a295->a.as<Mod>()) {
              if (equal(a240->a, a296->a)) {
                if (equal(a239->a, a296->b)) {
                  return (select((a239->a == 0), 0, a240->a) - a295->b);
                }
              }
            }
          }
        }
      }
      if (const Div *a243 = a239->a.as<Div>()) {
        if (equal(a243->b, a239->b)) {
          if (const Mod *a244 = expr->b.as<Mod>()) {
            if (equal(a243->a, a244->a)) {
              if (equal(a243->b, a244->b)) {
                return select((a243->b == 0), 0, a243->a);
              }
            }
          }
          if (const Add *a291 = expr->b.as<Add>()) {
            if (const Mod *a292 = a291->a.as<Mod>()) {
              if (equal(a243->a, a292->a)) {
                if (equal(a243->b, a292->b)) {
                  return (select((a243->b == 0), 0, a243->a) + a291->b);
                }
              }
            }
            if (const Mod *a308 = a291->b.as<Mod>()) {
              if (equal(a243->a, a308->a)) {
                if (equal(a243->b, a308->b)) {
                  return (select((a243->b == 0), 0, a243->a) + a291->a);
                }
              }
            }
          }
          if (const Sub *a299 = expr->b.as<Sub>()) {
            if (const Mod *a300 = a299->a.as<Mod>()) {
              if (equal(a243->a, a300->a)) {
                if (equal(a243->b, a300->b)) {
                  return (select((a243->b == 0), 0, a243->a) - a299->b);
                }
              }
            }
          }
        }
      }
      if (const Add *a246 = a239->b.as<Add>()) {
        if (const Div *a247 = a246->b.as<Div>()) {
          if (equal(a239->a, a247->b)) {
            if (const Mod *a248 = expr->b.as<Mod>()) {
              if (equal(a247->a, a248->a)) {
                if (equal(a239->a, a248->b)) {
                  return select((a239->a == 0), 0, ((a246->a * a239->a) + a247->a));
                }
              }
            }
          }
        }
        if (const Div *a255 = a246->a.as<Div>()) {
          if (equal(a239->a, a255->b)) {
            if (const Mod *a256 = expr->b.as<Mod>()) {
              if (equal(a255->a, a256->a)) {
                if (equal(a239->a, a256->b)) {
                  return select((a239->a == 0), 0, (a255->a + (a246->b * a239->a)));
                }
              }
            }
          }
        }
      }
      if (const Add *a250 = a239->a.as<Add>()) {
        if (const Div *a251 = a250->b.as<Div>()) {
          if (equal(a251->b, a239->b)) {
            if (const Mod *a252 = expr->b.as<Mod>()) {
              if (equal(a251->a, a252->a)) {
                if (equal(a251->b, a252->b)) {
                  return select((a251->b == 0), 0, ((a250->a * a251->b) + a251->a));
                }
              }
            }
          }
        }
        if (const Div *a259 = a250->a.as<Div>()) {
          if (equal(a259->b, a239->b)) {
            if (const Mod *a260 = expr->b.as<Mod>()) {
              if (equal(a259->a, a260->a)) {
                if (equal(a259->b, a260->b)) {
                  return select((a259->b == 0), 0, (a259->a + (a250->b * a259->b)));
                }
              }
            }
          }
        }
      }
    }
    if (const Mod *a261 = expr->a.as<Mod>()) {
      if (const Add *a262 = expr->b.as<Add>()) {
        if (const Mul *a263 = a262->a.as<Mul>()) {
          if (equal(a261->b, a263->a)) {
            if (const Div *a264 = a263->b.as<Div>()) {
              if (equal(a261->a, a264->a)) {
                if (equal(a261->b, a264->b)) {
                  return (select((a261->b == 0), 0, a261->a) + a262->b);
                }
              }
            }
          }
          if (const Div *a268 = a263->a.as<Div>()) {
            if (equal(a261->a, a268->a)) {
              if (equal(a261->b, a268->b)) {
                if (equal(a261->b, a263->b)) {
                  return (select((a261->b == 0), 0, a261->a) + a262->b);
                }
              }
            }
          }
        }
        if (const Mul *a279 = a262->b.as<Mul>()) {
          if (equal(a261->b, a279->a)) {
            if (const Div *a280 = a279->b.as<Div>()) {
              if (equal(a261->a, a280->a)) {
                if (equal(a261->b, a280->b)) {
                  return (select((a261->b == 0), 0, a261->a) + a262->a);
                }
              }
            }
          }
          if (const Div *a284 = a279->a.as<Div>()) {
            if (equal(a261->a, a284->a)) {
              if (equal(a261->b, a284->b)) {
                if (equal(a261->b, a279->b)) {
                  return (select((a261->b == 0), 0, a261->a) + a262->a);
                }
              }
            }
          }
        }
      }
      if (const Sub *a270 = expr->b.as<Sub>()) {
        if (const Mul *a271 = a270->a.as<Mul>()) {
          if (equal(a261->b, a271->a)) {
            if (const Div *a272 = a271->b.as<Div>()) {
              if (equal(a261->a, a272->a)) {
                if (equal(a261->b, a272->b)) {
                  return (select((a261->b == 0), 0, a261->a) - a270->b);
                }
              }
            }
          }
          if (const Div *a276 = a271->a.as<Div>()) {
            if (equal(a261->a, a276->a)) {
              if (equal(a261->b, a276->b)) {
                if (equal(a261->b, a271->b)) {
                  return (select((a261->b == 0), 0, a261->a) - a270->b);
                }
              }
            }
          }
        }
      }
    }
    if (const Div *a309 = expr->a.as<Div>()) {
      if (is_const_int(a309->b, 2)) {
        if (const Mod *a311 = expr->b.as<Mod>()) {
          if (equal(a309->a, a311->a)) {
            if (is_const_int(a311->b, 2)) {
              return ((a309->a + 1) / 2);
            }
          }
        }
      }
    }
    if (const Mul *a313 = expr->b.as<Mul>()) {
      if (const Div *a314 = a313->a.as<Div>()) {
        if (const Sub *a315 = a314->a.as<Sub>()) {
          if (is_const(a315->a)) {
            if (equal(expr->a, a315->b)) {
              if (is_const(a314->b)) {
                if (equal(a314->b, a313->b)) {
                  if (evaluate_predicate(fold((a314->b > 0)))) {
                    return (a315->a - ((a315->a - expr->a) % a314->b));
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a317 = a313->a.as<Add>()) {
        if (const Div *a318 = a317->a.as<Div>()) {
          if (const Sub *a319 = a318->a.as<Sub>()) {
            if (is_const(a319->a)) {
              if (equal(expr->a, a319->b)) {
                if (is_const(a318->b)) {
                  if (equal(a318->b, a313->b)) {
                    if (evaluate_predicate(fold((a318->b > 0)))) {
                      return (((a317->b * a318->b) - ((a319->a - expr->a) % a318->b)) + a319->a);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Div *a322 = a317->b.as<Div>()) {
          if (const Sub *a323 = a322->a.as<Sub>()) {
            if (is_const(a323->a)) {
              if (equal(expr->a, a323->b)) {
                if (is_const(a322->b)) {
                  if (equal(a322->b, a313->b)) {
                    if (evaluate_predicate(fold((a322->b > 0)))) {
                      return (((a317->a * a322->b) - ((a323->a - expr->a) % a322->b)) + a323->a);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
