#include "Expr.h"
#include "Type.h"
#include "Simplify_Internal.h"
#include "SimplifyGeneratedInternal.h"

namespace Halide {
namespace Internal {
namespace CodeGen {
Expr Simplify_Max(const Max *expr, Simplify *simplifier) {
  if (equal(expr->a, expr->b)) {
    return expr->a;
  }
  if (is_const(expr->a)) {
    if (is_const(expr->b)) {
      return fold(max(expr->a, expr->b));
    }
  }
  if (const Mul *a0 = expr->a.as<Mul>()) {
    if (const Div *a1 = a0->a.as<Div>()) {
      if (is_const(a1->b)) {
        if (equal(a1->b, a0->b)) {
          if (equal(a1->a, expr->b)) {
            if (evaluate_predicate(fold((a1->b > 0)))) {
              return a1->a;
            }
          }
        }
      }
    }
  }
  if (const Mul *a2 = expr->b.as<Mul>()) {
    if (const Div *a3 = a2->a.as<Div>()) {
      if (equal(expr->a, a3->a)) {
        if (is_const(a3->b)) {
          if (equal(a3->b, a2->b)) {
            if (evaluate_predicate(fold((a3->b > 0)))) {
              return expr->a;
            }
          }
        }
      }
    }
  }
  if (const Max *a4 = expr->a.as<Max>()) {
    if (equal(a4->a, expr->b)) {
      return max(a4->a, a4->b);
    }
    if (equal(a4->b, expr->b)) {
      return max(a4->a, a4->b);
    }
    if (const Max *a7 = a4->a.as<Max>()) {
      if (equal(a7->a, expr->b)) {
        return max(max(a7->a, a7->b), a4->b);
      }
      if (equal(a7->b, expr->b)) {
        return max(max(a7->a, a7->b), a4->b);
      }
      if (const Max *a12 = a7->a.as<Max>()) {
        if (equal(a12->a, expr->b)) {
          return max(max(max(a12->a, a12->b), a7->b), a4->b);
        }
        if (equal(a12->b, expr->b)) {
          return max(max(max(a12->a, a12->b), a7->b), a4->b);
        }
        if (const Max *a19 = a12->a.as<Max>()) {
          if (equal(a19->a, expr->b)) {
            return max(max(max(max(a19->a, a19->b), a12->b), a7->b), a4->b);
          }
          if (equal(a19->b, expr->b)) {
            return max(max(max(max(a19->a, a19->b), a12->b), a7->b), a4->b);
          }
        }
      }
    }
    if (const Min *a29 = expr->b.as<Min>()) {
      if (equal(a4->a, a29->a)) {
        if (equal(a4->b, a29->b)) {
          return max(a4->a, a4->b);
        }
        return max(a4->a, a4->b);
      }
      if (equal(a4->b, a29->a)) {
        if (equal(a4->a, a29->b)) {
          return max(a4->a, a4->b);
        }
        return max(a4->a, a4->b);
      }
      if (equal(a4->a, a29->b)) {
        return max(a4->a, a4->b);
      }
      if (equal(a4->b, a29->b)) {
        return max(a4->a, a4->b);
      }
    }
    if (is_const(a4->b)) {
      if (is_const(expr->b)) {
        return max(a4->a, fold(max(a4->b, expr->b)));
      }
      return max(max(a4->a, expr->b), a4->b);
    }
    if (const Max *a131 = expr->b.as<Max>()) {
      if (equal(a4->a, a131->a)) {
        return max(max(a4->b, a131->b), a4->a);
      }
      if (equal(a4->b, a131->a)) {
        return max(max(a4->a, a131->b), a4->b);
      }
      if (equal(a4->a, a131->b)) {
        return max(max(a4->b, a131->a), a4->a);
      }
      if (equal(a4->b, a131->b)) {
        return max(max(a4->a, a131->a), a4->b);
      }
      return max(max(max(a4->a, a4->b), a131->a), a131->b);
    }
    if (const Broadcast *a143 = a4->b.as<Broadcast>()) {
      if (is_const(a143->lanes)) {
        if (const Broadcast *a144 = expr->b.as<Broadcast>()) {
          if (equal(a143->lanes, a144->lanes)) {
            return max(a4->a, broadcast(max(a143->value, a144->value), a143->lanes));
          }
        }
      }
    }
    if (const Div *a159 = a4->a.as<Div>()) {
      if (is_const(a159->b)) {
        if (const Div *a160 = expr->b.as<Div>()) {
          if (equal(a159->b, a160->b)) {
            if (evaluate_predicate(fold((a159->b > 0)))) {
              return max((max(a159->a, a160->a) / a159->b), a4->b);
            }
          }
        }
      }
    }
    if (const Min *a172 = a4->b.as<Min>()) {
      if (equal(a172->a, expr->b)) {
        return max(a4->a, a172->a);
      }
      if (equal(a172->b, expr->b)) {
        return max(a4->a, a172->b);
      }
    }
    if (const Min *a176 = a4->a.as<Min>()) {
      if (equal(a176->a, expr->b)) {
        return max(a4->b, a176->a);
      }
      if (equal(a176->b, expr->b)) {
        return max(a4->b, a176->b);
      }
    }
  }
  if (const Max *a24 = expr->b.as<Max>()) {
    if (equal(expr->a, a24->a)) {
      return max(expr->a, a24->b);
    }
    if (equal(expr->a, a24->b)) {
      return max(a24->a, expr->a);
    }
    if (const Min *a180 = a24->b.as<Min>()) {
      if (equal(expr->a, a180->a)) {
        return max(a24->a, expr->a);
      }
      if (equal(expr->a, a180->b)) {
        return max(a24->a, expr->a);
      }
    }
    if (const Min *a184 = a24->a.as<Min>()) {
      if (equal(expr->a, a184->a)) {
        return max(expr->a, a24->b);
      }
      if (equal(expr->a, a184->b)) {
        return max(expr->a, a24->b);
      }
    }
  }
  if (const Min *a25 = expr->b.as<Min>()) {
    if (equal(expr->a, a25->a)) {
      return expr->a;
    }
    if (equal(expr->a, a25->b)) {
      return expr->a;
    }
    if (const Min *a36 = a25->b.as<Min>()) {
      if (equal(expr->a, a36->a)) {
        return expr->a;
      }
      if (equal(expr->a, a36->b)) {
        return expr->a;
      }
    }
    if (const Min *a40 = a25->a.as<Min>()) {
      if (equal(expr->a, a40->a)) {
        return expr->a;
      }
      if (equal(expr->a, a40->b)) {
        return expr->a;
      }
    }
  }
  if (const Min *a32 = expr->a.as<Min>()) {
    if (equal(a32->a, expr->b)) {
      return a32->a;
    }
    if (equal(a32->b, expr->b)) {
      return a32->b;
    }
    if (is_const(a32->b)) {
      if (is_const(expr->b)) {
        if (evaluate_predicate(fold((expr->b >= a32->b)))) {
          return expr->b;
        }
      }
    }
    if (const Min *a44 = a32->b.as<Min>()) {
      if (equal(a44->a, expr->b)) {
        return a44->a;
      }
      if (equal(a44->b, expr->b)) {
        return a44->b;
      }
    }
    if (const Min *a48 = a32->a.as<Min>()) {
      if (equal(a48->a, expr->b)) {
        return a48->a;
      }
      if (equal(a48->b, expr->b)) {
        return a48->b;
      }
    }
    if (const Min *a146 = expr->b.as<Min>()) {
      if (equal(a32->a, a146->a)) {
        return min(a32->a, max(a32->b, a146->b));
      }
      if (equal(a32->a, a146->b)) {
        return min(a32->a, max(a32->b, a146->a));
      }
      if (equal(a32->b, a146->a)) {
        return min(max(a32->a, a146->b), a32->b);
      }
      if (equal(a32->b, a146->b)) {
        return min(max(a32->a, a146->a), a32->b);
      }
    }
    if (const Max *a154 = a32->a.as<Max>()) {
      if (equal(a154->b, expr->b)) {
        return max(min(a154->a, a32->b), a154->b);
      }
      if (equal(a154->a, expr->b)) {
        return max(a154->a, min(a154->b, a32->b));
      }
    }
  }
  if (const Select *a59 = expr->a.as<Select>()) {
    if (const Max *a60 = a59->true_value.as<Max>()) {
      if (equal(a60->a, expr->b)) {
        return max(select(a59->condition, a60->b, a59->false_value), a60->a);
      }
      if (equal(a60->b, expr->b)) {
        return max(select(a59->condition, a60->a, a59->false_value), a60->b);
      }
    }
    if (const Max *a64 = a59->false_value.as<Max>()) {
      if (equal(a64->a, expr->b)) {
        return max(select(a59->condition, a59->true_value, a64->b), a64->a);
      }
      if (equal(a64->b, expr->b)) {
        return max(select(a59->condition, a59->true_value, a64->a), a64->b);
      }
    }
    if (const EQ *a166 = a59->condition.as<EQ>()) {
      if (is_const(a166->b)) {
        if (is_const(a59->true_value)) {
          if (equal(a166->a, a59->false_value)) {
            if (is_const(expr->b)) {
              if (evaluate_predicate(fold(((a166->b <= expr->b) && (a59->true_value <= expr->b))))) {
                return max(a166->a, expr->b);
              }
            }
            if (equal(a166->a, expr->b)) {
              if (evaluate_predicate(fold((a166->b < a59->true_value)))) {
                return select((a166->a == a166->b), a59->true_value, a166->a);
              }
              if (evaluate_predicate(fold((a59->true_value <= a166->b)))) {
                return a166->a;
              }
            }
          }
        }
      }
    }
    if (const Min *a188 = a59->true_value.as<Min>()) {
      if (equal(a188->b, expr->b)) {
        return select(a59->condition, a188->b, max(a59->false_value, a188->b));
      }
      if (equal(a188->a, expr->b)) {
        return select(a59->condition, a188->a, max(a59->false_value, a188->a));
      }
    }
    if (const Min *a196 = a59->false_value.as<Min>()) {
      if (equal(a196->b, expr->b)) {
        return select(a59->condition, max(a59->true_value, a196->b), a196->b);
      }
      if (equal(a196->a, expr->b)) {
        return select(a59->condition, max(a59->true_value, a196->a), a196->a);
      }
    }
    if (const Select *a204 = expr->b.as<Select>()) {
      if (equal(a59->condition, a204->condition)) {
        return select(a59->condition, max(a59->true_value, a204->true_value), max(a59->false_value, a204->false_value));
      }
    }
  }
  if (is_no_overflow(expr)) {
    if (const Ramp *a67 = expr->a.as<Ramp>()) {
      if (is_const(a67->lanes)) {
        if (const Broadcast *a68 = expr->b.as<Broadcast>()) {
          if (equal(a67->lanes, a68->lanes)) {
            if (evaluate_predicate(fold(can_prove((((a67->base + (a67->stride * (a67->lanes - 1))) >= a68->value) && (a67->base >= a68->value)), simplifier)))) {
              return ramp(a67->base, a67->stride, a67->lanes);
            }
            if (evaluate_predicate(fold(can_prove((((a67->base + (a67->stride * (a67->lanes - 1))) <= a68->value) && (a67->base <= a68->value)), simplifier)))) {
              return broadcast(a68->value, a67->lanes);
            }
          }
        }
      }
    }
    if (const Add *a71 = expr->a.as<Add>()) {
      if (const Mul *a72 = a71->a.as<Mul>()) {
        if (const Div *a73 = a72->a.as<Div>()) {
          if (const Add *a74 = a73->a.as<Add>()) {
            if (is_const(a74->b)) {
              if (is_const(a73->b)) {
                if (equal(a73->b, a72->b)) {
                  if (is_const(a71->b)) {
                    if (equal(a74->a, expr->b)) {
                      if (evaluate_predicate(fold(((a73->b > 0) && ((a74->b + a71->b) >= (a73->b - 1)))))) {
                        return ((((a74->a + a74->b) / a73->b) * a73->b) + a71->b);
                      }
                      if (evaluate_predicate(fold(((a73->b > 0) && ((a74->b + a71->b) <= 0))))) {
                        return a74->a;
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const(a73->b)) {
            if (equal(a73->b, a72->b)) {
              if (is_const(a71->b)) {
                if (equal(a73->a, expr->b)) {
                  if (evaluate_predicate(fold(((a73->b > 0) && (a71->b >= (a73->b - 1)))))) {
                    return (((a73->a / a73->b) * a73->b) + a71->b);
                  }
                  if (evaluate_predicate(fold(((a73->b > 0) && (a71->b <= 0))))) {
                    return a73->a;
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a121 = a71->a.as<Min>()) {
        if (is_const(a71->b)) {
          if (equal(a121->a, expr->b)) {
            if (evaluate_predicate(fold((a71->b <= 0)))) {
              return a121->a;
            }
          }
          if (equal(a121->b, expr->b)) {
            if (evaluate_predicate(fold((a71->b <= 0)))) {
              return a121->b;
            }
          }
        }
      }
      if (const Max *a206 = a71->a.as<Max>()) {
        if (is_const(a71->b)) {
          if (equal(a206->a, expr->b)) {
            if (evaluate_predicate(fold((a71->b < 0)))) {
              return max(a206->a, (a206->b + a71->b));
            }
            if (evaluate_predicate(fold((a71->b > 0)))) {
              return (max(a206->a, a206->b) + a71->b);
            }
          }
          if (equal(a206->b, expr->b)) {
            if (evaluate_predicate(fold((a71->b < 0)))) {
              return max((a206->a + a71->b), a206->b);
            }
            if (evaluate_predicate(fold((a71->b > 0)))) {
              return (max(a206->a, a206->b) + a71->b);
            }
          }
        }
      }
      if (is_const(a71->b)) {
        if (is_const(expr->b)) {
          return (max(a71->a, fold((expr->b - a71->b))) + a71->b);
        }
        if (const Add *a223 = expr->b.as<Add>()) {
          if (is_const(a223->b)) {
            if (evaluate_predicate(fold((a223->b > a71->b)))) {
              return (max(a71->a, (a223->a + fold((a223->b - a71->b)))) + a71->b);
            }
            if (evaluate_predicate(fold((a71->b > a223->b)))) {
              return (max((a71->a + fold((a71->b - a223->b))), a223->a) + a223->b);
            }
          }
        }
      }
      if (const Add *a235 = expr->b.as<Add>()) {
        if (equal(a71->a, a235->a)) {
          return (a71->a + max(a71->b, a235->b));
        }
        if (equal(a71->a, a235->b)) {
          return (a71->a + max(a71->b, a235->a));
        }
        if (equal(a71->b, a235->a)) {
          return (max(a71->a, a235->b) + a71->b);
        }
        if (equal(a71->b, a235->b)) {
          return (max(a71->a, a235->a) + a71->b);
        }
        if (const Add *a308 = a235->a.as<Add>()) {
          if (equal(a71->a, a308->b)) {
            return (a71->a + max((a308->a + a235->b), a71->b));
          }
          if (equal(a71->a, a308->a)) {
            return (a71->a + max((a308->b + a235->b), a71->b));
          }
          if (equal(a71->b, a308->b)) {
            return (max((a308->a + a235->b), a71->a) + a71->b);
          }
          if (equal(a71->b, a308->a)) {
            return (max((a308->b + a235->b), a71->a) + a71->b);
          }
        }
      }
      if (equal(a71->b, expr->b)) {
        return (max(a71->a, 0) + a71->b);
      }
      if (equal(a71->a, expr->b)) {
        return (a71->a + max(a71->b, 0));
      }
      if (const Add *a291 = a71->a.as<Add>()) {
        if (const Add *a292 = expr->b.as<Add>()) {
          if (equal(a291->a, a292->a)) {
            return (a291->a + max((a291->b + a71->b), a292->b));
          }
          if (equal(a291->b, a292->a)) {
            return (max((a291->a + a71->b), a292->b) + a291->b);
          }
          if (equal(a291->a, a292->b)) {
            return (a291->a + max((a291->b + a71->b), a292->a));
          }
          if (equal(a291->b, a292->b)) {
            return (max((a291->a + a71->b), a292->a) + a291->b);
          }
        }
        if (equal(a291->a, expr->b)) {
          return (a291->a + max((a291->b + a71->b), 0));
        }
        if (equal(a291->b, expr->b)) {
          return (a291->b + max((a291->a + a71->b), 0));
        }
      }
      if (const Sub *a341 = a71->a.as<Sub>()) {
        if (equal(a341->a, expr->b)) {
          return (max((a71->b - a341->b), 0) + a341->a);
        }
      }
      if (const Sub *a343 = a71->b.as<Sub>()) {
        if (equal(a343->a, expr->b)) {
          return (max((a71->a - a343->b), 0) + a343->a);
        }
      }
    }
    if (const Add *a75 = expr->b.as<Add>()) {
      if (const Mul *a76 = a75->a.as<Mul>()) {
        if (const Div *a77 = a76->a.as<Div>()) {
          if (const Add *a78 = a77->a.as<Add>()) {
            if (equal(expr->a, a78->a)) {
              if (is_const(a78->b)) {
                if (is_const(a77->b)) {
                  if (equal(a77->b, a76->b)) {
                    if (is_const(a75->b)) {
                      if (evaluate_predicate(fold(((a77->b > 0) && ((a78->b + a75->b) >= (a77->b - 1)))))) {
                        return ((((expr->a + a78->b) / a77->b) * a77->b) + a75->b);
                      }
                      if (evaluate_predicate(fold(((a77->b > 0) && ((a78->b + a75->b) <= 0))))) {
                        return expr->a;
                      }
                    }
                  }
                }
              }
            }
          }
          if (equal(expr->a, a77->a)) {
            if (is_const(a77->b)) {
              if (equal(a77->b, a76->b)) {
                if (is_const(a75->b)) {
                  if (evaluate_predicate(fold(((a77->b > 0) && (a75->b >= (a77->b - 1)))))) {
                    return (((expr->a / a77->b) * a77->b) + a75->b);
                  }
                  if (evaluate_predicate(fold(((a77->b > 0) && (a75->b <= 0))))) {
                    return expr->a;
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a117 = a75->a.as<Min>()) {
        if (equal(expr->a, a117->a)) {
          if (is_const(a75->b)) {
            if (evaluate_predicate(fold((a75->b <= 0)))) {
              return expr->a;
            }
          }
        }
        if (equal(expr->a, a117->b)) {
          if (is_const(a75->b)) {
            if (evaluate_predicate(fold((a75->b <= 0)))) {
              return expr->a;
            }
          }
        }
      }
      if (const Max *a214 = a75->a.as<Max>()) {
        if (equal(expr->a, a214->a)) {
          if (is_const(a75->b)) {
            if (evaluate_predicate(fold((a75->b < 0)))) {
              return max(expr->a, (a214->b + a75->b));
            }
            if (evaluate_predicate(fold((a75->b > 0)))) {
              return (max(expr->a, a214->b) + a75->b);
            }
          }
        }
        if (equal(expr->a, a214->b)) {
          if (is_const(a75->b)) {
            if (evaluate_predicate(fold((a75->b < 0)))) {
              return max(expr->a, (a214->a + a75->b));
            }
            if (evaluate_predicate(fold((a75->b > 0)))) {
              return (max(expr->a, a214->a) + a75->b);
            }
          }
        }
      }
      if (equal(expr->a, a75->a)) {
        return (expr->a + max(a75->b, 0));
      }
      if (equal(expr->a, a75->b)) {
        return (expr->a + max(a75->a, 0));
      }
      if (const Add *a319 = a75->a.as<Add>()) {
        if (equal(expr->a, a319->b)) {
          return (expr->a + max((a319->a + a75->b), 0));
        }
        if (equal(expr->a, a319->a)) {
          return (expr->a + max((a319->b + a75->b), 0));
        }
      }
      if (const Sub *a335 = a75->a.as<Sub>()) {
        if (equal(expr->a, a335->a)) {
          return (expr->a + max((a75->b - a335->b), 0));
        }
      }
      if (const Sub *a337 = a75->b.as<Sub>()) {
        if (equal(expr->a, a337->a)) {
          return (expr->a + max((a75->a - a337->b), 0));
        }
      }
    }
    if (const Mul *a87 = expr->a.as<Mul>()) {
      if (const Div *a88 = a87->a.as<Div>()) {
        if (is_const(a88->b)) {
          if (equal(a88->b, a87->b)) {
            if (const Add *a89 = expr->b.as<Add>()) {
              if (const Mul *a90 = a89->a.as<Mul>()) {
                if (const Div *a91 = a90->a.as<Div>()) {
                  if (equal(a88->a, a91->a)) {
                    if (is_const(a91->b)) {
                      if (equal(a91->b, a90->b)) {
                        if (is_const(a89->b)) {
                          if (evaluate_predicate(fold((((a89->b >= a91->b) && (a91->b > 0)) && (a88->b != 0))))) {
                            return (((a88->a / a91->b) * a91->b) + a89->b);
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
        if (const Add *a100 = a88->a.as<Add>()) {
          if (is_const(a100->b)) {
            if (is_const(a88->b)) {
              if (equal(a88->b, a87->b)) {
                if (equal(a100->a, expr->b)) {
                  if (evaluate_predicate(fold(((a88->b > 0) && (a100->b >= (a88->b - 1)))))) {
                    return (((a100->a + a100->b) / a88->b) * a88->b);
                  }
                  if (evaluate_predicate(fold(((a88->b > 0) && (a100->b <= 0))))) {
                    return a100->a;
                  }
                }
                if (const Add *a377 = expr->b.as<Add>()) {
                  if (equal(a100->a, a377->a)) {
                    if (is_const(a377->b)) {
                      if (evaluate_predicate(fold(((a88->b > 0) && ((a100->b + 1) >= (a88->b + a377->b)))))) {
                        return (((a100->a + a100->b) / a88->b) * a88->b);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a247 = a87->a.as<Add>()) {
        if (const Mul *a248 = a247->a.as<Mul>()) {
          if (is_const(a248->b)) {
            if (is_const(a87->b)) {
              if (const Add *a249 = expr->b.as<Add>()) {
                if (const Mul *a250 = a249->a.as<Mul>()) {
                  if (equal(a248->a, a250->a)) {
                    if (is_const(a250->b)) {
                      if (evaluate_predicate(fold(((a248->b * a87->b) == a250->b)))) {
                        return (max((a247->b * a87->b), a249->b) + (a248->a * a250->b));
                      }
                    }
                  }
                }
                if (const Mul *a260 = a249->b.as<Mul>()) {
                  if (equal(a248->a, a260->a)) {
                    if (is_const(a260->b)) {
                      if (evaluate_predicate(fold(((a248->b * a87->b) == a260->b)))) {
                        return (max((a247->b * a87->b), a249->a) + (a248->a * a260->b));
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Mul *a253 = a247->b.as<Mul>()) {
          if (is_const(a253->b)) {
            if (is_const(a87->b)) {
              if (const Add *a254 = expr->b.as<Add>()) {
                if (const Mul *a255 = a254->a.as<Mul>()) {
                  if (equal(a253->a, a255->a)) {
                    if (is_const(a255->b)) {
                      if (evaluate_predicate(fold(((a253->b * a87->b) == a255->b)))) {
                        return (max((a247->a * a87->b), a254->b) + (a253->a * a255->b));
                      }
                    }
                  }
                }
                if (const Mul *a265 = a254->b.as<Mul>()) {
                  if (equal(a253->a, a265->a)) {
                    if (is_const(a265->b)) {
                      if (evaluate_predicate(fold(((a253->b * a87->b) == a265->b)))) {
                        return (max((a247->a * a87->b), a254->a) + (a253->a * a265->b));
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (is_const(a87->b)) {
        if (is_const(expr->b)) {
          if (evaluate_predicate(fold(((a87->b > 0) && ((expr->b % a87->b) == 0))))) {
            return (max(a87->a, fold((expr->b / a87->b))) * a87->b);
          }
          if (evaluate_predicate(fold(((a87->b < 0) && ((expr->b % a87->b) == 0))))) {
            return (min(a87->a, fold((expr->b / a87->b))) * a87->b);
          }
        }
        if (const Mul *a349 = expr->b.as<Mul>()) {
          if (is_const(a349->b)) {
            if (evaluate_predicate(fold(((a87->b > 0) && ((a349->b % a87->b) == 0))))) {
              return (max(a87->a, (a349->a * fold((a349->b / a87->b)))) * a87->b);
            }
            if (evaluate_predicate(fold(((a87->b < 0) && ((a349->b % a87->b) == 0))))) {
              return (min(a87->a, (a349->a * fold((a349->b / a87->b)))) * a87->b);
            }
            if (evaluate_predicate(fold(((a349->b > 0) && ((a87->b % a349->b) == 0))))) {
              return (max((a87->a * fold((a87->b / a349->b))), a349->a) * a349->b);
            }
            if (evaluate_predicate(fold(((a349->b < 0) && ((a87->b % a349->b) == 0))))) {
              return (min((a87->a * fold((a87->b / a349->b))), a349->a) * a349->b);
            }
          }
        }
        if (const Add *a357 = expr->b.as<Add>()) {
          if (const Mul *a358 = a357->a.as<Mul>()) {
            if (equal(a87->b, a358->b)) {
              if (is_const(a357->b)) {
                if (evaluate_predicate(fold(((a87->b > 0) && ((a357->b % a87->b) == 0))))) {
                  return (max(a87->a, (a358->a + fold((a357->b / a87->b)))) * a87->b);
                }
                if (evaluate_predicate(fold(((a87->b < 0) && ((a357->b % a87->b) == 0))))) {
                  return (min(a87->a, (a358->a + fold((a357->b / a87->b)))) * a87->b);
                }
              }
            }
          }
        }
      }
    }
    if (const Mul *a101 = expr->b.as<Mul>()) {
      if (const Div *a102 = a101->a.as<Div>()) {
        if (const Add *a103 = a102->a.as<Add>()) {
          if (equal(expr->a, a103->a)) {
            if (is_const(a103->b)) {
              if (is_const(a102->b)) {
                if (equal(a102->b, a101->b)) {
                  if (evaluate_predicate(fold(((a102->b > 0) && (a103->b >= (a102->b - 1)))))) {
                    return (((expr->a + a103->b) / a102->b) * a102->b);
                  }
                  if (evaluate_predicate(fold(((a102->b > 0) && (a103->b <= 0))))) {
                    return expr->a;
                  }
                }
              }
            }
          }
        }
      }
    }
    if (const Max *a226 = expr->a.as<Max>()) {
      if (const Add *a227 = expr->b.as<Add>()) {
        if (equal(a226->a, a227->a)) {
          if (is_const(a227->b)) {
            if (evaluate_predicate(fold((a227->b > 0)))) {
              return max((a226->a + a227->b), a226->b);
            }
            if (evaluate_predicate(fold((a227->b < 0)))) {
              return max(a226->a, a226->b);
            }
          }
        }
        if (equal(a226->b, a227->a)) {
          if (is_const(a227->b)) {
            if (evaluate_predicate(fold((a227->b > 0)))) {
              return max(a226->a, (a226->b + a227->b));
            }
            if (evaluate_predicate(fold((a227->b < 0)))) {
              return max(a226->a, a226->b);
            }
          }
        }
      }
      if (const Add *a267 = a226->a.as<Add>()) {
        if (const Add *a268 = expr->b.as<Add>()) {
          if (equal(a267->a, a268->a)) {
            return max((a267->a + max(a267->b, a268->b)), a226->b);
          }
          if (equal(a267->a, a268->b)) {
            return max((a267->a + max(a267->b, a268->a)), a226->b);
          }
          if (equal(a267->b, a268->a)) {
            return max((max(a267->a, a268->b) + a267->b), a226->b);
          }
          if (equal(a267->b, a268->b)) {
            return max((max(a267->a, a268->a) + a267->b), a226->b);
          }
        }
      }
      if (const Add *a270 = a226->b.as<Add>()) {
        if (const Add *a271 = expr->b.as<Add>()) {
          if (equal(a270->a, a271->a)) {
            return max((a270->a + max(a270->b, a271->b)), a226->a);
          }
          if (equal(a270->a, a271->b)) {
            return max((a270->a + max(a270->b, a271->a)), a226->a);
          }
          if (equal(a270->b, a271->a)) {
            return max((max(a270->a, a271->b) + a270->b), a226->a);
          }
          if (equal(a270->b, a271->b)) {
            return max((max(a270->a, a271->a) + a270->b), a226->a);
          }
        }
      }
    }
    if (const Sub *a322 = expr->a.as<Sub>()) {
      if (const Sub *a323 = expr->b.as<Sub>()) {
        if (equal(a322->b, a323->b)) {
          return (max(a322->a, a323->a) - a322->b);
        }
        if (equal(a322->a, a323->a)) {
          return (a322->a - min(a322->b, a323->b));
        }
      }
      if (const Add *a327 = expr->b.as<Add>()) {
        if (const Sub *a328 = a327->a.as<Sub>()) {
          if (equal(a322->b, a328->b)) {
            return (max(a322->a, (a328->a + a327->b)) - a322->b);
          }
        }
        if (const Sub *a331 = a327->b.as<Sub>()) {
          if (equal(a322->b, a331->b)) {
            return (max(a322->a, (a327->a + a331->a)) - a322->b);
          }
        }
      }
      if (equal(a322->a, expr->b)) {
        return (a322->a - min(a322->b, 0));
      }
      if (const Sub *a345 = a322->a.as<Sub>()) {
        if (equal(a345->a, expr->b)) {
          return (a345->a - min((a345->b + a322->b), 0));
        }
      }
      if (is_const(a322->a)) {
        if (is_const(expr->b)) {
          return (a322->a - min(a322->b, fold((a322->a - expr->b))));
        }
      }
    }
    if (const Sub *a332 = expr->b.as<Sub>()) {
      if (equal(expr->a, a332->a)) {
        return (expr->a - min(a332->b, 0));
      }
      if (const Sub *a339 = a332->a.as<Sub>()) {
        if (equal(expr->a, a339->a)) {
          return (expr->a - min((a339->b + a332->b), 0));
        }
      }
    }
    if (const Div *a362 = expr->a.as<Div>()) {
      if (is_const(a362->b)) {
        if (const Div *a363 = expr->b.as<Div>()) {
          if (equal(a362->b, a363->b)) {
            if (evaluate_predicate(fold((a362->b > 0)))) {
              return (max(a362->a, a363->a) / a362->b);
            }
            if (evaluate_predicate(fold((a362->b < 0)))) {
              return (min(a362->a, a363->a) / a362->b);
            }
          }
        }
        if (is_const(expr->b)) {
          if (evaluate_predicate(fold(((a362->b > 0) && !(overflows((expr->b * a362->b))))))) {
            return (max(a362->a, fold((expr->b * a362->b))) / a362->b);
          }
          if (evaluate_predicate(fold(((a362->b < 0) && !(overflows((expr->b * a362->b))))))) {
            return (min(a362->a, fold((expr->b * a362->b))) / a362->b);
          }
        }
        if (const Add *a369 = expr->b.as<Add>()) {
          if (const Div *a370 = a369->a.as<Div>()) {
            if (equal(a362->b, a370->b)) {
              if (is_const(a369->b)) {
                if (evaluate_predicate(fold(((a362->b > 0) && !(overflows((a369->b * a362->b))))))) {
                  return (max(a362->a, (a370->a + fold((a369->b * a362->b)))) / a362->b);
                }
                if (evaluate_predicate(fold(((a362->b < 0) && !(overflows((a369->b * a362->b))))))) {
                  return (min(a362->a, (a370->a + fold((a369->b * a362->b)))) / a362->b);
                }
              }
            }
          }
        }
        if (const Mul *a389 = expr->b.as<Mul>()) {
          if (const Div *a390 = a389->a.as<Div>()) {
            if (const Add *a391 = a390->a.as<Add>()) {
              if (equal(a362->a, a391->a)) {
                if (is_const(a391->b)) {
                  if (is_const(a390->b)) {
                    if (is_const(a389->b)) {
                      if (evaluate_predicate(fold(((((a391->b <= 0) && (a362->b > 0)) && (a390->b > 0)) && ((a362->b * a389->b) == a390->b))))) {
                        return (a362->a / a362->b);
                      }
                      if (evaluate_predicate(fold((((((a390->b - a362->b) <= a391->b) && (a362->b > 0)) && (a390->b > 0)) && ((a362->b * a389->b) == a390->b))))) {
                        return (((a362->a + a391->b) / a390->b) * a389->b);
                      }
                    }
                  }
                }
              }
            }
            if (equal(a362->a, a390->a)) {
              if (is_const(a390->b)) {
                if (is_const(a389->b)) {
                  if (evaluate_predicate(fold((((a362->b > 0) && (a390->b > 0)) && ((a362->b * a389->b) == a390->b))))) {
                    return (a362->a / a362->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a379 = a362->a.as<Add>()) {
        if (is_const(a379->b)) {
          if (is_const(a362->b)) {
            if (const Mul *a380 = expr->b.as<Mul>()) {
              if (const Div *a381 = a380->a.as<Div>()) {
                if (const Add *a382 = a381->a.as<Add>()) {
                  if (equal(a379->a, a382->a)) {
                    if (is_const(a382->b)) {
                      if (is_const(a381->b)) {
                        if (is_const(a380->b)) {
                          if (evaluate_predicate(fold(((((a382->b <= a379->b) && (a362->b > 0)) && (a381->b > 0)) && ((a362->b * a380->b) == a381->b))))) {
                            return ((a379->a + a379->b) / a362->b);
                          }
                          if (evaluate_predicate(fold(((((((a379->b + a381->b) - a362->b) <= a382->b) && (a362->b > 0)) && (a381->b > 0)) && ((a362->b * a380->b) == a381->b))))) {
                            return (((a379->a + a382->b) / a381->b) * a380->b);
                          }
                        }
                      }
                    }
                  }
                }
                if (equal(a379->a, a381->a)) {
                  if (is_const(a381->b)) {
                    if (is_const(a380->b)) {
                      if (evaluate_predicate(fold(((((0 <= a379->b) && (a362->b > 0)) && (a381->b > 0)) && ((a362->b * a380->b) == a381->b))))) {
                        return ((a379->a + a379->b) / a362->b);
                      }
                      if (evaluate_predicate(fold(((((((a379->b + a381->b) - a362->b) <= 0) && (a362->b > 0)) && (a381->b > 0)) && ((a362->b * a380->b) == a381->b))))) {
                        return ((a379->a / a381->b) * a380->b);
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
  }
  if (is_no_overflow_int(expr)) {
    if (const Min *a124 = expr->a.as<Min>()) {
      if (const Sub *a125 = a124->a.as<Sub>()) {
        if (is_const(a125->a)) {
          if (equal(a125->b, a124->b)) {
            if (is_const(expr->b)) {
              if (evaluate_predicate(fold(((2 * expr->b) >= (a125->a - 1))))) {
                return expr->b;
              }
            }
          }
        }
      }
      if (const Sub *a127 = a124->b.as<Sub>()) {
        if (is_const(a127->a)) {
          if (equal(a124->a, a127->b)) {
            if (is_const(expr->b)) {
              if (evaluate_predicate(fold(((2 * expr->b) >= (a127->a - 1))))) {
                return expr->b;
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a140 = expr->a.as<Broadcast>()) {
    if (is_const(a140->lanes)) {
      if (const Broadcast *a141 = expr->b.as<Broadcast>()) {
        if (equal(a140->lanes, a141->lanes)) {
          return broadcast(max(a140->value, a141->value), a140->lanes);
        }
      }
    }
  }
  if (const Select *a161 = expr->b.as<Select>()) {
    if (const EQ *a162 = a161->condition.as<EQ>()) {
      if (equal(expr->a, a162->a)) {
        if (is_const(a162->b)) {
          if (is_const(a161->true_value)) {
            if (equal(expr->a, a161->false_value)) {
              if (evaluate_predicate(fold((a162->b < a161->true_value)))) {
                return select((expr->a == a162->b), a161->true_value, expr->a);
              }
              if (evaluate_predicate(fold((a161->true_value <= a162->b)))) {
                return expr->a;
              }
            }
          }
        }
      }
    }
    if (const Min *a192 = a161->true_value.as<Min>()) {
      if (equal(expr->a, a192->b)) {
        return select(a161->condition, expr->a, max(expr->a, a161->false_value));
      }
      if (equal(expr->a, a192->a)) {
        return select(a161->condition, expr->a, max(expr->a, a161->false_value));
      }
    }
    if (const Min *a200 = a161->false_value.as<Min>()) {
      if (equal(expr->a, a200->b)) {
        return select(a161->condition, max(expr->a, a161->true_value), expr->a);
      }
      if (equal(expr->a, a200->a)) {
        return select(a161->condition, max(expr->a, a161->true_value), expr->a);
      }
    }
  }
  return Expr();
}
}  // namespace CodeGen
}  // namespace Internal
}  // namespace Halide
