#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_Max(const Min *expr, Simplify *simplifier) {
  if (equal(expr->a, expr->b)) {
    return expr->a;
  }
  if (is_const_v(expr->a)) {
    if (is_const_v(expr->b)) {
      return fold(min(expr->a, expr->b));
    }
  }
  if (const Mul *a0 = expr->a->as<Mul>()) {
    if (const Div *a1 = a0->a->as<Div>()) {
      if (is_const_v(a1->b)) {
        if (equal(a1->b, a0->b)) {
          if (equal(a1->a, expr->b)) {
            if (evaluate_predicate(fold((a1->b > 0)))) {
              return b;
            }
          }
        }
      }
    }
  }
  if (const Mul *a2 = expr->b->as<Mul>()) {
    if (const Div *a3 = a2->a->as<Div>()) {
      if (equal(expr->a, a3->a)) {
        if (is_const_v(a3->b)) {
          if (equal(a3->b, a2->b)) {
            if (evaluate_predicate(fold((a3->b > 0)))) {
              return a;
            }
          }
        }
      }
    }
  }
  if (const Min *a4 = expr->a->as<Min>()) {
    if (equal(a4->a, expr->b)) {
      return a;
      return b;
    }
    if (equal(a4->b, expr->b)) {
      return a;
      return b;
    }
    if (const Min *a7 = a4->a->as<Min>()) {
      if (equal(a7->a, expr->b)) {
        return a;
        return b;
        return min(a7->a, min(a7->b, a4->b));
        return min(a4->b, a7->a);
      }
      if (equal(a7->b, expr->b)) {
        return a;
        return b;
        return min(min(a7->a, a4->b), a7->b);
        return min(a4->b, a7->b);
      }
      if (const Min *a12 = a7->a->as<Min>()) {
        if (equal(a12->a, expr->b)) {
          return a;
        }
        if (equal(a12->b, expr->b)) {
          return a;
        }
        if (const Min *a19 = a12->a->as<Min>()) {
          if (equal(a19->a, expr->b)) {
            return a;
          }
          if (equal(a19->b, expr->b)) {
            return a;
          }
        }
      }
    }
    if (const Min *a29 = expr->b->as<Min>()) {
      if (equal(a4->a, a29->a)) {
        if (equal(a4->b, a29->b)) {
          return a;
        }
        return a;
        return min(min(a4->b, a29->b), a4->a);
        return min(a4->a, min(a4->b, a29->b));
      }
      if (equal(a4->b, a29->a)) {
        if (equal(a4->a, a29->b)) {
          return a;
        }
        return a;
        return min(min(a4->a, a29->b), a4->b);
      }
      if (equal(a4->a, a29->b)) {
        return a;
        return min(min(a4->b, a29->a), a4->a);
        return min(a4->a, min(a4->b, a29->a));
      }
      if (equal(a4->b, a29->b)) {
        return a;
        return min(min(a4->a, a29->a), a4->b);
      }
      return min(min(min(a4->a, a4->b), a29->a), a29->b);
    }
    if (is_const_v(a4->b)) {
      if (is_const_v(expr->b)) {
        if (evaluate_predicate(fold((expr->b >= a4->b)))) {
          return b;
        }
        return min(a4->a, fold(min(a4->b, expr->b)));
      }
      return min(min(a4->a, expr->b), a4->b);
    }
    if (const Min *a44 = a4->b->as<Min>()) {
      if (equal(a44->a, expr->b)) {
        return b;
        return min(a4->a, a44->a);
      }
      if (equal(a44->b, expr->b)) {
        return b;
        return min(a4->a, a44->b);
      }
    }
    if (const Broadcast *a164 = a4->b->as<Broadcast>()) {
      if (is_const_v(a164->lanes)) {
        if (const Broadcast *a165 = expr->b->as<Broadcast>()) {
          if (equal(a164->lanes, a165->lanes)) {
            return min(a4->a, broadcast(min(a164->value, a165->value), a164->lanes));
          }
        }
      }
    }
    if (const Div *a180 = a4->a->as<Div>()) {
      if (is_const_v(a180->b)) {
        if (const Div *a181 = expr->b->as<Div>()) {
          if (equal(a180->b, a181->b)) {
            if (evaluate_predicate(fold((a180->b > 0)))) {
              return min((min(a180->a, a181->a) / a180->b), a4->b);
            }
          }
        }
      }
    }
  }
  if (const Min *a24 = expr->b->as<Min>()) {
    if (equal(expr->a, a24->a)) {
      return b;
      return a;
    }
    if (equal(expr->a, a24->b)) {
      return b;
      return a;
    }
    if (const Min *a36 = a24->b->as<Min>()) {
      if (equal(expr->a, a36->a)) {
        return a;
        return min(a24->a, expr->a);
      }
      if (equal(expr->a, a36->b)) {
        return a;
        return min(a24->a, expr->a);
      }
    }
    if (const Min *a40 = a24->a->as<Min>()) {
      if (equal(expr->a, a40->a)) {
        return a;
        return min(expr->a, a24->b);
      }
      if (equal(expr->a, a40->b)) {
        return a;
        return min(expr->a, a24->b);
      }
    }
  }
  if (const Select *a59 = expr->a->as<Select>()) {
    if (const Min *a60 = a59->a->as<Min>()) {
      if (equal(a60->a, expr->b)) {
        return min(select(a59->cond, a60->b, a59->b), a60->a);
        return select(a59->cond, a60->a, min(a59->b, a60->a));
      }
      if (equal(a60->b, expr->b)) {
        return min(select(a59->cond, a60->a, a59->b), a60->b);
        return select(a59->cond, a60->b, min(a59->b, a60->b));
      }
    }
    if (const Min *a64 = a59->b->as<Min>()) {
      if (equal(a64->a, expr->b)) {
        return min(select(a59->cond, a59->a, a64->b), a64->a);
        return select(a59->cond, min(a59->a, a64->a), a64->a);
      }
      if (equal(a64->b, expr->b)) {
        return min(select(a59->cond, a59->a, a64->a), a64->b);
        return select(a59->cond, min(a59->a, a64->b), a64->b);
      }
    }
    if (const EQ *a187 = a59->cond->as<EQ>()) {
      if (is_const_v(a187->b)) {
        if (is_const_v(a59->a)) {
          if (equal(a187->a, a59->b)) {
            if (is_const_v(expr->b)) {
              if (evaluate_predicate(fold(((a187->b <= expr->b) && (a59->a <= expr->b))))) {
                return min(a187->a, expr->b);
              }
            }
            if (equal(a187->a, expr->b)) {
              if (evaluate_predicate(fold((a187->b < a59->a)))) {
                return select((a187->a == a187->b), a59->a, a187->a);
              }
              if (evaluate_predicate(fold((a59->a <= a187->b)))) {
                return a187->a;
              }
            }
          }
        }
      }
    }
    if (const Select *a225 = expr->b->as<Select>()) {
      if (equal(a59->cond, a225->cond)) {
        return select(a59->cond, min(a59->a, a225->a), min(a59->b, a225->b));
      }
    }
  }
  if (expr->is_no_overflow()) {
    if (const Min *a67 = expr->as<Min>()) {
      if (const Ramp *a68 = a67->a->as<Ramp>()) {
        if (is_const_v(a68->lanes)) {
          if (const Broadcast *a69 = a67->b->as<Broadcast>()) {
            if (equal(a68->lanes, a69->lanes)) {
              if (evaluate_predicate(fold(can_prove((((a68->base + (a68->stride * (a68->lanes - 1))) >= a69->value) && (a68->base >= a69->value)), simplifier)))) {
                return a;
              }
              if (evaluate_predicate(fold(can_prove((((a68->base + (a68->stride * (a68->lanes - 1))) <= a69->value) && (a68->base <= a69->value)), simplifier)))) {
                return b;
              }
            }
          }
        }
      }
      if (const Add *a74 = a67->a->as<Add>()) {
        if (const Mul *a75 = a74->a->as<Mul>()) {
          if (const Div *a76 = a75->a->as<Div>()) {
            if (const Add *a77 = a76->a->as<Add>()) {
              if (is_const_v(a77->b)) {
                if (is_const_v(a76->b)) {
                  if (equal(a76->b, a75->b)) {
                    if (is_const_v(a74->b)) {
                      if (equal(a77->a, a67->b)) {
                        if (evaluate_predicate(fold(((a76->b > 0) && ((a77->b + a74->b) >= (a76->b - 1)))))) {
                          return a;
                        }
                        if (evaluate_predicate(fold(((a76->b > 0) && ((a77->b + a74->b) <= 0))))) {
                          return b;
                        }
                      }
                    }
                  }
                }
              }
            }
            if (is_const_v(a76->b)) {
              if (equal(a76->b, a75->b)) {
                if (is_const_v(a74->b)) {
                  if (equal(a76->a, a67->b)) {
                    if (evaluate_predicate(fold(((a76->b > 0) && (a74->b >= (a76->b - 1)))))) {
                      return a;
                    }
                    if (evaluate_predicate(fold(((a76->b > 0) && (a74->b <= 0))))) {
                      return b;
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a139 = a74->a->as<Min>()) {
          if (is_const_v(a74->b)) {
            if (equal(a139->a, a67->b)) {
              if (evaluate_predicate(fold((a74->b <= 0)))) {
                return b;
              }
              if (evaluate_predicate(fold((a74->b < 0)))) {
                return min(a139->a, (a139->b + a74->b));
              }
              if (evaluate_predicate(fold((a74->b > 0)))) {
                return (min(a139->a, a139->b) + a74->b);
              }
            }
            if (equal(a139->b, a67->b)) {
              if (evaluate_predicate(fold((a74->b <= 0)))) {
                return b;
              }
              if (evaluate_predicate(fold((a74->b < 0)))) {
                return min((a139->a + a74->b), a139->b);
              }
              if (evaluate_predicate(fold((a74->b > 0)))) {
                return (min(a139->a, a139->b) + a74->b);
              }
            }
          }
        }
        if (is_const_v(a74->b)) {
          if (is_const_v(a67->b)) {
            return (min(a74->a, fold((a67->b - a74->b))) + a74->b);
          }
          if (const Add *a254 = a67->b->as<Add>()) {
            if (is_const_v(a254->b)) {
              if (evaluate_predicate(fold((a254->b > a74->b)))) {
                return (min(a74->a, (a254->a + fold((a254->b - a74->b)))) + a74->b);
              }
              if (evaluate_predicate(fold((a74->b > a254->b)))) {
                return (min((a74->a + fold((a74->b - a254->b))), a254->a) + a254->b);
              }
            }
          }
        }
        if (const Add *a272 = a67->b->as<Add>()) {
          if (equal(a74->a, a272->a)) {
            return (a74->a + min(a74->b, a272->b));
          }
          if (equal(a74->a, a272->b)) {
            return (a74->a + min(a74->b, a272->a));
          }
          if (equal(a74->b, a272->a)) {
            return (min(a74->a, a272->b) + a74->b);
          }
          if (equal(a74->b, a272->b)) {
            return (min(a74->a, a272->a) + a74->b);
          }
          if (const Add *a371 = a272->a->as<Add>()) {
            if (equal(a74->a, a371->b)) {
              return (a74->a + min((a371->a + a272->b), a74->b));
            }
            if (equal(a74->a, a371->a)) {
              return (a74->a + min((a371->b + a272->b), a74->b));
            }
            if (equal(a74->b, a371->b)) {
              return (min((a371->a + a272->b), a74->a) + a74->b);
            }
            if (equal(a74->b, a371->a)) {
              return (min((a371->b + a272->b), a74->a) + a74->b);
            }
          }
        }
        if (equal(a74->b, a67->b)) {
          return (min(a74->a, 0) + a74->b);
        }
        if (equal(a74->a, a67->b)) {
          return (a74->a + min(a74->b, 0));
        }
        if (const Add *a348 = a74->a->as<Add>()) {
          if (const Add *a349 = a67->b->as<Add>()) {
            if (equal(a348->a, a349->a)) {
              return (a348->a + min((a348->b + a74->b), a349->b));
            }
            if (equal(a348->b, a349->a)) {
              return (min((a348->a + a74->b), a349->b) + a348->b);
            }
            if (equal(a348->a, a349->b)) {
              return (a348->a + min((a348->b + a74->b), a349->a));
            }
            if (equal(a348->b, a349->b)) {
              return (min((a348->a + a74->b), a349->a) + a348->b);
            }
          }
          if (equal(a348->a, a67->b)) {
            return (a348->a + min((a348->b + a74->b), 0));
          }
          if (equal(a348->b, a67->b)) {
            return (a348->b + min((a348->a + a74->b), 0));
          }
        }
        if (const Sub *a419 = a74->a->as<Sub>()) {
          if (equal(a419->a, a67->b)) {
            return (min((a74->b - a419->b), 0) + a419->a);
          }
        }
        if (const Sub *a422 = a74->b->as<Sub>()) {
          if (equal(a422->a, a67->b)) {
            return (min((a74->a - a422->b), 0) + a422->a);
          }
        }
      }
      if (const Add *a79 = a67->b->as<Add>()) {
        if (const Mul *a80 = a79->a->as<Mul>()) {
          if (const Div *a81 = a80->a->as<Div>()) {
            if (const Add *a82 = a81->a->as<Add>()) {
              if (equal(a67->a, a82->a)) {
                if (is_const_v(a82->b)) {
                  if (is_const_v(a81->b)) {
                    if (equal(a81->b, a80->b)) {
                      if (is_const_v(a79->b)) {
                        if (evaluate_predicate(fold(((a81->b > 0) && ((a82->b + a79->b) >= (a81->b - 1)))))) {
                          return b;
                        }
                        if (evaluate_predicate(fold(((a81->b > 0) && ((a82->b + a79->b) <= 0))))) {
                          return a;
                        }
                      }
                    }
                  }
                }
              }
            }
            if (equal(a67->a, a81->a)) {
              if (is_const_v(a81->b)) {
                if (equal(a81->b, a80->b)) {
                  if (is_const_v(a79->b)) {
                    if (evaluate_predicate(fold(((a81->b > 0) && (a79->b >= (a81->b - 1)))))) {
                      return b;
                    }
                    if (evaluate_predicate(fold(((a81->b > 0) && (a79->b <= 0))))) {
                      return a;
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a133 = a79->a->as<Min>()) {
          if (equal(a67->a, a133->a)) {
            if (is_const_v(a79->b)) {
              if (evaluate_predicate(fold((a79->b <= 0)))) {
                return a;
              }
              if (evaluate_predicate(fold((a79->b < 0)))) {
                return min(a67->a, (a133->b + a79->b));
              }
              if (evaluate_predicate(fold((a79->b > 0)))) {
                return (min(a67->a, a133->b) + a79->b);
              }
            }
          }
          if (equal(a67->a, a133->b)) {
            if (is_const_v(a79->b)) {
              if (evaluate_predicate(fold((a79->b <= 0)))) {
                return a;
              }
              if (evaluate_predicate(fold((a79->b < 0)))) {
                return min(a67->a, (a133->a + a79->b));
              }
              if (evaluate_predicate(fold((a79->b > 0)))) {
                return (min(a67->a, a133->a) + a79->b);
              }
            }
          }
        }
        if (equal(a67->a, a79->a)) {
          return (a67->a + min(a79->b, 0));
        }
        if (equal(a67->a, a79->b)) {
          return (a67->a + min(a79->a, 0));
        }
        if (const Add *a386 = a79->a->as<Add>()) {
          if (equal(a67->a, a386->b)) {
            return (a67->a + min((a386->a + a79->b), 0));
          }
          if (equal(a67->a, a386->a)) {
            return (a67->a + min((a386->b + a79->b), 0));
          }
        }
        if (const Sub *a410 = a79->a->as<Sub>()) {
          if (equal(a67->a, a410->a)) {
            return (a67->a + min((a79->b - a410->b), 0));
          }
        }
        if (const Sub *a413 = a79->b->as<Sub>()) {
          if (equal(a67->a, a413->a)) {
            return (a67->a + min((a79->a - a413->b), 0));
          }
        }
      }
      if (const Mul *a94 = a67->a->as<Mul>()) {
        if (const Div *a95 = a94->a->as<Div>()) {
          if (is_const_v(a95->b)) {
            if (equal(a95->b, a94->b)) {
              if (const Add *a96 = a67->b->as<Add>()) {
                if (const Mul *a97 = a96->a->as<Mul>()) {
                  if (const Div *a98 = a97->a->as<Div>()) {
                    if (equal(a95->a, a98->a)) {
                      if (is_const_v(a98->b)) {
                        if (equal(a98->b, a97->b)) {
                          if (is_const_v(a96->b)) {
                            if (evaluate_predicate(fold((((a96->b >= a98->b) && (a98->b > 0)) && (a95->b != 0))))) {
                              return b;
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
          if (const Add *a110 = a95->a->as<Add>()) {
            if (is_const_v(a110->b)) {
              if (is_const_v(a95->b)) {
                if (equal(a95->b, a94->b)) {
                  if (equal(a110->a, a67->b)) {
                    if (evaluate_predicate(fold(((a95->b > 0) && (a110->b >= (a95->b - 1)))))) {
                      return a;
                    }
                    if (evaluate_predicate(fold(((a95->b > 0) && (a110->b <= 0))))) {
                      return b;
                    }
                  }
                  if (const Add *a472 = a67->b->as<Add>()) {
                    if (equal(a110->a, a472->a)) {
                      if (is_const_v(a472->b)) {
                        if (evaluate_predicate(fold(((a95->b > 0) && ((a110->b + 1) >= (a95->b + a472->b)))))) {
                          return (((a110->a + a110->b) / a95->b) * a95->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a292 = a94->a->as<Add>()) {
          if (const Mul *a293 = a292->a->as<Mul>()) {
            if (is_const_v(a293->b)) {
              if (is_const_v(a94->b)) {
                if (const Add *a294 = a67->b->as<Add>()) {
                  if (const Mul *a295 = a294->a->as<Mul>()) {
                    if (equal(a293->a, a295->a)) {
                      if (is_const_v(a295->b)) {
                        if (evaluate_predicate(fold(((a293->b * a94->b) == a295->b)))) {
                          return (min((a292->b * a94->b), a294->b) + (a293->a * a295->b));
                        }
                      }
                    }
                  }
                  if (const Mul *a307 = a294->b->as<Mul>()) {
                    if (equal(a293->a, a307->a)) {
                      if (is_const_v(a307->b)) {
                        if (evaluate_predicate(fold(((a293->b * a94->b) == a307->b)))) {
                          return (min((a292->b * a94->b), a294->a) + (a293->a * a307->b));
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a299 = a292->b->as<Mul>()) {
            if (is_const_v(a299->b)) {
              if (is_const_v(a94->b)) {
                if (const Add *a300 = a67->b->as<Add>()) {
                  if (const Mul *a301 = a300->a->as<Mul>()) {
                    if (equal(a299->a, a301->a)) {
                      if (is_const_v(a301->b)) {
                        if (evaluate_predicate(fold(((a299->b * a94->b) == a301->b)))) {
                          return (min((a292->a * a94->b), a300->b) + (a299->a * a301->b));
                        }
                      }
                    }
                  }
                  if (const Mul *a313 = a300->b->as<Mul>()) {
                    if (equal(a299->a, a313->a)) {
                      if (is_const_v(a313->b)) {
                        if (evaluate_predicate(fold(((a299->b * a94->b) == a313->b)))) {
                          return (min((a292->a * a94->b), a300->a) + (a299->a * a313->b));
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a94->b)) {
          if (is_const_v(a67->b)) {
            if (evaluate_predicate(fold(((a94->b > 0) && ((a67->b % a94->b) == 0))))) {
              return (min(a94->a, fold((a67->b / a94->b))) * a94->b);
            }
            if (evaluate_predicate(fold(((a94->b < 0) && ((a67->b % a94->b) == 0))))) {
              return (min(a94->a, fold((a67->b / a94->b))) * a94->b);
            }
          }
          if (const Mul *a432 = a67->b->as<Mul>()) {
            if (is_const_v(a432->b)) {
              if (evaluate_predicate(fold(((a94->b > 0) && ((a432->b % a94->b) == 0))))) {
                return (min(a94->a, (a432->a * fold((a432->b / a94->b)))) * a94->b);
              }
              if (evaluate_predicate(fold(((a94->b < 0) && ((a432->b % a94->b) == 0))))) {
                return (min(a94->a, (a432->a * fold((a432->b / a94->b)))) * a94->b);
              }
              if (evaluate_predicate(fold(((a432->b > 0) && ((a94->b % a432->b) == 0))))) {
                return (min((a94->a * fold((a94->b / a432->b))), a432->a) * a432->b);
              }
              if (evaluate_predicate(fold(((a432->b < 0) && ((a94->b % a432->b) == 0))))) {
                return (min((a94->a * fold((a94->b / a432->b))), a432->a) * a432->b);
              }
            }
          }
          if (const Add *a444 = a67->b->as<Add>()) {
            if (const Mul *a445 = a444->a->as<Mul>()) {
              if (equal(a94->b, a445->b)) {
                if (is_const_v(a444->b)) {
                  if (evaluate_predicate(fold(((a94->b > 0) && ((a444->b % a94->b) == 0))))) {
                    return (min(a94->a, (a445->a + fold((a444->b / a94->b)))) * a94->b);
                  }
                  if (evaluate_predicate(fold(((a94->b < 0) && ((a444->b % a94->b) == 0))))) {
                    return (min(a94->a, (a445->a + fold((a444->b / a94->b)))) * a94->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Mul *a112 = a67->b->as<Mul>()) {
        if (const Div *a113 = a112->a->as<Div>()) {
          if (const Add *a114 = a113->a->as<Add>()) {
            if (equal(a67->a, a114->a)) {
              if (is_const_v(a114->b)) {
                if (is_const_v(a113->b)) {
                  if (equal(a113->b, a112->b)) {
                    if (evaluate_predicate(fold(((a113->b > 0) && (a114->b >= (a113->b - 1)))))) {
                      return b;
                    }
                    if (evaluate_predicate(fold(((a113->b > 0) && (a114->b <= 0))))) {
                      return a;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a259 = a67->a->as<Min>()) {
        if (const Add *a260 = a67->b->as<Add>()) {
          if (equal(a259->a, a260->a)) {
            if (is_const_v(a260->b)) {
              if (evaluate_predicate(fold((a260->b > 0)))) {
                return min((a259->a + a260->b), a259->b);
              }
              if (evaluate_predicate(fold((a260->b < 0)))) {
                return min(a259->a, a259->b);
              }
            }
          }
          if (equal(a259->b, a260->a)) {
            if (is_const_v(a260->b)) {
              if (evaluate_predicate(fold((a260->b > 0)))) {
                return min(a259->a, (a259->b + a260->b));
              }
              if (evaluate_predicate(fold((a260->b < 0)))) {
                return min(a259->a, a259->b);
              }
            }
          }
        }
        if (const Add *a316 = a259->a->as<Add>()) {
          if (const Add *a317 = a67->b->as<Add>()) {
            if (equal(a316->a, a317->a)) {
              return min((a316->a + min(a316->b, a317->b)), a259->b);
            }
            if (equal(a316->a, a317->b)) {
              return min((a316->a + min(a316->b, a317->a)), a259->b);
            }
            if (equal(a316->b, a317->a)) {
              return min((min(a316->a, a317->b) + a316->b), a259->b);
            }
            if (equal(a316->b, a317->b)) {
              return min((min(a316->a, a317->a) + a316->b), a259->b);
            }
          }
        }
        if (const Add *a320 = a259->b->as<Add>()) {
          if (const Add *a321 = a67->b->as<Add>()) {
            if (equal(a320->a, a321->a)) {
              return min((a320->a + min(a320->b, a321->b)), a259->a);
            }
            if (equal(a320->a, a321->b)) {
              return min((a320->a + min(a320->b, a321->a)), a259->a);
            }
            if (equal(a320->b, a321->a)) {
              return min((min(a320->a, a321->b) + a320->b), a259->a);
            }
            if (equal(a320->b, a321->b)) {
              return min((min(a320->a, a321->a) + a320->b), a259->a);
            }
          }
        }
      }
      if (const Sub *a391 = a67->a->as<Sub>()) {
        if (const Sub *a392 = a67->b->as<Sub>()) {
          if (equal(a391->b, a392->b)) {
            return (min(a391->a, a392->a) - a391->b);
          }
          if (equal(a391->a, a392->a)) {
            return (a391->a - min(a391->b, a392->b));
          }
        }
        if (const Add *a398 = a67->b->as<Add>()) {
          if (const Sub *a399 = a398->a->as<Sub>()) {
            if (equal(a391->b, a399->b)) {
              return (min(a391->a, (a399->a + a398->b)) - a391->b);
            }
          }
          if (const Sub *a403 = a398->b->as<Sub>()) {
            if (equal(a391->b, a403->b)) {
              return (min(a391->a, (a398->a + a403->a)) - a391->b);
            }
          }
        }
        if (equal(a391->a, a67->b)) {
          return (a391->a - min(a391->b, 0));
        }
        if (const Sub *a425 = a391->a->as<Sub>()) {
          if (equal(a425->a, a67->b)) {
            return (a425->a - min((a425->b + a391->b), 0));
          }
        }
        if (is_const_v(a391->a)) {
          if (is_const_v(a67->b)) {
            return (a391->a - min(a391->b, fold((a391->a - a67->b))));
          }
        }
      }
      if (const Sub *a405 = a67->b->as<Sub>()) {
        if (equal(a67->a, a405->a)) {
          return (a67->a - min(a405->b, 0));
        }
        if (const Sub *a416 = a405->a->as<Sub>()) {
          if (equal(a67->a, a416->a)) {
            return (a67->a - min((a416->b + a405->b), 0));
          }
        }
      }
      if (const Div *a451 = a67->a->as<Div>()) {
        if (is_const_v(a451->b)) {
          if (const Div *a452 = a67->b->as<Div>()) {
            if (equal(a451->b, a452->b)) {
              if (evaluate_predicate(fold((a451->b > 0)))) {
                return (min(a451->a, a452->a) / a451->b);
              }
              if (evaluate_predicate(fold((a451->b < 0)))) {
                return (min(a451->a, a452->a) / a451->b);
              }
            }
          }
          if (is_const_v(a67->b)) {
            if (evaluate_predicate(fold(((a451->b > 0) && !(overflows((a67->b * a451->b))))))) {
              return (min(a451->a, fold((a67->b * a451->b))) / a451->b);
            }
            if (evaluate_predicate(fold(((a451->b < 0) && !(overflows((a67->b * a451->b))))))) {
              return (min(a451->a, fold((a67->b * a451->b))) / a451->b);
            }
          }
          if (const Add *a462 = a67->b->as<Add>()) {
            if (const Div *a463 = a462->a->as<Div>()) {
              if (equal(a451->b, a463->b)) {
                if (is_const_v(a462->b)) {
                  if (evaluate_predicate(fold(((a451->b > 0) && !(overflows((a462->b * a451->b))))))) {
                    return (min(a451->a, (a463->a + fold((a462->b * a451->b)))) / a451->b);
                  }
                  if (evaluate_predicate(fold(((a451->b < 0) && !(overflows((a462->b * a451->b))))))) {
                    return (min(a451->a, (a463->a + fold((a462->b * a451->b)))) / a451->b);
                  }
                }
              }
            }
          }
          if (const Mul *a487 = a67->b->as<Mul>()) {
            if (const Div *a488 = a487->a->as<Div>()) {
              if (const Add *a489 = a488->a->as<Add>()) {
                if (equal(a451->a, a489->a)) {
                  if (is_const_v(a489->b)) {
                    if (is_const_v(a488->b)) {
                      if (is_const_v(a487->b)) {
                        if (evaluate_predicate(fold(((((a489->b <= 0) && (a451->b > 0)) && (a488->b > 0)) && ((a451->b * a487->b) == a488->b))))) {
                          return (a451->a / a451->b);
                        }
                        if (evaluate_predicate(fold((((((a488->b - a451->b) <= a489->b) && (a451->b > 0)) && (a488->b > 0)) && ((a451->b * a487->b) == a488->b))))) {
                          return (((a451->a + a489->b) / a488->b) * a487->b);
                        }
                      }
                    }
                  }
                }
              }
              if (equal(a451->a, a488->a)) {
                if (is_const_v(a488->b)) {
                  if (is_const_v(a487->b)) {
                    if (evaluate_predicate(fold((((a451->b > 0) && (a488->b > 0)) && ((a451->b * a487->b) == a488->b))))) {
                      return (a451->a / a451->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a475 = a451->a->as<Add>()) {
          if (is_const_v(a475->b)) {
            if (is_const_v(a451->b)) {
              if (const Mul *a476 = a67->b->as<Mul>()) {
                if (const Div *a477 = a476->a->as<Div>()) {
                  if (const Add *a478 = a477->a->as<Add>()) {
                    if (equal(a475->a, a478->a)) {
                      if (is_const_v(a478->b)) {
                        if (is_const_v(a477->b)) {
                          if (is_const_v(a476->b)) {
                            if (evaluate_predicate(fold(((((a478->b <= a475->b) && (a451->b > 0)) && (a477->b > 0)) && ((a451->b * a476->b) == a477->b))))) {
                              return ((a475->a + a475->b) / a451->b);
                            }
                            if (evaluate_predicate(fold(((((((a475->b + a477->b) - a451->b) <= a478->b) && (a451->b > 0)) && (a477->b > 0)) && ((a451->b * a476->b) == a477->b))))) {
                              return (((a475->a + a478->b) / a477->b) * a476->b);
                            }
                          }
                        }
                      }
                    }
                  }
                  if (equal(a475->a, a477->a)) {
                    if (is_const_v(a477->b)) {
                      if (is_const_v(a476->b)) {
                        if (evaluate_predicate(fold(((((0 <= a475->b) && (a451->b > 0)) && (a477->b > 0)) && ((a451->b * a476->b) == a477->b))))) {
                          return ((a475->a + a475->b) / a451->b);
                        }
                        if (evaluate_predicate(fold(((((((a475->b + a477->b) - a451->b) <= 0) && (a451->b > 0)) && (a477->b > 0)) && ((a451->b * a476->b) == a477->b))))) {
                          return ((a475->a / a477->b) * a476->b);
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
  }
  if (expr->is_no_overflow_int()) {
    if (const Min *a143 = expr->as<Min>()) {
      if (const Min *a144 = a143->a->as<Min>()) {
        if (const Sub *a145 = a144->a->as<Sub>()) {
          if (is_const_v(a145->a)) {
            if (equal(a145->b, a144->b)) {
              if (is_const_v(a143->b)) {
                if (evaluate_predicate(fold(((2 * a143->b) >= (a145->a - 1))))) {
                  return b;
                }
              }
            }
          }
        }
        if (const Sub *a148 = a144->b->as<Sub>()) {
          if (is_const_v(a148->a)) {
            if (equal(a144->a, a148->b)) {
              if (is_const_v(a143->b)) {
                if (evaluate_predicate(fold(((2 * a143->b) >= (a148->a - 1))))) {
                  return b;
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a161 = expr->a->as<Broadcast>()) {
    if (is_const_v(a161->lanes)) {
      if (const Broadcast *a162 = expr->b->as<Broadcast>()) {
        if (equal(a161->lanes, a162->lanes)) {
          return broadcast(min(a161->value, a162->value), a161->lanes);
        }
      }
    }
  }
  if (const Select *a182 = expr->b->as<Select>()) {
    if (const EQ *a183 = a182->cond->as<EQ>()) {
      if (equal(expr->a, a183->a)) {
        if (is_const_v(a183->b)) {
          if (is_const_v(a182->a)) {
            if (equal(expr->a, a182->b)) {
              if (evaluate_predicate(fold((a183->b < a182->a)))) {
                return select((expr->a == a183->b), a182->a, expr->a);
              }
              if (evaluate_predicate(fold((a182->a <= a183->b)))) {
                return expr->a;
              }
            }
          }
        }
      }
    }
    if (const Min *a213 = a182->a->as<Min>()) {
      if (equal(expr->a, a213->b)) {
        return select(a182->cond, expr->a, min(expr->a, a182->b));
      }
      if (equal(expr->a, a213->a)) {
        return select(a182->cond, expr->a, min(expr->a, a182->b));
      }
    }
    if (const Min *a221 = a182->b->as<Min>()) {
      if (equal(expr->a, a221->b)) {
        return select(a182->cond, min(expr->a, a182->a), expr->a);
      }
      if (equal(expr->a, a221->a)) {
        return select(a182->cond, min(expr->a, a182->a), expr->a);
      }
    }
  }
  return expr;
}
