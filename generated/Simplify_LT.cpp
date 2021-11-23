#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_LT(const LT *expr, Simplify *simplifier) {
  if (is_const_v(expr->a)) {
    if (is_const_v(expr->b)) {
      return fold((expr->a < expr->b));
    }
    if (const Mod *a31 = expr->b->as<Mod>()) {
      if (is_const_v(a31->b)) {
        if (evaluate_predicate(fold((((expr->a + 2) == a31->b) && (a31->b > 0))))) {
          return ((a31->a % a31->b) == fold((a31->b - 1)));
        }
      }
    }
    if (const Mul *a289 = expr->b->as<Mul>()) {
      if (is_const_v(a289->b)) {
        if (evaluate_predicate(fold((a289->b > 0)))) {
          return (fold((expr->a / a289->b)) < a289->a);
        }
      }
    }
  }
  if (equal(expr->a, expr->b)) {
    return false;
  }
  if (const Min *a0 = expr->a->as<Min>()) {
    if (equal(a0->a, expr->b)) {
      return false;
    }
    if (equal(a0->b, expr->b)) {
      return false;
    }
    if (const Min *a5 = expr->b->as<Min>()) {
      if (equal(a0->a, a5->b)) {
        return false;
      }
      if (equal(a0->a, a5->a)) {
        return false;
      }
      if (equal(a0->b, a5->b)) {
        return false;
      }
      if (equal(a0->b, a5->a)) {
        return false;
      }
    }
  }
  if (const Min *a2 = expr->b->as<Min>()) {
    if (equal(expr->a, a2->a)) {
      return false;
    }
    if (equal(expr->a, a2->b)) {
      return false;
    }
  }
  if (expr->is_operand_no_overflow()) {
    if (const LT *a12 = expr->as<LT>()) {
      if (const Ramp *a13 = a12->a->as<Ramp>()) {
        if (is_const_v(a13->stride)) {
          if (is_const_v(a13->lanes)) {
            if (const Broadcast *a14 = a12->b->as<Broadcast>()) {
              if (equal(a13->lanes, a14->lanes)) {
                if (evaluate_predicate(fold(can_prove(((a13->base + fold(min(0, (a13->stride * (a13->lanes - 1))))) < a14->value), simplifier)))) {
                  return true;
                }
                if (evaluate_predicate(fold(can_prove(((a13->base + fold(min(0, (a13->stride * (a13->lanes - 1))))) >= a14->value), simplifier)))) {
                  return false;
                }
              }
            }
          }
        }
        if (is_const_v(a13->lanes)) {
          if (const Ramp *a34 = a12->b->as<Ramp>()) {
            if (equal(a13->stride, a34->stride)) {
              if (equal(a13->lanes, a34->lanes)) {
                return broadcast((a13->base < a34->base), a13->lanes);
              }
            }
            if (equal(a13->lanes, a34->lanes)) {
              return (ramp((a13->base - a34->base), (a13->stride - a34->stride), a13->lanes) < 0);
            }
          }
          if (const Broadcast *a569 = a12->b->as<Broadcast>()) {
            if (const Add *a570 = a569->value->as<Add>()) {
              if (equal(a13->base, a570->a)) {
                if (equal(a13->lanes, a569->lanes)) {
                  return (ramp(0, a13->stride, a13->lanes) < broadcast(a570->b, a13->lanes));
                }
              }
              if (equal(a13->base, a570->b)) {
                if (equal(a13->lanes, a569->lanes)) {
                  return (ramp(0, a13->stride, a13->lanes) < broadcast(a570->a, a13->lanes));
                }
              }
            }
            if (const Sub *a578 = a569->value->as<Sub>()) {
              if (equal(a13->base, a578->a)) {
                if (equal(a13->lanes, a569->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a13->base, 0))))) {
                    return (ramp(0, a13->stride, a13->lanes) < broadcast((0 - a578->b), a13->lanes));
                  }
                }
              }
            }
          }
        }
        if (const Add *a539 = a13->base->as<Add>()) {
          if (is_const_v(a13->lanes)) {
            if (const Broadcast *a540 = a12->b->as<Broadcast>()) {
              if (const Add *a541 = a540->value->as<Add>()) {
                if (equal(a539->a, a541->a)) {
                  if (equal(a13->lanes, a540->lanes)) {
                    return (ramp(a539->b, a13->stride, a13->lanes) < broadcast(a541->b, a13->lanes));
                  }
                }
                if (equal(a539->b, a541->a)) {
                  if (equal(a13->lanes, a540->lanes)) {
                    return (ramp(a539->a, a13->stride, a13->lanes) < broadcast(a541->b, a13->lanes));
                  }
                }
                if (equal(a539->a, a541->b)) {
                  if (equal(a13->lanes, a540->lanes)) {
                    return (ramp(a539->b, a13->stride, a13->lanes) < broadcast(a541->a, a13->lanes));
                  }
                }
                if (equal(a539->b, a541->b)) {
                  if (equal(a13->lanes, a540->lanes)) {
                    return (ramp(a539->a, a13->stride, a13->lanes) < broadcast(a541->a, a13->lanes));
                  }
                }
              }
              if (equal(a539->a, a540->value)) {
                if (equal(a13->lanes, a540->lanes)) {
                  return (ramp(a539->b, a13->stride, a13->lanes) < 0);
                }
              }
              if (equal(a539->b, a540->value)) {
                if (equal(a13->lanes, a540->lanes)) {
                  return (ramp(a539->a, a13->stride, a13->lanes) < 0);
                }
              }
            }
          }
        }
        if (const Sub *a559 = a13->base->as<Sub>()) {
          if (is_const_v(a13->lanes)) {
            if (const Broadcast *a560 = a12->b->as<Broadcast>()) {
              if (const Sub *a561 = a560->value->as<Sub>()) {
                if (equal(a559->a, a561->a)) {
                  if (equal(a13->lanes, a560->lanes)) {
                    if (evaluate_predicate(fold(!(is_const(a559->a, 0))))) {
                      return (ramp((0 - a559->b), a13->stride, a13->lanes) < broadcast((0 - a561->b), a13->lanes));
                    }
                  }
                }
                if (equal(a559->b, a561->b)) {
                  if (equal(a13->lanes, a560->lanes)) {
                    return (ramp(a559->a, a13->stride, a13->lanes) < broadcast(a561->a, a13->lanes));
                  }
                }
              }
              if (equal(a559->a, a560->value)) {
                if (equal(a13->lanes, a560->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a559->a, 0))))) {
                    return (ramp((0 - a559->b), a13->stride, a13->lanes) < 0);
                  }
                }
              }
            }
          }
        }
      }
      if (const Broadcast *a19 = a12->a->as<Broadcast>()) {
        if (is_const_v(a19->lanes)) {
          if (const Ramp *a20 = a12->b->as<Ramp>()) {
            if (is_const_v(a20->stride)) {
              if (equal(a19->lanes, a20->lanes)) {
                if (evaluate_predicate(fold(can_prove((a19->value < (a20->base + fold(min(0, (a20->stride * (a19->lanes - 1)))))), simplifier)))) {
                  return true;
                }
                if (evaluate_predicate(fold(can_prove((a19->value >= (a20->base + fold(min(0, (a20->stride * (a19->lanes - 1)))))), simplifier)))) {
                  return false;
                }
              }
            }
            if (const Add *a636 = a20->base->as<Add>()) {
              if (equal(a19->value, a636->a)) {
                if (equal(a19->lanes, a20->lanes)) {
                  return (0 < ramp(a636->b, a20->stride, a19->lanes));
                }
              }
              if (equal(a19->value, a636->b)) {
                if (equal(a19->lanes, a20->lanes)) {
                  return (0 < ramp(a636->a, a20->stride, a19->lanes));
                }
              }
            }
            if (const Sub *a644 = a20->base->as<Sub>()) {
              if (equal(a19->value, a644->a)) {
                if (equal(a19->lanes, a20->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a19->value, 0))))) {
                    return (0 < ramp((0 - a644->b), a20->stride, a19->lanes));
                  }
                }
              }
            }
          }
        }
        if (const Add *a593 = a19->value->as<Add>()) {
          if (is_const_v(a19->lanes)) {
            if (const Ramp *a594 = a12->b->as<Ramp>()) {
              if (const Add *a595 = a594->base->as<Add>()) {
                if (equal(a593->a, a595->a)) {
                  if (equal(a19->lanes, a594->lanes)) {
                    return (broadcast(a593->b, a19->lanes) < ramp(a595->b, a594->stride, a19->lanes));
                  }
                }
                if (equal(a593->a, a595->b)) {
                  if (equal(a19->lanes, a594->lanes)) {
                    return (broadcast(a593->b, a19->lanes) < ramp(a595->a, a594->stride, a19->lanes));
                  }
                }
                if (equal(a593->b, a595->a)) {
                  if (equal(a19->lanes, a594->lanes)) {
                    return (broadcast(a593->a, a19->lanes) < ramp(a595->b, a594->stride, a19->lanes));
                  }
                }
                if (equal(a593->b, a595->b)) {
                  if (equal(a19->lanes, a594->lanes)) {
                    return (broadcast(a593->a, a19->lanes) < ramp(a595->a, a594->stride, a19->lanes));
                  }
                }
              }
              if (equal(a593->a, a594->base)) {
                if (equal(a19->lanes, a594->lanes)) {
                  return (broadcast(a593->b, a19->lanes) < ramp(0, a594->stride, a19->lanes));
                }
              }
              if (equal(a593->b, a594->base)) {
                if (equal(a19->lanes, a594->lanes)) {
                  return (broadcast(a593->a, a19->lanes) < ramp(0, a594->stride, a19->lanes));
                }
              }
            }
          }
        }
        if (const Sub *a613 = a19->value->as<Sub>()) {
          if (is_const_v(a19->lanes)) {
            if (const Ramp *a614 = a12->b->as<Ramp>()) {
              if (const Sub *a615 = a614->base->as<Sub>()) {
                if (equal(a613->a, a615->a)) {
                  if (equal(a19->lanes, a614->lanes)) {
                    if (evaluate_predicate(fold(!(is_const(a613->a, 0))))) {
                      return (broadcast((0 - a613->b), a19->lanes) < ramp((0 - a615->b), a614->stride, a19->lanes));
                    }
                  }
                }
                if (equal(a613->b, a615->b)) {
                  if (equal(a19->lanes, a614->lanes)) {
                    return (broadcast(a613->a, a19->lanes) < ramp(a615->a, a614->stride, a19->lanes));
                  }
                }
              }
              if (equal(a613->a, a614->base)) {
                if (equal(a19->lanes, a614->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a613->a, 0))))) {
                    return (broadcast((0 - a613->b), a19->lanes) < ramp(0, a614->stride, a19->lanes));
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a36 = a12->a->as<Add>()) {
        if (is_const_v(a36->b)) {
          return (a36->a < (a12->b + fold((0 - a36->b))));
        }
        if (const Sub *a47 = a36->a->as<Sub>()) {
          return ((a47->a + a36->b) < (a47->b + a12->b));
        }
        if (const Sub *a50 = a36->b->as<Sub>()) {
          return ((a50->a + a36->a) < (a50->b + a12->b));
        }
        if (const Add *a59 = a36->a->as<Add>()) {
          if (const Sub *a60 = a59->a->as<Sub>()) {
            return (((a60->a + a59->b) + a36->b) < (a12->b + a60->b));
          }
          if (const Sub *a64 = a59->b->as<Sub>()) {
            return (((a64->a + a59->a) + a36->b) < (a12->b + a64->b));
          }
          if (equal(a59->a, a12->b)) {
            return ((a59->b + a36->b) < 0);
          }
          if (equal(a59->b, a12->b)) {
            return ((a59->a + a36->b) < 0);
          }
          if (const Add *a136 = a12->b->as<Add>()) {
            if (equal(a59->a, a136->a)) {
              return ((a59->b + a36->b) < a136->b);
            }
            if (equal(a59->b, a136->a)) {
              return ((a59->a + a36->b) < a136->b);
            }
            if (equal(a59->a, a136->b)) {
              return ((a59->b + a36->b) < a136->a);
            }
            if (equal(a59->b, a136->b)) {
              return ((a59->a + a36->b) < a136->a);
            }
            if (const Add *a201 = a136->a->as<Add>()) {
              if (equal(a59->a, a201->a)) {
                return ((a59->b + a36->b) < (a201->b + a136->b));
              }
              if (equal(a59->b, a201->a)) {
                return ((a59->a + a36->b) < (a201->b + a136->b));
              }
              if (equal(a59->a, a201->b)) {
                return ((a59->b + a36->b) < (a201->a + a136->b));
              }
              if (equal(a59->b, a201->b)) {
                return ((a59->a + a36->b) < (a201->a + a136->b));
              }
            }
            if (const Add *a241 = a136->b->as<Add>()) {
              if (equal(a59->a, a241->a)) {
                return ((a59->b + a36->b) < (a241->b + a136->a));
              }
              if (equal(a59->b, a241->a)) {
                return ((a59->a + a36->b) < (a241->b + a136->a));
              }
              if (equal(a59->a, a241->b)) {
                return ((a59->b + a36->b) < (a241->a + a136->a));
              }
              if (equal(a59->b, a241->b)) {
                return ((a59->a + a36->b) < (a241->a + a136->a));
              }
            }
          }
        }
        if (const Add *a67 = a36->b->as<Add>()) {
          if (const Sub *a68 = a67->a->as<Sub>()) {
            return (((a68->a + a67->b) + a36->a) < (a12->b + a68->b));
          }
          if (const Sub *a72 = a67->b->as<Sub>()) {
            return (((a72->a + a67->a) + a36->a) < (a12->b + a72->b));
          }
          if (equal(a67->a, a12->b)) {
            return ((a36->a + a67->b) < 0);
          }
          if (equal(a67->b, a12->b)) {
            return ((a36->a + a67->a) < 0);
          }
          if (const Add *a144 = a12->b->as<Add>()) {
            if (equal(a67->a, a144->a)) {
              return ((a67->b + a36->a) < a144->b);
            }
            if (equal(a67->b, a144->a)) {
              return ((a67->a + a36->a) < a144->b);
            }
            if (equal(a67->a, a144->b)) {
              return ((a67->b + a36->a) < a144->a);
            }
            if (equal(a67->b, a144->b)) {
              return ((a67->a + a36->a) < a144->a);
            }
            if (const Add *a221 = a144->a->as<Add>()) {
              if (equal(a67->a, a221->a)) {
                return ((a67->b + a36->a) < (a221->b + a144->b));
              }
              if (equal(a67->b, a221->a)) {
                return ((a67->a + a36->a) < (a221->b + a144->b));
              }
              if (equal(a67->a, a221->b)) {
                return ((a67->b + a36->a) < (a221->a + a144->b));
              }
              if (equal(a67->b, a221->b)) {
                return ((a67->a + a36->a) < (a221->a + a144->b));
              }
            }
            if (const Add *a261 = a144->b->as<Add>()) {
              if (equal(a67->a, a261->a)) {
                return ((a67->b + a36->a) < (a261->b + a144->a));
              }
              if (equal(a67->b, a261->a)) {
                return ((a67->a + a36->a) < (a261->b + a144->a));
              }
              if (equal(a67->a, a261->b)) {
                return ((a67->b + a36->a) < (a261->a + a144->a));
              }
              if (equal(a67->b, a261->b)) {
                return ((a67->a + a36->a) < (a261->a + a144->a));
              }
            }
          }
        }
        if (equal(a36->a, a12->b)) {
          return (a36->b < 0);
        }
        if (equal(a36->b, a12->b)) {
          return (a36->a < 0);
        }
        if (const Add *a123 = a12->b->as<Add>()) {
          if (equal(a36->a, a123->a)) {
            return (a36->b < a123->b);
          }
          if (equal(a36->a, a123->b)) {
            return (a36->b < a123->a);
          }
          if (equal(a36->b, a123->a)) {
            return (a36->a < a123->b);
          }
          if (equal(a36->b, a123->b)) {
            return (a36->a < a123->a);
          }
          if (const Add *a168 = a123->a->as<Add>()) {
            if (equal(a36->a, a168->a)) {
              return (a36->b < (a168->b + a123->b));
            }
            if (equal(a36->a, a168->b)) {
              return (a36->b < (a168->a + a123->b));
            }
            if (equal(a36->b, a168->a)) {
              return (a36->a < (a168->b + a123->b));
            }
            if (equal(a36->b, a168->b)) {
              return (a36->a < (a168->a + a123->b));
            }
          }
          if (const Add *a176 = a123->b->as<Add>()) {
            if (equal(a36->a, a176->a)) {
              return (a36->b < (a176->b + a123->a));
            }
            if (equal(a36->a, a176->b)) {
              return (a36->b < (a176->a + a123->a));
            }
            if (equal(a36->b, a176->a)) {
              return (a36->a < (a176->b + a123->a));
            }
            if (equal(a36->b, a176->b)) {
              return (a36->a < (a176->a + a123->a));
            }
          }
        }
      }
      if (is_const_v(a12->a)) {
        if (const Sub *a38 = a12->b->as<Sub>()) {
          if (is_const_v(a38->a)) {
            return (a38->b < fold((a38->a - a12->a)));
          }
        }
        if (const Add *a40 = a12->b->as<Add>()) {
          if (is_const_v(a40->b)) {
            return (fold((a12->a - a40->b)) < a40->a);
          }
        }
        if (const Min *a383 = a12->b->as<Min>()) {
          if (is_const_v(a383->b)) {
            return ((a12->a < a383->a) && fold((a12->a < a383->b)));
            return ((a12->a < a383->a) || fold((a12->a < a383->b)));
          }
        }
        if (const Select *a531 = a12->b->as<Select>()) {
          if (is_const_v(a531->a)) {
            if (is_const_v(a531->b)) {
              return select(a531->cond, fold((a12->a < a531->a)), fold((a12->a < a531->b)));
            }
          }
        }
      }
      if (const Sub *a42 = a12->a->as<Sub>()) {
        return (a42->a < (a12->b + a42->b));
      }
      if (const Sub *a44 = a12->b->as<Sub>()) {
        return ((a12->a + a44->b) < a44->a);
      }
      if (const Add *a52 = a12->b->as<Add>()) {
        if (const Sub *a53 = a52->a->as<Sub>()) {
          return ((a12->a + a53->b) < (a53->a + a52->b));
        }
        if (const Sub *a56 = a52->b->as<Sub>()) {
          return ((a12->a + a56->b) < (a56->a + a52->a));
        }
        if (const Add *a75 = a52->a->as<Add>()) {
          if (const Sub *a76 = a75->a->as<Sub>()) {
            return ((a12->a + a76->b) < ((a76->a + a75->b) + a52->b));
          }
          if (const Sub *a80 = a75->b->as<Sub>()) {
            return ((a12->a + a80->b) < ((a80->a + a75->a) + a52->b));
          }
          if (equal(a12->a, a75->a)) {
            return (0 < (a75->b + a52->b));
          }
          if (equal(a12->a, a75->b)) {
            return (0 < (a75->a + a52->b));
          }
        }
        if (const Add *a83 = a52->b->as<Add>()) {
          if (const Sub *a84 = a83->a->as<Sub>()) {
            return ((a12->a + a84->b) < ((a84->a + a83->b) + a52->a));
          }
          if (const Sub *a88 = a83->b->as<Sub>()) {
            return ((a12->a + a88->b) < ((a88->a + a83->a) + a52->a));
          }
          if (equal(a12->a, a83->a)) {
            return (0 < (a52->a + a83->b));
          }
          if (equal(a12->a, a83->b)) {
            return (0 < (a52->a + a83->a));
          }
        }
        if (equal(a12->a, a52->a)) {
          return (0 < a52->b);
        }
        if (equal(a12->a, a52->b)) {
          return (0 < a52->a);
        }
        if (const Min *a308 = a52->a->as<Min>()) {
          if (const Add *a309 = a308->a->as<Add>()) {
            if (equal(a12->a, a309->a)) {
              if (is_const_v(a309->b)) {
                if (is_const_v(a52->b)) {
                  return ((a12->a < (a308->b + a52->b)) && fold((0 < (a309->b + a52->b))));
                  return ((a12->a < (a308->b + a52->b)) || fold((0 < (a309->b + a52->b))));
                }
              }
            }
          }
          if (const Add *a313 = a308->b->as<Add>()) {
            if (equal(a12->a, a313->a)) {
              if (is_const_v(a313->b)) {
                if (is_const_v(a52->b)) {
                  return ((a12->a < (a308->a + a52->b)) && fold((0 < (a313->b + a52->b))));
                  return ((a12->a < (a308->a + a52->b)) || fold((0 < (a313->b + a52->b))));
                }
              }
            }
          }
          if (equal(a12->a, a308->a)) {
            if (is_const_v(a52->b)) {
              return ((a12->a < (a308->b + a52->b)) && fold((0 < a52->b)));
              return ((a12->a < (a308->b + a52->b)) || fold((0 < a52->b)));
            }
          }
          if (equal(a12->a, a308->b)) {
            if (is_const_v(a52->b)) {
              return ((a12->a < (a308->a + a52->b)) && fold((0 < a52->b)));
              return ((a12->a < (a308->a + a52->b)) || fold((0 < a52->b)));
            }
          }
        }
        if (const Select *a488 = a52->a->as<Select>()) {
          if (const Add *a489 = a488->a->as<Add>()) {
            if (equal(a12->a, a489->a)) {
              if (is_const_v(a489->b)) {
                if (is_const_v(a52->b)) {
                  if (evaluate_predicate(fold(((a489->b + a52->b) <= 0)))) {
                    return (!(a488->cond) && (a12->a < (a488->b + a52->b)));
                  }
                  if (evaluate_predicate(fold(((a489->b + a52->b) > 0)))) {
                    return (a488->cond || (a12->a < (a488->b + a52->b)));
                  }
                }
              }
            }
          }
          if (const Add *a497 = a488->b->as<Add>()) {
            if (equal(a12->a, a497->a)) {
              if (is_const_v(a497->b)) {
                if (is_const_v(a52->b)) {
                  if (evaluate_predicate(fold(((a497->b + a52->b) <= 0)))) {
                    return (a488->cond && (a12->a < (a488->a + a52->b)));
                  }
                  if (evaluate_predicate(fold(((a497->b + a52->b) > 0)))) {
                    return (!(a488->cond) || (a12->a < (a488->a + a52->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Mul *a278 = a12->a->as<Mul>()) {
        if (is_const_v(a278->b)) {
          if (const Mul *a279 = a12->b->as<Mul>()) {
            if (equal(a278->b, a279->b)) {
              if (evaluate_predicate(fold((a278->b > 0)))) {
                return (a278->a < a279->a);
              }
              if (evaluate_predicate(fold((a278->b < 0)))) {
                return (a279->a < a278->a);
              }
            }
          }
        }
      }
      if (const Min *a291 = a12->a->as<Min>()) {
        if (const Add *a292 = a291->a->as<Add>()) {
          if (is_const_v(a292->b)) {
            if (const Add *a293 = a12->b->as<Add>()) {
              if (equal(a292->a, a293->a)) {
                if (is_const_v(a293->b)) {
                  return ((a291->b < (a292->a + a293->b)) || fold((a292->b < a293->b)));
                  return ((a291->b < (a292->a + a293->b)) && fold((a292->b < a293->b)));
                }
              }
            }
            if (equal(a292->a, a12->b)) {
              return ((a291->b < a292->a) || fold((a292->b < 0)));
              return ((a291->b < a292->a) && fold((a292->b < 0)));
            }
            if (const Min *a425 = a12->b->as<Min>()) {
              if (equal(a292->a, a425->b)) {
                if (evaluate_predicate(fold((a292->b < 0)))) {
                  return (min(a291->b, (a292->a + a292->b)) < a425->a);
                }
                if (evaluate_predicate(fold((a292->b > 0)))) {
                  return (min(a291->b, (a292->a + a292->b)) < a425->a);
                }
              }
              if (equal(a292->a, a425->a)) {
                if (evaluate_predicate(fold((a292->b < 0)))) {
                  return (min(a291->b, (a292->a + a292->b)) < a425->b);
                }
                if (evaluate_predicate(fold((a292->b > 0)))) {
                  return (min(a291->b, (a292->a + a292->b)) < a425->b);
                }
              }
            }
          }
        }
        if (const Add *a296 = a291->b->as<Add>()) {
          if (is_const_v(a296->b)) {
            if (const Add *a297 = a12->b->as<Add>()) {
              if (equal(a296->a, a297->a)) {
                if (is_const_v(a297->b)) {
                  return ((a291->a < (a296->a + a297->b)) || fold((a296->b < a297->b)));
                  return ((a291->a < (a296->a + a297->b)) && fold((a296->b < a297->b)));
                }
              }
            }
            if (equal(a296->a, a12->b)) {
              return ((a291->a < a296->a) || fold((a296->b < 0)));
              return ((a291->a < a296->a) && fold((a296->b < 0)));
            }
            if (const Min *a403 = a12->b->as<Min>()) {
              if (equal(a296->a, a403->b)) {
                if (evaluate_predicate(fold((a296->b < 0)))) {
                  return (min(a291->a, (a296->a + a296->b)) < a403->a);
                }
                if (evaluate_predicate(fold((a296->b > 0)))) {
                  return (min(a291->a, (a296->a + a296->b)) < a403->a);
                }
              }
              if (equal(a296->a, a403->a)) {
                if (evaluate_predicate(fold((a296->b < 0)))) {
                  return (min(a291->a, (a296->a + a296->b)) < a403->b);
                }
                if (evaluate_predicate(fold((a296->b > 0)))) {
                  return (min(a291->a, (a296->a + a296->b)) < a403->b);
                }
              }
            }
          }
        }
        if (const Add *a324 = a12->b->as<Add>()) {
          if (equal(a291->a, a324->a)) {
            if (is_const_v(a324->b)) {
              return ((a291->b < (a291->a + a324->b)) || fold((0 < a324->b)));
              return ((a291->b < (a291->a + a324->b)) && fold((0 < a324->b)));
            }
          }
          if (equal(a291->b, a324->a)) {
            if (is_const_v(a324->b)) {
              return ((a291->a < (a291->b + a324->b)) || fold((0 < a324->b)));
              return ((a291->a < (a291->b + a324->b)) && fold((0 < a324->b)));
            }
          }
        }
        if (equal(a291->a, a12->b)) {
          return (a291->b < a291->a);
        }
        if (equal(a291->b, a12->b)) {
          return (a291->a < a291->b);
        }
        if (is_const_v(a291->b)) {
          if (is_const_v(a12->b)) {
            return ((a291->a < a12->b) || fold((a291->b < a12->b)));
            return ((a291->a < a12->b) && fold((a291->b < a12->b)));
          }
        }
        if (const Min *a388 = a12->b->as<Min>()) {
          if (equal(a291->b, a388->b)) {
            return (a291->a < min(a388->a, a291->b));
            return (min(a291->a, a291->b) < a388->a);
          }
          if (equal(a291->b, a388->a)) {
            return (a291->a < min(a291->b, a388->b));
            return (min(a291->a, a291->b) < a388->b);
          }
          if (const Add *a395 = a388->b->as<Add>()) {
            if (equal(a291->b, a395->a)) {
              if (is_const_v(a395->b)) {
                if (evaluate_predicate(fold((a395->b > 0)))) {
                  return (min(a291->a, a291->b) < a388->a);
                }
                if (evaluate_predicate(fold((a395->b < 0)))) {
                  return (min(a291->a, a291->b) < a388->a);
                }
              }
            }
            if (equal(a291->a, a395->a)) {
              if (is_const_v(a395->b)) {
                if (evaluate_predicate(fold((a395->b > 0)))) {
                  return (min(a291->b, a291->a) < a388->a);
                }
                if (evaluate_predicate(fold((a395->b < 0)))) {
                  return (min(a291->b, a291->a) < a388->a);
                }
              }
            }
          }
          if (const Add *a399 = a388->a->as<Add>()) {
            if (equal(a291->b, a399->a)) {
              if (is_const_v(a399->b)) {
                if (evaluate_predicate(fold((a399->b > 0)))) {
                  return (min(a291->a, a291->b) < a388->b);
                }
                if (evaluate_predicate(fold((a399->b < 0)))) {
                  return (min(a291->a, a291->b) < a388->b);
                }
              }
            }
            if (equal(a291->a, a399->a)) {
              if (is_const_v(a399->b)) {
                if (evaluate_predicate(fold((a399->b > 0)))) {
                  return (min(a291->b, a291->a) < a388->b);
                }
                if (evaluate_predicate(fold((a399->b < 0)))) {
                  return (min(a291->b, a291->a) < a388->b);
                }
              }
            }
          }
          if (equal(a291->a, a388->b)) {
            return (a291->b < min(a388->a, a291->a));
            return (min(a291->b, a291->a) < a388->a);
          }
          if (equal(a291->a, a388->a)) {
            return (a291->b < min(a291->a, a388->b));
            return (min(a291->b, a291->a) < a388->b);
          }
        }
      }
      if (const Min *a359 = a12->b->as<Min>()) {
        if (const Add *a360 = a359->a->as<Add>()) {
          if (equal(a12->a, a360->a)) {
            if (is_const_v(a360->b)) {
              return ((a12->a < a359->b) && fold((0 < a360->b)));
              return ((a12->a < a359->b) || fold((0 < a360->b)));
            }
          }
        }
        if (const Add *a363 = a359->b->as<Add>()) {
          if (equal(a12->a, a363->a)) {
            if (is_const_v(a363->b)) {
              return ((a12->a < a359->a) && fold((0 < a363->b)));
              return ((a12->a < a359->a) || fold((0 < a363->b)));
            }
          }
        }
        if (equal(a12->a, a359->a)) {
          return (a12->a < a359->b);
        }
        if (equal(a12->a, a359->b)) {
          return (a12->a < a359->a);
        }
      }
      if (const Select *a475 = a12->b->as<Select>()) {
        if (const Add *a476 = a475->a->as<Add>()) {
          if (equal(a12->a, a476->a)) {
            if (is_const_v(a476->b)) {
              if (evaluate_predicate(fold((a476->b <= 0)))) {
                return (!(a475->cond) && (a12->a < a475->b));
              }
              if (evaluate_predicate(fold((a476->b > 0)))) {
                return (a475->cond || (a12->a < a475->b));
              }
            }
          }
        }
        if (const Add *a482 = a475->b->as<Add>()) {
          if (equal(a12->a, a482->a)) {
            if (is_const_v(a482->b)) {
              if (evaluate_predicate(fold((a482->b <= 0)))) {
                return (a475->cond && (a12->a < a475->a));
              }
              if (evaluate_predicate(fold((a482->b > 0)))) {
                return (!(a475->cond) || (a12->a < a475->a));
              }
            }
          }
        }
      }
      if (const Select *a503 = a12->a->as<Select>()) {
        if (const Add *a504 = a503->a->as<Add>()) {
          if (is_const_v(a504->b)) {
            if (equal(a504->a, a12->b)) {
              if (evaluate_predicate(fold((a504->b >= 0)))) {
                return (!(a503->cond) && (a503->b < a504->a));
              }
              if (evaluate_predicate(fold((a504->b < 0)))) {
                return (a503->cond || (a503->b < a504->a));
              }
            }
            if (const Add *a517 = a12->b->as<Add>()) {
              if (equal(a504->a, a517->a)) {
                if (is_const_v(a517->b)) {
                  if (evaluate_predicate(fold((a504->b >= a517->b)))) {
                    return (!(a503->cond) && (a503->b < (a504->a + a517->b)));
                  }
                  if (evaluate_predicate(fold((a504->b < a517->b)))) {
                    return (a503->cond || (a503->b < (a504->a + a517->b)));
                  }
                }
              }
            }
          }
        }
        if (const Add *a510 = a503->b->as<Add>()) {
          if (is_const_v(a510->b)) {
            if (equal(a510->a, a12->b)) {
              if (evaluate_predicate(fold((a510->b >= 0)))) {
                return (a503->cond && (a503->a < a510->a));
              }
              if (evaluate_predicate(fold((a510->b < 0)))) {
                return (!(a503->cond) || (a503->a < a510->a));
              }
            }
            if (const Add *a525 = a12->b->as<Add>()) {
              if (equal(a510->a, a525->a)) {
                if (is_const_v(a525->b)) {
                  if (evaluate_predicate(fold((a510->b >= a525->b)))) {
                    return (a503->cond && (a503->a < (a510->a + a525->b)));
                  }
                  if (evaluate_predicate(fold((a510->b < a525->b)))) {
                    return (!(a503->cond) || (a503->a < (a510->a + a525->b)));
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a503->a)) {
          if (is_const_v(a503->b)) {
            if (is_const_v(a12->b)) {
              return select(a503->cond, fold((a503->a < a12->b)), fold((a503->b < a12->b)));
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a24 = expr->a->as<Broadcast>()) {
    if (is_const_v(a24->lanes)) {
      if (const Broadcast *a25 = expr->b->as<Broadcast>()) {
        if (equal(a24->lanes, a25->lanes)) {
          return broadcast((a24->value < a25->value), a24->lanes);
        }
      }
    }
  }
  if (const Mod *a26 = expr->a->as<Mod>()) {
    if (is_const_int(expr->b, 1)) {
      return ((a26->a % a26->b) == 0);
    }
    if (is_const_v(a26->b)) {
      if (is_const_v(expr->b)) {
        if (evaluate_predicate(fold((((expr->b + 1) == a26->b) && (a26->b > 0))))) {
          return ((a26->a % a26->b) != fold((a26->b - 1)));
        }
      }
    }
  }
  if (is_const_int(expr->a, 0)) {
    if (const Mod *a29 = expr->b->as<Mod>()) {
      return ((a29->a % a29->b) != 0);
    }
  }
  if (expr->is_operand_no_overflow_int()) {
    if (const LT *a283 = expr->as<LT>()) {
      if (const Mul *a284 = a283->a->as<Mul>()) {
        if (is_const_v(a284->b)) {
          if (is_const_v(a283->b)) {
            if (evaluate_predicate(fold((a284->b > 0)))) {
              return (a284->a < fold((((a283->b + a284->b) - 1) / a284->b)));
            }
          }
          if (const Mul *a647 = a283->b->as<Mul>()) {
            if (is_const_v(a647->b)) {
              if (evaluate_predicate(fold((((a647->b % a284->b) == 0) && (a284->b > 0))))) {
                return (a284->a < (a647->a * fold((a647->b / a284->b))));
              }
              if (evaluate_predicate(fold((((a284->b % a647->b) == 0) && (a647->b > 0))))) {
                return ((a284->a * fold((a284->b / a647->b))) < a647->a);
              }
            }
          }
          if (const Add *a653 = a283->b->as<Add>()) {
            if (const Mul *a654 = a653->a->as<Mul>()) {
              if (equal(a284->b, a654->b)) {
                if (is_const_v(a653->b)) {
                  if (evaluate_predicate(fold((a284->b > 0)))) {
                    return (a284->a < (a654->a + fold((((a653->b + a284->b) - 1) / a284->b))));
                  }
                }
              }
            }
          }
        }
        if (const Div *a709 = a284->a->as<Div>()) {
          if (const Add *a710 = a709->a->as<Add>()) {
            if (is_const_v(a710->b)) {
              if (is_const_v(a709->b)) {
                if (equal(a709->b, a284->b)) {
                  if (const Add *a711 = a283->b->as<Add>()) {
                    if (equal(a710->a, a711->a)) {
                      if (evaluate_predicate(fold((a709->b > 0)))) {
                        return (a710->b < (((a710->a + a710->b) % a709->b) + a711->b));
                      }
                    }
                    if (equal(a710->a, a711->b)) {
                      if (evaluate_predicate(fold((a709->b > 0)))) {
                        return (a710->b < (((a710->a + a710->b) % a709->b) + a711->a));
                      }
                    }
                  }
                  if (equal(a710->a, a283->b)) {
                    if (evaluate_predicate(fold((a709->b > 0)))) {
                      return (a710->b < ((a710->a + a710->b) % a709->b));
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a709->b)) {
            if (equal(a709->b, a284->b)) {
              if (const Add *a798 = a283->b->as<Add>()) {
                if (equal(a709->a, a798->a)) {
                  if (evaluate_predicate(fold((a709->b > 0)))) {
                    return (0 < ((a709->a % a709->b) + a798->b));
                  }
                }
                if (equal(a709->a, a798->b)) {
                  if (evaluate_predicate(fold((a709->b > 0)))) {
                    return (0 < ((a709->a % a709->b) + a798->a));
                  }
                }
              }
              if (equal(a709->a, a283->b)) {
                if (evaluate_predicate(fold((a709->b > 0)))) {
                  return ((a709->a % a709->b) != 0);
                }
              }
            }
          }
        }
      }
      if (const Add *a656 = a283->a->as<Add>()) {
        if (const Mul *a657 = a656->a->as<Mul>()) {
          if (is_const_v(a657->b)) {
            if (is_const_v(a656->b)) {
              if (const Mul *a658 = a283->b->as<Mul>()) {
                if (equal(a657->b, a658->b)) {
                  if (evaluate_predicate(fold((a657->b > 0)))) {
                    return ((a657->a + fold((a656->b / a657->b))) < a658->a);
                  }
                }
              }
            }
          }
          if (const Div *a662 = a657->a->as<Div>()) {
            if (const Add *a663 = a662->a->as<Add>()) {
              if (is_const_v(a663->b)) {
                if (is_const_v(a662->b)) {
                  if (equal(a662->b, a657->b)) {
                    if (const Add *a664 = a283->b->as<Add>()) {
                      if (equal(a663->a, a664->a)) {
                        if (evaluate_predicate(fold((a662->b > 0)))) {
                          return ((a656->b + a663->b) < (((a663->a + a663->b) % a662->b) + a664->b));
                        }
                      }
                      if (equal(a663->a, a664->b)) {
                        if (evaluate_predicate(fold((a662->b > 0)))) {
                          return ((a656->b + a663->b) < (((a663->a + a663->b) % a662->b) + a664->a));
                        }
                      }
                    }
                    if (equal(a663->a, a283->b)) {
                      if (evaluate_predicate(fold((a662->b > 0)))) {
                        return ((a656->b + a663->b) < ((a663->a + a663->b) % a662->b));
                      }
                    }
                  }
                }
              }
            }
            if (is_const_v(a662->b)) {
              if (equal(a662->b, a657->b)) {
                if (const Add *a751 = a283->b->as<Add>()) {
                  if (equal(a662->a, a751->a)) {
                    if (evaluate_predicate(fold((a662->b > 0)))) {
                      return (a656->b < ((a662->a % a662->b) + a751->b));
                    }
                  }
                  if (equal(a662->a, a751->b)) {
                    if (evaluate_predicate(fold((a662->b > 0)))) {
                      return (a656->b < ((a662->a % a662->b) + a751->a));
                    }
                  }
                }
                if (equal(a662->a, a283->b)) {
                  if (evaluate_predicate(fold((a662->b > 0)))) {
                    return (a656->b < (a662->a % a662->b));
                  }
                }
              }
            }
          }
        }
        if (const Mul *a667 = a656->b->as<Mul>()) {
          if (const Div *a668 = a667->a->as<Div>()) {
            if (const Add *a669 = a668->a->as<Add>()) {
              if (is_const_v(a669->b)) {
                if (is_const_v(a668->b)) {
                  if (equal(a668->b, a667->b)) {
                    if (const Add *a670 = a283->b->as<Add>()) {
                      if (equal(a669->a, a670->a)) {
                        if (evaluate_predicate(fold((a668->b > 0)))) {
                          return ((a656->a + a669->b) < (((a669->a + a669->b) % a668->b) + a670->b));
                        }
                      }
                      if (equal(a669->a, a670->b)) {
                        if (evaluate_predicate(fold((a668->b > 0)))) {
                          return ((a656->a + a669->b) < (((a669->a + a669->b) % a668->b) + a670->a));
                        }
                      }
                    }
                    if (equal(a669->a, a283->b)) {
                      if (evaluate_predicate(fold((a668->b > 0)))) {
                        return ((a656->a + a669->b) < ((a669->a + a669->b) % a668->b));
                      }
                    }
                  }
                }
              }
            }
            if (is_const_v(a668->b)) {
              if (equal(a668->b, a667->b)) {
                if (const Add *a756 = a283->b->as<Add>()) {
                  if (equal(a668->a, a756->a)) {
                    if (evaluate_predicate(fold((a668->b > 0)))) {
                      return (a656->a < ((a668->a % a668->b) + a756->b));
                    }
                  }
                  if (equal(a668->a, a756->b)) {
                    if (evaluate_predicate(fold((a668->b > 0)))) {
                      return (a656->a < ((a668->a % a668->b) + a756->a));
                    }
                  }
                }
                if (equal(a668->a, a283->b)) {
                  if (evaluate_predicate(fold((a668->b > 0)))) {
                    return (a656->a < (a668->a % a668->b));
                  }
                }
              }
            }
          }
        }
        if (const Add *a685 = a283->b->as<Add>()) {
          if (const Mul *a686 = a685->a->as<Mul>()) {
            if (const Div *a687 = a686->a->as<Div>()) {
              if (const Add *a688 = a687->a->as<Add>()) {
                if (equal(a656->a, a688->a)) {
                  if (is_const_v(a688->b)) {
                    if (is_const_v(a687->b)) {
                      if (equal(a687->b, a686->b)) {
                        if (evaluate_predicate(fold((a687->b > 0)))) {
                          return ((((a656->a + a688->b) % a687->b) + a656->b) < (a685->b + a688->b));
                        }
                      }
                    }
                  }
                }
                if (equal(a656->b, a688->a)) {
                  if (is_const_v(a688->b)) {
                    if (is_const_v(a687->b)) {
                      if (equal(a687->b, a686->b)) {
                        if (evaluate_predicate(fold((a687->b > 0)))) {
                          return ((((a656->b + a688->b) % a687->b) + a656->a) < (a685->b + a688->b));
                        }
                      }
                    }
                  }
                }
              }
              if (equal(a656->a, a687->a)) {
                if (is_const_v(a687->b)) {
                  if (equal(a687->b, a686->b)) {
                    if (evaluate_predicate(fold((a687->b > 0)))) {
                      return (((a656->a % a687->b) + a656->b) < a685->b);
                    }
                  }
                }
              }
              if (equal(a656->b, a687->a)) {
                if (is_const_v(a687->b)) {
                  if (equal(a687->b, a686->b)) {
                    if (evaluate_predicate(fold((a687->b > 0)))) {
                      return (((a656->b % a687->b) + a656->a) < a685->b);
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a692 = a685->b->as<Mul>()) {
            if (const Div *a693 = a692->a->as<Div>()) {
              if (const Add *a694 = a693->a->as<Add>()) {
                if (equal(a656->a, a694->a)) {
                  if (is_const_v(a694->b)) {
                    if (is_const_v(a693->b)) {
                      if (equal(a693->b, a692->b)) {
                        if (evaluate_predicate(fold((a693->b > 0)))) {
                          return ((((a656->a + a694->b) % a693->b) + a656->b) < (a685->a + a694->b));
                        }
                      }
                    }
                  }
                }
                if (equal(a656->b, a694->a)) {
                  if (is_const_v(a694->b)) {
                    if (is_const_v(a693->b)) {
                      if (equal(a693->b, a692->b)) {
                        if (evaluate_predicate(fold((a693->b > 0)))) {
                          return ((((a656->b + a694->b) % a693->b) + a656->a) < (a685->a + a694->b));
                        }
                      }
                    }
                  }
                }
              }
              if (equal(a656->a, a693->a)) {
                if (is_const_v(a693->b)) {
                  if (equal(a693->b, a692->b)) {
                    if (evaluate_predicate(fold((a693->b > 0)))) {
                      return (((a656->a % a693->b) + a656->b) < a685->a);
                    }
                  }
                }
              }
              if (equal(a656->b, a693->a)) {
                if (is_const_v(a693->b)) {
                  if (equal(a693->b, a692->b)) {
                    if (evaluate_predicate(fold((a693->b > 0)))) {
                      return (((a656->b % a693->b) + a656->a) < a685->a);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Mul *a719 = a283->b->as<Mul>()) {
          if (const Div *a720 = a719->a->as<Div>()) {
            if (const Add *a721 = a720->a->as<Add>()) {
              if (equal(a656->a, a721->a)) {
                if (is_const_v(a721->b)) {
                  if (is_const_v(a720->b)) {
                    if (equal(a720->b, a719->b)) {
                      if (evaluate_predicate(fold((a720->b > 0)))) {
                        return ((((a656->a + a721->b) % a720->b) + a656->b) < a721->b);
                      }
                    }
                  }
                }
              }
              if (equal(a656->b, a721->a)) {
                if (is_const_v(a721->b)) {
                  if (is_const_v(a720->b)) {
                    if (equal(a720->b, a719->b)) {
                      if (evaluate_predicate(fold((a720->b > 0)))) {
                        return ((((a656->b + a721->b) % a720->b) + a656->a) < a721->b);
                      }
                    }
                  }
                }
              }
            }
            if (equal(a656->a, a720->a)) {
              if (is_const_v(a720->b)) {
                if (equal(a720->b, a719->b)) {
                  if (evaluate_predicate(fold((a720->b > 0)))) {
                    return (((a656->a % a720->b) + a656->b) < 0);
                  }
                }
              }
            }
            if (equal(a656->b, a720->a)) {
              if (is_const_v(a720->b)) {
                if (equal(a720->b, a719->b)) {
                  if (evaluate_predicate(fold((a720->b > 0)))) {
                    return (((a656->b % a720->b) + a656->a) < 0);
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a738 = a283->b->as<Add>()) {
        if (const Mul *a739 = a738->a->as<Mul>()) {
          if (const Div *a740 = a739->a->as<Div>()) {
            if (const Add *a741 = a740->a->as<Add>()) {
              if (equal(a283->a, a741->a)) {
                if (is_const_v(a741->b)) {
                  if (is_const_v(a740->b)) {
                    if (equal(a740->b, a739->b)) {
                      if (evaluate_predicate(fold((a740->b > 0)))) {
                        return (((a283->a + a741->b) % a740->b) < (a738->b + a741->b));
                      }
                    }
                  }
                }
              }
            }
            if (equal(a283->a, a740->a)) {
              if (is_const_v(a740->b)) {
                if (equal(a740->b, a739->b)) {
                  if (evaluate_predicate(fold((a740->b > 0)))) {
                    return ((a283->a % a740->b) < a738->b);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a744 = a738->b->as<Mul>()) {
          if (const Div *a745 = a744->a->as<Div>()) {
            if (const Add *a746 = a745->a->as<Add>()) {
              if (equal(a283->a, a746->a)) {
                if (is_const_v(a746->b)) {
                  if (is_const_v(a745->b)) {
                    if (equal(a745->b, a744->b)) {
                      if (evaluate_predicate(fold((a745->b > 0)))) {
                        return (((a283->a + a746->b) % a745->b) < (a738->a + a746->b));
                      }
                    }
                  }
                }
              }
            }
            if (equal(a283->a, a745->a)) {
              if (is_const_v(a745->b)) {
                if (equal(a745->b, a744->b)) {
                  if (evaluate_predicate(fold((a745->b > 0)))) {
                    return ((a283->a % a745->b) < a738->a);
                  }
                }
              }
            }
          }
        }
      }
      if (const Mul *a792 = a283->b->as<Mul>()) {
        if (const Div *a793 = a792->a->as<Div>()) {
          if (const Add *a794 = a793->a->as<Add>()) {
            if (equal(a283->a, a794->a)) {
              if (is_const_v(a794->b)) {
                if (is_const_v(a793->b)) {
                  if (equal(a793->b, a792->b)) {
                    if (evaluate_predicate(fold((a793->b > 0)))) {
                      return (((a283->a + a794->b) % a793->b) < a794->b);
                    }
                  }
                }
              }
            }
          }
          if (equal(a283->a, a793->a)) {
            if (is_const_v(a793->b)) {
              if (equal(a793->b, a792->b)) {
                if (evaluate_predicate(fold((a793->b > 0)))) {
                  return false;
                }
              }
            }
          }
        }
      }
      if (const Div *a834 = a283->a->as<Div>()) {
        if (const Add *a835 = a834->a->as<Add>()) {
          if (is_const_v(a835->b)) {
            if (is_const_v(a834->b)) {
              if (const Div *a836 = a283->b->as<Div>()) {
                if (const Add *a837 = a836->a->as<Add>()) {
                  if (equal(a835->a, a837->a)) {
                    if (is_const_v(a837->b)) {
                      if (equal(a834->b, a836->b)) {
                        if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= a837->b))))) {
                          return false;
                        }
                        if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= (a837->b - a834->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (equal(a835->a, a836->a)) {
                  if (equal(a834->b, a836->b)) {
                    if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= 0))))) {
                      return false;
                    }
                    if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= (0 - a834->b)))))) {
                      return true;
                    }
                  }
                }
              }
              if (const Add *a862 = a283->b->as<Add>()) {
                if (const Div *a863 = a862->a->as<Div>()) {
                  if (equal(a835->a, a863->a)) {
                    if (equal(a834->b, a863->b)) {
                      if (is_const_v(a862->b)) {
                        if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= (a862->b * a834->b)))))) {
                          return false;
                        }
                        if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= ((a862->b * a834->b) - a834->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (const Min *a873 = a862->a->as<Min>()) {
                  if (const Div *a874 = a873->a->as<Div>()) {
                    if (equal(a835->a, a874->a)) {
                      if (equal(a834->b, a874->b)) {
                        if (is_const_v(a862->b)) {
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= (a862->b * a834->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= ((a862->b * a834->b) - a834->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (const Div *a908 = a873->b->as<Div>()) {
                    if (equal(a835->a, a908->a)) {
                      if (equal(a834->b, a908->b)) {
                        if (is_const_v(a862->b)) {
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= (a862->b * a834->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= ((a862->b * a834->b) - a834->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                }
              }
              if (const Min *a884 = a283->b->as<Min>()) {
                if (const Div *a885 = a884->a->as<Div>()) {
                  if (const Add *a886 = a885->a->as<Add>()) {
                    if (equal(a835->a, a886->a)) {
                      if (is_const_v(a886->b)) {
                        if (equal(a834->b, a885->b)) {
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= a886->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= (a886->b - a834->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a835->a, a885->a)) {
                    if (equal(a834->b, a885->b)) {
                      if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= (0 - a834->b)))))) {
                        return true;
                      }
                    }
                  }
                }
                if (const Div *a919 = a884->b->as<Div>()) {
                  if (const Add *a920 = a919->a->as<Add>()) {
                    if (equal(a835->a, a920->a)) {
                      if (is_const_v(a920->b)) {
                        if (equal(a834->b, a919->b)) {
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= a920->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= (a920->b - a834->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a835->a, a919->a)) {
                    if (equal(a834->b, a919->b)) {
                      if (evaluate_predicate(fold(((a834->b > 0) && (a835->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a834->b > 0) && (a835->b <= (0 - a834->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Min *a1048 = a835->a->as<Min>()) {
            if (const Add *a1049 = a1048->b->as<Add>()) {
              if (const Mul *a1050 = a1049->a->as<Mul>()) {
                if (is_const_v(a1050->b)) {
                  if (is_const_v(a1049->b)) {
                    if (is_const_v(a835->b)) {
                      if (equal(a1050->b, a834->b)) {
                        if (equal(a1050->a, a283->b)) {
                          if (evaluate_predicate(fold(((a1050->b > 0) && ((a1049->b + a835->b) < 0))))) {
                            return (((a1048->a + a835->b) / a1050->b) < a1050->a);
                            return true;
                          }
                          if (evaluate_predicate(fold(((a1050->b > 0) && ((a1049->b + a835->b) >= 0))))) {
                            return false;
                            return (((a1048->a + a835->b) / a1050->b) < a1050->a);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Mul *a1061 = a1048->b->as<Mul>()) {
              if (is_const_v(a1061->b)) {
                if (is_const_v(a835->b)) {
                  if (equal(a1061->b, a834->b)) {
                    if (equal(a1061->a, a283->b)) {
                      if (evaluate_predicate(fold(((a1061->b > 0) && (a835->b < 0))))) {
                        return (((a1048->a + a835->b) / a1061->b) < a1061->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1061->b > 0) && (a835->b >= 0))))) {
                        return false;
                        return (((a1048->a + a835->b) / a1061->b) < a1061->a);
                      }
                    }
                  }
                }
              }
            }
            if (const Add *a1071 = a1048->a->as<Add>()) {
              if (const Mul *a1072 = a1071->a->as<Mul>()) {
                if (is_const_v(a1072->b)) {
                  if (is_const_v(a1071->b)) {
                    if (is_const_v(a835->b)) {
                      if (equal(a1072->b, a834->b)) {
                        if (equal(a1072->a, a283->b)) {
                          if (evaluate_predicate(fold(((a1072->b > 0) && ((a1071->b + a835->b) < 0))))) {
                            return (((a1048->b + a835->b) / a1072->b) < a1072->a);
                            return true;
                          }
                          if (evaluate_predicate(fold(((a1072->b > 0) && ((a1071->b + a835->b) >= 0))))) {
                            return false;
                            return (((a1048->b + a835->b) / a1072->b) < a1072->a);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Mul *a1083 = a1048->a->as<Mul>()) {
              if (is_const_v(a1083->b)) {
                if (is_const_v(a835->b)) {
                  if (equal(a1083->b, a834->b)) {
                    if (equal(a1083->a, a283->b)) {
                      if (evaluate_predicate(fold(((a1083->b > 0) && (a835->b < 0))))) {
                        return (((a1048->b + a835->b) / a1083->b) < a1083->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1083->b > 0) && (a835->b >= 0))))) {
                        return false;
                        return (((a1048->b + a835->b) / a1083->b) < a1083->a);
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a834->b)) {
          if (const Div *a845 = a283->b->as<Div>()) {
            if (const Add *a846 = a845->a->as<Add>()) {
              if (equal(a834->a, a846->a)) {
                if (is_const_v(a846->b)) {
                  if (equal(a834->b, a845->b)) {
                    if (evaluate_predicate(fold(((a834->b > 0) && (0 >= a846->b))))) {
                      return false;
                    }
                    if (evaluate_predicate(fold(((a834->b > 0) && (0 <= (a846->b - a834->b)))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
          if (const Min *a1007 = a283->b->as<Min>()) {
            if (const Div *a1008 = a1007->a->as<Div>()) {
              if (const Add *a1009 = a1008->a->as<Add>()) {
                if (equal(a834->a, a1009->a)) {
                  if (is_const_v(a1009->b)) {
                    if (equal(a834->b, a1008->b)) {
                      if (evaluate_predicate(fold(((a834->b > 0) && (a1009->b < 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a834->b > 0) && (a834->b <= a1009->b))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
            if (const Div *a1018 = a1007->b->as<Div>()) {
              if (const Add *a1019 = a1018->a->as<Add>()) {
                if (equal(a834->a, a1019->a)) {
                  if (is_const_v(a1019->b)) {
                    if (equal(a834->b, a1018->b)) {
                      if (evaluate_predicate(fold(((a834->b > 0) && (a1019->b < 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a834->b > 0) && (a834->b <= a1019->b))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a1091 = a834->a->as<Min>()) {
          if (const Add *a1092 = a1091->b->as<Add>()) {
            if (const Mul *a1093 = a1092->a->as<Mul>()) {
              if (is_const_v(a1093->b)) {
                if (is_const_v(a1092->b)) {
                  if (equal(a1093->b, a834->b)) {
                    if (equal(a1093->a, a283->b)) {
                      if (evaluate_predicate(fold(((a1093->b > 0) && (a1092->b < 0))))) {
                        return ((a1091->a / a1093->b) < a1093->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1093->b > 0) && (a1092->b >= 0))))) {
                        return false;
                        return ((a1091->a / a1093->b) < a1093->a);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a1102 = a1091->b->as<Mul>()) {
            if (is_const_v(a1102->b)) {
              if (equal(a1102->b, a834->b)) {
                if (equal(a1102->a, a283->b)) {
                  if (evaluate_predicate(fold((a1102->b > 0)))) {
                    return false;
                    return ((a1091->a / a1102->b) < a1102->a);
                  }
                }
              }
            }
          }
          if (const Add *a1106 = a1091->a->as<Add>()) {
            if (const Mul *a1107 = a1106->a->as<Mul>()) {
              if (is_const_v(a1107->b)) {
                if (is_const_v(a1106->b)) {
                  if (equal(a1107->b, a834->b)) {
                    if (equal(a1107->a, a283->b)) {
                      if (evaluate_predicate(fold(((a1107->b > 0) && (a1106->b < 0))))) {
                        return ((a1091->b / a1107->b) < a1107->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1107->b > 0) && (a1106->b >= 0))))) {
                        return false;
                        return ((a1091->b / a1107->b) < a1107->a);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a1116 = a1091->a->as<Mul>()) {
            if (is_const_v(a1116->b)) {
              if (equal(a1116->b, a834->b)) {
                if (equal(a1116->a, a283->b)) {
                  if (evaluate_predicate(fold((a1116->b > 0)))) {
                    return false;
                    return ((a1091->b / a1116->b) < a1116->a);
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a938 = a283->a->as<Min>()) {
        if (const Div *a939 = a938->a->as<Div>()) {
          if (const Add *a940 = a939->a->as<Add>()) {
            if (is_const_v(a940->b)) {
              if (is_const_v(a939->b)) {
                if (const Div *a941 = a283->b->as<Div>()) {
                  if (const Add *a942 = a941->a->as<Add>()) {
                    if (equal(a940->a, a942->a)) {
                      if (is_const_v(a942->b)) {
                        if (equal(a939->b, a941->b)) {
                          if (evaluate_predicate(fold(((a939->b > 0) && (a940->b >= a942->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a939->b > 0) && (a940->b <= (a942->b - a939->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a940->a, a941->a)) {
                    if (equal(a939->b, a941->b)) {
                      if (evaluate_predicate(fold(((a939->b > 0) && (a940->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a939->b > 0) && ((a940->b + a939->b) <= 0))))) {
                        return true;
                      }
                    }
                  }
                }
                if (const Add *a985 = a283->b->as<Add>()) {
                  if (const Div *a986 = a985->a->as<Div>()) {
                    if (equal(a940->a, a986->a)) {
                      if (equal(a939->b, a986->b)) {
                        if (is_const_v(a985->b)) {
                          if (evaluate_predicate(fold(((a939->b > 0) && (a940->b >= (a985->b * a939->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a939->b > 0) && (a940->b <= ((a985->b * a939->b) - a939->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a939->b)) {
            if (const Div *a952 = a283->b->as<Div>()) {
              if (const Add *a953 = a952->a->as<Add>()) {
                if (equal(a939->a, a953->a)) {
                  if (is_const_v(a953->b)) {
                    if (equal(a939->b, a952->b)) {
                      if (evaluate_predicate(fold(((a939->b > 0) && (0 >= a953->b))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a939->b > 0) && (0 <= (a953->b - a939->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Div *a961 = a938->b->as<Div>()) {
          if (const Add *a962 = a961->a->as<Add>()) {
            if (is_const_v(a962->b)) {
              if (is_const_v(a961->b)) {
                if (const Div *a963 = a283->b->as<Div>()) {
                  if (const Add *a964 = a963->a->as<Add>()) {
                    if (equal(a962->a, a964->a)) {
                      if (is_const_v(a964->b)) {
                        if (equal(a961->b, a963->b)) {
                          if (evaluate_predicate(fold(((a961->b > 0) && (a962->b >= a964->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a961->b > 0) && (a962->b <= (a964->b - a961->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a962->a, a963->a)) {
                    if (equal(a961->b, a963->b)) {
                      if (evaluate_predicate(fold(((a961->b > 0) && (a962->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a961->b > 0) && ((a962->b + a961->b) <= 0))))) {
                        return true;
                      }
                    }
                  }
                }
                if (const Add *a997 = a283->b->as<Add>()) {
                  if (const Div *a998 = a997->a->as<Div>()) {
                    if (equal(a962->a, a998->a)) {
                      if (equal(a961->b, a998->b)) {
                        if (is_const_v(a997->b)) {
                          if (evaluate_predicate(fold(((a961->b > 0) && (a962->b >= (a997->b * a961->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a961->b > 0) && (a962->b <= ((a997->b * a961->b) - a961->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a961->b)) {
            if (const Div *a974 = a283->b->as<Div>()) {
              if (const Add *a975 = a974->a->as<Add>()) {
                if (equal(a961->a, a975->a)) {
                  if (is_const_v(a975->b)) {
                    if (equal(a961->b, a974->b)) {
                      if (evaluate_predicate(fold(((a961->b > 0) && (0 >= a975->b))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a961->b > 0) && (0 <= (a975->b - a961->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a938->b)) {
          if (const Min *a1191 = a283->b->as<Min>()) {
            if (equal(a938->a, a1191->a)) {
              if (is_const_v(a1191->b)) {
                if (evaluate_predicate(fold((a938->b >= a1191->b)))) {
                  return false;
                }
              }
            }
          }
          if (const Add *a1194 = a283->b->as<Add>()) {
            if (const Min *a1195 = a1194->a->as<Min>()) {
              if (equal(a938->a, a1195->a)) {
                if (is_const_v(a1195->b)) {
                  if (is_const_v(a1194->b)) {
                    if (evaluate_predicate(fold(((a938->b >= (a1195->b + a1194->b)) && (a1194->b <= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Ramp *a1204 = a283->a->as<Ramp>()) {
        if (const Add *a1205 = a1204->base->as<Add>()) {
          if (const Mul *a1206 = a1205->a->as<Mul>()) {
            if (is_const_v(a1206->b)) {
              if (is_const_v(a1205->b)) {
                if (is_const_v(a1204->stride)) {
                  if (is_const_v(a1204->lanes)) {
                    if (const Broadcast *a1207 = a283->b->as<Broadcast>()) {
                      if (const Mul *a1208 = a1207->value->as<Mul>()) {
                        if (is_const_v(a1208->b)) {
                          if (equal(a1204->lanes, a1207->lanes)) {
                            if (evaluate_predicate(fold(((((a1208->b > 0) && ((a1206->b % a1208->b) == 0)) && (((a1205->b % a1208->b) + (a1204->stride * (a1204->lanes - 1))) < a1208->b)) && (((a1205->b % a1208->b) + (a1204->stride * (a1204->lanes - 1))) >= 0))))) {
                              return broadcast((((a1206->a * fold((a1206->b / a1208->b))) + fold((a1205->b / a1208->b))) < a1208->a), a1204->lanes);
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
        if (const Mul *a1211 = a1204->base->as<Mul>()) {
          if (is_const_v(a1211->b)) {
            if (is_const_v(a1204->stride)) {
              if (is_const_v(a1204->lanes)) {
                if (const Broadcast *a1212 = a283->b->as<Broadcast>()) {
                  if (const Mul *a1213 = a1212->value->as<Mul>()) {
                    if (is_const_v(a1213->b)) {
                      if (equal(a1204->lanes, a1212->lanes)) {
                        if (evaluate_predicate(fold(((((a1213->b > 0) && ((a1211->b % a1213->b) == 0)) && ((a1204->stride * (a1204->lanes - 1)) < a1213->b)) && ((a1204->stride * (a1204->lanes - 1)) >= 0))))) {
                          return broadcast(((a1211->a * fold((a1211->b / a1213->b))) < a1213->a), a1204->lanes);
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
  if (expr->is_operand_float()) {
    if (const LT *a285 = expr->as<LT>()) {
      if (const Mul *a286 = a285->a->as<Mul>()) {
        if (is_const_v(a286->b)) {
          if (is_const_v(a285->b)) {
            if (evaluate_predicate(fold((a286->b > 0)))) {
              return (a286->a < fold((a285->b / a286->b)));
            }
          }
        }
      }
      if (is_const_v(a285->a)) {
        if (const Div *a288 = a285->b->as<Div>()) {
          if (is_const_v(a288->b)) {
            if (evaluate_predicate(fold((a288->b < 0)))) {
              return (a288->a < fold((a285->a * a288->b)));
            }
          }
        }
      }
    }
  }
  return expr;
}
