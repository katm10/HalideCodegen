#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_LT(const LT *expr, Simplify *simplifier) {
  if (is_const_v(expr->a)) {
    if (is_const_v(expr->b)) {
      return fold((expr->a < expr->b));
    }
    if (const Mod *a29 = expr->b.as<Mod>()) {
      if (is_const_v(a29->b)) {
        if (evaluate_predicate(fold((((expr->a + 2) == a29->b) && (a29->b > 0))))) {
          return ((a29->a % a29->b) == fold((a29->b - 1)));
        }
      }
    }
    if (const Mul *a287 = expr->b.as<Mul>()) {
      if (is_const_v(a287->b)) {
        if (evaluate_predicate(fold((a287->b > 0)))) {
          return (fold((expr->a / a287->b)) < a287->a);
        }
      }
    }
  }
  if (equal(expr->a, expr->b)) {
    return false;
  }
  if (const Min *a0 = expr->a.as<Min>()) {
    if (equal(a0->a, expr->b)) {
      return false;
    }
    if (equal(a0->b, expr->b)) {
      return false;
    }
    if (const Min *a5 = expr->b.as<Min>()) {
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
  if (const Min *a2 = expr->b.as<Min>()) {
    if (equal(expr->a, a2->a)) {
      return false;
    }
    if (equal(expr->a, a2->b)) {
      return false;
    }
  }
  if (expr->is_operand_no_overflow()) {
    if (const LT *a12 = expr.as<LT>()) {
      if (const Ramp *a13 = a12->a.as<Ramp>()) {
        if (is_const_v(a13->stride)) {
          if (is_const_v(a13->lanes)) {
            if (const Broadcast *a14 = a12->b.as<Broadcast>()) {
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
          if (const Ramp *a32 = a12->b.as<Ramp>()) {
            if (equal(a13->stride, a32->stride)) {
              if (equal(a13->lanes, a32->lanes)) {
                return broadcast((a13->base < a32->base), a13->lanes);
              }
            }
            if (equal(a13->lanes, a32->lanes)) {
              return (ramp((a13->base - a32->base), (a13->stride - a32->stride), a13->lanes) < 0);
            }
          }
          if (const Broadcast *a567 = a12->b.as<Broadcast>()) {
            if (const Add *a568 = a567->value.as<Add>()) {
              if (equal(a13->base, a568->a)) {
                if (equal(a13->lanes, a567->lanes)) {
                  return (ramp(0, a13->stride, a13->lanes) < broadcast(a568->b, a13->lanes));
                }
              }
              if (equal(a13->base, a568->b)) {
                if (equal(a13->lanes, a567->lanes)) {
                  return (ramp(0, a13->stride, a13->lanes) < broadcast(a568->a, a13->lanes));
                }
              }
            }
            if (const Sub *a576 = a567->value.as<Sub>()) {
              if (equal(a13->base, a576->a)) {
                if (equal(a13->lanes, a567->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a13->base, 0))))) {
                    return (ramp(0, a13->stride, a13->lanes) < broadcast((0 - a576->b), a13->lanes));
                  }
                }
              }
            }
          }
        }
        if (const Add *a537 = a13->base.as<Add>()) {
          if (is_const_v(a13->lanes)) {
            if (const Broadcast *a538 = a12->b.as<Broadcast>()) {
              if (const Add *a539 = a538->value.as<Add>()) {
                if (equal(a537->a, a539->a)) {
                  if (equal(a13->lanes, a538->lanes)) {
                    return (ramp(a537->b, a13->stride, a13->lanes) < broadcast(a539->b, a13->lanes));
                  }
                }
                if (equal(a537->b, a539->a)) {
                  if (equal(a13->lanes, a538->lanes)) {
                    return (ramp(a537->a, a13->stride, a13->lanes) < broadcast(a539->b, a13->lanes));
                  }
                }
                if (equal(a537->a, a539->b)) {
                  if (equal(a13->lanes, a538->lanes)) {
                    return (ramp(a537->b, a13->stride, a13->lanes) < broadcast(a539->a, a13->lanes));
                  }
                }
                if (equal(a537->b, a539->b)) {
                  if (equal(a13->lanes, a538->lanes)) {
                    return (ramp(a537->a, a13->stride, a13->lanes) < broadcast(a539->a, a13->lanes));
                  }
                }
              }
              if (equal(a537->a, a538->value)) {
                if (equal(a13->lanes, a538->lanes)) {
                  return (ramp(a537->b, a13->stride, a13->lanes) < 0);
                }
              }
              if (equal(a537->b, a538->value)) {
                if (equal(a13->lanes, a538->lanes)) {
                  return (ramp(a537->a, a13->stride, a13->lanes) < 0);
                }
              }
            }
          }
        }
        if (const Sub *a557 = a13->base.as<Sub>()) {
          if (is_const_v(a13->lanes)) {
            if (const Broadcast *a558 = a12->b.as<Broadcast>()) {
              if (const Sub *a559 = a558->value.as<Sub>()) {
                if (equal(a557->a, a559->a)) {
                  if (equal(a13->lanes, a558->lanes)) {
                    if (evaluate_predicate(fold(!(is_const(a557->a, 0))))) {
                      return (ramp((0 - a557->b), a13->stride, a13->lanes) < broadcast((0 - a559->b), a13->lanes));
                    }
                  }
                }
                if (equal(a557->b, a559->b)) {
                  if (equal(a13->lanes, a558->lanes)) {
                    return (ramp(a557->a, a13->stride, a13->lanes) < broadcast(a559->a, a13->lanes));
                  }
                }
              }
              if (equal(a557->a, a558->value)) {
                if (equal(a13->lanes, a558->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a557->a, 0))))) {
                    return (ramp((0 - a557->b), a13->stride, a13->lanes) < 0);
                  }
                }
              }
            }
          }
        }
      }
      if (const Broadcast *a19 = a12->a.as<Broadcast>()) {
        if (is_const_v(a19->lanes)) {
          if (const Ramp *a20 = a12->b.as<Ramp>()) {
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
            if (const Add *a634 = a20->base.as<Add>()) {
              if (equal(a19->value, a634->a)) {
                if (equal(a19->lanes, a20->lanes)) {
                  return (0 < ramp(a634->b, a20->stride, a19->lanes));
                }
              }
              if (equal(a19->value, a634->b)) {
                if (equal(a19->lanes, a20->lanes)) {
                  return (0 < ramp(a634->a, a20->stride, a19->lanes));
                }
              }
            }
            if (const Sub *a642 = a20->base.as<Sub>()) {
              if (equal(a19->value, a642->a)) {
                if (equal(a19->lanes, a20->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a19->value, 0))))) {
                    return (0 < ramp((0 - a642->b), a20->stride, a19->lanes));
                  }
                }
              }
            }
          }
        }
        if (const Add *a591 = a19->value.as<Add>()) {
          if (is_const_v(a19->lanes)) {
            if (const Ramp *a592 = a12->b.as<Ramp>()) {
              if (const Add *a593 = a592->base.as<Add>()) {
                if (equal(a591->a, a593->a)) {
                  if (equal(a19->lanes, a592->lanes)) {
                    return (broadcast(a591->b, a19->lanes) < ramp(a593->b, a592->stride, a19->lanes));
                  }
                }
                if (equal(a591->a, a593->b)) {
                  if (equal(a19->lanes, a592->lanes)) {
                    return (broadcast(a591->b, a19->lanes) < ramp(a593->a, a592->stride, a19->lanes));
                  }
                }
                if (equal(a591->b, a593->a)) {
                  if (equal(a19->lanes, a592->lanes)) {
                    return (broadcast(a591->a, a19->lanes) < ramp(a593->b, a592->stride, a19->lanes));
                  }
                }
                if (equal(a591->b, a593->b)) {
                  if (equal(a19->lanes, a592->lanes)) {
                    return (broadcast(a591->a, a19->lanes) < ramp(a593->a, a592->stride, a19->lanes));
                  }
                }
              }
              if (equal(a591->a, a592->base)) {
                if (equal(a19->lanes, a592->lanes)) {
                  return (broadcast(a591->b, a19->lanes) < ramp(0, a592->stride, a19->lanes));
                }
              }
              if (equal(a591->b, a592->base)) {
                if (equal(a19->lanes, a592->lanes)) {
                  return (broadcast(a591->a, a19->lanes) < ramp(0, a592->stride, a19->lanes));
                }
              }
            }
          }
        }
        if (const Sub *a611 = a19->value.as<Sub>()) {
          if (is_const_v(a19->lanes)) {
            if (const Ramp *a612 = a12->b.as<Ramp>()) {
              if (const Sub *a613 = a612->base.as<Sub>()) {
                if (equal(a611->a, a613->a)) {
                  if (equal(a19->lanes, a612->lanes)) {
                    if (evaluate_predicate(fold(!(is_const(a611->a, 0))))) {
                      return (broadcast((0 - a611->b), a19->lanes) < ramp((0 - a613->b), a612->stride, a19->lanes));
                    }
                  }
                }
                if (equal(a611->b, a613->b)) {
                  if (equal(a19->lanes, a612->lanes)) {
                    return (broadcast(a611->a, a19->lanes) < ramp(a613->a, a612->stride, a19->lanes));
                  }
                }
              }
              if (equal(a611->a, a612->base)) {
                if (equal(a19->lanes, a612->lanes)) {
                  if (evaluate_predicate(fold(!(is_const(a611->a, 0))))) {
                    return (broadcast((0 - a611->b), a19->lanes) < ramp(0, a612->stride, a19->lanes));
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a34 = a12->a.as<Add>()) {
        if (is_const_v(a34->b)) {
          return (a34->a < (a12->b + fold((0 - a34->b))));
        }
        if (const Sub *a45 = a34->a.as<Sub>()) {
          return ((a45->a + a34->b) < (a45->b + a12->b));
        }
        if (const Sub *a48 = a34->b.as<Sub>()) {
          return ((a48->a + a34->a) < (a48->b + a12->b));
        }
        if (const Add *a57 = a34->a.as<Add>()) {
          if (const Sub *a58 = a57->a.as<Sub>()) {
            return (((a58->a + a57->b) + a34->b) < (a12->b + a58->b));
          }
          if (const Sub *a62 = a57->b.as<Sub>()) {
            return (((a62->a + a57->a) + a34->b) < (a12->b + a62->b));
          }
          if (equal(a57->a, a12->b)) {
            return ((a57->b + a34->b) < 0);
          }
          if (equal(a57->b, a12->b)) {
            return ((a57->a + a34->b) < 0);
          }
          if (const Add *a134 = a12->b.as<Add>()) {
            if (equal(a57->a, a134->a)) {
              return ((a57->b + a34->b) < a134->b);
            }
            if (equal(a57->b, a134->a)) {
              return ((a57->a + a34->b) < a134->b);
            }
            if (equal(a57->a, a134->b)) {
              return ((a57->b + a34->b) < a134->a);
            }
            if (equal(a57->b, a134->b)) {
              return ((a57->a + a34->b) < a134->a);
            }
            if (const Add *a199 = a134->a.as<Add>()) {
              if (equal(a57->a, a199->a)) {
                return ((a57->b + a34->b) < (a199->b + a134->b));
              }
              if (equal(a57->b, a199->a)) {
                return ((a57->a + a34->b) < (a199->b + a134->b));
              }
              if (equal(a57->a, a199->b)) {
                return ((a57->b + a34->b) < (a199->a + a134->b));
              }
              if (equal(a57->b, a199->b)) {
                return ((a57->a + a34->b) < (a199->a + a134->b));
              }
            }
            if (const Add *a239 = a134->b.as<Add>()) {
              if (equal(a57->a, a239->a)) {
                return ((a57->b + a34->b) < (a239->b + a134->a));
              }
              if (equal(a57->b, a239->a)) {
                return ((a57->a + a34->b) < (a239->b + a134->a));
              }
              if (equal(a57->a, a239->b)) {
                return ((a57->b + a34->b) < (a239->a + a134->a));
              }
              if (equal(a57->b, a239->b)) {
                return ((a57->a + a34->b) < (a239->a + a134->a));
              }
            }
          }
        }
        if (const Add *a65 = a34->b.as<Add>()) {
          if (const Sub *a66 = a65->a.as<Sub>()) {
            return (((a66->a + a65->b) + a34->a) < (a12->b + a66->b));
          }
          if (const Sub *a70 = a65->b.as<Sub>()) {
            return (((a70->a + a65->a) + a34->a) < (a12->b + a70->b));
          }
          if (equal(a65->a, a12->b)) {
            return ((a34->a + a65->b) < 0);
          }
          if (equal(a65->b, a12->b)) {
            return ((a34->a + a65->a) < 0);
          }
          if (const Add *a142 = a12->b.as<Add>()) {
            if (equal(a65->a, a142->a)) {
              return ((a65->b + a34->a) < a142->b);
            }
            if (equal(a65->b, a142->a)) {
              return ((a65->a + a34->a) < a142->b);
            }
            if (equal(a65->a, a142->b)) {
              return ((a65->b + a34->a) < a142->a);
            }
            if (equal(a65->b, a142->b)) {
              return ((a65->a + a34->a) < a142->a);
            }
            if (const Add *a219 = a142->a.as<Add>()) {
              if (equal(a65->a, a219->a)) {
                return ((a65->b + a34->a) < (a219->b + a142->b));
              }
              if (equal(a65->b, a219->a)) {
                return ((a65->a + a34->a) < (a219->b + a142->b));
              }
              if (equal(a65->a, a219->b)) {
                return ((a65->b + a34->a) < (a219->a + a142->b));
              }
              if (equal(a65->b, a219->b)) {
                return ((a65->a + a34->a) < (a219->a + a142->b));
              }
            }
            if (const Add *a259 = a142->b.as<Add>()) {
              if (equal(a65->a, a259->a)) {
                return ((a65->b + a34->a) < (a259->b + a142->a));
              }
              if (equal(a65->b, a259->a)) {
                return ((a65->a + a34->a) < (a259->b + a142->a));
              }
              if (equal(a65->a, a259->b)) {
                return ((a65->b + a34->a) < (a259->a + a142->a));
              }
              if (equal(a65->b, a259->b)) {
                return ((a65->a + a34->a) < (a259->a + a142->a));
              }
            }
          }
        }
        if (equal(a34->a, a12->b)) {
          return (a34->b < 0);
        }
        if (equal(a34->b, a12->b)) {
          return (a34->a < 0);
        }
        if (const Add *a121 = a12->b.as<Add>()) {
          if (equal(a34->a, a121->a)) {
            return (a34->b < a121->b);
          }
          if (equal(a34->a, a121->b)) {
            return (a34->b < a121->a);
          }
          if (equal(a34->b, a121->a)) {
            return (a34->a < a121->b);
          }
          if (equal(a34->b, a121->b)) {
            return (a34->a < a121->a);
          }
          if (const Add *a166 = a121->a.as<Add>()) {
            if (equal(a34->a, a166->a)) {
              return (a34->b < (a166->b + a121->b));
            }
            if (equal(a34->a, a166->b)) {
              return (a34->b < (a166->a + a121->b));
            }
            if (equal(a34->b, a166->a)) {
              return (a34->a < (a166->b + a121->b));
            }
            if (equal(a34->b, a166->b)) {
              return (a34->a < (a166->a + a121->b));
            }
          }
          if (const Add *a174 = a121->b.as<Add>()) {
            if (equal(a34->a, a174->a)) {
              return (a34->b < (a174->b + a121->a));
            }
            if (equal(a34->a, a174->b)) {
              return (a34->b < (a174->a + a121->a));
            }
            if (equal(a34->b, a174->a)) {
              return (a34->a < (a174->b + a121->a));
            }
            if (equal(a34->b, a174->b)) {
              return (a34->a < (a174->a + a121->a));
            }
          }
        }
      }
      if (is_const_v(a12->a)) {
        if (const Sub *a36 = a12->b.as<Sub>()) {
          if (is_const_v(a36->a)) {
            return (a36->b < fold((a36->a - a12->a)));
          }
        }
        if (const Add *a38 = a12->b.as<Add>()) {
          if (is_const_v(a38->b)) {
            return (fold((a12->a - a38->b)) < a38->a);
          }
        }
        if (const Min *a381 = a12->b.as<Min>()) {
          if (is_const_v(a381->b)) {
            return ((a12->a < a381->a) && fold((a12->a < a381->b)));
            return ((a12->a < a381->a) || fold((a12->a < a381->b)));
          }
        }
        if (const Select *a529 = a12->b.as<Select>()) {
          if (is_const_v(a529->true_value)) {
            if (is_const_v(a529->false_value)) {
              return select(a529->condition, fold((a12->a < a529->true_value)), fold((a12->a < a529->false_value)));
            }
          }
        }
      }
      if (const Sub *a40 = a12->a.as<Sub>()) {
        return (a40->a < (a12->b + a40->b));
      }
      if (const Sub *a42 = a12->b.as<Sub>()) {
        return ((a12->a + a42->b) < a42->a);
      }
      if (const Add *a50 = a12->b.as<Add>()) {
        if (const Sub *a51 = a50->a.as<Sub>()) {
          return ((a12->a + a51->b) < (a51->a + a50->b));
        }
        if (const Sub *a54 = a50->b.as<Sub>()) {
          return ((a12->a + a54->b) < (a54->a + a50->a));
        }
        if (const Add *a73 = a50->a.as<Add>()) {
          if (const Sub *a74 = a73->a.as<Sub>()) {
            return ((a12->a + a74->b) < ((a74->a + a73->b) + a50->b));
          }
          if (const Sub *a78 = a73->b.as<Sub>()) {
            return ((a12->a + a78->b) < ((a78->a + a73->a) + a50->b));
          }
          if (equal(a12->a, a73->a)) {
            return (0 < (a73->b + a50->b));
          }
          if (equal(a12->a, a73->b)) {
            return (0 < (a73->a + a50->b));
          }
        }
        if (const Add *a81 = a50->b.as<Add>()) {
          if (const Sub *a82 = a81->a.as<Sub>()) {
            return ((a12->a + a82->b) < ((a82->a + a81->b) + a50->a));
          }
          if (const Sub *a86 = a81->b.as<Sub>()) {
            return ((a12->a + a86->b) < ((a86->a + a81->a) + a50->a));
          }
          if (equal(a12->a, a81->a)) {
            return (0 < (a50->a + a81->b));
          }
          if (equal(a12->a, a81->b)) {
            return (0 < (a50->a + a81->a));
          }
        }
        if (equal(a12->a, a50->a)) {
          return (0 < a50->b);
        }
        if (equal(a12->a, a50->b)) {
          return (0 < a50->a);
        }
        if (const Min *a306 = a50->a.as<Min>()) {
          if (const Add *a307 = a306->a.as<Add>()) {
            if (equal(a12->a, a307->a)) {
              if (is_const_v(a307->b)) {
                if (is_const_v(a50->b)) {
                  return ((a12->a < (a306->b + a50->b)) && fold((0 < (a307->b + a50->b))));
                  return ((a12->a < (a306->b + a50->b)) || fold((0 < (a307->b + a50->b))));
                }
              }
            }
          }
          if (const Add *a311 = a306->b.as<Add>()) {
            if (equal(a12->a, a311->a)) {
              if (is_const_v(a311->b)) {
                if (is_const_v(a50->b)) {
                  return ((a12->a < (a306->a + a50->b)) && fold((0 < (a311->b + a50->b))));
                  return ((a12->a < (a306->a + a50->b)) || fold((0 < (a311->b + a50->b))));
                }
              }
            }
          }
          if (equal(a12->a, a306->a)) {
            if (is_const_v(a50->b)) {
              return ((a12->a < (a306->b + a50->b)) && fold((0 < a50->b)));
              return ((a12->a < (a306->b + a50->b)) || fold((0 < a50->b)));
            }
          }
          if (equal(a12->a, a306->b)) {
            if (is_const_v(a50->b)) {
              return ((a12->a < (a306->a + a50->b)) && fold((0 < a50->b)));
              return ((a12->a < (a306->a + a50->b)) || fold((0 < a50->b)));
            }
          }
        }
        if (const Select *a486 = a50->a.as<Select>()) {
          if (const Add *a487 = a486->true_value.as<Add>()) {
            if (equal(a12->a, a487->a)) {
              if (is_const_v(a487->b)) {
                if (is_const_v(a50->b)) {
                  if (evaluate_predicate(fold(((a487->b + a50->b) <= 0)))) {
                    return (!(a486->condition) && (a12->a < (a486->false_value + a50->b)));
                  }
                  if (evaluate_predicate(fold(((a487->b + a50->b) > 0)))) {
                    return (a486->condition || (a12->a < (a486->false_value + a50->b)));
                  }
                }
              }
            }
          }
          if (const Add *a495 = a486->false_value.as<Add>()) {
            if (equal(a12->a, a495->a)) {
              if (is_const_v(a495->b)) {
                if (is_const_v(a50->b)) {
                  if (evaluate_predicate(fold(((a495->b + a50->b) <= 0)))) {
                    return (a486->condition && (a12->a < (a486->true_value + a50->b)));
                  }
                  if (evaluate_predicate(fold(((a495->b + a50->b) > 0)))) {
                    return (!(a486->condition) || (a12->a < (a486->true_value + a50->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Mul *a276 = a12->a.as<Mul>()) {
        if (is_const_v(a276->b)) {
          if (const Mul *a277 = a12->b.as<Mul>()) {
            if (equal(a276->b, a277->b)) {
              if (evaluate_predicate(fold((a276->b > 0)))) {
                return (a276->a < a277->a);
              }
              if (evaluate_predicate(fold((a276->b < 0)))) {
                return (a277->a < a276->a);
              }
            }
          }
        }
      }
      if (const Min *a289 = a12->a.as<Min>()) {
        if (const Add *a290 = a289->a.as<Add>()) {
          if (is_const_v(a290->b)) {
            if (const Add *a291 = a12->b.as<Add>()) {
              if (equal(a290->a, a291->a)) {
                if (is_const_v(a291->b)) {
                  return ((a289->b < (a290->a + a291->b)) || fold((a290->b < a291->b)));
                  return ((a289->b < (a290->a + a291->b)) && fold((a290->b < a291->b)));
                }
              }
            }
            if (equal(a290->a, a12->b)) {
              return ((a289->b < a290->a) || fold((a290->b < 0)));
              return ((a289->b < a290->a) && fold((a290->b < 0)));
            }
            if (const Min *a423 = a12->b.as<Min>()) {
              if (equal(a290->a, a423->b)) {
                if (evaluate_predicate(fold((a290->b < 0)))) {
                  return (min(a289->b, (a290->a + a290->b)) < a423->a);
                }
                if (evaluate_predicate(fold((a290->b > 0)))) {
                  return (min(a289->b, (a290->a + a290->b)) < a423->a);
                }
              }
              if (equal(a290->a, a423->a)) {
                if (evaluate_predicate(fold((a290->b < 0)))) {
                  return (min(a289->b, (a290->a + a290->b)) < a423->b);
                }
                if (evaluate_predicate(fold((a290->b > 0)))) {
                  return (min(a289->b, (a290->a + a290->b)) < a423->b);
                }
              }
            }
          }
        }
        if (const Add *a294 = a289->b.as<Add>()) {
          if (is_const_v(a294->b)) {
            if (const Add *a295 = a12->b.as<Add>()) {
              if (equal(a294->a, a295->a)) {
                if (is_const_v(a295->b)) {
                  return ((a289->a < (a294->a + a295->b)) || fold((a294->b < a295->b)));
                  return ((a289->a < (a294->a + a295->b)) && fold((a294->b < a295->b)));
                }
              }
            }
            if (equal(a294->a, a12->b)) {
              return ((a289->a < a294->a) || fold((a294->b < 0)));
              return ((a289->a < a294->a) && fold((a294->b < 0)));
            }
            if (const Min *a401 = a12->b.as<Min>()) {
              if (equal(a294->a, a401->b)) {
                if (evaluate_predicate(fold((a294->b < 0)))) {
                  return (min(a289->a, (a294->a + a294->b)) < a401->a);
                }
                if (evaluate_predicate(fold((a294->b > 0)))) {
                  return (min(a289->a, (a294->a + a294->b)) < a401->a);
                }
              }
              if (equal(a294->a, a401->a)) {
                if (evaluate_predicate(fold((a294->b < 0)))) {
                  return (min(a289->a, (a294->a + a294->b)) < a401->b);
                }
                if (evaluate_predicate(fold((a294->b > 0)))) {
                  return (min(a289->a, (a294->a + a294->b)) < a401->b);
                }
              }
            }
          }
        }
        if (const Add *a322 = a12->b.as<Add>()) {
          if (equal(a289->a, a322->a)) {
            if (is_const_v(a322->b)) {
              return ((a289->b < (a289->a + a322->b)) || fold((0 < a322->b)));
              return ((a289->b < (a289->a + a322->b)) && fold((0 < a322->b)));
            }
          }
          if (equal(a289->b, a322->a)) {
            if (is_const_v(a322->b)) {
              return ((a289->a < (a289->b + a322->b)) || fold((0 < a322->b)));
              return ((a289->a < (a289->b + a322->b)) && fold((0 < a322->b)));
            }
          }
        }
        if (equal(a289->a, a12->b)) {
          return (a289->b < a289->a);
        }
        if (equal(a289->b, a12->b)) {
          return (a289->a < a289->b);
        }
        if (is_const_v(a289->b)) {
          if (is_const_v(a12->b)) {
            return ((a289->a < a12->b) || fold((a289->b < a12->b)));
            return ((a289->a < a12->b) && fold((a289->b < a12->b)));
          }
        }
        if (const Min *a386 = a12->b.as<Min>()) {
          if (equal(a289->b, a386->b)) {
            return (a289->a < min(a386->a, a289->b));
            return (min(a289->a, a289->b) < a386->a);
          }
          if (equal(a289->b, a386->a)) {
            return (a289->a < min(a289->b, a386->b));
            return (min(a289->a, a289->b) < a386->b);
          }
          if (const Add *a393 = a386->b.as<Add>()) {
            if (equal(a289->b, a393->a)) {
              if (is_const_v(a393->b)) {
                if (evaluate_predicate(fold((a393->b > 0)))) {
                  return (min(a289->a, a289->b) < a386->a);
                }
                if (evaluate_predicate(fold((a393->b < 0)))) {
                  return (min(a289->a, a289->b) < a386->a);
                }
              }
            }
            if (equal(a289->a, a393->a)) {
              if (is_const_v(a393->b)) {
                if (evaluate_predicate(fold((a393->b > 0)))) {
                  return (min(a289->b, a289->a) < a386->a);
                }
                if (evaluate_predicate(fold((a393->b < 0)))) {
                  return (min(a289->b, a289->a) < a386->a);
                }
              }
            }
          }
          if (const Add *a397 = a386->a.as<Add>()) {
            if (equal(a289->b, a397->a)) {
              if (is_const_v(a397->b)) {
                if (evaluate_predicate(fold((a397->b > 0)))) {
                  return (min(a289->a, a289->b) < a386->b);
                }
                if (evaluate_predicate(fold((a397->b < 0)))) {
                  return (min(a289->a, a289->b) < a386->b);
                }
              }
            }
            if (equal(a289->a, a397->a)) {
              if (is_const_v(a397->b)) {
                if (evaluate_predicate(fold((a397->b > 0)))) {
                  return (min(a289->b, a289->a) < a386->b);
                }
                if (evaluate_predicate(fold((a397->b < 0)))) {
                  return (min(a289->b, a289->a) < a386->b);
                }
              }
            }
          }
          if (equal(a289->a, a386->b)) {
            return (a289->b < min(a386->a, a289->a));
            return (min(a289->b, a289->a) < a386->a);
          }
          if (equal(a289->a, a386->a)) {
            return (a289->b < min(a289->a, a386->b));
            return (min(a289->b, a289->a) < a386->b);
          }
        }
      }
      if (const Min *a357 = a12->b.as<Min>()) {
        if (const Add *a358 = a357->a.as<Add>()) {
          if (equal(a12->a, a358->a)) {
            if (is_const_v(a358->b)) {
              return ((a12->a < a357->b) && fold((0 < a358->b)));
              return ((a12->a < a357->b) || fold((0 < a358->b)));
            }
          }
        }
        if (const Add *a361 = a357->b.as<Add>()) {
          if (equal(a12->a, a361->a)) {
            if (is_const_v(a361->b)) {
              return ((a12->a < a357->a) && fold((0 < a361->b)));
              return ((a12->a < a357->a) || fold((0 < a361->b)));
            }
          }
        }
        if (equal(a12->a, a357->a)) {
          return (a12->a < a357->b);
        }
        if (equal(a12->a, a357->b)) {
          return (a12->a < a357->a);
        }
      }
      if (const Select *a473 = a12->b.as<Select>()) {
        if (const Add *a474 = a473->true_value.as<Add>()) {
          if (equal(a12->a, a474->a)) {
            if (is_const_v(a474->b)) {
              if (evaluate_predicate(fold((a474->b <= 0)))) {
                return (!(a473->condition) && (a12->a < a473->false_value));
              }
              if (evaluate_predicate(fold((a474->b > 0)))) {
                return (a473->condition || (a12->a < a473->false_value));
              }
            }
          }
        }
        if (const Add *a480 = a473->false_value.as<Add>()) {
          if (equal(a12->a, a480->a)) {
            if (is_const_v(a480->b)) {
              if (evaluate_predicate(fold((a480->b <= 0)))) {
                return (a473->condition && (a12->a < a473->true_value));
              }
              if (evaluate_predicate(fold((a480->b > 0)))) {
                return (!(a473->condition) || (a12->a < a473->true_value));
              }
            }
          }
        }
      }
      if (const Select *a501 = a12->a.as<Select>()) {
        if (const Add *a502 = a501->true_value.as<Add>()) {
          if (is_const_v(a502->b)) {
            if (equal(a502->a, a12->b)) {
              if (evaluate_predicate(fold((a502->b >= 0)))) {
                return (!(a501->condition) && (a501->false_value < a502->a));
              }
              if (evaluate_predicate(fold((a502->b < 0)))) {
                return (a501->condition || (a501->false_value < a502->a));
              }
            }
            if (const Add *a515 = a12->b.as<Add>()) {
              if (equal(a502->a, a515->a)) {
                if (is_const_v(a515->b)) {
                  if (evaluate_predicate(fold((a502->b >= a515->b)))) {
                    return (!(a501->condition) && (a501->false_value < (a502->a + a515->b)));
                  }
                  if (evaluate_predicate(fold((a502->b < a515->b)))) {
                    return (a501->condition || (a501->false_value < (a502->a + a515->b)));
                  }
                }
              }
            }
          }
        }
        if (const Add *a508 = a501->false_value.as<Add>()) {
          if (is_const_v(a508->b)) {
            if (equal(a508->a, a12->b)) {
              if (evaluate_predicate(fold((a508->b >= 0)))) {
                return (a501->condition && (a501->true_value < a508->a));
              }
              if (evaluate_predicate(fold((a508->b < 0)))) {
                return (!(a501->condition) || (a501->true_value < a508->a));
              }
            }
            if (const Add *a523 = a12->b.as<Add>()) {
              if (equal(a508->a, a523->a)) {
                if (is_const_v(a523->b)) {
                  if (evaluate_predicate(fold((a508->b >= a523->b)))) {
                    return (a501->condition && (a501->true_value < (a508->a + a523->b)));
                  }
                  if (evaluate_predicate(fold((a508->b < a523->b)))) {
                    return (!(a501->condition) || (a501->true_value < (a508->a + a523->b)));
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a501->true_value)) {
          if (is_const_v(a501->false_value)) {
            if (is_const_v(a12->b)) {
              return select(a501->condition, fold((a501->true_value < a12->b)), fold((a501->false_value < a12->b)));
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a24 = expr->a.as<Broadcast>()) {
    if (is_const_v(a24->lanes)) {
      if (const Broadcast *a25 = expr->b.as<Broadcast>()) {
        if (equal(a24->lanes, a25->lanes)) {
          return broadcast((a24->value < a25->value), a24->lanes);
        }
      }
    }
  }
  if (const Mod *a26 = expr->a.as<Mod>()) {
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
    if (const Mod *a27 = expr->b.as<Mod>()) {
      return ((a27->a % a27->b) != 0);
    }
  }
  if (expr->is_operand_no_overflow_int()) {
    if (const LT *a281 = expr.as<LT>()) {
      if (const Mul *a282 = a281->a.as<Mul>()) {
        if (is_const_v(a282->b)) {
          if (is_const_v(a281->b)) {
            if (evaluate_predicate(fold((a282->b > 0)))) {
              return (a282->a < fold((((a281->b + a282->b) - 1) / a282->b)));
            }
          }
          if (const Mul *a645 = a281->b.as<Mul>()) {
            if (is_const_v(a645->b)) {
              if (evaluate_predicate(fold((((a645->b % a282->b) == 0) && (a282->b > 0))))) {
                return (a282->a < (a645->a * fold((a645->b / a282->b))));
              }
              if (evaluate_predicate(fold((((a282->b % a645->b) == 0) && (a645->b > 0))))) {
                return ((a282->a * fold((a282->b / a645->b))) < a645->a);
              }
            }
          }
          if (const Add *a651 = a281->b.as<Add>()) {
            if (const Mul *a652 = a651->a.as<Mul>()) {
              if (equal(a282->b, a652->b)) {
                if (is_const_v(a651->b)) {
                  if (evaluate_predicate(fold((a282->b > 0)))) {
                    return (a282->a < (a652->a + fold((((a651->b + a282->b) - 1) / a282->b))));
                  }
                }
              }
            }
          }
        }
        if (const Div *a707 = a282->a.as<Div>()) {
          if (const Add *a708 = a707->a.as<Add>()) {
            if (is_const_v(a708->b)) {
              if (is_const_v(a707->b)) {
                if (equal(a707->b, a282->b)) {
                  if (const Add *a709 = a281->b.as<Add>()) {
                    if (equal(a708->a, a709->a)) {
                      if (evaluate_predicate(fold((a707->b > 0)))) {
                        return (a708->b < (((a708->a + a708->b) % a707->b) + a709->b));
                      }
                    }
                    if (equal(a708->a, a709->b)) {
                      if (evaluate_predicate(fold((a707->b > 0)))) {
                        return (a708->b < (((a708->a + a708->b) % a707->b) + a709->a));
                      }
                    }
                  }
                  if (equal(a708->a, a281->b)) {
                    if (evaluate_predicate(fold((a707->b > 0)))) {
                      return (a708->b < ((a708->a + a708->b) % a707->b));
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a707->b)) {
            if (equal(a707->b, a282->b)) {
              if (const Add *a796 = a281->b.as<Add>()) {
                if (equal(a707->a, a796->a)) {
                  if (evaluate_predicate(fold((a707->b > 0)))) {
                    return (0 < ((a707->a % a707->b) + a796->b));
                  }
                }
                if (equal(a707->a, a796->b)) {
                  if (evaluate_predicate(fold((a707->b > 0)))) {
                    return (0 < ((a707->a % a707->b) + a796->a));
                  }
                }
              }
              if (equal(a707->a, a281->b)) {
                if (evaluate_predicate(fold((a707->b > 0)))) {
                  return ((a707->a % a707->b) != 0);
                }
              }
            }
          }
        }
      }
      if (const Add *a654 = a281->a.as<Add>()) {
        if (const Mul *a655 = a654->a.as<Mul>()) {
          if (is_const_v(a655->b)) {
            if (is_const_v(a654->b)) {
              if (const Mul *a656 = a281->b.as<Mul>()) {
                if (equal(a655->b, a656->b)) {
                  if (evaluate_predicate(fold((a655->b > 0)))) {
                    return ((a655->a + fold((a654->b / a655->b))) < a656->a);
                  }
                }
              }
            }
          }
          if (const Div *a660 = a655->a.as<Div>()) {
            if (const Add *a661 = a660->a.as<Add>()) {
              if (is_const_v(a661->b)) {
                if (is_const_v(a660->b)) {
                  if (equal(a660->b, a655->b)) {
                    if (const Add *a662 = a281->b.as<Add>()) {
                      if (equal(a661->a, a662->a)) {
                        if (evaluate_predicate(fold((a660->b > 0)))) {
                          return ((a654->b + a661->b) < (((a661->a + a661->b) % a660->b) + a662->b));
                        }
                      }
                      if (equal(a661->a, a662->b)) {
                        if (evaluate_predicate(fold((a660->b > 0)))) {
                          return ((a654->b + a661->b) < (((a661->a + a661->b) % a660->b) + a662->a));
                        }
                      }
                    }
                    if (equal(a661->a, a281->b)) {
                      if (evaluate_predicate(fold((a660->b > 0)))) {
                        return ((a654->b + a661->b) < ((a661->a + a661->b) % a660->b));
                      }
                    }
                  }
                }
              }
            }
            if (is_const_v(a660->b)) {
              if (equal(a660->b, a655->b)) {
                if (const Add *a749 = a281->b.as<Add>()) {
                  if (equal(a660->a, a749->a)) {
                    if (evaluate_predicate(fold((a660->b > 0)))) {
                      return (a654->b < ((a660->a % a660->b) + a749->b));
                    }
                  }
                  if (equal(a660->a, a749->b)) {
                    if (evaluate_predicate(fold((a660->b > 0)))) {
                      return (a654->b < ((a660->a % a660->b) + a749->a));
                    }
                  }
                }
                if (equal(a660->a, a281->b)) {
                  if (evaluate_predicate(fold((a660->b > 0)))) {
                    return (a654->b < (a660->a % a660->b));
                  }
                }
              }
            }
          }
        }
        if (const Mul *a665 = a654->b.as<Mul>()) {
          if (const Div *a666 = a665->a.as<Div>()) {
            if (const Add *a667 = a666->a.as<Add>()) {
              if (is_const_v(a667->b)) {
                if (is_const_v(a666->b)) {
                  if (equal(a666->b, a665->b)) {
                    if (const Add *a668 = a281->b.as<Add>()) {
                      if (equal(a667->a, a668->a)) {
                        if (evaluate_predicate(fold((a666->b > 0)))) {
                          return ((a654->a + a667->b) < (((a667->a + a667->b) % a666->b) + a668->b));
                        }
                      }
                      if (equal(a667->a, a668->b)) {
                        if (evaluate_predicate(fold((a666->b > 0)))) {
                          return ((a654->a + a667->b) < (((a667->a + a667->b) % a666->b) + a668->a));
                        }
                      }
                    }
                    if (equal(a667->a, a281->b)) {
                      if (evaluate_predicate(fold((a666->b > 0)))) {
                        return ((a654->a + a667->b) < ((a667->a + a667->b) % a666->b));
                      }
                    }
                  }
                }
              }
            }
            if (is_const_v(a666->b)) {
              if (equal(a666->b, a665->b)) {
                if (const Add *a754 = a281->b.as<Add>()) {
                  if (equal(a666->a, a754->a)) {
                    if (evaluate_predicate(fold((a666->b > 0)))) {
                      return (a654->a < ((a666->a % a666->b) + a754->b));
                    }
                  }
                  if (equal(a666->a, a754->b)) {
                    if (evaluate_predicate(fold((a666->b > 0)))) {
                      return (a654->a < ((a666->a % a666->b) + a754->a));
                    }
                  }
                }
                if (equal(a666->a, a281->b)) {
                  if (evaluate_predicate(fold((a666->b > 0)))) {
                    return (a654->a < (a666->a % a666->b));
                  }
                }
              }
            }
          }
        }
        if (const Add *a683 = a281->b.as<Add>()) {
          if (const Mul *a684 = a683->a.as<Mul>()) {
            if (const Div *a685 = a684->a.as<Div>()) {
              if (const Add *a686 = a685->a.as<Add>()) {
                if (equal(a654->a, a686->a)) {
                  if (is_const_v(a686->b)) {
                    if (is_const_v(a685->b)) {
                      if (equal(a685->b, a684->b)) {
                        if (evaluate_predicate(fold((a685->b > 0)))) {
                          return ((((a654->a + a686->b) % a685->b) + a654->b) < (a683->b + a686->b));
                        }
                      }
                    }
                  }
                }
                if (equal(a654->b, a686->a)) {
                  if (is_const_v(a686->b)) {
                    if (is_const_v(a685->b)) {
                      if (equal(a685->b, a684->b)) {
                        if (evaluate_predicate(fold((a685->b > 0)))) {
                          return ((((a654->b + a686->b) % a685->b) + a654->a) < (a683->b + a686->b));
                        }
                      }
                    }
                  }
                }
              }
              if (equal(a654->a, a685->a)) {
                if (is_const_v(a685->b)) {
                  if (equal(a685->b, a684->b)) {
                    if (evaluate_predicate(fold((a685->b > 0)))) {
                      return (((a654->a % a685->b) + a654->b) < a683->b);
                    }
                  }
                }
              }
              if (equal(a654->b, a685->a)) {
                if (is_const_v(a685->b)) {
                  if (equal(a685->b, a684->b)) {
                    if (evaluate_predicate(fold((a685->b > 0)))) {
                      return (((a654->b % a685->b) + a654->a) < a683->b);
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a690 = a683->b.as<Mul>()) {
            if (const Div *a691 = a690->a.as<Div>()) {
              if (const Add *a692 = a691->a.as<Add>()) {
                if (equal(a654->a, a692->a)) {
                  if (is_const_v(a692->b)) {
                    if (is_const_v(a691->b)) {
                      if (equal(a691->b, a690->b)) {
                        if (evaluate_predicate(fold((a691->b > 0)))) {
                          return ((((a654->a + a692->b) % a691->b) + a654->b) < (a683->a + a692->b));
                        }
                      }
                    }
                  }
                }
                if (equal(a654->b, a692->a)) {
                  if (is_const_v(a692->b)) {
                    if (is_const_v(a691->b)) {
                      if (equal(a691->b, a690->b)) {
                        if (evaluate_predicate(fold((a691->b > 0)))) {
                          return ((((a654->b + a692->b) % a691->b) + a654->a) < (a683->a + a692->b));
                        }
                      }
                    }
                  }
                }
              }
              if (equal(a654->a, a691->a)) {
                if (is_const_v(a691->b)) {
                  if (equal(a691->b, a690->b)) {
                    if (evaluate_predicate(fold((a691->b > 0)))) {
                      return (((a654->a % a691->b) + a654->b) < a683->a);
                    }
                  }
                }
              }
              if (equal(a654->b, a691->a)) {
                if (is_const_v(a691->b)) {
                  if (equal(a691->b, a690->b)) {
                    if (evaluate_predicate(fold((a691->b > 0)))) {
                      return (((a654->b % a691->b) + a654->a) < a683->a);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Mul *a717 = a281->b.as<Mul>()) {
          if (const Div *a718 = a717->a.as<Div>()) {
            if (const Add *a719 = a718->a.as<Add>()) {
              if (equal(a654->a, a719->a)) {
                if (is_const_v(a719->b)) {
                  if (is_const_v(a718->b)) {
                    if (equal(a718->b, a717->b)) {
                      if (evaluate_predicate(fold((a718->b > 0)))) {
                        return ((((a654->a + a719->b) % a718->b) + a654->b) < a719->b);
                      }
                    }
                  }
                }
              }
              if (equal(a654->b, a719->a)) {
                if (is_const_v(a719->b)) {
                  if (is_const_v(a718->b)) {
                    if (equal(a718->b, a717->b)) {
                      if (evaluate_predicate(fold((a718->b > 0)))) {
                        return ((((a654->b + a719->b) % a718->b) + a654->a) < a719->b);
                      }
                    }
                  }
                }
              }
            }
            if (equal(a654->a, a718->a)) {
              if (is_const_v(a718->b)) {
                if (equal(a718->b, a717->b)) {
                  if (evaluate_predicate(fold((a718->b > 0)))) {
                    return (((a654->a % a718->b) + a654->b) < 0);
                  }
                }
              }
            }
            if (equal(a654->b, a718->a)) {
              if (is_const_v(a718->b)) {
                if (equal(a718->b, a717->b)) {
                  if (evaluate_predicate(fold((a718->b > 0)))) {
                    return (((a654->b % a718->b) + a654->a) < 0);
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a736 = a281->b.as<Add>()) {
        if (const Mul *a737 = a736->a.as<Mul>()) {
          if (const Div *a738 = a737->a.as<Div>()) {
            if (const Add *a739 = a738->a.as<Add>()) {
              if (equal(a281->a, a739->a)) {
                if (is_const_v(a739->b)) {
                  if (is_const_v(a738->b)) {
                    if (equal(a738->b, a737->b)) {
                      if (evaluate_predicate(fold((a738->b > 0)))) {
                        return (((a281->a + a739->b) % a738->b) < (a736->b + a739->b));
                      }
                    }
                  }
                }
              }
            }
            if (equal(a281->a, a738->a)) {
              if (is_const_v(a738->b)) {
                if (equal(a738->b, a737->b)) {
                  if (evaluate_predicate(fold((a738->b > 0)))) {
                    return ((a281->a % a738->b) < a736->b);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a742 = a736->b.as<Mul>()) {
          if (const Div *a743 = a742->a.as<Div>()) {
            if (const Add *a744 = a743->a.as<Add>()) {
              if (equal(a281->a, a744->a)) {
                if (is_const_v(a744->b)) {
                  if (is_const_v(a743->b)) {
                    if (equal(a743->b, a742->b)) {
                      if (evaluate_predicate(fold((a743->b > 0)))) {
                        return (((a281->a + a744->b) % a743->b) < (a736->a + a744->b));
                      }
                    }
                  }
                }
              }
            }
            if (equal(a281->a, a743->a)) {
              if (is_const_v(a743->b)) {
                if (equal(a743->b, a742->b)) {
                  if (evaluate_predicate(fold((a743->b > 0)))) {
                    return ((a281->a % a743->b) < a736->a);
                  }
                }
              }
            }
          }
        }
      }
      if (const Mul *a790 = a281->b.as<Mul>()) {
        if (const Div *a791 = a790->a.as<Div>()) {
          if (const Add *a792 = a791->a.as<Add>()) {
            if (equal(a281->a, a792->a)) {
              if (is_const_v(a792->b)) {
                if (is_const_v(a791->b)) {
                  if (equal(a791->b, a790->b)) {
                    if (evaluate_predicate(fold((a791->b > 0)))) {
                      return (((a281->a + a792->b) % a791->b) < a792->b);
                    }
                  }
                }
              }
            }
          }
          if (equal(a281->a, a791->a)) {
            if (is_const_v(a791->b)) {
              if (equal(a791->b, a790->b)) {
                if (evaluate_predicate(fold((a791->b > 0)))) {
                  return false;
                }
              }
            }
          }
        }
      }
      if (const Div *a832 = a281->a.as<Div>()) {
        if (const Add *a833 = a832->a.as<Add>()) {
          if (is_const_v(a833->b)) {
            if (is_const_v(a832->b)) {
              if (const Div *a834 = a281->b.as<Div>()) {
                if (const Add *a835 = a834->a.as<Add>()) {
                  if (equal(a833->a, a835->a)) {
                    if (is_const_v(a835->b)) {
                      if (equal(a832->b, a834->b)) {
                        if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= a835->b))))) {
                          return false;
                        }
                        if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= (a835->b - a832->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (equal(a833->a, a834->a)) {
                  if (equal(a832->b, a834->b)) {
                    if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= 0))))) {
                      return false;
                    }
                    if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= (0 - a832->b)))))) {
                      return true;
                    }
                  }
                }
              }
              if (const Add *a860 = a281->b.as<Add>()) {
                if (const Div *a861 = a860->a.as<Div>()) {
                  if (equal(a833->a, a861->a)) {
                    if (equal(a832->b, a861->b)) {
                      if (is_const_v(a860->b)) {
                        if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= (a860->b * a832->b)))))) {
                          return false;
                        }
                        if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= ((a860->b * a832->b) - a832->b)))))) {
                          return true;
                        }
                      }
                    }
                  }
                }
                if (const Min *a871 = a860->a.as<Min>()) {
                  if (const Div *a872 = a871->a.as<Div>()) {
                    if (equal(a833->a, a872->a)) {
                      if (equal(a832->b, a872->b)) {
                        if (is_const_v(a860->b)) {
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= (a860->b * a832->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= ((a860->b * a832->b) - a832->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (const Div *a906 = a871->b.as<Div>()) {
                    if (equal(a833->a, a906->a)) {
                      if (equal(a832->b, a906->b)) {
                        if (is_const_v(a860->b)) {
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= (a860->b * a832->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= ((a860->b * a832->b) - a832->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                }
              }
              if (const Min *a882 = a281->b.as<Min>()) {
                if (const Div *a883 = a882->a.as<Div>()) {
                  if (const Add *a884 = a883->a.as<Add>()) {
                    if (equal(a833->a, a884->a)) {
                      if (is_const_v(a884->b)) {
                        if (equal(a832->b, a883->b)) {
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= a884->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= (a884->b - a832->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a833->a, a883->a)) {
                    if (equal(a832->b, a883->b)) {
                      if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= (0 - a832->b)))))) {
                        return true;
                      }
                    }
                  }
                }
                if (const Div *a917 = a882->b.as<Div>()) {
                  if (const Add *a918 = a917->a.as<Add>()) {
                    if (equal(a833->a, a918->a)) {
                      if (is_const_v(a918->b)) {
                        if (equal(a832->b, a917->b)) {
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= a918->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= (a918->b - a832->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a833->a, a917->a)) {
                    if (equal(a832->b, a917->b)) {
                      if (evaluate_predicate(fold(((a832->b > 0) && (a833->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a832->b > 0) && (a833->b <= (0 - a832->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Min *a1046 = a833->a.as<Min>()) {
            if (const Add *a1047 = a1046->b.as<Add>()) {
              if (const Mul *a1048 = a1047->a.as<Mul>()) {
                if (is_const_v(a1048->b)) {
                  if (is_const_v(a1047->b)) {
                    if (is_const_v(a833->b)) {
                      if (equal(a1048->b, a832->b)) {
                        if (equal(a1048->a, a281->b)) {
                          if (evaluate_predicate(fold(((a1048->b > 0) && ((a1047->b + a833->b) < 0))))) {
                            return (((a1046->a + a833->b) / a1048->b) < a1048->a);
                            return true;
                          }
                          if (evaluate_predicate(fold(((a1048->b > 0) && ((a1047->b + a833->b) >= 0))))) {
                            return false;
                            return (((a1046->a + a833->b) / a1048->b) < a1048->a);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Mul *a1059 = a1046->b.as<Mul>()) {
              if (is_const_v(a1059->b)) {
                if (is_const_v(a833->b)) {
                  if (equal(a1059->b, a832->b)) {
                    if (equal(a1059->a, a281->b)) {
                      if (evaluate_predicate(fold(((a1059->b > 0) && (a833->b < 0))))) {
                        return (((a1046->a + a833->b) / a1059->b) < a1059->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1059->b > 0) && (a833->b >= 0))))) {
                        return false;
                        return (((a1046->a + a833->b) / a1059->b) < a1059->a);
                      }
                    }
                  }
                }
              }
            }
            if (const Add *a1069 = a1046->a.as<Add>()) {
              if (const Mul *a1070 = a1069->a.as<Mul>()) {
                if (is_const_v(a1070->b)) {
                  if (is_const_v(a1069->b)) {
                    if (is_const_v(a833->b)) {
                      if (equal(a1070->b, a832->b)) {
                        if (equal(a1070->a, a281->b)) {
                          if (evaluate_predicate(fold(((a1070->b > 0) && ((a1069->b + a833->b) < 0))))) {
                            return (((a1046->b + a833->b) / a1070->b) < a1070->a);
                            return true;
                          }
                          if (evaluate_predicate(fold(((a1070->b > 0) && ((a1069->b + a833->b) >= 0))))) {
                            return false;
                            return (((a1046->b + a833->b) / a1070->b) < a1070->a);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Mul *a1081 = a1046->a.as<Mul>()) {
              if (is_const_v(a1081->b)) {
                if (is_const_v(a833->b)) {
                  if (equal(a1081->b, a832->b)) {
                    if (equal(a1081->a, a281->b)) {
                      if (evaluate_predicate(fold(((a1081->b > 0) && (a833->b < 0))))) {
                        return (((a1046->b + a833->b) / a1081->b) < a1081->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1081->b > 0) && (a833->b >= 0))))) {
                        return false;
                        return (((a1046->b + a833->b) / a1081->b) < a1081->a);
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a832->b)) {
          if (const Div *a843 = a281->b.as<Div>()) {
            if (const Add *a844 = a843->a.as<Add>()) {
              if (equal(a832->a, a844->a)) {
                if (is_const_v(a844->b)) {
                  if (equal(a832->b, a843->b)) {
                    if (evaluate_predicate(fold(((a832->b > 0) && (0 >= a844->b))))) {
                      return false;
                    }
                    if (evaluate_predicate(fold(((a832->b > 0) && (0 <= (a844->b - a832->b)))))) {
                      return true;
                    }
                  }
                }
              }
            }
          }
          if (const Min *a1005 = a281->b.as<Min>()) {
            if (const Div *a1006 = a1005->a.as<Div>()) {
              if (const Add *a1007 = a1006->a.as<Add>()) {
                if (equal(a832->a, a1007->a)) {
                  if (is_const_v(a1007->b)) {
                    if (equal(a832->b, a1006->b)) {
                      if (evaluate_predicate(fold(((a832->b > 0) && (a1007->b < 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a832->b > 0) && (a832->b <= a1007->b))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
            if (const Div *a1016 = a1005->b.as<Div>()) {
              if (const Add *a1017 = a1016->a.as<Add>()) {
                if (equal(a832->a, a1017->a)) {
                  if (is_const_v(a1017->b)) {
                    if (equal(a832->b, a1016->b)) {
                      if (evaluate_predicate(fold(((a832->b > 0) && (a1017->b < 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a832->b > 0) && (a832->b <= a1017->b))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a1089 = a832->a.as<Min>()) {
          if (const Add *a1090 = a1089->b.as<Add>()) {
            if (const Mul *a1091 = a1090->a.as<Mul>()) {
              if (is_const_v(a1091->b)) {
                if (is_const_v(a1090->b)) {
                  if (equal(a1091->b, a832->b)) {
                    if (equal(a1091->a, a281->b)) {
                      if (evaluate_predicate(fold(((a1091->b > 0) && (a1090->b < 0))))) {
                        return ((a1089->a / a1091->b) < a1091->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1091->b > 0) && (a1090->b >= 0))))) {
                        return false;
                        return ((a1089->a / a1091->b) < a1091->a);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a1100 = a1089->b.as<Mul>()) {
            if (is_const_v(a1100->b)) {
              if (equal(a1100->b, a832->b)) {
                if (equal(a1100->a, a281->b)) {
                  if (evaluate_predicate(fold((a1100->b > 0)))) {
                    return false;
                    return ((a1089->a / a1100->b) < a1100->a);
                  }
                }
              }
            }
          }
          if (const Add *a1104 = a1089->a.as<Add>()) {
            if (const Mul *a1105 = a1104->a.as<Mul>()) {
              if (is_const_v(a1105->b)) {
                if (is_const_v(a1104->b)) {
                  if (equal(a1105->b, a832->b)) {
                    if (equal(a1105->a, a281->b)) {
                      if (evaluate_predicate(fold(((a1105->b > 0) && (a1104->b < 0))))) {
                        return ((a1089->b / a1105->b) < a1105->a);
                        return true;
                      }
                      if (evaluate_predicate(fold(((a1105->b > 0) && (a1104->b >= 0))))) {
                        return false;
                        return ((a1089->b / a1105->b) < a1105->a);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a1114 = a1089->a.as<Mul>()) {
            if (is_const_v(a1114->b)) {
              if (equal(a1114->b, a832->b)) {
                if (equal(a1114->a, a281->b)) {
                  if (evaluate_predicate(fold((a1114->b > 0)))) {
                    return false;
                    return ((a1089->b / a1114->b) < a1114->a);
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a936 = a281->a.as<Min>()) {
        if (const Div *a937 = a936->a.as<Div>()) {
          if (const Add *a938 = a937->a.as<Add>()) {
            if (is_const_v(a938->b)) {
              if (is_const_v(a937->b)) {
                if (const Div *a939 = a281->b.as<Div>()) {
                  if (const Add *a940 = a939->a.as<Add>()) {
                    if (equal(a938->a, a940->a)) {
                      if (is_const_v(a940->b)) {
                        if (equal(a937->b, a939->b)) {
                          if (evaluate_predicate(fold(((a937->b > 0) && (a938->b >= a940->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a937->b > 0) && (a938->b <= (a940->b - a937->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a938->a, a939->a)) {
                    if (equal(a937->b, a939->b)) {
                      if (evaluate_predicate(fold(((a937->b > 0) && (a938->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a937->b > 0) && ((a938->b + a937->b) <= 0))))) {
                        return true;
                      }
                    }
                  }
                }
                if (const Add *a983 = a281->b.as<Add>()) {
                  if (const Div *a984 = a983->a.as<Div>()) {
                    if (equal(a938->a, a984->a)) {
                      if (equal(a937->b, a984->b)) {
                        if (is_const_v(a983->b)) {
                          if (evaluate_predicate(fold(((a937->b > 0) && (a938->b >= (a983->b * a937->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a937->b > 0) && (a938->b <= ((a983->b * a937->b) - a937->b)))))) {
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
          if (is_const_v(a937->b)) {
            if (const Div *a950 = a281->b.as<Div>()) {
              if (const Add *a951 = a950->a.as<Add>()) {
                if (equal(a937->a, a951->a)) {
                  if (is_const_v(a951->b)) {
                    if (equal(a937->b, a950->b)) {
                      if (evaluate_predicate(fold(((a937->b > 0) && (0 >= a951->b))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a937->b > 0) && (0 <= (a951->b - a937->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (const Div *a959 = a936->b.as<Div>()) {
          if (const Add *a960 = a959->a.as<Add>()) {
            if (is_const_v(a960->b)) {
              if (is_const_v(a959->b)) {
                if (const Div *a961 = a281->b.as<Div>()) {
                  if (const Add *a962 = a961->a.as<Add>()) {
                    if (equal(a960->a, a962->a)) {
                      if (is_const_v(a962->b)) {
                        if (equal(a959->b, a961->b)) {
                          if (evaluate_predicate(fold(((a959->b > 0) && (a960->b >= a962->b))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a959->b > 0) && (a960->b <= (a962->b - a959->b)))))) {
                            return true;
                          }
                        }
                      }
                    }
                  }
                  if (equal(a960->a, a961->a)) {
                    if (equal(a959->b, a961->b)) {
                      if (evaluate_predicate(fold(((a959->b > 0) && (a960->b >= 0))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a959->b > 0) && ((a960->b + a959->b) <= 0))))) {
                        return true;
                      }
                    }
                  }
                }
                if (const Add *a995 = a281->b.as<Add>()) {
                  if (const Div *a996 = a995->a.as<Div>()) {
                    if (equal(a960->a, a996->a)) {
                      if (equal(a959->b, a996->b)) {
                        if (is_const_v(a995->b)) {
                          if (evaluate_predicate(fold(((a959->b > 0) && (a960->b >= (a995->b * a959->b)))))) {
                            return false;
                          }
                          if (evaluate_predicate(fold(((a959->b > 0) && (a960->b <= ((a995->b * a959->b) - a959->b)))))) {
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
          if (is_const_v(a959->b)) {
            if (const Div *a972 = a281->b.as<Div>()) {
              if (const Add *a973 = a972->a.as<Add>()) {
                if (equal(a959->a, a973->a)) {
                  if (is_const_v(a973->b)) {
                    if (equal(a959->b, a972->b)) {
                      if (evaluate_predicate(fold(((a959->b > 0) && (0 >= a973->b))))) {
                        return false;
                      }
                      if (evaluate_predicate(fold(((a959->b > 0) && (0 <= (a973->b - a959->b)))))) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a936->b)) {
          if (const Min *a1189 = a281->b.as<Min>()) {
            if (equal(a936->a, a1189->a)) {
              if (is_const_v(a1189->b)) {
                if (evaluate_predicate(fold((a936->b >= a1189->b)))) {
                  return false;
                }
              }
            }
          }
          if (const Add *a1192 = a281->b.as<Add>()) {
            if (const Min *a1193 = a1192->a.as<Min>()) {
              if (equal(a936->a, a1193->a)) {
                if (is_const_v(a1193->b)) {
                  if (is_const_v(a1192->b)) {
                    if (evaluate_predicate(fold(((a936->b >= (a1193->b + a1192->b)) && (a1192->b <= 0))))) {
                      return false;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Ramp *a1202 = a281->a.as<Ramp>()) {
        if (const Add *a1203 = a1202->base.as<Add>()) {
          if (const Mul *a1204 = a1203->a.as<Mul>()) {
            if (is_const_v(a1204->b)) {
              if (is_const_v(a1203->b)) {
                if (is_const_v(a1202->stride)) {
                  if (is_const_v(a1202->lanes)) {
                    if (const Broadcast *a1205 = a281->b.as<Broadcast>()) {
                      if (const Mul *a1206 = a1205->value.as<Mul>()) {
                        if (is_const_v(a1206->b)) {
                          if (equal(a1202->lanes, a1205->lanes)) {
                            if (evaluate_predicate(fold(((((a1206->b > 0) && ((a1204->b % a1206->b) == 0)) && (((a1203->b % a1206->b) + (a1202->stride * (a1202->lanes - 1))) < a1206->b)) && (((a1203->b % a1206->b) + (a1202->stride * (a1202->lanes - 1))) >= 0))))) {
                              return broadcast((((a1204->a * fold((a1204->b / a1206->b))) + fold((a1203->b / a1206->b))) < a1206->a), a1202->lanes);
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
        if (const Mul *a1209 = a1202->base.as<Mul>()) {
          if (is_const_v(a1209->b)) {
            if (is_const_v(a1202->stride)) {
              if (is_const_v(a1202->lanes)) {
                if (const Broadcast *a1210 = a281->b.as<Broadcast>()) {
                  if (const Mul *a1211 = a1210->value.as<Mul>()) {
                    if (is_const_v(a1211->b)) {
                      if (equal(a1202->lanes, a1210->lanes)) {
                        if (evaluate_predicate(fold(((((a1211->b > 0) && ((a1209->b % a1211->b) == 0)) && ((a1202->stride * (a1202->lanes - 1)) < a1211->b)) && ((a1202->stride * (a1202->lanes - 1)) >= 0))))) {
                          return broadcast(((a1209->a * fold((a1209->b / a1211->b))) < a1211->a), a1202->lanes);
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
    if (const LT *a283 = expr.as<LT>()) {
      if (const Mul *a284 = a283->a.as<Mul>()) {
        if (is_const_v(a284->b)) {
          if (is_const_v(a283->b)) {
            if (evaluate_predicate(fold((a284->b > 0)))) {
              return (a284->a < fold((a283->b / a284->b)));
            }
          }
        }
      }
      if (is_const_v(a283->a)) {
        if (const Div *a286 = a283->b.as<Div>()) {
          if (is_const_v(a286->b)) {
            if (evaluate_predicate(fold((a286->b < 0)))) {
              return (a286->a < fold((a283->a * a286->b)));
            }
          }
        }
      }
    }
  }
  return expr;
}
