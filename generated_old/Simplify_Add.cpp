#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_Add(const Add *expr, Simplify *simplifier) {
  if (is_const_int(expr->b, 0)) {
    return expr->a;
  }
  if (is_const_int(expr->a, 0)) {
    return expr->b;
  }
  if (is_const_v(expr->a)) {
    if (is_const_v(expr->b)) {
      return fold((expr->a + expr->b));
    }
  }
  if (equal(expr->a, expr->b)) {
    return (expr->a * 2);
  }
  if (const Ramp *a0 = expr->a.as<Ramp>()) {
    if (is_const_v(a0->lanes)) {
      if (const Ramp *a1 = expr->b.as<Ramp>()) {
        if (equal(a0->lanes, a1->lanes)) {
          return ramp((a0->base + a1->base), (a0->stride + a1->stride), a0->lanes);
        }
      }
      if (const Broadcast *a3 = expr->b.as<Broadcast>()) {
        if (equal(a0->lanes, a3->lanes)) {
          return ramp((a0->base + a3->value), a0->stride, a0->lanes);
        }
      }
    }
    if (const Broadcast *a43 = a0->base.as<Broadcast>()) {
      if (is_const_v(a43->lanes)) {
        if (is_const_v(a0->lanes)) {
          if (const Broadcast *a44 = expr->b.as<Broadcast>()) {
            if (is_const_v(a44->lanes)) {
              if (evaluate_predicate(fold((a44->lanes == (a43->lanes * a0->lanes))))) {
                return ramp(broadcast((a43->value + a44->value), a43->lanes), a0->stride, a0->lanes);
              }
            }
          }
        }
      }
    }
    if (const Ramp *a46 = a0->base.as<Ramp>()) {
      if (is_const_v(a46->lanes)) {
        if (is_const_v(a0->lanes)) {
          if (const Broadcast *a47 = expr->b.as<Broadcast>()) {
            if (is_const_v(a47->lanes)) {
              if (evaluate_predicate(fold((a47->lanes == (a46->lanes * a0->lanes))))) {
                return ramp(ramp((a46->base + a47->value), a46->stride, a46->lanes), a0->stride, a0->lanes);
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a4 = expr->a.as<Broadcast>()) {
    if (is_const_v(a4->lanes)) {
      if (const Broadcast *a5 = expr->b.as<Broadcast>()) {
        if (is_const_v(a5->lanes)) {
          if (evaluate_predicate(fold(((a5->lanes % a4->lanes) == 0)))) {
            return broadcast((a4->value + broadcast(a5->value, fold((a5->lanes / a4->lanes)))), a4->lanes);
          }
          if (evaluate_predicate(fold(((a4->lanes % a5->lanes) == 0)))) {
            return broadcast((a5->value + broadcast(a4->value, fold((a4->lanes / a5->lanes)))), a5->lanes);
          }
        }
      }
    }
  }
  if (const Add *a8 = expr->a.as<Add>()) {
    if (const Broadcast *a9 = a8->b.as<Broadcast>()) {
      if (is_const_v(a9->lanes)) {
        if (const Broadcast *a10 = expr->b.as<Broadcast>()) {
          if (is_const_v(a10->lanes)) {
            if (evaluate_predicate(fold(((a10->lanes % a9->lanes) == 0)))) {
              return (a8->a + broadcast((a9->value + broadcast(a10->value, fold((a10->lanes / a9->lanes)))), a9->lanes));
            }
            if (evaluate_predicate(fold(((a9->lanes % a10->lanes) == 0)))) {
              return (a8->a + broadcast((a10->value + broadcast(a9->value, fold((a9->lanes / a10->lanes)))), a10->lanes));
            }
          }
        }
      }
    }
    if (const Broadcast *a15 = a8->a.as<Broadcast>()) {
      if (is_const_v(a15->lanes)) {
        if (const Broadcast *a16 = expr->b.as<Broadcast>()) {
          if (is_const_v(a16->lanes)) {
            if (evaluate_predicate(fold(((a16->lanes % a15->lanes) == 0)))) {
              return (a8->b + broadcast((a15->value + broadcast(a16->value, fold((a16->lanes / a15->lanes)))), a15->lanes));
            }
            if (evaluate_predicate(fold(((a15->lanes % a16->lanes) == 0)))) {
              return (a8->b + broadcast((a16->value + broadcast(a15->value, fold((a15->lanes / a16->lanes)))), a16->lanes));
            }
          }
        }
      }
    }
    if (is_const_v(a8->b)) {
      if (is_const_v(expr->b)) {
        return (a8->a + fold((a8->b + expr->b)));
      }
      return ((a8->a + expr->b) + a8->b);
    }
    if (const Sub *a83 = a8->a.as<Sub>()) {
      if (equal(a83->b, expr->b)) {
        return (a83->a + a8->b);
      }
    }
    if (const Sub *a85 = a8->b.as<Sub>()) {
      if (equal(a85->b, expr->b)) {
        return (a8->a + a85->a);
      }
    }
  }
  if (const Sub *a20 = expr->a.as<Sub>()) {
    if (const Broadcast *a21 = a20->b.as<Broadcast>()) {
      if (is_const_v(a21->lanes)) {
        if (const Broadcast *a22 = expr->b.as<Broadcast>()) {
          if (is_const_v(a22->lanes)) {
            if (evaluate_predicate(fold(((a22->lanes % a21->lanes) == 0)))) {
              return (a20->a + broadcast((broadcast(a22->value, fold((a22->lanes / a21->lanes))) - a21->value), a21->lanes));
            }
            if (evaluate_predicate(fold(((a21->lanes % a22->lanes) == 0)))) {
              return (a20->a + broadcast((a22->value - broadcast(a21->value, fold((a21->lanes / a22->lanes)))), a22->lanes));
            }
          }
        }
      }
    }
    if (const Broadcast *a27 = a20->a.as<Broadcast>()) {
      if (is_const_v(a27->lanes)) {
        if (const Broadcast *a28 = expr->b.as<Broadcast>()) {
          if (is_const_v(a28->lanes)) {
            if (evaluate_predicate(fold(((a28->lanes % a27->lanes) == 0)))) {
              return (broadcast((a27->value + broadcast(a28->value, fold((a28->lanes / a27->lanes)))), a27->lanes) - a20->b);
            }
            if (evaluate_predicate(fold(((a27->lanes % a28->lanes) == 0)))) {
              return (broadcast((a28->value + broadcast(a27->value, fold((a27->lanes / a28->lanes)))), a28->lanes) - a20->b);
            }
          }
        }
      }
    }
    if (is_const_v(a20->a)) {
      if (is_const_v(expr->b)) {
        return (fold((a20->a + expr->b)) - a20->b);
      }
      return ((expr->b - a20->b) + a20->a);
    }
    if (equal(a20->b, expr->b)) {
      return a20->a;
    }
    if (const Sub *a92 = expr->b.as<Sub>()) {
      if (equal(a20->b, a92->a)) {
        return (a20->a - a92->b);
      }
      if (equal(a20->a, a92->b)) {
        return (a92->a - a20->b);
      }
    }
    if (const Add *a96 = expr->b.as<Add>()) {
      if (equal(a20->b, a96->a)) {
        return (a20->a + a96->b);
      }
      if (equal(a20->b, a96->b)) {
        return (a20->a + a96->a);
      }
    }
    if (const Sub *a102 = a20->a.as<Sub>()) {
      if (equal(a102->b, expr->b)) {
        return (a102->a - a20->b);
      }
      if (is_const_int(a102->a, 0)) {
        return (expr->b - (a102->b + a20->b));
      }
      if (is_const_v(a102->a)) {
        if (is_const_v(expr->b)) {
          return ((fold((a102->a + expr->b)) - a20->b) - a102->b);
        }
      }
    }
    if (const Add *a108 = a20->b.as<Add>()) {
      if (equal(a108->a, expr->b)) {
        return (a20->a - a108->b);
      }
      if (equal(a108->b, expr->b)) {
        return (a20->a - a108->a);
      }
    }
  }
  if (const Select *a32 = expr->a.as<Select>()) {
    if (const Select *a33 = expr->b.as<Select>()) {
      if (equal(a32->condition, a33->condition)) {
        return select(a32->condition, (a32->true_value + a33->true_value), (a32->false_value + a33->false_value));
      }
    }
    if (is_const_v(a32->true_value)) {
      if (is_const_v(a32->false_value)) {
        if (is_const_v(expr->b)) {
          return select(a32->condition, fold((a32->true_value + expr->b)), fold((a32->false_value + expr->b)));
        }
      }
      if (const Add *a38 = a32->false_value.as<Add>()) {
        if (is_const_v(a38->b)) {
          if (is_const_v(expr->b)) {
            return select(a32->condition, fold((a32->true_value + expr->b)), (a38->a + fold((a38->b + expr->b))));
          }
        }
      }
    }
    if (const Add *a36 = a32->true_value.as<Add>()) {
      if (is_const_v(a36->b)) {
        if (is_const_v(a32->false_value)) {
          if (is_const_v(expr->b)) {
            return select(a32->condition, (a36->a + fold((a36->b + expr->b))), fold((a32->false_value + expr->b)));
          }
        }
        if (const Add *a41 = a32->false_value.as<Add>()) {
          if (is_const_v(a41->b)) {
            if (is_const_v(expr->b)) {
              return select(a32->condition, (a36->a + fold((a36->b + expr->b))), (a41->a + fold((a41->b + expr->b))));
            }
          }
        }
      }
    }
    if (const Add *a49 = expr->b.as<Add>()) {
      if (const Select *a50 = a49->a.as<Select>()) {
        if (equal(a32->condition, a50->condition)) {
          return (select(a32->condition, (a32->true_value + a50->true_value), (a32->false_value + a50->false_value)) + a49->b);
        }
      }
      if (const Select *a53 = a49->b.as<Select>()) {
        if (equal(a32->condition, a53->condition)) {
          return (select(a32->condition, (a32->true_value + a53->true_value), (a32->false_value + a53->false_value)) + a49->a);
        }
      }
    }
    if (const Sub *a55 = expr->b.as<Sub>()) {
      if (const Select *a56 = a55->a.as<Select>()) {
        if (equal(a32->condition, a56->condition)) {
          return (select(a32->condition, (a32->true_value + a56->true_value), (a32->false_value + a56->false_value)) - a55->b);
        }
      }
      if (const Select *a59 = a55->b.as<Select>()) {
        if (equal(a32->condition, a59->condition)) {
          return (select(a32->condition, (a32->true_value - a59->true_value), (a32->false_value - a59->false_value)) + a55->a);
        }
      }
    }
    if (const Sub *a61 = a32->true_value.as<Sub>()) {
      if (is_const_v(a61->a)) {
        if (is_const_v(a32->false_value)) {
          if (is_const_v(expr->b)) {
            return select(a32->condition, (fold((a61->a + expr->b)) - a61->b), fold((a32->false_value + expr->b)));
            return (fold((a61->a + expr->b)) - select(a32->condition, a61->b, fold((a61->a - a32->false_value))));
          }
        }
      }
    }
    if (const Add *a63 = a32->false_value.as<Add>()) {
      if (is_const_v(a63->b)) {
        if (is_const_v(expr->b)) {
          if (evaluate_predicate(fold(((a63->b + expr->b) == 0)))) {
            return select(a32->condition, (a32->true_value + expr->b), a63->a);
          }
        }
      }
    }
  }
  if (const Mul *a66 = expr->b.as<Mul>()) {
    if (const Sub *a67 = a66->b.as<Sub>()) {
      if (is_const_int(a67->a, 0)) {
        if (is_const_int(a67->b, 1)) {
          return (expr->a - a66->a);
        }
      }
    }
  }
  if (const Mul *a68 = expr->a.as<Mul>()) {
    if (const Sub *a69 = a68->b.as<Sub>()) {
      if (is_const_int(a69->a, 0)) {
        if (is_const_int(a69->b, 1)) {
          return (expr->b - a68->a);
        }
      }
    }
    if (const Mul *a118 = expr->b.as<Mul>()) {
      if (equal(a68->b, a118->b)) {
        return ((a68->a + a118->a) * a68->b);
      }
      if (equal(a68->b, a118->a)) {
        return ((a68->a + a118->b) * a68->b);
      }
      if (equal(a68->a, a118->b)) {
        return (a68->a * (a68->b + a118->a));
      }
      if (equal(a68->a, a118->a)) {
        return (a68->a * (a68->b + a118->b));
      }
    }
    if (is_const_v(a68->b)) {
      if (const Mul *a126 = expr->b.as<Mul>()) {
        if (is_const_v(a126->b)) {
          if (evaluate_predicate(fold(((a126->b % a68->b) == 0)))) {
            return ((a68->a + (a126->a * fold((a126->b / a68->b)))) * a68->b);
          }
          if (evaluate_predicate(fold(((a68->b % a126->b) == 0)))) {
            return (((a68->a * fold((a68->b / a126->b))) + a126->a) * a126->b);
          }
        }
      }
    }
  }
  if (const Add *a72 = expr->b.as<Add>()) {
    if (is_const_v(a72->b)) {
      return ((expr->a + a72->a) + a72->b);
    }
    if (const Sub *a87 = a72->a.as<Sub>()) {
      if (equal(expr->a, a87->b)) {
        return (a87->a + a72->b);
      }
    }
    if (const Sub *a89 = a72->b.as<Sub>()) {
      if (equal(expr->a, a89->b)) {
        return (a72->a + a89->a);
      }
    }
  }
  if (const Min *a75 = expr->a.as<Min>()) {
    if (const Add *a76 = a75->b.as<Add>()) {
      if (const Mul *a77 = a76->a.as<Mul>()) {
        if (is_const_v(a77->b)) {
          if (const Mul *a78 = expr->b.as<Mul>()) {
            if (const Sub *a79 = a78->a.as<Sub>()) {
              if (equal(a77->a, a79->b)) {
                if (equal(a77->b, a78->b)) {
                  return (min((a75->a - (a77->a * a77->b)), a76->b) + (a79->a * a77->b));
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Sub *a81 = expr->b.as<Sub>()) {
    if (equal(expr->a, a81->b)) {
      return a81->a;
    }
    if (is_const_v(a81->a)) {
      return ((expr->a - a81->b) + a81->a);
    }
    if (const Sub *a100 = a81->a.as<Sub>()) {
      if (equal(expr->a, a100->b)) {
        return (a100->a - a81->b);
      }
      if (is_const_int(a100->a, 0)) {
        return (expr->a - (a100->b + a81->b));
      }
    }
    if (const Add *a104 = a81->b.as<Add>()) {
      if (equal(expr->a, a104->a)) {
        return (a81->a - a104->b);
      }
      if (equal(expr->a, a104->b)) {
        return (a81->a - a104->a);
      }
    }
  }
  if (expr->is_no_overflow()) {
    if (const Add *a129 = expr.as<Add>()) {
      if (const Mul *a130 = a129->b.as<Mul>()) {
        if (equal(a129->a, a130->a)) {
          return (a129->a * (a130->b + 1));
        }
        if (equal(a129->a, a130->b)) {
          return ((a130->a + 1) * a129->a);
        }
      }
      if (const Mul *a134 = a129->a.as<Mul>()) {
        if (equal(a134->a, a129->b)) {
          return (a134->a * (a134->b + 1));
        }
        if (equal(a134->b, a129->b)) {
          if (evaluate_predicate(fold(!(is_const(a134->b))))) {
            return ((a134->a + 1) * a134->b);
          }
        }
      }
      if (const Div *a138 = a129->a.as<Div>()) {
        if (const Add *a139 = a138->a.as<Add>()) {
          if (is_const_v(a139->b)) {
            if (is_const_v(a138->b)) {
              if (is_const_v(a129->b)) {
                if (evaluate_predicate(fold((a138->b != 0)))) {
                  return ((a139->a + fold((a139->b + (a138->b * a129->b)))) / a138->b);
                }
              }
            }
          }
          if (is_const_v(a138->b)) {
            if (equal(a139->a, a129->b)) {
              if (evaluate_predicate(fold((a138->b != 0)))) {
                return (((fold((a138->b + 1)) * a139->a) + a139->b) / a138->b);
              }
            }
            if (equal(a139->b, a129->b)) {
              if (evaluate_predicate(fold((a138->b != 0)))) {
                return ((a139->a + (fold((a138->b + 1)) * a139->b)) / a138->b);
              }
            }
          }
        }
        if (const Sub *a150 = a138->a.as<Sub>()) {
          if (is_const_v(a150->a)) {
            if (is_const_v(a138->b)) {
              if (is_const_v(a129->b)) {
                if (evaluate_predicate(fold(((a150->a != 0) && (a138->b != 0))))) {
                  return ((fold((a150->a + (a138->b * a129->b))) - a150->b) / a138->b);
                }
              }
            }
          }
          if (is_const_v(a138->b)) {
            if (equal(a150->a, a129->b)) {
              if (evaluate_predicate(fold((a138->b != 0)))) {
                return (((fold((a138->b + 1)) * a150->a) - a150->b) / a138->b);
              }
            }
            if (equal(a150->b, a129->b)) {
              if (evaluate_predicate(fold((a138->b != 0)))) {
                return ((a150->a + (fold((a138->b - 1)) * a150->b)) / a138->b);
              }
            }
          }
        }
      }
      if (const Add *a141 = a129->a.as<Add>()) {
        if (const Div *a142 = a141->b.as<Div>()) {
          if (const Add *a143 = a142->a.as<Add>()) {
            if (is_const_v(a143->b)) {
              if (is_const_v(a142->b)) {
                if (is_const_v(a129->b)) {
                  if (evaluate_predicate(fold((a142->b != 0)))) {
                    return (a141->a + ((a143->a + fold((a143->b + (a142->b * a129->b)))) / a142->b));
                  }
                }
              }
            }
          }
        }
        if (const Div *a146 = a141->a.as<Div>()) {
          if (const Add *a147 = a146->a.as<Add>()) {
            if (is_const_v(a147->b)) {
              if (is_const_v(a146->b)) {
                if (is_const_v(a129->b)) {
                  if (evaluate_predicate(fold((a146->b != 0)))) {
                    return (a141->b + ((a147->a + fold((a147->b + (a146->b * a129->b)))) / a146->b));
                  }
                }
              }
            }
          }
        }
      }
      if (const Div *a152 = a129->b.as<Div>()) {
        if (const Add *a153 = a152->a.as<Add>()) {
          if (equal(a129->a, a153->a)) {
            if (is_const_v(a152->b)) {
              if (evaluate_predicate(fold((a152->b != 0)))) {
                return (((fold((a152->b + 1)) * a129->a) + a153->b) / a152->b);
              }
            }
          }
          if (equal(a129->a, a153->b)) {
            if (is_const_v(a152->b)) {
              if (evaluate_predicate(fold((a152->b != 0)))) {
                return (((fold((a152->b + 1)) * a129->a) + a153->a) / a152->b);
              }
            }
          }
        }
        if (const Sub *a159 = a152->a.as<Sub>()) {
          if (equal(a129->a, a159->b)) {
            if (is_const_v(a152->b)) {
              if (evaluate_predicate(fold((a152->b != 0)))) {
                return (((fold((a152->b - 1)) * a129->a) + a159->a) / a152->b);
              }
            }
          }
          if (equal(a129->a, a159->a)) {
            if (is_const_v(a152->b)) {
              if (evaluate_predicate(fold((a152->b != 0)))) {
                return (((fold((a152->b + 1)) * a129->a) - a159->b) / a152->b);
              }
            }
          }
        }
      }
      if (const Min *a176 = a129->a.as<Min>()) {
        if (const Sub *a177 = a176->b.as<Sub>()) {
          if (equal(a177->b, a129->b)) {
            return min((a176->a + a177->b), a177->a);
          }
        }
        if (const Sub *a180 = a176->a.as<Sub>()) {
          if (equal(a180->b, a129->b)) {
            return min(a180->a, (a176->b + a180->b));
          }
        }
        if (const Add *a183 = a176->b.as<Add>()) {
          if (is_const_v(a183->b)) {
            if (is_const_v(a129->b)) {
              if (evaluate_predicate(fold(((a183->b + a129->b) == 0)))) {
                return min((a176->a + a129->b), a183->a);
              }
            }
          }
          if (const Mul *a220 = a183->b.as<Mul>()) {
            if (is_const_v(a220->b)) {
              if (const Mul *a221 = a129->b.as<Mul>()) {
                if (equal(a220->a, a221->a)) {
                  if (is_const_v(a221->b)) {
                    if (evaluate_predicate(fold(((a220->b + a221->b) == 0)))) {
                      return min((a176->a + (a220->a * a221->b)), a183->a);
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a225 = a183->a.as<Mul>()) {
            if (is_const_v(a225->b)) {
              if (const Mul *a226 = a129->b.as<Mul>()) {
                if (equal(a225->a, a226->a)) {
                  if (is_const_v(a226->b)) {
                    if (evaluate_predicate(fold(((a225->b + a226->b) == 0)))) {
                      return min((a176->a + (a225->a * a226->b)), a183->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a186 = a176->a.as<Add>()) {
          if (is_const_v(a186->b)) {
            if (is_const_v(a129->b)) {
              if (evaluate_predicate(fold(((a186->b + a129->b) == 0)))) {
                return min(a186->a, (a176->b + a129->b));
              }
            }
          }
          if (const Mul *a234 = a186->b.as<Mul>()) {
            if (is_const_v(a234->b)) {
              if (const Mul *a235 = a129->b.as<Mul>()) {
                if (equal(a234->a, a235->a)) {
                  if (is_const_v(a235->b)) {
                    if (evaluate_predicate(fold(((a234->b + a235->b) == 0)))) {
                      return min(((a234->a * a235->b) + a176->b), a186->a);
                      return min(a186->a, ((a234->a * a235->b) + a176->b));
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a239 = a186->a.as<Mul>()) {
            if (is_const_v(a239->b)) {
              if (const Mul *a240 = a129->b.as<Mul>()) {
                if (equal(a239->a, a240->a)) {
                  if (is_const_v(a240->b)) {
                    if (evaluate_predicate(fold(((a239->b + a240->b) == 0)))) {
                      return min(a186->b, ((a239->a * a240->b) + a176->b));
                      return min(((a239->a * a240->b) + a176->b), a186->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a213 = a129->b.as<Min>()) {
          if (equal(a176->a, a213->a)) {
            if (equal(a176->b, a213->b)) {
              return (a176->a + a176->b);
            }
          }
          if (equal(a176->b, a213->a)) {
            if (equal(a176->a, a213->b)) {
              return (a176->a + a176->b);
            }
          }
        }
        if (const Mul *a229 = a176->b.as<Mul>()) {
          if (is_const_v(a229->b)) {
            if (const Mul *a230 = a129->b.as<Mul>()) {
              if (equal(a229->a, a230->a)) {
                if (is_const_v(a230->b)) {
                  if (evaluate_predicate(fold(((a229->b + a230->b) == 0)))) {
                    return min((a176->a + (a229->a * a230->b)), 0);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a243 = a176->a.as<Mul>()) {
          if (is_const_v(a243->b)) {
            if (const Mul *a244 = a129->b.as<Mul>()) {
              if (equal(a243->a, a244->a)) {
                if (is_const_v(a244->b)) {
                  if (evaluate_predicate(fold(((a243->b + a244->b) == 0)))) {
                    return min(((a243->a * a244->b) + a176->b), 0);
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a188 = a129->b.as<Min>()) {
        if (const Sub *a189 = a188->b.as<Sub>()) {
          if (equal(a129->a, a189->b)) {
            return min((a129->a + a188->a), a189->a);
          }
        }
        if (const Sub *a192 = a188->a.as<Sub>()) {
          if (equal(a129->a, a192->b)) {
            return min(a192->a, (a129->a + a188->b));
          }
        }
      }
    }
  }
  if (expr->is_no_overflow_int()) {
    if (const Add *a273 = expr.as<Add>()) {
      if (const Mul *a274 = a273->a.as<Mul>()) {
        if (const Div *a275 = a274->b.as<Div>()) {
          if (equal(a274->a, a275->b)) {
            if (const Mod *a276 = a273->b.as<Mod>()) {
              if (equal(a275->a, a276->a)) {
                if (equal(a274->a, a276->b)) {
                  return select((a274->a == 0), 0, a275->a);
                }
              }
            }
            if (const Add *a334 = a273->b.as<Add>()) {
              if (const Mod *a335 = a334->a.as<Mod>()) {
                if (equal(a275->a, a335->a)) {
                  if (equal(a274->a, a335->b)) {
                    return (select((a274->a == 0), 0, a275->a) + a334->b);
                  }
                }
              }
              if (const Mod *a355 = a334->b.as<Mod>()) {
                if (equal(a275->a, a355->a)) {
                  if (equal(a274->a, a355->b)) {
                    return (select((a274->a == 0), 0, a275->a) + a334->a);
                  }
                }
              }
            }
            if (const Sub *a344 = a273->b.as<Sub>()) {
              if (const Mod *a345 = a344->a.as<Mod>()) {
                if (equal(a275->a, a345->a)) {
                  if (equal(a274->a, a345->b)) {
                    return (select((a274->a == 0), 0, a275->a) - a344->b);
                  }
                }
              }
            }
          }
        }
        if (const Div *a279 = a274->a.as<Div>()) {
          if (equal(a279->b, a274->b)) {
            if (const Mod *a280 = a273->b.as<Mod>()) {
              if (equal(a279->a, a280->a)) {
                if (equal(a279->b, a280->b)) {
                  return select((a279->b == 0), 0, a279->a);
                }
              }
            }
            if (const Add *a339 = a273->b.as<Add>()) {
              if (const Mod *a340 = a339->a.as<Mod>()) {
                if (equal(a279->a, a340->a)) {
                  if (equal(a279->b, a340->b)) {
                    return (select((a279->b == 0), 0, a279->a) + a339->b);
                  }
                }
              }
              if (const Mod *a360 = a339->b.as<Mod>()) {
                if (equal(a279->a, a360->a)) {
                  if (equal(a279->b, a360->b)) {
                    return (select((a279->b == 0), 0, a279->a) + a339->a);
                  }
                }
              }
            }
            if (const Sub *a349 = a273->b.as<Sub>()) {
              if (const Mod *a350 = a349->a.as<Mod>()) {
                if (equal(a279->a, a350->a)) {
                  if (equal(a279->b, a350->b)) {
                    return (select((a279->b == 0), 0, a279->a) - a349->b);
                  }
                }
              }
            }
          }
        }
        if (const Add *a283 = a274->b.as<Add>()) {
          if (const Div *a284 = a283->b.as<Div>()) {
            if (equal(a274->a, a284->b)) {
              if (const Mod *a285 = a273->b.as<Mod>()) {
                if (equal(a284->a, a285->a)) {
                  if (equal(a274->a, a285->b)) {
                    return select((a274->a == 0), 0, ((a283->a * a274->a) + a284->a));
                  }
                }
              }
            }
          }
          if (const Div *a294 = a283->a.as<Div>()) {
            if (equal(a274->a, a294->b)) {
              if (const Mod *a295 = a273->b.as<Mod>()) {
                if (equal(a294->a, a295->a)) {
                  if (equal(a274->a, a295->b)) {
                    return select((a274->a == 0), 0, (a294->a + (a283->b * a274->a)));
                  }
                }
              }
            }
          }
        }
        if (const Add *a288 = a274->a.as<Add>()) {
          if (const Div *a289 = a288->b.as<Div>()) {
            if (equal(a289->b, a274->b)) {
              if (const Mod *a290 = a273->b.as<Mod>()) {
                if (equal(a289->a, a290->a)) {
                  if (equal(a289->b, a290->b)) {
                    return select((a289->b == 0), 0, ((a288->a * a289->b) + a289->a));
                  }
                }
              }
            }
          }
          if (const Div *a299 = a288->a.as<Div>()) {
            if (equal(a299->b, a274->b)) {
              if (const Mod *a300 = a273->b.as<Mod>()) {
                if (equal(a299->a, a300->a)) {
                  if (equal(a299->b, a300->b)) {
                    return select((a299->b == 0), 0, (a299->a + (a288->b * a299->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Mod *a302 = a273->a.as<Mod>()) {
        if (const Add *a303 = a273->b.as<Add>()) {
          if (const Mul *a304 = a303->a.as<Mul>()) {
            if (equal(a302->b, a304->a)) {
              if (const Div *a305 = a304->b.as<Div>()) {
                if (equal(a302->a, a305->a)) {
                  if (equal(a302->b, a305->b)) {
                    return (select((a302->b == 0), 0, a302->a) + a303->b);
                  }
                }
              }
            }
            if (const Div *a310 = a304->a.as<Div>()) {
              if (equal(a302->a, a310->a)) {
                if (equal(a302->b, a310->b)) {
                  if (equal(a302->b, a304->b)) {
                    return (select((a302->b == 0), 0, a302->a) + a303->b);
                  }
                }
              }
            }
          }
          if (const Mul *a324 = a303->b.as<Mul>()) {
            if (equal(a302->b, a324->a)) {
              if (const Div *a325 = a324->b.as<Div>()) {
                if (equal(a302->a, a325->a)) {
                  if (equal(a302->b, a325->b)) {
                    return (select((a302->b == 0), 0, a302->a) + a303->a);
                  }
                }
              }
            }
            if (const Div *a330 = a324->a.as<Div>()) {
              if (equal(a302->a, a330->a)) {
                if (equal(a302->b, a330->b)) {
                  if (equal(a302->b, a324->b)) {
                    return (select((a302->b == 0), 0, a302->a) + a303->a);
                  }
                }
              }
            }
          }
        }
        if (const Sub *a313 = a273->b.as<Sub>()) {
          if (const Mul *a314 = a313->a.as<Mul>()) {
            if (equal(a302->b, a314->a)) {
              if (const Div *a315 = a314->b.as<Div>()) {
                if (equal(a302->a, a315->a)) {
                  if (equal(a302->b, a315->b)) {
                    return (select((a302->b == 0), 0, a302->a) - a313->b);
                  }
                }
              }
            }
            if (const Div *a320 = a314->a.as<Div>()) {
              if (equal(a302->a, a320->a)) {
                if (equal(a302->b, a320->b)) {
                  if (equal(a302->b, a314->b)) {
                    return (select((a302->b == 0), 0, a302->a) - a313->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Div *a362 = a273->a.as<Div>()) {
        if (is_const_int(a362->b, 2)) {
          if (const Mod *a363 = a273->b.as<Mod>()) {
            if (equal(a362->a, a363->a)) {
              if (is_const_int(a363->b, 2)) {
                return ((a362->a + 1) / 2);
              }
            }
          }
        }
      }
      if (const Mul *a365 = a273->b.as<Mul>()) {
        if (const Div *a366 = a365->a.as<Div>()) {
          if (const Sub *a367 = a366->a.as<Sub>()) {
            if (is_const_v(a367->a)) {
              if (equal(a273->a, a367->b)) {
                if (is_const_v(a366->b)) {
                  if (equal(a366->b, a365->b)) {
                    if (evaluate_predicate(fold((a366->b > 0)))) {
                      return (a367->a - ((a367->a - a273->a) % a366->b));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a370 = a365->a.as<Add>()) {
          if (const Div *a371 = a370->a.as<Div>()) {
            if (const Sub *a372 = a371->a.as<Sub>()) {
              if (is_const_v(a372->a)) {
                if (equal(a273->a, a372->b)) {
                  if (is_const_v(a371->b)) {
                    if (equal(a371->b, a365->b)) {
                      if (evaluate_predicate(fold((a371->b > 0)))) {
                        return (((a370->b * a371->b) - ((a372->a - a273->a) % a371->b)) + a372->a);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Div *a376 = a370->b.as<Div>()) {
            if (const Sub *a377 = a376->a.as<Sub>()) {
              if (is_const_v(a377->a)) {
                if (equal(a273->a, a377->b)) {
                  if (is_const_v(a376->b)) {
                    if (equal(a376->b, a365->b)) {
                      if (evaluate_predicate(fold((a376->b > 0)))) {
                        return (((a370->a * a376->b) - ((a377->a - a273->a) % a376->b)) + a377->a);
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
  return expr;
}
