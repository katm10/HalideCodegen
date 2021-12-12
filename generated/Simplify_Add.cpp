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
      if (equal(a34->cond, a35->cond)) {
        return select(a34->cond, (a34->true_value + a35->true_value), (a34->false_value + a35->false_value));
      }
    }
    if (is_const(a34->true_value)) {
      if (is_const(a34->false_value)) {
        if (is_const(expr->b)) {
          return select(a34->cond, fold((a34->true_value + expr->b)), fold((a34->false_value + expr->b)));
        }
      }
      if (const Add *a40 = a34->false_value.as<Add>()) {
        if (is_const(a40->b)) {
          if (is_const(expr->b)) {
            return select(a34->cond, fold((a34->true_value + expr->b)), (a40->a + fold((a40->b + expr->b))));
          }
        }
      }
    }
    if (const Add *a38 = a34->true_value.as<Add>()) {
      if (is_const(a38->b)) {
        if (is_const(a34->false_value)) {
          if (is_const(expr->b)) {
            return select(a34->cond, (a38->a + fold((a38->b + expr->b))), fold((a34->false_value + expr->b)));
          }
        }
        if (const Add *a43 = a34->false_value.as<Add>()) {
          if (is_const(a43->b)) {
            if (is_const(expr->b)) {
              return select(a34->cond, (a38->a + fold((a38->b + expr->b))), (a43->a + fold((a43->b + expr->b))));
            }
          }
        }
      }
    }
    if (const Add *a51 = expr->b.as<Add>()) {
      if (const Select *a52 = a51->a.as<Select>()) {
        if (equal(a34->cond, a52->cond)) {
          return (select(a34->cond, (a34->true_value + a52->true_value), (a34->false_value + a52->false_value)) + a51->b);
        }
      }
      if (const Select *a55 = a51->b.as<Select>()) {
        if (equal(a34->cond, a55->cond)) {
          return (select(a34->cond, (a34->true_value + a55->true_value), (a34->false_value + a55->false_value)) + a51->a);
        }
      }
    }
    if (const Sub *a57 = expr->b.as<Sub>()) {
      if (const Select *a58 = a57->a.as<Select>()) {
        if (equal(a34->cond, a58->cond)) {
          return (select(a34->cond, (a34->true_value + a58->true_value), (a34->false_value + a58->false_value)) - a57->b);
        }
      }
      if (const Select *a61 = a57->b.as<Select>()) {
        if (equal(a34->cond, a61->cond)) {
          return (select(a34->cond, (a34->true_value - a61->true_value), (a34->false_value - a61->false_value)) + a57->a);
        }
      }
    }
    if (const Sub *a63 = a34->true_value.as<Sub>()) {
      if (is_const(a63->a)) {
        if (is_const(a34->false_value)) {
          if (is_const(expr->b)) {
            return select(a34->cond, (fold((a63->a + expr->b)) - a63->b), fold((a34->false_value + expr->b)));
            return (fold((a63->a + expr->b)) - select(a34->cond, a63->b, fold((a63->a - a34->false_value))));
          }
        }
      }
    }
    if (const Add *a65 = a34->false_value.as<Add>()) {
      if (is_const(a65->b)) {
        if (is_const(expr->b)) {
          if (evaluate_predicate(fold(((a65->b + expr->b) == 0)))) {
            return select(a34->cond, (a34->true_value + expr->b), a65->a);
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
  if (const Min *a81 = expr->a.as<Min>()) {
    if (const Add *a82 = a81->b.as<Add>()) {
      if (const Mul *a83 = a82->a.as<Mul>()) {
        if (is_const(a83->b)) {
          if (const Mul *a84 = expr->b.as<Mul>()) {
            if (const Sub *a85 = a84->a.as<Sub>()) {
              if (equal(a83->a, a85->b)) {
                if (equal(a83->b, a84->b)) {
                  return (min((a81->a - (a83->a * a83->b)), a82->b) + (a85->a * a83->b));
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
  if (expr->is_no_overflow()) {
    if (const Add *a137 = expr.as<Add>()) {
      if (const Mul *a138 = a137->b.as<Mul>()) {
        if (equal(a137->a, a138->a)) {
          return (a137->a * (a138->b + 1));
        }
        if (equal(a137->a, a138->b)) {
          return ((a138->a + 1) * a137->a);
        }
      }
      if (const Mul *a142 = a137->a.as<Mul>()) {
        if (equal(a142->a, a137->b)) {
          return (a142->a * (a142->b + 1));
        }
        if (equal(a142->b, a137->b)) {
          if (evaluate_predicate(fold(!(is_const(a142->b))))) {
            return ((a142->a + 1) * a142->b);
          }
        }
      }
      if (const Div *a146 = a137->a.as<Div>()) {
        if (const Add *a147 = a146->a.as<Add>()) {
          if (is_const(a147->b)) {
            if (is_const(a146->b)) {
              if (is_const(a137->b)) {
                if (evaluate_predicate(fold((a146->b != 0)))) {
                  return ((a147->a + fold((a147->b + (a146->b * a137->b)))) / a146->b);
                }
              }
            }
          }
          if (is_const(a146->b)) {
            if (equal(a147->a, a137->b)) {
              if (evaluate_predicate(fold((a146->b != 0)))) {
                return (((fold((a146->b + 1)) * a147->a) + a147->b) / a146->b);
              }
            }
            if (equal(a147->b, a137->b)) {
              if (evaluate_predicate(fold((a146->b != 0)))) {
                return ((a147->a + (fold((a146->b + 1)) * a147->b)) / a146->b);
              }
            }
          }
        }
        if (const Sub *a158 = a146->a.as<Sub>()) {
          if (is_const(a158->a)) {
            if (is_const(a146->b)) {
              if (is_const(a137->b)) {
                if (evaluate_predicate(fold(((a158->a != 0) && (a146->b != 0))))) {
                  return ((fold((a158->a + (a146->b * a137->b))) - a158->b) / a146->b);
                }
              }
            }
          }
          if (is_const(a146->b)) {
            if (equal(a158->a, a137->b)) {
              if (evaluate_predicate(fold((a146->b != 0)))) {
                return (((fold((a146->b + 1)) * a158->a) - a158->b) / a146->b);
              }
            }
            if (equal(a158->b, a137->b)) {
              if (evaluate_predicate(fold((a146->b != 0)))) {
                return ((a158->a + (fold((a146->b - 1)) * a158->b)) / a146->b);
              }
            }
          }
        }
      }
      if (const Add *a149 = a137->a.as<Add>()) {
        if (const Div *a150 = a149->b.as<Div>()) {
          if (const Add *a151 = a150->a.as<Add>()) {
            if (is_const(a151->b)) {
              if (is_const(a150->b)) {
                if (is_const(a137->b)) {
                  if (evaluate_predicate(fold((a150->b != 0)))) {
                    return (a149->a + ((a151->a + fold((a151->b + (a150->b * a137->b)))) / a150->b));
                  }
                }
              }
            }
          }
        }
        if (const Div *a154 = a149->a.as<Div>()) {
          if (const Add *a155 = a154->a.as<Add>()) {
            if (is_const(a155->b)) {
              if (is_const(a154->b)) {
                if (is_const(a137->b)) {
                  if (evaluate_predicate(fold((a154->b != 0)))) {
                    return (a149->b + ((a155->a + fold((a155->b + (a154->b * a137->b)))) / a154->b));
                  }
                }
              }
            }
          }
        }
      }
      if (const Div *a160 = a137->b.as<Div>()) {
        if (const Add *a161 = a160->a.as<Add>()) {
          if (equal(a137->a, a161->a)) {
            if (is_const(a160->b)) {
              if (evaluate_predicate(fold((a160->b != 0)))) {
                return (((fold((a160->b + 1)) * a137->a) + a161->b) / a160->b);
              }
            }
          }
          if (equal(a137->a, a161->b)) {
            if (is_const(a160->b)) {
              if (evaluate_predicate(fold((a160->b != 0)))) {
                return (((fold((a160->b + 1)) * a137->a) + a161->a) / a160->b);
              }
            }
          }
        }
        if (const Sub *a167 = a160->a.as<Sub>()) {
          if (equal(a137->a, a167->b)) {
            if (is_const(a160->b)) {
              if (evaluate_predicate(fold((a160->b != 0)))) {
                return (((fold((a160->b - 1)) * a137->a) + a167->a) / a160->b);
              }
            }
          }
          if (equal(a137->a, a167->a)) {
            if (is_const(a160->b)) {
              if (evaluate_predicate(fold((a160->b != 0)))) {
                return (((fold((a160->b + 1)) * a137->a) - a167->b) / a160->b);
              }
            }
          }
        }
      }
      if (const Min *a184 = a137->a.as<Min>()) {
        if (const Sub *a185 = a184->b.as<Sub>()) {
          if (equal(a185->b, a137->b)) {
            return min((a184->a + a185->b), a185->a);
          }
        }
        if (const Sub *a188 = a184->a.as<Sub>()) {
          if (equal(a188->b, a137->b)) {
            return min(a188->a, (a184->b + a188->b));
          }
        }
        if (const Add *a191 = a184->b.as<Add>()) {
          if (is_const(a191->b)) {
            if (is_const(a137->b)) {
              if (evaluate_predicate(fold(((a191->b + a137->b) == 0)))) {
                return min((a184->a + a137->b), a191->a);
              }
            }
          }
          if (const Mul *a228 = a191->b.as<Mul>()) {
            if (is_const(a228->b)) {
              if (const Mul *a229 = a137->b.as<Mul>()) {
                if (equal(a228->a, a229->a)) {
                  if (is_const(a229->b)) {
                    if (evaluate_predicate(fold(((a228->b + a229->b) == 0)))) {
                      return min((a184->a + (a228->a * a229->b)), a191->a);
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a233 = a191->a.as<Mul>()) {
            if (is_const(a233->b)) {
              if (const Mul *a234 = a137->b.as<Mul>()) {
                if (equal(a233->a, a234->a)) {
                  if (is_const(a234->b)) {
                    if (evaluate_predicate(fold(((a233->b + a234->b) == 0)))) {
                      return min((a184->a + (a233->a * a234->b)), a191->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a194 = a184->a.as<Add>()) {
          if (is_const(a194->b)) {
            if (is_const(a137->b)) {
              if (evaluate_predicate(fold(((a194->b + a137->b) == 0)))) {
                return min(a194->a, (a184->b + a137->b));
              }
            }
          }
          if (const Mul *a242 = a194->b.as<Mul>()) {
            if (is_const(a242->b)) {
              if (const Mul *a243 = a137->b.as<Mul>()) {
                if (equal(a242->a, a243->a)) {
                  if (is_const(a243->b)) {
                    if (evaluate_predicate(fold(((a242->b + a243->b) == 0)))) {
                      return min(((a242->a * a243->b) + a184->b), a194->a);
                      return min(a194->a, ((a242->a * a243->b) + a184->b));
                    }
                  }
                }
              }
            }
          }
          if (const Mul *a247 = a194->a.as<Mul>()) {
            if (is_const(a247->b)) {
              if (const Mul *a248 = a137->b.as<Mul>()) {
                if (equal(a247->a, a248->a)) {
                  if (is_const(a248->b)) {
                    if (evaluate_predicate(fold(((a247->b + a248->b) == 0)))) {
                      return min(a194->b, ((a247->a * a248->b) + a184->b));
                      return min(((a247->a * a248->b) + a184->b), a194->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a221 = a137->b.as<Min>()) {
          if (equal(a184->a, a221->a)) {
            if (equal(a184->b, a221->b)) {
              return (a184->a + a184->b);
            }
          }
          if (equal(a184->b, a221->a)) {
            if (equal(a184->a, a221->b)) {
              return (a184->a + a184->b);
            }
          }
        }
        if (const Mul *a237 = a184->b.as<Mul>()) {
          if (is_const(a237->b)) {
            if (const Mul *a238 = a137->b.as<Mul>()) {
              if (equal(a237->a, a238->a)) {
                if (is_const(a238->b)) {
                  if (evaluate_predicate(fold(((a237->b + a238->b) == 0)))) {
                    return min((a184->a + (a237->a * a238->b)), 0);
                  }
                }
              }
            }
          }
        }
        if (const Mul *a251 = a184->a.as<Mul>()) {
          if (is_const(a251->b)) {
            if (const Mul *a252 = a137->b.as<Mul>()) {
              if (equal(a251->a, a252->a)) {
                if (is_const(a252->b)) {
                  if (evaluate_predicate(fold(((a251->b + a252->b) == 0)))) {
                    return min(((a251->a * a252->b) + a184->b), 0);
                  }
                }
              }
            }
          }
        }
      }
      if (const Min *a196 = a137->b.as<Min>()) {
        if (const Sub *a197 = a196->b.as<Sub>()) {
          if (equal(a137->a, a197->b)) {
            return min((a137->a + a196->a), a197->a);
          }
        }
        if (const Sub *a200 = a196->a.as<Sub>()) {
          if (equal(a137->a, a200->b)) {
            return min(a200->a, (a137->a + a196->b));
          }
        }
      }
    }
  }
  if (expr->is_no_overflow_int()) {
    if (const Add *a281 = expr.as<Add>()) {
      if (const Mul *a282 = a281->a.as<Mul>()) {
        if (const Div *a283 = a282->b.as<Div>()) {
          if (equal(a282->a, a283->b)) {
            if (const Mod *a284 = a281->b.as<Mod>()) {
              if (equal(a283->a, a284->a)) {
                if (equal(a282->a, a284->b)) {
                  return select((a282->a == 0), 0, a283->a);
                }
              }
            }
            if (const Add *a342 = a281->b.as<Add>()) {
              if (const Mod *a343 = a342->a.as<Mod>()) {
                if (equal(a283->a, a343->a)) {
                  if (equal(a282->a, a343->b)) {
                    return (select((a282->a == 0), 0, a283->a) + a342->b);
                  }
                }
              }
              if (const Mod *a363 = a342->b.as<Mod>()) {
                if (equal(a283->a, a363->a)) {
                  if (equal(a282->a, a363->b)) {
                    return (select((a282->a == 0), 0, a283->a) + a342->a);
                  }
                }
              }
            }
            if (const Sub *a352 = a281->b.as<Sub>()) {
              if (const Mod *a353 = a352->a.as<Mod>()) {
                if (equal(a283->a, a353->a)) {
                  if (equal(a282->a, a353->b)) {
                    return (select((a282->a == 0), 0, a283->a) - a352->b);
                  }
                }
              }
            }
          }
        }
        if (const Div *a287 = a282->a.as<Div>()) {
          if (equal(a287->b, a282->b)) {
            if (const Mod *a288 = a281->b.as<Mod>()) {
              if (equal(a287->a, a288->a)) {
                if (equal(a287->b, a288->b)) {
                  return select((a287->b == 0), 0, a287->a);
                }
              }
            }
            if (const Add *a347 = a281->b.as<Add>()) {
              if (const Mod *a348 = a347->a.as<Mod>()) {
                if (equal(a287->a, a348->a)) {
                  if (equal(a287->b, a348->b)) {
                    return (select((a287->b == 0), 0, a287->a) + a347->b);
                  }
                }
              }
              if (const Mod *a368 = a347->b.as<Mod>()) {
                if (equal(a287->a, a368->a)) {
                  if (equal(a287->b, a368->b)) {
                    return (select((a287->b == 0), 0, a287->a) + a347->a);
                  }
                }
              }
            }
            if (const Sub *a357 = a281->b.as<Sub>()) {
              if (const Mod *a358 = a357->a.as<Mod>()) {
                if (equal(a287->a, a358->a)) {
                  if (equal(a287->b, a358->b)) {
                    return (select((a287->b == 0), 0, a287->a) - a357->b);
                  }
                }
              }
            }
          }
        }
        if (const Add *a291 = a282->b.as<Add>()) {
          if (const Div *a292 = a291->b.as<Div>()) {
            if (equal(a282->a, a292->b)) {
              if (const Mod *a293 = a281->b.as<Mod>()) {
                if (equal(a292->a, a293->a)) {
                  if (equal(a282->a, a293->b)) {
                    return select((a282->a == 0), 0, ((a291->a * a282->a) + a292->a));
                  }
                }
              }
            }
          }
          if (const Div *a302 = a291->a.as<Div>()) {
            if (equal(a282->a, a302->b)) {
              if (const Mod *a303 = a281->b.as<Mod>()) {
                if (equal(a302->a, a303->a)) {
                  if (equal(a282->a, a303->b)) {
                    return select((a282->a == 0), 0, (a302->a + (a291->b * a282->a)));
                  }
                }
              }
            }
          }
        }
        if (const Add *a296 = a282->a.as<Add>()) {
          if (const Div *a297 = a296->b.as<Div>()) {
            if (equal(a297->b, a282->b)) {
              if (const Mod *a298 = a281->b.as<Mod>()) {
                if (equal(a297->a, a298->a)) {
                  if (equal(a297->b, a298->b)) {
                    return select((a297->b == 0), 0, ((a296->a * a297->b) + a297->a));
                  }
                }
              }
            }
          }
          if (const Div *a307 = a296->a.as<Div>()) {
            if (equal(a307->b, a282->b)) {
              if (const Mod *a308 = a281->b.as<Mod>()) {
                if (equal(a307->a, a308->a)) {
                  if (equal(a307->b, a308->b)) {
                    return select((a307->b == 0), 0, (a307->a + (a296->b * a307->b)));
                  }
                }
              }
            }
          }
        }
      }
      if (const Mod *a310 = a281->a.as<Mod>()) {
        if (const Add *a311 = a281->b.as<Add>()) {
          if (const Mul *a312 = a311->a.as<Mul>()) {
            if (equal(a310->b, a312->a)) {
              if (const Div *a313 = a312->b.as<Div>()) {
                if (equal(a310->a, a313->a)) {
                  if (equal(a310->b, a313->b)) {
                    return (select((a310->b == 0), 0, a310->a) + a311->b);
                  }
                }
              }
            }
            if (const Div *a318 = a312->a.as<Div>()) {
              if (equal(a310->a, a318->a)) {
                if (equal(a310->b, a318->b)) {
                  if (equal(a310->b, a312->b)) {
                    return (select((a310->b == 0), 0, a310->a) + a311->b);
                  }
                }
              }
            }
          }
          if (const Mul *a332 = a311->b.as<Mul>()) {
            if (equal(a310->b, a332->a)) {
              if (const Div *a333 = a332->b.as<Div>()) {
                if (equal(a310->a, a333->a)) {
                  if (equal(a310->b, a333->b)) {
                    return (select((a310->b == 0), 0, a310->a) + a311->a);
                  }
                }
              }
            }
            if (const Div *a338 = a332->a.as<Div>()) {
              if (equal(a310->a, a338->a)) {
                if (equal(a310->b, a338->b)) {
                  if (equal(a310->b, a332->b)) {
                    return (select((a310->b == 0), 0, a310->a) + a311->a);
                  }
                }
              }
            }
          }
        }
        if (const Sub *a321 = a281->b.as<Sub>()) {
          if (const Mul *a322 = a321->a.as<Mul>()) {
            if (equal(a310->b, a322->a)) {
              if (const Div *a323 = a322->b.as<Div>()) {
                if (equal(a310->a, a323->a)) {
                  if (equal(a310->b, a323->b)) {
                    return (select((a310->b == 0), 0, a310->a) - a321->b);
                  }
                }
              }
            }
            if (const Div *a328 = a322->a.as<Div>()) {
              if (equal(a310->a, a328->a)) {
                if (equal(a310->b, a328->b)) {
                  if (equal(a310->b, a322->b)) {
                    return (select((a310->b == 0), 0, a310->a) - a321->b);
                  }
                }
              }
            }
          }
        }
      }
      if (const Div *a370 = a281->a.as<Div>()) {
        if (is_const_int(a370->b, 2)) {
          if (const Mod *a372 = a281->b.as<Mod>()) {
            if (equal(a370->a, a372->a)) {
              if (is_const_int(a372->b, 2)) {
                return ((a370->a + 1) / 2);
              }
            }
          }
        }
      }
      if (const Mul *a375 = a281->b.as<Mul>()) {
        if (const Div *a376 = a375->a.as<Div>()) {
          if (const Sub *a377 = a376->a.as<Sub>()) {
            if (is_const(a377->a)) {
              if (equal(a281->a, a377->b)) {
                if (is_const(a376->b)) {
                  if (equal(a376->b, a375->b)) {
                    if (evaluate_predicate(fold((a376->b > 0)))) {
                      return (a377->a - ((a377->a - a281->a) % a376->b));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a380 = a375->a.as<Add>()) {
          if (const Div *a381 = a380->a.as<Div>()) {
            if (const Sub *a382 = a381->a.as<Sub>()) {
              if (is_const(a382->a)) {
                if (equal(a281->a, a382->b)) {
                  if (is_const(a381->b)) {
                    if (equal(a381->b, a375->b)) {
                      if (evaluate_predicate(fold((a381->b > 0)))) {
                        return (((a380->b * a381->b) - ((a382->a - a281->a) % a381->b)) + a382->a);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Div *a386 = a380->b.as<Div>()) {
            if (const Sub *a387 = a386->a.as<Sub>()) {
              if (is_const(a387->a)) {
                if (equal(a281->a, a387->b)) {
                  if (is_const(a386->b)) {
                    if (equal(a386->b, a375->b)) {
                      if (evaluate_predicate(fold((a386->b > 0)))) {
                        return (((a380->a * a386->b) - ((a387->a - a281->a) % a386->b)) + a387->a);
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
