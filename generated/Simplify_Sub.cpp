ExprPtr Simplify_Sub(const Sub *expr, Simplify *simplifier) {
  if (is_const_int(expr->b, 0)) {
    return expr->a;
  }
  if (is_const_v(expr->a)) {
    if (is_const_v(expr->b)) {
      return fold((expr->a - expr->b));
    }
    if (const Select *a91 = expr->b->as<Select>()) {
      if (is_const_v(a91->a)) {
        if (is_const_v(a91->b)) {
          return select(a91->cond, fold((expr->a - a91->a)), fold((expr->a - a91->b)));
        }
      }
    }
  }
  if (equal(expr->a, expr->b)) {
    return 0;
  }
  if (const Ramp *a1 = expr->a->as<Ramp>()) {
    if (is_const_v(a1->lanes)) {
      if (const Ramp *a2 = expr->b->as<Ramp>()) {
        if (equal(a1->lanes, a2->lanes)) {
          return ramp((a1->base - a2->base), (a1->stride - a2->stride), a1->lanes);
        }
      }
      if (const Broadcast *a4 = expr->b->as<Broadcast>()) {
        if (equal(a1->lanes, a4->lanes)) {
          return ramp((a1->base - a4->value), a1->stride, a1->lanes);
        }
      }
    }
    if (const Broadcast *a20 = a1->base->as<Broadcast>()) {
      if (is_const_v(a20->lanes)) {
        if (is_const_v(a1->lanes)) {
          if (const Broadcast *a21 = expr->b->as<Broadcast>()) {
            if (is_const_v(a21->lanes)) {
              if (evaluate_predicate(fold((a21->lanes == (a20->lanes * a1->lanes))))) {
                return ramp(broadcast((a20->value - a21->value), a20->lanes), a1->stride, a1->lanes);
              }
            }
          }
        }
      }
    }
    if (const Ramp *a23 = a1->base->as<Ramp>()) {
      if (is_const_v(a23->lanes)) {
        if (is_const_v(a1->lanes)) {
          if (const Broadcast *a24 = expr->b->as<Broadcast>()) {
            if (is_const_v(a24->lanes)) {
              if (evaluate_predicate(fold((a24->lanes == (a23->lanes * a1->lanes))))) {
                return ramp(ramp((a23->base - a24->value), a23->stride, a23->lanes), a1->stride, a1->lanes);
              }
            }
          }
        }
      }
    }
  }
  if (const Broadcast *a5 = expr->a->as<Broadcast>()) {
    if (is_const_v(a5->lanes)) {
      if (const Ramp *a6 = expr->b->as<Ramp>()) {
        if (equal(a5->lanes, a6->lanes)) {
          return ramp((a5->value - a6->base), (0 - a6->stride), a5->lanes);
        }
      }
      if (const Broadcast *a8 = expr->b->as<Broadcast>()) {
        if (equal(a5->lanes, a8->lanes)) {
          return broadcast((a5->value - a8->value), a5->lanes);
        }
        if (is_const_v(a8->lanes)) {
          if (evaluate_predicate(fold(((a8->lanes % a5->lanes) == 0)))) {
            return broadcast((a5->value - broadcast(a8->value, fold((a8->lanes / a5->lanes)))), a5->lanes);
          }
          if (evaluate_predicate(fold(((a5->lanes % a8->lanes) == 0)))) {
            return broadcast((broadcast(a5->value, fold((a5->lanes / a8->lanes))) - a8->value), a8->lanes);
          }
        }
      }
    }
  }
  if (const Sub *a13 = expr->a->as<Sub>()) {
    if (const Broadcast *a14 = a13->b->as<Broadcast>()) {
      if (is_const_v(a14->lanes)) {
        if (const Broadcast *a15 = expr->b->as<Broadcast>()) {
          if (equal(a14->lanes, a15->lanes)) {
            return (a13->a - broadcast((a14->value + a15->value), a14->lanes));
          }
        }
      }
    }
    if (equal(a13->a, expr->b)) {
      return (0 - a13->b);
    }
    if (const Select *a89 = a13->a->as<Select>()) {
      if (const Select *a90 = expr->b->as<Select>()) {
        if (equal(a89->cond, a90->cond)) {
          return (select(a89->cond, (a89->a - a90->a), (a89->b - a90->b)) - a13->b);
        }
      }
    }
    if (is_const_v(a13->a)) {
      if (const Sub *a99 = expr->b->as<Sub>()) {
        if (is_const_v(a99->a)) {
          return ((a99->b - a13->b) + fold((a13->a - a99->a)));
        }
      }
      if (const Add *a101 = expr->b->as<Add>()) {
        if (is_const_v(a101->b)) {
          return (fold((a13->a - a101->b)) - (a13->b + a101->a));
        }
      }
      if (is_const_v(expr->b)) {
        return (fold((a13->a - expr->b)) - a13->b);
      }
    }
    if (const Mul *a127 = a13->b->as<Mul>()) {
      if (const Mul *a128 = expr->b->as<Mul>()) {
        if (equal(a127->b, a128->b)) {
          return (a13->a - ((a127->a + a128->a) * a127->b));
        }
        if (equal(a127->b, a128->a)) {
          return (a13->a - ((a127->a + a128->b) * a127->b));
        }
        if (equal(a127->a, a128->b)) {
          return (a13->a - (a127->a * (a127->b + a128->a)));
        }
        if (equal(a127->a, a128->a)) {
          return (a13->a - (a127->a * (a127->b + a128->b)));
        }
      }
    }
    if (const Mul *a151 = a13->a->as<Mul>()) {
      if (const Mul *a152 = expr->b->as<Mul>()) {
        if (equal(a151->b, a152->b)) {
          return (((a151->a - a152->a) * a151->b) - a13->b);
        }
        if (equal(a151->b, a152->a)) {
          return (((a151->a - a152->b) * a151->b) - a13->b);
        }
        if (equal(a151->a, a152->b)) {
          return ((a151->a * (a151->b - a152->a)) - a13->b);
        }
        if (equal(a151->a, a152->a)) {
          return ((a151->a * (a151->b - a152->b)) - a13->b);
        }
      }
    }
    if (const Add *a267 = expr->b->as<Add>()) {
      if (equal(a13->a, a267->a)) {
        return ((0 - a13->b) - a267->b);
      }
      if (equal(a13->a, a267->b)) {
        return ((0 - a13->b) - a267->a);
      }
    }
    if (const Add *a271 = a13->a->as<Add>()) {
      if (equal(a271->a, expr->b)) {
        return (a271->b - a13->b);
      }
      if (equal(a271->b, expr->b)) {
        return (a271->a - a13->b);
      }
    }
    if (const Sub *a295 = a13->a->as<Sub>()) {
      if (equal(a295->a, expr->b)) {
        return (0 - (a295->b + a13->b));
      }
    }
  }
  if (const Add *a16 = expr->a->as<Add>()) {
    if (const Broadcast *a17 = a16->b->as<Broadcast>()) {
      if (is_const_v(a17->lanes)) {
        if (const Broadcast *a18 = expr->b->as<Broadcast>()) {
          if (equal(a17->lanes, a18->lanes)) {
            return (a16->a + broadcast((a17->value - a18->value), a17->lanes));
          }
        }
      }
    }
    if (equal(a16->a, expr->b)) {
      return a16->b;
    }
    if (equal(a16->b, expr->b)) {
      return a16->a;
    }
    if (const Select *a77 = a16->a->as<Select>()) {
      if (const Select *a78 = expr->b->as<Select>()) {
        if (equal(a77->cond, a78->cond)) {
          return (select(a77->cond, (a77->a - a78->a), (a77->b - a78->b)) + a16->b);
        }
      }
    }
    if (const Select *a80 = a16->b->as<Select>()) {
      if (const Select *a81 = expr->b->as<Select>()) {
        if (equal(a80->cond, a81->cond)) {
          return (select(a80->cond, (a80->a - a81->a), (a80->b - a81->b)) + a16->a);
        }
      }
    }
    if (is_const_v(a16->b)) {
      if (is_const_v(expr->b)) {
        return (a16->a + fold((a16->b - expr->b)));
      }
      if (const Sub *a94 = expr->b->as<Sub>()) {
        if (is_const_v(a94->a)) {
          return ((a16->a + a94->b) + fold((a16->b - a94->a)));
        }
      }
      if (const Add *a96 = expr->b->as<Add>()) {
        if (is_const_v(a96->b)) {
          return ((a16->a - a96->a) + fold((a16->b - a96->b)));
        }
      }
      return ((a16->a - expr->b) + a16->b);
    }
    if (const Mul *a115 = a16->b->as<Mul>()) {
      if (const Mul *a116 = expr->b->as<Mul>()) {
        if (equal(a115->b, a116->b)) {
          return (a16->a + ((a115->a - a116->a) * a115->b));
        }
        if (equal(a115->b, a116->a)) {
          return (a16->a + ((a115->a - a116->b) * a115->b));
        }
        if (equal(a115->a, a116->b)) {
          return (a16->a + (a115->a * (a115->b - a116->a)));
        }
        if (equal(a115->a, a116->a)) {
          return (a16->a + (a115->a * (a115->b - a116->b)));
        }
      }
    }
    if (const Mul *a139 = a16->a->as<Mul>()) {
      if (const Mul *a140 = expr->b->as<Mul>()) {
        if (equal(a139->b, a140->b)) {
          return (a16->b + ((a139->a - a140->a) * a139->b));
        }
        if (equal(a139->b, a140->a)) {
          return (a16->b + ((a139->a - a140->b) * a139->b));
        }
        if (equal(a139->a, a140->b)) {
          return (a16->b + (a139->a * (a139->b - a140->a)));
        }
        if (equal(a139->a, a140->a)) {
          return (a16->b + (a139->a * (a139->b - a140->b)));
        }
      }
    }
    if (const Add *a211 = expr->b->as<Add>()) {
      if (equal(a16->a, a211->a)) {
        return (a16->b - a211->b);
      }
      if (equal(a16->a, a211->b)) {
        return (a16->b - a211->a);
      }
      if (equal(a16->b, a211->a)) {
        return (a16->a - a211->b);
      }
      if (equal(a16->b, a211->b)) {
        return (a16->a - a211->a);
      }
      if (const Add *a244 = a211->b->as<Add>()) {
        if (equal(a16->a, a244->b)) {
          return (a16->b - (a211->a + a244->a));
        }
        if (equal(a16->b, a244->b)) {
          return (a16->a - (a211->a + a244->a));
        }
        if (equal(a16->a, a244->a)) {
          return (a16->b - (a211->a + a244->b));
        }
        if (equal(a16->b, a244->a)) {
          return (a16->a - (a211->a + a244->b));
        }
      }
      if (const Add *a256 = a211->a->as<Add>()) {
        if (equal(a16->a, a256->a)) {
          return (a16->b - (a256->b + a211->b));
        }
        if (equal(a16->b, a256->a)) {
          return (a16->a - (a256->b + a211->b));
        }
        if (equal(a16->a, a256->b)) {
          return (a16->b - (a256->a + a211->b));
        }
        if (equal(a16->b, a256->b)) {
          return (a16->a - (a256->a + a211->b));
        }
      }
    }
    if (const Add *a219 = a16->a->as<Add>()) {
      if (equal(a219->a, expr->b)) {
        return (a219->b + a16->b);
      }
      if (equal(a219->b, expr->b)) {
        return (a219->a + a16->b);
      }
    }
    if (const Add *a223 = a16->b->as<Add>()) {
      if (equal(a223->a, expr->b)) {
        return (a16->a + a223->b);
      }
      if (equal(a223->b, expr->b)) {
        return (a16->a + a223->a);
      }
    }
    if (const Sub *a231 = a16->b->as<Sub>()) {
      if (equal(a231->a, expr->b)) {
        return (a16->a - a231->b);
      }
    }
    if (const Sub *a233 = a16->a->as<Sub>()) {
      if (equal(a233->a, expr->b)) {
        return (a16->b - a233->b);
      }
    }
    if (const Min *a281 = expr->b->as<Min>()) {
      if (equal(a16->a, a281->a)) {
        if (equal(a16->b, a281->b)) {
          return min(a16->b, a16->a);
        }
      }
      if (equal(a16->b, a281->a)) {
        if (equal(a16->a, a281->b)) {
          return min(a16->b, a16->a);
          return min(a16->a, a16->b);
        }
      }
    }
  }
  if (const Select *a25 = expr->a->as<Select>()) {
    if (const Select *a26 = expr->b->as<Select>()) {
      if (equal(a25->cond, a26->cond)) {
        return select(a25->cond, (a25->a - a26->a), (a25->b - a26->b));
      }
    }
    if (equal(a25->a, expr->b)) {
      return select(a25->cond, 0, (a25->b - a25->a));
    }
    if (equal(a25->b, expr->b)) {
      return select(a25->cond, (a25->a - a25->b), 0);
    }
    if (const Add *a32 = a25->a->as<Add>()) {
      if (equal(a32->a, expr->b)) {
        return select(a25->cond, a32->b, (a25->b - a32->a));
      }
      if (equal(a32->b, expr->b)) {
        return select(a25->cond, a32->a, (a25->b - a32->b));
      }
      if (const Add *a41 = a32->b->as<Add>()) {
        if (equal(a41->b, expr->b)) {
          return select(a25->cond, (a32->a + a41->a), (a25->b - a41->b));
        }
        if (equal(a41->a, expr->b)) {
          return select(a25->cond, (a32->a + a41->b), (a25->b - a41->a));
        }
      }
      if (const Add *a47 = a32->a->as<Add>()) {
        if (equal(a47->a, expr->b)) {
          return select(a25->cond, (a32->b + a47->b), (a25->b - a47->a));
        }
        if (equal(a47->b, expr->b)) {
          return select(a25->cond, (a32->b + a47->a), (a25->b - a47->b));
        }
      }
      if (const Add *a53 = expr->b->as<Add>()) {
        if (equal(a32->a, a53->b)) {
          return (select(a25->cond, a32->b, (a25->b - a32->a)) - a53->a);
        }
        if (equal(a32->b, a53->b)) {
          return (select(a25->cond, a32->a, (a25->b - a32->b)) - a53->a);
        }
        if (equal(a32->a, a53->a)) {
          return (select(a25->cond, a32->b, (a25->b - a32->a)) - a53->b);
        }
        if (equal(a32->b, a53->a)) {
          return (select(a25->cond, a32->a, (a25->b - a32->b)) - a53->b);
        }
      }
    }
    if (const Add *a36 = a25->b->as<Add>()) {
      if (equal(a36->a, expr->b)) {
        return select(a25->cond, (a25->a - a36->a), a36->b);
      }
      if (equal(a36->b, expr->b)) {
        return select(a25->cond, (a25->a - a36->b), a36->a);
      }
    }
    if (const Add *a83 = expr->b->as<Add>()) {
      if (const Select *a84 = a83->a->as<Select>()) {
        if (equal(a25->cond, a84->cond)) {
          return (select(a25->cond, (a25->a - a84->a), (a25->b - a84->b)) - a83->b);
        }
      }
      if (const Select *a87 = a83->b->as<Select>()) {
        if (equal(a25->cond, a87->cond)) {
          return (select(a25->cond, (a25->a - a87->a), (a25->b - a87->b)) - a83->a);
        }
      }
    }
  }
  if (const Select *a29 = expr->b->as<Select>()) {
    if (equal(expr->a, a29->a)) {
      return select(a29->cond, 0, (expr->a - a29->b));
    }
    if (equal(expr->a, a29->b)) {
      return select(a29->cond, (expr->a - a29->a), 0);
    }
    if (const Add *a64 = a29->a->as<Add>()) {
      if (equal(expr->a, a64->a)) {
        return (0 - select(a29->cond, a64->b, (a29->b - expr->a)));
      }
      if (equal(expr->a, a64->b)) {
        return (0 - select(a29->cond, a64->a, (a29->b - expr->a)));
      }
    }
    if (const Add *a68 = a29->b->as<Add>()) {
      if (equal(expr->a, a68->a)) {
        return (0 - select(a29->cond, (a29->a - expr->a), a68->b));
      }
      if (equal(expr->a, a68->b)) {
        return (0 - select(a29->cond, (a29->a - expr->a), a68->a));
      }
    }
  }
  if (const Add *a73 = expr->b->as<Add>()) {
    if (equal(expr->a, a73->a)) {
      return (0 - a73->b);
    }
    if (equal(expr->a, a73->b)) {
      return (0 - a73->a);
    }
    if (is_const_v(a73->b)) {
      return ((expr->a - a73->a) - a73->b);
    }
    if (const Sub *a227 = a73->b->as<Sub>()) {
      if (equal(expr->a, a227->a)) {
        return (a227->b - a73->a);
      }
    }
    if (const Sub *a229 = a73->a->as<Sub>()) {
      if (equal(expr->a, a229->a)) {
        return (a229->b - a73->b);
      }
    }
    if (const Add *a235 = a73->b->as<Add>()) {
      if (equal(expr->a, a235->a)) {
        return (0 - (a73->a + a235->b));
      }
      if (equal(expr->a, a235->b)) {
        return (0 - (a73->a + a235->a));
      }
    }
    if (const Add *a239 = a73->a->as<Add>()) {
      if (equal(expr->a, a239->a)) {
        return (0 - (a239->b + a73->b));
      }
      if (equal(expr->a, a239->b)) {
        return (0 - (a239->a + a73->b));
      }
    }
  }
  if (const Sub *a102 = expr->b->as<Sub>()) {
    return (expr->a + (a102->b - a102->a));
  }
  if (const Mul *a103 = expr->b->as<Mul>()) {
    if (is_const_v(a103->b)) {
      if (evaluate_predicate(fold(((a103->b < 0) && (0 - (a103->b > 0)))))) {
        return (expr->a + (a103->a * fold((0 - a103->b))));
      }
    }
    if (const Div *a298 = a103->a->as<Div>()) {
      if (const Add *a299 = a298->a->as<Add>()) {
        if (equal(expr->a, a299->a)) {
          if (is_const_v(a299->b)) {
            if (is_const_v(a298->b)) {
              if (equal(a298->b, a103->b)) {
                if (evaluate_predicate(fold((a298->b > 0)))) {
                  return (((expr->a + a299->b) % a298->b) - a299->b);
                }
              }
            }
          }
        }
      }
    }
  }
  if (const Mul *a106 = expr->a->as<Mul>()) {
    if (const Mul *a107 = expr->b->as<Mul>()) {
      if (equal(a106->b, a107->b)) {
        return ((a106->a - a107->a) * a106->b);
      }
      if (equal(a106->b, a107->a)) {
        return ((a106->a - a107->b) * a106->b);
      }
      if (equal(a106->a, a107->b)) {
        return (a106->a * (a106->b - a107->a));
      }
      if (equal(a106->a, a107->a)) {
        return (a106->a * (a106->b - a107->b));
      }
    }
    if (const Add *a163 = expr->b->as<Add>()) {
      if (const Mul *a164 = a163->b->as<Mul>()) {
        if (equal(a106->b, a164->b)) {
          return (((a106->a - a164->a) * a106->b) - a163->a);
        }
        if (equal(a106->b, a164->a)) {
          return (((a106->a - a164->b) * a106->b) - a163->a);
        }
        if (equal(a106->a, a164->b)) {
          return ((a106->a * (a106->b - a164->a)) - a163->a);
        }
        if (equal(a106->a, a164->a)) {
          return ((a106->a * (a106->b - a164->b)) - a163->a);
        }
      }
      if (const Mul *a188 = a163->a->as<Mul>()) {
        if (equal(a106->b, a188->b)) {
          return (((a106->a - a188->a) * a106->b) - a163->b);
        }
        if (equal(a106->b, a188->a)) {
          return (((a106->a - a188->b) * a106->b) - a163->b);
        }
        if (equal(a106->a, a188->b)) {
          return ((a106->a * (a106->b - a188->a)) - a163->b);
        }
        if (equal(a106->a, a188->a)) {
          return ((a106->a * (a106->b - a188->b)) - a163->b);
        }
      }
    }
    if (const Sub *a175 = expr->b->as<Sub>()) {
      if (const Mul *a176 = a175->b->as<Mul>()) {
        if (equal(a106->b, a176->b)) {
          return (((a106->a + a176->a) * a106->b) - a175->a);
        }
        if (equal(a106->b, a176->a)) {
          return (((a106->a + a176->b) * a106->b) - a175->a);
        }
        if (equal(a106->a, a176->b)) {
          return ((a106->a * (a106->b + a176->a)) - a175->a);
        }
        if (equal(a106->a, a176->a)) {
          return ((a106->a * (a106->b + a176->b)) - a175->a);
        }
      }
      if (const Mul *a200 = a175->a->as<Mul>()) {
        if (equal(a106->b, a200->b)) {
          return (((a106->a - a200->a) * a106->b) + a175->b);
        }
        if (equal(a106->b, a200->a)) {
          return (((a106->a - a200->b) * a106->b) + a175->b);
        }
        if (equal(a106->a, a200->b)) {
          return ((a106->a * (a106->b - a200->a)) + a175->b);
        }
        if (equal(a106->a, a200->a)) {
          return ((a106->a * (a106->b - a200->b)) + a175->b);
        }
      }
    }
  }
  if (const Min *a274 = expr->b->as<Min>()) {
    if (const Sub *a275 = a274->a->as<Sub>()) {
      if (equal(expr->a, a275->a)) {
        if (is_const_int(a274->b, 0)) {
          return min(expr->a, a275->b);
        }
      }
    }
  }
  if (is_const_int(expr->a, 0)) {
    if (const Add *a289 = expr->b->as<Add>()) {
      if (const Sub *a290 = a289->b->as<Sub>()) {
        return (a290->b - (a289->a + a290->a));
      }
      if (const Sub *a293 = a289->a->as<Sub>()) {
        return (a293->b - (a293->a + a289->b));
      }
    }
  }
  if (const Mod *a296 = expr->b->as<Mod>()) {
    if (equal(expr->a, a296->a)) {
      if (is_const_v(a296->b)) {
        return ((expr->a / a296->b) * a296->b);
      }
    }
  }
  if (expr->is_no_overflow()) {
    if (const Sub *a300 = expr->as<Sub>()) {
      if (const Min *a301 = a300->a->as<Min>()) {
        if (equal(a301->a, a300->b)) {
          return min((a301->b - a301->a), 0);
        }
        if (equal(a301->b, a300->b)) {
          return min((a301->a - a301->b), 0);
        }
        if (const Sub *a322 = a301->a->as<Sub>()) {
          if (is_const_int(a301->b, 0)) {
            if (equal(a322->a, a300->b)) {
              return (0 - min(a322->a, a322->b));
            }
          }
        }
        if (const Add *a330 = a300->b->as<Add>()) {
          if (equal(a301->a, a330->a)) {
            if (equal(a301->b, a330->b)) {
              return (0 - min(a301->b, a301->a));
              return (0 - min(a301->a, a301->b));
            }
          }
          if (equal(a301->b, a330->a)) {
            if (equal(a301->a, a330->b)) {
              return (0 - min(a301->a, a301->b));
              return (0 - min(a301->b, a301->a));
            }
          }
        }
        if (const Add *a364 = a301->a->as<Add>()) {
          if (equal(a364->a, a300->b)) {
            return min((a301->b - a364->a), a364->b);
          }
          if (equal(a364->b, a300->b)) {
            return min((a301->b - a364->b), a364->a);
          }
          if (const Add *a393 = a364->b->as<Add>()) {
            if (equal(a393->b, a300->b)) {
              return min((a301->b - a393->b), (a364->a + a393->a));
            }
            if (equal(a393->a, a300->b)) {
              return min((a301->b - a393->a), (a364->a + a393->b));
            }
          }
          if (const Add *a401 = a364->a->as<Add>()) {
            if (equal(a401->b, a300->b)) {
              return min((a301->b - a401->b), (a401->a + a364->b));
            }
            if (equal(a401->a, a300->b)) {
              return min((a301->b - a401->a), (a401->b + a364->b));
            }
          }
          if (is_const_v(a364->b)) {
            if (const Min *a482 = a300->b->as<Min>()) {
              if (equal(a364->a, a482->a)) {
                if (evaluate_predicate(fold(can_prove((a301->b <= (a482->b + a364->b)), simplifier)))) {
                  return min((a301->b - min(a364->a, a482->b)), a364->b);
                  return min((min((a364->a + a364->b), a301->b) - a482->b), a364->b);
                }
                if (evaluate_predicate(fold(can_prove((a301->b >= (a482->b + a364->b)), simplifier)))) {
                  return min((min((a364->a + a364->b), a301->b) - a482->b), a364->b);
                  return min((a301->b - min(a364->a, a482->b)), a364->b);
                }
              }
              if (const Add *a499 = a482->a->as<Add>()) {
                if (equal(a364->a, a499->a)) {
                  if (is_const_v(a499->b)) {
                    if (evaluate_predicate(fold(can_prove(((a301->b + a499->b) <= (a482->b + a364->b)), simplifier)))) {
                      return min((a301->b - min((a364->a + a499->b), a482->b)), fold((a364->b - a499->b)));
                      return min((min((a364->a + a364->b), a301->b) - a482->b), fold((a364->b - a499->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a301->b + a499->b) >= (a482->b + a364->b)), simplifier)))) {
                      return min((min((a364->a + a364->b), a301->b) - a482->b), fold((a364->b - a499->b)));
                      return min((a301->b - min((a364->a + a499->b), a482->b)), fold((a364->b - a499->b)));
                    }
                  }
                }
              }
              if (equal(a364->a, a482->b)) {
                if (evaluate_predicate(fold(can_prove((a301->b <= (a482->a + a364->b)), simplifier)))) {
                  return min((a301->b - min(a364->a, a482->a)), a364->b);
                  return min((min((a364->a + a364->b), a301->b) - a482->a), a364->b);
                }
                if (evaluate_predicate(fold(can_prove((a301->b >= (a482->a + a364->b)), simplifier)))) {
                  return min((min((a364->a + a364->b), a301->b) - a482->a), a364->b);
                  return min((a301->b - min(a364->a, a482->a)), a364->b);
                }
              }
              if (const Add *a563 = a482->b->as<Add>()) {
                if (equal(a364->a, a563->a)) {
                  if (is_const_v(a563->b)) {
                    if (evaluate_predicate(fold(can_prove(((a301->b + a563->b) <= (a482->a + a364->b)), simplifier)))) {
                      return min((a301->b - min((a364->a + a563->b), a482->a)), fold((a364->b - a563->b)));
                      return min((min((a364->a + a364->b), a301->b) - a482->a), fold((a364->b - a563->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a301->b + a563->b) >= (a482->a + a364->b)), simplifier)))) {
                      return min((min((a364->a + a364->b), a301->b) - a482->a), fold((a364->b - a563->b)));
                      return min((a301->b - min((a364->a + a563->b), a482->a)), fold((a364->b - a563->b)));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Add *a370 = a301->b->as<Add>()) {
          if (equal(a370->a, a300->b)) {
            return min((a301->a - a370->a), a370->b);
          }
          if (equal(a370->b, a300->b)) {
            return min((a301->a - a370->b), a370->a);
          }
          if (const Add *a377 = a370->b->as<Add>()) {
            if (equal(a377->b, a300->b)) {
              return min((a301->a - a377->b), (a370->a + a377->a));
            }
            if (equal(a377->a, a300->b)) {
              return min((a301->a - a377->a), (a370->a + a377->b));
            }
          }
          if (const Add *a385 = a370->a->as<Add>()) {
            if (equal(a385->b, a300->b)) {
              return min((a301->a - a385->b), (a385->a + a370->b));
            }
            if (equal(a385->a, a300->b)) {
              return min((a301->a - a385->a), (a385->b + a370->b));
            }
          }
          if (is_const_v(a370->b)) {
            if (const Min *a514 = a300->b->as<Min>()) {
              if (equal(a370->a, a514->b)) {
                if (evaluate_predicate(fold(can_prove((a301->a <= (a514->a + a370->b)), simplifier)))) {
                  return min((a301->a - min(a370->a, a514->a)), a370->b);
                  return min((min((a370->a + a370->b), a301->a) - a514->a), a370->b);
                }
                if (evaluate_predicate(fold(can_prove((a301->a >= (a514->a + a370->b)), simplifier)))) {
                  return min((min((a370->a + a370->b), a301->a) - a514->a), a370->b);
                  return min((a301->a - min(a370->a, a514->a)), a370->b);
                }
              }
              if (const Add *a531 = a514->b->as<Add>()) {
                if (equal(a370->a, a531->a)) {
                  if (is_const_v(a531->b)) {
                    if (evaluate_predicate(fold(can_prove(((a301->a + a531->b) <= (a514->a + a370->b)), simplifier)))) {
                      return min((a301->a - min((a370->a + a531->b), a514->a)), fold((a370->b - a531->b)));
                      return min((min((a370->a + a370->b), a301->a) - a514->a), fold((a370->b - a531->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a301->a + a531->b) >= (a514->a + a370->b)), simplifier)))) {
                      return min((min((a370->a + a370->b), a301->a) - a514->a), fold((a370->b - a531->b)));
                      return min((a301->a - min((a370->a + a531->b), a514->a)), fold((a370->b - a531->b)));
                    }
                  }
                }
              }
              if (equal(a370->a, a514->a)) {
                if (evaluate_predicate(fold(can_prove((a301->a <= (a514->b + a370->b)), simplifier)))) {
                  return min((a301->a - min(a370->a, a514->b)), a370->b);
                  return min((min((a370->a + a370->b), a301->a) - a514->b), a370->b);
                }
                if (evaluate_predicate(fold(can_prove((a301->a >= (a514->b + a370->b)), simplifier)))) {
                  return min((min((a370->a + a370->b), a301->a) - a514->b), a370->b);
                  return min((a301->a - min(a370->a, a514->b)), a370->b);
                }
              }
              if (const Add *a595 = a514->a->as<Add>()) {
                if (equal(a370->a, a595->a)) {
                  if (is_const_v(a595->b)) {
                    if (evaluate_predicate(fold(can_prove(((a301->a + a595->b) <= (a514->b + a370->b)), simplifier)))) {
                      return min((a301->a - min((a370->a + a595->b), a514->b)), fold((a370->b - a595->b)));
                      return min((min((a370->a + a370->b), a301->a) - a514->b), fold((a370->b - a595->b)));
                    }
                    if (evaluate_predicate(fold(can_prove(((a301->a + a595->b) >= (a514->b + a370->b)), simplifier)))) {
                      return min((min((a370->a + a370->b), a301->a) - a514->b), fold((a370->b - a595->b)));
                      return min((a301->a - min((a370->a + a595->b), a514->b)), fold((a370->b - a595->b)));
                    }
                  }
                }
              }
            }
          }
        }
        if (const Min *a408 = a300->b->as<Min>()) {
          if (equal(a301->b, a408->a)) {
            if (equal(a301->a, a408->b)) {
              return 0;
            }
            if (evaluate_predicate(fold(can_prove((a301->a <= a408->b), simplifier)))) {
              return min((a301->a - min(a301->b, a408->b)), 0);
              return min((min(a301->b, a301->a) - a408->b), 0);
            }
            if (evaluate_predicate(fold(can_prove((a301->a >= a408->b), simplifier)))) {
              return min((min(a301->b, a301->a) - a408->b), 0);
              return min((a301->a - min(a301->b, a408->b)), 0);
            }
          }
          if (evaluate_predicate(fold(can_prove(((a301->a - a301->b) == (a408->a - a408->b)), simplifier)))) {
            return (a301->b - a408->b);
          }
          if (evaluate_predicate(fold(can_prove(((a301->a - a301->b) == (a408->b - a408->a)), simplifier)))) {
            return (a301->b - a408->a);
          }
          if (equal(a301->a, a408->a)) {
            if (evaluate_predicate(fold(can_prove((a301->b <= a408->b), simplifier)))) {
              return min((a301->b - min(a301->a, a408->b)), 0);
              return min((min(a301->a, a301->b) - a408->b), 0);
            }
            if (evaluate_predicate(fold(can_prove((a301->b >= a408->b), simplifier)))) {
              return min((min(a301->a, a301->b) - a408->b), 0);
              return min((a301->b - min(a301->a, a408->b)), 0);
            }
          }
          if (const Add *a490 = a408->a->as<Add>()) {
            if (equal(a301->a, a490->a)) {
              if (is_const_v(a490->b)) {
                if (evaluate_predicate(fold(can_prove(((a301->b + a490->b) <= a408->b), simplifier)))) {
                  return min((a301->b - min((a301->a + a490->b), a408->b)), fold((0 - a490->b)));
                  return min((min(a301->a, a301->b) - a408->b), fold((0 - a490->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a301->b + a490->b) >= a408->b), simplifier)))) {
                  return min((min(a301->a, a301->b) - a408->b), fold((0 - a490->b)));
                  return min((a301->b - min((a301->a + a490->b), a408->b)), fold((0 - a490->b)));
                }
              }
            }
            if (equal(a301->b, a490->a)) {
              if (is_const_v(a490->b)) {
                if (evaluate_predicate(fold(can_prove(((a301->a + a490->b) <= a408->b), simplifier)))) {
                  return min((a301->a - min((a301->b + a490->b), a408->b)), fold((0 - a490->b)));
                  return min((min(a301->b, a301->a) - a408->b), fold((0 - a490->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a301->a + a490->b) >= a408->b), simplifier)))) {
                  return min((min(a301->b, a301->a) - a408->b), fold((0 - a490->b)));
                  return min((a301->a - min((a301->b + a490->b), a408->b)), fold((0 - a490->b)));
                }
              }
            }
          }
          if (equal(a301->b, a408->b)) {
            if (evaluate_predicate(fold(can_prove((a301->a <= a408->a), simplifier)))) {
              return min((a301->a - min(a301->b, a408->a)), 0);
              return min((min(a301->b, a301->a) - a408->a), 0);
            }
            if (evaluate_predicate(fold(can_prove((a301->a >= a408->a), simplifier)))) {
              return min((min(a301->b, a301->a) - a408->a), 0);
              return min((a301->a - min(a301->b, a408->a)), 0);
            }
          }
          if (const Add *a522 = a408->b->as<Add>()) {
            if (equal(a301->b, a522->a)) {
              if (is_const_v(a522->b)) {
                if (evaluate_predicate(fold(can_prove(((a301->a + a522->b) <= a408->a), simplifier)))) {
                  return min((a301->a - min((a301->b + a522->b), a408->a)), fold((0 - a522->b)));
                  return min((min(a301->b, a301->a) - a408->a), fold((0 - a522->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a301->a + a522->b) >= a408->a), simplifier)))) {
                  return min((min(a301->b, a301->a) - a408->a), fold((0 - a522->b)));
                  return min((a301->a - min((a301->b + a522->b), a408->a)), fold((0 - a522->b)));
                }
              }
            }
            if (equal(a301->a, a522->a)) {
              if (is_const_v(a522->b)) {
                if (evaluate_predicate(fold(can_prove(((a301->b + a522->b) <= a408->a), simplifier)))) {
                  return min((a301->b - min((a301->a + a522->b), a408->a)), fold((0 - a522->b)));
                  return min((min(a301->a, a301->b) - a408->a), fold((0 - a522->b)));
                }
                if (evaluate_predicate(fold(can_prove(((a301->b + a522->b) >= a408->a), simplifier)))) {
                  return min((min(a301->a, a301->b) - a408->a), fold((0 - a522->b)));
                  return min((a301->b - min((a301->a + a522->b), a408->a)), fold((0 - a522->b)));
                }
              }
            }
          }
          if (equal(a301->a, a408->b)) {
            if (evaluate_predicate(fold(can_prove((a301->b <= a408->a), simplifier)))) {
              return min((a301->b - min(a301->a, a408->a)), 0);
              return min((min(a301->a, a301->b) - a408->a), 0);
            }
            if (evaluate_predicate(fold(can_prove((a301->b >= a408->a), simplifier)))) {
              return min((min(a301->a, a301->b) - a408->a), 0);
              return min((a301->b - min(a301->a, a408->a)), 0);
            }
          }
        }
        if (const Mul *a417 = a301->a->as<Mul>()) {
          if (is_const_v(a417->b)) {
            if (is_const_v(a301->b)) {
              if (const Mul *a418 = a300->b->as<Mul>()) {
                if (const Min *a419 = a418->a->as<Min>()) {
                  if (equal(a417->a, a419->a)) {
                    if (is_const_v(a419->b)) {
                      if (equal(a417->b, a418->b)) {
                        if (evaluate_predicate(fold(((a417->b > 0) && (a301->b <= (a419->b * a417->b)))))) {
                          return min((a301->b - (min(a417->a, a419->b) * a417->b)), 0);
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
      if (const Min *a309 = a300->b->as<Min>()) {
        if (const Sub *a310 = a309->b->as<Sub>()) {
          if (equal(a300->a, a310->a)) {
            return min((a300->a - a309->a), a310->b);
          }
        }
        if (const Sub *a313 = a309->a->as<Sub>()) {
          if (equal(a300->a, a313->a)) {
            return min(a313->b, (a300->a - a309->b));
          }
          if (is_const_v(a309->b)) {
            return (a300->a + min((a313->b - a313->a), fold((0 - a309->b))));
          }
        }
        if (const Min *a348 = a309->a->as<Min>()) {
          if (const Sub *a349 = a348->a->as<Sub>()) {
            if (is_const_v(a348->b)) {
              if (is_const_v(a309->b)) {
                return (a300->a + min(min((a349->b - a349->a), fold((0 - a348->b))), fold((0 - a309->b))));
              }
            }
          }
        }
      }
      if (const Mul *a355 = a300->a->as<Mul>()) {
        if (equal(a355->a, a300->b)) {
          return (a355->a * (a355->b - 1));
        }
        if (equal(a355->b, a300->b)) {
          return ((a355->a - 1) * a355->b);
        }
      }
      if (const Mul *a359 = a300->b->as<Mul>()) {
        if (equal(a300->a, a359->a)) {
          return (a300->a * (1 - a359->b));
        }
        if (equal(a300->a, a359->b)) {
          return ((1 - a359->a) * a300->a);
        }
      }
    }
  }
  if (expr->is_no_overflow_int()) {
    if (const Sub *a729 = expr->as<Sub>()) {
      if (is_const_v(a729->a)) {
        if (const Div *a730 = a729->b->as<Div>()) {
          if (const Sub *a731 = a730->a->as<Sub>()) {
            if (is_const_v(a731->a)) {
              if (is_const_v(a730->b)) {
                if (evaluate_predicate(fold((a730->b > 0)))) {
                  return ((fold(((((a729->a * a730->b) - a731->a) + a730->b) - 1)) + a731->b) / a730->b);
                }
              }
            }
          }
          if (const Add *a734 = a730->a->as<Add>()) {
            if (is_const_v(a734->b)) {
              if (is_const_v(a730->b)) {
                if (evaluate_predicate(fold((a730->b > 0)))) {
                  return ((fold(((((a729->a * a730->b) - a734->b) + a730->b) - 1)) - a734->a) / a730->b);
                }
              }
            }
          }
        }
      }
      if (const Div *a736 = a729->b->as<Div>()) {
        if (const Add *a737 = a736->a->as<Add>()) {
          if (equal(a729->a, a737->a)) {
            if (is_const_v(a736->b)) {
              if (evaluate_predicate(fold((a736->b > 0)))) {
                return ((((a729->a * fold((a736->b - 1))) - a737->b) + fold((a736->b - 1))) / a736->b);
              }
            }
          }
          if (equal(a729->a, a737->b)) {
            if (is_const_v(a736->b)) {
              if (evaluate_predicate(fold((a736->b > 0)))) {
                return ((((a729->a * fold((a736->b - 1))) - a737->a) + fold((a736->b - 1))) / a736->b);
              }
            }
          }
        }
        if (const Sub *a740 = a736->a->as<Sub>()) {
          if (equal(a729->a, a740->a)) {
            if (is_const_v(a736->b)) {
              if (evaluate_predicate(fold((a736->b > 0)))) {
                return ((((a729->a * fold((a736->b - 1))) + a740->b) + fold((a736->b - 1))) / a736->b);
              }
            }
          }
          if (equal(a729->a, a740->b)) {
            if (is_const_v(a736->b)) {
              if (evaluate_predicate(fold((a736->b > 0)))) {
                return ((((a729->a * fold((a736->b + 1))) - a740->a) + fold((a736->b - 1))) / a736->b);
              }
            }
          }
        }
      }
      if (const Div *a748 = a729->a->as<Div>()) {
        if (const Add *a749 = a748->a->as<Add>()) {
          if (is_const_v(a748->b)) {
            if (equal(a749->a, a729->b)) {
              return (((a749->a * fold((1 - a748->b))) + a749->b) / a748->b);
            }
            if (equal(a749->b, a729->b)) {
              return ((a749->a + (a749->b * fold((1 - a748->b)))) / a748->b);
            }
            if (const Div *a789 = a729->b->as<Div>()) {
              if (const Add *a790 = a789->a->as<Add>()) {
                if (equal(a749->b, a790->a)) {
                  if (equal(a749->a, a790->b)) {
                    if (equal(a748->b, a789->b)) {
                      if (evaluate_predicate(fold((a748->b != 0)))) {
                        return 0;
                      }
                    }
                  }
                }
                if (equal(a749->a, a790->a)) {
                  if (is_const_v(a790->b)) {
                    if (equal(a748->b, a789->b)) {
                      if (evaluate_predicate(fold((a748->b > 0)))) {
                        return ((((a749->a + fold((a790->b % a748->b))) % a748->b) + (a749->b - a790->b)) / a748->b);
                      }
                    }
                  }
                }
              }
              if (equal(a749->a, a789->a)) {
                if (equal(a748->b, a789->b)) {
                  if (evaluate_predicate(fold((a748->b > 0)))) {
                    return (((a749->a % a748->b) + a749->b) / a748->b);
                  }
                }
              }
            }
          }
          if (const Add *a782 = a749->a->as<Add>()) {
            if (is_const_v(a748->b)) {
              if (const Div *a783 = a729->b->as<Div>()) {
                if (const Add *a784 = a783->a->as<Add>()) {
                  if (const Add *a785 = a784->a->as<Add>()) {
                    if (equal(a782->b, a785->a)) {
                      if (equal(a782->a, a785->b)) {
                        if (equal(a748->b, a783->b)) {
                          if (evaluate_predicate(fold((a748->b > 0)))) {
                            return ((((a782->a + a782->b) + a749->b) / a748->b) - (((a782->a + a782->b) + a784->b) / a748->b));
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (is_const_v(a749->b)) {
            if (is_const_v(a748->b)) {
              if (const Div *a799 = a729->b->as<Div>()) {
                if (const Add *a800 = a799->a->as<Add>()) {
                  if (equal(a749->a, a800->a)) {
                    if (equal(a748->b, a799->b)) {
                      if (evaluate_predicate(fold((a748->b > 0)))) {
                        return (((fold(((a748->b + a749->b) - 1)) - a800->b) - ((a749->a + fold((a749->b % a748->b))) % a748->b)) / a748->b);
                      }
                    }
                  }
                }
                if (const Sub *a810 = a799->a->as<Sub>()) {
                  if (equal(a749->a, a810->a)) {
                    if (equal(a748->b, a799->b)) {
                      if (evaluate_predicate(fold((a748->b > 0)))) {
                        return (((a810->b + fold(((a748->b + a749->b) - 1))) - ((a749->a + fold((a749->b % a748->b))) % a748->b)) / a748->b);
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Min *a870 = a749->a->as<Min>()) {
            if (const Add *a871 = a870->a->as<Add>()) {
              if (const Mul *a872 = a871->a->as<Mul>()) {
                if (is_const_v(a872->b)) {
                  if (is_const_v(a748->b)) {
                    if (const Mul *a873 = a729->b->as<Mul>()) {
                      if (equal(a872->a, a873->a)) {
                        if (is_const_v(a873->b)) {
                          if (evaluate_predicate(fold((a872->b == (a748->b * a873->b))))) {
                            return ((min(a871->b, (a870->b - (a872->a * a872->b))) + a749->b) / a748->b);
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (const Add *a878 = a870->b->as<Add>()) {
              if (const Mul *a879 = a878->a->as<Mul>()) {
                if (is_const_v(a879->b)) {
                  if (is_const_v(a748->b)) {
                    if (const Mul *a880 = a729->b->as<Mul>()) {
                      if (equal(a879->a, a880->a)) {
                        if (is_const_v(a880->b)) {
                          if (evaluate_predicate(fold((a879->b == (a748->b * a880->b))))) {
                            return ((min((a870->a - (a879->a * a879->b)), a878->b) + a749->b) / a748->b);
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
        if (const Sub *a755 = a748->a->as<Sub>()) {
          if (is_const_v(a748->b)) {
            if (equal(a755->a, a729->b)) {
              return (((a755->a * fold((1 - a748->b))) - a755->b) / a748->b);
            }
            if (equal(a755->b, a729->b)) {
              return ((a755->a - (a755->b * fold((1 + a748->b)))) / a748->b);
            }
            if (const Div *a804 = a729->b->as<Div>()) {
              if (const Add *a805 = a804->a->as<Add>()) {
                if (equal(a755->a, a805->a)) {
                  if (is_const_v(a805->b)) {
                    if (equal(a748->b, a804->b)) {
                      if (evaluate_predicate(fold((a748->b > 0)))) {
                        return (((((a755->a + fold((a805->b % a748->b))) % a748->b) - a755->b) - a805->b) / a748->b);
                      }
                    }
                  }
                }
              }
              if (equal(a755->a, a804->a)) {
                if (equal(a748->b, a804->b)) {
                  if (evaluate_predicate(fold((a748->b > 0)))) {
                    return (((a755->a % a748->b) - a755->b) / a748->b);
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a748->b)) {
          if (const Div *a813 = a729->b->as<Div>()) {
            if (const Add *a814 = a813->a->as<Add>()) {
              if (equal(a748->a, a814->a)) {
                if (equal(a748->b, a813->b)) {
                  if (evaluate_predicate(fold((a748->b > 0)))) {
                    return (((fold((a748->b - 1)) - a814->b) - (a748->a % a748->b)) / a748->b);
                  }
                }
              }
            }
            if (const Sub *a822 = a813->a->as<Sub>()) {
              if (equal(a748->a, a822->a)) {
                if (equal(a748->b, a813->b)) {
                  if (evaluate_predicate(fold((a748->b > 0)))) {
                    return (((a822->b + fold((a748->b - 1))) - (a748->a % a748->b)) / a748->b);
                  }
                }
              }
            }
          }
        }
        if (const Min *a857 = a748->a->as<Min>()) {
          if (const Add *a858 = a857->a->as<Add>()) {
            if (const Mul *a859 = a858->a->as<Mul>()) {
              if (is_const_v(a859->b)) {
                if (is_const_v(a748->b)) {
                  if (const Mul *a860 = a729->b->as<Mul>()) {
                    if (equal(a859->a, a860->a)) {
                      if (is_const_v(a860->b)) {
                        if (evaluate_predicate(fold((a859->b == (a748->b * a860->b))))) {
                          return (min(a858->b, (a857->b - (a859->a * a859->b))) / a748->b);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (const Add *a864 = a857->b->as<Add>()) {
            if (const Mul *a865 = a864->a->as<Mul>()) {
              if (is_const_v(a865->b)) {
                if (is_const_v(a748->b)) {
                  if (const Mul *a866 = a729->b->as<Mul>()) {
                    if (equal(a865->a, a866->a)) {
                      if (is_const_v(a866->b)) {
                        if (evaluate_predicate(fold((a865->b == (a748->b * a866->b))))) {
                          return (min(a864->b, (a857->a - (a865->a * a865->b))) / a748->b);
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
      if (const Mul *a760 = a729->a->as<Mul>()) {
        if (const Div *a761 = a760->a->as<Div>()) {
          if (is_const_v(a761->b)) {
            if (equal(a761->b, a760->b)) {
              if (equal(a761->a, a729->b)) {
                if (evaluate_predicate(fold((a761->b > 0)))) {
                  return (0 - (a761->a % a761->b));
                }
              }
            }
          }
          if (const Add *a768 = a761->a->as<Add>()) {
            if (is_const_v(a768->b)) {
              if (is_const_v(a761->b)) {
                if (equal(a761->b, a760->b)) {
                  if (equal(a768->a, a729->b)) {
                    if (evaluate_predicate(fold(((a761->b > 0) && ((a768->b + 1) == a761->b))))) {
                      return ((0 - a768->a) % a761->b);
                    }
                  }
                }
              }
            }
          }
        }
        if (is_const_v(a760->b)) {
          if (const Mul *a775 = a729->b->as<Mul>()) {
            if (is_const_v(a775->b)) {
              if (evaluate_predicate(fold(((a760->b % a775->b) == 0)))) {
                return (((a760->a * fold((a760->b / a775->b))) - a775->a) * a775->b);
              }
              if (evaluate_predicate(fold(((a775->b % a760->b) == 0)))) {
                return ((a760->a - (a775->a * fold((a775->b / a760->b)))) * a760->b);
              }
            }
          }
        }
      }
      if (const Mul *a763 = a729->b->as<Mul>()) {
        if (const Div *a764 = a763->a->as<Div>()) {
          if (equal(a729->a, a764->a)) {
            if (is_const_v(a764->b)) {
              if (equal(a764->b, a763->b)) {
                if (evaluate_predicate(fold((a764->b > 0)))) {
                  return (a729->a % a764->b);
                }
              }
            }
          }
          if (const Add *a772 = a764->a->as<Add>()) {
            if (equal(a729->a, a772->a)) {
              if (is_const_v(a772->b)) {
                if (is_const_v(a764->b)) {
                  if (equal(a764->b, a763->b)) {
                    if (evaluate_predicate(fold(((a764->b > 0) && ((a772->b + 1) == a764->b))))) {
                      return (((a729->a + a772->b) % a764->b) + fold((0 - a772->b)));
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (const Add *a828 = a729->a->as<Add>()) {
        if (const Min *a829 = a828->a->as<Min>()) {
          if (const Add *a830 = a829->a->as<Add>()) {
            if (equal(a830->a, a729->b)) {
              return (min((a829->b - a830->a), a830->b) + a828->b);
            }
          }
        }
      }
      if (const Min *a832 = a729->a->as<Min>()) {
        if (const Add *a833 = a832->a->as<Add>()) {
          if (const Add *a834 = a833->a->as<Add>()) {
            if (equal(a834->a, a729->b)) {
              return min((a832->b - a834->a), (a834->b + a833->b));
            }
          }
          if (const Mul *a846 = a833->a->as<Mul>()) {
            if (const Add *a847 = a846->a->as<Add>()) {
              if (const Mul *a848 = a729->b->as<Mul>()) {
                if (equal(a847->a, a848->a)) {
                  if (equal(a846->b, a848->b)) {
                    return min((a832->b - (a847->a * a846->b)), ((a847->b * a846->b) + a833->b));
                  }
                }
                if (equal(a847->b, a848->a)) {
                  if (equal(a846->b, a848->b)) {
                    return min((a832->b - (a847->b * a846->b)), ((a847->a * a846->b) + a833->b));
                  }
                }
              }
            }
          }
        }
        if (const Min *a837 = a832->a->as<Min>()) {
          if (const Add *a838 = a837->a->as<Add>()) {
            if (equal(a838->a, a729->b)) {
              return min((min(a837->b, a832->b) - a838->a), a838->b);
            }
          }
          if (const Add *a842 = a837->b->as<Add>()) {
            if (equal(a842->a, a729->b)) {
              return min((min(a837->a, a832->b) - a842->a), a842->b);
            }
          }
        }
      }
    }
  }
  return expr;
}
