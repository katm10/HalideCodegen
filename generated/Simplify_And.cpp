ExprPtr Simplify_And(const And *expr, Simplify *simplifier) {
  return expr->a;
  return expr->b;
  if (equal(expr->a, expr->b)) {
    return expr->a;
  }
  if (const And *a0 = expr->a->as<And>()) {
    if (equal(a0->a, expr->b)) {
      return (a0->a && a0->b);
    }
    if (equal(a0->b, expr->b)) {
      return (a0->a && a0->b);
    }
    if (const And *a5 = a0->a->as<And>()) {
      if (equal(a5->a, expr->b)) {
        return ((a5->a && a5->b) && a0->b);
      }
      if (equal(a5->b, expr->b)) {
        return ((a5->a && a5->b) && a0->b);
      }
    }
    if (const And *a9 = a0->b->as<And>()) {
      if (equal(a9->a, expr->b)) {
        return (a0->a && (a9->a && a9->b));
      }
      if (equal(a9->b, expr->b)) {
        return (a0->a && (a9->a && a9->b));
      }
    }
    if (const NE *a29 = a0->b->as<NE>()) {
      if (const EQ *a30 = expr->b->as<EQ>()) {
        if (equal(a29->a, a30->a)) {
          if (equal(a29->b, a30->b)) {
            return false;
          }
        }
        if (equal(a29->b, a30->a)) {
          if (equal(a29->a, a30->b)) {
            return false;
          }
        }
      }
    }
    if (const NE *a35 = a0->a->as<NE>()) {
      if (const EQ *a36 = expr->b->as<EQ>()) {
        if (equal(a35->a, a36->a)) {
          if (equal(a35->b, a36->b)) {
            return false;
          }
        }
        if (equal(a35->b, a36->a)) {
          if (equal(a35->a, a36->b)) {
            return false;
          }
        }
      }
    }
    if (const EQ *a41 = a0->b->as<EQ>()) {
      if (const NE *a42 = expr->b->as<NE>()) {
        if (equal(a41->a, a42->a)) {
          if (equal(a41->b, a42->b)) {
            return false;
          }
        }
        if (equal(a41->b, a42->a)) {
          if (equal(a41->a, a42->b)) {
            return false;
          }
        }
      }
    }
    if (const EQ *a47 = a0->a->as<EQ>()) {
      if (const NE *a48 = expr->b->as<NE>()) {
        if (equal(a47->a, a48->a)) {
          if (equal(a47->b, a48->b)) {
            return false;
          }
        }
        if (equal(a47->b, a48->a)) {
          if (equal(a47->a, a48->b)) {
            return false;
          }
        }
      }
    }
    if (const Or *a95 = a0->b->as<Or>()) {
      if (equal(a95->a, expr->b)) {
        return (a0->a && a95->a);
      }
      if (equal(a95->b, expr->b)) {
        return (a0->a && a95->b);
      }
    }
    if (const Or *a103 = a0->a->as<Or>()) {
      if (equal(a103->a, expr->b)) {
        return (a0->b && a103->a);
      }
      if (equal(a103->b, expr->b)) {
        return (a0->b && a103->b);
      }
    }
  }
  if (const And *a1 = expr->b->as<And>()) {
    if (equal(expr->a, a1->a)) {
      return (expr->a && a1->b);
    }
    if (equal(expr->a, a1->b)) {
      return (a1->a && expr->a);
    }
    if (const And *a7 = a1->a->as<And>()) {
      if (equal(expr->a, a7->a)) {
        return ((expr->a && a7->b) && a1->b);
      }
      if (equal(expr->a, a7->b)) {
        return ((a7->a && expr->a) && a1->b);
      }
    }
    if (const And *a11 = a1->b->as<And>()) {
      if (equal(expr->a, a11->a)) {
        return (a1->a && (expr->a && a11->b));
      }
      if (equal(expr->a, a11->b)) {
        return (a1->a && (a11->a && expr->a));
      }
    }
    if (const Or *a99 = a1->b->as<Or>()) {
      if (equal(expr->a, a99->a)) {
        return (expr->a && a1->a);
      }
      if (equal(expr->a, a99->b)) {
        return (expr->a && a1->a);
      }
    }
    if (const Or *a107 = a1->a->as<Or>()) {
      if (equal(expr->a, a107->a)) {
        return (expr->a && a1->b);
      }
      if (equal(expr->a, a107->b)) {
        return (expr->a && a1->b);
      }
    }
  }
  if (const Or *a20 = expr->a->as<Or>()) {
    if (equal(a20->a, expr->b)) {
      return a20->a;
    }
    if (equal(a20->b, expr->b)) {
      return a20->b;
    }
    if (const And *a79 = a20->b->as<And>()) {
      if (equal(a79->a, expr->b)) {
        return ((a20->a || a79->b) && a79->a);
      }
      if (equal(a79->b, expr->b)) {
        return ((a20->a || a79->a) && a79->b);
      }
    }
    if (const And *a87 = a20->a->as<And>()) {
      if (equal(a87->a, expr->b)) {
        return ((a87->b || a20->b) && a87->a);
      }
      if (equal(a87->b, expr->b)) {
        return ((a87->a || a20->b) && a87->b);
      }
    }
    if (const Or *a111 = expr->b->as<Or>()) {
      if (equal(a20->a, a111->a)) {
        return (a20->a || (a20->b && a111->b));
      }
      if (equal(a20->a, a111->b)) {
        return (a20->a || (a20->b && a111->a));
      }
      if (equal(a20->b, a111->a)) {
        return (a20->b || (a20->a && a111->b));
      }
      if (equal(a20->b, a111->b)) {
        return (a20->b || (a20->a && a111->a));
      }
    }
  }
  if (const Or *a21 = expr->b->as<Or>()) {
    if (equal(expr->a, a21->a)) {
      return expr->a;
    }
    if (equal(expr->a, a21->b)) {
      return expr->a;
    }
    if (const And *a83 = a21->b->as<And>()) {
      if (equal(expr->a, a83->a)) {
        return (expr->a && (a21->a || a83->b));
      }
      if (equal(expr->a, a83->b)) {
        return (expr->a && (a21->a || a83->a));
      }
    }
    if (const And *a91 = a21->a->as<And>()) {
      if (equal(expr->a, a91->a)) {
        return (expr->a && (a91->b || a21->b));
      }
      if (equal(expr->a, a91->b)) {
        return (expr->a && (a91->a || a21->b));
      }
    }
  }
  if (const NE *a24 = expr->a->as<NE>()) {
    if (const EQ *a25 = expr->b->as<EQ>()) {
      if (equal(a24->a, a25->a)) {
        if (equal(a24->b, a25->b)) {
          return false;
        }
      }
      if (equal(a24->b, a25->a)) {
        if (equal(a24->a, a25->b)) {
          return false;
        }
      }
    }
    if (is_const_v(a24->b)) {
      if (const EQ *a57 = expr->b->as<EQ>()) {
        if (equal(a24->a, a57->a)) {
          if (is_const_v(a57->b)) {
            if (evaluate_predicate(fold((a24->b != a57->b)))) {
              return b;
            }
          }
        }
      }
    }
  }
  if (const Not *a52 = expr->b->as<Not>()) {
    if (equal(expr->a, a52->a)) {
      return false;
    }
  }
  if (const Not *a53 = expr->a->as<Not>()) {
    if (equal(a53->a, expr->b)) {
      return false;
    }
  }
  if (const LE *a54 = expr->a->as<LE>()) {
    if (const LT *a55 = expr->b->as<LT>()) {
      if (equal(a54->b, a55->a)) {
        if (equal(a54->a, a55->b)) {
          return false;
        }
      }
    }
    if (is_const_v(a54->b)) {
      if (const LT *a61 = expr->b->as<LT>()) {
        if (is_const_v(a61->a)) {
          if (equal(a54->a, a61->b)) {
            if (evaluate_predicate(fold((a54->b <= a61->a)))) {
              return false;
            }
          }
        }
      }
      if (const LE *a67 = expr->b->as<LE>()) {
        if (is_const_v(a67->a)) {
          if (equal(a54->a, a67->b)) {
            if (evaluate_predicate(fold((a54->b < a67->a)))) {
              return false;
            }
          }
        }
        if (equal(a54->a, a67->a)) {
          if (is_const_v(a67->b)) {
            return (a54->a <= fold(min(a54->b, a67->b)));
          }
        }
      }
    }
    if (is_const_v(a54->a)) {
      if (const LT *a63 = expr->b->as<LT>()) {
        if (equal(a54->b, a63->a)) {
          if (is_const_v(a63->b)) {
            if (evaluate_predicate(fold((a63->b <= a54->a)))) {
              return false;
            }
          }
        }
      }
      if (const LE *a65 = expr->b->as<LE>()) {
        if (equal(a54->b, a65->a)) {
          if (is_const_v(a65->b)) {
            if (evaluate_predicate(fold((a65->b < a54->a)))) {
              return false;
            }
          }
        }
        if (is_const_v(a65->a)) {
          if (equal(a54->b, a65->b)) {
            return (fold(min(a54->a, a65->a)) <= a54->b);
          }
        }
      }
    }
    if (const LE *a123 = expr->b->as<LE>()) {
      if (equal(a54->a, a123->a)) {
        return (a54->a <= min(a54->b, a123->b));
      }
      if (equal(a54->b, a123->b)) {
        return (min(a54->a, a123->a) <= a54->b);
      }
    }
  }
  if (const EQ *a58 = expr->a->as<EQ>()) {
    if (is_const_v(a58->b)) {
      if (const EQ *a59 = expr->b->as<EQ>()) {
        if (equal(a58->a, a59->a)) {
          if (is_const_v(a59->b)) {
            if (evaluate_predicate(fold((a58->b != a59->b)))) {
              return false;
            }
          }
        }
      }
    }
  }
  if (const LT *a68 = expr->a->as<LT>()) {
    if (is_const_v(a68->a)) {
      if (const LT *a69 = expr->b->as<LT>()) {
        if (is_const_v(a69->a)) {
          if (equal(a68->b, a69->b)) {
            return (fold(min(a68->a, a69->a)) < a68->b);
          }
        }
      }
    }
    if (is_const_v(a68->b)) {
      if (const LT *a73 = expr->b->as<LT>()) {
        if (equal(a68->a, a73->a)) {
          if (is_const_v(a73->b)) {
            return (a68->a < fold(min(a68->b, a73->b)));
          }
        }
      }
    }
    if (const LT *a119 = expr->b->as<LT>()) {
      if (equal(a68->a, a119->a)) {
        return (a68->a < min(a68->b, a119->b));
      }
      if (equal(a68->b, a119->b)) {
        return (min(a68->a, a119->a) < a68->b);
      }
    }
  }
  if (const Broadcast *a76 = expr->a->as<Broadcast>()) {
    if (is_const_v(a76->lanes)) {
      if (const Broadcast *a77 = expr->b->as<Broadcast>()) {
        if (equal(a76->lanes, a77->lanes)) {
          return broadcast((a76->value && a77->value), a76->lanes);
        }
      }
    }
  }
  return expr;
}
