#include "Simplify_Internal.h"
#include "Expr.h"
#include "Type.h"

Expr Simplify_And(const And *expr, Simplify *simplifier) {
  return expr->a;
  return expr->b;
  if (equal(expr->a, expr->b)) {
    return expr->a;
  }
  if (const And *a0 = expr->a.as<And>()) {
    if (equal(a0->a, expr->b)) {
      return (a0->a && a0->b);
    }
    if (equal(a0->b, expr->b)) {
      return (a0->a && a0->b);
    }
    if (const And *a5 = a0->a.as<And>()) {
      if (equal(a5->a, expr->b)) {
        return ((a5->a && a5->b) && a0->b);
      }
      if (equal(a5->b, expr->b)) {
        return ((a5->a && a5->b) && a0->b);
      }
    }
    if (const And *a9 = a0->b.as<And>()) {
      if (equal(a9->a, expr->b)) {
        return (a0->a && (a9->a && a9->b));
      }
      if (equal(a9->b, expr->b)) {
        return (a0->a && (a9->a && a9->b));
      }
    }
    if (const NE *a29 = a0->b.as<NE>()) {
      if (const EQ *a30 = expr->b.as<EQ>()) {
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
    if (const NE *a35 = a0->a.as<NE>()) {
      if (const EQ *a36 = expr->b.as<EQ>()) {
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
    if (const EQ *a41 = a0->b.as<EQ>()) {
      if (const NE *a42 = expr->b.as<NE>()) {
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
    if (const EQ *a47 = a0->a.as<EQ>()) {
      if (const NE *a48 = expr->b.as<NE>()) {
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
    if (const Or *a99 = a0->b.as<Or>()) {
      if (equal(a99->a, expr->b)) {
        return (a0->a && a99->a);
      }
      if (equal(a99->b, expr->b)) {
        return (a0->a && a99->b);
      }
    }
    if (const Or *a107 = a0->a.as<Or>()) {
      if (equal(a107->a, expr->b)) {
        return (a0->b && a107->a);
      }
      if (equal(a107->b, expr->b)) {
        return (a0->b && a107->b);
      }
    }
  }
  if (const And *a1 = expr->b.as<And>()) {
    if (equal(expr->a, a1->a)) {
      return (expr->a && a1->b);
    }
    if (equal(expr->a, a1->b)) {
      return (a1->a && expr->a);
    }
    if (const And *a7 = a1->a.as<And>()) {
      if (equal(expr->a, a7->a)) {
        return ((expr->a && a7->b) && a1->b);
      }
      if (equal(expr->a, a7->b)) {
        return ((a7->a && expr->a) && a1->b);
      }
    }
    if (const And *a11 = a1->b.as<And>()) {
      if (equal(expr->a, a11->a)) {
        return (a1->a && (expr->a && a11->b));
      }
      if (equal(expr->a, a11->b)) {
        return (a1->a && (a11->a && expr->a));
      }
    }
    if (const Or *a103 = a1->b.as<Or>()) {
      if (equal(expr->a, a103->a)) {
        return (expr->a && a1->a);
      }
      if (equal(expr->a, a103->b)) {
        return (expr->a && a1->a);
      }
    }
    if (const Or *a111 = a1->a.as<Or>()) {
      if (equal(expr->a, a111->a)) {
        return (expr->a && a1->b);
      }
      if (equal(expr->a, a111->b)) {
        return (expr->a && a1->b);
      }
    }
  }
  if (const Or *a20 = expr->a.as<Or>()) {
    if (equal(a20->a, expr->b)) {
      return a20->a;
    }
    if (equal(a20->b, expr->b)) {
      return a20->b;
    }
    if (const And *a83 = a20->b.as<And>()) {
      if (equal(a83->a, expr->b)) {
        return ((a20->a || a83->b) && a83->a);
      }
      if (equal(a83->b, expr->b)) {
        return ((a20->a || a83->a) && a83->b);
      }
    }
    if (const And *a91 = a20->a.as<And>()) {
      if (equal(a91->a, expr->b)) {
        return ((a91->b || a20->b) && a91->a);
      }
      if (equal(a91->b, expr->b)) {
        return ((a91->a || a20->b) && a91->b);
      }
    }
    if (const Or *a115 = expr->b.as<Or>()) {
      if (equal(a20->a, a115->a)) {
        return (a20->a || (a20->b && a115->b));
      }
      if (equal(a20->a, a115->b)) {
        return (a20->a || (a20->b && a115->a));
      }
      if (equal(a20->b, a115->a)) {
        return (a20->b || (a20->a && a115->b));
      }
      if (equal(a20->b, a115->b)) {
        return (a20->b || (a20->a && a115->a));
      }
    }
  }
  if (const Or *a21 = expr->b.as<Or>()) {
    if (equal(expr->a, a21->a)) {
      return expr->a;
    }
    if (equal(expr->a, a21->b)) {
      return expr->a;
    }
    if (const And *a87 = a21->b.as<And>()) {
      if (equal(expr->a, a87->a)) {
        return (expr->a && (a21->a || a87->b));
      }
      if (equal(expr->a, a87->b)) {
        return (expr->a && (a21->a || a87->a));
      }
    }
    if (const And *a95 = a21->a.as<And>()) {
      if (equal(expr->a, a95->a)) {
        return (expr->a && (a95->b || a21->b));
      }
      if (equal(expr->a, a95->b)) {
        return (expr->a && (a95->a || a21->b));
      }
    }
  }
  if (const NE *a24 = expr->a.as<NE>()) {
    if (const EQ *a25 = expr->b.as<EQ>()) {
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
      if (const EQ *a57 = expr->b.as<EQ>()) {
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
  if (const Not *a52 = expr->b.as<Not>()) {
    if (equal(expr->a, a52->a)) {
      return false;
    }
  }
  if (const Not *a53 = expr->a.as<Not>()) {
    if (equal(a53->a, expr->b)) {
      return false;
    }
  }
  if (const LE *a54 = expr->a.as<LE>()) {
    if (const LT *a55 = expr->b.as<LT>()) {
      if (equal(a54->b, a55->a)) {
        if (equal(a54->a, a55->b)) {
          return false;
        }
      }
    }
    if (is_const_v(a54->b)) {
      if (const LT *a65 = expr->b.as<LT>()) {
        if (is_const_v(a65->a)) {
          if (equal(a54->a, a65->b)) {
            if (evaluate_predicate(fold((a54->b <= a65->a)))) {
              return false;
            }
          }
        }
      }
      if (const LE *a71 = expr->b.as<LE>()) {
        if (is_const_v(a71->a)) {
          if (equal(a54->a, a71->b)) {
            if (evaluate_predicate(fold((a54->b < a71->a)))) {
              return false;
            }
          }
        }
        if (equal(a54->a, a71->a)) {
          if (is_const_v(a71->b)) {
            return (a54->a <= fold(min(a54->b, a71->b)));
          }
        }
      }
    }
    if (is_const_v(a54->a)) {
      if (const LT *a67 = expr->b.as<LT>()) {
        if (equal(a54->b, a67->a)) {
          if (is_const_v(a67->b)) {
            if (evaluate_predicate(fold((a67->b <= a54->a)))) {
              return false;
            }
          }
        }
      }
      if (const LE *a69 = expr->b.as<LE>()) {
        if (equal(a54->b, a69->a)) {
          if (is_const_v(a69->b)) {
            if (evaluate_predicate(fold((a69->b < a54->a)))) {
              return false;
            }
          }
        }
        if (is_const_v(a69->a)) {
          if (equal(a54->b, a69->b)) {
            return (fold(min(a54->a, a69->a)) <= a54->b);
          }
        }
      }
    }
    if (const LE *a127 = expr->b.as<LE>()) {
      if (equal(a54->a, a127->a)) {
        return (a54->a <= min(a54->b, a127->b));
      }
      if (equal(a54->b, a127->b)) {
        return (min(a54->a, a127->a) <= a54->b);
      }
    }
  }
  if (const EQ *a58 = expr->a.as<EQ>()) {
    if (is_const_v(a58->b)) {
      if (const EQ *a59 = expr->b.as<EQ>()) {
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
  if (const LT *a60 = expr->a.as<LT>()) {
    if (is_const_v(a60->a)) {
      if (const LT *a61 = expr->b.as<LT>()) {
        if (equal(a60->b, a61->a)) {
          if (is_const_v(a61->b)) {
            if (evaluate_predicate(fold((!(is_float(a60->b)) && (a61->b <= (a60->a + 1)))))) {
              return false;
            }
          }
        }
        if (is_const_v(a61->a)) {
          if (equal(a60->b, a61->b)) {
            return (fold(min(a60->a, a61->a)) < a60->b);
          }
        }
      }
    }
    if (is_const_v(a60->b)) {
      if (const LT *a63 = expr->b.as<LT>()) {
        if (is_const_v(a63->a)) {
          if (equal(a60->a, a63->b)) {
            if (evaluate_predicate(fold((!(is_float(a60->a)) && (a60->b <= (a63->a + 1)))))) {
              return false;
            }
          }
        }
        if (equal(a60->a, a63->a)) {
          if (is_const_v(a63->b)) {
            return (a60->a < fold(min(a60->b, a63->b)));
          }
        }
      }
    }
    if (const LT *a123 = expr->b.as<LT>()) {
      if (equal(a60->a, a123->a)) {
        return (a60->a < min(a60->b, a123->b));
      }
      if (equal(a60->b, a123->b)) {
        return (min(a60->a, a123->a) < a60->b);
      }
    }
  }
  if (const Broadcast *a80 = expr->a.as<Broadcast>()) {
    if (is_const_v(a80->lanes)) {
      if (const Broadcast *a81 = expr->b.as<Broadcast>()) {
        if (equal(a80->lanes, a81->lanes)) {
          return broadcast((a80->value && a81->value), a80->lanes);
        }
      }
    }
  }
  return expr;
}
