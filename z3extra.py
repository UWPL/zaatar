from z3 import *
from z3core import *
from z3types import *
from z3consts import *
from z3printer import *
from fractions import Fraction
import sys
import io
import math


class AstRefKey:
    """ Wrapper for allowing Z3 ASTs to be stored into Python Hashtables """

    def __init__(self, n):
        self.n = n

    def __hash__(self):
        return self.n.hash()

    def __eq__(self, other):
        return self.n.eq(other.n)

    def __repr__(self):
        return str(self.n)


def askey(n):
    assert isinstance(n, AstRef)
    return AstRefKey(n)


def get_vars_(f):
    r = set()

    def collect(f):
        if is_const(f):
            if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
                r.add(askey(f))
        else:
            for c in f.children():
                collect(c)
    collect(f)
    return r


def get_vars(f):
    return map(lambda x: x.n, get_vars_(f))


def bigAnd(l):
    if l == []:
        return True
    if len(l) == 1:
        return l[0]
    return And(*l)


def bigOr(l):
    if l == []:
        return False
    if len(l) == 1:
        return l[0]
    return Or(*l)


def z3ToFloat(r):
    assert(is_rational_value(r))
    return float(r.numerator_as_long()) / float(r.denominator_as_long())


def z3ToMath(f):
    s = str(f)
    s = s.replace("(", "[")
    s = s.replace(")", "]")
    return s


def var(name, id=None):
    if id is not None:
        return Real(name + "_" + str(id))

    return Real(name)


""" get prime implicant of list ps of predicates w.r.t to e """


def primeImplicant(ps, e):
    s = Solver()

    # we want to find a subset ps' of ps such that /\ ps => e
    s.add(Not(e))

    # holds temp bool vars for unsat core
    bs = []

    # map from temp vars to predicates
    btop = {}

    i = 0

    for p in ps:
        bp = Bool("b" + str(i))
        btop[bp] = p

        bs.append(bp)

        s.add(Implies(bp, p))

        i = i + 1

    assert(s.check(bs) == unsat)

    # only take predicates in unsat core
    res = map(lambda x:  btop[x], s.unsat_core())

    return res


""" get all atomic predicates in e """


def getPreds(e):
    s = set()

    # assumes NNF
    def getPreds_(e):
        if e in s:
            return

        if is_not(e):
            s.add(e)

        if is_and(e) or is_or(e):
            for e_ in e.children():
                getPreds_(e_)
            return

        assert(is_bool(e))

        s.add(e)

    # convert to NNF and then look for preds
    ep = Tactic('nnf')(e).as_expr()
    getPreds_(ep)

    return s

def z3max(a,b):
    return If(a > b, a, b)

def z3min(a,b):
    return If(a < b, a, b)

""" evals a set of predicates on model m """


def evalPreds(preds, m):
    res = []

    for p in preds:
        if str(m.eval(p)) == "True":
            res.append(p)

        elif str(m.eval(p)) == "False":
            res.append(Not(p))

        else:
            pass

    return res

""" returns a DNF of phi -- use at your own risk """


def toDNF(phi):
    s = Solver()
    s.add(phi)

    # get all predicates in phi
    preds = getPreds(phi)

    # disjuncts
    res = []

    while s.check() == sat:
        # get model
        m = s.model()

        # evaluate model --> get disjunct
        d = evalPreds(preds, m)
        print "size before", len(d)

        # get prime implicant of disjunct
        d = primeImplicant(d, phi)
        print "size after", len(d)

        # asser the negation of disjunct to avoid getting it again
        s.add(Not(bigAnd(d)))

        res = res + [bigAnd(d)]

    # NOTE: sanity checking code, ensures DNF is equivalent to phi

    resphi = Or(*res)

    s.reset()
    s.add(Not(phi))
    s.add(resphi)
    assert(s.check() == unsat)

    s.reset()
    s.add(phi)
    s.add(Not(resphi))
    assert(s.check() == unsat)

    # return dnf as list
    return res

""" turn to DNF and qelim each disjunct """


def qelimForallDNF(vs, e):
    # qelim of Forall X, e
    # performs qelim of Exists X, Not(e)
    # turns Not(Phi) to DNF {d1...dn}, then eliminates Exists X, di
    # as Exists distributes over disjunction

    phi = Not(e)

    res = toDNF(phi)

    dnf = []
    for r in res:
        q = Exists(vs, r)

        tl = Tactic('qe-light')
        t = Tactic('qe')

        qres_ = tl(q).as_expr()
        qres = t(qres_).as_expr()

        dnf.append(qres)

    print "# of disjuncts", len(dnf)
    return Not(bigOr(dnf))

""" one var at a time qelim """


def qelimForall(vars, phi):
    t = Tactic('qe')
    tl = Tactic('qe-light')

    # try qe-light first
    res = tl(phi).as_expr()

    print "# of vars: ", len(vars)
    i = 1
    for v in vars:
        print i, "eliminating", v

        q = ForAll([v], res)
        t = Tactic('qe')
        qres = t(q)

        assert (len(qres) == 1)

        res = qres.as_expr()
        i = i + 1

    return res
