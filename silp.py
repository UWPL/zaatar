from z3 import *
from itertools import *
from timeit import default_timer as timer


class Relation:
    """ Relations """

    def __init__(self, name, arity):
        self.name = name
        self.arity = arity

    def __eq__(self, other):
        return self.name == other.name

    def __repr__(self):
        return self.name + "__" + str(self.arity)

    def __hash__(self):
        return hash(self.name)

    def l(self, *args):
        return Literal(self, *args)

    def f(self, *args):
        return Fact(self, *args)


class Literal:
    """ Literal appearing in a Horn clause: application of rel to args """

    def __init__(self, rel, *args):
        self.rel = rel
        self.args = args

    def __eq__(self,other):
        if self.rel != other.rel: return False
        if self.args != other.args: return False
        return True

    def __hash__(self):
        return hash(self.rel)

    def __repr__(self):
        if len(self.args) == 1:
            args = str(self.args[0])
        else:
            args = reduce(lambda a, b: a + ", " + b, self.args)
        return self.rel.name + "(" + args + ")"


class Fact:
    """ Fact: tuple ftuple of relation rel """

    def __init__(self, rel, *t):
        self.rel = rel
        self.ftuple = t
        assert(self.rel.arity == len(self.ftuple))

    def __eq__(self, other):
        c1 = self.rel == other.rel
        c2 = self.ftuple == other.ftuple
        return c1 and c2

    def __repr__(self):
        return self.rel.name + str(self.ftuple)


class EDB:
    """ Extensional database: stores facts in "input" relations; consists of:
        irels: relations comprising edb
        facts: tuples of relations in irels
    """

    def __init__(self, irels, facts):
        self.irels = irels
        self.facts = facts

        # check all facts belong to declared relations
        for f in facts:
            assert(len(filter(lambda r: r == f.rel, irels)) == 1)

        # check no repeated decl of same relation
        # TODO: fix when relations are hashable
        #assert(len(set(irels)) == len(irels))
        #assert(len(set(orels)) == len(orels))

    def __repr__(self):
        return "irels " + str(self.irels) + "\nfacts " + str(self.facts)


class Clause:
    """ Clause: Horn clause with head (predicate) and tail (list of predicates) """

    def __init__(self, head, tail):
        self.head = head
        self.tail = tail

    def __repr__(self):
        if len(set(self.tail)) == 1:
            tailStr = str(self.tail[0])
        elif len(set(self.tail)) == 0:
            tailStr = "true"
        else:
            tailStr = reduce(lambda a, b: str(a) + ", " + str(b), set(self.tail))
        return str(self.head) + " :- " + tailStr


class STask:
    """ Synthesis task; consists of
        edb: extensional database
        orels: output relations
        pf: positive facts
        nf: negative facts
        domain: maximum integer that can appear
            (models finite domain)
    """

    def __init__(self, edb, orels, pf, nf, domain, base=1, chain=False, soft=True):
        self.edb = edb
        self.orels = orels
        self.pfacts = pf
        self.nfacts = nf
        self.domain = domain
        self.time = 0
        self.chain = chain
        self.base = base
        self.soft = soft

        # check all facts belong to declared relations
        for f in (nf + pf):
            assert(len(filter(lambda r: r == f.rel, self.orels)) == 1)

    def verify(self, clauses):
        s = Fixedpoint()
        d = FiniteDomainSort('D', self.domain)
        consts = {}

        args = {}
        rels = {}

        def argsToZ3(l):
            r = []
            for a in l:
                if a in args:
                    r = r + [args[a]]
                else:
                    args[a] = Var(int(a.replace('X', '')), d)
                    r = r + [args[a]]
            return r

        def litToZ3(l):
            lrel = l.rel
            lz3 = rels[lrel](*argsToZ3(l.args))
            return lz3

        def factToZ3(l):
            r = rels[l.rel]
            args = map(lambda v: consts[v], l.ftuple)
            return r(*args)

        # create array of constant values for the given domain:
        for i in range(1, self.domain):
            consts[i] = FiniteDomainVal(i, d)

        # register relations in Z3
        for r in self.edb.irels + self.orels:
            print r
            dom = [d for i in range(0, r.arity)] + [BoolSort()]
            rz3 = Function(r.name, *dom)
            rels[r] = rz3
            print "registering ", r, " - > ", rz3
            s.register_relation(rz3)

        # create argument variables for clauses
        for c in clauses:
            head = litToZ3(c.head)
            body = map(litToZ3, c.tail)
            s.rule(head, body)

        # add all facts in EDB
        for f in self.edb.facts:
            s.fact(factToZ3(f))

        print "Created Z3 Fixedpoint"
        print s
        print "Now checking queries"

        # check pos examples
        for p in self.pfacts:
            print "Checking pos", p, "-->", factToZ3(p)

            if s.query(factToZ3(p)) == unsat:
                return False

        # check neg examples
        for n in self.nfacts:
            print "Checking neg", n, "-->", Not(factToZ3(n))

            if s.query(Not(factToZ3(n))) == unsat:
                return False

        return True

    def getMaxArity(self):
        na = 0
        for r in (self.orels + self.edb.irels):
            if (r.arity > na):
                na = r.arity


        return na

    def idToRel(self, relId):
        i = 1
        for r in self.edb.irels + self.orels:
            #print r
            if relId == i:
                return r

            i = i + 1

    def idsToLit(self, relId, hargsId):
        r = self.idToRel(relId)
        return r.l(*(hargsId[0:r.arity]))

    def modelToClause(self, m, pos):
        # first get the head of the clause
        h = self.heads[pos]
        headId = m[h].as_long()
        hargsId = map(lambda v: "X" + str(m[v]), self.argvars[h])
        headLiteral = self.idsToLit(headId, hargsId)
        # print headLiteral

        bLiterals = []
        for b in self.bodies[pos]:
            bId = m[b].as_long()
            bargsId = map(lambda v: "X" + str(m[v]), self.argvars[b])
            bLit = self.idsToLit(bId, bargsId)
            bLiterals.append(bLit)
            # print bLit

        clause = Clause(headLiteral, bLiterals)
        print clause
        return clause


    def solveConst(self, phi, pos, softC):
        s = Optimize()

        s.add(phi)
        s.add(And(*pos))

        for c in softC:
            s.add_soft(c)

        start = timer()
        res = s.check()
        end = timer()
        self.time = self.time + (end - start)

        print res

        if res == unsat:
            print "No solution found -- unsat"
            return (None, None)
        else:
            m = s.model()
            print "MODEL:", m
            cs = []
            print self.nc
            for i in range(1, self.nc + 1):
                cs.append(self.modelToClause(m, i))

        return (cs, m)

    def getZ3Sort(self, r):
        s = Datatype(r.name + '_t')
        dec = []
        for i in range(1, r.arity + 1):
            dec.append(('i' + str(i), IntSort()))

        s.declare('tuple', *dec)

        return s.create()

    def getSymmetry(self):
        const = []

        for i in range(1, self.nc + 1):
            bs = self.bodies[i]
            for j in range(0, len(bs) - 1):
                const.append(bs[j] <= bs[j + 1])

        return And(*const)

    """ asserts that clause l is a base case, i.e., no IDBs in body """

    def getBase(self, l):
        const = []

        bs = self.bodies[l]
        head = self.heads[l]

        bargs = []
        for b in bs:
            const.append(b >= 1)
            const.append(b <= len(self.edb.irels))
            bargs = bargs + self.argvars[b]

        for harg in self.argvars[head]:
            d = map(lambda x : x == harg , bargs)
            const.append(Or(*d))

        print const

        return And(*const)

    """ Get constraint specifying that all locations should be connected """

    def getEquality(self, l):
        const = []

        args = []
        bargs = []

        bs = self.bodies[l]
        head = self.heads[l]

        def inHead(a,a2):
            l = self.argvars[head]
            l1 = filter (lambda x: x is a, l)
            l2 = filter (lambda x: x is a2, l)

            return l1 != [] and l2 != []

        for r in bs:
            args = args + self.argvars[r][0:2]

        args = args + self.argvars[head]


        for r in bs:
            bargs = bargs + self.argvars[r]

        for a in args:
            disj = []
            for a2 in args:
                if a is a2: continue
                if inHead(a,a2):
                    continue
                disj = disj + [a == a2]
            const = const + [Or(*disj)]


        # HACK: if ternary relations
        if self.na == 3 and l == 1:
            for i,a in enumerate(bargs[:-1]):
                if (i+1) % 3 == 0:
                    const.append(a == bargs[i-1])

        print const
        #exit(1)
        return And(*const)

    """ ensure one relation is IDB in clause l """

    def getNonBase(self, l):
        # idb relations start at indices > n
        n = len(self.edb.irels)
        m = n + len(self.orels)


        # at least one relation is IDB
        dis = []

        for b in self.bodies[l]:
            dis.append(And(b >= n + 1, b <= m))

        return Or(*dis)


    """ chain constraints for clause l for chain of length "length" """

    def getChain(self, l, length):
        const = []

        bs = self.bodies[l]
        head = self.heads[l]

        ds = []
        chain = []

        # first and last arguments of chain
        first = self.argvars[bs[0]][0]
        last = self.argvars[bs[length - 1]][1]

        # HACK:
        # CURRENTLY ASSUMES ALL RELATIONS ARE BINARY
        for i, b in enumerate(bs[0:length]):

            args = self.argvars[b]

            if i == 0:
                ds.append(args[0])
            if i == length - 1:
                ds.append(args[1])
                continue

            argsNext = self.argvars[bs[i + 1]]
            const.append(args[1] == argsNext[0])

        # head arguments are beginning and end of chain
        headc = Or(And(self.argvars[head][0] == first,
                    self.argvars[head][1] == last),
                    And(self.argvars[head][1] == first,
                    self.argvars[head][0] == last))

        print headc
        print const
        print ds


        # idb relations start at indices > n
        n = len(self.edb.irels)
        m = n + len(self.orels)


        # at least one relation is IDB
        dis = []
        for b in bs[0:length]:
            dis.append(And(b >= n + 1, b <= m))


        return And(And(*const), Distinct(ds), headc)#, Or(*dis))

    """ set of soft constraints asserting that all """

    def getSoft(self):

        consts = []

        for i in range(1, self.nc+1):
            bs = self.bodies[i]

            seen = []
            for b in bs:
                for b2 in bs:
                    if b is b2: continue
                    if (b2,b) in seen: continue
                    #consts.append(b == b2)
                    ba = self.argvars[b]
                    b2a = self.argvars[b2]
                    #consts =  consts + map(lambda (a,b): a == b,zip(ba,b2a))
                    l = map(lambda (a,b): a == b,zip(ba,b2a))
                    consts  = consts + [And(b==b2,And(*l))]
                    seen = seen + [(b,b2)]

        return consts

    """ simulation all enclosed here """

    def simulation(self):

        # takes a fact and turns it into a Z3 tuple
        def factToZ3Tuple(f):
            t = tup[f.rel]
            res = t.tuple(*f.ftuple)
            return res

        # create idbArrays
        def createIdbArrays():
            for r in self.orels:
                for i in range(1, self.bound + 1):
                    domain = self.getZ3Sort(r)
                    tup[r] = domain

                    arr = Array(r.name + str(i), domain, BoolSort())
                    idbArr[r].append(arr)

        def createInitConsts():
            # create initial arrays for EDB relations
            for r in self.edb.irels:
                domain = self.getZ3Sort(r)
                tup[r] = domain

                print r.name
                arr = Array(r.name, domain, BoolSort())
                edbArr[r] = arr

                edbFacts[r] = []

            # create initial arrays for IDB relations
            for r in self.orels:
                domain = self.getZ3Sort(r)
                tup[r] = domain

                arr = Array(r.name + "0", domain, BoolSort())
                idbArr[r] = [arr]

            # go thru facts and encode them as array constraints
            initConsts = []
            for f in self.edb.facts:
                t = factToZ3Tuple(f)
                arr = edbArr[f.rel]
                initConsts.append(Select(arr, t))
                edbFacts[f.rel].append(f.ftuple)

            # go thru frame (all not facts) and negate them
            for r in self.edb.irels:

                # go thru all possible combinations
                for t in product(range(1, self.domain), repeat=r.arity):

                    # if r(t) is a fact, skip it
                    if t in edbFacts[r]:
                        continue

                    f = Fact(r, *t)
                    tp = factToZ3Tuple(f)
                    arr = edbArr[r]
                    initConsts.append(Not(Select(arr, tp)))

            # just as above, but initializing IDB -- where all facts are
            # negative
            for r in self.orels:
                # go thru all possible combinations
                for t in product(range(1, self.domain), repeat=r.arity):
                    f = Fact(r, *t)
                    tp = factToZ3Tuple(f)
                    arr = idbArr[r][0]
                    initConsts.append(Not(Select(arr, tp)))

            return initConsts

        # constrain head i assuming its set to IDB k
        # at frame l
        def constrainHead(i, k, l):
            # get idb k
            idb = self.idToRel(k)
            arrPrev = idbArr[idb][l - 1]
            arrNext = idbArr[idb][l]

            print "idb", idb
            print "arrPrev", arrPrev
            print "arrNext", arrNext

            consts = []
            tupleType = tup[idb]

            headTuple = frameArgs[l][0:idb.arity]
            headTuple = tupleType.tuple(*headTuple)

            # assert that fact not true at l-1
            consts.append(Not(Select(arrPrev, headTuple)))

            # assert that at frame l, everything is same as l-1 except headTuple,
            # it is now True.
            consts.append(arrNext == Update(arrPrev, headTuple, True))

            # constrains all relations that did not change
            # in rule application
            for i in idbArr:
                if i is not idb:
                    frame = idbArr[i][l - 1] == idbArr[i][l]
                    consts.append(frame)

            print "head consts", consts
            return And(*consts)

        # constrain body pos in clause i assuming its set to IDB/EDB k
        # at frame l
        def constrainBody(i, pos, k, l):
            # get rel k
            rel = self.idToRel(k)

            if rel in idbArr:
                arrPrev = idbArr[rel][l - 1]
            else:
                assert(rel in edbArr)
                arrPrev = edbArr[rel]

            # where the body rel args begin and end
            begin = self.na + pos * self.na
            end = begin + rel.arity

            print "b", begin
            print "e", end

            tupleType = tup[rel]
            headTuple = frameArgs[l][begin:end]
            print frameArgs[l]
            print headTuple
            print rel
            print tupleType
            headTuple = tupleType.tuple(*headTuple)
            print headTuple

            res = Select(arrPrev, headTuple)

            return res

        def getClauseArgs(i):
            h = self.heads[i]
            args = self.argvars[h]

            for b in self.bodies[i]:
                args = args + self.argvars[b]

            return args

        def matchLatches(i, l):
            args = frameArgs[l]
            cargs = getClauseArgs(i)

            const = []
            assert (len(args) == len(cargs))

            for i1, c1 in enumerate(cargs):
                for i2, c2 in enumerate(cargs):
                    if i1 == i2:
                        continue

                    phi = Implies(c1 == c2, args[i1] == args[i2])
                    const.append(phi)

            return And(*const)

        # apply clause i at level l
        def applyClause(i, l):
            n = len(self.edb.irels)
            m = n + len(self.orels)

            headConsts = []
            bodyConsts = []
            h = self.heads[i]
            bs = self.bodies[i]

            for k in range(n + 1, m + 1):
                lhs = h == k
                rhs = constrainHead(i, k, l)
                print "constrainHead", rhs
                headConsts.append(Implies(lhs, rhs))

            for pos, b in enumerate(bs):
                for k in range(1, m + 1):
                    lhs = b == k
                    rhs = constrainBody(i, pos, k, l)
                    bodyConsts.append(Implies(lhs, rhs))

            print "bodyConsts", bodyConsts

            # this connects args "af*-*" with
            # the chosen clause arguments
            latches = matchLatches(i, l)

            return And(And(*headConsts), And(*bodyConsts), latches)

        # get constrains for rule app at level l
        def getFrame(l):
            consts = []

            # integer indicating clause to apply
            S = Int('S' + str(l))

            ruleArgs.append(S)

            consts.append(S >= 1)
            consts.append(S <= self.nc)

            for i in range(1, self.nc + 1):
                consts.append(Implies(S == i, applyClause(i, l)))

            print "Constraint at frame", l, consts

            return And(*consts)

        def getCorrectness():
            pos = []
            neg = []
            for p in self.pfacts:
                t = factToZ3Tuple(p)
                arr = idbArr[p.rel][self.bound]
                pos.append(Select(arr, t))

            for p in self.nfacts:
                t = factToZ3Tuple(p)
                arr = idbArr[p.rel][self.bound]
                neg.append(Not(Select(arr, t)))

            return (pos,neg)

        def getApplyAll():
            conj = []

            for i in range(1, self.nc+1):
                disj = []

                for s in ruleArgs:
                    disj.append (s == i)

                conj.append(Or(*disj))

            return And(*conj)

        def getDerivSymmetry():
            res = []
            for i,s in enumerate(ruleArgs[:-1]):
                imp = Implies(s > self.base, ruleArgs[i+1] > self.base)
                res.append(imp)

            return And(*res)

        edbArr = {}
        edbFacts = {}

        tup = {}

        idbArr = {}

        initConsts = createInitConsts()
        createIdbArrays()

        print "idbArr", idbArr
        print "tup", tup

        frames = []
        frameArgs = {}

        ruleArgs = []

        # generate variables for all arities
        argWidth = self.na * (self.nl + 1)
        print "wdit" , argWidth
        print self.na
        for i in range(1, self.bound + 1):
            print "DOING FRAME", i
            # create frame variables denoting latches
            args = []
            argsConst = []
            for j in range(1, argWidth + 1):
                arg = Int("af" + str(i) + "-" + str(j))
                args.append(arg)
                argsConst.append(And(arg >= 1, arg <= self.domain - 1))

            # latches for frame i
            frameArgs[i] = args

            # get frame constraint
            frames.append(And(getFrame(i), And(*argsConst)))

        symmetry = getDerivSymmetry()
        frames = And(*frames)
        initConsts = And(*initConsts)
        (pos,neg) = getCorrectness()


        applyAll = getApplyAll()
        print "applyAll", applyAll

        #print "Correctness", correctness
        # exit(1)
        return (And(initConsts, frames, And(*neg), applyAll, symmetry), pos)

    # encodes variables in vs as their equivalence classes per model
    def getEquivClasses(self, model, vs):
        eq = {}
        consts = []

        print "EQ vs", vs
        for v in vs:
            if model[v].as_long() not in eq:
                eq[model[v].as_long()] = [v]
                continue

            eq[model[v].as_long()].append(v)

        print eq
        for k in eq:
            for i in range(0, len(eq[k]) - 1):
                consts.append(eq[k][i] == eq[k][i + 1])

        for k1 in eq:
            for k2 in eq:
                print k1, k2
                if k1 == k2:
                    continue
                print "here"
                consts.append(eq[k1][0] != eq[k2][0])

        print "Equiv repr, ", consts
        # exit(1)
        return And(*consts)

    def negateModel(self, model):
        const = []
        for i in range(1, self.nc + 1):
            equiv = []
            rels = []
            h = self.heads[i]
            vs = []

            # append head const
            rels.append(h == model[h])

            vs = vs + self.argvars[h]

            # append body consts
            for b in self.bodies[i]:
                rels.append(b == model[b])
                vs = vs + self.argvars[b]

            # get equivalence class
            equiv = self.getEquivClasses(model, vs)

            # exit(1)
            const = const + rels + [equiv]
        print "model repr, ", const
        # exit(1)
        return And(*const)

    def getArgEqModel(self, model):
        modelF = []

        # collect all arg variables
        for i in range(1, self.nc + 1):
            vs = []
            modelFi = []
            vs = vs + self.argvars[self.heads[i]]
            for j in range(1, self.nl + 1):
                vs = vs + self.argvars[self.bodies[i][j - 1]]

            for v1 in vs:
                for v2 in vs:
                    if v1 is v2:
                        continue
                    if is_true(model.eval(v1 == v2)):
                        modelFi.append(v1 == v2)
                    else:
                        modelFi.append(Not(v1 == v2))
            print i, modelFi
            print "\n"
            modelF = modelF + modelFi

        assert(is_true(model.eval(And(*modelF))))
        return And(*modelF)

    def stats(self,i):
        stats = []

        #time
        stats.append("%.2f" % self.time)

        # num of iters
        stats.append(i)

        # of input rels
        stats.append(len(self.edb.irels))

        # of output rels
        stats.append(len(self.orels))

        # of pos ex
        stats.append(len(self.pfacts))

        # of neg ex
        stats.append(len(self.nfacts))

        # of clauses
        stats.append(self.nc)

        # of literals
        stats.append(self.nl)

        # bound
        stats.append(self.bound)

        return stats

    def synthesize(self, nc, nl, bound):
        # number of clauses
        self.nc = nc

        # number of literals per clause
        self.nl = nl

        # max relation arity
        self.na = self.getMaxArity()

        # bound on simulation
        self.bound = bound

        allvars = set()

        def intVar(s):
            v = Int(s)
            allvars.add(v)
            return v

        heads = {}
        bodies = {}

        headsConst = []
        bodiesConst = []
        argsConst = []

        # idb relations start at indices > n
        n = len(self.edb.irels)
        m = n + len(self.orels)

        print "n = ", n
        print "m = ", m

        for i in range(1,n+1):
            print i, self.idToRel(i)


        #exit(1)



        # create head and body literal variables
        for i in range(1, nc + 1):
            print "********bodiesConst", bodiesConst
            heads[i] = intVar('H' + str(i))
            print heads[i]
            headsConst.append(And(heads[i] >= n + 1, heads[i] <= m))

            # for every head, there are nl bodies
            bi = []
            for j in range(1, nl + 1):
                bv = intVar('B' + str(i) + "-" + str(j))
                bi.append(bv)
                bodiesConst.append(And(bv >= 1, bv <= m))

                # HACK: Andersen 4 constraints
            #     if i == 1:
            #        bodiesConst.append(bv == 1)
            #     if i == 2:
            #        bodiesConst.append(Or(bv == 2, bv == m))
            #        #bodiesConst.append(m)
            #
            #     if i == 3:
            #        bodiesConst.append(Or(bv == 3, bv == m))
            #        #bodiesConst.append(m)
            #
            #     if i == 4:
            #        bodiesConst.append(Or(bv == 4, bv == m))
            #        #bodiesConst.append(m)
            #
            # andersen = []
            # if i > 1:
            #     disj = []
            #     for b in bi:
            #         disj.append(b == i)
            #
            #     #print "----->", disj
            #     bodiesConst.append(Or(*disj))


            bodies[i] = bi
            print bodies[i]

        #print "---------------------"
        #for b in bodiesConst: print b
        #exit(1)
        argvars = {}
        argvarsset = set()

        print "Head vars", heads
        print "Body vars", bodies

        argWidth = self.na * (self.nl + 1)

        # TEST
        #argWidth = 3

        # argument variables
        for i in range(1, nc + 1):
            hvars = []

            # generate variables for all arities
            for j in range(1, self.na + 1):
                h = intVar('h' + str(i) + "-" + str(j))
                hvars.append(h)
                argsConst.append(And(h >= 1, h <= argWidth))

                # #####TEST
                # if j == 1:
                #     argsConst.append(h == 1)
                # if j == 2:
                #     argsConst.append(h == 2)
            argvars[heads[i]] = hvars
            argvarsset.update(hvars)

        for i in range(1, nc + 1):
            for j in range(1, nl + 1):
                bvars = []
                for k in range(1, self.na + 1):
                    b = intVar('b' + str(i) + "-" + str(j) + "-" + str(k))
                    bvars.append(b)
                    argsConst.append(And(b >= 1, b <= argWidth))

                    # TEST
                    # if i == 1 and k == 1:
                    #     argsConst.append(b == 1)
                    # if i == 1 and k == 2:
                    #     argsConst.append(b == 2)

                argvars[bodies[i][j - 1]] = bvars

                argvarsset.update(bvars)

        print "\n"
        print "Heads constraints", headsConst
        print "Bodies constraints", bodiesConst
        print "Arguments constraints", argsConst

        self.heads = heads
        self.bodies = bodies
        self.argvars = argvars

        headsConst = And(*headsConst)
        bodiesConst = And(*bodiesConst)
        argsConst = And(*argsConst)

        # get simulation constraint
        (simulation,pos) = self.simulation()
        print simulation

        # get symmetry constraint
        symmetry = True
        #if not self.chain:
        #    symmetry = self.getSymmetry()
        print self.argvars

        equality = True
        chain = True

        # enforce chain rule
        if self.chain:
            # HACK: assumes chains of length 1 for base cases
            # base case has chain of length 1
            #for i in range(1,self.base+1):
            #    chain = And(chain, self.getChain(i,1))

            for i in range(self.base+1, self.nc+1):
                ichain = False

                for j in range(1,self.nl+1):
                    ichain = Or(ichain, self.getChain(i,j))

                chain = And(chain, ichain)
            #print simplify(chain)
            #exit(1)

        # enforce equality -- weaker than chain

        for i in range(1, self.nc+1):
            equality = And(equality, self.getEquality(i))

        base = True

        for i in range(1,self.base+1):
            base = And(base, self.getBase(i))

        nonbase = True
        for i in range(self.base+1, self.nc+1):
            nonbase = And(nonbase, self.getNonBase(i))

        # print "b", base
        # print "eq", equality
        # print "ch", chain
        # print "nb", nonbase
        # exit(1)

        if self.soft:
            softC = self.getSoft()
        else:
            softC = []

        softC = softC
        #pos = []
        # exit(1)
        # solve verify loop

        print symmetry
        const = And(headsConst, bodiesConst, argsConst, chain, base, nonbase, simulation, equality)

        # TEST
        #const = And(const, self.bodies[1][0] == 1, self.bodies[1][1] == 1)
        #const = And(const, self.bodies[2][0] == 1, self.bodies[2][1] == 2)

        i = 1
        while True:
            print "Iteration: ", i

            (clauses, model) = self.solveConst(const, pos, softC)
            print "Clauses: "
            for c in clauses:
                print c
            print "\n"
            #raw_input()

            if clauses == None:
                print "no solution exists"
                return False
            if self.verify(clauses):
                print "Success!"
                print "Interation:", i
                for c in clauses:
                    print c

                print "SOLVING TIME: ", self.time

                # TEST
                #phi = model.eval(simulation)
                # solve(phi)
                s = self.stats(i)
                return s
            else:
                modelF = self.negateModel(model)

                negModel = Not(modelF)

                print negModel
                const = And(const, negModel)

            i = i + 1


# rin = Relation("E", 2)
# rout = Relation("T", 2)
#
# oblue = Relation("Outblue", 2)
# ored = Relation("Outred", 2)
#
# blue = Relation("Blue", 2)
# red = Relation("Red", 2)
#
#
# # transitive closure
# # input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4)]
# #
# # pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout, 1, 3)]
# # ne = [Fact(rout, 3, 2), Fact(rout, 3, 3), Fact(rout, 2, 2),
# #       Fact(rout, 1, 1), Fact(rout, 3, 1), Fact(rout, 2, 1)]
# #
# # x = EDB([rin], input)
# # s = STask(x, [rout], pe, ne, domain=5)
# # s.synthesize(nc=2, nl=2, bound=4)
#
# # same generation
# # input = [Fact(rin, 2, 1), Fact(rin, 3, 1), Fact(rin, 4, 2), Fact(rin, 5, 2), Fact(rin, 6 , 3), Fact(rin, 7, 3)]
# #
# # pe = [Fact(rout, 4, 5), Fact(rout, 6, 7), Fact(rout, 2, 3), Fact(rout, 5,6)]
# # ne = [Fact(rout, 2, 5), Fact(rout, 2, 4), Fact(rout, 3, 6),
# #        Fact(rout, 3, 1), Fact(rout, 3, 7), Fact(rout, 1,2), Fact(rout, 2,1)]
# #
# # x = EDB([rin], input)
# # s = STask(x, [rout], pe, ne, domain=8)
# # s.synthesize(nc=2, nl=3, bound=4)
#
# # # undirected TC
# # input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4)]
# #
# # pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout, 3, 4), Fact(rout, 4,3), Fact(rout, 2, 1), Fact(rout, 1,4)]
# # ne = [Fact(rout, 1, 1)]
# #
# # x = EDB([rin], input)
# # s = STask(x, [rout], pe, ne, domain=5)
# # s.synthesize(nc=3, nl=2, bound=7)
#
# # alternating paths
# # input = [Fact(red, 1, 2), Fact(blue, 2, 3), Fact(red, 3, 4), Fact(blue, 4,5), Fact(red, 4,6)]
# #
# # pe = [Fact(rout, 1, 3), Fact(rout, 3, 5), Fact(rout, 1,5)]
# # ne = [Fact(rout, 1, 6)]
# #
# # x = EDB([ blue, red], input)
# # s = STask(x, [rout], pe, ne, domain=7)
# # s.synthesize(nc=2, nl=2, bound=3)
#
# # red and blue
# # requires chain
# input = [Fact(red, 1, 2), Fact(red, 2, 3), Fact(blue, 3, 4), Fact(blue, 4,5)]
#
# pe = [Fact(ored, 1,2), Fact(ored,2,3), Fact(ored, 1, 3), Fact(oblue, 3,4), Fact(oblue, 3, 5), Fact(oblue, 4,5) ]
# ne = [Fact(ored, 1, 5), Fact(ored, 3,1), Fact(ored, 2, 2), Fact(ored, 4,3), Fact(ored, 3,4),  Fact(ored, 2,1), Fact(oblue, 1,2), Fact(oblue,2,3), Fact(ored,4,5), Fact(ored, 1, 1), Fact(oblue, 1, 1), Fact(oblue, 5,3), Fact(oblue, 1,5), Fact(oblue, 1,3), Fact(oblue, 4,3), Fact(oblue, 5,3)]
#
# x = EDB([ blue, red], input)
# s = STask(x, [oblue, ored], pe, ne, domain=6)
# s.synthesize(nc=4, nl=2, bound=6)
#
# # print f
#
# # x = rin.l("a", "b", "c")
# # c = Clause(x, [x, x])
# # print x
