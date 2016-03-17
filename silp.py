from z3 import *

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

    def __repr__(self):
        if len(self.args) == 1:
            args = str(self.args[0])
        else:
            args = reduce(lambda a,b: a+", " +b, self.args)
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
        if len(self.tail) == 1:
            tailStr = str(self.tail[0])
        elif len(self.tail) == 0:
            tailStr = "true"
        else:
            tailStr = reduce(lambda a,b: str(a)+ ", " +str(b), self.tail)
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

    def __init__(self, edb, orels, pf, nf, domain):
        self.edb = edb
        self.orels = orels
        self.pfacts = pf
        self.nfacts = nf
        self.domain = domain

        # check all facts belong to declared relations
        for f in (nf + pf):
            assert(len(filter(lambda r: r == f.rel, self.orels)) == 1)

    def verify(self, clauses):
        s = Fixedpoint()
        d = FiniteDomainSort('D',self.domain+1)
        consts = {}

        args = {}
        rels = {}

        def argsToZ3(l):
            r = []
            for a in l:
                if a in args:
                    r = r + [args[a]]
                else:
                    args[a] = Var(int(a.replace('X','')), d)
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

        #create array of constant values for the given domain:
        for i in range(1,self.domain+1):
            consts[i] = FiniteDomainVal(i,d)

        #register relations in Z3
        for r in self.edb.irels + self.orels:
            print r
            dom = [d for i in range(0,r.arity)] + [BoolSort()]
            rz3 = Function(r.name, *dom)
            rels[r] = rz3
            print "registering ", r, " - > ", rz3
            s.register_relation(rz3)

        # create argument variables for clauses
        for c in clauses:
            head = litToZ3(c.head)
            body = map(litToZ3, c.tail)
            s.rule(head,body)



        #add all facts in EDB
        for f in self.edb.facts:
            s.fact(factToZ3(f))

        print "Created Z3 Fixedpoint"
        print s
        print "Now checking queries"

        #check pos examples
        for p in self.pfacts:
            print "Checking pos", p

            if s.query(factToZ3(p)) == unsat:
                return False


        #check neg examples
        for n in self.nfacts:
            print "Checking neg", n

            if s.query(Not(factToZ3(n))) == unsat:
                return False

        return True



    def getMaxArity(self):
        na = 0
        for r in (self.orels + self.edb.irels):
            r.arity > na
            na = r.arity

        return na

    def idToRel(self,relId):
        i = 1
        for r in  self.edb.irels + self.orels:
            print r
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
        hargsId = map(lambda v: "X"+str(m[v]), self.argvars[h])

        headLiteral = self.idsToLit(headId, hargsId)
        #print headLiteral

        bLiterals = []
        for b in self.bodies[pos]:
            bId = m[b].as_long()
            bargsId = map(lambda v: "X"+str(m[v]), self.argvars[b])
            bLit = self.idsToLit(bId,bargsId)
            bLiterals.append(bLit)
            #print bLit

        clause = Clause(headLiteral, bLiterals)
        print clause
        return clause


    def solveConst(self, phi):
        s = Solver()
        s.add(phi)
        res = s.check()
        print res

        if res == unsat:
            print "No solution found -- unsat"
            return (None,None)
        else:
            m = s.model()
            print m
            cs = []
            print self.nc
            for i in range(1,self.nc+1):
                cs.append(self.modelToClause(m,i))

        return (cs,m)


    def synthesize(self, nc, nl, bound):
        self.nc = nc
        self.nl = nl
        self.na = self.getMaxArity()
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

        n = len(self.edb.irels)
        m = n + len(self.orels)

        print "n = ", n
        print "m = ", m

        # create head and body literal variables
        for i in range(1,nc+1):
            heads[i] = intVar('H'+str(i))
            print heads[i]
            headsConst.append(And(heads[i] >= n+1, heads[i] <= m))

            bi = []
            for j in range(1,nl+1):
                bv = intVar('B'+str(i)+"-"+str(j))
                bi.append(bv)
                bodiesConst.append(And(bv >= 1, bv <= m))

                ######TEST
                # if i == 1:
                #     bodiesConst.append(And(bv == 1))
                #
                # if i == 2:
                #     if j == 1:
                #         bodiesConst.append(And(bv == 1))
                #     else:
                #         bodiesConst.append(And(bv == 2))

            bodies[i] = bi
            print bodies[i]

        argvars = {}

        print "Head vars", heads
        print "Body vars", bodies

        argWidth = self.na*(self.nl+1)

        ### TEST
        #argWidth = 3

        for i in range(1,nc+1):
            hvars = []
            for j in range(1,self.na+1):
                h = intVar('h'+str(i)+"-"+str(j))
                hvars.append(h)
                argsConst.append(And(h >= 1, h <= argWidth))

                # #####TEST
                # if j == 1:
                #     argsConst.append(h == 1)
                # if j == 2:
                #     argsConst.append(h == 2)
            argvars[heads[i]] = hvars

        for i in range(1,nc+1):
            for j in range(1,nl+1):
                bvars = []
                for k in range(1,self.na+1):
                    b = intVar('b'+str(i)+"-"+str(j)+"-"+str(k))
                    bvars.append(b)
                    argsConst.append(And(b >= 1, b <= argWidth))

                    # if i == 1 and k == 1:
                    #     argsConst.append(b == 1)
                    # if i == 1 and k == 2:
                    #     argsConst.append(b == 2)



                argvars[bodies[i][j-1]] = bvars

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


        # solve verify loop
        const = And(headsConst,bodiesConst,argsConst)
        i = 1
        while True:
            print "Iteration: ", i

            (clauses, model) = self.solveConst(const)
            if clauses == None:
                print "no solution exists"
                return False
            if self.verify(clauses):
                print "Success!"
                print "Interation:", i
                for c in clauses:
                    print c
                return True
            else:
                modelF = []
                for v in allvars:
                    phi = (v == model[v])
                    print phi
                    modelF.append(phi)
                negModel = Not(And(*modelF))
                print negModel
                const = And(const,negModel)

            i = i + 1




rin = Relation("Rin", 2)
rout = Relation("Rout", 2)
assert(rin != rout)

f1 = Fact(rin, 1, 2)
f2 = Fact(rin, 2, 3)

pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout,1,3)]
ne = [Fact(rout, 3, 2), Fact(rout, 3, 3), Fact(rout, 2,2)]
#print f

#assert(f != f2)

x = EDB([rin], [f1,f2])
#print x

s = STask(x, [rout], pe, ne, 4)
s.synthesize(nc=2,nl=2,bound=3)
#print f

x = rin.l("a", "b", "c")
c = Clause(x, [x, x])
#print x
