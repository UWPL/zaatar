class Relation:
    """ Relations """
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity

    def __eq__(self, other):
        return self.name == other.name

    def __repr__(self):
        return self.name + "__" + str(self.arity)

    def l(self, *args):
        return Literal(self,*args)

    def f(self, *args):
        return Fact(self,*args)


class Literal:
    """ Literal appearing in a Horn clause: application of rel to args """
    def __init__(self, rel, *args):
        self.rel = rel
        self.args = args

    def __repr__(self):
        return self.rel.name + str(self.args)

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

        #check all facts belong to declared relations
        for f in facts:
            assert(len(filter(lambda r: r == f.rel, irels)) == 1)

        #check no repeated decl of same relation
        #TODO: fix when relations are hashable
        #assert(len(set(irels)) == len(irels))
        #assert(len(set(orels)) == len(orels))

    def __repr__(self):
        return "irels " + str(self.irels) +  "\nfacts " + str(self.facts)

class Clause:
    """ Clause: Horn clause with head (predicate) and tail (list of predicates) """
    def __init__(self, head, tail):
        self.head = head
        self.tail = tail

    def __repr__(self):
        return str(self.head) + " :- " + str(self.tail)

class Datalog:
    """ Datalog program
        edb: extensional db
        orels: other relations not in db to appear in rules
        cls: list of Horn clauses
    """
    def __init__(self, edb, orels, cls):
        self.edb = edb
        self.orels = orels
        self.cls = cls


class STask:
    """ Synthesis task; consists of
        edb: extensional database
        orels: output relations
        pf: positive facts
        nf: negative facts
    """
    def __init__(self, edb, orels, pf, nf):
        self.edb = edb
        self.orels = orels
        self.pfacts = pf
        self.nfacts = nf

        #check all facts belong to declared relations
        for f in (nf + pf):
            assert(len(filter(lambda r: r == f.rel, self.orels)) == 1)

rin = Relation("Rin",3)
rout = Relation("Rout",3)
assert( rin != rout )

f = Fact(rin,1,2,3)
f2 = Fact(rout,1,2,3)
f3 = Fact(rout,1,2,4)

assert( f != f2 )

x = EDB([rin],[f])
print x

s = STask(x, [rout], [f2], [f3])
print f

x = rin.l("a","b","c")
c = Clause(x, [x,x])
print c
