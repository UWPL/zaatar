from silp import *
import argparse

parser = argparse.ArgumentParser(description='Zaatar: The Symbolic Datalog Synthesizer')

parser.add_argument("-b", "--benchmark", required=True,
                        help="Input benchmark bench")


args = parser.parse_args()


rin = Relation("E", 2)
rout = Relation("T", 2)
trout = Relation("Tr", 3)

oblue = Relation("Outblue", 2)
ored = Relation("Outred", 2)

blue = Relation("Blue", 2)
red = Relation("Red", 2)

pts = Relation("ptsTo", 2)
asn = Relation("asn", 2)
aof = Relation("aof", 2)
store = Relation("store", 2)

if args.benchmark == "TC":
# transitive closure
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4)]

    pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout, 1, 3)]
    ne = [Fact(rout, 3, 2), Fact(rout, 3, 3), Fact(rout, 2, 2),
          Fact(rout, 1, 1), Fact(rout, 3, 1), Fact(rout, 2, 1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=5, base=1)
    s.synthesize(nc=2, nl=2, bound=4)

if args.benchmark == "EP":
# paths of even length
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin,4,5)]

    pe = [Fact(rout, 1, 3), Fact(rout, 2, 4), Fact(rout,1,5)]
    ne = [Fact(rout, 1, 2), Fact(rout,3,1), Fact(rout,1,1), Fact(rout,2,1), Fact(rout,3,3), Fact(rout,1,4), Fact(rout, 3,4)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=6, base=1, chain=False)
    s.synthesize(nc=2, nl=3, bound=3)

elif args.benchmark == "OP":
# paths of odd length
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6)]

    pe = [Fact(rout, 1, 2), Fact(rout, 2,3), Fact(rout, 1,4), Fact(rout, 2,5),Fact(rout,1,6)]
    ne = [Fact(rout, 1, 3), Fact(rout, 5, 1), Fact(rout, 2, 4), Fact(rout, 1, 5), Fact(rout, 4, 2), Fact(rout, 3, 1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=7, base=1, soft=True, chain=False)
    s.synthesize(nc=2, nl=3, bound=6)

elif args.benchmark == "OP3":
# paths of length divisible by 3
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6), Fact(rin,6,7)]

    pe = [Fact(rout, 1, 4), Fact(rout, 1, 7)]
    ne = [Fact(rout, 1, 3), Fact(rout, 5, 1), Fact(rout, 2, 4), Fact(rout, 1, 5), Fact(rout, 4, 2), Fact(rout, 3, 1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=8, base=1, soft=False, chain=False)
    s.synthesize(nc=2, nl=4, bound=2)

elif args.benchmark == "OP4":
# paths of length divisible by 4
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6), Fact(rin,6,7), Fact(rin,7,8), Fact(rin,8,9)]

    pe = [Fact(rout, 1, 5), Fact(rout, 1, 9)]
    ne = [Fact(rout, 1, 3), Fact(rout, 5, 1), Fact(rout, 2, 4), Fact(rout, 4, 2), Fact(rout, 3, 1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=10, base=1, soft=False, chain=False)
    s.synthesize(nc=2, nl=5, bound=2)

elif args.benchmark == "SG":
# same generation
    input = [Fact(rin, 2, 1), Fact(rin, 3, 1), Fact(rin, 4, 2), Fact(rin, 5, 2), Fact(rin, 6 , 3), Fact(rin, 7, 3)]

    pe = [Fact(rout, 4, 5), Fact(rout, 6, 7), Fact(rout, 2, 3), Fact(rout, 5,6)]
    ne = [Fact(rout, 2, 5), Fact(rout, 2, 4), Fact(rout, 3, 6),
           Fact(rout, 3, 1), Fact(rout, 3, 7), Fact(rout, 1,2), Fact(rout, 2,1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=8, base=1, soft=False)
    s.synthesize(nc=2, nl=3, bound=4)

elif args.benchmark == "UTC":
    # undirected TC
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4)]

    pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout, 3, 4), Fact(rout, 4,3), Fact(rout, 2, 1), Fact(rout, 1,4)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=5, base=2, soft=False)
    s.synthesize(nc=3, nl=2, bound=7)

elif args.benchmark == "Eq":
    # undirected TC
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 5, 6)]

    pe = [Fact(rout, 1, 1), Fact(rout, 2, 2), Fact(rout, 4, 4), Fact(rout, 2,3), Fact(rout, 4, 1), Fact(rout, 6 ,5), Fact(rout, 1, 4)]
    ne = [Fact(rout, 1, 6), Fact(rout, 2, 5), Fact(rout, 5, 1), Fact(rout, 3, 6)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=7, base=2, soft=False, chain=True)#True)
    s.synthesize(nc=3, nl=2, bound=10)


elif args.benchmark == "P3":
    # path of length 3 (non-recursive)
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5)]

    pe = [Fact(rout, 1, 4), Fact(rout, 2,5)]
    ne = [Fact(rout, 1, 3), Fact(rout, 2, 3), Fact(rout, 1, 5), Fact(rout, 4, 2), Fact(rout, 1, 2)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=6, base=1, soft=True)
    s.synthesize(nc=1, nl=3, bound=2)



elif args.benchmark == "Triangle":
    # triangles
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 1), Fact(rin,4,1), Fact(rin,1,4)]

    pe = [Fact(trout, 1, 2, 3), Fact(trout, 2, 3, 1)]
    ne = [Fact(trout, 1, 3, 2), Fact(trout, 1, 1, 2), Fact(trout, 4, 1, 2), Fact(trout, 4, 2, 3), Fact(trout, 1, 3, 4), Fact(trout,2,4,1), Fact(trout,4,1,3), Fact(trout,4,2,1), Fact(trout,4,3,1)]

    x = EDB([rin], input)
    s = STask(x, [trout], pe, ne, domain=5, base=1, soft=False,chain=False)
    s.synthesize(nc=1, nl=3, bound=2)


elif args.benchmark == "AP":
# alternating paths
    input = [Fact(red, 1, 2), Fact(blue, 2, 3), Fact(red, 3, 4), Fact(blue, 4,5), Fact(red, 4,6)]

    pe = [Fact(rout, 1, 3), Fact(rout, 3, 5), Fact(rout, 1,5)]
    ne = [Fact(rout, 1, 6)]

    x = EDB([ blue, red], input)
    s = STask(x, [rout], pe, ne, domain=7, base=1)
    s.synthesize(nc=2, nl=2, bound=3)

# red and blue
# requires chain to finish in 2sec
elif args.benchmark == "RB":
    input = [Fact(red, 1, 2), Fact(red, 2, 3), Fact(blue, 3, 4), Fact(blue, 4,5)]

    pe = [Fact(ored, 1,2), Fact(ored,2,3), Fact(ored, 1, 3), Fact(oblue, 3,4), Fact(oblue, 3, 5), Fact(oblue, 4,5) ]
    ne = [Fact(ored, 1, 5), Fact(ored, 3,1), Fact(ored, 2, 2), Fact(ored, 4,3), Fact(ored, 3,4),  Fact(ored, 2,1), Fact(oblue, 1,2), Fact(oblue,2,3), Fact(ored,4,5), Fact(ored, 1, 1), Fact(oblue, 1, 1), Fact(oblue, 5,3), Fact(oblue, 1,5), Fact(oblue, 1,3), Fact(oblue, 4,3), Fact(oblue, 5,3)]

    x = EDB([ blue, red], input)
    s = STask(x, [oblue, ored], pe, ne, domain=6, base=2, chain=False)
    s.synthesize(nc=4, nl=2, bound=6)

# red and blue -- one output relation
# requires chain to finish in 2sec
elif args.benchmark == "RBO":
    input = [Fact(red, 1, 2), Fact(red, 2, 3), Fact(blue, 3, 4), Fact(blue, 4,5)]

    pe = [Fact(rout, 1,2), Fact(rout,2,3), Fact(rout, 1, 3), Fact(rout, 3,4), Fact(rout, 3, 5), Fact(rout, 4,5) ]
    ne = [Fact(rout, 1, 5), Fact(rout, 3,1), Fact(rout, 2, 2), Fact(rout, 4,3), Fact(rout, 3,4),  Fact(rout, 2,1), Fact(rout, 1,2), Fact(rout,2,3), Fact(rout,4,5), Fact(rout, 1, 1), Fact(rout, 1, 1), Fact(rout, 5,3), Fact(rout, 1,5), Fact(rout, 1,3), Fact(rout, 4,3), Fact(rout, 5,3)]

    x = EDB([ blue, red], input)
    s = STask(x, [rout, oblue, ored], pe, ne, domain=6, base=2, chain=True)
    s.synthesize(nc=5, nl=2, bound=12)

# Andersen
elif args.benchmark == "And":
    input = [Fact(aof,1,2), Fact(aof,2,3), Fact(asn,4,1)]

    pe = [Fact(pts,1,2),Fact(pts,2,3),Fact(pts,4,2)]
    ne = []

    x = EDB([aof, asn, store], input)
    s = STask(x, [pts], pe, ne, domain=5, base=1, chain=True)
    s.synthesize(nc=2, nl=2, bound=3)

else:
    print "No such benchmark available"
# print f

# x = rin.l("a", "b", "c")
# c = Clause(x, [x, x])
# print x
