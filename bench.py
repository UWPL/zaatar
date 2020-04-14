from silp import *
import argparse

parser = argparse.ArgumentParser(description='Zaatar: The Symbolic Datalog Synthesizer')

parser.add_argument("-b", "--benchmark", required=True,
                        help="Input benchmark bench")


parser.add_argument("-l", "--log", required=False, action='store_true',
                        default = False,
                        help="log stats to res.csv")



args = parser.parse_args()


rin = Relation("E", 2)
rout = Relation("T", 2)
cycle = Relation("C", 2)
oneout = Relation("O", 1)
trout = Relation("Tr", 3)

oblue = Relation("Outblue", 2)
ored = Relation("Outred", 2)

blue = Relation("Blue", 2)
red = Relation("Red", 2)

pts = Relation("ptsTo", 2)
asn = Relation("asn", 2)
aof = Relation("aof", 2)
store = Relation("store", 2)
load = Relation("load", 2)

intra = Relation("intra", 2)
call = Relation("call", 2)
ret = Relation("ret", 2)
inter = Relation("inter", 2)

lp = Relation("L", 1)
rp = Relation("R", 1)
ns = Relation("Next", 2)

up = Relation("up", 2)
down = Relation("down", 2)
flat = Relation("flat", 2)

init = Relation("init", 1)
inv = Relation("inv", 2)

if args.benchmark == "TC":
# transitive closure
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4)]

    pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout, 1, 3)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=5, base=1)
    stats = s.synthesize(nc=2, nl=2, bound=4)



# elif args.benchmark == "lasso":
# # cycles
#     input = [Fact(rin, 1, 2), Fact(rin, 2, 3),
#     Fact(rin,3,2), Fact(rin,4,5),Fact(rin,5,6)]
#
#     pe = [Fact(cycle,1,2), Fact(cycle,1,3)]
#     ne = [Fact(cycle,4,5),Fact(cycle,3,1),Fact(cycle,6,4)]
#
#     x = EDB([rin], input)
#     s = STask(x, [cycle,rout], pe, ne, domain=7, base=1, chain=True)
#     stats = s.synthesize(nc=3, nl=2, bound=9)
#
#
#
#
#
#
# elif args.benchmark == "cycle":
# # cycles
#     input = [Fact(rin, 1, 2), Fact(rin, 2, 3),
#     Fact(rin,3,4), Fact(rin,4,3)]
#
#     pe = [Fact(cycle,4,4), Fact(cycle,3,3)]
#     ne = [Fact(cycle,1,1),Fact(cycle,2,2),Fact(cycle,1,2),Fact(cycle,2,1),
#     Fact(cycle,1,3), Fact(cycle,3,1)]
#
#     x = EDB([rin], input)
#     s = STask(x, [rout,cycle], pe, ne, domain=5, base=1, chain=True)
#     stats = s.synthesize(nc=3, nl=2, bound=10)




#
elif args.benchmark == "Reach":
# transitive closure from a starting point (2 in this case)
    input = [Fact(rin, 7, 1), Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 2, 5), Fact(rin, 1,6)]

    pe = [Fact(oneout, 3), Fact(oneout, 2), Fact(oneout, 4), Fact(oneout, 5)]
    ne = [Fact(oneout, 1), Fact(oneout, 6)]

    x = EDB([rin], input)
    s = STask(x, [oneout], pe, ne, domain=8, base=1)
    stats = s.synthesize(nc=2, nl=3, bound=4)


elif args.benchmark == "EP":
# paths of even length
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin,4,5)]

    pe = [Fact(rout, 1, 3), Fact(rout, 2, 4), Fact(rout,1,5)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=6, base=1, chain=False)
    stats = s.synthesize(nc=2, nl=3, bound=3)

elif args.benchmark == "OP":
# paths of odd length
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6)]

    pe = [Fact(rout, 1, 2), Fact(rout, 2,3), Fact(rout, 1,4), Fact(rout, 2,5),Fact(rout,1,6)]
    ne = [ Fact(rout, 5, 1), Fact(rout, 2, 4), Fact(rout, 1, 5), Fact(rout, 4, 2), Fact(rout, 3, 1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=7, base=1, soft=True, chain=False)
    stats = s.synthesize(nc=2, nl=3, bound=6)

elif args.benchmark == "OP3":
# paths of length divisible by 3
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6), Fact(rin,6,7)]

    #pe = [Fact(rout, 1, 4), Fact(rout, 1, 7)]
    #ne = [Fact(rout, 1, 3), Fact(rout, 5, 1), Fact(rout, 2, 4), Fact(rout, 1, 5), Fact(rout, 4, 2), Fact(rout, 3, 1)]

    pe = [Fact(rout, 1, 4), Fact(rout, 1, 7)]
    ne = [Fact(rout, 1, 3),  Fact(rout, 2, 4), Fact(rout, 1, 5), Fact(rout, 4, 2), Fact(rout, 3, 1)]


    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=8, base=1, soft=False, chain=False)
    stats = s.synthesize(nc=2, nl=4, bound=2)

elif args.benchmark == "OP4":
# paths of length divisible by 4
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6), Fact(rin,6,7), Fact(rin,7,8), Fact(rin,8,9)]

    pe = [Fact(rout, 1, 5), Fact(rout, 1, 9)]
    ne = [Fact(rout, 1, 3), Fact(rout, 5, 1), Fact(rout, 2, 4), Fact(rout, 4, 2), Fact(rout, 3, 1)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=10, base=1, soft=False, chain=False)
    stats = s.synthesize(nc=2, nl=5, bound=2)

elif args.benchmark == "SG":
# same generation
    input = [Fact(rin, 2, 1), Fact(rin, 3, 1), Fact(rin, 4, 2), Fact(rin, 5, 2), Fact(rin, 6 , 3), Fact(rin, 7, 3)]

    pe = [Fact(rout, 4, 5), Fact(rout, 6, 7), Fact(rout, 2, 3), Fact(rout, 5,6)]
    ne = [Fact(rout, 2, 5)]

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=8, base=1, soft=False)
    stats = s.synthesize(nc=2, nl=3, bound=4)


elif args.benchmark == "UpDown":
# same generation with up/down
    input = [Fact(up, 7, 1), Fact(up, 8, 1), Fact(up, 1, 2),
    Fact(down, 3, 4), Fact(down, 3 , 5), Fact(down, 4, 6),
    Fact(flat, 2, 3)]

    pe = [Fact(rout, 2, 3), Fact(rout, 1, 4), Fact(rout, 1, 5), Fact(rout, 7,6), Fact(rout, 8, 6)]
    ne = [Fact(rout, 2, 5), Fact(rout, 2, 4), Fact(rout, 3, 6),
           Fact(rout, 3, 1), Fact(rout, 3, 7), Fact(rout, 1,2), Fact(rout, 1, 6)]

    x = EDB([up, down, flat], input)
    s = STask(x, [rout], pe, ne, domain=9, base=1, soft=False)
    stats = s.synthesize(nc=2, nl=3, bound=5)


elif args.benchmark == "UTC":
    # undirected TC
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4)]

    pe = [Fact(rout, 1, 2), Fact(rout, 2, 3), Fact(rout, 3, 4), Fact(rout, 4,3), Fact(rout, 2, 1), Fact(rout, 1,4)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=5, base=2, soft=False)
    stats = s.synthesize(nc=3, nl=2, bound=7)

elif args.benchmark == "Balance":
    # balancing parentheses
    # Balance(x, y) :- Left(x), Next(x, y), Right(y).
    # Balance(x, y) :- Left(x), Balance(x, y), Right(y).
    # Balance(x, y) :- Balance(x, z), Next(z, w), Balance(w, y).

    input = [Fact(lp, 1), Fact(lp, 2), Fact(lp, 4), Fact(lp, 7),
    Fact(rp, 3), Fact(rp, 5), Fact(rp, 6), Fact(rp, 8),
    Fact(ns, 1, 2), Fact(ns, 2, 3), Fact(ns, 3,4), Fact(ns,4,5), Fact(ns, 5, 6), Fact(ns, 6, 7), Fact(ns, 7, 8)]

    pe = [Fact(rout, 2, 3), Fact(rout, 4, 5), Fact(rout, 2, 5), Fact(rout, 1, 6), Fact(rout, 7, 8), Fact(rout, 1, 8)]
    ne = [Fact(rout, 2, 4), Fact(rout,  5, 1), Fact(rout, 1, 7), Fact(rout, 1, 3), Fact(rout, 2, 6), Fact(rout, 2, 7), Fact(rout, 7, 2), Fact(rout, 7, 3), Fact(rout, 4, 7), Fact(rout, 4, 8)]

    x = EDB([lp, rp, ns], input)
    s = STask(x, [rout], pe, ne, domain=9, base=1, soft=False, chain=True)
    stats = s.synthesize(nc=3, nl=3, bound=6)

# elif args.benchmark == "Eq":
#     # undirected TC
#     input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 5, 6)]
#
#     pe = [Fact(rout, 1, 1), Fact(rout, 2, 2), Fact(rout, 4, 4), Fact(rout, 2,3), Fact(rout, 4, 1), Fact(rout, 6 ,5), Fact(rout, 1, 4)]
#     ne = [Fact(rout, 1, 6), Fact(rout, 2, 5), Fact(rout, 5, 1), Fact(rout, 3, 6)]
#
#     x = EDB([rin], input)
#     s = STask(x, [rout], pe, ne, domain=7, base=2, soft=False, chain=True)#True)
#     stats = s.synthesize(nc=3, nl=2, bound=10)


# the next examples are for non-recursive conjunctive queries
elif args.benchmark == "P3":
    # path of length 3
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5)]

    pe = [Fact(rout, 1, 4)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=6, base=1, soft=True)
    stats = s.synthesize(nc=1, nl=3, bound=2)

elif args.benchmark == "P4":
    # path of length 4
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4), Fact(rin, 4, 5),Fact(rin,5,6)]

    pe = [Fact(rout, 1, 5), Fact(rout, 2,6)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [rout], pe, ne, domain=7, base=1, soft=False)
    stats = s.synthesize(nc=1, nl=4, bound=2)


elif args.benchmark == "RedBlue":
    # starts red then blue
    # T(x, y) :-  Red(x, z), Blue(z, y).
    input = [Fact(red, 1, 2), Fact(blue, 2, 3), Fact(red, 3, 4), Fact(blue, 4,5), Fact(red, 4,6)]

    pe = [Fact(rout, 1, 3)]
    ne = []

    x = EDB([red, blue], input)
    s = STask(x, [rout], pe, ne, domain=7, base=1, soft=True)
    stats = s.synthesize(nc=1, nl=3, bound=2)

elif args.benchmark == "RedBlueS":
    # starts red then blue but symmetric
    # T(x, y) :-  Red(x, z), Blue(z, y).
    # T(y, x) :-  Red(x, z), Blue(z, y).
    input = [Fact(red, 1, 2), Fact(blue, 2, 3), Fact(red, 3, 4), Fact(blue, 4,5), Fact(red, 4,6)]

    pe = [ Fact(rout, 3,5), Fact(rout, 3, 1)]
    ne = []
            #, Fact(rout, 2, 3), Fact(rout, 5, 1), Fact(rout, 4, 2)]

    x = EDB([red, blue], input)
    s = STask(x, [rout], pe, ne, domain=7, base=2, soft=True)
    stats = s.synthesize(nc=2, nl=3, bound=3)


elif args.benchmark == "Triangle":
    # triangles
    # Triangle(x, y, z) :- E(x, y), E(x, y), E(y, z).
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 1), Fact(rin,4,1), Fact(rin,1,4)]

    pe = [Fact(trout, 1, 2, 3), Fact(trout, 2, 3, 1)]
    ne = [Fact(trout, 1, 3, 2), Fact(trout, 1, 1, 2), Fact(trout, 4, 1, 2), Fact(trout, 4, 2, 3), Fact(trout, 1, 3, 4), Fact(trout,2,4,1), Fact(trout,4,1,3), Fact(trout,4,3,1)]

    x = EDB([rin], input)
    s = STask(x, [trout], pe, ne, domain=5, base=1, soft=False,chain=False)
    stats = s.synthesize(nc=1, nl=3, bound=2)


elif args.benchmark == "2C":
    # vertex that stars a 2-cycle
    # Out(x) :- E(x, y), E(y, x).
    input = [Fact(rin, 1, 2), Fact(rin, 2, 1), Fact(rin, 3, 1), Fact(rin,4,1), Fact(rin,1,4), Fact(rin,4,5)]

    pe = [Fact(oneout, 1), Fact(oneout, 2), Fact(oneout, 4)]
    ne = []

    x = EDB([rin], input)
    s = STask(x, [oneout], pe, ne, domain=6, base=1, soft=False,chain=False)
    stats = s.synthesize(nc=1, nl=2, bound=3)


elif args.benchmark == "AP":
# alternating paths
    input = [Fact(red, 1, 2), Fact(blue, 2, 3), Fact(red, 3, 4), Fact(blue, 4,5), Fact(red, 4,6)]

    pe = [Fact(rout, 1, 3), Fact(rout, 3, 5), Fact(rout, 1,5)]
    ne = [Fact(rout, 1, 6)]

    x = EDB([ blue, red], input)
    s = STask(x, [rout], pe, ne, domain=7, base=1)
    stats = s.synthesize(nc=2, nl=2, bound=3)

# red and blue
# requires chain to finish in 2sec
elif args.benchmark == "RB":
    input = [Fact(red, 1, 2), Fact(red, 2, 3), Fact(blue, 3, 4), Fact(blue, 4,5)]

    pe = [Fact(ored, 1,2), Fact(ored,2,3), Fact(ored, 1, 3), Fact(oblue, 3,4), Fact(oblue, 3, 5), Fact(oblue, 4,5) ]
    ne = []

    x = EDB([ blue, red], input)
    s = STask(x, [oblue, ored], pe, ne, domain=6, base=2, chain=False)
    stats = s.synthesize(nc=4, nl=2, bound=6)

# # red and blue -- one output relation
# # requires chain to finish in 2sec
# elif args.benchmark == "RBO":
#     input = [Fact(red, 1, 2), Fact(red, 2, 3), Fact(blue, 3, 4), Fact(blue, 4,5)]
#
#     pe = [Fact(rout, 1,2), Fact(rout,2,3), Fact(rout, 1, 3), Fact(rout, 3,4), Fact(rout, 3, 5), Fact(rout, 4,5) ]
#     ne = [Fact(rout, 1, 5), Fact(rout, 3,1), Fact(rout, 2, 2), Fact(rout, 4,3), Fact(rout, 3,4),  Fact(rout, 2,1), Fact(rout, 1,2), Fact(rout,2,3), Fact(rout,4,5), Fact(rout, 1, 1), Fact(rout, 1, 1), Fact(rout, 5,3), Fact(rout, 1,5), Fact(rout, 1,3), Fact(rout, 4,3), Fact(rout, 5,3)]
#
#     x = EDB([ blue, red], input)
#     s = STask(x, [rout, oblue, ored], pe, ne, domain=6, base=2, chain=True)
#     stats = s.synthesize(nc=5, nl=2, bound=12)

# Andersen (3 rules -- no load)
elif args.benchmark == "And3":
    input = [Fact(aof,1,2), Fact(aof,2,3), Fact(aof,3,5), Fact(aof,5,6), Fact(asn,4,1),
    Fact(store,4,5)]

    pe = [Fact(pts,1,2),Fact(pts,2,3),Fact(pts,4,2), Fact(pts, 3,5), Fact(pts,5,6), Fact(pts,2,6)]
    ne = []

    x = EDB([aof, asn, store], input)
    s = STask(x, [pts], pe, ne, domain=7, base=1, chain=False,andersen=True)
    stats = s.synthesize(nc=3, nl=3, bound=6)

# Andersen (full)
# PointsTo(y, x) :- AddressOf(y, x).
# PointsTo(y, x) :- Assign(y, z), PointsTo(z, x).
# PointsTo(z, w) :- Store(y, x), PointsTo(y, z), PointsTo(x, w).
# PointsTo(y, w) :- Load(y, x), PointsTo(x, z), PointsTo(z, w).
elif args.benchmark == "And":
    input = [
    Fact(aof,1,2),
    Fact(aof,2,3),
    Fact(aof,3,5),
    Fact(aof,5,6),
    Fact(asn,4,1),
    Fact(store,4,5),
    Fact(load,7,2)
    ]

    pe = [
    Fact(pts,1,2),
    Fact(pts,2,3),
    Fact(pts, 3,5),
    Fact(pts,4,2),
    Fact(pts,5,6),
    Fact(pts,2,6),
    Fact(pts,7,5)
    ]
    ne = [
    Fact(pts,1,5)
    ]

    x = EDB([aof, asn, store, load], input)
    s = STask(x, [pts], pe, ne, domain=8, base=1, chain=False,andersen=True)
    stats = s.synthesize(nc=4, nl=3, bound=7)

if args.benchmark == "INV":
# transitive closure
    input = [Fact(rin, 1, 2), Fact(rin, 2, 3), Fact(rin, 3, 4),Fact(rin,5,6),
            Fact(init,1)]

    pe = [Fact(oneout, 1), Fact(oneout, 2), Fact(oneout, 3),Fact(oneout,4)]
    ne = [Fact(oneout,5),Fact(oneout,6)]

    x = EDB([rin,init], input)
    s = STask(x, [oneout], pe, ne, domain=7, base=1)
    stats = s.synthesize(nc=2, nl=2, bound=4)

if args.benchmark == "CLEVR":
    for r in [2]:
        input = [Fact(rin,x,x+1) for x in range(1,r)]
        pe = [Fact(oneout,r)]
        ne = [Fact(oneout,x) for x in range(1,r)]
        x = EDB([rin], input)
        s = STask(x, [oneout], pe, ne, domain=r+1, base=1)
        stats = s.synthesize(nc=1, nl=r, bound=1)
        print ("DONE with: ", r)
        print (stats)

# Steensgaard3
# PointsTo(y, x) :- AddressOf(y, x).
# ptsto(q,x) :- Assign(p,q), ptsto(p,x).
# ptsto(q,x) :- store(p,q), ptsto(p,y), ptsto(y,x).
# (not included) ptsto(q,y) :- load(p,q), ptsto(p,y), ptsto(q,x).
# elif args.benchmark == "Steen3":
#     input = [
#     Fact(aof,1,2),
#     Fact(aof,5,6),
#     Fact(aof,6,7),
#     Fact(asn,5,1),
#     Fact(store,5,1)
#     ]
#
#     pe = [
#     Fact(pts,1,2),
#     Fact(pts,5,6),
#     Fact(pts,6,7),
#     Fact(pts,1,6),
#     Fact(pts,1,7)
#     ]
#     ne = []
#
#     x = EDB([aof, asn, store], input)
#     s = STask(x, [pts], pe, ne, domain=8, base=1, chain=False)
#     stats = s.synthesize(nc=3, nl=3, bound=5)

# # Steensgaard (full)
# # PointsTo(y, x) :- AddressOf(y, x).
# # ptsto(q,x) :- Assign(p,q), ptsto(p,x).
# # ptsto(q,x) :- store(p,q), ptsto(p,y), ptsto(y,x).
# # ptsto(q,y) :- load(p,q), ptsto(p,y), ptsto(q,x).
# elif args.benchmark == "Steen":
#     input = [
#     Fact(aof,1,2),
#     Fact(aof,5,6),
#     Fact(aof,6,7),
#     Fact(asn,5,1),
#     Fact(store,5,1),
#     Fact(load,1,6)
#     ]
#
#     pe = [
#     Fact(pts,1,2),
#     Fact(pts,5,6),
#     Fact(pts,6,7),
#     Fact(pts,1,6),
#     Fact(pts,1,7),
#     Fact(pts,6,2)
#     ]
#     ne = []
#
#     x = EDB([aof, asn, store, load], input)
#     s = STask(x, [pts], pe, ne, domain=8, base=1, chain=False)
#     stats = s.synthesize(nc=4, nl=3, bound=6)
#
# elif args.benchmark == "callRet":
#     input = [
#     Fact(intra,1,2),
#     Fact(call,2,3),
#     Fact(intra,3,4),
#     Fact(ret,4,5),
#     Fact(intra,5,6)
#     ]
#
#     pe = [
#     Fact(inter,1,2),
#     Fact(inter,3,4),
#     Fact(inter,5,6),
#     Fact(inter,1,6)
#     ]
#     ne = [
#     Fact(inter,1,4),
#     Fact(inter,1,5)
#     ]
#
#     x = EDB([intra, call, ret], input)
#     s = STask(x, [inter], pe, ne, domain=7, base=1, soft=True,chain=True)
#     stats = s.synthesize(nc=2, nl=5, bound=4)


else:
    print ("No such benchmark available")
# print f

res = ", ".join(map(str,[args.benchmark] + stats))
print (res)

if args.log:
    f = open('res.csv', 'a')
    f.write(res+"\n")
    f.close()

# x = rin.l("a", "b", "c")
# c = Clause(x, [x, x])
# print x
