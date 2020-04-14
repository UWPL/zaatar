import json
from silp import *
import argparse

import signal
from contextlib import contextmanager

class TimeoutException(Exception): pass

@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        raise TimeoutException("Timed out!")
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)



    
parser = argparse.ArgumentParser(description='CLEVER on Zaatar')

parser.add_argument("-f", "--file", required=True,
                        help="Input data file")

parser.add_argument("-l", "--litnum", required=True,
                        help="Bound on # of literals")

parser.add_argument("-i", "--ilim", required=True,
                        help="Time limit per test")

args = parser.parse_args()

f = open(args.file)
x = json.load(f)

rblue = Relation('Blue',1)
rred = Relation('Red',1)
rgreen = Relation('Green',1)
ryellow = Relation('Yellow',1)
rcyan = Relation('Cyan',1)
rpurple = Relation('Purple',1)
rgray = Relation('Gray',1)
rbrown = Relation('Brown',1)

rsmall = Relation('Small',1)
rlarge = Relation('Large',1)

rcylinder = Relation('Cylinder',1)
rsphere = Relation('Sphere',1)
rcube = Relation('Cube',1)

rmetal = Relation('Metal',1)
rrubber = Relation('Rubber',1)

rleft = Relation('Left',2)
rright = Relation('Right',2)
rfront = Relation('Front',2)
rbehind = Relation('Behind',2)

rout = Relation('O',1)

rins = [rblue,
    rred,
    rgreen,
    ryellow ,
    rcyan ,
    rpurple ,
    rgray ,
    rbrown ,

    rsmall ,
    rlarge ,

    rcylinder ,
    rsphere ,
    rcube ,

    rmetal ,
    rrubber ,

    rleft ,
    rright,
    rfront ,
    rbehind 
]

solved = 0
total = 0
for t in x:
    # test example t
    fs = []
    for i,o in enumerate(t['objects'],1):
        if o['size'] == 'large':
            fs.append(Fact(rlarge,i))
        elif o['size'] == 'small':
            fs.append(Fact(rsmall,i))
        else:
            assert(False)
            
        if o['material'] == 'rubber':
            fs.append(Fact(rrubber,i))
        elif o['material'] == 'metal':
            fs.append(Fact(rmetal,i))
        else:
            assert(False)
            
        if o['color'] == 'blue':
            fs.append(Fact(rblue,i))
        elif o['color'] == 'red':
            fs.append(Fact(rred,i))
        elif o['color'] == 'green':
            fs.append(Fact(rgreen,i))
        elif o['color'] == 'yellow':
            fs.append(Fact(ryellow,i))    
        elif o['color'] == 'cyan':
            fs.append(Fact(rcyan,i))
        elif o['color'] == 'purple':
            fs.append(Fact(rpurple,i)) 
        elif o['color'] == 'gray':
            fs.append(Fact(rgray,i))
        elif o['color'] == 'brown':
            fs.append(Fact(rbrown,i)) 
        else:
            print (o['color'])
            assert(False)
            
        if o['shape'] == 'cylinder':
            fs.append(Fact(rcylinder,i))
        elif o['shape'] == 'sphere':
            fs.append(Fact(rsphere,i))
        elif o['shape'] == 'cube':
            fs.append(Fact(rcube,1))
        else:
            assert(False)
            
    for i,os in enumerate(t['relationships']['left'],1):    
        for o in os:
            fs.append(Fact(rleft,i,o+1))
    
    for i,os in enumerate(t['relationships']['right'],1):    
        for o in os:
            fs.append(Fact(rright,i,o+1))
            
    for i,os in enumerate(t['relationships']['behind'],1):    
        for o in os:
            fs.append(Fact(rbehind,i,o+1))
    
    for i,os in enumerate(t['relationships']['front'],1):    
        for o in os:
            fs.append(Fact(rfront,i,o+1))
            
    # create all synthesis instances
    nobj = len(t['objects'])
    
    for o in range(1,nobj+1):
        pe = [Fact(rout, o)]
        nes = [Fact(rout,x) for x in range(1,o)]
        nes = nes + [Fact(rout,x) for x in range(o+1,nobj+1)]
        print (pe)
        print (nes)

        edb = EDB(rins,fs)
        s = STask(edb, [rout], pe,nes,domain=nobj+1,base=1)
        
        try:
            try:
                with time_limit(int(args.ilim)):
                    for i in range(1,int(args.litnum)+1):
                        stats = s.synthesize(nc=1, nl=i, bound=1)
                        if stats != False: break
            except TimeoutException as e:
                stats = False
                print("Timed out!")
        except:
            stats = False
            print ("Timed out2")
            

        
        print (stats)
        total = total+1
        if stats != False:
            solved = solved + 1
        print (solved, "out of", total)

print (solved, "out of", total)
