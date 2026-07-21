import sys

sys.path.append('..')

from piter import Piter
from sympy.abc import c , d , e , f , g , k , l
from sympy import true
import sympy
import numpy as np

# Consider the following building composed of 
# concrete blocks:
#                  --------------
#                  |     G      |
#   -----------------------------  -----
#   |      E            |  |   |   | L |
#   ---------------------  | F |   -----
#   | C |    | D |         |   |   | K |
# -----------------------------------------
# Each of the blocks C , D , E , F , G , K
# is expected to fail in the next 100 years
# with a given probability and logical
# statements c , d , e , f , g , k mean the
# descruction of the corresponding block.

p = Piter({c , d , e , f , g , k , l})

p.addP(c , true , 0.2)
print("p(c | x) = 0.2")

p.addP(d , true , 0.1)
print("p(d | x) = 0.1")

p.addP(e , true , 0.2)
print("p(e | x) = 0.2")
# CAREFULL, some values of probability may result in 
# systems without a positive real solution.
# Replace the previous line with the following for an example:
#p.addP(e , true , 0.1)

p.addP(f , true , 0.2)
print("p(f | x) = 0.2")

p.addP(g , true , 0.2)
print("p(g | x) = 0.2")

p.addP(k , true , 0.3)
print("p(k | x) = 0.3")

p.addP(l , true , 0.4)
print("p(l | x) = 0.4")

p.addP(l , k , 0.99)
print("p(l | k) = 0.99") # nearly certain that if k fails l fails

p.addP(e , c & d , 0.9)    # both pillars have failed
print("p(e | c d) = 0.9")

p.addP(e , c & ~d , 0.5)   # pillar c has failed but d is fine
print("p(e | c ~d) = 0.5")

p.addP(e , ~c & d , 0.5)   # pillar d has failed but c is fine
print("p(e | ~c d) = 0.5")

p.addP(g , e & f , 0.9)    # both e and f have failed
print("p(g | e f) = 0.9")

p.addP(g , e & ~f , 0.9)   # e failed f is fine
print("p(g | e ~f) = 0.9")

p.addP(g , ~e & f , 0.9)   # f failed e is fine
print("p(g | ~e f) = 0.9")

p.finalize()

#i = 0
#for s in p:
#    print(i , s)
#    i += 1

ab = p.getNumpy()

a = ab[: , :-1]
b = ab[: , -1]

print("a.shape : " , a.shape)
print("b.shape : " , b.shape)

x = p.getOptimalSolution(method = "default" , verbose = 1)

print("x.shape : " , x.shape)

num , dem = p.getNumDem(c , true)
print("calculated p(c | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(d , true)
print("calculated p(d | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(e , true)
print("calculated p(e | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(f , true)
print("calculated p(f | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(g , true)
print("calculated p(g | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(k , true)
print("calculated p(k | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(l , true)
print("calculated p(l | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(l , k)
print("calculated p(l | k): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(e , c & d)
print("calculated p(e | c d): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(e , c & ~d)
print("calculated p(e | c ~d): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(e , ~c & d)
print("calculated p(e | ~c d): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(g , e & f)
print("calculated p(g | e f): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(g , e & ~f)
print("calculated p(g | e ~f): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(g , ~e & f)
print("calculated p(g | ~e f): " , np.sum(num * x) / np.sum(dem * x))


n = 1000000

samples = np.random.choice(np.array(range(x.shape[0])) , size = n , p = x)

def calculateFromSamples(left , right , samples = samples , x = x):
    leftparts = []
    rightparts = []
    i = 0
    for s in p:
        if sympy.logic.inference.satisfiable(left & s):
            if sympy.logic.inference.satisfiable(right & s):
                leftparts.append(i)
        i += 1
    i = 0
    for s in p:
        if sympy.logic.inference.satisfiable(right & s):
            rightparts.append(i)
        i += 1
    lefttotal = 0
    for i in leftparts:
        lefttotal += np.sum(samples == i)
    righttotal = 0
    for i in rightparts:
        righttotal += np.sum(samples == i)
    return lefttotal / righttotal

print("simulated from solution p(c | x): " , calculateFromSamples(c , true))
print("simulated from solution p(d | x): " , calculateFromSamples(d , true))
print("simulated from solution p(e | x): " , calculateFromSamples(e , true))
print("simulated from solution p(f | x): " , calculateFromSamples(f , true))
print("simulated from solution p(g | x): " , calculateFromSamples(g , true))
print("simulated from solution p(k | x): " , calculateFromSamples(k , true))
print("simulated from solution p(l | x): " , calculateFromSamples(l , true))
print("simulated from solution p(l | k): " , calculateFromSamples(l , k))
print("simulated from solution p(e | c d): " , calculateFromSamples(e , c & d))
print("simulated from solution p(e | c ~d): " , calculateFromSamples(e , c & ~d))
print("simulated from solution p(e | ~c d): " , calculateFromSamples(e , ~c & d))
print("simulated from solution p(g | e f): " , calculateFromSamples(g , e & f))
print("simulated from solution p(g | e ~f): " , calculateFromSamples(g , e & ~f))
print("simulated from solution p(g | ~e f): " , calculateFromSamples(g , ~e & f))


