import sys

sys.path.append('..')

from piter import Piter
from sympy.abc import c , d
from sympy import true
import sympy
import numpy as np

# Consider the following building composed of 
# concrete blocks:
#   -----
#   | D |
#   -----
#   | C |
# ----------
# Each of the blocks C , D
# is expected to fail in the next 100 years
# with a given probability and logical
# statements c , d mean the
# descruction of the corresponding block.

p = Piter({c , d})
p.addP(c , true , 0.1)
p.addP(d , true , 0.2)
p.addP(d , c , 0.9)
p.finalize()

print("p(c | x) = 0.1")
print("p(d | x) = 0.2")
print("p(d | c) = 0.9")

i = 0
for s in p:
    print(i , s)
    i += 1

ab = p.getNumpy()

a = ab[: , :-1]
b = ab[: , -1]

x , residuals , rank , s = np.linalg.lstsq(a , b)

num , dem = p.getNumDem(c , true)
print("calculated p(c | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(d , true)
print("calculated p(d | x): " , np.sum(num * x) / np.sum(dem * x))

num , dem = p.getNumDem(d , c)
print("calculated p(d | c): " , np.sum(num * x) / np.sum(dem * x))

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
print("simulated from solution p(d | c): " , calculateFromSamples(d , c))


