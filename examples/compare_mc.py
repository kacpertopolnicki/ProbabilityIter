###############
# DESCRIPTION #
###############

# This is one of two examples:
# 
# - `compare_mc.py` (this example)
# - `compare_mc_1.py`
# 
# that contain a probabilistic description of two architectural structures.
# 
# The fist example `compare_mc.py` considers a simple structure built from two concrete blocks $C$ and $D$:
# ```
#     -----
#     | D |
#     -----
#     | C |
#   ----------
# ```
# Each of these two blocks is expected to fail in the
# next $100$ years with some probability. In the code variables 
# $c$, $d$ state the destruction of block $A$ , $B$.
# Probabilities are assigned to 
# $p(c | x)$ (the failure of block $C$), 
# $p(d | x)$ (the failure of block $D$), and
# $p(d | c x)$ (the destruction of block $D$ if block $C$ fails).
# The $x$ symbolizes implicit assumptions.
# 
# The second example `compare_mc_1.py` considers a more complicated structure:
# ```
#                    --------------
#                    |     G      |
#     -----------------------------  -----
#     |      E            |  |   |   | L |
#     ---------------------  | F |   -----
#     | C |    | D |         |   |   | K |
#   -----------------------------------------
# 
# ```
# composed of $7$ concrete blocks. Again each block is expected
# to fail in the next $100$ with some probability. The values
# of probability, including the vocational probability of the destruction
# of one block given another has failed, are defined in the code.
# 
# Both programs:
# 
# 1. start with specifying the probability values for `Piter`,
# 2. calculate the probability of each combination of failed / intact blocks using `Piter`,
# 3. using the probabilities computed in 2 a Monte Carlo simulation is constructed,
# 4. samples from the simulation 3 are used calculate the input probabilities in 1
# 5. a comparison is of the input probabilities and estimates calculated from the samples
#    is written to standard output


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


