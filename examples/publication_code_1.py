import sys

sys.path.append('..')

from piter import Piter
from sympy.abc import A , B , C , O
from sympy import true
import numpy as np

p = Piter({A , B , C , O})
p.addConstraint((A & ~B & ~C) | (~A & B & ~C) | (~A & ~B & C))
p.addConstraint(~(O & B))
p.addP(A , true , 1.0 / 3.0)
p.addP(B , true , 1.0 / 3.0)
p.addP(C , true , 1.0 / 3.0)
p.addP(O , A , 0.5)
p.addP(O , C , 1.0)
p.finalize()

ab = p.getNumpy()

a = ab[: , :-1]
b = ab[: , -1]

x , residuals , rank , s = np.linalg.lstsq(a , b)

num , dem = p.getNumDem(A , O)
dont_switch = np.sum(num * x) / np.sum(dem * x)

print("prob. of success when testing sample 1 : " , dont_switch)

num , dem = p.getNumDem(C , O)
switch = np.sum(num * x) / np.sum(dem * x)

print("prob. of success when switching to sample 3:" , switch)



