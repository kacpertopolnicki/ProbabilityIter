# d - two dead 
# m - the mother is a murderess
from sympy.abc import d , m , a , b , c

from sympy import true

from piter import *

import numpy as np

#p = Piter({d , m})
#p.addP(m , true , 0.0001)
#p.addP(d , true , 0.001)
#p.addP(d , m , 1.0)
#p.finalize()

p = Piter({d , m , a , b})
p.addP(m & ~a & ~b & ~d , true , 0.1)
p.addP(b & d & m & ~a , true , 0.1)
p.finalize()

print("""\
d (two dead) and m (mother is a murderess):

base = [\
""")
for dnf in p:
    print("   P(" , dnf , " | X)")
print("]\n")

ab = p.getNumpy()

a = ab[: , :-1]
b = ab[: , -1]

print("a :")
print(a)
print("b :")
print(b)

sol = p.getOptimalSolution()

print("optimized solution :" , sol)
print("check :" , a @ sol - b)


