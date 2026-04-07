# d - two dead 
# m - the mother is a murderess
from sympy.abc import d , m , a , b , c , e , f , g , h

from sympy import true

from piter import *

import numpy as np

#p = Piter({d , m})
#p.addP(m , true , 0.0001)
#p.addP(d , true , 0.001)
#p.addP(d , m , 1.0)
#p.finalize()

p = Piter({d , m , a , b , e , f , g , h})
p.addP(e & ~a & ~b & ~d & ~f & ~m & g & h, true , 0.1)
p.addP(b & f & m & ~a & ~d & ~e & g & h , true , 0.1)
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

sol = p.getOptimalSolution(verbose = 1 , epochs = 3000 , stop = 0.00001)

print("optimized solution :" , sol)
print("check normalization :" , sol.sum())
print("check :" , a @ sol - b)


