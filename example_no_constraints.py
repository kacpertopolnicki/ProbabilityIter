# d - two dead 
# m - the mother is a murderess
from sympy.abc import d , m

from sympy import true

from piter import *

import numpy as np

p = Piter({d , m})
p.addP(m , true , 0.0001)
p.addP(d , true , 0.001)
p.addP(d , m , 1.0)
p.finalize()

# print DNF expressions in p
print("""\
Probabilities of DNF expressions created from 
d (two dead) and m (mother is a murderess):

x = [\
""")
for dnf in p:
    print("   P(" , dnf , " | X)")
print("]\n")

ab = p.getNumpy()

print("In A x = b, the matrix (A|b):\n")
print(ab , "\n")

a = ab[: , :-1]
b = ab[: , -1]
x = np.linalg.solve(a , b)

print("The solution:")
print("x =" , x , "\n")
print("Sum of probabilities in x:" , np.sum(x) , "\n")

num , dem = p.getNumDem(m , d)

print("""\
Probability that the mother is a murderess
if two are dead:\
""")
print(np.sum(num * x) / np.sum(dem * x) , "\n")

num , dem = p.getNumDem(~m , d)

print("""\
Probability that the mother is not a murderess
if two are dead:\
""")
print(np.sum(num * x) / np.sum(dem * x))
