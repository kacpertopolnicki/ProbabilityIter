import sys

sys.path.append('..')

from piter import Piter

from sympy.abc import d , m , a , b , c , e , f , g , h
from sympy import true
import numpy as np

p = Piter({d , m , a , b , e , f , g , h})
p.addP(e & ~a & ~b & ~d & ~f & ~m & g & h, true , 0.02)
p.addP(b & f & m & ~a & ~d & ~e & g & h , true , 0.02)
p.finalize()

vv , ns = p.getPositiveSolition()

print("vv.shape : " , vv.shape)
print("ns.shape : " , ns.shape)

other = vv > 0.01
newvv = np.random.rand(vv.shape[0])
newvv[other] = 0.0
newvv = 0.96 * newvv / np.sum(newvv)
newvv[other] = vv[other]

print("this schould be 3 : " , np.sum(other))
print("this schould be close to 1 : " , np.sum(newvv[:-1]))

np.savetxt("iterations_0" , newvv[:-1])
res20 = p.optimizeEntropy(vv , ns , epochs = 20)
np.savetxt("iterations_20" , res20)
res40 = p.optimizeEntropy(vv , ns , epochs = 40)
np.savetxt("iterations_40" , res40)
res80 = p.optimizeEntropy(vv , ns , epochs = 80)
np.savetxt("iterations_80" , res80)
res160 = p.optimizeEntropy(vv , ns , epochs = 160)
np.savetxt("iterations_160" , res160)
res320 = p.optimizeEntropy(vv , ns , epochs = 320)
np.savetxt("iterations_320" , res320)

#print("res:")
#print(res)
