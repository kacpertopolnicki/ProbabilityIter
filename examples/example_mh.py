###############
# DESCRIPTION #
############### 

# This is one of three examples related to the 
# [Monty Hall problem](https://en.wikipedia.org/wiki/Monty_Hall_problem).
# In the code we use the notation from 
# [this lecture](https://bechtel.colorado.edu/~balajir/CVEN5454/lectures/monty.pdf).
# The `sympy` symbols `A`, `B`, `C` are statemets about the placement
# of the car: behind curtain 1 , 2 , 3 respectively. `O` symbolizes
# the statement that Monty Hall opens curtain number 2.
# 
# - `example_mh.py` (this example)
#   - Simple setup, the comments in the code contain descriptions 
#     of the assumed probabilities and constraints.
# - `example_mh_optimize.py`
#   - Additional statements, irrelevant to the problem are introduced
#     to test optimization. The additional statements
#     increase the size of the problem but the calculated probabilities
#     are the same as in the basic example.
# - `example_mh_optimize_.py`
#   - Alternative problem setup to test optimization, note that for numerical purposes `p.addP(O , C , 0.99999)`
#     is used instead of `p.addP(O , C , 1.0)`.

import sys

sys.path.append('..')
from piter import Piter

def main():
    # sauce : https://bechtel.colorado.edu/~balajir/CVEN5454/lectures/monty.pdf
    # A , B , C - car behind 1 , 2 , 3
    # O - MH opens curtain 2
    # contestant picks curtain 1
    from sympy.abc import A , B , C , O
    from sympy import true
    import numpy as np

    p = Piter({A , B , C , O})
    # only one car
    p.addConstraint((A & ~B & ~C) | (~A & B & ~C) | (~A & ~B & C))
    # car is behind 2, Monty Hall won't chose this curtain to open
    p.addConstraint(~(O & B))
    # the chanses of the car being behind curtain 1 , 2 , 3 are the same
    p.addP(A , true , 1.0 / 3.0)
    p.addP(B , true , 1.0 / 3.0)
    p.addP(C , true , 1.0 / 3.0)
    # car is behind 1, contentant picks 1, chance of MH picking 2 or 3 are equal
    p.addP(O , A , 0.5)
    # car is behind 3, contestant picks1, MH must open 2
    p.addP(O , C , 1.0)
    p.finalize()

    for d in p:
        print(d)

    ab = p.getNumpy()

    a = ab[: , :-1]
    b = ab[: , -1]

    x , residuals , rank , s = np.linalg.lstsq(a , b)

    print("The solution obtained using least squares:")
    print("x =" , x)
    print("Sum of probabilities in x:" , np.sum(x) , "\n")
    print("max(abs(A x - b)):" , np.max(np.abs(a @ x - b)))

    num , dem = p.getNumDem(A , O)
    print("probability of car behind curtain 1 (contenstant chose 1, MH showed 2):" , np.sum(num * x) / np.sum(dem * x))
    
    num , dem = p.getNumDem(C , O)
    print("probability of car behind curtain 3 (contenstant chose 1, MH showed 2):" , np.sum(num * x) / np.sum(dem * x))

if __name__ == '__main__':
    main()
