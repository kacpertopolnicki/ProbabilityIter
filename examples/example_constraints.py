###############
# DESCRIPTION #
###############

# This is one of two examples loosely related to the 
# [Sally Clark](https://en.wikipedia.org/wiki/Sally_Clark) case:
# 
# - `example_constraints.py` (this example)
# - `example_no_constraints.py`
# 
# Both describe a hypothetical scenario where two infants are
# found dead (this is denoted in the code as `d`) and the
# mother is suspected of being a murderess (this is denoted in the code as `m`).
# 
# The probability of the mother being a murderess given no additional information
# (the background prevalence of murderers in the population) is assumed to be 
# $0.0001$. The probability of two infant children dying 
# in the same home is assumed to be $0.001$. These numbers are chosen
# arbitrarily to demonstrate how the problem is set up in `Piter`
# and don't reflect the realities of the real criminal case.
# 
# In the first example `example_constraints.py` a constraint is imposed 
# on the problem. It is assumed that the situation where the mother is
# a murderess and the two infants are alive never takes place.
# The second example `example_no_constraints.py` no 
# constraints are imposed.


import sys

sys.path.append('..')
from piter import Piter

def main():
    # d - two dead 
    # m - the mother is a murderess
    from sympy.abc import d , m
    from sympy import true
    import numpy as np

    p = Piter({d , m})
    p.addConstraint(~(~d & m))
    p.addP(m , true , 0.0001)
    p.addP(d , true , 0.001)
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

if __name__ == '__main__':
    main()
