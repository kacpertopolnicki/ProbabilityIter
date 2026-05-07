import sys

sys.path.append('..')
from piter import Piter

def main():
    # sauce : https://bechtel.colorado.edu/~balajir/CVEN5454/lectures/monty.pdf
    # A , B , C - car behind 1 , 2 , 3
    # O - MH opens curtain 2
    # contestant picks curtain 1
    from sympy.abc import A , B , C , O , D , E , F
    from sympy import true
    import numpy as np

    p = Piter({A , B , C , O , D , E , F})
    #p = Piter({A , B , C , O , D})
    # only one car
    p.addConstraint((A & ~B & ~C) | (~A & B & ~C) | (~A & ~B & C))
    # car is behind 2, Monty Hall won't chose this curtain to open
    p.addConstraint(~(O & B))
    # ~O means that curtain 3 is open 
    #p.addConstraint(~(C & (~O)))
    # the chanses of the car being behind curtain 1 , 2 , 3 are the same
    p.addP(A , true , 1.0 / 3.0)
    p.addP(B , true , 1.0 / 3.0)
    p.addP(C , true , 1.0 / 3.0)
    #p.addP(~(C & (~O)) , true , 0.0)
    # car is behind 1, contentant picks 1, chance of MH picking 2 or 3 are equal
    p.addP(O , A , 0.5)
    # car is behind 3, contestant picks1, MH must open 2
    # carefull this is equivalent to adding ~(C & (~O)) constraint
    #p.addP(O , C , 1.0)
    p.addP(O , C , 0.99999)
    p.finalize()

    if False:
        i = 0
        for d in p:
            print(i , d)
            i += 1

        num , dem = p.getNumDem(C & (~O) , true)
        print(",".join(list(map(str , num))))
        print(",".join(list(map(str , dem))))
        num , dem = p.getNumDem(C , O)
        print(",".join(list(map(str , num))))
        print(",".join(list(map(str , dem))))
        num , dem = p.getNumDem(A , O)
        print(",".join(list(map(str , num))))
        print(",".join(list(map(str , dem))))
        ab = p.getNumpy()

        a = ab[: , :-1]
        b = ab[: , -1]

        print(a)
        print(b)

    if True:
        ab = p.getNumpy()

        a = ab[: , :-1]
        b = ab[: , -1]

        x = p.getOptimalSolution(method = "default" , verbose = 1)

        print("The solution fancy method:")
        print("x =" , x)
        print("Sum of probabilities in x:" , np.sum(x) , "\n")
        print("max(abs(A x - b)):" , np.max(np.abs(a @ x - b)))

        num , dem = p.getNumDem(A , O)
        print("probability of car behind curtain 1 (contenstant chose 1, MH showed 2):" , np.sum(num * x) / np.sum(dem * x))
        
        num , dem = p.getNumDem(C , O)
        print("probability of car behind curtain 3 (contenstant chose 1, MH showed 2):" , np.sum(num * x) / np.sum(dem * x))

if __name__ == '__main__':
    main()
