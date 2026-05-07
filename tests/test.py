import sys
import unittest
import logging
import sympy
import os
import numpy as np

sys.path.append('..')
from piter import Piter
from piter import logger

# tollerance for comparing with 0
TOLLERANCE = 10e-12

# tollerance for checking if distrbution us uniform
# this typically is used to compare deviations
# relative to the maximum value
TOLLERANCE_UNIFORM = 0.012

# stopping value
# iterations will stop when the difference in vector components
# is less then the stopping value
STOP = 0.00001

class TestPiter(unittest.TestCase):
    def test_optimized_solution(self):
        from sympy.abc import d , m , a , b , c , e , f , g , h
        from sympy import true

        logger.debug("starting test_optimized_solution")
       
        p = Piter({d , m , a , b , e , f , g , h})
        p.addP(e & ~a & ~b & ~d & ~f & ~m & g & h, true , 0.1)
        p.addP(b & f & m & ~a & ~d & ~e & g & h , true , 0.1)
        p.finalize()

        rest = 0.8 / (len(p) - 2)

        sol = p.getOptimalSolution(verbose = 1 , epochs = 3000 , stop = STOP)

        maxabsdif = 0.0
        i = 0
        for expr in p:
            if expr == e & ~a & ~b & ~d & ~f & ~m & g & h:
                self.assertTrue(np.abs(sol[i] - 0.1) < TOLLERANCE)
            elif expr == b & f & m & ~a & ~d & ~e & g & h:
                self.assertTrue(np.abs(sol[i] - 0.1) < TOLLERANCE)
            else:
                self.assertTrue(np.abs(sol[i] - rest) / 0.1 < TOLLERANCE_UNIFORM , msg = "Found difference from uniform " + str(np.abs(sol[i] - rest) / 0.1))
            i += 1

        #print(maxabsdif)

        logger.debug("finished test_optimized_solution")

    def test_optimized_solution_MH(self):
        # sauce : https://bechtel.colorado.edu/~balajir/CVEN5454/lectures/monty.pdf
        from sympy.abc import A , B , C , O , D , E , F
        from sympy import true
        import numpy as np

        p = Piter({A , B , C , O , D , E , F})
        p.addConstraint((A & ~B & ~C) | (~A & B & ~C) | (~A & ~B & C))
        p.addConstraint(~(O & B))
        p.addConstraint(~(C & (~O))) # test without this constraint after new method for finding positive soluition
        p.addP(A , true , 1.0 / 3.0)
        p.addP(B , true , 1.0 / 3.0)
        p.addP(C , true , 1.0 / 3.0)
        p.addP(O , A , 0.5)
        p.addP(O , C , 1.0)
        p.finalize()

        ab = p.getNumpy()

        a = ab[: , :-1]
        b = ab[: , -1]

        x = p.getOptimalSolution()

        num , dem = p.getNumDem(A , O)
        dont_switch = np.sum(num * x) / np.sum(dem * x)

        self.assertTrue(np.abs(dont_switch - 1.0 / 3.0) < TOLLERANCE)

        num , dem = p.getNumDem(C , O)
        switch = np.sum(num * x) / np.sum(dem * x)
        
        self.assertTrue(np.abs(switch - 2.0 / 3.0) < TOLLERANCE)


    def test_unique_solution_MH(self):
        # sauce : https://bechtel.colorado.edu/~balajir/CVEN5454/lectures/monty.pdf
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

        self.assertTrue(np.abs(dont_switch - 1.0 / 3.0) < TOLLERANCE)

        num , dem = p.getNumDem(C , O)
        switch = np.sum(num * x) / np.sum(dem * x)
        
        self.assertTrue(np.abs(switch - 2.0 / 3.0) < TOLLERANCE)

    def test_unique_solution_SC(self):
        from sympy.abc import d , m
        from sympy import true

        logger.debug("starting test_unique_solution")

        p = Piter({d , m})
        p.addP(m , true , 0.0001)
        p.addP(d , true , 0.001)
        p.addP(d , m , 1.0)
        p.finalize()

        ab = p.getNumpy()
        a = ab[: , :-1]
        b = ab[: , -1]
        x = np.linalg.solve(a , b)

        num , dem = p.getNumDem(m , d)
        p_md_1 = np.sum(num * x) / np.sum(dem * x) 

        num , dem = p.getNumDem(~m , d)
        p_mbard_1 = np.sum(num * x) / np.sum(dem * x) 

        self.assertTrue(np.abs(p_md_1 - 0.1) < TOLLERANCE , msg = "P(m|d) : " + str(p_md_1)) 
        self.assertTrue(np.abs(p_md_1 + p_mbard_1 - 1.0) < TOLLERANCE , msg = "P(m|d) + P(~m|d) : " + str(p_md_1 + p_mbard_1))
        
        x_1 = p.getOptimalSolution()

        num , dem = p.getNumDem(m , d)
        p_md_2 = np.sum(num * x_1) / np.sum(dem * x_1) 

        num , dem = p.getNumDem(~m , d)
        p_mbard_2 = np.sum(num * x_1) / np.sum(dem * x_1) 

        self.assertTrue(np.abs(p_md_2 - p_md_1) < TOLLERANCE , msg = "P(m|d) : " + str(p_md_2))
        self.assertTrue(np.abs(p_mbard_2 - p_mbard_1) < TOLLERANCE , msg = "P(~m|d) : " + str(p_md_2))

        p = Piter({d , m})
        p.addConstraint(~(~d & m))
        p.addP(m , true , 0.0001)
        p.addP(d , true , 0.001)
        p.finalize()

        ab = p.getNumpy()

        a = ab[: , :-1]
        b = ab[: , -1]
        x = np.linalg.solve(a , b)

        num , dem = p.getNumDem(m , d)
        p_md_3 = np.sum(num * x) / np.sum(dem * x)
        
        num , dem = p.getNumDem(~m , d)
        p_mbard_3 = np.sum(num * x) / np.sum(dem * x)

        self.assertTrue(np.abs(p_md_3 - 0.1) < TOLLERANCE , msg = "P(m|d) : " + str(p_md_1)) 
        self.assertTrue(np.abs(p_md_3 + p_mbard_3 - 1.0) < TOLLERANCE , msg = "P(m|d) + P(~m|d) : " + str(p_md_1 + p_mbard_1))

        x_1 = p.getOptimalSolution()

        num , dem = p.getNumDem(m , d)
        p_md_4 = np.sum(num * x_1) / np.sum(dem * x_1) 

        num , dem = p.getNumDem(~m , d)
        p_mbard_4 = np.sum(num * x_1) / np.sum(dem * x_1) 
 
        self.assertTrue(np.abs(p_md_4 - p_md_3) < TOLLERANCE , msg = "P(m|d) : " + str(p_md_2))
        self.assertTrue(np.abs(p_mbard_4 - p_mbard_3) < TOLLERANCE , msg = "P(~m|d) : " + str(p_md_2))

        logger.debug("finished test_unique_solution")

    def test_logic(self):

        from sympy.abc import f , g , h , i , j

        logger.debug("starting test_logic")

        smpl = [(True , True) , (True , False) , (False , True) , (False , False)]
        
        for s1 , s2 in smpl:
            p = Piter({f , g , h})
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(g & h) , simplify = s1)
            p.addConstraint(~(h & f) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & ~h, ~f & g & ~h, ~f & ~g & h, ~f & ~g & ~h])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))
            
            p = Piter({f , g , h})
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(g & h) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & h, f & ~g & ~h, ~f & g & ~h, ~f & ~g & h, ~f & ~g & ~h])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))
            
            p = Piter({f , g , h})
            p.addConstraint(~(f & g) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & h, f & ~g & ~h, ~f & g & h, ~f & g & ~h, ~f & ~g & h, ~f & ~g & ~h])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h})
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & g & h, f & g & ~h, f & ~g & h, f & ~g & ~h, ~f & g & h, ~f & g & ~h, ~f & ~g & h, ~f & ~g & ~h])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h})
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(f & h) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & ~h, ~f & g & h, ~f & g & ~h, ~f & ~g & h, ~f & ~g & ~h])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))
            
            p = Piter({f , g , h , i , j})
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(f & h) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & ~h & i & j,
             f & ~g & ~h & i & ~j,
             f & ~g & ~h & ~i & j,
             f & ~g & ~h & ~i & ~j,
             ~f & g & h & i & j,
             ~f & g & h & i & ~j,
             ~f & g & h & ~i & j,
             ~f & g & h & ~i & ~j,
             ~f & g & ~h & i & j,
             ~f & g & ~h & i & ~j,
             ~f & g & ~h & ~i & j,
             ~f & g & ~h & ~i & ~j,
             ~f & ~g & h & i & j,
             ~f & ~g & h & i & ~j,
             ~f & ~g & h & ~i & j,
             ~f & ~g & h & ~i & ~j,
             ~f & ~g & ~h & i & j,
             ~f & ~g & ~h & i & ~j,
             ~f & ~g & ~h & ~i & j,
             ~f & ~g & ~h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))
            
            p = Piter({f , g , h , i , j})
            p.addConstraint((f & g & i) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & g & h & i & j,
             f & g & h & i & ~j,
             f & g & ~h & i & j,
             f & g & ~h & i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h , i , j})
            p.addConstraint(f >> i , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & g & h & i & j,
             f & g & h & i & ~j,
             f & g & ~h & i & j,
             f & g & ~h & i & ~j,
             f & ~g & h & i & j,
             f & ~g & h & i & ~j,
             f & ~g & ~h & i & j,
             f & ~g & ~h & i & ~j,
             ~f & g & h & i & j,
             ~f & g & h & i & ~j,
             ~f & g & h & ~i & j,
             ~f & g & h & ~i & ~j,
             ~f & g & ~h & i & j,
             ~f & g & ~h & i & ~j,
             ~f & g & ~h & ~i & j,
             ~f & g & ~h & ~i & ~j,
             ~f & ~g & h & i & j,
             ~f & ~g & h & i & ~j,
             ~f & ~g & h & ~i & j,
             ~f & ~g & h & ~i & ~j,
             ~f & ~g & ~h & i & j,
             ~f & ~g & ~h & i & ~j,
             ~f & ~g & ~h & ~i & j,
             ~f & ~g & ~h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h , i , j})
            p.addConstraint((f >> i) & (~(f & g)) & (~(g & j)) & (h >> g) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & ~h & i & j,
             f & ~g & ~h & i & ~j,
             ~f & g & h & i & ~j,
             ~f & g & h & ~i & ~j,
             ~f & g & ~h & i & ~j,
             ~f & g & ~h & ~i & ~j,
             ~f & ~g & ~h & i & j,
             ~f & ~g & ~h & i & ~j,
             ~f & ~g & ~h & ~i & j,
             ~f & ~g & ~h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h , i , j})
            p.addConstraint((f >> i) , simplify = s1)
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(g & j) , simplify = s1)
            p.addConstraint(h >> g , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & ~h & i & j,
             f & ~g & ~h & i & ~j,
             ~f & g & h & i & ~j,
             ~f & g & h & ~i & ~j,
             ~f & g & ~h & i & ~j,
             ~f & g & ~h & ~i & ~j,
             ~f & ~g & ~h & i & j,
             ~f & ~g & ~h & i & ~j,
             ~f & ~g & ~h & ~i & j,
             ~f & ~g & ~h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h , i , j})
            p.addConstraint((f >> i) , simplify = s1)
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(g & j) , simplify = s1)
            p.addConstraint(~(h >> g) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & h & i & j,
             f & ~g & h & i & ~j,
             ~f & ~g & h & i & j,
             ~f & ~g & h & i & ~j,
             ~f & ~g & h & ~i & j,
             ~f & ~g & h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))
            
            p = Piter({f , g , h , i , j})
            p.addConstraint((f >> i) | ((~(f & g)) & (~(g & j)) & ~(h >> g)) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & g & h & i & j,
             f & g & h & i & ~j,
             f & g & ~h & i & j,
             f & g & ~h & i & ~j,
             f & ~g & h & i & j,
             f & ~g & h & i & ~j,
             f & ~g & h & ~i & j,
             f & ~g & h & ~i & ~j,
             f & ~g & ~h & i & j,
             f & ~g & ~h & i & ~j,
             ~f & g & h & i & j,
             ~f & g & h & i & ~j,
             ~f & g & h & ~i & j,
             ~f & g & h & ~i & ~j,
             ~f & g & ~h & i & j,
             ~f & g & ~h & i & ~j,
             ~f & g & ~h & ~i & j,
             ~f & g & ~h & ~i & ~j,
             ~f & ~g & h & i & j,
             ~f & ~g & h & i & ~j,
             ~f & ~g & h & ~i & j,
             ~f & ~g & h & ~i & ~j,
             ~f & ~g & ~h & i & j,
             ~f & ~g & ~h & i & ~j,
             ~f & ~g & ~h & ~i & j,
             ~f & ~g & ~h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h , i , j})
            p.addConstraint(~(f >> i) , simplify = s1)
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(g & j) , simplify = s1)
            p.addConstraint(~(g & f) , simplify = s1)
            p.addConstraint(~(h >> g) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & ~g & h & ~i & j,
             f & ~g & h & ~i & ~j])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h})
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set([f & g & h,
             f & g & ~h,
             f & ~g & h,
             f & ~g & ~h,
             ~f & g & h,
             ~f & g & ~h,
             ~f & ~g & h,
             ~f & ~g & ~h])
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h})
            p.addConstraint(sympy.false , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set()
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            p = Piter({f , g , h , i , j})
            p.addConstraint(~(f >> i) , simplify = s1)
            p.addConstraint(~(f & g) , simplify = s1)
            p.addConstraint(~(g & j) , simplify = s1)
            p.addConstraint((g & f) , simplify = s1)
            p.addConstraint((h >> g) , simplify = s1)
            p.finalize(simplifydnf = s2)
            a = set(p)
            b = set()
            self.assertEqual(a , b , msg = "s1 , s2 : " + str(s1) + " , " + str(s2))

            logger.debug("finished test_logic")

if __name__ == "__main__" :
    unittest.main()
