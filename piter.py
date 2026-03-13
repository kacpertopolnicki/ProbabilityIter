import sympy
import numpy as np
import torch

class PiterException(Exception):
    def __init__(self , message):
        self.__message = message
    def __str__(self):
        return self.__message

class Piter:
    """
    An iterator over logical propositions.
    For any two returned propositions:
      a , b
    the following property is met:
      a and b is false.

    Examples:
        If f , g , h are logical propositions
        that determine if an element belongs
        to set F , G , H respecively, then 
        the following code will return the
        only possible logical statements in
        this system:

        > from sympy.abc import f , g , h
        > from piter import *
        > p = Piter({f , g , h})
        > p.addConstraint(~(f & g))
        > p.addConstraint(~(g & h))
        > p.addConstraint(~(h & f))
        > f.finalize()
        > for s in p:
        >     print(p)

        ~f & ~g & ~h
        g & ~f & ~h
        f & ~g & ~h
        h & ~f & ~g
    """
    def __init__(self , symbols = set()):
        """
        The constructor for Piter.

        Parameters : 
            symbols (set) : set of sympy symbols for logical propositions. 
                Further symbols are added when calling added when calling addConstraint.

        Raises : 
            ValueError
        """
        if not isinstance(symbols , set):
            raise ValueError("Expecting set in Piter.__init__ symbols argument.")
        for s in symbols:
            if not isinstance(s , sympy.core.symbol.Symbol):
                raise ValueError("Expecting sympy symbol set in Piter.__init__ symbols argument.")
        self.__symbols = set()
        self.__symbols.update(symbols)
        self.__symbolsTuple = set()
        self.__constraints = set()
        self.__constraintsDnf = None
        self.__constraintsTupleSet = None
        self.__rejections = None # for denuging, ideally this is 0
        self.__initialized = False
        self.__probabilities = []
        self.__m = None

    def addP(self , a , b , alpha):
        """
        Add probability value 
            P(a | b x) == alpha
        where x is the previous knowlege.

        Parameters:
            a , b : Sympy logical expressions.
        """
        if not Piter.__isLogical(a):
            raise ValueError("Expecting logical expression in Piter.addP.")
        if not Piter.__isLogical(b):
            raise ValueError("Expecting logical expression in Piter.addP.")
        if not self.__initialized:
            self.__probabilities.append([a , b , alpha])
            symbolsIna = Piter.__getSymbols(a)
            self.__symbols.update(symbolsIna)
            symbolsInb = Piter.__getSymbols(b)
            self.__symbols.update(symbolsInb)
        else:
            raise PiterException("Attempting to add probability value to finalized Piter object.")


    def addConstraint(self , c , simplify = False):
        """
        Add constraint. Only propositions that are consistent with all constraints
        are returned by the iterator.

        Parameters:
            c : Sympy logical expression representing the constraint, if new symbols appear in c 
                they will be added to selfs symbols list.

        Keyword Arguments:
            simplify (bool) : Default False, if True sympy.logic.simplify_logic will be applied to constraints.

        Raises:
            ValueError , PiterException
        """
        if not Piter.__isLogical(c):
            raise ValueError("Expecting logical expression in Piter.addConstraint.")
        if not self.__initialized:
            cc = c
            if simplify:
                cc = sympy.logic.simplify_logic(c)
            self.__constraints.add(cc)
            symbolsInC = Piter.__getSymbols(cc)
            self.__symbols.update(symbolsInC)
        else:
            raise PiterException("Attempting to add constraint to finalized Piter object.")
    def __repr__(self):
        return ("Finished " if self.__initialized else "Unfinished ") + "Piter with " + str(len(self.__symbols)) + " symbols and " + str(len(self.__constraints)) + " constraints."
    def __str__(self):
        result = self.__repr__()
        result += "\nSymbols:\n"
        result += str(self.__symbols)
        result += "\nConstraints:\n"
        for c in self.__constraints:
            result += str(c) + "\n"
        if(self.__initialized):
            result += "DNF of constraints: \n"
            result += str(self.__constraintsDnf) + "\n"
            result += "Number of base elements: \n"
            result += str(len(self.__baseElements))
        return result

    def __getSymbols(expr):
        symbols = set()
        for arg in sympy.preorder_traversal(expr):
            if isinstance(arg , sympy.core.symbol.Symbol):
                symbols.add(arg)
        return symbols

    def __isLogical(expr):
        for arg in sympy.preorder_traversal(expr):
            if not (
                    isinstance(arg , sympy.core.symbol.Symbol) or
                    isinstance(arg , sympy.Not) or
                    isinstance(arg , sympy.And) or
                    isinstance(arg , sympy.Or) or
                    isinstance(arg , sympy.Implies) or
                    isinstance(arg , sympy.logic.boolalg.BooleanTrue) or
                    isinstance(arg , sympy.logic.boolalg.BooleanFalse)
                    ):
                return False
        return True

    def __dnfToTupleSet(self , dnf):
        def tupleGet(e):
            #print("e : " , e)
            # if symbols are a , b , c , d then
            #  a   b   c    d
            # (1 , 0 , 1 , -1) - a & c & ~d
            l = [0 for _ in range(len(self.__symbolsTuple))]
            args = e.args
            if isinstance(e , sympy.Not) or isinstance(e , sympy.core.symbol.Symbol):
                args = [e]
            for a in args:
                for i in range(len(self.__symbolsTuple)):
                    if a == self.__symbolsTuple[i]:
                        if(l[i] != 0):
                            return None
                        l[i] = 1
                    elif a == ~self.__symbolsTuple[i]:
                        if(l[i] != 0):
                            return None
                        l[i] = -1
            #print("r : " , tuple(l) , self.__symbolsTuple)
            return tuple(l)
        if isinstance(dnf , sympy.logic.boolalg.BooleanTrue):
            # {(0 , 0 , 0 , ...)} - True
            s = set()
            s.add(tuple(0 for _ in range(len(self.__symbols))))
            if None in s:
                s.remove(None)
            return s
        elif isinstance(dnf , sympy.logic.boolalg.BooleanFalse):
            # {} - False
            return set()
        elif isinstance(dnf , sympy.core.symbol.Symbol) or isinstance(dnf , sympy.And):
            s = set()
            s.add(tupleGet(dnf))
            if None in s:
                s.remove(None)
            return s
        elif isinstance(dnf , sympy.Or):
            s = set(map(tupleGet , dnf.args))
            if None in s:
                s.remove(None)
            return s
        else:
            raise ValueError("Expecting python logical expression in dnf form in first argument to dnfToTuple.")
   
    def __toSympy(self , t):
        ts = []
        for i in range(len(t)):
            if t[i] == 1:
                ts.append(self.__symbolsTuple[i])
            elif t[i] == -1:
                ts.append(sympy.Not(self.__symbolsTuple[i]))
            else:
                raise PiterException("Something is very wrong, values should be -1 or 1.")
        return sympy.And(*ts)

    def __iter__(self):
        if not self.__initialized:
            raise PiterException("Attempting get iterator from a uninitialized Piter object.")
        return map(self.__toSympy , self.__baseElements)
    
    def __len__(self):
        if not self.__initialized:
            raise PiterException("Attempting get length from a uninitialized Piter object.")
        return len(self.__baseElements)
    
    def getNumpy(self):
        """
        Returns numpy array representing the joint matrix
            (m|a) = ma
        such that if
            base
        is a list of probabilities generated for this object (for example [x for x in self]) and 
            p
        is a vector of probabilities
            p[0] = P(base[0] | X)
            p[1] = P(base[1] | X)
            ...
        then
            m.p = v
        determines the probability values.
        """
        if not self.__initialized:
            raise PiterException("Attempting to get a numpy array from an uninitialized Piter object.")
        return np.copy(self.__m)

    def getNumDem(self , a , b):
        if not self.__initialized:
            raise PiterException("Attempting to get numpy arrays from an uninitialized Piter object.")
        if not Piter.__isLogical(a):
            raise ValueError("Expecting logical expression in Piter.getNumDem.")
        if not Piter.__isLogical(b):
            raise ValueError("Expecting logical expression in Piter.getNumDem.")
        num = np.zeros((self.__m.shape[1] - 1 , ) , dtype = np.float64)
        dem = np.zeros((self.__m.shape[1] - 1 , ) , dtype = np.float64)
        for idx , x in enumerate(self.__baseElements):
            s = self.__toSympy(x)
            if sympy.logic.inference.satisfiable(a & b & s) is not False:
                num[idx] = 1.0
            if sympy.logic.inference.satisfiable(b & s) is not False:
                dem[idx] = 1.0
        return (num , dem)
    
    def finalize(self , simplifydnf = False):
        """
        Finalize self object. The iterator can be used only if this method is used.

        Keyword parameters:
            simplify (bool) : Default False. If True sympy.logic.to_dnf(... , simplify = True) will be used
                to convert constraints to DNF form. Using True may impact speed.
        """
        #print("finalize")
        self.__symbolsTuple = tuple(self.__symbols)
        #def toMathematica(x):
        #    return str(x).replace("&" , "&&").replace("|" , "||").replace("~" , "!")
        self.__constraintsDnf = sympy.logic.to_dnf(sympy.And(*self.__constraints) , simplify = simplifydnf)
        #print("self.__constraintsDnf" , toMathematica(self.__constraintsDnf))
        dnf = self.__dnfToTupleSet(self.__constraintsDnf)
        self.__constraintsTupleSet = set()
        #self.__constraintsTupleSet = self.__dnfToTupleSet(self.__constraintsDnf)
        # remove elements from dnf that are less general
        # for instance from {(0 , 0 , 1) , (1 , 1 , 1)}
        # remove (1 , 1 , 1)
        # TODO : this is wrong, or is it
        for c1 in dnf:
            addToNew = True
            for c2 in dnf:
                if not c1 == c2:
                    c2MoreGeneral = True
                    for i in range(len(self.__symbolsTuple)):
                        c2MoreGeneral = c2MoreGeneral and (c2[i] == c1[i] or c2[i] == 0)
                    addToNew = addToNew and (not c2MoreGeneral)
            if addToNew:
                self.__constraintsTupleSet.add(c1)
        # iterate over only the conjunctions in the dnf
        # create a set of unique elements then
        # then turn this into a list
        self.__rejections = 0 
        baseElements = set()
        #print(self.__constraintsTupleSet)
        for t in self.__constraintsTupleSet:
            #print("t : " , t , self.__symbolsTuple)
            zeroPositions = []
            for position , item in enumerate(t):
                if item == 0:
                    zeroPositions.append(position)
            r = [x for x in t]
            for i in range(2**len(zeroPositions)):
                #print("  i : " , i)
                for j in range(len(zeroPositions)):
                    r[zeroPositions[j]] = 2 * ((i // 2**j) % 2) - 1
                rt = tuple(r)
                if rt in baseElements:
                    self.__rejections += 1
                #else:
                    #print("  toSympy(rt) : " , toSympy(rt))
                    #print("  satisfiable : " , sympy.logic.satisfiable(self.__constraintsDnf & toSympy(rt)))
                #if sympy.logic.satisfiable(self.__constraintsDnf & toSympy(rt)) is not False:
                    #baseElements.add(rt)
                baseElements.add(rt)
        self.__baseElements = list(baseElements)       

        self.__m = np.zeros((len(self.__probabilities) + 1 , len(self.__baseElements) + 1) , dtype = np.float64)
        self.__m[0 , :] = 1.0

        row = 1
        for a , b , alpha in self.__probabilities:
            if b == sympy.true:
                for idx , x in enumerate(self.__baseElements):
                    s = self.__toSympy(x)
                    if sympy.logic.inference.satisfiable(a & s) is not False:
                        self.__m[row , idx] += 1.0
                self.__m[row , -1] = alpha
            else:
                for idx , x in enumerate(self.__baseElements):
                    s = self.__toSympy(x)
                    if sympy.logic.inference.satisfiable(b & s) is not False:
                        self.__m[row , idx] += alpha
                    if sympy.logic.inference.satisfiable(a & b & s) is not False:
                        self.__m[row , idx] -= 1.0
                self.__m[row , -1] = 0.0
            row += 1

        self.__initialized = True

import unittest

class TestPiter(unittest.TestCase):
    def test_all(self):

        from sympy.abc import f , g , h , i , j

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
if __name__ == "__main__" :
    unittest.main()

# TODO
