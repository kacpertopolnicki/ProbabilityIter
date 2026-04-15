import sympy
import numpy as np
import torch
import scipy

import os

from .piterexception import PiterException
from .piterlog import logger


# floating point type for numpy
NP_DTYPE = np.float64

# floating point type for torch
TR_DTYPE = torch.float64

# optimizer
OPTIMIZER = torch.optim.Adam

# learning rate
LEARNING_RATE = 0.01

class Piter:
    """
    Calculations related to probability.
    The class is also an iterator over logical propositions.

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
        Keyword arguments : 
            symbols (set) : set of sympy symbols for logical propositions. 
                Further symbols are added when calling added when calling addConstraint.

        Raises : 
            PiterException
        """
        if not isinstance(symbols , set):
            raise PiterException("Expecting set in Piter.__init__ symbols argument.")
        for s in symbols:
            if not isinstance(s , sympy.core.symbol.Symbol):
                raise PiterException("Expecting sympy symbol set in Piter.__init__ symbols argument.")
        self.__symbols = set()
        self.__symbols.update(symbols)
        self.__symbolsTuple = tuple()
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
        where x represents previous knowlege.

        Parameters:
            a , b : Sympy logical expressions.
        
        Raises:
            PiterException
        """
        if not Piter.__isLogical(a):
            raise PiterException("Expecting logical expression in Piter.addP.")
        if not Piter.__isLogical(b):
            raise PiterException("Expecting logical expression in Piter.addP.")
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
        are returned by the iterator and used to in creating the set of linear equations.

        Parameters:
            c : Sympy logical expression representing the constraint, if new symbols appear in c 
                they will be added to selfs symbols list.

        Keyword Arguments:
            simplify (bool) : Default False, if True sympy.logic.simplify_logic will be applied to constraints.

        Raises:
            PiterException
        """
        if not Piter.__isLogical(c):
            raise PiterException("Expecting logical expression in Piter.addConstraint.")
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
            raise PiterException("Expecting python logical expression in dnf form in first argument to dnfToTuple.")
   
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
            m.p = a
        determines the probability values.

        Raises:
            PiterException
        """
        if not self.__initialized:
            raise PiterException("Attempting to get a numpy array from an uninitialized Piter object.")
        return np.copy(self.__m)

    def getOptimalSolution(self , epochs = 2000 , stop = None , verbose = None):
        """
        Attempts to find a solution that maximizes entropy.

        Keyword arguments:
            epochs (int): Maximum number of epochs for optimization.
            stop (float): stop value
            varbose (bool or int): If int, the value determines verbosity (epochs between printing). 

        Returns:
            Vector of probabilities that maximize the entropy.

        Raises: 
            PiterException
        """
        if not self.__initialized:
            raise PiterException("Attempting to get a numpy array from an uninitialized Piter object.")

        # tollerance for comparing with 0
        TOLLERANCE = 10e-16

        # margin for calculating positive vector range
        EPSILON = 0.000001
 
        ab = self.getNumpy()

        logger.debug("ab.shape : " + str(ab.shape))

        # solving (a|-b).y == m.y == 0
        # columns of ns contain the vectors in the null space basis of m

        m = np.copy(ab)
        m[: , -1] *= -1.0
        ns = scipy.linalg.null_space(m)
        logger.debug("ns.shape : " + str(ns.shape))
        if ns.shape[1] == 1:
            logger.debug("Only one null space vector, returning solution.")
            sol = (ns / ns[-1])[:-1 , 0]
            if not np.all(sol >= -TOLLERANCE):
                raise PiterException("Could not find all positive solution.")
            return sol

        # calculating orthogonal complement (see sauce https://math.stackexchange.com/questions/5128405/transformation-to-basis-with-all-positive-vectors)
        # columns in sn contain the vectors in the complement

        sn = scipy.linalg.null_space(ns.T)
        logger.debug("sn.shape : " + str(sn.shape))

        # linear optimization (see sauce https://math.stackexchange.com/questions/5128405/transformation-to-basis-with-all-positive-vectors)
        # vv is the all positive solution (one dimensional vector) normalized so that the last coordinate is 1

        c = np.ones(sn.shape[0] , dtype = NP_DTYPE)
        aub = -np.eye(sn.shape[0] , dtype = NP_DTYPE)
        bub = -np.ones(sn.shape[0] , dtype = NP_DTYPE)
        aeq = sn.T
        beq = np.zeros(sn.shape[1] , dtype = NP_DTYPE)
        v = scipy.optimize.linprog(c , A_ub = aub , b_ub = bub , A_eq = aeq , b_eq = beq)
        if not v.success:
            raise PiterException("Failed to find positive vector.\n" + str(v))
        vv = v.x
        vv /= vv[-1]
        logger.debug("vv.shape : " + str(vv.shape))

        # optimizing entropy

        import torch
        
        def getMinMax(p , v , epsilon = EPSILON , maxrange = 10000000.):
            """
            Args:
                p : Vector with all positive coordinates.
                v : Vector with all positive coordinates.
                epsilon (optional) : Tollerance.

            Returns: 
                (alpha_0 , alpha_1)
                If alpha_0 < alpha < alpha_1 then
                all components of the vector
                  r = p + alpha v
                are positive.
            """
            gt0 = v >= 0
            valpha = (-p[gt0] / v[gt0])
            minalpha = -maxrange
            if valpha.numel() > 0:
                minalpha = valpha.max()
            lt0 = v < 0
            vvalpha = (-p[lt0] / v[lt0])
            maxalpha = maxrange
            if vvalpha.numel() > 0:
                maxalpha = vvalpha.min()
            return (minalpha + epsilon , maxalpha - epsilon)

        def vecFromParam(par , start , vecs):
            if par.shape[0] != vecs.shape[1]:
                raise PiterException("Number of parameters does not match the number of vectors.")
            # normalize all parameters to 0 ... 1 range
            parn = 0.5 * (torch.sin(par) + 1.0)
            vvv = start
            for i in range(par.shape[0]):
                minalpha , maxalpha = getMinMax(vvv , vecs[: , i])
                vvv = vvv + (minalpha + parn[i] * (maxalpha - minalpha)) * vecs[: , i]
            return vvv

        nst = torch.tensor(ns , dtype = TR_DTYPE)
        vvt = torch.tensor(vv , dtype = TR_DTYPE)
        par = torch.zeros(ns.shape[1] , dtype = TR_DTYPE , requires_grad = True)
        par_p = torch.tensor(1000.0 , dtype = TR_DTYPE) 
        parameters = [par , par_p]
        opt = OPTIMIZER(parameters , lr = LEARNING_RATE)

        new = None
        prevnorm = None
        newnorm = None
        for epoch in range(epochs):
            if newnorm is not None:
                prevnorm = newnorm.clone().detach()
            new = vecFromParam(par , par_p * par_p * vvt, nst)
            newnorm = new / new[-1]
            if newnorm is not None and prevnorm is not None:
                if stop is not None and torch.max(torch.abs((newnorm[:-1] - prevnorm[:-1]))).item() < stop:
                    break
            loss = (newnorm[:-1] * torch.log(newnorm[:-1])).sum() 
            opt.zero_grad()
            loss.backward()
            opt.step()
            if isinstance(verbose , int) and epoch % verbose == 0:
                logger.debug(str(epoch) + " " + str(epochs) + " " + str(-loss.item()))

        sol = newnorm.clone().detach().numpy()

        return sol[:-1]

    def getNumDem(self , a , b):
        """
        Used to calculate any probability P(a | b x) given 
        a vector of probabilities.

        Args:
            a , b (bool): Logical expressions.

        Returns:
            Tuple (num , dem). If x is the vector of probabilities
            then np.sum(num * x) / np.sum(dem * x) is the probability
            P(a | b x).
            
        """
        if not self.__initialized:
            raise PiterException("Attempting to get numpy arrays from an uninitialized Piter object.")
        if not Piter.__isLogical(a):
            raise PiterException("Expecting logical expression in Piter.getNumDem.")
        if not Piter.__isLogical(b):
            raise PiterException("Expecting logical expression in Piter.getNumDem.")
        if not Piter.__getSymbols(a).issubset(self.__symbols):
            raise PiterException("New symbols introduced in a.")
        if not Piter.__getSymbols(b).issubset(self.__symbols):
            raise PiterException("New symbols introduced in b.")
        num = np.zeros((self.__m.shape[1] - 1 , ) , dtype = NP_DTYPE)
        dem = np.zeros((self.__m.shape[1] - 1 , ) , dtype = NP_DTYPE)
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
        All public methods except `addP` and `addConstraint` require that the object
        is finalized.

        Keyword parameters:
            simplify (bool) : Default False. If True sympy.logic.to_dnf(... , simplify = True) will be used
                to convert constraints to DNF form. Using True may impact speed.
        """
        self.__symbolsTuple = list(self.__symbols)
        from functools import cmp_to_key
        self.__symbolsTuple.sort(key = cmp_to_key(lambda x , y : x.compare(y)))
        self.__symbolsTuple = tuple(self.__symbolsTuple)
        self.__constraintsDnf = sympy.logic.to_dnf(sympy.And(*self.__constraints) , simplify = simplifydnf)
        dnf = self.__dnfToTupleSet(self.__constraintsDnf)
        self.__constraintsTupleSet = set()
        
        # remove elements from dnf that are less general
        # for instance from {(0 , 0 , 1) , (1 , 1 , 1)}
        # remove (1 , 1 , 1)
        # TODO : this is wrong, or is it, this is ok
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
        for t in self.__constraintsTupleSet:
            zeroPositions = []
            for position , item in enumerate(t):
                if item == 0:
                    zeroPositions.append(position)
            r = [x for x in t]
            for i in range(2**len(zeroPositions)):
                for j in range(len(zeroPositions)):
                    r[zeroPositions[j]] = 2 * ((i // 2**j) % 2) - 1
                rt = tuple(r)
                if rt in baseElements:
                    self.__rejections += 1
                baseElements.add(rt)
        self.__baseElements = list(baseElements)       

        def sortfun(tp):
            val = 0
            mul = 1
            for x in reversed(tp):
                val += ((x + 1) // 2) * mul
                mul *= 2
            #print(tp , val , self.__symbols , self.__symbolsTuple)
            return val

        self.__baseElements.sort(key = sortfun)

        self.__m = np.zeros((len(self.__probabilities) + 1 , len(self.__baseElements) + 1) , dtype = NP_DTYPE)
        self.__m[0 , :] = 1.0 # is this necessary?

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


