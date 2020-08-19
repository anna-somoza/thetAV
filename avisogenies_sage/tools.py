from collections import UserList
from sage.rings.all import ZZ, Integer
from sage.arith.functions import lcm
integer_types = (int, Integer)

def TowerOfField(L):
    F = L[0];
    for elem in L[1:]:
        deg1 = F.degree()
        deg2 = elem.degree()
        deg = lcm(deg1, deg2) / deg1
        F = F.extend(deg)
    return F;

def rangeS(n, S):
    for x in range(n):
        if x in S:
            continue
        yield x
        
class ThetaStructure(UserList):
    """
    A list that can be accessed both by elements in Zmod(l_1)^g x ... x Zmod(l_n)^g
    or the corresponding integer.


    TODO:
    - Could generalize by accepting g a tuple of the same length as level if needed.
    """
    def __init__(self, data=None, level=2, g=None):
        self.level = level
        if isinstance(level, integer_types):
            self.n = 1
            if data == None:
                if g == None:
                    raise ValueError("You have to indicate the size of the modules")
                self.data = [None]*(level**g)
            else:
                self.data = data
        else:
            if g == None:
                raise ValueError("You have to indicate the size of the modules")
            if isinstance(g, integer_types):
                self.n = len(level)
                self.terms = [1]
                for l in level:
                    self.terms.append(self.terms[-1]*l**g)
                if data == None:
                    self.data = [None]*self.terms[-1]
                else:
                    self.data = data
            else:
                raise NotImplementedError
        
    def __setitem__(self, key, value):
        if isinstance(key, integer_types):
            self.data[key] = value
        else:
            self.data[self.idx(key)] = value

    def __getitem__(self, key):
        if isinstance(key, integer_types):
            return self.data[key]
        return self.data[self.idx(key)]

    def idx(self, key):
        if self.n == 1:
            return ZZ(list(key), self.level)
        idx = 0
        for term, l, coefficient in zip(key, self.level, self.terms):
            if isinstance(term, integer_types):
                idx += coefficient*term
            else:
                idx += coefficient*ZZ(list(term), l)
        return idx
