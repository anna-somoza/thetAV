from collections import UserList
from sage.rings.all import ZZ, Integer
from sage.arith.functions import lcm
integer_types = (int, Integer)

def TowerOfField(L):
    F = L[0]
    for elem in L[1:]:
        deg1 = F.degree()
        deg2 = elem.degree()
        deg = lcm(deg1, deg2) // deg1
        F = F.extension(ZZ(deg))
    return F;

def rangeS(n, S):
    for x in range(n):
        if x in S:
            continue
        yield x
