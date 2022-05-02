"""
Morphism functionalities.


AUTHORS:

- Anna Somoza (2021-22): initial implementation

"""


# ****************************************************************************
#             Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#    Distributed under the terms of the GNU General Public License (GPL)
#    as published by the Free Software Foundation; either version 2 of
#    the License, or (at your option) any later version.
#                                    https://www.gnu.org/licenses/
# ****************************************************************************

"""
This file contains functions to compute morphisms between hyperelliptic curves and the
corresponding abelian varieties (their jacobians) with theta functions of level 2 and 4.

The first half is from [VanW]_ and the last sections are algorithms from [Coss]_.
Based on the Magma implementation by Romain Cosset.

LAYOUT:
   
    3 - Manipulations of elements of Ep
    
    4 - twisted theta
    
    3 - Auxiliary functions
    
    4 - Expression of Ep
    
    6 - Mumford to Theta
    
    7 - Theta to Mumford

REFERENCES:

.. [VanW] P. Van Wamelen. Equations for the Jacobian of a hyperelliptic curve.
   Trans. Am. Math. Soc, 350(8), pp.3083-3106, 1998.

.. [Coss] R. Cosset. Applications des fonctions thêta à la cryptographie sur courbes hyperelliptiques.
   PhD thesis, Université Henri Poincaré – Nancy 1, 2011.


.. todo::

    - Reformat info above.
    - Sort documentation by source (to maintain layout)
    
"""


from collections import Counter
from itertools import product, combinations, chain

from sage.functions.other import ceil, floor
from sage.misc.all import prod, flatten, is_odd
from sage.rings.all import PolynomialRing, ZZ, Integer
from sage.structure.element import parent

integer_types = (int, Integer)

from .tools import rangeS
from .eta_maps import eta, eta_prime, eta_second, normalize_eta, sign_theta_normalized
from .ep_elements import EpElement



def compatible_sqrt(g, i, j):
    r"""
    Return the numerator and the denominator of sqrt(a_i - a_j) given by Definition 2
    in [VanW, page 3093] as an element of Ep.
    
    .. math ::
    
        \sqrt{\langle a_0 - a_j\rangle} = \sqrt{\langle a_0 - a_1\rangle} \frac{\theta[\eta_{U \circ V \circ \{j, \infty\}}]\theta[\eta_{U \circ V \circ \{0, 1\}}]}{\theta[\eta_{U \circ V \circ \{1, \infty\}}]\theta[\eta_{U \circ V \circ \{0, j\}}]}
        
    .. math ::
    
        \sqrt{\langle a_j - a_i\rangle} = \sqrt{\langle a_j - a_0\rangle} \frac{\theta[\eta_{U \circ V \circ \{i, \infty\}}]\theta[\eta_{U \circ V \circ \{0, j\}}]}{\theta[\eta_{U \circ V \circ \{0, \infty\}}]\theta[\eta_{U \circ V \circ \{i, j\}}]}

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import compatible_sqrt
        sage: compatible_sqrt(5, 6, 3)
        EpElement(sign=-1, power=1, numer=Counter({662: 1, 694: 1, 573: 1}), denom=Counter({663: 1, 607: 1, 725: 1}))

    """
    if i == j:
        raise ValueError('The difference of indices must be nonzero.')

    if i == 2*g + 1 or j == 2*g + 1:
        return EpElement(sign=1, power=0, numer=Counter(), denom=Counter())

    if i == 0:
        if j == 1:
            return EpElement(sign=1, power=1, numer=Counter(), denom=Counter())

        if j < g + 2:
            V = range(1, g+2)
        else:
            V = set(range(1, g+1))
            V.add(j)

        U = {2*x for x in range(g+1)}
        W = U.symmetric_difference(V)

        idx = lambda x : ZZ([c%2 for c in x], 2)
        ej = eta(g, W ^ {2*g + 1, j})
        e01 = eta(g, W ^ {0,1})
        e1 = eta(g, W ^ {2*g + 1, 1})
        e0j = eta(g, W ^ {0,j})
        n = Counter([idx(elem) for elem in [ej, e01]])
        d = Counter([idx(elem) for elem in [e1, e0j]])
        s = prod(sign_theta_normalized(elem) for elem in [ej, e01, e1, e0j])
        return EpElement(sign=s, power=1, numer=n, denom=d)

    L = list(range(1, g + 2))
    if i in L:
        L.remove(i)
    else:
        L.pop()
    if j not in L:
        L.pop()
        L.append(j)
    L.append(0)

    U = {2*x for x in range(g+1)}
    W = U.symmetric_difference(L)

    a = compatible_sqrt(g, 0, i)
    idx = lambda x : ZZ([c%2 for c in x], 2)
    e0i = eta(g, W ^ {0,i})
    ej = eta(g, W ^ {2*g + 1, j})
    e0 = eta(g, W ^ {2*g + 1, 0})
    eij = eta(g, W ^ {i,j})
    s = a.sign*prod(sign_theta_normalized(elem) for elem in [e0i, ej, e0, eij])
    n = a.numer + Counter([idx(elem) for elem in [e0i, ej]])
    d = a.denom + Counter([idx(elem) for elem in [e0, eij]])

    elem = EpElement(sign=s, power=a.power, numer=n, denom=d)

    return elem.clean_common()


##***** (4) twisted theta *****//

def constant_f(g, A, C):
    """
    Return the expression of f_A as an element of Ep, as defined by Definition 3 in [VanW, page 3095].

    INPUT:

    - ``g`` - an Integer, the dimension.
    - ``A`` - a set.
    - ``C`` - a choice of C as in [Coss]_ (see :func:`choice_of_C_Cosset` and :func:`choice_of_all_C_Cosset`).

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import constant_f
        sage: g = 5; A = set([1, 2, 3]); C = set([5, 6, 7])
        sage: fA = constant_f(g, A, C); fA
        EpElement(sign=1, power=-4, numer=Counter({607: 4, 694: 2, 911: 2, 843: 2, 415: 2, 347: 2, 723: 2, 850: 2, 484: 1, 637: 1, 626: 1, 561: 1, 950: 1, 638: 1, 724: 1, 573: 1, 595: 1, 978: 1, 330: 1}), denom=Counter({699: 5, 606: 4, 725: 2, 910: 2, 414: 2, 826: 1, 661: 1, 980: 1, 594: 1, 662: 1, 942: 1, 446: 1, 567: 1, 918: 1, 674: 1, 178: 1, 722: 1, 571: 1, 418: 1}))
        sage: print(fA)
        sign=1,
        power=-4,
        numer={
            [0, 0, 1, 0, 0, 1, 1, 1, 1]: 1,
            [0, 0, 1, 0, 1, 0, 1, 1, 0, 1]: 1,
            [0, 1, 0, 0, 1, 0, 1, 0, 1, 1]: 2,
            [0, 1, 0, 0, 1, 0, 1, 1, 1, 1]: 1,
        ...
            [1, 0, 1, 0, 1, 0, 1, 1, 0, 1]: 2,
            [1, 1, 0, 1, 1, 1, 0, 0, 0, 1]: 1,
            [1, 1, 0, 1, 1, 1, 0, 1, 0, 1]: 5,
            [1, 1, 1, 0, 1, 1, 0, 0, 0, 1]: 1
        }

    """
    f = {'power': 0}

    B = set(range(2*g + 1))
    U = {2*x for x in range(g+1)}

    # The two theta constants which appear in the definition
    idx = lambda x : ZZ([s%2 for s in x], 2)
    eC = eta(g, C)
    eUAC = eta(g, (U ^ A) ^ C)
    f['numer'] = Counter([idx(eC)])
    f['denom'] = Counter([idx(eUAC)])
    f['sign'] = prod(sign_theta_normalized(elem) for elem in [eC, eUAC])
    ff = EpElement(**f)

    #the four products of the definition
    # ff *= prod((compatible_sqrt(g, k, i) for i, k in product(A & U, U - A)), EpElement())
    # ff *= prod((compatible_sqrt(g, k, i) for i, k in product((B - A) & (B - U), A - U)), EpElement())
    # ff /= prod((compatible_sqrt(g, k, i) for i, k in product((A ^ C) & (U ^ C), (U ^ C) - (A ^ C))), EpElement())
    # ff /= prod((compatible_sqrt(g, k, i) for i, k in product((B - (A ^ C)) & (B - (U ^ C)), (A ^ C) - (U ^ C))), EpElement())

    # We compute a simplified version for speed
    prod_list = Counter([(i,k) for i, k in product(A & U, U - A)] + [(i,k) for i, k in product((B - A) & (B - U), A - U)])
    div_list = Counter([(i,k) for i, k in product((A ^ C) & (U ^ C), (U ^ C) - (A ^ C))] + [(i,k) for i, k in product((B - (A ^ C)) & (B - (U ^ C)), (A ^ C) - (U ^ C))])
    ff *= prod((compatible_sqrt(g, k, i)**m for (i,k), m in (prod_list - div_list).items()), EpElement())
    ff /= prod((compatible_sqrt(g, k, i)**m for (i,k), m in (div_list - prod_list).items()), EpElement())

    return ff.clean_common()

def choice_of_C_Cosset(g, A):
    """
    Make a choice for the constant C as in Definition 5.1.5 of [Coss]_.

    INPUT:

    - ``g`` - an Integer, the dimension.
    - ``A`` - a set.

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import choice_of_C_Cosset
        sage: choice_of_C_Cosset(5, {0,1,2})
        {3, 4}

    """
    if len(A) > g + 1:
        raise ValueError(f'Expected set A(={A}) of cardinality at most {g+1}')
    if 2*g + 1 in A:
        raise ValueError(f'A should not contain the index for the point at infinity')

    U = {2*x for x in range(g+1)}

    if len(A) == g or len(A) == g+1: # |A|=g+1
        return set()

    n = floor((g + 1 - len(A))/2)

    Cp = set() # 2*g + 1 in Cp  if 2*g + 1  not in A DIFF shouldn't it be Cp = {2*g + 1} then?
    Cpp = set()
    for i in range(0, 2*g + 2):
        if i not in A | U and len(Cp) < n:
            Cp.add(i)
        elif i in U - A and len(Cpp) < n:
            Cpp.add(i)
        else:
            if len(Cp) == n and len(Cpp) == n:
                break

    return Cp | Cpp

def choice_of_all_C_Cosset(g):
    """
    Make a choice for all the constants C as in Definition 5.1.5 of [Coss]_.

    INPUT:

    - ``g`` - an Integer, the dimension.

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import choice_of_all_C_Cosset
        sage: g = 5; C = choice_of_all_C_Cosset(g)
        sage: C[frozenset({1,3,4})]
        {0, 5}
        sage: B = frozenset(range(2*g + 1))
        sage: C[B.difference({1,3,4})]
        {0, 5}

    """
    C = {}
    B = frozenset(range(2*g + 1))

    for A in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(g + 1)):
        A = frozenset(A)
        C[A] = choice_of_C_Cosset(g, A)
        C[B - A] = C[A]

    return C

def sign_s_A(g, A, C):
    """
    Compute the sign of s_A as defined in Section 5.1.4 of [Coss]_.

    INPUT:

    - ``g`` - an Integer, the dimension.
    - ``A`` - a set.
    - ``C`` - a choice of all C as in [Coss]_ (see :func:`choice_of_all_C_Cosset`).

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import choice_of_all_C_Cosset, sign_s_A
        sage: g = 5; C = choice_of_all_C_Cosset(g)
        sage: sign_s_A(g, [1, 2, 3], C)
        1

    """
    if len(A) == 0 or len(A) == 1:
        return 1

    zg = eta_second(g, range(2*g + 1))/2 #DIFF is this eta_g as defined in [Coss]?
    U = {2*x for x in range(g+1)}

    if len(A) >= 2*g:
        sA = (-1)**ZZ(eta_prime(g, C[frozenset()] & U)*zg)
        for l in range(2*g + 1):
            sA *= (-1)**ZZ(eta_prime(g,C[frozenset({l})] & U)*zg)
        return sA

    s = len(A)
    n = floor(s/2)
    if not isinstance(A, frozenset):
        A = frozenset(A)

    sA = (-1)**ZZ(eta_prime(g,C[A] & U)*zg)
    for l in A:
        sA *= (-1)**ZZ(eta_prime(g,C[frozenset({l})] & U)*zg)

    if is_odd(s):
        sA *= (-1)**floor((n+1)/2) #DIFF why not directly (-1)**floor((s+1)/4)??
    else:
        sA *= (-1)**ZZ(eta_prime(g,C[frozenset()] & U)*zg)
        sA *= (-1)**floor(n/2) #DIFF why not directly (-1)**floor((s+1)/4)??

    if s >= g:
        sA *= (-1)**ZZ(eta_prime(g,C[A])*zg) #DIFF why?

    return sA

##***** (3) Auxiliary functions *****//

def IgusaTheorem(A, TH):
    """
    Apply Igusa theorems to the theta with characteristic given in the list A
    The theta in the summation are taken from TH #FIXME: Add reference

    INPUT:

    - ``A`` - A list with 4 eta vectors.
    - ``TH`` - A list of 4 analytic theta points.

    EXAMPLES ::

        sage: from avisogenies_sage import KummerVariety, AnalyticThetaNullPoint
        sage: from avisogenies_sage.morphisms_aux import IgusaTheorem
        sage: from avisogenies_sage.eta_maps import eta
        sage: g = 2; A = KummerVariety(GF(331), 2, [328 , 213 , 75 , 1])
        sage: P = A([255 , 89 , 30 , 1])
        sage: thc = AnalyticThetaNullPoint.from_algebraic(A)
        sage: thp = thc(P)
        sage: thO = thc(0)
        sage: IgusaTheorem([eta(g,{2*x for x in range(g+1)})]*4, [thp,thO,thO,thO])
        56

    .. todo:: Add reference, see FIXME.
    """
    if len(A)!=4 or len(TH)!=4:
        raise ValueError
    D = TH[0].abelian_variety()._numbering #Zmod(2)**(2*g)
    g = TH[0].abelian_variety()._dimension
    V = ZZ**(2*g)

    a1, a2, a3, a4 = A
    N = [sum(A)/2, (a1 + a2 - a3 - a4)/2, (a1 - a2 + a3 - a4)/2, (a1 - a2 - a3 + a4)/2]
    p = 0
    idx = lambda x : ZZ(list(x), 2)

    for a in D:
        a = V(a)
        t = (-1)**ZZ(a1[:g]*a[g:])
        t *= prod(th[idx(normalize_eta(n + a))] for th, n in zip(TH, N))
        t *= prod(sign_theta_normalized(n + a) for n in N)
        p += t

    return p/2**g
    
##***** (4) Expression of Ep *****//

def constant_f2_level2(a, thc, A, C):
    """
    Compute the constant f_S^2 from the theta constant of level 2

    INPUT:

    - ``a`` - list of x-coordinates of the Weierstrass points.
    - ``thc`` - the theta null point associated to the jacobian of the curve.
    - ``A`` - a set
    - ``C`` - a choice of C as in [Coss]_ (see :func:`choice_of_C_Cosset` and :func:`choice_of_all_C_Cosset`).

    EXAMPLES ::

        sage: from avisogenies_sage import KummerVariety, AnalyticThetaNullPoint
        sage: from avisogenies_sage.morphisms_aux import constant_f2_level2, choice_of_C_Cosset
        sage: g = 2; A = KummerVariety(GF(331), 2, [328 , 213 , 75 , 1])
        sage: thc = AnalyticThetaNullPoint.from_algebraic(A)
        sage: a = [0,1,4,6,7]
        sage: A = {3,4}; constant_f2_level2(a, thc, A, choice_of_C_Cosset(g, A))
        170

    """
    g = thc._dimension
    thO = thc(0)
    U = {2*x for x in range(g+1)}
    B = set(range(2*g + 1))

    # the two theta constants which appear in the definition
    f2 = thO[eta(g, C, normalized=True, idx=True)]/thO[eta(g, (U ^ A) ^ C, normalized=True, idx=True)]

    # the four product of the definitions
    f2 *= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product(A & U, U - A))
    f2 *= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product((B - A) & (B - U), A - U))
    f2 /= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product((A ^ C) & (U ^ C), (U ^ C) - (A ^ C)))
    f2 /= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product((B - (A ^ C)) & (B - (U ^ C)), (A ^ C) - (U ^ C)))

    return f2

##***** (6) Mumford to Theta *****//

def YS_fromMumford_Generic(g, a, S, points):
    """
    Compute Y_S(P) for P a preimage of a point D in Jac(C)\\Theta as defined in
    Equation (5.1) in [Coss]_..
    D can be writen as D = sum_1^g P_i - g P_infty.

    INPUT:

    - ``g`` - an integer. The genus of the curve.
    - ``a`` - list of x-coordinates of the Weierstrass points.
    - ``S`` - an iterable.
    - ``points`` - a list of coordinates (x,y) (as tuples) of the points P_i in D. Assume
      that all P_i are distinct.

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import YS_fromMumford_Generic
        sage: g = 2; a = [0,1,4,6,7]; S = [0,2,3]
        sage: points = [(2, 4), (3, 8)]
        sage: YS_fromMumford_Generic(g, a, S, points)
        92

    """
    if len(S) < 2 or len(S) > 2*g - 1:
        raise ValueError(f'Expected length of S={S} between 2 and {2*g - 1}')
    if len(points) != g or len(set(points)) != g:
        raise ValueError(f'Expected points={points} to be a list of {g} distinct elements')

    n = ceil((len(S)-1)/2)
    YS = 0
    for I in combinations(range(g), n):
        t = prod(points[i][1] for i in I)
        t *= prod(points[k][0] - a[l] for l, k in product(S, range(g)) if k not in I) #(x_k-a_l)
        t /= prod(points[i][0] - points[k][0] for i, k in product(I, range(g)) if k not in I)
        YS += t
    return YS

def YS_fromMumford_Delta(g, a, S, points, F): #DIFF: Not tested against Magma
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Assume that there exists i <=> j such that P_i = P_j but the other P_k are distinct
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of the Weierstrass points of the curve

    return the function Y_S

    See page 117 in [Coss]_.

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import YS_fromMumford_Delta
        sage: F = GF(331); g = 2; a = [0, 1, 2, 3, 4]; S = [0,2,3]
        sage: points = [(F(5), F(38))]*2
        sage: YS_fromMumford_Delta(g, [F(el) for el in a], S, points, F)
        64

    .. todo:: Test against Magma (minus the possible mistake)!
    """
    if len(S) < 2 or len(S) > 2*g - 1:
        raise ValueError(F'Expected length of S={S} between 2 and {2*g - 1}')
    if len(points) != g or len(set(points)) != g - 1:
        raise ValueError(F'Expected points={points} to be a list of {g} elements of which exactly two are equal')

    n = floor(len(S)/2)
    points = [(F(x), F(y)) for (x,y) in points]
    a = [F(elem) for elem in a]

    K = PolynomialRing(F, 2, 'xy')
    x, y = K.gens()

    for i, elemi in enumerate(points):
        for j, elemj in enumerate(points[i + 1:]):
            if elemi == elemj:
                points.pop(j)
                points.pop(i)
                points.append(elemi)
                points.append(elemj)
                #now the repeated elements are the last two
                break
        else:
            continue
        break

    Y = 0
    #Cases where I doesn't contain the indices of the repeated cases, or it contains both (if possible): normal.
    for I in chain.from_iterable(combinations(range(g-2), r) for r in [n, n-2] if r >=0):
        if len(I) == n-2:
            I = I + (g-2, g-1)  #DIFF: In Magma implementation, in this case, missing y_{-1}^2 ? See Definition 5.1.26 on pg 116
        t = prod(points[i][1] for i in I)
        t *= prod(points[k][0] - a[l] for l, k in product(S, range(g)) if k not in I)
        t /= prod(points[i][0] - points[k][0] for i, k in product(I, range(g)) if k not in I)
        Y+=t

    #Cases where I contains exactly one of the two.
    
    # With the formula in [Coss]_, t would be computed as follows

    # for I in combinations(range(g-2), n-1):
        # #First summand of p_I in [Coss, page 118].

        # P = prod(x - a[l] for l in range(2*g + 1) if l not in S)*prod(y - a[l] for l in S)
        # P -= prod(y - a[l] for l in range(2*g + 1) if l not in S)*prod(x - a[l] for l in S)
        # try:
            # P = K(P/(x-y))
        # except TypeError:
            # raise ValueError('P={P} should be divisible by {x - y}')
        # t = P(points[-1][0],points[-1][0])*prod((points[-1][0] - a[l])**2 for l in S)

        # t /= 2*points[-1][1]*prod(points[-1][0] - a[l] for l in S)

        # t *= prod(points[i][1] for i in I)
        # t /= prod(points[i][0] - points[-2][0] for i in I)

        # t *= prod(points[k][0] - a[l] for l, k in product(S, range(g-2)) if k not in I)
        # t /= prod(points[i][0] - points[k][0] for i, k in product(I + (-1,), range(g-2)) if k not in I)

        # Y += t

        # #Second summand of p_I in [Coss, page 118]

        # t = points[-2][1]
        # t *= prod(points[i][1] for i in I)
        # t *= prod(points[-1][0] - a[l] for l in S)

        # t *= prod(points[k][0]-a[l] for l, k in product(S, range(g-2)) if k not in I)
        # t /= prod(points[i][0]-points[k][0] for i, k in product(I, range(g-2) if k not in I)

        # t /= prod((points[i][0]-points[-2][0])**2 for i in I)
        # t /= prod((points[-1][0]-points[k][0])**2 for k in range(g-2) if k not in I)

        # P = prod(points[i][0] - x for i in I)*prod(y - points[k][0] for k in range(g-2) if k not in I)
        # P -= prod(points[i][0] - y for i in I)*prod(x - points[k][0] for k in range(g-2) if k not in I)
        # try:
          # P = K(P/(x-y))
        # except TypeError:
          # raise ValueError('P={P} should be divisible by {x - y}')

        # t *= P(points[1][0],points[1][0])

        # Y += t

    #We reorganize de computation for sake of efficiency

    P = prod(x - a[l] for l in range(2*g + 1) if l not in S)*prod(y - a[l] for l in S)
    P -= prod(y - a[l] for l in range(2*g + 1) if l not in S)*prod(x - a[l] for l in S)
    try:
        P = K(P/(x-y))
    except TypeError:
        raise ValueError('P={P} should be divisible by {x - y}')

    t01 = P(points[-1][0],points[-1][0])/(2*points[-1][1])*prod(points[-1][0] - a[l] for l in S)

    t02 = 1/prod(((points[i][0]-points[-1][0])**2 for i in range(g-2)), F(1))

    for I in combinations(range(g-2), n-1):

        t1 = t01 * prod(points[i][1] for i in I)
        t1 *= prod(points[k][0] - a[l] for l, k in product(S, range(g-1)) if k not in I)
        t1 /= prod(points[i][0] - points[k][0] for i, k in product(I + (-1,), range(g-2)) if k not in I)
        t1 /= prod(points[i][0] - points[-2][0] for i in I)

        t2 = t02 * prod(points[i][1] for i in I + (-2,))

        t2 *= prod(points[k][0] - a[l] for l, k in product(S, range(g-2)) if k not in I)
        t2 /= prod(points[i][0] - points[k][0] for i, k in product(I, range(g-2)) if k not in I)

        P = prod(points[i][0] - x for i in I)*prod(y - points[k][0] for k in range(g-2) if k not in I)
        P -= prod(points[i][0] - y for i in I)*prod(x - points[k][0] for k in range(g-2) if k not in I)
        try:
            P = K(P/(x-y))
        except TypeError:
            raise ValueError('P={P} should be divisible by {x - y}')
        t2 *= P(points[-1][0],points[-1][0])

        Y += t1 + t2

    return Y

def prodYp_fromMumford_with2torsion(g, a, S, points, V, C, F):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let S = [S1, S2, S3, S4] with S1 ^ S2 ^ S3 ^ S4 == {}
    Let C be the choice of sets in the definition of the f_A

    Assume that all P_i are distinct.

    Compute the function
    prod Y_Si' / prod a_l
    where the second product is over l in V counted twice iff it appears in all Si

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import choice_of_all_C_Cosset, prodYp_fromMumford_with2torsion
        sage: F = GF(331); g = 2; a = list(map(F, [0, 1, 2, 3, 4]))
        sage: S = [{0,2,3},{0},{2,4}, {3,4}]; V = {1}
        sage: points = [(F(1), F(0)), (F(8), F(10))]
        sage: C = choice_of_all_C_Cosset(g)
        sage: prodYp_fromMumford_with2torsion(g, a, S, points, V, C, F)
        187

    .. todo:: Address FIXME.
    """

    if len(V) < 1 or len(V) > g:
        raise ValueError(F'Expected length of V={V} between 1 and {g}')
    if len(points) != g:
        raise ValueError(F'Expected length of points={points} to be {g}')

    for s in S:
        if len(s) < 2*len(V & s):
            raise ValueError(F'Error?? FIXME')

    if S[0] ^ S[1] ^ S[2] ^ S[3] != set():
        raise ValueError(F'Error??? FIXME')

    points = [(F(x), F(y)) for (x,y) in points]
    a = [F(elem) for elem in a]
    K = PolynomialRing(F, 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)
    if any(u(a[l]) != 0 for l in V):
        raise ValueError('Indices in V should vanish u??') #FIXME

    # Let R be a subset {1, ..., g} which correspond to the index i such that P_i is the
    # ramification point a_l with l in V
    R = [points.index((a[l],0)) for l in V]
    ind_VmS = [{idx for idx, l in zip(R, V) if l in s} for s in S]

    n = [floor(len(s)/2) for s in S]
    zg = eta_second(g, range(2*g + 1))/2
    W = V.intersection(*S)

    Y = 0
    for Ip in product(*[combinations(rangeS(g, R), ni - len(V & si)) for ni, si in zip(n, S)]):
        I = [ s | set(ip) for s, ip in zip(ind_VmS, Ip)]
        t = prod(points[i][1]  for Ij in I for i in Ij.difference(R))

        for s, i in zip(S, I):
            if len(s) >=2:
                t *= prod(points[k][0] - a[l] for l, k in product(s, rangeS(g,i)))
                t /= prod(points[j][0] - points[k][0] for j, k in product(i, range(g)) if k not in i)

        t /= prod(points[k][0] - a[l] for l, k in product(V, range(g)) if k not in R)
        t /= prod(points[k][0] - a[l] for l, k in product(W, range(g)) if k not in R)

        Y += t

    Y *= (-1)**(len(W) * len(V - W))
    Y *= prod(a[l] - a[m] for l, m in product(V, range(2*g + 1)) if m not in V)
    Y *= prod(a[l] - a[m] for l, m in product(W, range(2*g + 1)) if m not in V)

    #The sign
    for s in S:
        if len(s) == 1:
            Y *= (-1)**g*u(next(iter(s)))
        elif 2 <= len(s) <= 2*g - 1:
            Y *= sign_s_A(g, s, C)
        elif len(s) == 2*g:
            Y *= sign_s_A(g, range(2*g+1), C)
            Y *= (-1)**floor(g/2)
            Y *= (-1)**ZZ(eta_prime(g, C[s])*zg)
        elif len(s) ==  2*g + 1:
            Y *= sign_s_A(g, range(2*g +1), C)
            Y *= (-1)**floor((g+1)/2)
            Y *= (-1)**ZZ(eta_prime(g,C[frozenset()])*zg)
        else:
            raise ValueError(F'Expected length of S={s} between 1 and {2*g+1}')

    return Y

def Y_fromMumford_with2torsion(g,a,S,points,V):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve

    Assume that all P_i are distinct.
    Assume that the first P_i are [a[l],0] with l in V
    Assume that V is a subset of S

    Compute the function Y_S^2 / prod a_l    where the product is over l in V

    EXAMPLES ::

        sage: from avisogenies_sage.morphisms_aux import Y_fromMumford_with2torsion
        sage: F = GF(331); g = 2; a = list(map(F, [0, 1, 2, 3, 4]))
        sage: S = {0,2,3,4}; V = {0,2}
        sage: points = [(F(0), F(0)), (F(2), F(0))]
        sage: Y_fromMumford_with2torsion(g,a,S,points,V)
        307

    TESTS::

        sage: from avisogenies_sage.morphisms_aux import Y_fromMumford_with2torsion
        sage: F = GF(331); g = 2; a = list(map(F, [0, 1, 2, 3, 4]))
        sage: S = {0,2,3,4}; V = {0}
        sage: points = [(F(0), F(0)), (F(8), F(10))]
        sage: Y_fromMumford_with2torsion(g,a,S,points,V)
        300

    .. todo:: Address FIXME.
    """
    if not V < S or len(V) == 0:
        raise ValueError(F'V={V} should be a non-empty subset of S={S}')
    if len(points) != g:
        raise ValueError(F'Expected length of points={points} to be {g}')
    if len(S) < 2*len(V):
        raise ValueError(F'Error?? FIXME')

    #s = len(S)
    v = len(V)
    n = floor(len(S)/2)

    aV = [a[i] for i in V]
    if any(points[l][0] not in aV for l in range(v)):
        raise ValueError(F'Expected the first {v} points to be in {aV}')

    if v == n:
        Y = prod(a[l] - a[k] for l, k in product(V, range(2*g + 1)) if k not in V)
        Y /= prod(points[k][1] - a[l] for l, k in product(V, range(v, g)))
        Y *= prod((points[k][1] - a[l])**2 for l, k in product(S - V, range(v, g)))
        return Y

    Y = 0
    for I, J in product(combinations(range(v,g), n-v), repeat=2):
        t = prod(points[i][1] for i in I + J)
        for elem in [I, J]:
            t *= prod(points[k][0] - a[l] for l, k in product(S - V, range(v,g)) if k not in elem)
            t /= prod(points[i][0] - points[k][0] for i, k in product(elem, range(v,g)) if k not in elem)
        Y+=t

    Y *= prod(a[l] - a[k] for l, k in product(V, range(2*g + 1)) if k not in V)
    Y /= prod(points[k][0] - a[l] for l, k in product(V, range(v, g)))

    return Y
