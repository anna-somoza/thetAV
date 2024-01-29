"""
Morphism functionalities.


AUTHORS:

- Anna Somoza (2021-22): initial implementation

"""


# ****************************************************************************
#             Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#    Distributed under the terms of the GNU General Public License (GPL)
#    as published by the Free Software Foundation; either version 3 of
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
    
.. todo::

    - Reformat info above.
    - Sort documentation by source (to maintain layout)
    
"""


from itertools import product, combinations, chain

from sage.functions.other import sqrt
from sage.misc.all import prod
from sage.rings.all import PolynomialRing, ZZ, Integer
from sage.structure.element import parent

integer_types = (int, Integer)
from sage.arith.misc import XGCD

from .eta_maps import eta, eta_prime, eta_second, normalize_eta, e_2
from .morphisms_aux import choice_of_all_C_Cosset, constant_f2_level2, YS_fromMumford_Generic, YS_fromMumford_Delta, Y_fromMumford_with2torsion, sign_s_A


def MumfordToTheta_2_Generic(a, thc2, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be written as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let thc2 be the theta constant of level 2

    Return the theta functions of level 2 associated to points

    EXAMPLES ::

        sage: from thetAV import KummerVariety
        sage: from thetAV.morphisms_level2 import MumfordToTheta_2_Generic
        sage: F = GF(331); g = 2; n = 2
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: points = [(F(7), F(62)), (F(8), F(10))]
        sage: A = KummerVariety(F, g, [328 , 213 , 75 , 1])
        sage: thc =  A.with_theta_basis('F(2,2)^2')
        sage: MumfordToTheta_2_Generic(a, thc, points)._coords #FIXME change when _repr_ is done
        (92, 265, 295, 308, 319, 261, 303, 111, 89, 193, 275, 12, 262, 214, 46, 70)

    .. todo::  Test against Magma in the case that uses YS_fromMumford_Delta

    """
    if thc2.level() != 2:
        raise ValueError(F'Expected level-2 theta structure.')

    g = thc2.dimension()
    if len(points) != g:
        raise ValueError(F'Expected degree-{g} divisor')

    F = thc2._R
    K = PolynomialRing(F, 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)

    if any(u(elem) == 0 for elem in a):
        raise ValueError(F'Expected generic divisor')

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result
    U = {2*x for x in range(g+1)}

    idx = thc2._char_to_idx
    th2 = [0]*(2**(2*g))
    e = eta(g, U, normalized=True)
    th2[idx(e)] = 1/constant_f2_level2(a, thc2, set(), C[frozenset()])

    for l in range(2*g + 1):
        ee = normalize_eta(e + eta(g, l))
        i = idx(ee)
        th2[i] = (-1)**g*u(a[l])
        th2[i] /= constant_f2_level2(a, thc2, {l}, C[frozenset({l})])

    lpoints = len(set(points))
    for S in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(2, g+1)):
        if lpoints == g:
            YS = YS_fromMumford_Generic(g, a, S, points)
        elif lpoints == g - 1:
            YS = YS_fromMumford_Delta(g, a, S, points, F)
        else:
            raise NotImplementedError('The case of non generic delta divisor is not implemented')
        ee = normalize_eta(e + eta(g, S))
        i = idx(ee)
        th2[i] = YS**2*(-1)**(g*len(S))
        th2[i] /= prod(u(a[l]) for l in S)
        th2[i] /= constant_f2_level2(a, thc2, set(S), C[frozenset(S)])

    return thc2(th2)

def MumfordToLevel2ThetaPoint(a, thc2, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be written as
    D = sum_1^d P_i - g P_infty
    Let points be the list of coordinates [x,y] of P_i
    Let a be the x-coordinates of the Weierstrass points of the curve
    Let thc2 be the theta constant of level 2

    Assume that all P_i are distinct if the divisor is either theta or has a
    ramification point in its support.

    Return the theta functions of level 2 associated to points

    EXAMPLES ::

        sage: from thetAV import KummerVariety
        sage: from thetAV.morphisms_level2 import MumfordToLevel2ThetaPoint
        sage: F = GF(331); g = 2; n = 2
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: points = [(F(7), F(62)), (F(8), F(10))]
        sage: A = KummerVariety(F, g, [328 , 213 , 75 , 1])
        sage: thc =  A.with_theta_basis('F(2,2)^2')
        sage: MumfordToLevel2ThetaPoint(a, thc, points)._coords #FIXME change when _repr_ is done
        (92, 265, 295, 308, 319, 261, 303, 111, 89, 193, 275, 12, 262, 214, 46, 70)


        sage: from thetAV import KummerVariety
        sage: from thetAV.morphisms_level2 import MumfordToLevel2ThetaPoint
        sage: F = GF(331); g = 2; n = 2
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: points = [(F(7), F(62))]
        sage: A = KummerVariety(F, g, [328 , 213 , 75 , 1])
        sage: thc = A.with_theta_basis('F(2,2)^2')
        sage: MumfordToLevel2ThetaPoint(a, thc, points)._coords #FIXME change when _repr_ is done, Magma output
        (288, 101, 184, 91, 289, 74, 111, 10, 106, 54, 12, 0, 292, 48, 113, 243)


    .. todo:: Add tests that cover the missing cases.
    
    """
    if thc2.level() != 2:
        raise ValueError(f'Expected level-2 theta structure.')

    g = thc2.dimension()

    if len(points) == 0:
        return thc2(0)

    K = PolynomialRing(parent(points[0][0]), 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)

    up = u
    points_p = list(points)

    V1 = {l for l, al in enumerate(a) if up(al) == 0}

    if len(points) == g and len(V1) == 0:
        return MumfordToTheta_2_Generic(a, thc2, points)

    V2 = set()
    
    if len(points) < g:
        for l, al in enumerate(a):
            if l not in V1:
                V2.add(l)
                up *= (x - al)
                points_p.append((al, 0))
                if up.degree() == g:
                    break

    V = V1 | V2

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result
    U = {2*x for x in range(g+1)}
    B = frozenset(range(2*g + 1))

    th2p = [0]*2**(2*g)

    i = eta(g, U, normalized=True, idx=True)
    th2p[i] = 1 / constant_f2_level2(a, thc2, set(), C[frozenset()])

    for l in range(2*g + 1):
        ii = eta(g, U ^ {l}, normalized=True, idx=True)
        th2p[ii] = (-1)**g*up(a[l])
        th2p[ii] /= constant_f2_level2(a, thc2, {l}, C[frozenset([l])])

    for S in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(2, g+1)):
        S = frozenset(S)
        if V & S == set():
            YS = YS_fromMumford_Generic(g, a, S, points_p)
            ii = eta(g, U ^ S, normalized=True, idx=True)
            th2p[ii] = YS**2*(-1)**(g*len(S))
            th2p[ii] /= prod(up(a[l]) for l in S)
            th2p[ii] /= constant_f2_level2(a, thc2, S, C[S])
        elif V < S:
            Sp = B - S
            YS = YS_fromMumford_Generic(g, a, Sp, points_p)
            ii = eta(g, U ^ Sp, normalized=True, idx=True)
            th2p[ii] = YS**2*(-1)**(g*len(Sp))
            th2p[ii] /= prod(up(a[l]) for l in Sp)
            th2p[ii] /= constant_f2_level2(a, thc2, Sp, C[Sp])
        elif len(S) < 2*len(V & S): #TODO: Not tested
            ii = eta(g,U ^ S, normalized=True, idx=True)
            th2p[ii] = 0
        else: #TODO: Not tested
            deb = [(a[l],0) for l in V & S]
            fin = [points_p[i] for i in range(g) if points_p[i] not in deb]
            YS_sq = Y_fromMumford_with2torsion(g, a, S, deb + fin, V & S)
            ii = eta(g, U ^ S, normalized=True, idx=True)
            th2p[ii] = YS_sq*(-1)**(g*len(S - V))
            th2p[ii] /= prod(up(a[l]) for l in S - V)
            th2p[ii] /= constant_f2_level2(a, thc2, S, C[S])

    th2 = thc2(th2p)
    for l in V2: ##TODO: Can we compute eta(V2) and add only once?
        th2 = th2.add_twotorsion_point(eta(g,l))

    return th2

def ThetaToMumford_2_Generic(a, th2):
    """
    Let D be a point in Jac(C)\\Theta
    D is represented by the theta functions th2 of level 2
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let thc2 be the theta constants of level 2

    Compute the Mumford polynomials (u,v^2) associated to D

    EXAMPLES ::

        sage: from thetAV import KummerVariety
        sage: from thetAV.morphisms_level2 import ThetaToMumford_2_Generic
        sage: F = GF(331); A = KummerVariety(F, 2, [328 , 213 , 75 , 1])
        sage: P = A([255 , 89 , 30 , 1])
        sage: thc = A.with_theta_basis('F(2,2)^2')
        sage: thp = thc(P)
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: ThetaToMumford_2_Generic(a, thp)
        (139*x^2 + 117*x + 157, 57*x^2 + 70*x + 210)

    """
    thc2 = th2.abelian_variety()
    g = thc2.dimension()

    if thc2.level() != 2:
        raise ValueError(f'Expected a level-2 theta structure')

    Ab = thc2._numbering
    idx = thc2._char_to_idx

    F = parent(th2[0])
    K = PolynomialRing(F, 'x')
    x = K.gen()
    a = [F(elem) for elem in a]

    U = frozenset(2*x for x in range(g+1))
    zg = eta_second(g, set(range(2*g+1)))/2

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result

    idx_etaU = eta(g, U, normalized=True, idx=True)
    if th2[idx_etaU] == 0:
        raise ValueError('Divisor theta!') #FIXME

    u_al = []
    ct_f2_empty = constant_f2_level2(a, thc2, set(), C[frozenset()])
    ct_f2_U = constant_f2_level2(a, thc2, U, C[U])
    for l in range(g+1):
        Sl = frozenset([l])
        val = (-1)**g
        val *= th2[eta(g, U ^ Sl, normalized=True, idx=True)]
        val /= th2[idx_etaU]
        val *= constant_f2_level2(a, thc2, Sl, C[Sl])
        val /= ct_f2_empty
        u_al.append(val)

    # use Lagrange interpolation
    u = K(0)
    for i, t in enumerate(u_al):
        t *= prod((x - a[j])/(a[i] - a[j]) for j in range(g+1) if j!= i)
        u += t

    # we have u
    v2_al = [F(0)]*(2*g - 1)
    for l in range(2*g - 1):
        if l < g:
            V = set(range(g+1))
            V.remove(l)
        else:
            V = set(range(g))

        for m in V:
            t = th2[eta(g,U ^ {l,m}, normalized=True, idx=True)]
            t /= th2[idx_etaU]
            t *= constant_f2_level2(a, thc2, {l,m}, C[frozenset([l,m])])
            t /= ct_f2_empty
            t *= u(a[l])*u(a[m])
            t /= prod((a[m] - a[k])**2 for k in V - {m})
            v2_al[l] += t

        # Now compute the terms t corresponding to m <=> n
        for m, n in product(V, repeat=2):
            if n == m:
                continue
            t = sign_s_A(g,{l,m},C)*sign_s_A(g,{l,n},C)

            t *= th2[eta(g, U ^ {l}, normalized=True, idx=True)]
            t /= th2[idx_etaU]**3
            t *= constant_f2_level2(a, thc2, {l}, C[frozenset([l])])
            t /= ct_f2_empty**3

            # we need to compute s = t_lm(z) t_ln(z) t_m(z) t_n(z)
            s = 0
            for S in combinations(range(2*g + 1), g+1):
                S = frozenset(S)
                if l not in S or len(S & {m,n}) != 1:
                    continue
                e = eta(g, U ^ S ^ {l,m,n})
                r = 0 # r = theta[e](2z) theta[e](0) theta[0](0)^2
                for idxb, b in enumerate(Ab):
                    q = (-1)**ZZ(e[:g]*b[g:])
                    q *= th2[idx(b + e)]
                    q *= th2[idxb]
                    r += q/2**g

                # We multiply r by the right constant in the sum
                c = set()
                for st in [{l,m}, {l,n}, {m}, {n}]:
                    c.symmetric_difference_update(C[frozenset(st)])
                c.intersection_update(U)
                cst = (-1)**ZZ(eta_prime(g,c)*zg)
                cst /= prod((-1)**(i > j)*(a[j] - a[i]) for i, j in product(S - {l, m, n}, range(2*g + 1)) if j not in S | {m, n})
                cst *= ct_f2_U
                cst *= constant_f2_level2(a, thc2, S ^ {l,m,n}, C[S ^ {l,m,n}])
                r *= cst

                #the sign in the sum
                r *= (-1)**g
                r *= e_2(g, U, S)
                r *= ZZ(-1)**(eta_prime(g, l)*eta_second(g,S - {m,n}))
                r *= ZZ(-1)**(eta_prime(g, {m,n})*eta_second(g,S - {l}))
                r *= ZZ(-1)**(eta_prime(g, m)*eta_second(g, n))
                r *= e_2(g, {n}, S)

                s += r/2**g

            t *= s
            t /= prod(a[m] - a[k] for k in V if k != m)
            t /= prod(a[n] - a[k] for k in V if k != n)
            v2_al[l]+=t

    v2 = K(0)
    for i, t in enumerate(v2_al):
        t *= prod((x-a[j])/(a[i]-a[j]) for j in range(2*g - 1) if j != i)
        v2 += t

    return u, v2


def ThetaToMumford_2_algclose(a, th2):
    """
    Let D be a point in Jac(C).
    D is represented by the theta functions th2 of level 2
    Let a be the x-coordinate of th Weierstrass points of the curve

    Assume that the base field is algebraically closed

    Compute the Mumford polynomials (u,v^2) associated to D
    
    .. todo:: Difference with function above? Do we need this or can we join them somehow? Test against Magma, add examples
    """
    thc2 = th2.abelian_variety()
    g = thc2.dimension()

    if thc2.level() != 2:
        raise ValueError(f'Expected a level-2 theta structure')

    # Ab = thc2._numbering
    U = {2*x for x in range(g+1)}
    th2p = th2

    V = set()
    idx_etaU = eta(g, U, normalized=True, idx=True)
    for l in range(2*g + 1):
        if th2p[idx_etaU] != 0:
            break
        V.add(l)
        th2p = th2p.add_twotorsion_point(eta(g, l))

    u, v2 = ThetaToMumford_2_Generic(a,th2p)

    K = parent(u)
    x = K.gen()

    for l in V:
        if (x - a[l]).divides(u):
            d = u.degree()
            u /= x - a[l]
            u = K(u)
            v = sqrt(v2)
            v2 = K(v2 + v2[2*d - 2]*u**2 - 2*v[d - 1]*v*u )
        else:
            d,e,f = XGCD(u, x - a[l])
            v = sqrt(v2)
            v2 = K(v2 + (e/d)**2*u*v2(a[l]) - 2*e/d*u*v*v(a[l]) )
            u *= x-a[l]

    return u,v2

def Level2ThetaPointToMumford(a, th2):
    """
    Let D be a point in Jac(C).
    D is represented by the theta functions th2 of level 2
    Let a be the x-coordinate of th Weierstrass points of the curve

    .. NOTE::
    
        We use an extension field of degree 2

    Compute the Mumford polynomials (u,v^2) associated to D
    
    .. todo:: Test against Magma, add examples
    """
    thc2 = th2.abelian_variety()
    g = thc2.dimension()

    if thc2.level() != 2:
        raise ValueError(f'Expected a level-2 theta structure')

    U = {2*x for x in range(g+1)}
    th2p = th2
    idx_etaU = eta(g, U, normalized=True, idx=True)
    V = set()
    for l in range(2*g + 1):
        if th2p[idx_etaU] != 0:
            break
        V.add(l)
        th2p = th2p.add_twotorsion_point(eta(g, l))

    u, v2 = ThetaToMumford_2_Generic(a, th2p)

    K = parent(u)

    F = parent(u[0])
    FF = F.extension(2)
    KK = PolynomialRing(FF, 'x')
    x = K.gen()

    for l in V:
        if (x - a[l]).divides(u):
            d = u.degree()
            u /= x - a[l]
            u = K(u)
            v = K(sqrt(KK(v2)))
            v2 = K(v2 + v2[2*d-2]*u**2 - 2*v[d-1]*v*u )
        else:
            d,e,f = XGCD(u, x - a[l])
            v = K(sqrt(KK(v2)))
            v2 = K(v2 + (e/d)**2*u*v2(a[l]) - 2*e/d*u*v*v(a[l]) )
            u *= x - a[l]

    return u,v2
