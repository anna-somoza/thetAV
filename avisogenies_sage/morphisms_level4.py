"""
Conversion between Mumford coordinates and theta points for level 4.

Based on the algorithms from [Coss]_.


AUTHORS:

- Anna Somoza (2021-22): initial implementation

REFERENCES:

.. [VanW] P. Van Wamelen. Equations for the Jacobian of a hyperelliptic curve.
   Trans. Am. Math. Soc, 350(8), pp.3083-3106, 1998.

.. [Coss] R. Cosset. Applications des fonctions thêta à la cryptographie sur courbes hyperelliptiques.
   PhD thesis, Université Henri Poincaré – Nancy 1, 2011.


.. todo::

    - Sort documentation by source (to maintain layout)

"""

# ****************************************************************************
#             Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#    Distributed under the terms of the GNU General Public License (GPL)
#    as published by the Free Software Foundation; either version 2 of
#    the License, or (at your option) any later version.
#                                    https://www.gnu.org/licenses/
# ****************************************************************************

from itertools import combinations, chain

from sage.arith.misc import XGCD
from sage.functions.other import floor
from sage.misc.all import prod
from sage.rings.all import PolynomialRing, ZZ, Integer
from sage.structure.element import parent

from .eta_maps import eta, eta_prime, eta_second, normalize_eta, sign_theta_normalized
from .morphisms_aux import choice_of_all_C_Cosset, constant_f, YS_fromMumford_Generic, sign_s_A, \
    prodYp_fromMumford_with2torsion, IgusaTheorem, YS_fromMumford_Delta
from .tools import rangeS

integer_types = (int, Integer)

# ***** (3) Manipulations of elements of Ep *****//


def MumfordToTheta_4_Generic(a, rac, thc, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates [x,y] of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let thc be the theta constant of level 4 associated to the curve C

    Assume that all P_i are distinct.

    Return the theta functions of level 4 associated to points.
    
    .. todo:: 
    
        - Test against Magma, add examples
        
        - Address FIXME.
    """
    if thc.level() != 4:
        raise ValueError(F'Expected level-4 theta structure.')

    g = thc.dimension()
    if len(points) != g:
        raise ValueError(F'Expected degree-{g} divisor')

    #TODO: We should try to take the polynomial ring from the parent, if possible
    K = PolynomialRing(parent(points[0][0]), 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)
    thO = thc(0)

    if any(u(elem) == 0 for elem in a):
        raise ValueError(F'Expected generic divisor')

    C = choice_of_all_C_Cosset(g)  # all other choices should give the same result
    U = {2 * x for x in range(g + 1)}
    zg = eta_second(g, range(2 * g + 1)) / 2

    idx = thc._char_to_idx
    th = [0] * 2 ** (2 * g)

    done = set()
    for S1 in chain.from_iterable(combinations(range(2 * g + 1), l) for l in [g, g + 1]):
        if eta_second(g, U.symmetric_difference(S1), normalized=True) != 0:
            continue
        for S2 in chain.from_iterable(combinations(range(2 * g + 1), l) for l in [g, g + 1]):
            if eta_prime(g, U.symmetric_difference(S2), normalized=True) != 0:
                continue

            ee = eta(g, U.symmetric_difference(S1)) + eta(g, U.symmetric_difference(S2))
            e = normalize_eta(ee)
            i = idx(e)
            if i in done:
                continue
            done.add(i)

            # we use the duplication formula. t will be the general term
            for S in chain.from_iterable(combinations(range(2 * g + 1), r) for r in range(g + 1)):
                S = frozenset(S)
                B = [S.symmetric_difference(S1).symmetric_difference(S2),
                     (S ^ U).symmetric_difference(S1), (S ^ U).symmetric_difference(S2), S]

                # we divide by f_Bi
                t = 1 / prod(constant_f(g, Bi, C[Bi]).evaluate(a, thc, rac) for Bi in B)

                # we multiply by Y_Bi'
                for Bi in B:
                    if len(Bi) == 1:
                        al = a[next(iter(Bi))]
                        t *= (-1) ** g * u(al)
                    elif 2 <= len(Bi) <= 2 * g - 1:
                        t *= YS_fromMumford_Generic(g, a, Bi, points)
                        t *= sign_s_A(g, Bi, C)
                    elif len(Bi) == 2 * g:
                        t *= prod(point[1] for point in points)
                        t *= sign_s_A(g, range(2 * g + 1), C)
                        t *= (-1) ** floor(g / 2)
                        t *= (-1) ** ZZ(eta_prime(g, C[Bi]) * zg)
                    elif len(Bi) == 2 * g + 1:
                        t *= prod(point[1] for point in points)
                        t *= sign_s_A(g, range(2 * g + 1), C)
                        t *= (-1) ** floor((g + 1) / 2)
                        t *= (-1) ** ZZ(eta_prime(g, C[frozenset()]) * zg)

                # we divide by the u(a_l)
                for l in range(2 * g + 1):
                    nb = sum(l in Bi for Bi in B)
                    try:
                        t /= ((-1) ** g * u(a[l])) ** (ZZ(nb / 2))
                    except TypeError:
                        raise ValueError('Expected even value.')  # FIXME
                # now t is theta[UoB1] * theta[UoB2] * theta[UoB3] * theta[UoB4] /t_empty(z)^4

                # the sign in the theta (we have changed the characteristic)
                for Bi in B[:-1]:
                    t *= (-1) ** ZZ(eta_prime(g, U ^ Bi) * (eta_second(g, U ^ S1) +
                                                            eta_second(g, U ^ S2) + eta_second(g, U ^ S) - eta_second(g,
                                                                                                                      U ^ Bi)) / 2)

                # the sign in the duplication formulae
                t *= (-1) ** ZZ(ee[:g] * eta_second(g, U ^ S))

                th[i] += t / 2 ** g

            # scale the theta. i.e. constants used in doubling
            for elem in [S1, S2, U]:
                eelem = eta(g, U.symmetric_difference(elem))
                th[i] *= sign_theta_normalized(eelem) / thO[idx(normalize_eta(eelem))]

            # sign when we have normalized the characteristic
            th[i] *= sign_theta_normalized(ee)

    return thc(th)


def MumfordToLevel4ThetaPoint(a, rac, thc, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^d P_i - g P_infty
    Let points be the list of coordinates [x,y] of P_i
    Let a be the x-coordinates of the Weierstrass points of the curve
    Let thc be the theta constant of level 4

    Assume that all P_i are distinct if the divisor is either theta or has a
    ramification point in its support.

    Return the theta functions of level 4 associated to points

    EXAMPLES ::

        sage: from avisogenies_sage import AnalyticThetaNullPoint
        sage: from avisogenies_sage.morphisms_level4 import MumfordToLevel4ThetaPoint
        sage: F = GF(83^2); z, = F.gens(); Fx.<X> = PolynomialRing(F)
        sage: g = 2; a = [F(0), 1, 3, 15, 20]; rac = sqrt(a[1] - a[0])
        sage: thc = [1,  37,  56, 57, 34*z + 43, 0, 50*z + 73, 0, 30, 2*z + 82, 0, 0, 16*z + 37, 0, 0, 61*z + 21]
        sage: thc = AnalyticThetaNullPoint(F, 4, g, thc)
        sage: u = (X-43)*(X-10); v = z^954*X + z^2518
        sage: points = sum(([(x, v(x))]*mult for x, mult in u.roots()), [])
        sage: th = MumfordToLevel4ThetaPoint(a, rac, thc, points); th
        (78*z2 + 13 : 77*z2 + 26 : 43*z2 + 3 : 54*z2 + 67 : 77*z2 + 61 : 35*z2 + 2 : 31*z2 + 8 :
        19*z2 + 38 : 25*z2 + 9 : z2 + 65 : 17*z2 + 75 : 18*z2 + 38 : 50*z2 + 17 : 41*z2 + 6 : 18*z2 + 48 : 39*z2 + 73)
        
    .. todo:: 
    
        - Check question in code.
        
        - Address FIXME.
    """
    if thc.level() != 4:
        raise ValueError(F'Expected level-4 theta structure.')

    g = thc.dimension()
    thO = thc(0)
    F = thc._R

    if len(points) == 0:
        return thO

    K = PolynomialRing(F, 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)  # TODO: Maybe we want to store u?

    up = u
    points_p = list(points)

    V1 = {l for l, al in enumerate(a) if up(al) == 0}

    V2 = set()
    for l, al in enumerate(a):
        if l not in V1:
            if up.degree() == g:
                break
            V2.add(l)
            up *= (x - al)
            points_p.append([al, 0])

    V = V1 | V2

    C = choice_of_all_C_Cosset(g)  # all other choices should give the same result
    U = {2 * x for x in range(g + 1)}
    zg = eta_second(g, range(2 * g + 1)) / 2

    thp = [0] * 2 ** (2 * g)

    idx = thc._char_to_idx
    done = set()
    for S1 in chain.from_iterable(combinations(range(2 * g + 1), l) for l in [g, g + 1]):
        if eta_second(g, U.symmetric_difference(S1), normalized=True) != 0:
            continue
        for S2 in chain.from_iterable(combinations(range(2 * g + 1), l) for l in [g, g + 1]):
            if eta_prime(g, U.symmetric_difference(S2), normalized=True) != 0:
                continue

            ee = eta(g, U.symmetric_difference(S1)) + eta(g, U.symmetric_difference(S2))
            e = normalize_eta(ee)
            i = idx(e)
            if i in done:
                continue
            done.add(i)

            # we use the duplication formula. t will be the general term
            for S in chain.from_iterable(combinations(range(2 * g + 1), r) for r in range(g + 1)):
                S = frozenset(S)
                B = [S.symmetric_difference(S1).symmetric_difference(S2),
                     (S ^ U).symmetric_difference(S1), (S ^ U).symmetric_difference(S2), S]

                if any(2 * len(V & Bi) > len(Bi) for Bi in B):
                    continue

                # we divide by f_Bi
                t = 1 / prod(constant_f(g, Bi, C[Bi]).evaluate(a, thc, rac) for Bi in B)

                W = V & frozenset.union(*B[:-1])  # TODO: Why not B[4]?

                if len(W) != 0:
                    # we multiply by Y_Bi'
                    t *= prodYp_fromMumford_with2torsion(g, a, B, points_p, W, C, F)

                    # we divide by the up(a_l)
                    for l in rangeS(2 * g + 1, W):
                        nb = sum(l in Bi for Bi in B)
                        try:
                            t /= ((-1) ** g * up(a[l])) ** ZZ(nb / 2)
                        except TypeError:
                            raise ValueError('Expected even value')  # FIXME

                else:
                    # we multiply by Y_Bi'
                    for Bi in B:
                        if len(Bi) == 1:
                            l = next(iter(Bi))
                            t *= (-1) ** g * up(F(a[l]))
                        elif 2 <= len(Bi) <= 2 * g - 1:
                            if len(set(points_p)) == len(points_p):
                                t *= YS_fromMumford_Generic(g, a, Bi, points_p)
                            elif len(set(points_p)) == len(points_p) - 1:
                                t *= YS_fromMumford_Delta(g, a, Bi, points_p, F)
                            else:
                                raise NotImplementedError('The case of non generic delta divisor is not implemented')
                            t *= sign_s_A(g, Bi, C)
                        elif len(Bi) == 2 * g:
                            t *= prod(point[1] for point in points_p)
                            t *= sign_s_A(g, range(2 * g + 1), C)
                            t *= (-1) ** floor(g / 2)
                            t *= (-1) ** ZZ(eta_prime(g, C[Bi]) * zg)
                        elif len(Bi) == 2 * g + 1:
                            t *= prod(point[1] for point in points_p)
                            t *= sign_s_A(g, range(2 * g + 1), C)
                            t *= (-1) ** floor((g + 1) / 2)
                            t *= (-1) ** ZZ(eta_prime(g, C[frozenset()]) * zg)

                    # we divide by the up(a_l)
                    for l in range(2 * g + 1):
                        nb = sum(l in Bi for Bi in B)
                        try:
                            t /= ((-1) ** g * u(a[l])) ** (ZZ(nb / 2))
                        except TypeError:
                            raise ValueError('Expected even value')  # FIXME
                # t is theta[UoB1] * theta[UoB2] * theta[UoB3] * theta[UoB4] /t_empty(z)^4

                # the sign in the theta (we have changed the characteristic
                es_US1 = eta_second(g, U.symmetric_difference(S1))
                es_US2 = eta_second(g, U.symmetric_difference(S2))
                es_US = eta_second(g, U ^ S)
                t *= (-1) ** ZZ(eta_prime(g, U ^ B[0]) * (es_US1 + es_US2 + es_US - eta_second(g, U ^ B[0])) / 2)
                t *= (-1) ** ZZ(eta_prime(g, U ^ B[1]) * (es_US1 + es_US - eta_second(g, U ^ B[1])) / 2)
                t *= (-1) ** ZZ(eta_prime(g, U ^ B[2]) * (es_US2 + es_US - eta_second(g, U ^ B[2])) / 2)

                # the sign in the duplication formulae
                t *= (-1) ** ZZ(ee[:g] * es_US)

                thp[i] += t / 2 ** g

            # scale the theta. i.e. constants used in doubling
            for elem in [S1, S2, U]:
                eelem = eta(g, U.symmetric_difference(elem))
                thp[i] *= sign_theta_normalized(eelem) / thO[idx(normalize_eta(eelem))]

            # sign when we have normalized the characteristic
            thp[i] *= sign_theta_normalized(ee)

    th = thc(thp)
    for l in V2:
        th = th.add_twotorsion_point(eta(g, {l}))

    return th


# ***** (7) Theta to Mumford *****//

def Ylm_fromTheta(a, rac, l, m, th, C):
    """
    Let D be a point in Jac(C)\\Theta
    D is represented by the theta functions th of level 4
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let rac be a root of a_1 - a_0
    Let C be the choice of sets in the definition of the f_A

    Compute the function Y_{l,m}
    
    .. todo::
    
        - Test against Magma, add examples.
        
        - Address FIXME.
    """
    thc = th.abelian_variety()
    g = thc.dimension()
    if l == m:
        raise ValueError(F'l(={l}) and m(={m}) have to be distinct')
    if thc.level() != 4:
        raise ValueError(f'Expected a level-4 theta structure')

    U = {2 * x for x in range(g + 1)}

    thO = thc(0)
    th_empty_4 = IgusaTheorem([eta(g, U)] * 4, [th, thO, thO, thO])

    if th_empty_4 == 0:
        raise ValueError('Divisor theta!')  # FIXME

    sets = [frozenset([l, m]), frozenset([l]), frozenset([m]), frozenset()]
    th_prod = IgusaTheorem([eta(g, U ^ S) for S in sets], [th, thO, thO, thO])

    Y = sign_s_A(g, [l, m], C)
    Y *= prod(constant_f(g, S, C[S]).evaluate(a, thc, rac) for S in sets[:-1])
    Y /= constant_f(g, set(), C[frozenset()]).evaluate(a, thc, rac) ** 3

    Y *= th_prod / th_empty_4

    return Y


def ThetaToMumford_4_Generic(a, rac, th):
    """
    Let D be a point in Jac(C)\\Theta
    D is represented by the theta functions th of level 4
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let rac be a root of a_2-a_1
    Let thc be the theta constants of level 4

    Compute the Mumford polynomials associated to D
    
    .. todo:: 
    
        - Test against Magma, add examples
        
        - Address FIXME.
    """
    thc = th.abelian_variety()
    g = thc.dimension()
    if thc.level() != 4:
        raise ValueError(f'Expected a level-4 theta structure')

    F = thc._R
    K = PolynomialRing(F, 'x')
    x = K.gen()
    a = [F(elem) for elem in a]

    U = {2 * x for x in range(g + 1)}
    C = choice_of_all_C_Cosset(g)  # all other choices should give the same result

    thO = thc(0)
    list_th = [th, thO, thO, thO]
    th_empty_4 = IgusaTheorem([eta(g, U)] * 4, list_th)

    if th_empty_4 == 0:
        raise ValueError('Divisor theta!')  # FIXME

    u_al = []
    eltE_empty = constant_f(g, set(), C[frozenset()]).evaluate(a, thc, rac)
    for l in range(g + 1):
        Sl = frozenset([l])
        th_numer = IgusaTheorem([eta(g, U ^ Sl)] * 2 + [eta(g, U)] * 2, list_th)
        val = (-1) ** g * th_numer / th_empty_4
        val *= constant_f(g, Sl, C[Sl]).evaluate(a, thc, rac) ** 2
        val /= eltE_empty ** 2
        u_al.append(val)

    u = K(0)
    for i, t in enumerate(u_al):
        t *= prod((x - a[j]) / (a[i] - a[j]) for j in range(g + 1) if j != i)
        u += t

    v_al = [F(0)] * g
    for l in range(g):
        for m in rangeS(g + 1, [l]):
            t = Ylm_fromTheta(a, rac, l, m, th, C)
            t /= prod(a[m] - a[k] for k in range(g + 1) if k not in [l, m])
            v_al[l] += t

    v = K(0)
    for i, t in enumerate(v_al):
        t *= prod((x - a[j]) / (a[i] - a[j]) for j in range(g) if j != i)
        v += t

    return u, v


def Level4ThetaPointToMumford(a, rac, th):
    """
    Let D be a point in Jac(C)
    D is represented by the theta functions th of level 4
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let rac be a root of a_1 - a_0

    Compute the Mumford polynomials associated to D
    
    .. todo:: Test against Magma, add examples
    """
    thc = th.abelian_variety()
    g = thc.dimension()

    if thc.level() != 4:
        raise ValueError(f'Expected a level-4 theta structure')

    U = {2 * x for x in range(g + 1)}

    thO = thc(0)
    thp = th

    etas = [eta(g, U)] * 4
    t_empty_p = IgusaTheorem(etas, [thp, thO, thO, thO])

    V = set()
    for l in range(2 * g + 1):
        if t_empty_p != 0:
            break
        V.add(l)
        thp = thp.add_twotorsion_point(eta(g, l))
        t_empty_p = IgusaTheorem(etas, [thp, thO, thO, thO])

    u, v = ThetaToMumford_4_Generic(a, rac, thp)
    K = parent(u)
    x = K.gen()

    for l in V:
        if (x - a[l]).divides(u):
            u /= x - a[l]
            u = K(u)
            c = v.leading_coefficient()
            v -= c * u
        else:
            d, s, _ = XGCD(u, x - a[l])
            assert d != 0
            v -= s / d * u * v(a[l])
            u *= x - a[l]

    return u, v
