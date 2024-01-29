r"""
This module defines the classes of Abelian varieties with theta structure
and Kummer variety with theta structure as abstract schemes.

Following [Mum66]_ an abelian variety `A` of dimension `g` together with a level `n` theta
structure is provided with a unique embedding `i: A \rightarrow \mathbb{P}^{n^g-1}`. The data of
the theta structure is equivalent to the data of the theta null point `i(0)`. Actually, one
of the main results of [Mum66]_ states that if `n = 4`, one can recover a complete set of
equations for `i(A)` thanks to the Riemann equations, which are parametrized by the theta null
point.

In the case that `n = 2`, since all the level two theta functions are even, the map `i: A
\rightarrow \mathbb{P}^{n^g-1}` factors through the Kummer variety `K = A/(-1)` associated to `A`.

As for computations, one looks for the most compact and efficient representation, which means that
in most instances a level `4` representation is enough. In some cases, one can find useful the
increased speed up provided by the level `2` representation, that is, working with Kummer
varieties, at the expense of loosing the group law of the abelian variety.

The main point of this module is to provide constructors for the creation of an Abelian
and Kummer variety together with a level `n` theta structure (`n=2` in case of Kummer
variety) and computing Riemann equations to represent its projective embedding and arithmetic.


AUTHORS:

- Anna Somoza (2020-22): initial implementation

"""

# *****************************************************************************
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 3 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# *****************************************************************************
from functools import partial
from itertools import product, combinations_with_replacement, accumulate

from sage.misc.mrange import cantor_product
from sage.categories.fields import Fields
from sage.rings.all import PolynomialRing, FractionField, ZZ, Zmod
from sage.rings.integer import Integer
from sage.schemes.generic.algebraic_scheme import AlgebraicScheme
from sage.schemes.generic.homset import SchemeHomset_points
from sage.schemes.generic.morphism import SchemeMorphism_point
from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.structure.element import is_Vector
from sage.structure.richcmp import richcmp_method, richcmp, op_EQ, op_NE
from sage.schemes.hyperelliptic_curves.jacobian_morphism import JacobianMorphism_divisor_class_field
from sage.misc.functional import sqrt

from . import analytic_theta_point, constructor
from . import tools
from .theta_point import VarietyThetaStructurePoint, AbelianVarietyPoint, KummerVarietyPoint

_Fields = Fields()
integer_types = (int, Integer)


@richcmp_method
class Variety_ThetaStructure(AlgebraicScheme):
    r"""
    Generic class for Varieties with theta structure. See also
    :class:`~thetAV.theta_null_point.AbelianVariety_ThetaStructure`, :class:`~thetAV.theta_null_point.KummerVariety`..

    INPUT:

    - ``R`` -- a field of definition
    - ``n`` -- an even integer; the level of the theta structure.
    - ``g`` -- an integer; the dimension of the abelian variety.
    - ``T`` - a list of length n\ :sup:`g` elements of R - the theta
      null point determining the abelian variety.
    - ``check`` (default: *False*) -- A boolean; if *True*, checks that
      the riemann relations are satisfied by the input.
    """
    _point = VarietyThetaStructurePoint

    def __init__(self, R, n, g, T):
        """
        Initialize.
        """
        if type(self) == Variety_ThetaStructure:
            raise Exception("Use either AbelianVariety or KummerVariety.")
        PP = ProjectiveSpace(R, n ** g - 1)
        # Given a characteristic x in (Z/nZ)^g its theta constant is at position ZZ(x, n)
        # Given a coordinate i, T[i] corresponds to the theta constant with characteristic
        # i.digits(n, padto=g)
        self._dimension = g
        self._level = n
        self._ng = n ** g

        AlgebraicScheme.__init__(self, PP)

        self._thetanullpoint = self.point(T)
        self._riemann = {}
        self._dual = {}
        self._with_theta_basis = {}

    def __richcmp__(self, X, op):
        """
        Compare the variety self to X.  If X is a
        variety, then self and X are equal if and only if their fields
        of definition are equal and their theta null points are equal
        as projective points.
        
        EXAMPLES ::
        
            sage: from thetAV import AbelianVariety, KummerVariety
            sage: F1 = GF(331); F2 = GF(331^2)
            sage: pt = [328 , 213 , 75 , 1]
            sage: K1 = KummerVariety(F1, 2, pt)
            sage: K2 = KummerVariety(F2, 2, pt)
            sage: K3 = KummerVariety(F1, 2, [2*F1(el) for el in pt])
            sage: K1 == K2
            False
            sage: K1 == K3
            True
            sage: pt2 = [68, 33, 46, 33, 29, 77, 81, 16, 8, 67, 48, 67, 29, 16, 81, 77]
            sage: A = AbelianVariety(F1, 4, 2, pt2)
            sage: A == K1
            False
            
        """
        if not isinstance(X, Variety_ThetaStructure):
            return NotImplemented
        if self.base_ring() != X.base_ring():
            return False
        a, b = self.theta_null_point(), X.theta_null_point()
        if op in [op_EQ, op_NE]:
            for i in range(len(a)):
                for j in range(i + 1, len(a)):
                    if a[i] * b[j] != a[j] * b[i]:
                        return not (op == op_EQ)
            return op == op_EQ
        return richcmp(list(a), list(b), op)

    def dimension(self):
        """
        Return the dimension of this variety.
        """
        return self._dimension

    def level(self):
        """
        Return the level of the theta structure.
        
        TEST ::
            
            sage: from thetAV import KummerVariety
            sage: F = GF(331)
            sage: K = KummerVariety(F, 2, [328 , 213 , 75 , 1])
            sage: K.level()
            2
            sage: from thetAV import AbelianVariety
            sage: n = 2*randint(2,5); g = randint(2,5)
            sage: T = [randint(1, 331) for _ in range(n^g)]
            sage: A = AbelianVariety(F, n, g, T)
            sage: A.level() == n
            True

        """
        return self._level

    def __len__(self):
        """
        Return the length of the coordinate vector.
        """
        return self._ng

    def __getitem__(self, n):
        """
        Return the n-th coordinate of this point.
        """
        return self._thetanullpoint[n]

    def __iter__(self):
        """
        Return the coordinates of this point as a list.
        """
        return iter(self._thetanullpoint)

    def theta_null_point(self):
        """
        Return the theta null point as a point of the variety.
        """
        return self._thetanullpoint

    def change_ring(self, R):
        """
        Not implemented for a general variety.
        """
        raise NotImplementedError

    def base_extend(self, R):
        """
        Return the natural extension of self over R.
        """
        if R not in _Fields:
            raise TypeError(f"Argument (={R}) must be a field.")
        if self.base_ring() is R:
            return self
        if not R.has_coerce_map_from(self.base_ring()):
            raise ValueError(f"No natural map from the base ring (={self.base_ring()}) to R (={R})!")
        return self.change_ring(R)

    def _point_homset(self, *args, **kwds):
        return SchemeHomset_points(*args, **kwds)

    def point(self, P, **kwds):
        """
        Create a point.

        INPUT:

        - ``v`` -- anything that defines a point in a variety
          with theta structure. See :class:`~thetAV.theta_point.VarietyPoint`
          for details.

        - ``check`` -- boolean (optional, default: *False*); if *True*,
          check that the riemann relations are satisfied.

        OUTPUT:

        A point of the scheme.

        """
        if isinstance(P, JacobianMorphism_divisor_class_field):
            match self.level():
                case 2:
                    kwds['basis'] = 'F(2,2)^2'
                case 4:
                    kwds['basis'] = 'F(2,2)'
                case _:
                    raise NotImplementedError("Point from divisor only available for level 2 and 4.")
        label = kwds.pop('basis', None)
        if label is not None and label != 'Fn': #Classical basis
            A = self.with_theta_basis(label)
            AP = A(P)
            return AP.to_algebraic(A=self, **kwds)
        return self._point(self, P, **kwds)

    __call__ = point

    def with_theta_basis(self, *data, **kwargs):
        """
        Compute the representation of the thetanullpoint in the given basis of the space of theta functions.

        Possible values are:

        - 'F(n)'
        - 'F(2,2)', for level 4
        - 'F(2,2)^2', for level 2
        - 'classical', corresponds to 'F(2,2)' or 'F(2,2)^2' depending on the level of self.

        The method saves the already-computed values in the private variable _with_theta_basis.

        It can also be used as the constructor for the thetanullpoint using other representations, see
        :func:`~thetAV.constructor._with_theta_basis`

        EXAMPLES::

            sage: from thetAV import AbelianVariety, KummerVariety
            sage: F.<z2> = GF(19^2)
            sage: A = AbelianVariety(F, 4, 2, (5*z2 + 7 , 6*z2 + 8 , 6*z2 + 5 , 6*z2 + 8 , z2 + 13 , 4*z2 + 12 , 14*z2 + 11 , 11*z2 + 9 , 11*z2 + 6 , 6*z2 + 14 , 16*z2 + 5 , 6*z2 + 14 , z2 + 13 , 11*z2 + 9 , 14*z2 + 11 , 4*z2 + 12), check=True)
            sage: A.with_theta_basis('classical')
            (1 : 8*z2 + 15 : 15*z2 + 5 : z2 + 5 : 6*z2 + 11 : 0 : 16 : 0 : 17*z2 + 12 : 3*z2 + 1 : 0 : 0 : 17*z2 + 1 : 0 : 0 : 6*z2 + 11)
            sage: K1 = KummerVariety(GF(331), 2, [328,213,75,1])
            sage: K1.with_theta_basis('F(2,2)^2')
            (173 : 327 : 8 : 163 : 49 : 0 : 305 : 0 : 325 : 112 : 0 : 0 : 42 : 0 : 0 : 286)

        """
        if type(self) == str:
            from .constructor import _with_theta_basis
            return _with_theta_basis(self, *data, **kwargs)
        label = data[0]
        try:
            return self._with_theta_basis[label]
        except KeyError:
            pass
        if label == 'Fn':
            return self
        if label not in ['classical', 'F(2,2)', 'F(2,2)^2']:
            raise ValueError(f'The basis {label} is either not implemented or unknown.')

        n = self.level()
        g = self.dimension()
        O = self.theta_null_point()
        D = self._D
        point = [0] * (4 ** g)
        R = self.base_ring()

        if n == 2:
            if label == 'F(2,2)':
                raise ValueError(f'The basis {label} should be of level {n}.')
            for (idxa, a), (idxb, b) in product(enumerate(D), repeat=2):
                point[idxa + 2 ** g * idxb] = sum(
                    (-1) ** ZZ(a * beta) * O[b + beta] * O[idxbeta] for idxbeta, beta in enumerate(D)) / 2 ** g
            th = analytic_theta_point.AnalyticThetaNullPoint(R, n, g, point)
            self._with_theta_basis[label] = th
            return th

        if n == 4:
            if label == 'F(2,2)^2':
                raise ValueError(f'The basis {label} should be of level {n}.')
            twotorsion = self._twotorsion  # Zmod(2)^g
            for (idxa, a), (idxb, b) in product(enumerate(twotorsion), repeat=2):
                Db = D(list(b))
                point[idxa + 2 ** g * idxb] = sum(
                    (-1) ** ZZ(a * beta) * O[Db + beta] for beta in twotorsion) / 2 ** g
            th = analytic_theta_point.AnalyticThetaNullPoint(R, n, g, point)
            self._with_theta_basis[label] = th
            return th

        raise NotImplementedError

    def riemann_relation(self, *data):
        """
        Returns the indices appearing in the Riemann relation associated to a given triple chi, i, j.
        If it has not been computed, it computes it and stores it in the private variable _riemann.

        INPUT:

        Either 3 variables

        -  ``chi`` -- a character, given by its dual element in Z(2) as a subset of Z(n).

        -  ``i`` -- the index of a coordinate of P. For now we are assuming that they are an
           element of Zmod(n)^g.

        -  ``j`` -- the index of a coordinate of P. For now we are assuming that they are an
           element of Zmod(n)^g.

        Or a triple of 3 integers, the integer representation of ``chi``, ``i`` and ``j``.

        EXAMPLES:

            sage: #TODO examples

        """
        P0 = self.theta_null_point()
        idx = partial(tools.idx, n=self.level())
        D = self._D
        twotorsion = self._twotorsion
        match data:
            case [(idxchi, idxi, idxj)] | [[idxchi, idxi, idxj]]:
                i = D[idxi]
                j = D[idxj]
                chi = twotorsion[idxchi]
            case chi, i, j:
                idxchi = tools.idx(chi, n=2)
                idxi = idx(i)
                idxj = idx(j)
            case _:
                raise TypeError("Input should be a tuple of length 3 or 3 elements.")

        DD = [2 * d for d in D]
        i, j, tij = tools.reduce_twotorsion_couple(i, j)
        # we try to find k and l to apply the addition formulas such that
        # we can reuse the maximum the computations
        # for a differential addition, i == j (generically) and we take k = l = 0
        # for a normal addition we have j = 0, so we take k = i, l = j.
        k0, l0 = (D(0), D(0)) if i == j else (i, j)

        for u, v in product(D, D):
            if u + v not in DD:
                continue
            k, l, _ = tools.reduce_symtwotorsion_couple(k0 + u, l0 + v)
            el = (idxchi, idx(k), idx(l))
            if el not in self._dual:
                self._dual[el] = sum(tools.eval_car(chi, t) * P0[k + t] * P0[l + t] for t in twotorsion)
            if self._dual[el] != 0:
                kk = k0 + u
                ll = l0 + v
                break
        else:  # If we leave the for loop without encountering a break
            for t in twotorsion:
                self._riemann[(idxchi, idx(i + t), idx(j + t))] = []
            return []
        kk0, ll0, tkl = tools.reduce_symtwotorsion_couple(kk, ll)
        i2, j2, k2, l2 = tools.get_dual_quadruplet(i, j, kk, ll)
        i20, j20, tij2 = tools.reduce_twotorsion_couple(-i2, j2)
        k20, l20, tkl2 = tools.reduce_twotorsion_couple(k2, l2)
        for t in twotorsion:
            self._riemann[(idxchi, idx(i + t), idx(j + t))] = [i, j, kk0, ll0, i20, j20, k20, l20, t + tkl + tij2 + tkl2]
        return self._riemann[(idxchi, idxi, idxj)]

    def _addition_formula(self, P, Q, L):
        """
        Given two points P and Q and a list L containing integer triplets [idxchi, idxi, idxj]
        compute
        `\\sum_{t \\in Z(2)} \\chi(t) (P+Q)_{i + t} (P-Q)_{j + t}`
        for every given triplet.

        TESTS::

            sage: from thetAV import *
            sage: F.<z2> = GF(19^2)
            sage: A = AbelianVariety(F, 4, 2, (5*z2 + 7 , 6*z2 + 8 , 6*z2 + 5 , 6*z2 + 8 , z2 + 13 , 4*z2 + 12 , 14*z2 + 11 , 11*z2 + 9 , 11*z2 + 6 , 6*z2 + 14 , 16*z2 + 5 , 6*z2 + 14 , z2 + 13 , 11*z2 + 9 , 14*z2 + 11 , 4*z2 + 12), check=True)
            sage: A._addition_formula(A(0), A(0), [(1,8,7)])
            {(1, 0, 15): 11, (1, 2, 13): 8, (1, 8, 7): 11, (1, 10, 5): 8}

        """
        twotorsion = self._twotorsion
        idx = partial(tools.idx, n=self.level())
        r = {}
        for el in L:
            if el in r:
                continue
            # Are we sure that this pair (i,j) is reduced as in riemann? Or it is not done like that? check.
            IJ = self.riemann_relation(el)
            if not len(IJ):
                raise ValueError(
                    "Can't compute the addition! Either we are in level 2 and computing a normal addition, or a differential addition with null even theta null points.")
            ci0, cj0 = IJ[:2]
            k0, l0 = map(idx, IJ[2:4])
            ci20, cj20 = IJ[4:6]
            ck20, cl20 = IJ[6:8]
            tt = IJ[8]

            chi = twotorsion(el[0])

            s1 = sum(tools.eval_car(chi, t) * Q[ci20 + t] * Q[cj20 + t] for t in twotorsion)
            s2 = sum(tools.eval_car(chi, t) * P[ck20 + t] * P[cl20 + t] for t in twotorsion)
            A = self._dual[(el[0], k0, l0)]
            S = tools.eval_car(chi, tt) * s2 * s1 / A
            for t in twotorsion:
                r[(el[0], idx(ci0 + t), idx(cj0 + t))] = tools.eval_car(chi, t) * S
        return r

    def isogeny(self, l, basis, R=list(), check=True):
        """
        Given the basis of an isotropic subgroup B of the l-torsion of A, compute
        the thetanullpoints of the isogenous abelian variety A/B. Moreover, given a list of points R, it computes the
        image of these points via the isogeny.

        EXAMPLE::

            sage: #TODO examples

        """
        F = self.base_ring()
        g = self.dimension()
        ng = self._ng
        r = len(R) + 1

        pts = []
        deltas = []
        for i, ei in enumerate(basis):
            Re = [(P + ei)[0] for P in R]
            Be = [(ei + ej)[0] for ej in basis[i + 1:]]
            pts.append([ei] + Re + Be)
            deltas += ei.compatible_lift(l, R, Re)
            deltas += [eij.compatible_lift(l) for eij in Be]

        S = PolynomialRing(F, len(deltas), 'mu')
        mus = S.gens()
        T = S.quotient([mu ** l - delta for mu, delta in zip(mus, deltas)])
        AT = self.change_ring(T)

        idx = partial(tools.idx, n=l)
        Zl = Zmod(l) ** g
        B = Zl.basis()
        Bidx = [idx(e) for e in B]
        lg = l ** g

        support = [range(l)] * g + [range(r)]
        rows = list(accumulate((len(lst) for lst in pts)))

        K = [[None] * lg for i in range(r)]
        # The cantor_product iterator guarantees that when we reach a certain element
        # all the sub-sums are already initialized
        for *lst, j in cantor_product(*support):
            idxe = idx(lst)
            e = Zl(lst)
            ite = (i for i, t in enumerate(lst) if t)
            if e == 0:
                K[j][0] = AT(0) if j == 0 else AT(R[j - 1])
                continue
            i0 = next(ite)  # first non-zero element
            if e in B:  # i0 will be the index of the element in the basis
                rowi0 = rows[i0 - 1] if i0 != 0 else 0
                K[j][idxe] = AT(pts[i0][j]).scale(mus[rowi0 + j])
                continue
            k = next((i for i, t in enumerate(lst) if t > 1), None)
            if k is None:  # all elements are 0 or 1, and sum is at least 2
                i1 = next(ite)
                if j == 0 and next(ite, None) is None:  # we only have two ones, so it's still given in the input
                    rowi0 = rows[i0 - 1] if i0 != 0 else 0  # i0 < i1 by definition
                    ij = r + i1 - i0 - 1
                    K[0][idxe] = AT(pts[i0][ij]).scale(mus[rowi0 + ij])
                    continue
                e0, e1 = B[i0], B[i1]
                idx0, idx1 = Bidx[i0], Bidx[i1]
                K[j][idxe] = K[0][idx0].three_way_add(K[0][idx1], K[j][idx(e - e0 - e1)], K[0][idx(e0 + e1)],
                                                      K[j][idx(e - e0)], K[j][idx(e - e1)])
                continue
            ek = B[k]
            idxk = Bidx[k]
            K[j][idxe] = K[j][idx(e - ek)].diff_add(K[0][idxk], K[j][idx(e - 2 * ek)])

        img = []
        for j in range(r):
            imgr = [0] * ng
            for i in range(ng):
                imgr[i] = sum(el[i] ** l for el in K[j]).lift()
            img.append(imgr)

        fA = constructor.AbelianVariety(F, self.level(), g, img[0])
        fR = [fA(el, check=check) for el in img[1:]]
        return fA, fR


@richcmp_method
class AbelianVariety_ThetaStructure(Variety_ThetaStructure):
    r"""
    Class for Abelian Varieties with theta structure. See also
    :func:`~thetAV.constructor.AbelianVariety`.

    INPUT:

    - ``R`` -- a field of definition
    - ``n`` -- an even integer >= 4; the level of the theta structure.
    - ``g`` -- an integer; the dimension of the abelian variety.
    - ``T`` - a list of length n\ :sup:`g` elements of R - the theta
      null point determining the abelian variety.
    - ``check`` (default: *False*) -- A boolean; if *True*, checks that
      the riemann relations are satisfied by the input.

    EXAMPLES::

        sage: from thetAV import AbelianVariety
        sage: FF2 = GF(10753)
        sage: A2 = AbelianVariety(FF2, 4, 1, [732,45,98,7]); A2
        Abelian variety of dimension 1 with theta null point (732 : 45 : 98 : 7) defined over Finite Field of size 10753
        
    """
    _point = AbelianVarietyPoint

    def __init__(self, R, n, g, T, check=False):
        """
        Initialize.
        """
        if n % 2 != 0 or n < 4:
            raise ValueError(f"n={n} has to be an even number >= 4.")
        if is_Vector(T):
            T = list(T)
        if not isinstance(T, (list, tuple, SchemeMorphism_point)):
            raise TypeError(f"Argument (T={T}) must be a list, a tuple, a vector or a point.")
        if not isinstance(n, integer_types + (Integer,)):
            raise TypeError(f"Argument (n={n}) must be an integer.")
        if not isinstance(g, integer_types + (Integer,)):
            raise TypeError(f"Argument (g={g}) must be an integer.")
        if len(T) != n ** g:
            raise ValueError(f"T={T} must have length n^g={n ** g}.")

        T = tuple(R(a) for a in T)

        D, twotorsion = tools.create_indexing(n, g)

        if check:
            from .tools import idx
            idx = partial(tools.idx, n=n)
            dual = {}
            DD = [2 * d for d in D]

            if any(T[idx(-i)] != val for i, val in zip(D, T)):
                raise ValueError('The given list does not define a valid thetanullpoint')

            for (idxi, i), (idxj, j) in product(enumerate(D), repeat=2):
                ii, jj, tt = tools.reduce_twotorsion_couple(i, j)
                for idxchi, chi in enumerate(twotorsion):
                    el = (idxchi, idx(ii), idx(jj))
                    if el not in dual:
                        dual[el] = sum(tools.eval_car(chi, t) * T[idx(ii + t)] * T[idx(jj + t)] for t in twotorsion)
                    dual[(idxchi, idxi, idxj)] = tools.eval_car(chi, tt) * dual[el]

            for elem in combinations_with_replacement(combinations_with_replacement(enumerate(D), 2), 2):
                ((idxi, i), (idxj, j)), ((idxk, k), (idxl, l)) = elem
                if i + j + k + l in DD:
                    m = D([ZZ(x) / 2 for x in i + j + k + l])
                    for idxchi in range(len(twotorsion)):
                        el1 = (idxchi, idxi, idxj)
                        el2 = (idxchi, idxk, idxl)
                        el3 = (idxchi, idx(m - i), idx(m - j))
                        el4 = (idxchi, idx(m - k), idx(m - l))
                        if dual[el1] * dual[el2] != dual[el3] * dual[el4]:
                            raise ValueError('The given list does not define a valid thetanullpoint')
            self._dual = dual
        else:
            self._dual = None

        self._D = D
        self._twotorsion = twotorsion
        Variety_ThetaStructure.__init__(self, R, n, g, T)
        self._eqns = None

    def _repr_(self):
        """
        Return a string representation of this abelian variety.
        """
        return f"Abelian variety of dimension {self.dimension()} with theta null point {self.theta_null_point()} defined over {self.base_ring()}"

    def change_ring(self, R):
        r"""
        Return the abelian variety with field of definition R.
        """
        return AbelianVariety_ThetaStructure(R, self.level(), self.dimension(), self.theta_null_point())

    def equations(self):
        """
        Returns a list of defining equations for the abelian variety.

        EXAMPLES::

            sage: #TODO examples

        """
        print("Hello")
        if self._eqns is not None:
            return self._eqns
        F = self.base_ring()
        R = PolynomialRing(F, 'x', self._ng)
        FF = FractionField(R)
        x = R.gens()
        A = self.change_ring(FF)
        P = A.point(x, FF)
        D = self._D
        DD = [2 * d for d in D]
        twotorsion = self._twotorsion
        O = self.theta_null_point()

        eqns = []
        for elem in product(enumerate(D), repeat=4):
            (idxi, i), (idxj, j), (idxk, k), (idxl, l) = elem
            if i + j + k + l in DD:
                m = D([ZZ(x) / 2 for x in i + j + k + l])
                for idxchi, chi in enumerate(twotorsion):
                    Pel1 = sum(tools.eval_car(chi, t) * P[i + t] * P[j + t] for t in twotorsion)
                    Pel4 = sum(tools.eval_car(chi, t) * P[m - k + t] * P[m - l + t] for t in twotorsion)
                    Oel2 = sum(tools.eval_car(chi, t) * O[k + t] * O[l + t] for t in twotorsion)
                    Oel3 = sum(tools.eval_car(chi, t) * O[m - i + t] * O[m - j + t] for t in twotorsion)
                    eq = Pel1 * Oel2 - Oel3 * Pel4
                    if eq != 0 and eq not in eqns:
                        eqns.append(eq)
                        if len(eqns) == stop:
                            return eqns
        if eqns == [0]:
            eqns = []
        self._eqns = eqns
        return eqns


@richcmp_method
class KummerVariety(Variety_ThetaStructure):
    r"""
    Class for Kummer Varieties with theta structure.

    INPUT:

    - ``R`` -- a field of definition
    - ``n`` -- an integer; the level of the theta structure.
    - ``g`` -- an integer; the dimension of the kummer variety.
    - ``T`` - a list of length n\ :sup:`g` elements of R - the theta
      null point determining the kummer variety.

    EXAMPLES::

        sage: from thetAV import KummerVariety
        sage: FF1 = GF(331)
        sage: K1 = KummerVariety(FF1, 2, [328,213,75,1]); K1
        Kummer variety of dimension 2 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
        
    """
    _point = KummerVarietyPoint
    _level = 2

    def __init__(self, R, g, T):
        """
        Initialize.
        """
        n = 2

        if is_Vector(T):
            T = list(T)
        if not isinstance(T, (list, tuple, SchemeMorphism_point)):
            raise TypeError(f"Argument (T={T}) must be a list, a tuple, a vector or a point.")
        if not isinstance(n, integer_types + (Integer,)):
            raise TypeError(f"Argument (n={n}) must be an integer.")
        if not isinstance(g, integer_types + (Integer,)):
            raise TypeError(f"Argument (g={g}) must be an integer.")
        if len(T) != n ** g:
            raise ValueError(f"T={T} must have length 2^g={n ** g}.")

        T = tuple(R(a) for a in T)

        twotorsion = tools.create_indexing(n, g, False)

        Variety_ThetaStructure.__init__(self, R, n, g, T)

        self._D = twotorsion
        self._twotorsion = twotorsion
        self._eqns = None

    def _repr_(self):
        """
        Return a string representation of this abelian variety.
        """
        return f"Kummer variety of dimension {self.dimension()} with theta null point {self.theta_null_point()} defined over {self.base_ring()}"

    def change_ring(self, R):
        r"""
        Return the kummer variety with field of definition R.
        """
        return KummerVariety(R, self.dimension(), self.theta_null_point())

    def equations(self):
        """
        Returns a list of defining equations for the abelian variety.

        If the theta null point has dimension 2 and level 2, these are
        the equations as given by Gaudry in [Gaud]_. In that case, it assumes that the
        genericity conditions are satisfied (see [Gaud]_ for details).

        Otherwise, these are computed using the Riemann relations.

        EXAMPLES::

            sage: #TODO examples

        """
        if self._eqns is not None:
            return self._eqns
        if self._dimension != 2:
            raise NotImplementedError
        O = self.with_theta_basis('F(2,2)^2')
        idx = partial(tools.idx, n=2)
        a2 = O[idx([0,0,0,0])]
        b2 = O[idx([0,0,1,1])]
        c2 = O[idx([0,0,1,0])]
        d2 = O[idx([0,0,0,1])]
        A2 = (a2 + b2 + c2 + d2)
        B2 = (a2 + b2 - c2 - d2)
        C2 = (a2 - b2 + c2 - d2)
        D2 = (a2 - b2 - c2 + d2)
        abcd = sqrt(a2*b2*c2*d2)
        E = abcd * A2 * B2 * C2 * D2 / (
                (a2 * d2 - b2 * c2) * (a2 * c2 - b2 * d2) * (a2 * b2 - c2 * d2))
        F = (a2 ** 2 - b2 ** 2 - c2 ** 2 + d2 ** 2) / (a2 * d2 - b2 * c2)
        G = (a2 ** 2 - b2 ** 2 + c2 ** 2 - d2 ** 2) / (a2 * c2 - b2 * d2)
        H = (a2 ** 2 + b2 ** 2 - c2 ** 2 - d2 ** 2) / (a2 * b2 - c2 * d2)

        FF = abcd.parent()
        R = PolynomialRing(FF, 4, 'x')
        x, y, z, t = R.gens()
        self._eqns = [
            x ** 4 + y ** 4 + z ** 4 + t ** 4 + 2 * E * x * y * z * t - F * (x ** 2 * t ** 2 + y ** 2 * z ** 2) - G * (
                    x ** 2 * z ** 2 + y ** 2 * t ** 2) - H * (x ** 2 * y ** 2 + z ** 2 * t ** 2)]
        return self._eqns
