"""
This module defines the classes of Abelian varieties with theta structure
and Kummer variety with theta structure as an abstract schemes.

Following [Mum66] an abelian variety $A$ dimension $g$ together with a level $n$ theta
structure is provided with a unique embedding $i: A \rightarrow P^{n^g-1}$. The data of
the theta structure is equalent to the data of the theta null point $i(0)$. Actually,
one of the main results of [Mum66] states that if $n \eq 4$, 
one can recover a complete set of equations for $i(A)$ thanks to
Riemann equations which are parametrized by the theta null point.

AUTHORS:

- Anna Somoza (2020-22): initial implementation

REFERENCES:

.. [Gaud] P. Gaudry. Fast genus 2 arithmetic based on theta functions.
   J. Math. Cryptol. 1 (3) (2007) 243–265.

.. [Mum66] D. Mumford. On the equations defining abelian varieties. I. Invent. Math.,
237-354, 1966.

.. [Mum67a] D. Mumford. On the equations defining abelian varieties. II. Invent. Math.,
75-135, 1967.


.. todo::

    - Add more info to the paragraph above

    - Change coefficients in examples to be powers of gen?

    - Can we use equations to generate random points?

"""

# *****************************************************************************
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from itertools import product, combinations_with_replacement

from sage.arith.misc import two_squares, four_squares
from sage.categories.fields import Fields
from sage.matrix.all import matrix, column_matrix, identity_matrix
from sage.rings.all import Zmod, PolynomialRing, FractionField, mod, ZZ
from sage.rings.integer import Integer
from sage.schemes.generic.algebraic_scheme import AlgebraicScheme
from sage.schemes.generic.homset import SchemeHomset_points
from sage.schemes.generic.morphism import SchemeMorphism_point
from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.structure.element import is_Vector
from sage.structure.richcmp import richcmp_method, richcmp, op_EQ, op_NE

from .theta_point import VarietyThetaStructurePoint, AbelianVarietyPoint, KummerVarietyPoint
from .tools import reduce_twotorsion_couple, reduce_symtwotorsion_couple, eval_car, get_dual_quadruplet, \
    evaluate_formal_points

_Fields = Fields()
integer_types = (int, Integer)


@richcmp_method
class Variety_ThetaStructure(AlgebraicScheme):
    r"""
    Generic class for Varieties with theta structure. See also
    :func:`~avisogenies_sage.theta_null_point.AbelianVariety_ThetaStructure`, :class:`~avisogenies_sage.theta_null_point.KummerVariety`..

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

    def __richcmp__(self, X, op):
        """
        Compare the variety self to X.  If X is a
        variety, then self and X are equal if and only if their fields
        of definition are equal and their theta null points are equal
        as projective points.
        
        EXAMPLES ::
        
            sage: from avisogenies_sage import AbelianVariety, KummerVariety
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
            
            sage: from avisogenies_sage import KummerVariety
            sage: F = GF(331)
            sage: K = KummerVariety(F, 2, [328 , 213 , 75 , 1])
            sage: K.level()
            2
            sage: from avisogenies_sage import AbelianVariety
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

    def point(*args, **kwds):
        """
        Create a point.

        INPUT:

        - ``v`` -- anything that defines a point in a variety
          with theta structure. See :class:`~avisogenies_sage.theta_point.VarietyPoint`
          for details.

        - ``check`` -- boolean (optional, default: *False*); if *True*,
          check that the riemann relations are satisfied.

        OUTPUT:

        A point of the scheme.

        """
        self = args[0]
        return self._point(*args, **kwds)

    __call__ = point

    def _idx_to_char(self, idx, twotorsion=False):
        r"""
        Return the characteristic in ``D`` that corresponds to a given
        integer index.

        INPUT:

        - ``idx`` -- an integer between 0 and n\ :sup:`g` - 1.
        - ``twotorsion`` -- a boolean (default: *False*). If *True*, return
          an element of twotorsion `= Zmod(2)^g`, where g is the dimension
          of self. Otherwise, return an element of D = Zmod(n)^g, where
          n is the level of self.

        ..todo::

            - Make public?

            - rename?

            - Examples

        """
        g = self._dimension
        if twotorsion:
            n = 2
            universe = self._twotorsion
        else:
            n = self._level
            universe = self._D
        if idx < 0 or idx >= n ** g:
            raise ValueError(f"The integer idx = {idx} does not represent a valid element of D = {universe}")
        return universe(ZZ(idx).digits(n, padto=g))

    def _char_to_idx(self, c, twotorsion=False):
        """
        Return the integer index that corresponds to a given characteristic in ``D``.

        """
        n = 2 if twotorsion else self._level
        return ZZ(list(c), n)

    def riemann_relation(self, *data):
        """
        Returns the riemann relation associated to a given triple chi, i, j. If it is not computed,
        it computes it and stores it in the private variable _riemann.

        INPUT:

        Either 3 variables

        -  ``chi`` -- a character, given by its dual element in Z(2) as a subset of Z(n).

        -  ``i`` -- the index of a coordinate of P. For now we are assuming that they are an
           element of Zmod(n)^g.

        -  ``j`` -- the index of a coordinate of P. For now we are assuming that they are an
           element of Zmod(n)^g.

       Or a triple of 3 integers, the integer representation of ``chi``, ``i`` and ``j``.

        .. todo::

            - Check change with David.

            - Rename?

            - If we only want the addition of the two-torsion elements, why not store _riemann only with that? see _addition_formula

            - Private or public?

        """
        idx = self._char_to_idx
        char = self._idx_to_char
        P0 = self.theta_null_point()
        if len(data) == 1:
            try:
                return self._riemann[tuple(data[0])]
            except KeyError:
                idxchi, idxi, idxj = data[0]
                i = char(idxi)
                j = char(idxj)
                chi = char(idxchi, True)
        elif len(data) == 3:
            chi, i, j = data
            idxchi = idx(chi, True)
            idxi = idx(i)
            idxj = idx(j)
            try:
                return self._riemann[(idxchi, idxi, idxj)]
            except KeyError:
                pass
        else:
            raise TypeError("Input should be a tuple of length 3 or 3 elements.")

        D = self._D
        DD = [2 * d for d in D]
        twotorsion = self._twotorsion
        i, j, tij = reduce_twotorsion_couple(i, j)
        # we try to find k and l to apply the addition formulas such that
        # we can reuse the maximum the computations
        # for a differential addition, i == j (generically) and we take k = l = 0
        # for a normal addition we have j = 0, so we take k = i, l = j.
        if i == j:
            k0 = D(0)
            l0 = D(0)
        else:
            k0 = i
            l0 = j

        for u, v in product(D, D):
            if u + v not in DD:
                continue
            k, l, _ = reduce_symtwotorsion_couple(k0 + u, l0 + v)
            el = (idxchi, idx(k), idx(l))
            if el not in self._dual:
                self._dual[el] = sum(eval_car(chi, t) * P0[idx(k + t)] * P0[idx(l + t)] for t in twotorsion)
            if self._dual[el] != 0:
                kk = k0 + u
                ll = l0 + v
                break
        else:  # If we leave the for loop without encountering a break
            for t in twotorsion:
                self._riemann[(idxchi, idx(i + t), idx(j + t))] = []
            return []
        kk0, ll0, tkl = reduce_symtwotorsion_couple(kk, ll)
        i2, j2, k2, l2 = get_dual_quadruplet(i, j, kk, ll)
        i20, j20, tij2 = reduce_twotorsion_couple(-i2, j2)
        k20, l20, tkl2 = reduce_twotorsion_couple(k2, l2)
        for t in twotorsion:
            self._riemann[(idxchi, idx(i + t), idx(j + t))] = [i, j, t, kk0, ll0, tkl, i20, j20, tij2, k20, l20,
                                                               tkl2]  # DIFF Maybe we only need to store the sum of all twotorsion.
        return self._riemann[(idxchi, idxi, idxj)]

    def _addition_formula(self, P, Q, L):
        """
        Given two points P and Q and a list L containing triplets [chi, i, j]
        compute
        `\\sum_{t \\in Z(2)} \\chi(t) (P+Q)_{i + t} (P-Q)_{j + t}`
        for every given triplet.

        .. todo::

            - Add tests.

        """
        twotorsion = self._twotorsion
        idx = self._char_to_idx
        char = self._idx_to_char
        r = {}
        for el in L:
            if el in r:
                continue
            IJ = self.riemann_relation(
                el)  # Are we sure that this pair (i,j) is reduced as in riemann? Or it is not done like that? check.
            if not len(IJ):
                raise ValueError(
                    "Can't compute the addition! Either we are in level 2 and computing a normal addition, or a differential addition with null even theta null points.")
            ci0, cj0 = IJ[0:2]
            k0, l0 = map(idx, IJ[3:5])
            ci20, cj20 = IJ[6:8]
            ck20, cl20 = IJ[9:11]
            tt = IJ[2] + IJ[5] + IJ[8] + IJ[11]  # If we only want the addition, why not store _riemann only with that?

            chi = char(el[0], True)

            s1 = sum(eval_car(chi, t) * Q[idx(ci20 + t)] * Q[idx(cj20 + t)] for t in twotorsion)
            s2 = sum(eval_car(chi, t) * P[idx(ck20 + t)] * P[idx(cl20 + t)] for t in twotorsion)
            A = self._dual[(el[0], k0, l0)]
            S = eval_car(chi, tt) * s2 * s1 / A
            for t in twotorsion:
                r[(el[0], idx(ci0 + t), idx(cj0 + t))] = eval_car(chi, t) * S
        return r

    def isogeny(self, l, basis):
        """
        basis : list containing a basis of the kernel and the addition of x1 to all the other points
        l: torsion int
        """
        F = self.base_ring()
        g = self.dimension()
        deltas = [pt.compatible_lift(l) for pt in basis]

        # This is part of the input. When done with a formal point we obtain the expression for the isogeny
        P0 = self.theta_null_point()
        P0B = [0] * self._ng
        S = PolynomialRing(F, len(deltas), 'mu')
        mus = S.gens()
        T = S.quotient([mu ** l - delta for mu, delta in zip(mus, deltas)])
        AT = self.change_ring(T)
        K_compatible = [AT(pt).scale(mu) for mu, pt in zip(mus, basis)]

        # TODO check if it is more efficient to use the idx technique we use everywhere else
        K = {tuple([0] * g): P0}
        for i in range(g):
            ei = [0] * g
            ei[i] = 1
            K[tuple(ei)] = K_compatible[i]
            if i != 0:
                ei[0] = 1
                K[tuple(ei)] = K_compatible[g + i - 1]

        if self.dimension() != 2:
            raise NotImplementedError
        compP, compQ, compPQ = K_compatible
        for i, j in product(range(l), repeat=g):
            if (i, j) in K.keys():
                continue
            try:
                compjQ, compPjQ = K[(0, j)], K[(1, j)]
            except KeyError:
                K[(1, j)], K[(0, j)] = compQ.diff_multadd(ZZ(j), compPQ, compP)
                compjQ, compPjQ = K[(0, j)], K[(1, j)]
            if i != 1:
                K[(i, j)], K[(i, 0)] = compP.diff_multadd(ZZ(i), compPjQ, compjQ)
        for idx in range(len(self)):
            P0B[idx] = sum(el[idx] ** l for el in K.values()).lift()
        if self.level() == 2:
            return KummerVariety(F, g, P0B, check=True)
        return AbelianVariety_ThetaStructure(F, self.level(), g, P0B, check=True)


@richcmp_method
class AbelianVariety_ThetaStructure(Variety_ThetaStructure):
    r"""
    Class for Abelian Varieties with theta structure. See also
    :func:`~avisogenies_sage.constructor.AbelianVariety`.

    INPUT:

    - ``R`` -- a field of definition
    - ``n`` -- an even integer >= 4; the level of the theta structure.
    - ``g`` -- an integer; the dimension of the abelian variety.
    - ``T`` - a list of length n\ :sup:`g` elements of R - the theta
      null point determining the abelian variety.
    - ``check`` (default: *False*) -- A boolean; if *True*, checks that
      the riemann relations are satisfied by the input.

    EXAMPLES::

        sage: from avisogenies_sage import AbelianVariety
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

        D = Zmod(n) ** g
        twotorsion = Zmod(2) ** g

        if not D.has_coerce_map_from(twotorsion):
            from sage.structure.coerce_maps import CallableConvertMap
            s = n // 2

            def c(P, t):
                return P(s * t.change_ring(ZZ))

            c = CallableConvertMap(twotorsion, D, c)
            D.register_coercion(c)

        if check:
            idx = lambda i: ZZ(list(i), n)
            dual = {}
            DD = [2 * d for d in D]

            if any(T[idx(-i)] != val for i, val in zip(D, T)):
                raise ValueError('The given list does not define a valid thetanullpoint')

            for (idxi, i), (idxj, j) in product(enumerate(D), repeat=2):
                ii, jj, tt = reduce_twotorsion_couple(i, j)
                for idxchi, chi in enumerate(twotorsion):
                    el = (idxchi, idx(ii), idx(jj))
                    if el not in dual:
                        dual[el] = sum(eval_car(chi, t) * T[idx(ii + t)] * T[idx(jj + t)] for t in twotorsion)
                    dual[(idxchi, idxi, idxj)] = eval_car(chi, tt) * dual[el]

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

        .. todo::

            - Find a couple of examples

        """
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
        idx = self._char_to_idx
        O = self.theta_null_point()

        eqns = []
        for elem in product(enumerate(D), repeat=4):
            (idxi, i), (idxj, j), (idxk, k), (idxl, l) = elem
            if i + j + k + l in DD:
                m = D([ZZ(x) / 2 for x in i + j + k + l])
                for idxchi, chi in enumerate(twotorsion):
                    Pel1 = sum(eval_car(chi, t) * P[idx(i + t)] * P[idx(j + t)] for t in twotorsion)
                    Pel4 = sum(eval_car(chi, t) * P[idx(m - k + t)] * P[idx(m - l + t)] for t in twotorsion)
                    Oel2 = sum(eval_car(chi, t) * O[idx(k + t)] * O[idx(l + t)] for t in twotorsion)
                    Oel3 = sum(eval_car(chi, t) * O[idx(m - i + t)] * O[idx(m - j + t)] for t in twotorsion)
                    eq = Pel1 * Oel2 - Oel3 * Pel4
                    if eq != 0 and eq not in eqns:
                        eqns.append(eq)
        if eqns == [0]:
            eqns = []
        self._eqns = eqns
        return eqns

    def isogeny_old(self, l, Q, k, P=None):
        """
        Old isogeny algorithm

        INPUT:

        - ``self`` -- An abelian variety given as a theta null point of level n and dimension g
        - ``l`` -- an integer
        - ``Q`` -- An univariate polynomial of degree l^g describing a l-torsion subgroup of A
        - ``P`` -- A point of the abelian variety given as a projective theta point
        - ``k`` -- a element of Zmod(n)^g


        .. todo::

            - Add more info to docstring & references. Add examples.

        """

        sqfree = l.squarefree_part()
        l1 = ZZ((l / sqfree).sqrt())
        if sqfree == 1:
            return self._isogeny_1(l1, Q, P, k)
        try:
            a, b = two_squares(sqfree)
            return self._isogeny_twoSq(l, l1, a, b, Q, P, k)
        except ValueError:
            a, b, c, d = four_squares(sqfree)
            return self._isogeny_fourSq(l, l1, a, b, c, d, Q, P, k)

    def _isogeny_1(self, l1, Q, P, k):
        """
        .. todo:: add minimal docstring (private function) and test.
        """
        pass

    def _isogeny_twoSq(self, l, l1, a, b, Q, P, k):  ##Maybe add a line "if P != None"?
        """
        .. todo:: add minimal docstring (private function) and test.
        """
        S = Q.parent()
        B = S.quotient(Q)
        y, = B.gens()
        IK = self.point([1, y], B)  ##TODO: generalize this line to general g
        l1IK = l1 * IK
        l1aP = (l1 * a) * P
        eta = l1IK + l1aP  ##what shall we do when the level is 2? can't do it
        T = PolynomialRing(B, names='mu')
        mu, = T.gens()
        etamu = eta.scale(mu, T)
        beta0 = mod(-b / a, l)
        eta1 = beta0 * etamu
        D = self._D
        Zn = D.base_ring()
        M = l1 * matrix(Zn, 2, 2, [a, b, -b, a])
        J = (column_matrix(Zn, [k, D(0)]) * M.inverse()).columns()
        idx = self._char_to_idx
        delta = l1IK.compatible_lift(l1aP, eta, l)
        R = etamu[idx(D(J[0]))] * eta1[idx(D(J[1]))]  # This should have factors of mu^l, that we replace by delta
        return evaluate_formal_points(B(R.mod(mu ** l - delta)))

    def _isogeny_fourSq(self, l, l1, a, b, c, d, Q, P, k):
        """
        .. todo:: add minimal docstring (private function) and test.
        """
        # "Naive" implementation: Change to use three-way addition
        S = Q.parent().extend_variables('y0')
        B = S.quotient([q(v) for v in S.gens()])  # what is q here??
        IK = [self.point([1, v], B) for v in B.gens()]  ##TODO: generalize this line to general g
        l1IK = [l1 * IKi for IKi in IK]
        l1aP = (l1 * a) * P
        l1bP = (l1 * b) * P
        eta1 = l1IK[0] + l1aP  ##what shall we do when the level is 2? can't do it
        eta2 = l1IK[1] + l1bP
        eta12 = eta1 + eta2
        T = PolynomialRing(B, names='mu')
        mu1, mu2, mu12, = T.gens()
        etamu1 = eta1.scale(mu1, T)
        etamu2 = eta2.scale(mu2, T)
        etamu12 = eta12.scale(mu12, T)
        delta = [eta1 ** l - l1IK[0].compatible_lift(l1aP, eta1, l),
                 eta2 ** l - l1IK[1].compatible_lift(l1bP, eta2, l),
                 eta12 ** l - (l1IK[0] + l1IK[1]).compatible_lift((l1 * (a + b)) * P, eta1, l)]
        N = matrix(Zmod(l), 2, 2, [a, b, -b, a]).inverse() * matrix(Zmod(l), 2, 2, [c, d, -d, c])
        eta1 = N[0, 0] * etamu1 + N[0, 1] * etamu2
        eta2 = N[1, 0] * etamu1 + N[1, 1] * etamu2
        D = self._D
        Zn = D.base_ring()
        M = matrix(Zn, 4, 4, [a, b, -c, -d, b, a, -d, c, c, d, a, -b, d, -c, b, a])
        J = (column_matrix(Zn, [k] + [D(0)] * 3) * M.inverse()).columns()
        idx = self._char_to_idx
        R = etamu1[idx(D(J[0]))] * etamu1[idx(D(J[1]))] * eta1[idx(D(J[2]))] * eta2[idx(D(J[3]))]
        for eq in delta:
            R = R.mod(eq)
        return evaluate_formal_points(B(R))  ##How does Evaluate work in this case?

    def isogeny_pt(self, l, L, P=None):
        """
        Old isogeny algorithm

        INPUT:

        - ``self`` -- An abelian variety given as a theta null point of level n and dimension g
        - ``l`` -- an integer
        - ``L`` -- A list with a basis of the kernel of l-torsion of A
        - ``P`` -- A point of the abelian variety given as a projective theta point
        
        .. todo::

            - Add more info to docstring & references. Add examples.

        """
        raise NotImplementedError('TBD')


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

        sage: from avisogenies_sage import KummerVariety
        sage: FF1 = GF(331)
        sage: K1 = KummerVariety(FF1, 2, [328,213,75,1]); K1
        Kummer variety of dimension 2 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
        
    """
    _point = KummerVarietyPoint

    def __init__(self, R, g, T, check=False):
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

        twotorsion = Zmod(2) ** g

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
        the equations as given by Gaudry in [Gaud].

        Otherwise, these are computed using the Riemann relations.

        .. todo::

            - Find a couple of examples

        """
        if self._eqns is not None:
            return self._eqns
        if self._dimension != 2:
            raise NotImplementedError
        # TODO: add genericity condition checks.
        a, c, d, b = list(self.theta_null_point())
        A2 = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4
        B2 = (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) / 4
        C2 = (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) / 4
        D2 = (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) / 4
        E = a * b * c * d * A2 * B2 * C2 * D2 / (
                    (a ^ 2 * d ^ 2 - b ^ 2 * c ^ 2) * (a ^ 2 * c ^ 2 - b ^ 2 * d ^ 2) * (a ^ 2 * b ^ 2 - c ^ 2 * d ^ 2))
        F = (a ^ 4 - b ^ 4 - c ^ 4 + d ^ 4) / (a ^ 2 * d ^ 2 - b ^ 2 * c ^ 2)
        G = (a ^ 4 - b ^ 4 + c ^ 4 - d ^ 4) / (a ^ 2 * c ^ 2 - b ^ 2 * d ^ 2)
        H = (a ^ 4 + b ^ 4 - c ^ 4 - d ^ 4) / (a ^ 2 * b ^ 2 - c ^ 2 * d ^ 2)
        x, z, t, y = list(self)
        self._eqns = [
            x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 + 2 * E * x * y * z * t - F * (x ^ 2 * t ^ 2 + y ^ 2 * z ^ 2) - G * (
                        x ^ 2 * z ^ 2 + y ^ 2 * t ^ 2) - H * (x ^ 2 * y ^ 2 + z ^ 2 * t ^ 2)]
        return self._eqns

    def isogeny_old(self, l, Q, k, P=None):
        """
        Old isogeny algorithm

        INPUT:

        - ``self`` -- An abelian variety given as a theta null point of level n and dimension g
        - ``l`` -- an integer
        - ``Q`` -- An univariate polynomial of degree l^g describing a l-torsion subgroup of A
        - ``P`` -- A point of the abelian variety given as a projective theta point
        - ``k`` -- a element of Zmod(n)^g


        .. todo::

            - Add more info to docstring & references. Add examples.

        """
        if P is not None:
            raise ValueError('Cannot compute the image of a point via the isogeny')
        # here do stuff taking into account the shape of q? depending on de degree of Q we have to do different thinks, because it can be of the shape (x - a)*self^2
        if Q.degree() == l ** self.dimension():
            poly = 1
            for f, m in Q.factor():
                if m == 2:
                    poly *= f
            Q = poly
        assert 2 * Q.degree() + 1 == l ** self.dimension(), f'the input does not represent a valid {l}-torsion group of A={self}'
        S = Q.parent()
        B = S.quotient(Q)
        y, = B.gens()
        AB = self.change_ring(B)
        Q = AB.point([1, y])
        deltaQ = Q.compatible_lift(l)

        T = PolynomialRing(B, names='mu')
        mu, = T.gens()
        T2 = T.quotient(mu ** l - deltaQ)
        AT = self.change_ring(T2)
        compQ = AT.point(Q).scale(mu)

        # TODO generalize to include the other two cases.
        sqfree = l.squarefree_part()
        l1 = ZZ((l / sqfree).sqrt())
        a, b = two_squares(sqfree)

        t1 = (l1 * a) * compQ  # Revise if these are the right equations to use
        t2 = (l1 * b) * compQ
        idx = AT._char_to_idx
        W = B((t1[idx(k)] * t2[0]).lift())  # lth power of lambda
        P0 = self.theta_null_point()
        return P0[idx(k)] * P0[0] + 2 * evaluate_formal_points(W)(0)

    def isogeny_pt(self, l, L, P=None):
        """
        Old isogeny algorithm

        INPUT:

        - ``self`` -- An abelian variety given as a theta null point of level n and dimension g
        - ``l`` -- an integer
        - ``L`` -- A list with a basis of the kernel of l-torsion of A
        - ``P`` -- A point of the abelian variety given as a projective theta point
        
        .. todo::

            - Add more info to docstring & references. Add examples.

        """
        g = self.dimension()
        FF = self.base_ring()
        D = self._D
        idx = self._char_to_idx
        if P is not None:
            raise ValueError('Cannot compute the image of a point via the isogeny')
        # here do stuff taking into account the shape of q? depending on de degree of Q we have to do different thinks, because it can be of the shape (x - a)*self^2
        deltas = [pt.compatible_lift(l) for pt in L]

        P0B = [0] * self._ng
        S = PolynomialRing(FF, 'mu', len(L))
        mu = S.gens()
        T = S.quotient([mu[i] ** l - deltas[i] for i in range(len(L))])
        AT = self.change_ring(T)
        comps = [AT.point(L[i]).scale(mu[i]) for i in range(len(L))]

        V = Zmod(l) ** g
        idxl = lambda i: ZZ(list(i), l)
        vs = V.basis()
        K = [None] * V.cardinality()
        # Kplain = [None]*V.cardinality()
        K[0] = AT.theta_null_point()
        # Kplain[0] = self.theta_null_point()
        for i, v in enumerate(vs):
            K[idxl(v)] = comps[i]
            # Kplain[idxl(v)] = L[i]
            if i != 0:
                K[idxl(v + vs[0])] = comps[i + g - 1]
                # Kplain[idxl(v + vs[0])] = L[i + g - 1]
        if g == 1:
            compQ = comps[0]
            for el in range(l):
                K[el] = ZZ(el) * compQ

        elif g == 2:
            compP, compQ, compPQ = comps
            # P, Q, PQ = L
            for v in V:
                if K[idxl(v)] is not None:
                    continue
                i, j = v
                compjQ = K[idxl([0, j])]
                compPjQ = K[idxl([1, j])]
                # jQ = Kplain[idxl([0,j])]
                # PjQ = Kplain[idxl([1,j])]
                if compjQ is None or compPjQ is None:
                    K[idxl([1, j])], K[idxl([0, j])] = compQ.diff_multadd(ZZ(j), compPQ, compP)
                    compjQ = K[idxl([0, j])]
                    compPjQ = K[idxl([1, j])]
                    # Kplain[idxl([1, j])], Kplain[idxl([0, j])] = Q.diff_multadd(ZZ(j), PQ, P)
                    # jQ = Kplain[idxl([0,j])]
                    # PjQ = Kplain[idxl([1,j])]
                if i != 1:
                    K[idxl([i, j])], K[idxl([i, 0])] = compP.diff_multadd(ZZ(i), compPjQ, compjQ)
                    # Kplain[idxl([i, j])], Kplain[idxl([i, 0])] = P.diff_multadd(ZZ(i), PjQ, jQ)
        else:
            raise NotImplementedError

        sqfree = l.squarefree_part()
        l1 = ZZ((l / sqfree).sqrt())
        if sqfree == 1:
            r = 1
            M = matrix(ZZ, 1, 1, [l1])
        else:
            try:
                r = 2
                a, b = two_squares(sqfree)
                M = l1 * matrix(ZZ, 2, 2, [a, b, -b, a])
            except ValueError:
                r = 4
                a, b, c, d = four_squares(sqfree)
                M = matrix(ZZ, 4, 4, [a, -b, -c, -d, b, a, -d, c, c, d, a, -b, d, -c, b, a])

        assert M.transpose() * M == l * identity_matrix(ZZ, r), f"Wrong matrix, Mt*M = {M.transpose() * M}"
        Zn = D.base_ring()
        ker = M.change_ring(Zmod(l)).kernel()
        for idxk, k in enumerate(D):
            J = (column_matrix(Zn, [k] + [D(0)] * (r - 1)) * M.change_ring(Zn).inverse()).columns()
            for t in product(ker, repeat=g):
                ti = matrix(ZZ, t).columns()
                val = 1
                for i in range(r):
                    val *= K[idxl(ti[i])][idx(J[i])]
                P0B[idxk] += val
            P0B[idxk] = P0B[idxk].lift()
        B = KummerVariety(FF, g, P0B, check=True)
        return B
