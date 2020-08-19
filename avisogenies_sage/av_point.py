# ****************************************************************************
#       Copyright (C) 2020 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

"""
TODO:

> URGENT: If the data for AbelianVariety or AbelianVarietyPoint is a ThetaStructure, then there
is no need to transform it! Change __init__ for both.
> Clean a bit the functions, and imports, see what is really needed (eg. what do we get from
inheriting from Scheme vs just Parent?)
> To be decided - Should we create an interface for the point arithmetic from the abelian variety?
That is, add something like this to the abelian_variety class:
    def diff_add(self, P, Q, PmQ):
        (Maybe assert here that P, Q, PmQ are points in self)
        return P.diff_add(Q,PmQ)
  Especially for the pairings!
> On binary operations, test that all the points belong to the same abelian variety.
"""
from __future__ import print_function, division, absolute_import

from itertools import product, combinations_with_replacement

from sage.rings.all import PolynomialRing
from sage.rings.integer import Integer
integer_types = (int, Integer)
from sage.rings.integer_ring import ZZ

from sage.matrix.all import Matrix

from sage.schemes.generic.morphism import (is_SchemeMorphism,
                                           SchemeMorphism_point)
from sage.structure.element import AdditiveGroupElement
from sage.misc.constant_function import ConstantFunction
from sage.structure.element import is_Vector
from sage.modules.free_module_element import vector as Vector

from sage.structure.richcmp import richcmp, op_EQ, op_NE

from .tools import ThetaStructure

class AbelianVarietyPoint(AdditiveGroupElement, SchemeMorphism_point):
    def __init__(self, X, v, R=None, good_lift=False, check=False):
        """
        Constructor for a point on an abelian variety.

        INPUT:

        - ``X`` -- an abelian variety
        - ``v`` -- data determining a point (another point or a tuple of coordinates)
        - ``R`` -- the field of definition of the point (default: `None`). If left as default,
                the base ring of `X` is taken.
        - ``good_lift`` -- a boolean (default: `False`); indicates if the given affine lift
                is a good lift, i.e. a lift compatible with the lift of the theta null point.
        - ``check`` -- a boolean (default: `False`); indicates if computations to check
                the correctness of the input data should be performed, using the Riemann Relations.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]); P
            (255 : 89 : 30 : 1)
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
             155*t^3 + 84*t^2 + 15*t + 170, 1], R=F, check=True); Q
            (158*t^3 + 67*t^2 + 9*t + 293 : 290*t^3 + 25*t^2 + 235*t + 280 : 155*t^3 + 84*t^2 + 15*t + 170 : 1)

        """
        point_homset = X.point_homset()
        if is_SchemeMorphism(v) or isinstance(v, AbelianVarietyPoint) or is_Vector(v):
            v = list(v)
        if v == 0 or v == (0,):
            if check:
                ## if check, we should make sure that v has been checked when generated.
                # maybe with a boolean in X (or in the point) that saves if it has been checked.
                pass
            v = X.thetanullpoint
        if len(v) != X._ng:
            raise ValueError("v (=%s) must have length n^g (=%s)."%(v, X._ng))
        if R == None:
            R = point_homset.value_ring()

        v = ThetaStructure(tuple(R(a) for a in v), X.level)
        #TODO move to the definition of ThetaStructure
        for el in v:
            if el != 0:
                break
        else:
            raise ValueError('The given list does not define a valid thetapoint because all \
                             entries are zero')

        if check:
            from .abelian_variety import reduce_twotorsion_couple, eval_car
            O = X.thetanullpoint
            dual = X._dual
            #TODO: Create a method to extract all of this in one go.
            D = X.numbering
            n = X.level
            g = X.dimension
            twotorsion = X.two_torsion
            #TODO: Maybe this should be a function of X, with a boolean "full" to determine if the
            #dictionary is complete.
            if None in dual:
                for chi, i, j in product(twotorsion, D,D):
                    ii, jj, tt = reduce_twotorsion_couple(i, j);
                    if dual[chi, ii, jj] == None:
                        dual[chi, ii, jj] = sum(eval_car(chi,t)*O[ii + t]*O[jj + t] for t in twotorsion)
                    dual[chi, i, j] = eval_car(chi,tt)*dual[chi, ii, jj]
            X._dual = dual

            dualself = ThetaStructure(level=[2,n,n], g=g)
            DD = [2*d for d in D]

            for chi, i, j in product(twotorsion, D, D):
                ii, jj, tt = reduce_twotorsion_couple(i, j);
                if dualself[chi, ii, jj] == None:
                    dualself[chi, ii, jj] = sum(eval_car(chi,t)*v[ii + t]*v[jj + t] for t in twotorsion)
                dualself[chi, i, j] = eval_car(chi,tt)*dualself[chi, ii, jj]

            for (i, j), (k, l) in product(combinations_with_replacement(D,2), repeat=2):
                if i + j + k + l in DD:
                    m = D([ZZ(x)/2 for x in i + j + k + l])
                    for chi in twotorsion:
                        if dual[chi, i, j]*dualself[chi, k, l] != dual[chi, m-i, m-j]*dualself[chi, m-k, m-l]:
                            raise ValueError('The given list does not define a valid thetapoint')

        self._coords = v
        self._good_lift = good_lift
        self.domain = ConstantFunction(point_homset.domain())
        self._codomain = point_homset.codomain()
        self.codomain = ConstantFunction(self._codomain)
        AdditiveGroupElement.__init__(self, point_homset)
        self._R = R

    def _repr_(self):
        """
        Return a string representation of this point.
        """
        return self.codomain().ambient_space()._repr_generic_point(self._coords)

    def _latex_(self):
        """
        Return a LaTeX representation of this point.
        """
        return self.codomain().ambient_space()._latex_generic_point(self._coords)

    def __getitem__(self, n):
        """
        Return the n-th coordinate of this point.
        """
        return self._coords[n]

    def __iter__(self):
        """
        Return the coordinates of this point as a list.
        """
        return iter(self._coords)

    def __tuple__(self):
        """
        Return the coordinates of this point as a tuple.
        """
        return tuple(self._coords)

    def equal_points(self, Q, proj = True, factor = False):
        """
        Check whether two ThetaPoints are equal or not.
        If proj = true we compare them as projective points,
        and if factor = True, return as a second argument
        the rapport Q/P

        INPUT:
            - ``Q`` - a point.
            - ``proj`` - a boolean (default: `True`). Wether the comparison
                    is done as projective points.
            - ``factor`` - a boolean (default: `False`). If True, as a second
                    argument is returned, the rapport right/self.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]]) #A 1889-torsion point
            sage: 1889*P
            (12 : 141 : 31 : 327)
            sage: A(0).equal_points(1889*P)
            True

        If the points are equal as projective points but not as affine points,
        one can obtain the factor:

            sage: (1889*P).equal_points(A(0), proj=False)
            False
            sage: _, k = A(0).equal_points(1889*P, factor=True); k
            327

        """
        if self.abelian_variety != Q.abelian_variety:
            return False

        if not proj:
            return richcmp(self._coords, Q._coords, op_EQ)

        if factor:
            c = None;
            for i in range(len(self)):
                if (self[i] == 0) != (Q[i] == 0):
                    return False, None
                if self[i] != 0:
                    if c == None:
                        c = Q[i]/self[i]
                    if c != Q[i]/self[i]:
                        return False, None
                return True, c

        for i in range(len(self)):
            for j in range(i+1, len(self)):
                if self[i] * Q[j] != self[j] * Q[i]:
                    return False
        return True

    def _richcmp_(self, right, op):
        """
        Comparison function for points to allow sorting and equality
        testing (as projective points).
        """
        if not isinstance(right, AbelianVarietyPoint):
            try:
                right = self.codomain()(right)
            except TypeError:
                return NotImplemented
        if self.codomain() != right.codomain():
            return op == op_NE

        if op in [op_EQ, op_NE]:
            return self.equal_points(right) == (op == op_EQ)
        return richcmp(self._coords, right._coords, op)

    def good_lift(self):
        """
        Indicates if the given point is the affine lift compatible with
        the lift of the theta null point.
        """
        return self._good_lift

    def scheme(self):
        """
        Return the scheme of this point, i.e., the abelian variety it is on.
        This is synonymous with :meth:`abelian_variety` which is perhaps more
        intuitive.
        """

        return self.codomain()

    @property
    def abelian_variety(self):
        """
        Return the abelian variety that this point is on.

        EXAMPLES::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1]); A
            Abelian variety of dimension 2 with theta null point (328 : 213 : 75 : 1)
            sage: P = A([255 , 89 , 30 , 1])
            sage: P.abelian_variety
            Abelian variety of dimension 2 with theta null point (328 : 213 : 75 : 1)

        """
        return self.scheme()

    def __bool__(self):
        """
        Return ``True`` if this is not the zero point on the abelian variety.

        EXAMPLES::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]]) #A 1889-torsion point
            sage: (1889*P).is_zero()
            True
        """
        return self != self.abelian_variety(0)

    __nonzero__ = __bool__

    def get_nonzero_coord(self, idx=True):
        for i in range(len(self)):
            if self[i] != 0:
                if idx:
                    return i
                return self.abelian_variety._idx_to_char(i)
        raise ValueError('All entries are zero.')

    def diff_add(self, Q, PmQ, check=False):
        """
        Computes the differential addition of self with given point Q.

        INPUT:

        -  ``Q`` - a theta point

        -  ``PmQ`` - The theta point `self - Q`.

        -  ``check`` - (default: False) check with the riemann relations that the
        resulting point is indeed a point of the abelian variety.

        OUTPUT: The theta point `self + Q`. If `self`, `Q` and `PmQ` are good lifts,
        then the output is also a good lift.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
                155*t^3 + 84*t^2 + 15*t + 170, 1], R=F, check=True)
            sage: PmQ = A([62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 ,
                258*t^3 + 39*t^2 + 313*t + 150 , 1], R=F)
            sage: PQ = P.diff_add(Q, PmQ); PQ
            (261*t^3 + 107*t^2 + 37*t + 135 : 205*t^3 + 88*t^2 + 195*t + 125 : 88*t^3 + 99*t^2 + 164*t + 98 : 159*t^3 + 279*t^2 + 254*t + 276)

        """
        point0 = self.abelian_variety
        n = point0.level
        g = point0.dimension
        D = point0.numbering
        twotorsion = point0.two_torsion
        twog = 2**g
        PQ = ThetaStructure(level=n, g=g)
        lvl2 = (n == 2)
        if lvl2:
            from .abelian_variety import eval_car
        i0 = PmQ.get_nonzero_coord()
        L = []
        for i in D:
            if PmQ[i] != 0:
                j = i
                L += [(chi, i, j) for chi in twotorsion]
            else:
                j = i0
                if lvl2:
                    L += [(chi, i, j) for chi in twotorsion if eval_car(chi, i + j) == 1]
                else:
                    L += [(chi, i, j) for chi in twotorsion]

        r = point0.addition_formula(self, Q, L) #ThetaStructure(level=[2,n,n], g=g)

        for i in D:
            if PmQ[i] != 0:
                j = i
                PQ[i] = sum(r[chi,i,j] for chi in range(twog))/(2**g * PmQ[j]);
            else:
                j = i0
                if lvl2:
                    cartosum = [chi for chi in twotorsion if eval_car(chi, i + j) == 1]
                    PQ[i] = sum(r[chi,i,j] for chi in cartosum)/(PmQ[j]*len(cartosum))
                else:
                    PQ[i] = sum(r[chi,i,j] for chi in range(twog))/(2**g * PmQ[j]);
                    

        if lvl2:
            for i in D:
                # in level 2, in this case we only computed
                # PQ[i]PmQ[j]+PQ[j]PmQ[i] so we correct to get PQ[i]
                # we have to do it here to be sure we have computed PQ[j]
                #FIXME Makes no sense, we are substracting 0 all the time
                #FIXME j should be chosen to be a coordinate with PmQ[j]!= 0.
                #Should it just be PQ[i] -= PQ[i0]*PmQ[i]/PmQ[i0]?
                if PmQ[i] == 0:
                    PQ[i] -= PQ[j]*PmQ[i]/PmQ[j]
        #FIXME Find a way to improve how to deal with fields of definition
        try:
            pq = point0.point(PQ, Q._R, good_lift = (self._good_lift and Q._good_lift and PmQ._good_lift), check=check)
        except ValueError:
            pq = point0.point(PQ, self._R, good_lift = (self._good_lift and Q._good_lift and PmQ._good_lift), check=check)
        return pq

    def _diff_add_PQfactor(self, P, Q, PmQ):
        """
        Given a representative of (P+Q), computes the raport with respect to
        the representative obtained as P.diff_add(Q, PmQ).
        """
        point0 = self.abelian_variety
        D = point0.numbering
        twotorsion = point0.two_torsion
        for i in D:
            lambda2 = sum(self[i + t]*PmQ[i + t] for t in twotorsion)
            if lambda2 == 0:
                continue
            elt = (0, i, i)
            r = point0.addition_formula(P, Q, [elt])
            lambda1 = r[elt] #lambda1 = \sum PQ[i+t]PmQ[i+t]/2^g
            return lambda1/lambda2
        # Comments from the original Magma implementation:
        # sometimes it does not suffice when PmQ has a 0 coordinate, meaning we should
        # try to do the addition formula for i,j in D
        # and handle the level 2 case
        # TODO!
        # in practise this never happen, so I just call diff_add in this case
        PQ2 = P.diff_add(Q,PmQ)
        i0 = PQ2.get_nonzero_coord()
        return PQ2[i0]/self[i0];

    def _diff_add_PQ(self,P,Q,PmQ):
        """
        Given a representative of (P+Q), computes the affine representative
        obtained with P.diff_add(Q, PmQ).
        """
        point0 = self.abelian_variety
        PQn = [0]*point0._ng
        c = self._diff_add_PQfactor(P, Q, PmQ)
        for i, value in enumerate(self):
            PQn[i] = c*self
        return point0.point(PQn, Q._R)

    def _add_(self, other):
        """
        Add self to other.

        If we are in level two, this returns P+Q and P-Q.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
             155*t^3 + 84*t^2 + 15*t + 170, 1], R=F, check=True)
            sage: P + Q
            ((221*t^3 + 178*t^2 + 126*t + 27 : 301*t^3 + 265*t^2 + 257*t + 80 : \
            70*t^3 + 9*t^2 + 315*t + 316 : 67*t^3 + 283*t^2 + 52*t + 83),
            (1 : 281*t^3 + 76*t^2 + 257*t + 256 : 117*t^3 + 51*t^2 + 276*t + 303 : \
            48*t^3 + 140*t^2 + 238*t + 62))

        .. TODO ::

        Find tests that are not level 2!

        """
        return self._add(other)

    def _add(self, other, i0 = 0):
        """
        Normal addition between self and other on the affine plane with respect to i0.
        If (self - other)[i] == 0, then it tries with another affine plane.

        .. SEEALSO ::
            :meth: `_add_`
        """
        from .abelian_variety import eval_car
        point0 = self.abelian_variety
        n = point0.level
        g = point0.dimension
        D = point0.numbering
        twotorsion = point0.two_torsion
        ng = n**g
        twog = 2**g
        PQ = ThetaStructure(level=n, g=g)
        lvl2 = (n == 2)
        if lvl2:
            #n == 2
            PmQ = ThetaStructure(level=n, g=g)
            for i0, i1 in product(D,D): #TODO: Check if this can be done with combinations_with_replacement instead of product
                if i0 == i1:
                    continue
                L = [(chi,i,i0) for chi, i in product(twotorsion, D) if eval_car(chi, i + i0) == 1]\
                    + [(chi,i,i1) for chi, i in product(twotorsion, D) if eval_car(chi, i + i1) == 1]
                r = point0.addition_formula(self, other, L) #ThetaStructure(level=[2,n,n], g=g)
                kappa0 = ThetaStructure(level=n, g=g)
                kappa1 = ThetaStructure(level=n, g=g)
                for i in D:
                    cartosum = [chi for chi in twotorsion if eval_car(chi, i + i0) == 1]
                    kappa0[i] = sum(r[chi, i, i0] for chi in cartosum)/len(cartosum)
                    if i == i0 and kappa0[i0] == 0:
                        continue
                    cartosum = [chi for chi in twotorsion if eval_car(chi, i + i1) == 1]
                    kappa1[i] = sum(r[chi, i, i1] for chi in cartosum)/len(cartosum)
                F = kappa1[i0].parent()
                R = PolynomialRing(F, 'X')
                invkappa0 = 1/kappa0[i0]
                PmQ[i0] = F(1)
                PQ[i0] = kappa0[i0]
                poly = R([kappa1[i1]*invkappa0, - 2*kappa0[i1]*invkappa0, 1])
                roots = [el[0] for el in poly.roots()]
                # it can happen that P and Q are not rational in the av but
                # rational in the kummer variety, so P+Q won't be rational
                ## TODO: Find tests where this happens
                if len(roots) == 0:
                    #We need to work on the splitting field.
                    F = poly.splitting_field('t')
                    roots = [el for el, _ in poly.roots(F)]
                if len(roots) == 1:
                    roots = roots*2
                PmQ[i1] = roots[0]*PmQ[i0]
                PQ[i1] = roots[1]*PQ[i0]

                M = Matrix([[PmQ[i0], PmQ[i1]], [PQ[i0], PQ[i1]]])
                if not M.is_invertible():
                    continue
                for i in D:
                    if i == i0 or i == i1:
                        continue
                    v = Vector([kappa0[i], kappa1[i]])
                    w = M.solve_left(v)
                    PQ[i], PmQ[i] = w
                return point0.point(PQ, F), point0.point(PmQ, F)
        else:
            L = [(chi, i, i0) for chi, i in product(twotorsion, D)] #FIXME: i0 is an int, check that it doesn't break in point0.addition_formula
        r = point0.addition_formula(self, other, L) #ThetaStructure(level=[2,n,n], g=g)
        for i in range(ng):
            PQ[i] = sum(r[chi, i, i0] for chi in range(twog))
        if all(coor == 0 for coor in PQ):
            return self._add(other, i0 + 1)
        #FIXME Find a way to improve how to deal with fields of definition
        try:
            pq = point0.point(PQ, other._R)
        except ValueError:
            pq = point0.point(PQ, self._R)
        return pq

    def _neg_(self):
        """
        Computes the addition oposite of self.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]); - P
            (255 : 89 : 30 : 1)

        """
        point0 = self.abelian_variety
        D = point0.numbering
        n = point0.level
        g = point0.dimension
        mPcoord = ThetaStructure(level=n, g=g)
        for i in D:
            mPcoord[-i] = self[i]
        return point0.point(mPcoord, self._R)

    def _rmul_(self, k):
        """
        Compute scalar multiplication by `k` with a Montgomery ladder type algorithm.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: 42*P
            (311 : 326 : 136 : 305)

        .. TODO ::

        Find tests that are not level 2!

        """
        return self._mult(k)

    def _mult(self, k, algorithm='Montgomery'):
        """
        Compute scalar multiplication by `k` with a Montgomery ladder type algorithm.

        INPUT:

        - ``algorithm`` (default: 'Montgomery'): The chosen algorithm for the computation.
            It can either be 'Montgomery' for a Montgomery ladder type algorithm, or
            'SquareAndMultiply' for the usual square and multiply algorithm (only for level > 2).

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: P._mult(42)
            (311 : 326 : 136 : 305)

        .. SEEALSO ::
            :meth: `_rmul_`

        .. TODO ::

        Find tests that are not level 2!

        """
        if not isinstance(k, integer_types):
            raise NotImplementedError
        point0 = self.abelian_variety.thetanullpoint
        if k == 0:
            return point0
        if k == 1:
            return self
        if k < 0:
            return (-k)*(-self)
        kb = (k-1).digits(2)
        nP = self
        if algorithm == 'Montgomery':
            mP = -self
            n1P = self.diff_add(self, point0)
            for i in range(2, len(kb)+1):
                if kb[-i] == 1:
                    nn11P = n1P.diff_add(n1P,point0)
                    nP = nP.diff_add(n1P,mP)
                    n1P = nn11P
                else:
                    nn1P = n1P.diff_add(nP,self)
                    nP = nP.diff_add(nP,point0)
                    n1P = nn1P
            return n1P
        if algorithm == 'SquareAndMultiply':
            if self.abelian_variety.level == 2:
                raise NotImplementedError("Square and Multiply algorithm is only for level > 2.")
            for i in range(2, len(kb)+1):
                nP = nP.diff_add(nP,point0)
                if kb[-i] == 1:
                    nP = nP + self
            return nP;
        raise NotImplementedError("Unknown algorithm %s"%algorithm)

    def diff_multadd(self, k, PQ, Q):
        """
        Computes k*self + Q, k*self

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
             155*t^3 + 84*t^2 + 15*t + 170, 1], R=F, check=True)
            sage: PmQ = A([62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 ,
                258*t^3 + 39*t^2 + 313*t + 150 , 1], R=F)
            sage: PQ = P.diff_add(Q, PmQ)
            sage: P.diff_multadd(42, PQ, Q)
            ((41*t^3 + 291*t^2 + 122*t + 305 : 119*t^3 + 95*t^2 + 120*t + 68 : 81*t^3 + 168*t^2 + 326*t + 24 : 202*t^3 + 251*t^2 + 246*t + 169),
            (311 : 326 : 136 : 305))

        .. TODO ::

            If we don't need kP, then we don't need to compute kP, only (k/2)P, so
            we lose 2 differential additions. Could be optimized here.

        """
        if k == 0:
            point0 = self.abelian_variety.thetanullpoint
            return Q, point0 #In Magma implementation it only returns Q, but I think it should be Q, P0
        if k < 0:
            mP = - self
            return mP.diff_multadd(-k, Q.diff_add(mP,PQ), Q)
        if k == 1:
            return PQ, self
        point0 = self.abelian_variety.thetanullpoint
        nPQ = PQ
        n1PQ = PQ.diff_add(self,Q)
        nP = self
        n1P = self.diff_add(self,point0);
        kb = (k-1).digits(2)
        for i in range(2, len(kb)+1):
            if kb[-i] == 1:
             nn11PQ = n1PQ.diff_add(n1P,Q)
             nPQ = n1PQ.diff_add(nP,PQ)
             n1PQ = nn11PQ

             nn11P = n1P.diff_add(n1P,point0)
             nP = n1P.diff_add(nP,self)
             n1P = nn11P
            else:
             nn1PQ = n1PQ.diff_add(nP,PQ)
             nPQ = nPQ.diff_add(nP,Q)
             n1PQ = nn1PQ

             nn1P = n1P.diff_add(nP,self)
             nP = nP.diff_add(nP,point0)
             n1P = nn1P
        return n1PQ, n1P

    def pairing_from_points(self,Q,lP,lQ,lPQ,PlQ):
        """
        Computes the Weil pairing of self and Q, given all the points needed.

        .. TODO ::

            Maybe this could be included in the :meth:`pairing` with a keyword
            argument points that by default is None and otherwise is a list
            [lP, lQ, lPQ, PlQ]. But in that case we don't need l.
        """
        point0 = self.abelian_variety.thetanullpoint
        r, k0P = lP.equal_points(point0, proj=True, factor=True)
        assert r
        r, k0Q = lQ.equal_points(point0, proj=True, factor=True)
        assert r
        r, k1P = PlQ.equal_points(self, proj=True, factor=True)
        assert r
        r, k1Q = lPQ.equal_points(Q, proj=True, factor=True)
        assert r
        return k1P*k0P/(k1Q*k0Q);

    def pairing(self, l, Q, PQ=None):
        """
        Computes the Weil pairing of self and Q.

        EXAMPLES ::

            sage: from avisogenies_sage import *
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
             155*t^3 + 84*t^2 + 15*t + 170, 1], R=F, check=True)
            sage: PmQ = A([62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 ,
                258*t^3 + 39*t^2 + 313*t + 150 , 1], R=F)
            sage: PQ = P.diff_add(Q, PmQ)
            sage: P.pairing(1889, Q, PQ)
            17*t^3 + 153*t^2 + 305*t + 187

        """
        if PQ == None:
            if self.abelian_variety.level == 2:
                raise NotImplementedError
            PQ = self + Q
        point0 = self.abelian_variety.thetanullpoint
        lPQ, lP = self.diff_multadd(l,PQ,Q)
        PlQ, lQ = Q.diff_multadd(l,PQ,self)
        r, k0P = lP.equal_points(point0, proj=True, factor=True)
        assert r, "Bad pairing!"+str(self)
        r, k0Q = lQ.equal_points(point0, proj=True, factor=True)
        assert r, "Bad pairing!"+str(Q)
        r, k1P = PlQ.equal_points(self, proj=True, factor=True)
        assert r
        r, k1Q = lPQ.equal_points(Q, proj=True, factor=True)
        assert r
        return k1P*k0P/(k1Q*k0Q)
