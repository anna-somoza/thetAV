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

> On binary operations, test that all the points belong to the same abelian variety.
"""
from __future__ import print_function, division, absolute_import

from itertools import product, combinations_with_replacement

from sage.rings.all import PolynomialRing, Integer, ZZ
from sage.structure.richcmp import richcmp, op_EQ, op_NE
integer_types = (int, Integer)

from sage.matrix.all import Matrix
from sage.schemes.generic.morphism import is_SchemeMorphism, SchemeMorphism_point
from sage.structure.element import AdditiveGroupElement, is_Vector
from sage.structure.all import Sequence
from sage.misc.constant_function import ConstantFunction
from sage.modules.free_module_element import vector as Vector

class AbelianVarietyPoint(AdditiveGroupElement, SchemeMorphism_point):
    def __init__(self, X, v, good_lift=False, check=False):
        """
        Constructor for a point on an abelian variety.

        INPUT:

        - ``X`` -- an abelian variety
        - ``v`` -- data determining a point (another point or a tuple of coordinates)
        - ``good_lift`` -- a boolean (default: `False`); indicates if the given affine lift
                is a good lift, i.e. a lift compatible with the lift of the theta null point.
        - ``check`` -- a boolean (default: `False`); indicates if computations to check
                the correctness of the input data should be performed, using the Riemann Relations.

        EXAMPLES ::

            sage: from avisogenies_sage import AbelianVariety
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]); P
            (255 : 89 : 30 : 1)
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: B = A.change_ring(F)
            sage: Q = B([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280, \
             155*t^3 + 84*t^2 + 15*t + 170, 1], check=True); Q
            (158*t^3 + 67*t^2 + 9*t + 293 : 290*t^3 + 25*t^2 + 235*t + 280 : 155*t^3 + 84*t^2 + 15*t + 170 : 1)

        """
        point_homset = X.point_homset()
        if is_SchemeMorphism(v) or isinstance(v, AbelianVarietyPoint) or is_Vector(v):
            v = list(v)
        if isinstance(v,dict):
            try:
                ig = X._itemgetter
            except AttributeError:
                _ = X.general_point()
                ig = X._itemgetter
            v = ig(v)
        if v == 0 or v == (0,):
            if check:
                ## if check, we should make sure that v has been checked when generated.
                # maybe with a boolean in X (or in the point) that saves if it has been checked.
                pass
            v = X._thetanullpoint
        if len(v) != X._ng:
            raise ValueError("v (=%s) must have length n^g (=%s)."%(v, X._ng))
        R = point_homset.value_ring()
        v = Sequence(v, R)
        for el in v:
            if el != 0:
                break
        else:
            raise ValueError('The given list does not define a valid thetapoint because all entries are zero')
        if check:
            from .abelian_variety import reduce_twotorsion_couple, eval_car
            O = X._thetanullpoint
            idx = X._char_to_idx
            dual = X._dual
            D = X._D
            twotorsion = X._twotorsion
            ##Maybe this should be a function of X, with a boolean "full" to determine if the
            #dictionary is complete.
            if len(dual) != X._ng:
                for (idxi, i), (idxj, j) in product(enumerate(D), enumerate(D)):
                    ii, jj, tt = reduce_twotorsion_couple(i, j);
                    for idxchi, chi in enumerate(twotorsion):
                        el = (idxchi, idx(ii), idx(jj))
                        if el not in dual:
                            dual[el] = sum(eval_car(chi,t)*O[idx(ii + t)]*O[idx(jj + t)] for t in twotorsion)
                        el2 = (idxchi, idxi, idxj)
                        dual[el2] = eval_car(chi,tt)*dual[el]
            X._dual = dual
            
            dualself = {}
            DD = [2*d for d in D]
            for (idxi, i), (idxj, j) in product(enumerate(D), enumerate(D)):
                ii, jj, tt = reduce_twotorsion_couple(i, j);
                for idxchi, chi in enumerate(twotorsion):
                    el = (idxchi, idx(ii), idx(jj))
                    if el not in dualself:
                        dualself[el] = sum(eval_car(chi,t)*v[idx(ii + t)]*v[idx(jj + t)] for t in twotorsion)
                    el2 = (idxchi, idx(i), idx(j))
                    dualself[el2] = eval_car(chi,tt)*dualself[el]

            for elem in combinations_with_replacement(combinations_with_replacement(enumerate(D),2), 2):
                ((idxi, i), (idxj, j)), ((idxk, k), (idxl, l)) = elem
                if i + j + k + l in DD:
                    m = D([ZZ(x)/2 for x in i + j + k + l])
                    for idxchi, chi in enumerate(twotorsion):
                        el1 = (idxchi, idxi, idxj)
                        el2 = (idxchi, idxk, idxl)
                        el3 = (idxchi, idx(m-i), idx(m-j))
                        el4 = (idxchi, idx(m-k), idx(m-l))
                        if dual[el1]*dualself[el2] != dual[el3]*dualself[el4]:
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

            sage: from avisogenies_sage import AbelianVariety
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]) #A 1889-torsion point
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
        if self.abelian_variety() != Q.abelian_variety():
            return False

        if not proj:
            return richcmp(self._coords, Q._coords, op_EQ)

        if factor:
            c = None;
            for s, q in zip(self, Q):
                if (s == 0) != (q == 0):
                    return False, None
                if s != 0:
                    if c == None:
                        c = q/s
                    elif c != q/s:
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

    def abelian_variety(self):
        """
        Return the abelian variety that this point is on.

        EXAMPLES::

            sage: from avisogenies_sage import AbelianVariety
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1]); A
            Abelian variety of dimension 2 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
            sage: P = A([255 , 89 , 30 , 1])
            sage: P.abelian_variety()
            Abelian variety of dimension 2 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331

        """
        return self.scheme()

    def __bool__(self):
        """
        Return ``True`` if this is not the zero point on the abelian variety.

        EXAMPLES::

            sage: from avisogenies_sage import AbelianVariety
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]) #A 1889-torsion point
            sage: (1889*P).is_zero()
            True
        """
        return self != self.abelian_variety()(0)

    __nonzero__ = __bool__

    def get_nonzero_coord(self, idx=True):
        for i, val in enumerate(self):
            if val != 0:
                if idx:
                    return i
                return self.abelian_variety()._idx_to_char(i)
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
        
            sage: from avisogenies_sage import AbelianVariety
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: A = AbelianVariety(F, 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280, \
                155*t^3 + 84*t^2 + 15*t + 170, 1], check=True)
            sage: PmQ = A([62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 , \
                258*t^3 + 39*t^2 + 313*t + 150 , 1])
            sage: PQ = P.diff_add(Q, PmQ); PQ
            (261*t^3 + 107*t^2 + 37*t + 135 : 205*t^3 + 88*t^2 + 195*t + 125 : 88*t^3 + 99*t^2 + 164*t + 98 : 159*t^3 + 279*t^2 + 254*t + 276)
        
        """
        point0 = self.abelian_variety()
        n = point0._level
        g = point0._dimension
        D = point0._D
        twotorsion = point0._twotorsion
        ng = n**g
        twog = 2**g
        PQ = [0]*ng
        lvl2 = (n == 2)
        i0 = PmQ.get_nonzero_coord()
        if lvl2:
            from .abelian_variety import eval_car
            char = point0._idx_to_char
            chari0 = char(i0)
        L = []
        for i, chari in enumerate(D):
            if PmQ[i] == 0:
                j = i0
                charj = chari0
            else:
                j = i
            if PmQ[i] == 0 and lvl2:
                L += [(chi, i, j) for chi, charchi in enumerate(twotorsion) if eval_car(charchi, chari + charj) == 1] ##Change eval_car to accept also integers?
            else:
                L += [(chi, i, j) for chi in range(twog)]
        r = point0.addition_formula(self, Q, L)
        for i, chari in enumerate(D):
            if PmQ[i] == 0:
                j = i0
                charj = chari0
            else:
                j = i
            if PmQ[i] == 0 and lvl2:
                cartosum = [chi for chi, charchi in enumerate(twotorsion) if eval_car(charchi, chari + charj) == 1]
                PQ[i] = sum(r[(chi,i,j)] for chi in cartosum)/(PmQ[j]*len(cartosum))
            else:
                PQ[i] = sum(r[(chi,i,j)] for chi in range(twog))/(twog * PmQ[j]);
        #I think that this section is unnecessary
        # if lvl2:
            # for i in range(ng):
                # # in level 2, in this case we only computed
                # # (PQ[i]PmQ[j]+PQ[j]PmQ[i])/PmQ[j] so we correct to get PQ[i]
                # # we have to do it here to be sure we have computed PQ[j]
                # # FIXME We are substracting 0 all the time? Doesn't make too much sense...
                # # In the case with PmQ[i] == 0 (j = i0) we have computed (PQ[i]PmQ[i0] + PQ[i0]PmQ[i])/PmQ[i0] = PQ[i]
                # # In the case with PmQ[i] != 0 (j = i) we have computed (PQ[i]PmQ[i] + PQ[i]PmQ[i])/PmQ[i] = 2*PQ[i]
                # if PmQ[i] == 0:
                    # PQ[i] -= PQ[j]*PmQ[i]/PmQ[j]
        return point0.point(PQ, good_lift = (self._good_lift and Q._good_lift and PmQ._good_lift), check=check)

    def _diff_add_PQfactor(self, P, Q, PmQ):
        """
        Given a representative of (P+Q), computes the raport with respect to
        the representative obtained as P.diff_add(Q, PmQ).
        """
        point0 = self.abelian_variety()
        D = point0._D
        twotorsion = point0._twotorsion
        idx = point0._char_to_idx
        for i in D:
            lambda2 = sum(self[idx(i + t)]*PmQ[idx(i + t)] for t in twotorsion)
            if lambda2 == 0:
                continue
            elt = (0, idx(i), idx(i))
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
        point0 = self.abelian_variety()
        PQn = [0]*point0._ng
        lambda1 = self._diff_add_PQfactor(P, Q, PmQ)
        for i, val in enumerate(self):
            PQn[i] = lambda1*val
        return point0.point(PQn)

    def _add_(self, other):
        """
        Add self to other.

        If we are in level two, this returns P+Q and P-Q.

        EXAMPLES ::

            sage: from avisogenies_sage import AbelianVariety
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: A = AbelianVariety(F, 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280, \
             155*t^3 + 84*t^2 + 15*t + 170, 1], check=True)
            sage: P + Q
            ((221*t^3 + 178*t^2 + 126*t + 27 : 32*t^3 + 17*t^2 + 175*t + 171 : 180*t^3 + 188*t^2 + 161*t + 119 : 261*t^3 + 107*t^2 + 37*t + 135),
            (1 : 56*t^3 + 312*t^2 + 147*t + 287 : 277*t^3 + 295*t^2 + 7*t + 287 : 290*t^3 + 203*t^2 + 274*t + 10))


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

        .. TODO ::
            Deal with case where self or other is the thetanullpoint.
        """
        from .abelian_variety import eval_car
        point0 = self.abelian_variety()
        n = point0._level
        g = point0._dimension
        ng = n**g
        twog = 2**g
        PQ = [0]*ng
        lvl2 = (n == 2)
        if lvl2: #n == 2
            char = point0._idx_to_char
            PmQ = [0]*ng
            for i0 in range(ng):
                for i1 in range(ng):
                    if i0 == i1:
                        continue
                    L = [(chi,i,i0) for chi in range(twog) for i in range(ng) if eval_car(char(chi),char(i)+char(i0)) == 1]\
                        + [(chi,i,i1) for chi in range(twog) for i in range(ng) if eval_car(char(chi),char(i)+char(i1)) == 1]
                    r = point0.addition_formula(self, other, L)
                    kappa0 = [0]*ng
                    kappa1 = [0]*ng
                    for i in range(ng):
                        cartosum = [chi for chi in range(twog) if eval_car(char(chi), char(i) + char(i0)) == 1]
                        kappa0[i] = sum(r[(chi, i, i0)] for chi in cartosum)/len(cartosum)
                        if i == i0 and kappa0[i0] == 0:
                            continue #FIXME this continue should be for the i0-loop for efficiency.
                        cartosum = [chi for chi in range(twog) if eval_car(char(chi), char(i) + char(i1)) == 1]
                        kappa1[i] = sum(r[(chi, i, i1)] for chi in cartosum)/len(cartosum)
                    F = kappa1[i0].parent()
                    R = PolynomialRing(F, 'X')
                    invkappa0 = 1/kappa0[i0]
                    PmQ[i0] = F(1)
                    PQ[i0] = kappa0[i0]
                    poly = R([kappa1[i1]*invkappa0, - kappa0[i1]*invkappa0, 1])
                    roots = poly.roots(multiplicities=False)
                    # it can happen that P and Q are not rational in the av but
                    # rational in the kummer variety, so P+Q won't be rational
                    ## TODO: Find tests where this happens
                    if len(roots) == 0:
                        #We need to work on the splitting field.
                        F = poly.splitting_field('t')
                        raise ValueError(f'The normal addition is defined over the extension {F}.')
                    if len(roots) == 1:
                        roots = roots*2
                    PmQ[i1] = roots[0]*PmQ[i0]
                    PQ[i1] = roots[1]*PQ[i0]

                    M = Matrix([[PmQ[i0], PmQ[i1]], [PQ[i0], PQ[i1]]])
                    if not M.is_invertible():
                        # save(M, "error.sobj")
                        continue
                    for i in range(ng):
                        if i == i0 or i == i1:
                            continue
                        v = Vector([kappa0[i], kappa1[i]])
                        w = M.solve_left(v)
                        PmQ[i] = w[1]
                        PQ[i] = w[0]
                    return point0.point(PQ, F), point0.point(PmQ, F)
            raise ValueError("Failed to compute normal addition.")
        else:
            L = [(chi, i, i0) for chi in range(twog) for i in range(ng)]
        r = point0.addition_formula(self, other, L)
        for i in range(ng):
            PQ[i] = sum(r[(chi, i, i0)] for chi in range(twog))
        if all(coor == 0 for coor in PQ):
            return self._add(other, i0 + 1)
        return point0.point(PQ)

    def _neg_(self):
        """
        Computes the addition oposite of self.

        EXAMPLES ::

            sage: from avisogenies_sage import AbelianVariety
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1]); - P
            (255 : 89 : 30 : 1)
            
        """
        point0 = self.abelian_variety()
        D = point0._D
        mPcoord = [0]*point0._ng
        idx = point0._char_to_idx
        for i, val in zip(D, self):
            mPcoord[idx(-i)] = val
        return point0.point(mPcoord)

    def _rmul_(self, k):
        """
        Compute scalar multiplication by `k` with a Montgomery ladder type algorithm.

        EXAMPLES ::

            sage: from avisogenies_sage import AbelianVariety
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

            sage: from avisogenies_sage import AbelianVariety
            sage: A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: P._mult(42)
            (311 : 326 : 136 : 305)
            
        .. SEEALSO ::
            :meth: `_rmul_`
            
        .. TODO ::

        Find tests that are not level 2!
            
        """
        if not isinstance(k, integer_types + (Integer,)):
            raise NotImplementedError
        point0 = self.abelian_variety()._thetanullpoint
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
            for i in range(2, len(kb)+1): #FIXME: We can change this to walk the vector kb in reversed order?
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
            if self.abelian_variety()._level == 2:
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
        
            sage: from avisogenies_sage import AbelianVariety
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: A = AbelianVariety(F, 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,\
             155*t^3 + 84*t^2 + 15*t + 170, 1], check=True)
            sage: PmQ = A([62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 , \
                258*t^3 + 39*t^2 + 313*t + 150 , 1])
            sage: PQ = P.diff_add(Q, PmQ)
            sage: P.diff_multadd(42, PQ, Q)
            ((41*t^3 + 291*t^2 + 122*t + 305 : 119*t^3 + 95*t^2 + 120*t + 68 : 81*t^3 + 168*t^2 + 326*t + 24 : 202*t^3 + 251*t^2 + 246*t + 169),
            (311 : 326 : 136 : 305))
        
        .. TODO ::
        
            If we don't need kP, then we don't need to compute kP, only (k/2)P, so
            we lose 2 differential additions. Could be optimized here.
            
        """
        if k == 0:
            point0 = self.abelian_variety()._thetanullpoint
            return Q, point0 #In Magma implementation it only returns Q, but I think it should be Q, P0
        if k < 0:
            mP = - self
            return mP.diff_multadd(-k, Q.diff_add(mP,PQ), Q)
        if k == 1:
            return PQ, self
        point0 = self.abelian_variety()._thetanullpoint
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
        point0 = self.abelian_variety()._thetanullpoint
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
        
            sage: from avisogenies_sage import AbelianVariety
            sage: R.<X> = PolynomialRing(GF(331))
            sage: poly = X^4 + 3*X^2 + 290*X + 3
            sage: F.<t> = poly.splitting_field()
            sage: A = AbelianVariety(F, 2, 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: Q = A([158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280, \
             155*t^3 + 84*t^2 + 15*t + 170, 1], check=True)
            sage: PmQ = A([62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 , \
                258*t^3 + 39*t^2 + 313*t + 150 , 1])
            sage: PQ = P.diff_add(Q, PmQ)
            sage: P.pairing(1889, Q, PQ)
            17*t^3 + 153*t^2 + 305*t + 187
        """
        if PQ == None:
            if self.abelian_variety()._level == 2:
                raise NotImplementedError
            PQ = self + Q
        point0 = self.abelian_variety()._thetanullpoint
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

    
    def three_way_add(P, Q, R, PQ, QR, PR):
        from .abelian_variety import eval_car, reduce_twotorsion_couple
        point0 = P.abelian_variety()
        O = point0._thetanullpoint
        n = point0._level
        g = point0._dimension
        D = point0._D
        twotorsion = point0._twotorsion
        ng = n**g
        twog = 2**g
        PQR = [0]*ng
        lvl2 = (n == 2)
        idx = point0._char_to_idx
        idxi0 = P.get_nonzero_coord()
        i0 = point0._idx_to_char(idxi0)
        for idxI, I in enumerate(D):
            if P[idxI] == 0:
                idxJ, J = idxi0, i0
                i1, j1, t1 = reduce_twotorsion_couple(I - J, 0)
                i2, j2, t2 = reduce_twotorsion_couple(I, J)
                val = 0
                for chi in twotorsion:
                    l2 = sum(eval_car(chi, t)*Q[idx(i1 + t)]*R[idx(j1 + t)] for t in twotorsion)
                    l3 = sum(eval_car(chi, t)*O[idx(i2 + t)]*QR[idx(j2 + t)] for t in twotorsion)
                    l4 = sum(eval_car(chi, t)*PR[idx(i1 + t)]*PQ[idx(j1 + t)] for t in twotorsion)
                    val += eval_car(chi, t2)*l3*l4/l2
                PQR[idxI] = val/(2**g*P[idxJ])
            else:
                idxJ, J = idxI, I
                i2, j2, t2 = reduce_twotorsion_couple(I, J)
                val = 0
                for chi in twotorsion:
                    l2 = sum(eval_car(chi, t)*Q[idxt]*R[idxt] for idxt, t in enumerate(twotorsion))
                    l3 = sum(eval_car(chi, t)*O[idx(i2 + t)]*QR[idx(j2 + t)] for t in twotorsion)
                    l4 = sum(eval_car(chi, t)*PR[idxt]*PQ[idxt] for idxt, t in enumerate(twotorsion))
                    val += eval_car(chi, t2)*l3*l4/l2
                PQR[idxI] = val/(2**g*P[idxJ])
        return point0.point(PQR)

    def scale(self, k):
        """
        Given an affine lift point 'P' and a factor 'k' in the field of definition, returns the
        affine lift given by kx.
        """
        v = self._coords
        A = self.abelian_variety()
        R = self._R
        assert k in R, f'k={k} not in R={R}'
        return A.point(list(map(lambda i : k*i, v)))

    #TODO: Fix use of scale in this function
    def compatible_lift(self, l, other=None, add=None):
        """
        Compute a lift of an l-torsion point that is compatible with the chosen afine lift of the
        theta null point.

        INPUT ::
            - 'self' - an l-torsion point of the abelian variety
            - 'other' - a point of the abelian variety, or None if only the lift of an l-torsion
            point is needed.
            - 'add' - the point self + other, or None if only the lift of an l-torsion
            point is needed.
            - 'l' - the torsion
        """
        A = self.abelian_variety()
        if add == None:
            if other != None:
                raise ValueError('For the lift of a pair of points, you need to indicate the value of their sum too.')
            m = ZZ((l-1)/2)
            Qm = m*self
            Qm1 = (m+1)*self
            
            #the lift
            M = []
            for idx, el in enumerate(A._D):
                M.append(Qm[A._char_to_idx(-el)]/Qm1[idx])

            assert len(set(M)) == 1  #lift found
            return M[0]

        lam = self.compatible_lift(l)
        PlQ, lQ = self.diff_multadd(l, add, other)
        #assert lQ == 0
        
        #the lift
        M = []
        for idx in range(A._ng):
            M.append(other[idx]/PlQ[idx])
        assert len(set(M)) == 1  #lift found
        return M[0]/lam**(l-1)
