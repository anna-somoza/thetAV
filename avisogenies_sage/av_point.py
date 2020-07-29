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

> To be decided - Should we create an interface for the point arithmetic from the abelian variety?
That is, add something like this to the abelian_variety class:
    def diff_add(self, P, Q, PmQ):
        (Maybe assert here that P, Q, PmQ are points in self)
        return P.diff_add(Q,PmQ)
  Especially for the pairings!
> On binary operations, test that all the points belong to the same abelian variety.
"""
from __future__ import print_function, division, absolute_import

import math

import sage.plot.all as plot

from sage.rings.padics.factory import Qp
from sage.rings.padics.precision_error import PrecisionError

from itertools import product

import sage.rings.all as rings
from sage.rings.all import PolynomialRing
from sage.rings.real_mpfr import is_RealField
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
import sage.groups.generic as generic
from sage.libs.pari import pari
from cypari2.pari_instance import prec_words_to_bits
from sage.structure.sequence import Sequence
from sage.structure.richcmp import richcmp

from sage.matrix.all import Matrix

from sage.schemes.curves.projective_curve import Hasse_bounds
from sage.schemes.generic.morphism import (SchemeMorphism,
                                           is_SchemeMorphism,
                                           SchemeMorphism_point)
from sage.schemes.generic.morphism import is_SchemeMorphism
from sage.structure.element import AdditiveGroupElement
from sage.misc.constant_function import ConstantFunction
from sage.structure.element import is_Vector
from sage.modules.free_module_element import vector as Vector

from sage.structure.richcmp import op_EQ, op_NE

class AbelianVarietyPoint(AdditiveGroupElement, SchemeMorphism_point):
    def __init__(self, X, v, good_lift=False, check=False):
        """
        Constructor for a point on an abelian variety.

        INPUT:

        - X -- an abelian variety
        - v -- data determining a point (another point or a tuple of coordinates)
        
        """
        point_homset = X.point_homset()
        if is_SchemeMorphism(v) or isinstance(v, AbelianVarietyPoint) or is_Vector(v):
            v = list(v)
        if v == 0 or v == (0,):
            if check:
                ## if check, we should make sure that v has been checked when generated.
                # maybe with a boolean in X (or in the point) that saves if it has been checked.
                pass
            v = X._thetanullpoint
        if check:
            from .abelian_variety import reduce_twotorsion_couple, eval_car
            ##There sould be a way of testing the thetanullpoint directly here!
            O = X._thetanullpoint
            idx = X._char_to_idx
            dual = X._dual
            D = X._D
            twotorsion = X._twotorsion
            ##Maybe this should be a function of X, with a boolean "full" to determine if the
            #dictionary is complete.
            if len(dual) != X._ng:
                for i, j in product(D,D):
                    for chi in twotorsion:
                        ii, jj, tt = reduce_twotorsion_couple(i, j);
                        el = (idx(chi, True), idx(ii), idx(jj))
                        if el not in dual:
                            dual[el] = sum([eval_car(chi,t)*O[idx(ii + t)]*O[idx(jj + t)] for t in twotorsion])
                        el2 = (idx(chi, True), idx(i), idx(j))
                        dual[el2] = eval_car(chi,tt)*dual[el]
            X._dual = dual
            dualself = {}
            DD = [2*d for d in D]

            for i, j in product(D,D):
                for chi in twotorsion:
                    ii, jj, tt = reduce_twotorsion_couple(i, j);
                    el = (idx(chi, True), idx(ii), idx(jj))
                    if el not in dualself:
                        dualself[el] = sum([eval_car(chi,t)*v[idx(ii + t)]*v[idx(jj + t)] for t in twotorsion])
                    el2 = (idx(chi, True), idx(i), idx(j))
                    dualself[el2] = eval_car(chi,tt)*dualself[el]

            S = []
            for i, j, k, l in product(D, repeat=4):
                if i + j + k + l in DD:
                    s = [sorted([i,j]),sorted([k,l])]
                    if s not in S:
                        S.append(s)
                        m = D([ZZ(x)/2 for x in i + j + k + l])
                        for chi in twotorsion:
                            el1 = (idx(chi, True), idx(i), idx(j))
                            el2 = (idx(chi, True), idx(k), idx(l))
                            el3 = (idx(chi, True), idx(m-i), idx(m-j))
                            el4 = (idx(chi, True), idx(m-k), idx(m-l))
                            if dual[el1]*dualself[el2] != dual[el3]*dualself[el4]:
                                raise ValueError('The given list does not define a valid thetapoint')
        if len(v) != X._ng:
            raise ValueError("v (=%s) must have length n^g (=%s)."%(v, X._ng))
        self._coords = tuple(v) #should check that length is correct!
        self._good_lift = good_lift
        self.domain = ConstantFunction(point_homset.domain())
        self._codomain = point_homset.codomain()
        self.codomain = ConstantFunction(self._codomain)
        AdditiveGroupElement.__init__(self, point_homset)

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
        Return the n'th coordinate of this point.
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
        return tuple(self._coords)  # Warning: _coords is a list!

    def equal_points(self, right, proj = True, factor = False):
        """
        Check whether two ThetaPoints are equal or not.
        If proj = true we compare them as projective points,
        and if factor = True, return as a second argument
        the rapport Q/P
        """
        if self.abelian_variety() != right.abelian_variety():
            return False

        if not proj:
            return richcmp(self._coords, right._coords, op_EQ)

        if factor:
            c = None;
            for i in range(len(self)):
                if (self[i] == 0) != (right[i] == 0):
                    return False, _
                if self[i] != 0:
                    if c == None:
                        c = right[i]/self[i]
                    if c != right[i]/self[i]:
                        return False, _
                return True, c

        for i in range(len(self)):
            for j in range(i+1, len(self)):
                if self[i] * right[j] != self[j] * right[i]:
                    return False
        return True

    def _richcmp_(self, right, op):
        """
        Comparison function for points to allow sorting and equality testing.
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
        #TODO include in all operations
        return self._good_lift
        
    def scheme(self):
        """
        Return the scheme of this point, i.e., the curve it is on.
        This is synonymous with :meth:`curve` which is perhaps more
        intuitive.
        """

        return self.codomain()

    def abelian_variety(self):
        """
        Return the abelian variety that this point is on.

        EXAMPLES::

            #TODO
            sage: E = EllipticCurve('389a')
            sage: P = E([-1,1])
            sage: P.curve()
            Elliptic Curve defined by y^2 + y = x^3 + x^2 - 2*x over Rational Field
        """
        return self.scheme()

    # With which type of comparison?
    def __bool__(self):
        """
        Return ``True`` if this is not the zero point on the curve.

        EXAMPLES::

            sage: E = EllipticCurve('37a')
            sage: P = E(0); P
            (0 : 1 : 0)
            sage: P.is_zero()
            True
            sage: P = E.gens()[0]
            sage: P.is_zero()
            False
        """
        return self == self.abelian_variety()(0)

    __nonzero__ = __bool__

    def get_nonzero_coord(self, idx=True):
        for i in range(len(self)):
            if self[i] != 0:
                if idx:
                    return i
                return self.abelian_variety()._idx_to_char(i)
        raise ValueError('All entries are zero.')

    def diff_add(self, Q, PmQ, check=False):
        """
        Computes the differential addition of self with given point Q.

        INPUT:

        INPUT:

        -  ``Q`` - a theta point

        -  ``PmQ`` - The theta point self - Q.

        -  ``check`` - (default: False) check with the riemann relations that the
        resulting point is indeed a point of the abelian variety.
        """
        point0 = self.abelian_variety()
        n = point0._level
        g = point0._dimension
        ng = n**g
        twog = 2**g
        PQ = [0]*ng
        idx = point0._char_to_idx
        lvl2 = (n == 2)
        if lvl2:
            from .abelian_variety import eval_car
            char = point0._idx_to_char
        i0 = PmQ.get_nonzero_coord()
        L = []
        for i in range(ng):
            if PmQ[i] == 0:
                j = i0
            else:
                j = i
            if PmQ[i] == 0 and lvl2:
                L += [(chi, i, j) for chi in range(twog) if eval_car(char(chi, True),char(i) + char(j)) == 1] ##Change eval_car to accept also integers?
            else:
                L += [(chi, i, j) for chi in range(twog)]
        r = point0.addition_formula(self, Q, L)
        for i in range(ng):
            if PmQ[i] == 0:
                j = i0
            else:
                j = i
            if PmQ[i] == 0 and lvl2:
                cartosum = {chi for chi in range(twog) if eval_car(chi,i+j) == 1}
                PQ[i] = sum([r[(chi,i,j)] for chi in cartosum])/(PmQ[j]*len(cartosum))
            else:
                PQ[i] = sum([r[(chi,i,j)] for chi in range(twog)])/(twog * PmQ[j]);
        if lvl2:
            for i in range(ng):
                # // in level 2, in this case we only computed
                # // PQ[i]PmQ[j]+PQ[j]PmQ[i] so we correct to get PQ[i]
                # // we have to do it here to be sure we have computed PQ[j]
                if PmQ[i] == 0:
                    PQ[i] += - PQ[j]*PmQ[i]/PmQ[j]
        return AbelianVarietyPoint(point0, PQ, check)

    def diff_add_PQfactor(self, P, Q, PmQ):
        """
        //we have PQ(self) from a normal addition, we would like to recover the
        //differential addition. Here we only have to compute a single coefficient
        //to find the correct projective factor
        """
        point0 = self.abelian_variety()
        D = point0._D
        twotorsion = point0._twotorsion
        n = point0._level
        k = n/2
        idx = point0._char_to_idx
        for i in D:
            lambda2 = sum([self[idx(i + t)]*PmQ[idx(i + t)] for t in twotorsion])
            if lambda2 == 0:
                continue
            elt = (0, idx(i), idx(i))
            r = point0.addition_formula(P, Q, [elt])
            lambda1 = r[elt] #lambda1 = \sum PQ[i+t]PmQ[i+t]/2^g
            return lambda1/lambda2
        ##If we are here it means that we didn't succeed!
        """
        // sometimes it does not suffice when PmQ has a 0 coordinate, meaning we should
        // try to do the addition formula for i,j in D
        // and handle the level 2 case
        // TODO!
        // in practise this never happen, so I just call diff_add in this case
        """ 
        PQ2 = P.diff_add(Q,PmQ)
        i0 = PQ2.get_nonzero_coord()
        return PQ2[i0]/self[i0];
    
    def diff_add_PQ(self,P,Q,PmQ):
        point0 = self.abelian_variety()
        D = point0._D
        PQn = [0]*point0._ng
        lambda1 = self.diff_add_PQfactor(P, Q, PmQ)
        for i in range(point0._ng):
            PQn[i] = lambda1*PQ[i]
        return point0.point(PQn)

    def _add_(self, other):
        return self._add(other)

    def _add(self, other, i0 = 0):
        """
        Normal addition between self and other.
        We assume (P - Q)[i0] != 0
        """
        from .abelian_variety import eval_car
        point0 = self.abelian_variety()
        n = point0._level
        g = point0._dimension
        ng = n**g
        twog = 2**g
        PQ = [0]*ng
        lvl2 = (n == 2)
        if lvl2:
            #n == 2
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
                        kappa0[i] = sum([r[(chi, i, i0)] for chi in cartosum])/len(cartosum)
                        if i == i0 and kappa0[i0] == 0:
                            continue
                        cartosum = [chi for chi in range(twog) if eval_car(char(chi), char(i) + char(i1)) == 1]
                        kappa1[i] = sum([r[(chi, i, i1)] for chi in cartosum])/len(cartosum)
                    F = kappa1[i0].parent()
                    R = PolynomialRing(F, 'X')
                    invkappa0 = 1/kappa0[i0]
                    PmQ[i0] = F(1)
                    PQ[i0] = kappa0[i0]
                    poly = R([kappa1[i1]*invkappa0, - 2*kappa0[i1]*invkappa0, 1])
                    roots = [el[0] for el in poly.roots()]
                    """
                    # it can happen that P and Q are not rational in the av but
                    # rational in the kummer variety, so P+Q won't be rational
                    """
                    if len(roots) == 0:
                        #We need to work on the splitting field.
                        roots = [el[0] for el in poly.roots(poly.splitting_field('t'))]
                    if len(roots) == 1:
                        roots = roots*2
                    PmQ[i1] = roots[0]*PmQ[i0]
                    PQ[i1] = roots[1]*PQ[i0]

                    M = Matrix([[PmQ[i0], PmQ[i1]], [PQ[i0], PQ[i1]]])
                    if not M.is_invertible():
                        continue
                    for i in range(ng):
                        if i == i0 or i == i1:
                            continue
                        v = Vector([kappa0[i], kappa1[i]])
                        w = M.solve_left(v)
                        PmQ[i] = w[1]
                        PQ[i] = w[0]
                    return point0.point(PQ), point0.point(PmQ)
        else:
            L = [(chi, i, i0) for chi in range(twog) for i in range(ng)]
        r = point0.addition_formula(self, other, L)
        for i in range(ng):
            PQ[i] = sum([r[(chi, i, i0)] for chi in range(twog)])
        if all([coor == 0 for coor in PQ]):
            return self._add(other, i0 + 1)
        return point0.point(PQ)

    def _neg_(self):
        """
        Computes the addition oposite of self.
        """
        point0 = self.abelian_variety()
        D = point0._D
        mPcoord = [0]*point0._ng
        idx = point0._char_to_idx
        for i in D:
            mPcoord[idx(-i)] = self[idx(i)]
        return point0.point(mPcoord)

    def _rmul_(self, k):
        return self._mult(k, algorithm='Montgomery')

    def _mult(self, k, algorithm):
        ##TODO: Maybe we should add some checks to make sure that `k` is an integer
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
            for i in range(2, len(kb)+1):
                nP = nP.diff_add(nP,point0)
                if kb[-i] == 1:
                    nP = nP + self
            return nP;
        raise NotImplementedError

    def diff_multadd(self, k, PQ, Q):
        """
        // return kP+Q, kP
        // (if we don't need kP, then we don't need to compute kP, only (k/2)P, so
        // we lose 2 differential additions. Could be optimized here.
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
        if PQ == None:
            if self.abelian_variety()._level == 2:
                raise NotImplementedError
            PQ = self + Q
        point0 = self.abelian_variety()._thetanullpoint
        lPQ, lP = self.diff_multadd(l,PQ,Q)
        PlQ, lQ = Q.diff_multadd(l,PQ,self)
        r, k0P = lP.equal_points(point0, proj=True, factor=True)
        assert r, "Bad pairing!"+str(P)
        r, k0Q = lQ.equal_points(point0, proj=True, factor=True)
        assert r, "Bad pairing!"+str(Q)
        r, k1P = PlQ.equal_points(self, proj=True, factor=True)
        assert r
        r, k1Q = lPQ.equal_points(Q, proj=True, factor=True)
        assert r
        return k1P*k0P/(k1Q*k0Q)
