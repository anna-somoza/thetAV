# ****************************************************************************
#       Copyright (C) 2020 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
from __future__ import print_function, division, absolute_import

import math

import sage.plot.all as plot

from sage.rings.padics.factory import Qp
from sage.rings.padics.precision_error import PrecisionError

import sage.rings.all as rings
from sage.rings.real_mpfr import is_RealField
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
import sage.groups.generic as generic
from sage.libs.pari import pari
from cypari2.pari_instance import prec_words_to_bits
from sage.structure.sequence import Sequence
from sage.structure.richcmp import richcmp

from sage.schemes.curves.projective_curve import Hasse_bounds
from sage.schemes.generic.morphism import (SchemeMorphism,
                                           is_SchemeMorphism,
                                           SchemeMorphism_point)
from sage.schemes.generic.morphism import is_SchemeMorphism
from sage.structure.element import AdditiveGroupElement
from sage.misc.constant_function import ConstantFunction


class AbelianVarietyPoint(AdditiveGroupElement, SchemeMorphism_point):
    def __init__(self, X, v, good_lift=False, check=False):
        """
        Constructor for a point on an abelian variety.

        INPUT:

        - X -- an abelian variety
        - v -- data determining a point (another point or a tuple of coordinates)
        
        """
        point_homset = X.point_homset()
        if is_SchemeMorphism(v) or isinstance(v, AbelianVarietyPoint):
            v = list(v)
        if check:
            pass
        #TODO: check that v is a list of the right length!
        if v == 0 or v == (0,):
            v = X._thetanullpoint
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

    def _richcmp_(self, other, op):
        """
        Comparison function for points to allow sorting and equality testing.
        """
        ##this is actually not used because here we can assume that they belong
        # both to the same parent
        if not isinstance(other, AbelianVarietyPoint):
            print ('here')
            try:
                other = self.codomain().ambient_space()(other)
            except TypeError:
                return NotImplemented
        ##TODO: Actually we should compare them as projective points, since we 
        # haven't normalized, or maybe it's ok like this since we care about the affine repr also
        return richcmp(self._coords, other._coords, op) 

    def good_lift(self):
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

    def diff_add(self, Q, PmQ):
        point0 = self.abelian_variety()
        D = point0._D
        twotorsion = point0._twotorsion
        PQ = [0]*D.cardinality()
        idx = point0._char_to_idx
        lvl2 = (point0._level == 2)
        if lvl2:
            char = point0._idx_to_char
        i0 = PmQ.get_nonzero_coord()
        L = []
        for i in range(D.cardinality()):
            if PmQ[i] == 0:
                j = i0
            else:
                j = i
            if PmQ[i] == 0 and lvl2:
                L += [(chi, i, j) for chi in range(twotorsion.cardinality()) if eval_car(char(chi, True),char(i) + char(j)) == 1] ##Change eval_car to accept also integers?
            else:
                L += [(chi, i, j) for chi in range(twotorsion.cardinality())]
        r = point0.addition_formula(self, Q, L) ##Change addition_formula to take integers
        for i in range(D.cardinality()):
            if PmQ[i] == 0:
                j = i0
            else:
                j = i
            if PmQ[i] == 0 and lvl2:
                cartosum = {chi for chi in range(twotorsion.cardinality()) if eval_car(chi,i+j) == 1}
                PQ[i] = sum([r[(chi,i,j)] for chi in cartosum])/(PmQ[j]*len(cartosum))
            else:
                PQ[i] = sum([r[(chi,i,j)] for chi in range(twotorsion.cardinality())])/(twotorsion.cardinality() * PmQ[j]);
        if lvl2:
            for i in range(D.cardinality()):
                # // in level 2, in this case we only computed
                # // PQ[i]PmQ[j]+PQ[j]PmQ[i] so we correct to get PQ[i]
                # // we have to do it here to be sure we have computed PQ[j]
                if PmQ[i] == 0:
                    PQ[i] += - PQ[j]*PmQ[i]/PmQ[j]
        return AbelianVarietyPoint(point0, PQ)


