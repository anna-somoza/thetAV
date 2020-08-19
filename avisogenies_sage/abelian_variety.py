"""
Abelian varieties

This module defines the base class of Abelian varieties with theta structure
as an abstract Scheme.

AUTHORS:

- Anna Somoza (2020)

"""
#*****************************************************************************
#       Copyright (C) 2020 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from itertools import product, combinations_with_replacement
from .av_point import AbelianVarietyPoint
from .tools import ThetaStructure

from sage.categories.fields import Fields
_Fields = Fields()
from sage.rings.all import Integer, ZZ, Zmod
integer_types = (int, Integer)

from sage.structure.element import is_Vector

from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.schemes.generic.algebraic_scheme import AlgebraicScheme
from sage.schemes.generic.morphism import SchemeMorphism_point
from sage.schemes.generic.homset import SchemeHomset_points
from sage.structure.richcmp import richcmp_method, richcmp

#Note that there is a constructor with the name AbelianVariety. Either overwrite it
#or change name. Maybe create different possible constructors? See EllipticCurve.
@richcmp_method
class AbelianVariety(AlgebraicScheme):
    """
    Base class for Abelian Varieties with theta structure. TODO: Write what base we're taking for the theta structure.

    INPUT:

    -  ``R`` - a field of definition

    -  ``n`` - an integer - the level of the theta structure.

    -  ``g`` - an integer - the dimension of the abelian variety.

    -  ``T`` - a ThetaStructure of length n^g - the theta null point determining the abelian variety.

    EXAMPLES::

        sage: FF = GF(331)
        sage: A = AbelianVariety(FF, 2,2,[328,213,75,1]); A
        Abelian variety of dimension 2 with theta null point (328 : 213 : 75 : 1)
    """
    _point = AbelianVarietyPoint

    def __init__(self, R, n, g, T, check=False):
        """
        Initialize.
        """
        if is_Vector(T):
            T = list(T)
        if not isinstance(T, (list, tuple, SchemeMorphism_point)):
            raise TypeError("Argument (=%s) must be a list, a tuple, a vector or a point."%T)
        if not isinstance(n, integer_types):
            raise TypeError("Argument (=%s) must be an integer."%n)
        if not isinstance(g, integer_types):
            raise TypeError("Argument (=%s) must be an integer."%g)
        if R not in _Fields:
            raise TypeError("T (=%s) must be defined over a field."%T)
        if len(T) != n**g:
            raise ValueError("T (=%s) must have length n^g (=%s)."%(T, n**g))

        D = Zmod(n)**g
        twotorsion = Zmod(2)**g
        if not D.has_coerce_map_from(twotorsion):
            from sage.matrix.constructor import identity_matrix
            c = twotorsion.hom(n//2*identity_matrix(g), D)
            D.register_coercion(c)

        T = ThetaStructure(T, n)
        
        if check:
            dual = ThetaStructure(level=[2,n,n], g=g)
            DD = [2*d for d in D]

            for i in D:
                if T[i] != T[-i]:
                    raise ValueError('The given list does not define a valid thetanullpoint')

            for chi, i, j in product(twotorsion, D, D):
                ii, jj, tt = reduce_twotorsion_couple(i, j);
                if dual[chi, ii, jj] == None:
                    dual[chi, ii, jj] = sum(eval_car(chi,t)*T[ii + t]*T[jj + t] for t in twotorsion)
                dual[chi,i,j] = eval_car(chi,tt)*dual[chi, ii, jj]

            for (i, j), (k, l) in combinations_with_replacement(combinations_with_replacement(D,2), 2):
                if i + j + k + l in DD:
                    m = D([ZZ(x)/2 for x in i + j + k + l])
                    for chi in twotorsion:
                        if dual[chi, i, j]*dual[chi, k, l] != dual[chi, m-i, m-j]*dual[chi, m-k, m-l]:
                            raise ValueError('The given list does not define a valid thetanullpoint')

        PP = ProjectiveSpace(R, n**g -1) #Do we need this?
        self._dimension = g
        self._level = n
        self._ng = n**g #To have easy access to the size of D
        #Try to create a projective scheme class, it will give us the projective space associated to it
        AlgebraicScheme.__init__(self, PP)

        self._thetanullpoint = self(tuple(R(a) for a in T))
        self._D = D
        self._twotorsion = twotorsion
        self._riemann = ThetaStructure(level=[2,n,n], g=g)
        if check:
            self._dual = dual
        else:
            self._dual = ThetaStructure(level=[2,n,n], g=g)


    def __richcmp__(self, X, op):
        """
        Compare the Abelian Variety self to `X`.  If `X` is an Abelian Variety,
        then self and `X` are equal if and only if their theta null points are
        equal as projective points.
        """
        if not isinstance(X,AbelianVariety):
            return NotImplemented
        #Question: If the fields of def are different, should this say False?
        return richcmp(self.coords, X.coords, op)

    def _repr_(self):
        """
        Return a string representation of this Abelian variety.
        """
        return "Abelian variety of dimension %s with theta null point %s" % (self.dimension, self.thetanullpoint)

    @property
    def dimension(self):
        """
        Return the dimension of this Abelian Variety.
        """
        return self._dimension

    @property
    def level(self):
        """
        Return the level of the theta structure.
        """
        return self._level

    @property
    def thetanullpoint(self):
        """
        Return the theta null points as a point of the abelian variety.
        """
        return self._thetanullpoint

    @property
    def coords(self):
        """
        Return the theta null points as a list.
        """
        return self.thetanullpoint._coords

    @property
    def numbering(self):
        """
        """
        return self._D

    @property
    def two_torsion(self):
        """
        """
        return self._twotorsion

    @property
    def data(self):
        """
        Return a tuple with the level, dimension, numbering group and twotorsion numbering group
        of self.
        """
        return self.level, self.dimension, self.numbering, self.two_torsion

    def change_ring(self, R):
        """
        Return the Abelian Variety over the ring `R`.

        INPUT:

        - ``R`` -- a field. The new base ring.

        OUTPUT:

        The Abelian Variety over the ring `R`.
        """
        return AbelianVariety(R, self.level, self.dimension, self.theta_null_point)

    def base_extend(self, R):
        """
        Return the natural extension of ``self`` over `R`

        INPUT:

        - ``R`` -- a field. The new base field.

        OUTPUT:

        The Abelian Variety over the ring `R`.
        """
        if R not in _Fields:
            raise TypeError("Argument (=%s) must be a field."%R)
        if self.base_ring() is R:
            return self
        if not R.has_coerce_map_from(self.base_ring()):
            raise ValueError('no natural map from the base ring (=%s) to R (=%s)!'
                             % (self.base_ring(), R))
        return self.change_ring(R)

    def _point_homset(self, *args, **kwds):
        return SchemeHomset_points(*args, **kwds)

    def point(*args, **kwds):
        """
        Create a point.

        INPUT:

        - ``v`` -- anything that defines a point

        - ``check`` -- boolean (optional, default: ``False``); whether
          to check the defining data for consistency

        OUTPUT:

        A point of the scheme.
        """
        self = args[0]
        return self._point(*args, **kwds)

    __call__ = point

    #TODO: check all places where is used and remove (see get_nonzero_coordinate in av_point. As an alternative, programe it as a method of ThetaStructure.
    def _idx_to_char(self, x, twotorsion=False):
        """
        Return the caracteristic in D that corresponds to a given integer index.
        """
        g = self.dimension
        if twotorsion:
            n = 2
            D = self._twotorsion
        else:
            n = self.level
            D = self._D
        return D(ZZ(x).digits(n, padto=g))

    # def _char_to_idx(self, x, twotorsion=False):
        # """
        # Return the integer index that corresponds to a given caracteristic in D.
        # """
        # if twotorsion:
            # n = 2
        # else:
            # n = self.level
        # return ZZ(list(x), n)

    def riemann_relation(self, chi, i=None, j=None):
        """
        Computes the riemann relation associated to a given chi, i, j and stores it in P._riemann.
        Depends on which coordinates of P are zero.

        INPUT:

        -  ``P`` - a theta null point

        -  ``chi`` - a character, given by its dual element in Z(2) as a subset of Z(n).

        -  ``i`` - the index of a coordinate of P. For now we are assuming that they are an
        element of Zmod(n)^g.

        -  ``j`` - the index of a coordinate of P. For now we are assuming that they are an
        element of Zmod(n)^g.
        """
        #TODO this cold be handled by an *args type of input (I think)
        if i == None and j == None:
            if len(chi) != 3:
                raise TypeError("Input should be a tuple of length 3 or 3 elements.")
            chi, i, j = chi
        elif i == None or j == None:
            raise TypeError("Input should be a tuple of length 3 or 3 elements.")

        D = self.numbering
        DD = [2*d for d in D]
        twotorsion = self.two_torsion
        if self._riemann[chi, i, j] != None:
            return
        i, j, tij = reduce_twotorsion_couple(i,j)
         # we try to find k and l to apply the addition formulas such that
         # we can reuse the maximum the computations
         # for a differential addition, i == j (generically) and we take k = l = 0
         # for a normal addition, j = 0 so we take k = i, l = j.
        if i == j:
            k0 = D(0)
            l0 = D(0)
        else:
            k0 = i
            l0 = j

        for u, v in product(D,D):
            if u + v not in DD:
                continue
            k, l, _ = reduce_symtwotorsion_couple(k0 + u, l0 + v);
            el = (chi, k, l)
            if self._dual[el] == None:
                self._dual[el] = sum(eval_car(chi,t)*self.thetanullpoint[k + t]*self.thetanullpoint[l + t] for t in twotorsion)
            if self._dual[el] != 0:
                kk = k0 + u
                ll = l0 + v
                break
        else: #If we leave the for loop without encountering a break
            for t in twotorsion:
                self._riemann[chi, i+t, j+t] = []
            return
            
        kk0, ll0, tkl = reduce_symtwotorsion_couple(kk, ll)
        i2, j2, k2, l2 = get_dual_quadruplet(i, j, kk, ll)
        i20, j20, tij2 = reduce_twotorsion_couple(-i2, j2)
        k20, l20, tkl2 = reduce_twotorsion_couple(k2, l2)
        for t in twotorsion:
            self._riemann[chi, i + t, j + t] = [i, j, t, kk0, ll0, tkl, i20, j20, tij2, k20, l20, tkl2]
        return

    def addition_formula(self, P, Q, L):
        """
        Given two points P and Q and a list L containing triplets [chi, i, j] (of lists, not of integers), compute
        sum_{t in Z(2)} chi(t) PpQ[i + t] PmQ[j + t]
        for every given triplet.

        NOTE:
        
            Q should be the point living in the big field
        """
        twotorsion = self.two_torsion
        n = self.level
        g = self.dimension
        r = ThetaStructure(level=[2,n,n], g=g)
        for el in L:
            if r[el] != None:
                continue
            #TODO: Are we sure that this pair (i,j) is reduced as in riemann? Or it is not 
            #done like that? check.
            if self._riemann[el] == None:
                #TODO: We can also make it a function that returns said riemann relations,
                #and if they are not computed yet, it computes them and then returns them!
                # That would deal with 4 lines of code and also give a public method to access _riemann.
                self.riemann_relation(el) 
            IJ = self._riemann[el]
            if len(IJ) == 0:
                raise ValueError("Can't compute the addition! Either we are in level 2 and \
                                 computing a normal addition, or a differential addition with \
                                 null even theta null points.")
            ci0, cj0 = IJ[0:2]
            k0, l0 = IJ[3:5]
            ci20, cj20 = IJ[6:8]
            ck20, cl20 = IJ[9:11]
            #If we only want the addition, why not store _riemann only with that?
            tt = IJ[2] + IJ[5] + IJ[8] + IJ[11]

            chi = el[0]

            s1 = sum(eval_car(chi,t)*Q[ci20 + t]*Q[cj20 + t] for t in twotorsion)
            s2 = sum(eval_car(chi,t)*P[ck20 + t]*P[cl20 + t] for t in twotorsion)
            A = self._dual[chi, k0, l0]
            # Comment from the Magma implementation:
            # we prefer to store the data in Q because for a differential
            # addition we will have i2=j2=0, so in level 4, we gain.
            # s1A = s1/A
            S = eval_car(chi, tt)*s2*s1/A
            for t in twotorsion:
                r[chi, ci0+t, cj0+t] = eval_car(chi,t)*S
        return r


##TODO: Warning, the twotorsion elements should be returned as elements in the twotorsion.
def reduce_sym(x):
    return min(x, -x)

def reduce_twotorsion(x):
    r = list(x)
    D = x.parent()
    halflevels =[i.order()//2 for i in D.gens()]
    n = D.rank()
    for i in range(n):
        if r[i] >= halflevels[i]:
            r[i] = r[i] - halflevels[i];
    return  D(r), x-D(r)

def reduce_symtwotorsion(x):
    x1, tx1 = reduce_twotorsion(x)
    x2, tx2 = reduce_twotorsion(-x)
    if x1 <= x2:
        return x1, tx1
    return x2, tx2

def reduce_symcouple(x,y):
    xred = reduce_sym(x)
    yred = reduce_sym(y)
    if xred < yred:
        return xred, yred
    return yred, xred

def reduce_twotorsion_couple(x,y):
    xred, tx = reduce_twotorsion(x)
    yred, ty = reduce_twotorsion(y)
    if xred < yred:
        return xred, y+tx, tx
    return yred, x+ty, ty

def reduce_symtwotorsion_couple(x,y):
    xred, tx = reduce_symtwotorsion(x)
    yred, ty = reduce_symtwotorsion(y)
    if xred < yred:
        return xred, reduce_sym(y+tx), tx
    return yred, reduce_sym(x+ty), ty

def get_dual_quadruplet(x, y, u, v):
    r = x + y + u + v
    z = r.parent()([ZZ(e)//2 for e in list(r)])
    xbis = z - x
    ybis = z - y
    ubis = z - u
    vbis = z - v
    return xbis, ybis, ubis, vbis

def eval_car(chi,t):
    if chi.parent() != t.parent():
        r = list(t)
        D = t.parent()
        twotorsion = chi.parent()
        halflevels =[i.order()//2 for i in D.gens()]
        n = D.rank()
        for i in range(n):
            r[i] = ZZ(r[i])/halflevels[i]
        t = twotorsion(r)
    return ZZ(-1)**(chi*t);
