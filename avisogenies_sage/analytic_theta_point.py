"""
Analytic theta null point and theta point.


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

from sage.structure.element import is_Vector, parent
from sage.functions.other import sqrt
from itertools import product
from sage.schemes.hyperelliptic_curves.hyperelliptic_g2 import HyperellipticCurve_g2
from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
from sage.schemes.hyperelliptic_curves.jacobian_morphism import JacobianMorphism_divisor_class_field
from sage.schemes.generic.morphism import SchemeMorphism_point

from sage.rings.all import ZZ, Zmod, Integer
integer_types = (int, Integer)

from .theta_null_point import AbelianVariety_ThetaStructure, KummerVariety
from .morphisms import MumfordToLevel4ThetaPoint
from .eta_maps import eta


class AnalyticThetaPoint:
    """
    Components:
    - level, // an integer
    - coord, // a ThetaStructure of level 2 and g = 2*g
    
    .. todo::
    
        - Add examples to all class functions
        
        - Add _repr_ to the classes and modify the examples accordingly
        
        - Field of definition
    """
    def __init__(self, thc, v):  #Equivalent to "AnalyticThetaPoint" intrinsic method in magma
        l = thc._level
        if l != 2 and l != 4:
            raise NotImplementedError

        if v == 0 or v == (0,):
            v = thc._coords
        R = thc._R
        self._coords = tuple(R(el) for el in v)
        self._codomain = thc
        
    @classmethod
    def from_divisor(cls, D, data=None):
        """
        Given a divisor in Mumford coordinates (u, v), compute the corresponding
        theta point.
        """
        if not isinstance(D, JacobianMorphism_divisor_class_field):
            raise NotImplementedError
        if data == None:
            C = D.scheme().curve()
            th = AnalyticThetaNullPoint.from_curve(C)
            wp, rt = th._data[1:]
        elif isinstance(data, AnalyticThetaNullPoint):
            th = data
            _, wp, rt = th._data
        else:
            th, wp, rt = data
        u, v = D
        points = sum(([(x, v(x))]*mult for x, mult in u.roots(u.splitting_field('z'))), [])
        return MumfordToLevel4ThetaPoint(wp, rt, th, points)
        
    @classmethod
    def from_algebraic(cls, th, thc=None):
        """
        Let th be a theta point given by algebraic coordinates (i.e. :class:`AbelianVarietyPoint`, :class:`KummerVarietyPoint`). Compute the
        corresponding theta null point in analytic coordinates (i.e. :class:`ThetaNull_Analytic`).
        """
        tnp = th.scheme()
        O = tnp.theta_null_point()
        n = tnp._level
        g = tnp._dimension
        D = tnp._D
        point = [0]*(4**g)
        idx = tnp._char_to_idx

        if thc == None:
            import avisogenies_sage.analytic_theta_point as ATP
            thc = ATP.AnalyticThetaNullPoint.from_algebraic(tnp)

        if n == 2:
            for (idxa, a), (idxb, b) in product(enumerate(D), repeat=2):
                point[idxa + 2**g*idxb] = sum((-1)**ZZ(a*beta)*th[idx(b + beta)]*O[idxbeta] for idxbeta, beta in enumerate(D))/2**g

            return thc(point)

        if n == 4:
            twotorsion = tnp._twotorsion #Zmod(2)^g
            for (idxa, a), (idxb, b) in product(enumerate(twotorsion), repeat=2):
                Db = D(list(b))
                point[idxa + 2**g*idxb] = sum((-1)**(a*beta)*th[idx(Db + beta)] for beta in twotorsion)/2**g

            return thc(point)

        raise NotImplementedError

    def abelian_variety(self):
        """
        Return the thetanullpoint associated to this theta point.
        """
        return self._codomain

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

    def __repr__(self):
        """
        Return a string representation of this point.
        """
        return f'({" : ".join(repr(f) for f in self._coords)})'

    def to_algebraic(self, A = None): # Corresponds to `AnalyticToAlgebraicThetaPoint` in magma
        """
        Compute the algebraic theta point corresponding to an analytic theta point.

        INPUT:

        - ``self``- a theta null point given by analytic coordinates (see :class:`AnalyticThetaPoint`).

        - ``g``- the dimension of the ab. variety? #Maybe it should be a variable in self?

        OUTPUT:

        The corresponding theta point in algebraic coordinates (see :class:`AbelianVarietyPoint`, :class:`KummerVarietyPoint`)
        """
        thc = self.abelian_variety()
        n = thc._level
        g = thc._dimension
        ng = n**g
        point = [0]*ng
        idx = thc._char_to_idx

        if A == None:
            A = thc.to_algebraic()

        if n == 2:
            for b in range(ng):
                point[b] = sum(self[a + 2**g*b] for a in range(ng))
            return A(point)

        #if n == 4:
        D = Zmod(n)**g
        twotorsion = Zmod(2)**g
        V = ZZ**g

        for idxb, b in enumerate(D): #char(b) in Zmod(4)^g
            for a in twotorsion:
                ttb = twotorsion(list(b))
                ib = D((V(b) - V(ttb))/2)
                sign = (-1)**ZZ(a*ib)
                point[idxb] += self[idx(a, ttb)]*sign

        return A(point)
        
    def add_twotorsion_point(self, eta):
        """
        Add the two torsion points corresponding to the caracteristic eta to self.

        EXAMPLES ::

            sage: from avisogenies_sage import KummerVariety, AnalyticThetaPoint
            sage: from avisogenies_sage.eta_maps import eta
            sage: g = 2; A = KummerVariety(GF(331), 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: thp = AnalyticThetaPoint.from_algebraic(P)
            sage: thp.add_twotorsion_point(eta(g, 2))._coords #FIXME change when _repr_ is done.
            (163, 328, 50, 185, 96, 217, 63, 183, 53, 307, 229, 76, 56, 118, 48, 199)
            
        .. todo:: Address FIXME.
        """
        thc = self.abelian_variety()
        level = thc._level
        Ab = thc._numbering
        g = thc._dimension
        idx = thc._char_to_idx

        if level == 2:
            t = [(-1)**ZZ(eta[:g]*e[g:])*self[idx(e + eta)] for e in Ab]
            return thc(t)

        if level == 4:
            t = self._coords
            for idxe, e in enumerate(Ab):
                t[idxe] *= (-1)**ZZ(e[:g]*eta[g:] + eta[:g]*e[g:])
            return thc(t)

        raise NotImplementedError('Only implemented for level 2 and 4.')

class AnalyticThetaNullPoint:
    """
    Class for analytic theta null points.

    For level 2, the basis used is F(2,2)^2.
    For level 4, the basis used is F(2,2).

    See Section 3.1.2 in [Coss]_ for the definition of the notation.
    """

    def __init__(self, R, l, g, v, data = None): #Equivalent to "AnalyticThetaNullPoint" intrinsic method in magma
        if l != 2 and l != 4:
            raise NotImplementedError
        if is_Vector(v):
            v = list(v)
        if not isinstance(v, (list, tuple, SchemeMorphism_point)):
            raise TypeError(f"Argument (v={v}) must be a list, a tuple, a vector or a point.")
        if not isinstance(l, integer_types + (Integer,)):
            raise TypeError(f"Argument (l={l}) must be an integer.")
        if not isinstance(g, integer_types + (Integer,)):
            raise TypeError(f"Argument (g={g}) must be an integer.")
        self._level = l
        if len(v) != 2**(2*g):
            raise ValueError(f'v(={v}) does not define a valid analytic thetanullpoint')
        self._R = R
        self._coords = tuple(R(el) for el in v)
        self._dimension = g
        self._numbering = Zmod(2)**(2*g)
        if data!=None:
            self._data = data
        
    @classmethod
    def from_curve(cls, C):
        """
        Given a hyperelliptic curve of genus 2, returns the analytic
        theta null point of level 4.
        
        EXAMPLES ::
        
            sage: from avisogenies_sage import AnalyticThetaNullPoint
            sage: F = GF(83^2); Fx.<X> = PolynomialRing(F)
            sage: a = [0, 1, 3, 15, 20]
            sage: C = HyperellipticCurve(prod(X - al for al in a)); C
            Hyperelliptic Curve over Finite Field in z2 of size 83^2 defined by y^2 = x^5 + 44*x^4 + 28*x^3 + 23*x^2 + 70*x
            sage: th = AnalyticThetaNullPoint.from_curve(C); th
            (1 : 37 : 56 : 57 : 34*z + 43 : 0 : 50*z + 73 : 0 : 30 : 2*z + 82 : 0 : 0 : 16*z + 37 : 0 : 0 : 61*z + 21)
            
        """
        if not isinstance(C, HyperellipticCurve_g2):
            raise NotImplementedError('Thomae formulas are only implemented for curves of genus 2')
        f, h = C.hyperelliptic_polynomials()
        if h != 0:
            f = f + h**2/4
        if f.degree() % 2 == 0:
            C2 = HyperellipticCurve(f)
            f, _ = C2.odd_degree_model().hyperelliptic_polynomials()
        F = f.splitting_field('z')
        z, = F.gens()
        a = f.roots(F, multiplicities=False)
        a.sort()
        if a[:2] == [0,1]:
            l, m, n = a[2:]
        else:
            l, m, n = [(el - a[0])/(a[0] - a[1]) for el in a[2:]]
        D = Zmod(2)**4
        ng = 2**4
        idx = lambda i : ZZ(list(i), 2)
        th4 = [m/(l*n),m*(l-m)*(n-1)/(n*(m-1)*(l-n)),m*(l-1)*(n-1)/(l*n*(m-1)),m*(l-1)*(n-m)/(l*(n-l)*(m-1))]
        th2 = [F(1)] + [F(0)]*(ng-1)
        if not all([el.is_square() for el in th4]):
            F, to_F = F.extension(2, map=True)
            z = F.gens()
            th4 = [to_F(el) for el in th4]
        for i, ei in enumerate(D.gens()):
            th2[idx(ei)] = sqrt(th4[i])
        th2[idx([1,0,0,1])] = 1/n*th2[idx([0,0,0,1])]/th2[idx([1,0,0,0])]
        th2[idx([1,1,0,0])] = 1/l*th2[idx([0,1,0,0])]/th2[idx([1,0,0,0])]
        th2[idx([0,0,1,1])] = (n-1)*th2[idx([1,0,0,0])]*th2[idx([1,0,0,1])]/th2[idx([0,0,1,0])]
        th2[idx([0,1,1,0])] = (l-1)*th2[idx([1,0,0,0])]*th2[idx([1,1,0,0])]/th2[idx([0,0,1,0])]
        th2[idx([1,1,1,1])] = (n-m)/(n-1)*th2[idx([0,0,1,0])]*th2[idx([1,1,0,0])]/th2[idx([0,0,0,1])]
        if not all([el.is_square() for el in th2]):
            F, to_F = F.extension(2, map=True)
            z, = F.gens()
            th2 = [to_F(el) for el in th2]
        th = [sqrt(el) for el in th2]
        wp = [F(el) for el in [0,1,l,m,n]]
        return cls(F, 4, 2, th, data=[C, wp, F(1)])
        
    @classmethod
    def from_algebraic(cls, thc):
        """
        Let thc be a theta null point given by algebraic coordinates (i.e. :class:`AbelianVariety_ThetaStructure`, :class:`KummerVariety`). Compute the
        corresponding theta null point (i.e. :class:`AnalyticThetaNullPoint`) in analytic coordinates.
        """
        n = thc._level
        g = thc._dimension

        O = thc.theta_null_point()
        D = thc._D
        idx = thc._char_to_idx
        point = [0]*(4**g)
        R = thc.base_ring()
        
        if n == 2:
            for (idxa, a), (idxb, b) in product(enumerate(D), repeat=2):
                point[idxa + 2**g*idxb] = sum((-1)**ZZ(a*beta)*O[idx(b + beta)]*O[idxbeta] for idxbeta, beta in enumerate(D))/2**g

            return cls(R, n, g, point)

        if n == 4:
            twotorsion = thc._twotorsion #Zmod(2)^g
            for (idxa, a), (idxb, b) in product(enumerate(twotorsion), repeat=2):
                Db = D(list(b))
                point[idxa + 2**g*idxb] = sum((-1)**(a*beta)*O[idx(Db + beta)] for beta in twotorsion)/2**g

            return cls(R, n, g, point)

        raise NotImplementedError
        
    def __eq__(self, X):
        """
        Compare the analytic theta null point self to X.  If X is an
        analytic theta null point, then self and X are equal if and only
        if their fields of definition are equal and their theta null 
        points are equal as projective points.
        """
        if not isinstance(X, type(self)):
            return NotImplemented
        if self._R != X._R:
            return False
        return self._coords == X._coords

    def _idx_to_char(self, x):
        """
        Return the caracteristic in D that corresponds to a given integer index.
        """
        g = self._dimension
        n = 2
        D = self._numbering
        return D(ZZ(x).digits(n, padto=2*g))

    def _char_to_idx(self, *x):
        """
        Return the integer index that corresponds to a given caracteristic in D.
        """
        return ZZ(sum((list(elem) for elem in x), []), 2)

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

    _point = AnalyticThetaPoint

    def __repr__(self):
        """
        Return a string representation of this point.
        """
        return f'({" : ".join(repr(f) for f in self._coords)})'

    def to_algebraic(self): #Equivalent to `AnalyticToAlgebraicThetaNullPoint` in magma
        """
        Compute the algebraic theta null point corresponding to an analytic theta null point.

        INPUT:

        - ``self``- a theta null point given by analytic coordinates (see :class:`AnalyticThetaNullPoint`).

        OUTPUT:

        The corresponding theta null point in algebraic coordinates (see :class:`AbelianVariety_ThetaStructure`, :class:`KummerVariety`)
        
        .. todo:: Address FIXME.
        """

        try:
            return self._algebraic
        except AttributeError:
            pass

        n = self._level
        g = self._dimension
        ng = n**g
        point = [0]*ng
        R = parent(self._coords[0]) #FIXME

        if n == 2:
            for b in range(ng): #char(b) in Zmod(2)^g
                point[b] = sum(self._coords[a + 2**g*b] for a in range(ng))
            assert point[0] != 0 #See Equation (3.12) in [Coss]
            return KummerVariety(R, g, point)

        #if n == 4:            
        D = Zmod(n)**g
        twotorsion = Zmod(2)**g
        if not D.has_coerce_map_from(twotorsion):
            from sage.structure.coerce_maps import CallableConvertMap
            s = n//2
            def c(P, el):
                return P(s*el.change_ring(ZZ))
            c = CallableConvertMap(twotorsion, D, c)
            D.register_coercion(c)

        V = ZZ**g
        idx = self._char_to_idx

        for idxb, b in enumerate(D): #char(b) in Zmod(4)^g
            for a in twotorsion:
                ttb = twotorsion(b)
                ib = D((V(b) - V(ttb))/2) #Probably very inefficient, look for an alternative
                sign = (-1)**ZZ(a*ib)
                point[idxb] += self._coords[idx(a, ttb)]*sign

        self._algebraic = AbelianVariety_ThetaStructure(R, n, g, point)
        return self._algebraic
