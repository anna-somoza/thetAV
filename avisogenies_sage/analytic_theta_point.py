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

from itertools import product

from sage.functions.other import sqrt
from sage.rings.all import ZZ, Zmod, Integer
from sage.schemes.generic.morphism import SchemeMorphism_point
from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
from sage.schemes.hyperelliptic_curves.hyperelliptic_g2 import HyperellipticCurve_g2
from sage.schemes.hyperelliptic_curves.jacobian_morphism import JacobianMorphism_divisor_class_field
from sage.structure.element import is_Vector, parent

from .aux_hyper import remove_h, odd_degree_model, rosenhain_model
from .morphisms_level2 import MumfordToLevel2ThetaPoint
from .morphisms_level4 import MumfordToLevel4ThetaPoint
from .theta_null_point import AbelianVariety_ThetaStructure, KummerVariety
from .theta_point import VarietyThetaStructurePoint

integer_types = (int, Integer)


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

    def __init__(self, thc, v):  # Equivalent to "AnalyticThetaPoint" intrinsic method in magma
        lvl = thc.level()
        if lvl not in [2, 4]:
            raise NotImplementedError

        if v == 0 or v == (0,):
            v = thc._coords
        R = thc._R
        self._level = lvl
        self._coords = tuple(R(el) for el in v)
        self._codomain = thc

    @classmethod
    def from_divisor(cls, th, D):
        """
        Given a divisor in Mumford coordinates (u, v), compute the corresponding
        theta point.
        """
        if not isinstance(D, JacobianMorphism_divisor_class_field):
            raise NotImplementedError
        C, phi = th.curve(phi=True)
        if D.scheme().curve() != C:
            raise ValueError
        wp = th._weierstrass_points()
        rt = th._root()
        u, v = D
        if phi is None or phi.codomain() == C:
            points = sum(([(x, v(x))] * mult for x, mult in u.roots()), [])
        else:
            points = sum(([phi([x, v(x), 1])] * mult for x, mult in u.roots()), [])
        if len(points) != u.degree():
            raise ValueError('Support not defined over field of definition')
        if th.level() == 2:
            return MumfordToLevel2ThetaPoint(wp, th, points)
        if th.level() == 4:
            return MumfordToLevel4ThetaPoint(wp, rt, th, points)
        raise NotImplementedError

    @classmethod
    def from_algebraic(cls, th, thc=None):
        """
        Let th be a theta point given by algebraic coordinates (i.e. :class:`AbelianVarietyPoint`, :class:`KummerVarietyPoint`). Compute the
        corresponding theta null point in analytic coordinates (i.e. :class:`ThetaNull_Analytic`).
        """
        tnp = th.scheme()
        P0 = tnp.theta_null_point()
        n = tnp.level()
        g = tnp.dimension()
        D = tnp._D
        point = [0] * (4 ** g)
        idx = tnp._char_to_idx

        if thc is None:
            thc = AnalyticThetaNullPoint.from_algebraic(tnp)

        if n == 2:
            for (idxa, a), (idxb, b) in product(enumerate(D), repeat=2):
                point[idxa + 2 ** g * idxb] = sum(
                    (-1) ** ZZ(a * beta) * th[idx(b + beta)] * P0[idxbeta] for idxbeta, beta in enumerate(D)) / 2 ** g

            return thc.point(point)

        if n == 4:
            twotorsion = tnp._twotorsion  # Zmod(2)^g
            for (idxa, a), (idxb, b) in product(enumerate(twotorsion), repeat=2):
                Db = D(list(b))
                point[idxa + 2 ** g * idxb] = sum(
                    (-1) ** (a * beta) * th[idx(Db + beta)] for beta in twotorsion) / 2 ** g

            return thc.point(point)

        raise NotImplementedError

    def abelian_variety(self):
        """
        Return the thetanullpoint associated to this theta point.
        """
        return self._codomain

    def level(self):
        """
        Return the level of the thetanullpoint, 2 or 4.
        """
        return self._level

    def __getitem__(self, n):
        """
        Return the n-th coordinate of this point.
        """
        return self._coords[n]

    def __iter__(self):
        """
        Return the coordinates of this point as an iterator.
        """
        return iter(self._coords)

    def __repr__(self):
        """
        Return a string representation of this point.
        """
        return f'({" : ".join(repr(f) for f in self._coords)})'

    def to_algebraic(self, A=None):  # Corresponds to `AnalyticToAlgebraicThetaPoint` in magma
        """
        Compute the algebraic theta point corresponding to an analytic theta point.

        INPUT:

        - ``g``- the dimension of the ab. variety? #Maybe it should be a variable in self?

        OUTPUT:

        The corresponding theta point in algebraic coordinates (see :class:`AbelianVarietyPoint`, :class:`KummerVarietyPoint`)
        """
        thc = self.abelian_variety()
        n = thc.level()
        g = thc.dimension()
        ng = n ** g
        point = [0] * ng
        idx = thc._char_to_idx

        if A is None:
            A = thc.to_algebraic()

        if n == 2:
            for b in range(ng):
                point[b] = sum(self[a + 2 ** g * b] for a in range(ng))
            return A(point)

        # if n == 4:
        D = Zmod(n) ** g
        twotorsion = Zmod(2) ** g
        V = ZZ ** g

        for idxb, b in enumerate(D):  # char(b) in Zmod(4)^g
            for a in twotorsion:
                ttb = twotorsion(list(b))
                ib = D((V(b) - V(ttb)) / 2)
                sign = (-1) ** ZZ(a * ib)
                point[idxb] += self[idx(a, ttb)] * sign

        return A(point)

    def add_twotorsion_point(self, eta):
        """
        Add the two torsion points corresponding to the characteristic eta to self.

        EXAMPLES ::

            sage: from avisogenies_sage import KummerVariety, AnalyticThetaNullPoint
            sage: from avisogenies_sage.eta_maps import eta
            sage: g = 2; A = KummerVariety(GF(331), 2, [328 , 213 , 75 , 1])
            sage: P = A([255 , 89 , 30 , 1])
            sage: th = AnalyticThetaNullPoint.from_algebraic(A)
            sage: thp = th(P)
            sage: thp.add_twotorsion_point(eta(g, 2))._coords #FIXME change when _repr_ is done.
            (163, 328, 50, 185, 96, 217, 63, 183, 53, 307, 229, 76, 56, 118, 48, 199)
            
        .. todo:: Address FIXME.
        """
        thc = self.abelian_variety()
        level = thc.level()
        Ab = thc._numbering
        g = thc.dimension()
        idx = thc._char_to_idx

        if level == 2:
            t = [(-1) ** ZZ(eta[:g] * e[g:]) * self[idx(e + eta)] for e in Ab]
            return thc(t)

        if level == 4:
            t = self._coords
            for idxe, e in enumerate(Ab):
                t[idxe] *= (-1) ** ZZ(e[:g] * eta[g:] + eta[:g] * e[g:])
            return thc(t)

        raise NotImplementedError('Only implemented for level 2 and 4.')


class AnalyticThetaNullPoint:
    """
    Class for analytic theta null points.

    For level 2, the basis used is F(2,2)^2.
    For level 4, the basis used is F(2,2).

    See Section 3.1.2 in [Coss]_ for the definition of the notation.
    """

    def __init__(self, R, l, g, v, curve=None, phi=None, wp=None, rac=None):
        # Equivalent to "AnalyticThetaNullPoint" intrinsic method in magma
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
        if len(v) != 2 ** (2 * g):
            raise ValueError(f'v(={v}) does not define a valid analytic thetanullpoint')
        self._R = R
        self._coords = tuple(R(el) for el in v)
        self._dimension = g
        self._numbering = Zmod(2) ** (2 * g)
        self._curve = curve
        self._wp = wp
        self._rac = rac
        self._phi = phi
        self._algebraic = None

    @classmethod
    def from_curve(cls, C, level):
        """
        Given a hyperelliptic curve of genus 2, returns the analytic
        theta null point of level 2 or 4.
        
        EXAMPLES ::
        
            sage: from avisogenies_sage import AnalyticThetaNullPoint
            sage: F = GF(83^2); Fx.<X> = PolynomialRing(F)
            sage: a = [0, 1, 3, 15, 20]
            sage: C = HyperellipticCurve(prod(X - al for al in a)); C
            Hyperelliptic Curve over Finite Field in z2 of size 83^2 defined by y^2 = x^5 + 44*x^4 + 28*x^3 + 23*x^2 + 70*x
            sage: th = AnalyticThetaNullPoint.from_curve(C, 4); th
            (1 : 37 : 56 : 57 : 34*z2 + 43 : 0 : 50*z2 + 73 : 0 : 30 : 2*z2 + 82 : 0 : 0 : 16*z2 + 37 : 0 : 0 : 61*z2 + 21)
        
        TODO ::
            
            - Can we generalize to more curves? Genus 1? Genus >2?
            
        """
        if not isinstance(C, HyperellipticCurve_g2):
            raise NotImplementedError('Thomae formulas are only implemented for curves of genus 2.')
        F = C.base_ring()
        f, h = C.hyperelliptic_polynomials()
        phi = C.identity_morphism()
        if h != 0:
            phi = remove_h(phi)
            f, h = phi.codomain().hyperelliptic_polynomials()
        if f.degree() % 2 == 0:
            phi = odd_degree_model(phi)
            f, h = phi.codomain().hyperelliptic_polynomials()
        a = sum(([el] * m for el, m in f.roots()), [])
        if len(a) != 5:
            raise ValueError('No Rosenhain model exists over field of definition')
        a.sort()
        if a[:2] != [0, 1]:
            phi = rosenhain_model(phi)
            f, h = phi.codomain().hyperelliptic_polynomials()
            a = sum(([el] * m for el, m in f.roots()), [])
            a.sort()
        l, m, n = a[2:]
        D = Zmod(2) ** 4
        ng = 2 ** 4
        idx = lambda c: ZZ(list(c), 2)
        th4 = [m / (l * n), m * (l - m) * (n - 1) / (n * (m - 1) * (l - n)), m * (l - 1) * (n - 1) / (l * n * (m - 1)),
               m * (l - 1) * (n - m) / (l * (n - l) * (m - 1))]
        th2 = [F(1)] + [F(0)] * (ng - 1)
        if not all([el.is_square() for el in th4]):
            F, to_F = F.extension(2, map=True)
            th4 = [to_F(el) for el in th4]
        for i, ei in enumerate(D.gens()):
            th2[idx(ei)] = sqrt(th4[i])
        th2[idx([1, 0, 0, 1])] = 1 / n * th2[idx([0, 0, 0, 1])] / th2[idx([1, 0, 0, 0])]
        th2[idx([1, 1, 0, 0])] = 1 / l * th2[idx([0, 1, 0, 0])] / th2[idx([1, 0, 0, 0])]
        th2[idx([0, 0, 1, 1])] = (n - 1) * th2[idx([1, 0, 0, 0])] * th2[idx([1, 0, 0, 1])] / th2[idx([0, 0, 1, 0])]
        th2[idx([0, 1, 1, 0])] = (l - 1) * th2[idx([1, 0, 0, 0])] * th2[idx([1, 1, 0, 0])] / th2[idx([0, 0, 1, 0])]
        th2[idx([1, 1, 1, 1])] = (n - m) / (n - 1) * th2[idx([0, 0, 1, 0])] * th2[idx([1, 1, 0, 0])] / th2[
            idx([0, 0, 0, 1])]
        if level == 2:
            return cls(F, 2, 2, th2, curve=C, phi=phi, wp=[0, 1, l, m, n], rac=F(1))
        if not all([el.is_square() for el in th2]):
            F, to_F = F.extension(2, map=True)
            th2 = [to_F(el) for el in th2]
        th = [sqrt(el) for el in th2]
        wp = [F(el) for el in [0, 1, l, m, n]]
        return cls(F, 4, 2, th, curve=C, phi=phi, wp=wp, rac=F(1))

    @classmethod
    def from_algebraic(cls, thc):
        """
        Let thc be a theta null point given by algebraic coordinates (i.e. :class:`AbelianVariety_ThetaStructure`, :class:`KummerVariety`). Compute the
        corresponding theta null point (i.e. :class:`AnalyticThetaNullPoint`) in analytic coordinates.
        """
        n = thc.level()
        g = thc.dimension()

        O = thc.theta_null_point()
        D = thc._D
        idx = thc._char_to_idx
        point = [0] * (4 ** g)
        R = thc.base_ring()

        if n == 2:
            for (idxa, a), (idxb, b) in product(enumerate(D), repeat=2):
                point[idxa + 2 ** g * idxb] = sum(
                    (-1) ** ZZ(a * beta) * O[idx(b + beta)] * O[idxbeta] for idxbeta, beta in enumerate(D)) / 2 ** g

            return cls(R, n, g, point)

        if n == 4:
            twotorsion = thc._twotorsion  # Zmod(2)^g
            for (idxa, a), (idxb, b) in product(enumerate(twotorsion), repeat=2):
                Db = D(list(b))
                point[idxa + 2 ** g * idxb] = sum(
                    (-1) ** (a * beta) * O[idx(Db + beta)] for beta in twotorsion) / 2 ** g

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

    def __getitem__(self, n):
        """
        Return the n-th coordinate of this nullpoint.
        """
        return self._coords[n]

    def __iter__(self):
        """
        Return the coordinates of this nullpoint as an iterator.
        """
        return iter(self._coords)

    def level(self):
        """
        Return the level of the thetanullpoint, 2 or 4.
        """
        return self._level

    def dimension(self):
        """
        Return the level of the thetanullpoint, 2 or 4.
        """
        return self._dimension

    def _idx_to_char(self, x):
        """
        Return the characteristic in D that corresponds to a given integer index.
        """
        g = self.dimension()
        n = 2
        D = self._numbering
        return D(ZZ(x).digits(n, padto=2 * g))

    @staticmethod
    def _char_to_idx(*x):
        """
        Return the integer index that corresponds to a given characteristic in D.
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
        P = args[1]
        if isinstance(P, JacobianMorphism_divisor_class_field):
            return self._point.from_divisor(self, P)
        elif isinstance(P, VarietyThetaStructurePoint):
            return self._point.from_algebraic(P, thc=self)
        return self._point(*args, **kwds)

    __call__ = point

    _point = AnalyticThetaPoint

    def __repr__(self):
        """
        Return a string representation of this point.
        """
        return f'({" : ".join(repr(f) for f in self._coords)})'

    def to_algebraic(self):  # Equivalent to `AnalyticToAlgebraicThetaNullPoint` in magma
        """
        Compute the algebraic theta null point corresponding to an analytic theta null point.

        INPUT:

        - ``self``- a theta null point given by analytic coordinates (see :class:`AnalyticThetaNullPoint`).

        OUTPUT:

        The corresponding theta null point in algebraic coordinates (see :class:`AbelianVariety_ThetaStructure`, :class:`KummerVariety`)
        
        .. todo:: Address FIXME.
        """

        if self._algebraic is not None:
            return self._algebraic
        n = self.level()
        g = self.dimension()
        ng = n ** g
        point = [0] * ng
        R = parent(self._coords[0])  # FIXME

        if n == 2:
            for b in range(ng):  # char(b) in Zmod(2)^g
                point[b] = sum(self._coords[a + 2 ** g * b] for a in range(ng))
            assert point[0] != 0  # See Equation (3.12) in [Coss]
            return KummerVariety(R, g, point)

        # if n == 4:
        D = Zmod(n) ** g
        twotorsion = Zmod(2) ** g
        if not D.has_coerce_map_from(twotorsion):
            from sage.structure.coerce_maps import CallableConvertMap
            s = n // 2

            def c(P, el):
                return P(s * el.change_ring(ZZ))

            c = CallableConvertMap(twotorsion, D, c)
            D.register_coercion(c)

        V = ZZ ** g
        idx = self._char_to_idx

        for idxb, b in enumerate(D):  # char(b) in Zmod(4)^g
            for a in twotorsion:
                ttb = twotorsion(b)
                ib = D((V(b) - V(ttb)) / 2)  # Probably very inefficient, look for an alternative
                sign = (-1) ** ZZ(a * ib)
                point[idxb] += self._coords[idx(a, ttb)] * sign

        self._algebraic = AbelianVariety_ThetaStructure(R, n, g, point)
        return self._algebraic

    def curve(self, phi=False):
        """
        Hyperelliptic curve corresponding to this analytic theta null point.
        """
        if self._curve is None:
            raise NotImplementedError('Curve not indicated upon creation.')
        return self._curve if not phi else [self._curve, self._phi]

    def _weierstrass_points(self):
        """
        x-coordinates of the Weierstrass points of the corresponding curve
        """
        if self._wp is not None:
            return self._wp
        C = self.curve()
        f, h = C.hyperelliptic_polynomials()
        if h != 0:
            f = f + h ** 2 / 4
        if f.degree() % 2 == 0:
            C2 = HyperellipticCurve(f)
            f, _ = C2.odd_degree_model().hyperelliptic_polynomials()
        F = f.splitting_field('z')
        a = f.roots(F, multiplicities=False)
        a.sort()
        self._wp = a if a[:2] == [0, 1] else [0, 1] + [(el - a[0]) / (a[0] - a[1]) for el in a[2:]]
        return self._wp

    def _root(self):
        """
        Chosen square root of the difference between the x-coordinates 
        of the first two Weierstrass points (a[0] - a[1]).
        """
        if self._rac is not None:
            return self._rac
        wp = self._weierstrass_points()
        if wp[:2] == [0, 1]:
            self._rac = 1
            return 1
        raise NotImplementedError('Square root of (a_1 - a_0) not indicated upon creation.')
