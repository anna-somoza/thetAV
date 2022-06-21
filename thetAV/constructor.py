"""
Constructor for abelian varieties with extra structure.

AUTHORS:

- Anna Somoza (2021-22): initial implementation

"""

# *****************************************************************************
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# *****************************************************************************
from functools import partial

from sage.all import ZZ
from sage.misc.functional import sqrt
from sage.modular.abvar.constructor import AbelianVariety as ModularAbelianVariety
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.schemes.hyperelliptic_curves.hyperelliptic_g2 import HyperellipticCurve_g2

from . import theta_null_point, analytic_theta_point, aux_hyper


def AbelianVariety(*data, **kwargs):
    """
    Create the abelian variety corresponding to the given defining data.

    INPUT:

    An integer, string, newform, modsym space, congruence subgroup or tuple of congruence subgroups (see :func:`~sage:sage.modular.abvar.constructor.AbelianVariety` in Sagemath) or a theta
    structure (see :class:`~thetAV.abelian_variety.AbelianVariety_ThetaStructure`).

    OUTPUT: a modular abelian variety with extra structure.
    
    EXAMPLES:
    
    Giving the data of the theta structure associated to an Abelian Variety we can create an instance of :class:`~thetAV.abelian_variety.AbelianVariety_ThetaStructure`::
    
        sage: from thetAV import AbelianVariety
        sage: AbelianVariety(GF(331), 4, 1, [328,213,75,1])
        Abelian variety of dimension 1 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
        
    If the level of the abelian variety is 2, it correctly returns an instance of :class:`~thetAV.abelian_variety.KummerVariety_ThetaStructure`::
    
        sage: from thetAV import AbelianVariety
        sage: AbelianVariety(GF(331), 2, 2, [328,213,75,1])
        Kummer variety of dimension 2 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
    
    But the function is also compatible with the functionality currently available in Sagemath::
    
        sage: AbelianVariety(Gamma0(37))
        Abelian variety J0(37) of dimension 2
        sage: AbelianVariety('37a')
        Newform abelian subvariety 37a of dimension 1 of J0(37)
        sage: AbelianVariety(Newform('37a'))
        Newform abelian subvariety 37a of dimension 1 of J0(37)
        sage: AbelianVariety(ModularSymbols(37).cuspidal_submodule())
        Abelian variety J0(37) of dimension 2
        sage: AbelianVariety((Gamma0(37), Gamma0(11)))
        Abelian variety J0(37) x J0(11) of dimension 3
        sage: AbelianVariety(37)
        Abelian variety J0(37) of dimension 2
        sage: AbelianVariety([1,2,3])
        Traceback (most recent call last):
        ...
        TypeError: X must be an integer, string, newform, modsym space, congruence subgroup or tuple of congruence subgroups

    TEST:
    
    The constructor should also pass the named parameters::
    
        sage: from thetAV import *
        sage: F.<z> = GF(83^2)
        sage: T = [68, z + 33, 46, z + 33, 2*z + 29, 77*z + 58, 81*z + 31, 38*z + 16, 8, 67*z + 53, 48, 67*z + 53, 2*z + 29, 38*z + 16, 81*z + 31, 77*z + 58]
        sage: A = AbelianVariety(F, 4, 2, T, check=True)

    """
    if len(data) > 1:
        if data[1] == 2:
            data = data[:1] + data[2:]
            return theta_null_point.KummerVariety(*data, **kwargs)
        return theta_null_point.AbelianVariety_ThetaStructure(*data, **kwargs)

    return ModularAbelianVariety(data[0])


def _with_theta_basis(label: str, *data, **kwargs):
    if label == 'Fn':
        return AbelianVariety(*data, **kwargs)
    if label in ['F(2,2)', 'F(2,2)^2']:
        #TODO: add checks for level
        A = analytic_theta_point.AnalyticThetaNullPoint(*data, **kwargs)
        return A.to_algebraic()
    raise ValueError(f'The basis {label} is either not implemented or unknown.')


setattr(AbelianVariety, 'with_theta_basis', _with_theta_basis)

def _from_curve(C, level=4):
    """
    Given a hyperelliptic curve of genus 2, returns the analytic
    theta null point of level 4 (default) or 2.

    This function is accessible via AbelianVariety.from_curve
    or KummerVariety.from_curve

    EXAMPLES ::

        sage: from thetAV import AbelianVariety
        sage: F = GF(83^2); Fx.<X> = PolynomialRing(F)
        sage: a = [0, 1, 3, 15, 20]
        sage: C = HyperellipticCurve(prod(X - al for al in a)); C
        Hyperelliptic Curve over Finite Field in z2 of size 83^2 defined by y^2 = x^5 + 44*x^4 + 28*x^3 + 23*x^2 + 70*x
        sage: th = AbelianVariety.from_curve(C); th.with_theta_basis('F(2,2)')
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
        phi = aux_hyper.remove_h(phi)
        f, _ = phi.codomain().hyperelliptic_polynomials()
    a = sum(([el] * m for el, m in f.roots()), [])
    if len(a) not in [5, 6]:
        raise ValueError('No Rosenhain model exists over field of definition')
    phi = aux_hyper.rosenhain_model(phi)
    f, _ = phi.codomain().hyperelliptic_polynomials()
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
        A = analytic_theta_point.AnalyticThetaNullPoint(F, 2, 2, th2, curve=C, phi=phi, wp=[0, 1, l, m, n], rac=F(1))
    else:
        if not all([el.is_square() for el in th2]):
            F, to_F = F.extension(2, map=True)
            th2 = [to_F(el) for el in th2]
        th = [sqrt(el) for el in th2]
        wp = [F(el) for el in [0, 1, l, m, n]]
        A = analytic_theta_point.AnalyticThetaNullPoint(F, 4, 2, th, curve=C, phi=phi, wp=wp, rac=F(1))
    return A.to_algebraic()


setattr(AbelianVariety, 'from_curve', _from_curve)
setattr(theta_null_point.KummerVariety, 'from_curve', partial(_from_curve, level=2))