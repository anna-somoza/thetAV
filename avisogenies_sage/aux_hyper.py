"""
Auxiliary functions to obtain different isomorphic models of hyperelliptic curves.


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

from sage.categories.homset import hom
from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
from sage.functions.other import sqrt
from sage.misc.misc_c import prod


def remove_h(phi):
    C = phi.codomain()
    f, h = C.hyperelliptic_polynomials()
    f1 = f + h ** 2 / 4
    C1 = HyperellipticCurve(f1)
    x0, x1, x2 = C.defining_polynomial().parent().gens()
    phi1 = hom(C, C1, [x0 / x2, x1 / x2 + h(x0 / x2) / 2, 1])
    phi1.normalize_coordinates()
    return phi1 * phi


def transformation(C, a, b, c, d, e, skip=None):
    f, _ = C.hyperelliptic_polynomials()
    g = C.genus()
    rts = f.roots()
    phi0 = lambda r: (a * r + b) / (c * r + d) if (c * r + d) != 0 else None
    X = f.parent().gen()
    f1 = prod(X - phi0(r) for r, m in rts if r != skip)
    C1 = HyperellipticCurve(f1)
    x0, x1, x2 = C.defining_polynomial().parent().gens()
    x = x0 / x2
    y = x1 / x2
    phi = hom(C, C1, [phi0(x), e * y / (c * x + d) ** (g + 1), 1])
    return phi


def rosenhain_model(phi):
    C = phi.codomain()
    f, h = C.hyperelliptic_polynomials()
    if h:
        raise TypeError(f'Expected a hyperelliptic curve with h={h}=0')
    g = C.genus()
    rts = f.roots()
    nroots = sum(m for el, m in rts)
    if not 2 * g + 1 <= nroots <= 2 * g + 2:
        raise ValueError(f'No Rosenhain model exists over field of definition: nroots={nroots}')
    rts.sort()
    r0 = rts[0][0]
    r1 = rts[1][0]
    if nroots == 2 * g + 1:
        if r0 == 0 and r1 == 1 and f.lc() == 1:
            return phi
        w0 = f.lc()
        a = 1 / (r1 - r0)
        b = -a * r0
        c = 0
        d = 1
        if not (a ** 5 / w0).is_square():
            raise ValueError('No Rosenhain model exists over field of definition')
        w = sqrt(a ** 5 / w0)
        phi1 = transformation(C, a, b, c, d, w)
        return phi1 * phi
    r5 = rts[-1][0]
    w0 = f.lc()
    c = 1
    d = - r5
    a = (r1 + d) / (r1 - r0)
    b = -a * r0
    sw = (a * d - b * c) ** 5 * c / prod((c * root + d) ** m for root, m in rts[:-1])
    if not (sw / w0).is_square():
        raise ValueError('No Rosenhain model exists over field of definition')
    w = sqrt(sw / w0)
    phi1 = transformation(C, a, b, c, d, w, r5)
    return phi1 * phi
