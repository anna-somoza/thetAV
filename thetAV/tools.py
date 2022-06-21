"""
Additional tools.

AUTHORS:

- Anna Somoza (2020-22): initial implementation

"""

# *****************************************************************************
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from sage.rings.all import ZZ, Integer, Zmod
from sage.structure.coerce_maps import CallableConvertMap
from sage.misc.constant_function import ConstantFunction

integer_types = (int, Integer)


def rangeS(n, S):
    for x in range(n):
        if x in S:
            continue
        yield x


def reduce_sym(x):
    r"""
    Returns the lexicographic minimum among x and -x for x an element in
    Zmod(n)\ :sup:`g`.
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el = D([6, 6, 6, 3])
        sage: from thetAV.tools import reduce_sym
        sage: reduce_sym(el)
        (4, 4, 4, 7)
        
    """
    return min(x, -x)


def reduce_twotorsion(x):
    r"""
    Returns elements y in Zmod(2n)\ :sup:`g`, t Zmod(2)\ :sup:`g` such that 
    x = y + t and y is the lexicographic minimum of the elements in the 
    class of x in Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual 
    inclusion of Zmod(2) into Zmod(2n).
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el = D([9, 2, 0, 8])
        sage: from thetAV.tools import reduce_twotorsion
        sage: reduce_twotorsion(el)
        ((4, 2, 0, 3), (1, 0, 0, 1))

    """
    r = list(x)
    D = x.parent()
    n = D.rank()
    T = Zmod(2) ** n
    t = [0] * n
    halflevels = [i.order() // 2 for i in D.gens()]
    for i in range(n):
        if r[i] >= halflevels[i]:
            r[i] = r[i] - halflevels[i]
            t[i] = 1
    return D(r), T(t)


def reduce_symtwotorsion(x):
    r"""
    Returns elements y in Zmod(2n)\ :sup:`g`, t Zmod(2)\ :sup:`g` such that 
    y is the lexicographic minimum among the elements in the classes of 
    x and -x in Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual 
    inclusion of Zmod(2) into Zmod(2n), and t is such that y + t is 
    either x or -x.
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el = D([8, 1, 5, 3])
        sage: from thetAV.tools import reduce_symtwotorsion
        sage: reduce_symtwotorsion(el)
        ((2, 4, 0, 2), (0, 1, 1, 1))
    
    """
    x1, tx1 = reduce_twotorsion(x)
    x2, tx2 = reduce_twotorsion(-x)
    return (x1, tx1) if x1 <= x2 else (x2, tx2)


def reduce_symcouple(x, y):
    r"""
    Returns the lexicographic minimum of the symmetrical reduction of two
    elements x, y in Zmod(n)\ :sup:`g`.
    
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el1 = D([4, 0, 5, 1]); el2 = D([9, 4, 6, 9])
        sage: from thetAV.tools import reduce_symcouple
        sage: reduce_symcouple(el1, el2)
        ((1, 6, 4, 1), (4, 0, 5, 1))
        
    """
    xred = reduce_sym(x)
    yred = reduce_sym(y)
    return (xred, yred) if xred < yred else (yred, xred)


def reduce_twotorsion_couple(x, y):
    r"""
    Given two elements x, y in Zmod(2n)\ :sup:`g`, returns elements r, s in
    Zmod(2n)\ :sup:`g`, t in Zmod(2)\ :sup:`g`, such that r is the lexicographic
    minimum among the elements in the classes of x and y in 
    Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual  inclusion of Zmod(2)
    into Zmod(2n), s satisfies r + s = x + y and t is such that r + t is
    either x or y.
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el1 = D([8, 1, 8, 0]); el2 = D([5, 8, 4, 5])
        sage: from thetAV.tools import reduce_twotorsion_couple
        sage: reduce_twotorsion_couple(el1, el2)
        ((0, 3, 4, 0), (3, 6, 8, 5), (1, 1, 0, 1))
        
    """
    xred, tx = reduce_twotorsion(x)
    yred, ty = reduce_twotorsion(y)
    # check that the inclusion of Zmod(2)^g in Zmod(2n)^g is taken into account already.
    D = xred.parent()
    T = tx.parent()
    if not D.has_coerce_map_from(T):
        from sage.structure.coerce_maps import CallableConvertMap
        n = D.gens()[0].order()
        s = n // 2

        def c(P, el):
            return P(s * el.change_ring(ZZ))

        c = CallableConvertMap(T, D, c)
        D.register_coercion(c)
    return (xred, y + tx, tx) if xred < yred else (yred, x + ty, ty)


def reduce_symtwotorsion_couple(x, y):
    r"""
    Given two elements x, y in Zmod(2n)\ :sup:`g`, returns elements r, s in
    Zmod(2n)\ :sup:`g`, t in Zmod(2)\ :sup:`g`, such that r is the lexicographic
    minimum among the elements in the classes of x, -x, y and -y in 
    Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual  inclusion of Zmod(2)
    into Zmod(2n), s satisfies r + s = ± x ± y and t is such that r + t is
    either x, -x, y or -y.
    
    .. todo:: Is s minimal in any sense among all the ones that satisfy 
              that condition?
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el1 = D([0, 7, 9, 1]); el2 = D([3, 5, 8, 8])
        sage: from thetAV.tools import reduce_symtwotorsion_couple
        sage: reduce_symtwotorsion_couple(el1, el2)
        ((0, 2, 4, 1), (3, 0, 3, 8), (0, 1, 1, 0))
        
    """
    xred, tx = reduce_symtwotorsion(x)
    yred, ty = reduce_symtwotorsion(y)
    # check that the inclusion of Zmod(2)^g in Zmod(2n)^g is taken into account already.
    D = xred.parent()
    T = tx.parent()
    if not D.has_coerce_map_from(T):
        from sage.structure.coerce_maps import CallableConvertMap
        n = D.gens()[0].order()
        s = n // 2

        def c(P, el):
            return P(s * el.change_ring(ZZ))

        c = CallableConvertMap(T, D, c)
        D.register_coercion(c)
    return (xred, reduce_sym(y + tx), tx) if xred < yred else (yred, reduce_sym(x + ty), ty)


def get_dual_quadruplet(x, y, u, v):
    r"""
    .. todo:: add minimal docstring. Twotorsion elements should be returned as elements in the twotorsion.
    """
    r = x + y + u + v
    z = r.parent()([ZZ(e) // 2 for e in list(r)])
    xbis = z - x
    ybis = z - y
    ubis = z - u
    vbis = z - v
    return xbis, ybis, ubis, vbis


def eval_car(chi, t):
    r"""
    .. todo:: add minimal docstring.
    """
    if chi.parent() != t.parent():
        r = list(t)
        D = t.parent()
        twotorsion = chi.parent()
        halflevels = [i.order() // 2 for i in D.gens()]
        n = D.rank()
        for i in range(n):
            r[i] = ZZ(r[i]) / halflevels[i]
        t = twotorsion(r)
    return ZZ(-1) ** (chi * t)


def evaluate_formal_points(w):
    r"""
    .. todo:: add minimal docstring.
    """
    B = w.parent()
    q = B.modulus()
    S = q.parent()
    u = S.gen()
    f = u * S(w.list()) * q.derivative()
    return f // q


def idx(c, n):
    """
    Return the integer index that corresponds to a given characteristic in ``D``.
    """
    return ZZ(list(c), n)


def create_conversions(n, g):
    Z = Zmod(n) ** g
    from_ZZ = CallableConvertMap(ZZ, Z, lambda U, idx: U(idx.digits(n, padto=g)))
    from_int = CallableConvertMap(int, Z, lambda U, idx: U(ZZ(idx).digits(n, padto=g)))
    from_int.domain = ConstantFunction(int)
    Z._unset_coercions_used()
    Z.register_conversion(from_ZZ)
    Z.register_conversion(from_int)
    return Z


def create_indexing(n, g, twotorsion=True):
    Z = create_conversions(n, g)
    if not twotorsion:
        return Z
    TT = create_conversions(2, g)
    if not Z.has_coerce_map_from(TT):
        s = n // 2
        c = CallableConvertMap(TT, Z, lambda U, tt: U([s * ZZ(i) for i in tt]))
        Z.register_coercion(c)
    return Z, TT
