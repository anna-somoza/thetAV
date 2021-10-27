# ****************************************************************************
#             Copyright (C) 2020 Anna Somoza <anna.somoza.henares@gmail.com>
#
#    Distributed under the terms of the GNU General Public License (GPL)
#    as published by the Free Software Foundation; either version 2 of
#    the License, or (at your option) any later version.
#                                    https://www.gnu.org/licenses/
# ****************************************************************************

"""
This file contains functions to compute morphisms between hyperelliptic curves and the
corresponding abelian varieties (their jacobians) with theta functions of level 2 and 4.

The first half is from [VanW]_ and the last sections are algorithms from [Coss]_.
Based on the Magma implementation by Romain Cosset.

/************************* LAYOUT OF THE FILE ******************************/
/***** (1) Half-integer characteristics and computations of sign with half-integer characteristics
/***** (3) Manipulations of elements of Ep
/***** (4) twisted theta
/**************************************************************************/
/***** (1) Analytic structures and change of theta structures
/***** (3) Auxiliary functions
/***** (4) Expression of Ep
/***** (5) Add two torsion
/***** (6) Mumford to Theta
/***** (7) Theta to Mumford
/**************************************************************************/

REFERENCES:

.. [VanW] P. Van Wamelen. Equations for the Jacobian of a hyperelliptic curve.
   Trans. Am. Math. Soc, 350(8), pp.3083-3106, 1998.

.. [Coss] R. Cosset. Applications des fonctions thêta à la cryptographie sur courbes hyperelliptiques.
   PhD thesis, Université Henri Poincaré – Nancy 1, 2011.

"""

from .abelian_variety import AbelianVariety
from collections import Counter, namedtuple
from itertools import product, combinations, chain
from .tools import TowerOfField, rangeS

from sage.misc.all import prod, flatten, is_odd
from sage.structure.element import parent
from sage.functions.other import ceil, floor, sqrt
from sage.modules.free_module_element import zero_vector

from sage.rings.all import PolynomialRing, ZZ, Zmod, Integer
integer_types = (int, Integer)

from sage.arith.misc import XGCD

##***** (1) Half-integer characteristics and computations of sign with half-integer characteristics *****//

def eta_prime(g, L, normalized=False):
    """
    Following a definition analogous to that in [VanW, page 3089]_, returns eta_prime as
    a vector in ZZ^g.

    INPUT:

    - ``g`` -- an Integer; the length of eta_prime.
    - ``L`` -- an Integer or a list of integers; if it is a list, it returns the sum of eta_prime
      for all elements in the list.
    - ``normalized`` (default: False) - a boolean; it returns the vector reduced mod 2ZZ^g,
      that is, with entries 0 or 1.

    .. NOTE::

        The indexes are shifted to start at 0 with respect to the reference

    EXAMPLES ::

        sage: from avisogenies_sage import eta_prime
        sage: eta_prime(4, 6)
        (0, 0, 0, 1)
        sage: x = eta_prime(4,6) + eta_prime(4, 7)
        sage: y = eta_prime(4, [6, 7]); y
        (0, 0, 0, 2)
        sage: x == y
        True
        sage: eta_prime(4, [6, 7], normalized=True)
        (0, 0, 0, 0)

    """
    try:
        i = L
        if i < 0 or i > 2*g + 1:
            raise ValueError(f'Expected i={i} to be between 0 and {2*g + 1}')
    except TypeError:
        if len(L) == 0:
            return zero_vector(ZZ,g)
        v = sum(eta_prime(g, i) for i in L)
        if normalized:
            return normalize_eta(v)
        return v
    else:
        v = zero_vector(ZZ,g)
        if i >= 2*g:
            return v
        ih = floor(i / 2)
        v[ih] = 1
        return v


def eta_second(g, L, normalized=False):
    """
    Following a definition analogous to that in [VanW, page 3089]_, returns eta_second as
    a vector in ZZ^g.

    INPUT:

    - ``g`` - an Integer. The length of eta_second.
    - ``L`` - an Integer or a list of integers. If it is a list, it returns the sum of eta_second
            for all elements in the list.
    - ``normalized`` (default: False) - a boolean. It returns the vector reduced mod 2ZZ^g,
            that is, with entries 0 or 1.

    .. NOTE::

        The indexes are shifted to start at 0 with respect to the reference

    EXAMPLES ::

        sage: from avisogenies_sage import eta_second
        sage: eta_second(4, 6)
        (1, 1, 1, 0)
        sage: x = eta_second(4,6) + eta_second(4, 7)
        sage: y = eta_second(4, [6, 7]); y
        (2, 2, 2, 1)
        sage: x == y
        True
        sage: eta_second(4, [6, 7], normalized=True)
        (0, 0, 0, 1)

    """
    try:
        i = L
        if i < 0 or i > 2*g + 1:
            raise ValueError(f'Expected i={i} to be between 0 and {2*g + 1}')
    except TypeError:
        if len(L) == 0:
            return zero_vector(ZZ,g)
        v = sum(eta_second(g, i) for i in L)
        if normalized:
            return normalize_eta(v)
        return v
    else:
        V = ZZ**g
        if i == 2*g+1:
            return V(0)
        ih = ceil(i / 2)
        v = V([1]*ih + [0]*(g-ih))
        return v


def eta(g, L, normalized=False, idx=False):
    """
    Following a definition analogous to that in [VanW, page 3089]_, returns eta as
    a vector in ZZ^(2*g).

    INPUT:

    - ``g`` -- an Integer. The half-length of eta.
    - ``L`` -- an Integer or a list of integers. If it is a list, it returns the sum of eta_second
            for all elements in the list.
    - ``normalized`` (default: False) -- a boolean. It returns the vector reduced mod 2ZZ^g,
      that is, with entries 0 or 1.
    - ``idx`` (default: False) -- a boolean. If both normalize and idx are True, then ``eta``
      computes the integer with base-2 representation given by eta.

    .. NOTE::

        The indexes are shifted to start at 0 with respect to the reference

    EXAMPLES ::

        sage: from avisogenies_sage import eta
        sage: eta(4, 6)
        (0, 0, 0, 1, 1, 1, 1, 0)
        sage: x = eta(4,6) + eta(4, 7)
        sage: y = eta(4, [6, 7]); y
        (0, 0, 0, 2, 2, 2, 2, 1)
        sage: x == y
        True
        sage: eta(4, [6, 7], normalized=True)
        (0, 0, 0, 0, 0, 0, 0, 1)

    If normalized=True and idx=True, returns the integer with base-2 representation given
    by the eta vector ::

        sage: eta(4, [6,7], normalized=True, idx=True)
        128

    """
    V = ZZ**(2*g)
    try:
        if L == 2*g + 1 or len(L) == 0:
            if idx:
                return 0
            return V(0)
    except TypeError:
        ep = eta_prime(g, L)
        es = eta_second(g, L)
        v = V(list(chain(ep, es)))
        if idx:
            return ZZ(list(v), 2)
        return v
    else:
        ep = sum((eta_prime(g, i) for i in L))
        es = sum((eta_second(g, i) for i in L))
        v = V(list(chain(ep, es)))
        if normalized:
            if idx:
                return ZZ([x%2 for x in v], 2)
            return normalize_eta(v)
        return v


def normalize_eta(v):
    """
    It returns the vector `v` reduced mod 2ZZ^g, that is, with entries 0 or 1.

    EXAMPLES ::

        sage: from avisogenies_sage import eta, eta_second, normalize_eta
        sage: x = eta(4, [0,1,2,3]); x
        (2, 2, 0, 0, 3, 1, 0, 0)
        sage: normalize_eta(x)
        (0, 0, 0, 0, 1, 1, 0, 0)
        sage: x = eta_second(3, [0,1,2,3]); x
        (3, 1, 0)
        sage: normalize_eta(x)
        (1, 1, 0)

    """
    V = v.parent()
    return V([x % 2 for x in v])

def sign_theta_normalized(*data):
    """
    Computes the sign difference between theta constant with characteristic `e` and the
    theta constant with characteristic `normalized_eta(e)`.

    See [VanW, Equation (8)]_ for more information on the quasiperiodicity of theta constants.

    It accepts both eta vectors and a tuple (g, L) that defines an acceptable input for `eta`.

    EXAMPLES ::

        sage: from avisogenies_sage import eta, sign_theta_normalized
        sage: x = eta(4, [0,1,3,4]); x
        (2, 1, 1, 0, 3, 2, 0, 0)
        sage: sign_theta_normalized(x)
        -1
        sage: sign_theta_normalized(4, [0,1,3,4])
        -1

    """
    if len(data) > 1:
        e = eta(*data)
        g = data[0]
    else:
        e = data[0]
        try:
            g = ZZ(len(e)/2)
        except TypeError:
            raise ValueError(f'Expected eta(={eta}) of even length')
    en = normalize_eta(e)
    return ZZ((-1)**(en[:g]*(e[g:] - en[g:])/2))

def e_star(e):
    """
    Computes e_star as defined in [VanW, page 3090].

    EXAMPLES ::

        sage: from avisogenies_sage import eta, e_star
        sage: x = eta(4, [0,1,3,4]); x
        (2, 1, 1, 0, 3, 2, 0, 0)
        sage: e_star(x)
        1

    """
    try:
        g = ZZ(len(e)/2)
    except TypeError:
        raise ValueError(f'Expected eta(={eta}) of even length')
    return ZZ(-1)**(e[:g]*e[g:])

def e_2(g, A1, A2):
    """
    Compute e_2(eta(A1),eta(A2)) as defined in [VanW, page 3090].

    EXAMPLES ::

        sage: from avisogenies_sage import e_2
        sage: e_2(5, [0,1], [5,6])
        1

    """
    eta1 = eta(g, A1)
    eta2 = eta(g, A2)
    return ZZ((-1)**ZZ(eta2[:g]*eta1[g:] - eta1[:g]*eta2[g:]))


##***** (3) Manipulations of elements of Ep *****//

class EpElement(namedtuple('EpElement', ['sign', 'power', 'numer', 'denom'], defaults=[1, 0, Counter(), Counter()])):
    """
    The element of E as defined in Definition 5.1.3 in [Coss]_, where the roots sqrt(a_i - a_j)
    are expressed in terms of theta constants and sqrt(a_1 - a_0).

    .. NOTE::

        The indexes are shifted to start at 0 with respect to the reference.

    EXAMPLES:

    In order to see the vector representation of the keys in `numer` and `denom` one can use the `str` or `print` methods ::

        sage: from avisogenies_sage import EpElement
        sage: from collections import Counter
        sage: x = EpElement(sign=-1, power=1, numer=Counter({662: 1, 694: 1, 573: 1}), denom=Counter({663: 1, 607: 1, 725: 1}))
        sage: print(x)
        sign=-1,
        power=1,
        numer={
            [0, 1, 1, 0, 1, 0, 0, 1, 0, 1]: 1,
            [0, 1, 1, 0, 1, 1, 0, 1, 0, 1]: 1,
            [1, 0, 1, 1, 1, 1, 0, 0, 0, 1]: 1
        },
        denom={
            [1, 0, 1, 0, 1, 0, 1, 1, 0, 1]: 1,
            [1, 1, 1, 0, 1, 0, 0, 1, 0, 1]: 1,
            [1, 1, 1, 1, 1, 0, 1, 0, 0, 1]: 1
        }

    """

    def clean_common(self):
        """
        Clean the common factors in the numerator and denominator of an element of Ep.

        EXAMPLES ::

            sage: from avisogenies_sage import EpElement
            sage: from collections import Counter
            sage: x = EpElement(numer=Counter([1,2,3]), denom=Counter([1,1,2,4])); x
            EpElement(sign=1, power=0, numer=Counter({1: 1, 2: 1, 3: 1}), denom=Counter({1: 2, 2: 1, 4: 1}))
            sage: x.clean_common()
            EpElement(sign=1, power=0, numer=Counter({3: 1}), denom=Counter({1: 1, 4: 1}))

        """
        self = self._replace(numer = self.numer - self.denom, denom = self.denom - self.numer)

        return self

    def __mul__(self, other):
        """
        Multiply two elements of Ep, that is, multiply their signs, add their powers and multiply
        the numerators and denominators.

        EXAMPLES ::

            sage: from avisogenies_sage import EpElement
            sage: from collections import Counter
            sage: x = EpElement(sign=-1, power=2, numer=Counter([3]), denom=Counter([4]))
            sage: y = EpElement(sign=-1, power=3, numer=Counter([3]), denom=Counter([4, 5]))
            sage: x*y
            EpElement(sign=1, power=5, numer=Counter({3: 2}), denom=Counter({4: 2, 5: 1}))

        """
        elem = EpElement(self.sign * other.sign, self.power + other.power, self.numer + other.numer, self.denom + other.denom)
        return elem.clean_common()

    def __str__(self):
        s = []
        s.append(f'sign={self.sign}')
        s.append(f'power={self.power}')
        n = 'numer={\n    '
        n += ',\n    '.join(sorted(f'{key.digits(2)}: {value}' for key,value in self.numer.items()))
        n += '\n}'
        s.append(n)
        d = 'denom={\n    '
        d += ',\n    '.join(sorted(f'{key.digits(2)}: {value}' for key,value in self.denom.items()))
        d += '\n}'
        s.append(d)
        return ',\n'.join(s)

    def __truediv__(self, other):
        """
        Divide two elements of Ep, that is, divide their signs, substract their powers and
        cross-multiply the numerators and denominators.

        EXAMPLES ::

            sage: from avisogenies_sage import EpElement
            sage: from collections import Counter
            sage: x = EpElement(sign=-1, power=2, numer=Counter([3]), denom=Counter([4]))
            sage: y = EpElement(sign=-1, power=3, numer=Counter([3]), denom=Counter([4, 5]))
            sage: x/y
            EpElement(sign=1, power=-1, numer=Counter({5: 1}), denom=Counter())

        """
        elem = EpElement(self.sign * other.sign, self.power - other.power, self.numer + other.denom, self.denom + other.numer)
        return elem.clean_common()

    def __pow__(self, b):
        """
        Compute the power of an element of Ep, that is, compute the power of the sign,
        the multiple of the power, and multiply the multiplicites of the elements in the numerator
        and denominator.

        EXAMPLES ::

            sage: from avisogenies_sage import EpElement
            sage: from collections import Counter
            sage: x = EpElement(sign=-1, power=2, numer=Counter([3]), denom=Counter([4]))
            sage: y = EpElement(sign=-1, power=3, numer=Counter([3]), denom=Counter([4, 5]))
            sage: x/y
            EpElement(sign=1, power=-1, numer=Counter({5: 1}), denom=Counter())

        """
        if b == 0:
            return EpElement()
        elif b < 0:
            denom = Counter({k : -b*v for k,v in self.numer.items() if b*v != 0})
            numer = Counter({k : -b*v for k,v in self.denom.items() if b*v != 0})
        else:
            numer = Counter({k : b*v for k,v in self.numer.items() if b*v != 0})
            denom = Counter({k : b*v for k,v in self.denom.items() if b*v != 0})
        elem = EpElement(self.sign**b, self.power*b, numer, denom)

        return elem

def bp_sqrt(g, i, j):
    """
    Return the numerator and the denominator of sqrt(a_i - a_j) given by Definition 2
    in [VanW, page 3093] as an element of Ep.

    EXAMPLES ::

        sage: from avisogenies_sage import bp_sqrt
        sage: bp_sqrt(5, 6, 3)
        EpElement(sign=-1, power=1, numer=Counter({662: 1, 694: 1, 573: 1}), denom=Counter({663: 1, 607: 1, 725: 1}))

    """
    if i == j:
        raise ValueError('The difference of indices must be nonzero.')

    if i == 2*g + 1 or j == 2*g + 1:
        return EpElement(sign=1, power=0, numer=Counter(), denom=Counter())

    if i == 0:
        if j == 1:
            return EpElement(sign=1, power=1, numer=Counter(), denom=Counter())

        if j < g + 2:
            V = range(1, g+2)
        else:
            V = set(range(1, g+1))
            V.add(j)

        U = {2*x for x in range(g+1)}
        W = U.symmetric_difference(V)

        idx = lambda x : ZZ([s%2 for s in x], 2)
        ej = eta(g, W ^ {2*g + 1, j})
        e01 = eta(g, W ^ {0,1})
        e1 = eta(g, W ^ {2*g + 1, 1})
        e0j = eta(g, W ^ {0,j})
        n = Counter([idx(elem) for elem in [ej, e01]])
        d = Counter([idx(elem) for elem in [e1, e0j]])
        s = prod(sign_theta_normalized(elem) for elem in [ej, e01, e1, e0j])
        return EpElement(sign=s, power=1, numer=n, denom=d)

    L = list(range(1, g + 2))
    if i in L:
        L.remove(i)
    else:
        L.pop()
    if j not in L:
        L.pop()
        L.append(j)
    L.append(0)

    U = {2*x for x in range(g+1)}
    W = U.symmetric_difference(L)

    a = bp_sqrt(g, 0, i)
    idx = lambda x : ZZ([s%2 for s in x], 2)
    e0i = eta(g, W ^ {0,i})
    ej = eta(g, W ^ {2*g + 1, j})
    e0 = eta(g, W ^ {2*g + 1, 0})
    eij = eta(g, W ^ {i,j})
    s = a.sign*prod(sign_theta_normalized(elem) for elem in [e0i, ej, e0, eij])
    n = a.numer + Counter([idx(elem) for elem in [e0i, ej]])
    d = a.denom + Counter([idx(elem) for elem in [e0, eij]])

    elem = EpElement(sign=s, power=a.power, numer=n, denom=d)

    return elem.clean_common()


##***** (4) twisted theta *****//

def constant_f(g, A, C):
    """
    Return the expression of f_A as an element of Ep, as defined by Definition 3 in [VanW, page 3095].

    INPUT:

    - `g` : an Integer, the dimension.
    - `A` : a set.
    - `C` : a choice of C as in [Coss]_ (see :func:`choice_of_C_Cosset` and :func:`choice_of_all_C_Cosset`).

    EXAMPLES ::

        sage: from avisogenies_sage import constant_f
        sage: g = 5; A = set([1, 2, 3]); C = set([5, 6, 7])
        sage: fA = constant_f(g, A, C); fA
        EpElement(sign=1, power=-4, numer=Counter({607: 4, 694: 2, 911: 2, 843: 2, 415: 2, 347: 2, 723: 2, 850: 2, 484: 1, 637: 1, 626: 1, 561: 1, 950: 1, 638: 1, 724: 1, 573: 1, 595: 1, 978: 1, 330: 1}), denom=Counter({699: 5, 606: 4, 725: 2, 910: 2, 414: 2, 826: 1, 661: 1, 980: 1, 594: 1, 662: 1, 942: 1, 446: 1, 567: 1, 918: 1, 674: 1, 178: 1, 722: 1, 571: 1, 418: 1}))
        sage: print(fA)
        sign=1,
        power=-4,
        numer={
            [0, 0, 1, 0, 0, 1, 1, 1, 1]: 1,
            [0, 0, 1, 0, 1, 0, 1, 1, 0, 1]: 1,
            [0, 1, 0, 0, 1, 0, 1, 0, 1, 1]: 2,
            [0, 1, 0, 0, 1, 0, 1, 1, 1, 1]: 1,
            [0, 1, 0, 0, 1, 1, 1, 0, 0, 1]: 1,
            [0, 1, 0, 1, 0, 0, 1, 0, 1]: 1,
            [0, 1, 1, 0, 1, 1, 0, 1, 0, 1]: 2,
            [0, 1, 1, 0, 1, 1, 0, 1, 1, 1]: 1,
            [0, 1, 1, 1, 1, 1, 1, 0, 0, 1]: 1,
            [1, 0, 0, 0, 1, 1, 0, 0, 0, 1]: 1,
            [1, 0, 1, 1, 1, 1, 0, 0, 0, 1]: 1,
            [1, 0, 1, 1, 1, 1, 1, 0, 0, 1]: 1,
            [1, 1, 0, 0, 1, 0, 1, 0, 0, 1]: 1,
            [1, 1, 0, 0, 1, 0, 1, 1, 0, 1]: 2,
            [1, 1, 0, 1, 0, 0, 1, 0, 1, 1]: 2,
            [1, 1, 0, 1, 1, 0, 1, 0, 1]: 2,
            [1, 1, 1, 1, 0, 0, 0, 1, 1, 1]: 2,
            [1, 1, 1, 1, 1, 0, 0, 1, 1]: 2,
            [1, 1, 1, 1, 1, 0, 1, 0, 0, 1]: 4
        },
        denom={
            [0, 0, 1, 0, 1, 0, 1, 1, 1, 1]: 1,
            [0, 1, 0, 0, 0, 1, 0, 1, 0, 1]: 1,
            [0, 1, 0, 0, 0, 1, 0, 1, 1]: 1,
            [0, 1, 0, 0, 1, 0, 1, 0, 0, 1]: 1,
            [0, 1, 0, 0, 1, 0, 1, 1, 0, 1]: 1,
            [0, 1, 0, 0, 1, 1, 0, 1]: 1,
            [0, 1, 0, 1, 1, 1, 0, 0, 1, 1]: 1,
            [0, 1, 1, 0, 1, 0, 0, 1, 0, 1]: 1,
            [0, 1, 1, 0, 1, 0, 0, 1, 1, 1]: 1,
            [0, 1, 1, 1, 0, 0, 0, 1, 1, 1]: 2,
            [0, 1, 1, 1, 0, 1, 0, 1, 1, 1]: 1,
            [0, 1, 1, 1, 1, 0, 0, 1, 1]: 2,
            [0, 1, 1, 1, 1, 0, 1, 0, 0, 1]: 4,
            [0, 1, 1, 1, 1, 1, 0, 1, 1]: 1,
            [1, 0, 1, 0, 1, 0, 0, 1, 0, 1]: 1,
            [1, 0, 1, 0, 1, 0, 1, 1, 0, 1]: 2,
            [1, 1, 0, 1, 1, 1, 0, 0, 0, 1]: 1,
            [1, 1, 0, 1, 1, 1, 0, 1, 0, 1]: 5,
            [1, 1, 1, 0, 1, 1, 0, 0, 0, 1]: 1
        }

    """
    f = {'power': 0}

    B = set(range(2*g + 1))
    U = {2*x for x in range(g+1)}

    # The two theta constants which appear in the definition
    idx = lambda x : ZZ([s%2 for s in x], 2)
    eC = eta(g, C)
    eUAC = eta(g, (U ^ A) ^ C)
    f['numer'] = Counter([idx(eC)])
    f['denom'] = Counter([idx(eUAC)])
    f['sign'] = prod(sign_theta_normalized(elem) for elem in [eC, eUAC])
    ff = EpElement(**f)

    #the four products of the definition
    # ff *= prod((bp_sqrt(g, k, i) for i, k in product(A & U, U - A)), EpElement())
    # ff *= prod((bp_sqrt(g, k, i) for i, k in product((B - A) & (B - U), A - U)), EpElement())
    # ff /= prod((bp_sqrt(g, k, i) for i, k in product((A ^ C) & (U ^ C), (U ^ C) - (A ^ C))), EpElement())
    # ff /= prod((bp_sqrt(g, k, i) for i, k in product((B - (A ^ C)) & (B - (U ^ C)), (A ^ C) - (U ^ C))), EpElement())

    # We compute a simplified version for speed
    prod_list = Counter([(i,k) for i, k in product(A & U, U - A)] + [(i,k) for i, k in product((B - A) & (B - U), A - U)])
    div_list = Counter([(i,k) for i, k in product((A ^ C) & (U ^ C), (U ^ C) - (A ^ C))] + [(i,k) for i, k in product((B - (A ^ C)) & (B - (U ^ C)), (A ^ C) - (U ^ C))])
    ff *= prod((bp_sqrt(g, k, i)**m for (i,k), m in (prod_list - div_list).items()), EpElement())
    ff /= prod((bp_sqrt(g, k, i)**m for (i,k), m in (div_list - prod_list).items()), EpElement())


    return ff.clean_common()

def choice_of_C_Cosset(g, A):
    """
    Make a choice for the constant C as in Definition 5.1.5 of [Coss]_.

    INPUT:

    - `g` : an Integer, the dimension.
    - `A` : a set.

    EXAMPLES ::

        sage: from avisogenies_sage import choice_of_C_Cosset
        sage: choice_of_C_Cosset(5, {0,1,2})
        {3, 4}

    """
    if len(A) > g + 1:
        raise ValueError(f'Expected set A(={A}) of cardinality at most {g+1}')
    if 2*g + 1 in A:
        raise ValueError(f'A should not contain the index for the point at infinity')

    U = {2*x for x in range(g+1)}

    if len(A) == g or len(A) == g+1: # |A|=g+1
        return set()

    n = floor((g + 1 - len(A))/2)

    Cp = set() # 2*g + 1 in Cp  if 2*g + 1  not in A DIFF shouldn't it be Cp = {2*g + 1} then?
    Cpp = set()
    for i in range(0, 2*g + 2):
        if i not in A | U and len(Cp) < n:
            Cp.add(i)
        elif i in U - A and len(Cpp) < n:
            Cpp.add(i)
        else:
            if len(Cp) == n and len(Cpp) == n:
                break

    return Cp | Cpp

def choice_of_all_C_Cosset(g):
    """
    Make a choice for all the constant C as in Definition 5.1.5 of [Coss]_.

    INPUT:

    - `g` : an Integer, the dimension.

    EXAMPLES ::

        sage: from avisogenies_sage import choice_of_all_C_Cosset
        sage: g = 5; C = choice_of_all_C_Cosset(g)
        sage: C[frozenset({1,3,4})]
        {0, 5}
        sage: B = frozenset(range(2*g + 1))
        sage: C[B.difference({1,3,4})]
        {0, 5}

    """
    C = {}
    B = frozenset(range(2*g + 1))

    for A in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(g + 1)):
        A = frozenset(A)
        C[A] = choice_of_C_Cosset(g, A)
        C[B - A] = C[A]

    return C

def sign_s_A(g, A, C):
    """
    Compute the sign of s_A as defined in Section 5.1.4 of [Coss]_.

    INPUT:

    - `g` : an Integer, the dimension.
    - `A` : a set.
    - `C` : a choice of all C as in [Coss]_ (see :func:`choice_of_all_C_Cosset`).

    EXAMPLES ::

        sage: from avisogenies_sage import choice_of_all_C_Cosset, sign_s_A
        sage: g = 5; C = choice_of_all_C_Cosset(g)
        sage: sign_s_A(g, [1, 2, 3], C)
        1

    """
    if len(A) == 0 or len(A) == 1:
        return 1

    zg = eta_second(g, range(2*g + 1))/2 #DIFF is this eta_g as defined in [Coss]?
    U = {2*x for x in range(g+1)}

    if len(A) >= 2*g:
        sA = (-1)**ZZ(eta_prime(g, C[frozenset()] & U)*zg)
        for l in range(2*g + 1):
            sA *= (-1)**ZZ(eta_prime(g,C[frozenset({l})] & U)*zg)
        return sA

    s = len(A)
    n = floor(s/2)
    if not isinstance(A, frozenset):
        A = frozenset(A)

    sA = (-1)**ZZ(eta_prime(g,C[A] & U)*zg)
    for l in A:
        sA *= (-1)**ZZ(eta_prime(g,C[frozenset({l})] & U)*zg)

    if is_odd(s):
        sA *= (-1)**floor((n+1)/2) #DIFF why not directly (-1)**floor((s+1)/4)??
    else:
        sA *= (-1)**ZZ(eta_prime(g,C[frozenset()] & U)*zg)
        sA *= (-1)**floor(n/2) #DIFF why not directly (-1)**floor((s+1)/4)??

    if s >= g:
        sA *= (-1)**ZZ(eta_prime(g,C[A])*zg) #DIFF why?

    return sA

#**************************************************************************/

##***** (1) Structures and change of theta structures*****//


#TODO: Add examples to all class functions
#TODO: Add _repr_ to the classes and modify the examples accordingly
#TODO: Field of definition
class ThetaPoint_Analytic:
    """
    Components:
    - level, // an integer
    - coord, // a ThetaStructure of level 2 and g = 2*g
    """
    def __init__(self, thc, v):  #Equivalent to "AnalyticThetaPoint" intrinsic method in magma
        l = thc._level
        if l != 2 and l != 4:
            raise NotImplementedError

        if v == 0 or v == (0,):
            v = thc._coord
        self._coord = v
        self._codomain = thc

    def abelian_variety(self):
        """
        Return the thetanullpoint associated to this theta point.
        """
        return self._codomain

    def __getitem__(self, n):
        """
        Return the n-th coordinate of this point.
        """
        return self._coord[n]

    def __iter__(self):
        """
        Return the coordinates of this point as a list.
        """
        return iter(self._coord)

    def __repr__(self):
        """
        Return a string representation of this point.
        """
        return f'({" : ".join(repr(f) for f in self._coord)})'

    def to_algebraic(self, A = None): # Corresponds to `AnalyticToAlgebraicThetaPoint` in magma
        """
        Compute the algebraic theta point corresponding to an analytic theta point.

        INPUT:

        - `self`: a theta null point given by analytic coordinates (see :class:`ThetaPoint_Analytic`).

        - `g`: the dimension of the ab. variety? #Maybe it should be a variable in self?

        OUTPUT:

        The corresponding theta point in algebraic coordinates (see :class:`AbelianVarietyPoint`)
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

class ThetaNullPoint_Analytic:
    """
    Class for analytic theta null points.

    For level 2, the basis used is F(2,2)^2.
    For level 4, the basis used is F(2,2).

    See Section 3.1.2 in [Coss]_ for the definition of the notation.
    """

    def __init__(self, l, v, g): #Equivalent to "AnalyticThetaNullPoint" intrinsic method in magma
        if l != 2 and l != 4:
            raise NotImplementedError
        self._level = l
        if len(v) != 2**(2*g):
            raise ValueError('v(={v}) does not define a valid analytic thetanullpoint')
        self._coord = v
        self._dimension = g
        self._numbering = Zmod(2)**(2*g)

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

    _point = ThetaPoint_Analytic

    def __repr__(self):
        """
        Return a string representation of this point.
        """
        return f'({" : ".join(repr(f) for f in self._coord)})'

    def to_algebraic(self): #Equivalent to `AnalyticToAlgebraicThetaNullPoint` in magma
        """
        Compute the algebraic theta null point corresponding to an analytic theta null point.

        INPUT:

        - `self`: a theta null point given by analytic coordinates (see :class:`ThetaNullPoint_Analytic`).

        OUTPUT:

        The corresponding theta null point in algebraic coordinates (see :class:`AbelianVariety`)
        """

        try:
            return self._algebraic
        except AttributeError:
            pass

        n = self._level
        g = self._dimension
        ng = n**g
        point = [0]*ng
        R = parent(self._coord[0]) #FIXME

        if n == 2:
            for b in range(ng): #char(b) in Zmod(2)^g
                point[b] = sum(self._coord[a + 2**g*b] for a in range(ng))
            assert point[0] != 0 #See Equation (3.12) in [Coss]
            return AbelianVariety(R, n, g, point)

        #if n == 4:
        D = Zmod(n)**g
        twotorsion = Zmod(2)**g
        V = ZZ**g
        idx = self._char_to_idx

        for idxb, b in enumerate(D): #char(b) in Zmod(4)^g
            for a in twotorsion:
                ttb = twotorsion(b)
                ib = D((V(b) - V(ttb))/2) #Probably very inefficient, look for an alternative
                sign = (-1)**ZZ(a*ib)
                point[idxb] += self._coord[idx(a, ttb)]*sign

        self._algebraic = AbelianVariety(R, n, g, point)
        return self._algebraic

def AlgebraicToAnalyticThetaNullPoint(thc): ##TODO: as method in AbelianVariety
    """
    Let thc be a theta null point given by algebraic coordinates (i.e. :class:`AbelianVariety`). Compute the
    corresponding theta null point (i.e. :class:`ThetaNullPoint_Analytic`) in analytic coordinates.
    """
    n = thc._level
    g = thc._dimension

    O = thc.theta_null_point()
    D = thc._D
    idx = thc._char_to_idx
    point = [0]*(4**g)

    if n == 2:
        for (idxa, a), (idxb, b) in product(enumerate(D), repeat=2):
            point[idxa + 2**g*idxb] = sum((-1)**ZZ(a*beta)*O[idx(b + beta)]*O[idxbeta] for idxbeta, beta in enumerate(D))/2**g

        return ThetaNullPoint_Analytic(n, point, g)

    if n == 4:
        twotorsion = thc._twotorsion #Zmod(2)^g
        for (idxa, a), (idxb, b) in product(enumerate(twotorsion), repeat=2):
            Db = D(list(b))
            point[idxa + 2**g*idxb] = sum((-1)**(a*beta)*O[idx(Db + beta)] for beta in twotorsion)/2**g

        return ThetaNullPoint_Analytic(n, point, g)

    raise NotImplementedError

def AlgebraicToAnalyticThetaPoint(th, thc=None): ##TODO: as method in AbelianVarietyPoint
    """
    Let th be a theta point given by algebraic coordinates (i.e. :class:`AbelianVarietyPoint`). Compute the
    corresponding theta null point in analytic coordinates (i.e. :class:`ThetaNull_Analytic`).
    """
    tnp = th.abelian_variety()
    O = tnp.theta_null_point()
    n = tnp._level
    g = tnp._dimension
    D = tnp._D
    point = [0]*(4**g)
    idx = tnp._char_to_idx

    if thc == None:
        thc = AlgebraicToAnalyticThetaNullPoint(tnp)

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

##***** (3) Auxiliary functions *****//

def IgusaTheorem(A, TH):
    """
    Apply Igusa theorems to the theta with caracteristic given in the list A
    The theta in the summation are taken from TH #FIXME: Add reference

    INPUT:

    - A - A list with 4 eta vectors.
    - TH - A list of 4 analytic theta points.

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: g = 2; A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
        sage: P = A([255 , 89 , 30 , 1])
        sage: thp = AlgebraicToAnalyticThetaPoint(P)
        sage: thc = thp._codomain; thO = thc(0)
        sage: IgusaTheorem([eta(g,{2*x for x in range(g+1)})]*4, [thp,thO,thO,thO])
        56

    """
    if len(A)!=4 or len(TH)!=4:
        raise ValueError
    D = TH[0].abelian_variety()._numbering #Zmod(2)**(2*g)
    g = TH[0].abelian_variety()._dimension
    V = ZZ**(2*g)

    a1, a2, a3, a4 = A
    N = [sum(A)/2, (a1 + a2 - a3 - a4)/2, (a1 - a2 + a3 - a4)/2, (a1 - a2 - a3 + a4)/2]
    p = 0
    idx = lambda x : ZZ(list(x), 2)

    for a in D:
        a = V(a)
        t = (-1)**ZZ(a1[:g]*a[g:])
        t *= prod(th[idx(normalize_eta(n + a))] for th, n in zip(TH, N))
        t *= prod(sign_theta_normalized(n + a) for n in N)
        p += t

    return p/2**g


##***** (4) Expression of Ep *****//

def constant_f2_level2(a, thc, A, C):
    """
    Compute the constant f_S^2 from the theta constant of level 2

    INPUT:

    - `a` - list of x-coordinates of the Weierstrass points.
    - `thc` - the theta null point associated to the jacobian of the curve.
    - `A` - a set
    - `C` - a choice of C as in [Coss]_ (see :func:`choice_of_C_Cosset` and :func:`choice_of_all_C_Cosset`).

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: g = 2; A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
        sage: thc = AlgebraicToAnalyticThetaNullPoint(A)
        sage: a = [0,1,4,6,7]
        sage: A = {3,4}; constant_f2_level2(a, thc, A, choice_of_C_Cosset(g, A))
        170

    """
    g = thc._dimension
    thO = thc(0)
    U = {2*x for x in range(g+1)}
    B = set(range(2*g + 1))

    # the two theta constants which appear in the definition
    f2 = thO[eta(g, C, normalized=True, idx=True)]/thO[eta(g, (U ^ A) ^ C, normalized=True, idx=True)]

    # the four product of the definitions
    f2 *= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product(A & U, U - A))
    f2 *= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product((B - A) & (B - U), A - U))
    f2 /= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product((A ^ C) & (U ^ C), (U ^ C) - (A ^ C)))
    f2 /= prod((-1)**(k < i)*(a[k] - a[i]) for i, k in product((B - (A ^ C)) & (B - (U ^ C)), (A ^ C) - (U ^ C)))

    return f2

def eltEp_to_eltE(a, thc, f, rac=None):
    """
    Let f be an element of Ep. Evaluate f.

    INPUT:

    - `a` - list of x-coordinates of the Weierstrass points.
    - `thc` - the theta null point associated to the jacobian of the curve.
    - `f` - an EpElement.
    - `rac` - a root of <a_1 - a_0>

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: g = 2; A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
        sage: thc = AlgebraicToAnalyticThetaNullPoint(A)
        sage: a = [0,1,4,6,7]
        sage: f = bp_sqrt(g, 4, 2)
        sage: eltEp_to_eltE(a, thc, f*f)
        249

    """
    level = thc._level
    thO = thc(0)

    if level == 2:
        try:
            ff = f.sign*(a[1] - a[0])**ZZ(f.power/2)
        except TypeError:
            raise ValueError('The power of sqrt(a_1 - a_0) in f is expected to be even.')

        try:
            ff *= prod(thO[elem]**ZZ(multi/2) for elem, multi in f.numer.items())
        except TypeError: #If one of the exponents is not integer
            raise ValueError('All multiplicities in the numerator of f are expected to be even.')

        try:
            ff /= prod(thO[elem]**ZZ(multi/2) for elem, multi in f.denom.items())
        except TypeError: #If one of the exponents is not integer
            raise ValueError('All multiplicities in the denominator of f are expected to be even.')

        return ff

    if level == 4:
        if rac == None:
            raise TypeError('Missing root of <a_2-a_1>.')
        ff = f.sign*rac**f.power
        ff *= prod(thO[elem]**multi for elem, multi in f.numer.items())
        ff /= prod(thO[elem]**multi for elem, multi in f.denom.items())
        return ff

    raise NotImplementedError('Only implemented for level 2 and 4.')


##***** (5) Add two torsion *****//

def AddTwoTorsion(th, eta):
    """
    Add the two torsion points corresponding to the caracteristic eta to the theta.

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: g = 2; A = AbelianVariety(GF(331), 2, 2, [328 , 213 , 75 , 1])
        sage: P = A([255 , 89 , 30 , 1])
        sage: thp = AlgebraicToAnalyticThetaPoint(P)
        sage: AddTwoTorsion(thp, eta(g, 2))._coord #FIXME change when _repr_ is done.
        [163, 328, 50, 185, 96, 217, 63, 183, 53, 307, 229, 76, 56, 118, 48, 199]

    """
    thc = th.abelian_variety()
    level = thc._level
    Ab = thc._numbering
    g = thc._dimension
    idx = thc._char_to_idx

    if level == 2:
        t = [(-1)**ZZ(eta[:g]*e[g:])*th[idx(e + eta)] for e in Ab]
        return thc(t)

    if level == 4:
        t = th._coord
        for idxe, e in enumerate(Ab):
            t[idxe] *= (-1)**ZZ(e[:g]*eta[g:] + eta[:g]*e[g:])
        return thc(t)

    raise NotImplementedError('Only implemented for level 2 and 4.')

##***** (6) Mumford to Theta *****//

def YS_fromMumford_Generic(g, a, S, points):
    """
    Compute Y_S(P) for P a preimage of a point D in Jac(C)\\Theta as defined in
    Equation (5.1) in [Coss]_..
    D can be writen as D = sum_1^g P_i - g P_infty.

    INPUT:

    - `a` - list of x-coordinates of the Weierstrass points.
    - `thc` - the theta null point associated to the jacobian of the curve.
    - `S` - an iterable.
    - `points` - a list of coordinates (x,y) (as tuples) of the points P_i in D. Assume
        that all P_i are distinct.

    EXAMPLES ::

        sage: from avisogenies_sage import YS_fromMumford_Generic
        sage: g = 2; a = [0,1,4,6,7]; S = [0,2,3]
        sage: points = [(2, 4), (3, 8)]
        sage: YS_fromMumford_Generic(g, a, S, points)
        92

    """
    if len(S) < 2 or len(S) > 2*g - 1:
        raise ValueError(f'Expected length of S={S} between 2 and {2*g - 1}')
    if len(points) != g or len(set(points)) != g:
        raise ValueError(f'Expected points={points} to be a list of {g} distinct elements')

    n = ceil((len(S)-1)/2)
    YS = 0
    for I in combinations(range(g), n):
        t = prod(points[i][1] for i in I)
        t *= prod(points[k][0] - a[l] for l, k in product(S, range(g)) if k not in I) #(x_k-a_l)
        t /= prod(points[i][0] - points[k][0] for i, k in product(I, range(g)) if k not in I)
        YS += t
    return YS

def YS_fromMumford_Delta(g, a, S, points): #DIFF: Not tested against Magma
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Assume that there exists i <=> j such that P_i = P_j but the other P_k are distinct
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of the Weierstrass points of the curve

    return the function Y_S

    See page 117 in [Coss]_.

    EXAMPLES ::

        sage: from avisogenies_sage import YS_fromMumford_Delta
        sage: F = GF(331); g = 2; a = [0, 1, 2, 3, 4]; S = [0,2,3]
        sage: points = [(F(5), F(38))]*2
        sage: YS_fromMumford_Delta(g, [F(el) for el in a], S, points)
        64

    .. NOTE:: 
        TODO: Test against Magma (minus the possible mistake)!
    """
    if len(S) < 2 or len(S) > 2*g - 1:
        raise ValueError(F'Expected length of S={S} between 2 and {2*g - 1}')
    if len(points) != g or len(set(points)) != g - 1:
        raise ValueError(F'Expected points={points} to be a list of {g} elements of which exactly two are equal')

    n = floor(len(S)/2)
    F = TowerOfField([parent(elem) for elem in flatten(points) + a])
    points = [(F(x), F(y)) for (x,y) in points]
    a = [F(elem) for elem in a]

    K = PolynomialRing(F, 2, 'xy')
    x, y = K.gens()

    for i, elemi in enumerate(points):
        for j, elemj in enumerate(points[i + 1:]):
            if elemi == elemj:
                points.pop(j)
                points.pop(i)
                points.append(elemi)
                points.append(elemj)
                #now the repeated elements are the last two
                break
        else:
            continue
        break

    Y = 0
    #Cases where I doesn't contain the indices of the repeated cases or it contains both (if possible): normal.
    for I in chain.from_iterable(combinations(range(g-2), r) for r in [n, n-2] if r >=0):
        if len(I) == n-2:
            I = I + (g-2, g-1)  #DIFF: In Magma implementation, in this case, missing y_{-1}^2 ? See Definition 5.1.26 on pg 116
        t = prod(points[i][1] for i in I)
        t *= prod(points[k][0] - a[l] for l, k in product(S, range(g)) if k not in I)
        t /= prod(points[i][0] - points[k][0] for i, k in product(I, range(g)) if k not in I)
        Y+=t

    #print(Y) ##TO BE REMOVED

    #Cases where I contains exactly one of the two.
    
    # With the formula in [Coss]_, t would be computed as follows

    # for I in combinations(range(g-2), n-1):
        # #First summand of p_I in [Coss, page 118].

        # P = prod(x - a[l] for l in range(2*g + 1) if l not in S)*prod(y - a[l] for l in S)
        # P -= prod(y - a[l] for l in range(2*g + 1) if l not in S)*prod(x - a[l] for l in S)
        # try:
            # P = K(P/(x-y))
        # except TypeError:
            # raise ValueError('P={P} should be divisible by {x - y}')
        # t = P(points[-1][0],points[-1][0])*prod((points[-1][0] - a[l])**2 for l in S)

        # t /= 2*points[-1][1]*prod(points[-1][0] - a[l] for l in S)

        # t *= prod(points[i][1] for i in I)
        # t /= prod(points[i][0] - points[-2][0] for i in I)

        # t *= prod(points[k][0] - a[l] for l, k in product(S, range(g-2)) if k not in I)
        # t /= prod(points[i][0] - points[k][0] for i, k in product(I + (-1,), range(g-2)) if k not in I)

        # Y += t

        # #Second summand of p_I in [Coss, page 118]

        # t = points[-2][1]
        # t *= prod(points[i][1] for i in I)
        # t *= prod(points[-1][0] - a[l] for l in S)

        # t *= prod(points[k][0]-a[l] for l, k in product(S, range(g-2)) if k not in I)
        # t /= prod(points[i][0]-points[k][0] for i, k in product(I, range(g-2) if k not in I)

        # t /= prod((points[i][0]-points[-2][0])**2 for i in I)
        # t /= prod((points[-1][0]-points[k][0])**2 for k in range(g-2) if k not in I)

        # P = prod(points[i][0] - x for i in I)*prod(y - points[k][0] for k in range(g-2) if k not in I)
        # P -= prod(points[i][0] - y for i in I)*prod(x - points[k][0] for k in range(g-2) if k not in I)
        # try:
          # P = K(P/(x-y))
        # except TypeError:
          # raise ValueError('P={P} should be divisible by {x - y}')

        # t *= P(points[1][0],points[1][0])

        # Y += t

    #We reorganize de computation for sake of efficiency

    P = prod(x - a[l] for l in range(2*g + 1) if l not in S)*prod(y - a[l] for l in S)
    P -= prod(y - a[l] for l in range(2*g + 1) if l not in S)*prod(x - a[l] for l in S)
    try:
        P = K(P/(x-y))
    except TypeError:
        raise ValueError('P={P} should be divisible by {x - y}')

    t01 = P(points[-1][0],points[-1][0])/(2*points[-1][1])*prod(points[-1][0] - a[l] for l in S)

    t02 = 1/prod(((points[i][0]-points[-1][0])**2 for i in range(g-2)), F(1))

    for I in combinations(range(g-2), n-1):

        t1 = t01 * prod(points[i][1] for i in I)
        t1 *= prod(points[k][0] - a[l] for l, k in product(S, range(g-1)) if k not in I)
        t1 /= prod(points[i][0] - points[k][0] for i, k in product(I + (-1,), range(g-2)) if k not in I)
        t1 /= prod(points[i][0] - points[-2][0] for i in I)

        t2 = t02 * prod(points[i][1] for i in I + (-2,))

        t2 *= prod(points[k][0] - a[l] for l, k in product(S, range(g-2)) if k not in I)
        t2 /= prod(points[i][0] - points[k][0] for i, k in product(I, range(g-2)) if k not in I)

        P = prod(points[i][0] - x for i in I)*prod(y - points[k][0] for k in range(g-2) if k not in I)
        P -= prod(points[i][0] - y for i in I)*prod(x - points[k][0] for k in range(g-2) if k not in I)
        try:
            P = K(P/(x-y))
        except TypeError:
            raise ValueError('P={P} should be divisible by {x - y}')
        t2 *= P(points[-1][0],points[-1][0])

        Y += t1 + t2

    return Y

def prodYp_fromMumford_with2torsion(g, a, S, points, V, C):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let S = [S1, S2, S3, S4] with S1 ^ S2 ^ S3 ^ S4 == {}
    Let C be the choice of sets in the definition of the f_A

    Assume that all P_i are distinct.

    Compute the function
    prod Y_Si' / prod a_l
    where the second product is over l in V compted twice iff it appears in all Si

    EXAMPLES ::

        sage: from avisogenies_sage import choice_of_all_C_Cosset, prodYp_fromMumford_with2torsion
        sage: F = GF(331); g = 2; a = list(map(F, [0, 1, 2, 3, 4]))
        sage: S = [{0,2,3},{0},{2,4}, {3,4}]; V = {1}
        sage: points = [(F(1), F(0)), (F(8), F(10))]
        sage: C = choice_of_all_C_Cosset(g)
        sage: prodYp_fromMumford_with2torsion(g, a, S, points, V, C)
        187

    """

    if len(V) < 1 or len(V) > g:
        raise ValueError(F'Expected length of V={V} between 1 and {g}')
    if len(points) != g:
        raise ValueError(F'Expected length of points={points} to be {g}')

    for s in S:
        if len(s) < 2*len(V & s):
            raise ValueError(F'Error?? FIXME')

    if S[0] ^ S[1] ^ S[2] ^ S[3] != set():
        raise ValueError(F'Error??? FIXME')

    F = TowerOfField([parent(elem) for elem in flatten(points) + a])
    points = [(F(x), F(y)) for (x,y) in points]
    a = [F(elem) for elem in a]
    K = PolynomialRing(F, 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)
    if any(u(a[l]) != 0 for l in V):
        raise ValueError('Indices in V should vanish u??') #FIXME

    # Let R be a subset {1..g} which correspond to the index i such that P_i is the
    # ramification point a_l with l in V
    R = [points.index((a[l],0)) for l in V]
    ind_VmS = [{idx for idx, l in zip(R, V) if l in s} for s in S]

    n = [floor(len(s)/2) for s in S]
    zg = eta_second(g, range(2*g + 1))/2
    W = V.intersection(*S)

    Y = 0
    for Ip in product(*[combinations(rangeS(g, R), ni - len(V & si)) for ni, si in zip(n, S)]):
        Ip1, Ip2, Ip3, Ip4 = Ip
        I = [ s | set(ip) for s, ip in zip(ind_VmS, Ip)]
        t = prod(points[i][1]  for Ij in I for i in Ij.difference(R))

        for s, i in zip(S, I):
            if len(s) >=2:
                t *= prod(points[k][0] - a[l] for l, k in product(s, rangeS(g,i)))
                t /= prod(points[j][0] - points[k][0] for j, k in product(i, range(g)) if k not in i)

        t /= prod(points[k][0] - a[l] for l, k in product(V, range(g)) if k not in R)
        t /= prod(points[k][0] - a[l] for l, k in product(W, range(g)) if k not in R)

        Y += t

    Y *= (-1)**(len(W) * len(V - W))
    Y *= prod(a[l] - a[m] for l, m in product(V, range(2*g + 1)) if m not in V)
    Y *= prod(a[l] - a[m] for l, m in product(W, range(2*g + 1)) if m not in V)

    #The sign
    for s in S:
        if len(s) == 1:
            Y *= (-1)**g*u(next(iter(s)))
        elif len(s) >= 2 and len(s) <= 2*g - 1:
            Y *= sign_s_A(g, s, C)
        elif len(s) == 2*g:
            Y *= sign_s_A(g, range(2*g+1), C)
            Y *= (-1)**floor(g/2)
            Y *= (-1)**ZZ(eta_prime(g, C[s])*zg)
        elif len(s) ==  2*g + 1:
            Y *= sign_s_A(g, range(2*g +1), C)
            Y *= (-1)**floor((g+1)/2)
            Y *= (-1)**ZZ(eta_prime(g,C[frozenset()])*zg)
        else:
            raise ValueError(F'Expected length of S={s} between 1 and {2*g+1}')

    return Y

def Y_fromMumford_with2torsion(g,a,S,points,V):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve

    Assume that all P_i are distinct.
    Assume that the first P_i are [a[l],0] with l in V
    Assume that V is a subset of S

    Compute the function Y_S^2 / prod a_l    where the product is over l in V

    EXAMPLES ::

        sage: from avisogenies_sage import Y_fromMumford_with2torsion
        sage: F = GF(331); g = 2; a = list(map(F, [0, 1, 2, 3, 4]))
        sage: S = {0,2,3,4}; V = {0,2}
        sage: points = [(F(0), F(0)), (F(2), F(0))]
        sage: Y_fromMumford_with2torsion(g,a,S,points,V)
        307

    TESTS::

        sage: from avisogenies_sage import Y_fromMumford_with2torsion
        sage: F = GF(331); g = 2; a = list(map(F, [0, 1, 2, 3, 4]))
        sage: S = {0,2,3,4}; V = {0}
        sage: points = [(F(0), F(0)), (F(8), F(10))]
        sage: Y_fromMumford_with2torsion(g,a,S,points,V)
        300

    """
    if not V < S or len(V) == 0:
        raise ValueError(F'V={V} should be a non-empty subset of S={S}')
    if len(points) != g:
        raise ValueError(F'Expected length of points={points} to be {g}')
    if len(S) < 2*len(V):
        raise ValueError(F'Error?? FIXME')

    #s = len(S)
    v = len(V)
    n = floor(len(S)/2)

    aV = [a[i] for i in V]
    if any(points[l][0] not in aV for l in range(v)):
        raise ValueError(F'Expected the first {v} points to be in {aV}')

    if v == n:
        Y = prod(a[l] - a[k] for l, k in product(V, range(2*g + 1)) if k not in V)
        Y /= prod(points[k][1] - a[l] for l, k in product(V, range(v, g)))
        Y *= prod((points[k][1] - a[l])**2 for l, k in product(S - V, range(v, g)))
        return Y

    Y = 0
    for I, J in product(combinations(range(v,g), n-v), repeat=2):
        t = prod(points[i][1] for i in I + J)
        for elem in [I, J]:
            t *= prod(points[k][0] - a[l] for l, k in product(S - V, range(v,g)) if k not in elem)
            t /= prod(points[i][0] - points[k][0] for i, k in product(elem, range(v,g)) if k not in elem)
        Y+=t

    Y *= prod(a[l] - a[k] for l, k in product(V, range(2*g + 1)) if k not in V)
    Y /= prod(points[k][0] - a[l] for l, k in product(V, range(v, g)))

    return Y

#TODO: Test against Magma in the case that uses YS_fromMumford_Delta
def MumfordToTheta_2_Generic(a, thc2, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates (x,y) (as tuples) of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let thc2 be the theta constant of level 2

    Return the theta functions of level 2 associated to points

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: F = GF(331); g = 2; n = 2
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: points = [(F(7), F(62)), (F(8), F(10))]
        sage: A = AbelianVariety(F, n, g, [328 , 213 , 75 , 1], check=True)
        sage: thc = AlgebraicToAnalyticThetaNullPoint(A)
        sage: MumfordToTheta_2_Generic(a, thc, points)._coord #FIXME change when _repr_ is done
        [92, 265, 295, 308, 319, 261, 303, 111, 89, 193, 275, 12, 262, 214, 46, 70]

    """
    if thc2._level != 2:
        raise ValueError(F'Expected level-2 theta structure.')

    g = thc2._dimension
    if len(points) != g:
        raise ValueError(F'Expected degree-{g} divisor')

    K = PolynomialRing(parent(points[0][0]), 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)

    if any(u(elem) == 0 for elem in a):
        raise ValueError(F'Expected generic divisor')

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result
    U = {2*x for x in range(g+1)}

    idx = thc2._char_to_idx
    th2 = [0]*(2**(2*g))
    e = eta(g, U, normalized=True)
    th2[idx(e)] = 1/constant_f2_level2(a, thc2, set(), C[frozenset()])

    for l in range(2*g + 1):
        ee = normalize_eta(e + eta(g, l))
        i = idx(ee)
        th2[i] = (-1)**g*u(a[l])
        th2[i] /= constant_f2_level2(a, thc2, {l}, C[frozenset({l})])

    lpoints = len(set(points))
    for S in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(2, g+1)):
        if lpoints == g:
            YS = YS_fromMumford_Generic(g, a, S, points)
        elif lpoints == g - 1:
            YS = YS_fromMumford_Delta(g, a, S, points)
        else:
            raise NotImplementedError('The case of non generic delta divisor is not implemented')
        ee = normalize_eta(e + eta(g, S))
        i = idx(ee)
        th2[i] = YS**2*(-1)**(g*len(S))
        th2[i] /= prod(u(a[l]) for l in S)
        th2[i] /= constant_f2_level2(a, thc2, set(S), C[frozenset(S)])

    return thc2(th2)

#TODO: Test against Magma, add examples
def MumfordToTheta_4_Generic(a, rac, thc, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^g P_i - g P_infty
    Let points be the list of coordinates [x,y] of P_i
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let thc be the theta constant of level 4 associated to the curve C

    Assume that all P_i are distinct.

    Return the theta functions of level 4 associated to points.
    """
    if thc._level != 4:
        raise ValueError(F'Expected level-4 theta structure.')

    g = thc._dimension
    if len(points) != g:
        raise ValueError(F'Expected degree-{g} divisor')

    K = PolynomialRing(parent(points[0][0]), 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)
    thO = thc(0)

    if any(u(elem) == 0 for elem in a):
        raise ValueError(F'Expected generic divisor')

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result
    U = {2*x for x in range(g+1)}
    zg = eta_second(g, range(2*g + 1))/2

    idx = thc._char_to_idx
    th  = [0]*2**(2*g)

    done = set()
    for S1 in chain.from_iterable(combinations(range(2*g + 1), l) for l in [g, g+1]):
        if eta_second(g, U.symmetric_difference(S1), normalized=True) != 0:
            continue
        for S2 in chain.from_iterable(combinations(range(2*g + 1), l) for l in [g, g+1]):
            if eta_prime(g, U.symmetric_difference(S2), normalized=True) != 0:
                continue

            ee = eta(g, U.symmetric_difference(S1)) + eta(g, U.symmetric_difference(S2))
            e = normalize_eta(ee)
            i = idx(e)
            if i in done:
                continue
            done.add(i)

            # we use the dupplication formula. t will be the general term
            for S in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(g+1)):
                S = frozenset(S)
                B = [S.symmetric_difference(S1).symmetric_difference(S2),
                     (S ^ U).symmetric_difference(S1), (S ^ U).symmetric_difference(S2), S]

                # we divide by f_Bi
                t = 1/prod(eltEp_to_eltE(a, thc, constant_f(g, Bi, C[Bi]), rac) for Bi in B)

                # we multiply by Y_Bi'
                for Bi in B:
                    if len(Bi) == 1:
                        al = a[next(iter(Bi))]
                        t *= (-1)**g*u(al)
                    elif len(Bi) >= 2 and len(Bi) <= 2*g-1:
                        t *= YS_fromMumford_Generic(g, a, Bi, points)
                        t *= sign_s_A(g, Bi, C)
                    elif len(Bi) == 2*g:
                        t *= prod(point[1] for point in points)
                        t *= sign_s_A(g, range(2*g + 1), C)
                        t *= (-1)**floor(g/2)
                        t *= (-1)**ZZ(eta_prime(g, C[Bi])*zg)
                    elif len(Bi) == 2*g+1:
                        t *= prod(point[1] for point in points)
                        t *= sign_s_A(g, range(2*g + 1), C)
                        t *= (-1)**floor((g+1)/2)
                        t *= (-1)**ZZ(eta_prime(g,C[frozenset()])*zg)

                # we divide by the u(a_l)
                for l in range(2*g + 1):
                    nb = sum(l in Bi for Bi in B)
                    try:
                        t /= ((-1)**g*u(a[l]))**(ZZ(nb/2))
                    except TypeError:
                        raise ValueError('Expected even value.') #FIXME
                # now t is theta[UoB1] * theta[UoB2] * theta[UoB3] * theta[UoB4] /t_empty(z)^4

                # the sign in the theta (we have changed the caracteristic)
                for Bi in B[:-1]:
                    t*=(-1)**ZZ(eta_prime(g, U ^ Bi)*(eta_second(g, U ^ S1) +
                        eta_second(g, U ^ S2) + eta_second(g, U ^ S) - eta_second(g, U ^ Bi))/2)

                # the sign in the dupplication formulae
                t *= (-1)**ZZ(ee[:g]*eta_second(g, U ^ S))

                th[i] += t/2**g

            # scale the theta. i.e. constants used in doubling
            for elem in [S1, S2, U]:
                eelem = eta(g, U.symmetric_difference(elem))
                th[i] *= sign_theta_normalized(eelem)/thO[idx(normalize_eta(eelem))]

            # sign when we have normalized the caracteristic
            th[i] *= sign_theta_normalized(ee)

    return thc(th)

def MumfordToLevel2ThetaPoint(a, thc2, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^d P_i - g P_infty
    Let points be the list of coordinates [x,y] of P_i
    Let a be the x-coordinates of the Weierstrass points of the curve
    Let thc2 be the theta constant of level 2

    Assume that all P_i are distinct if the divisor is either theta or has a
    ramification point in its support.

    Return the theta functions of level 2 associated to points

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: F = GF(331); g = 2; n = 2
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: points = [(F(7), F(62)), (F(8), F(10))]
        sage: A = AbelianVariety(F, n, g, [328 , 213 , 75 , 1], check=True)
        sage: thc = AlgebraicToAnalyticThetaNullPoint(A)
        sage: MumfordToLevel2ThetaPoint(a, thc, points)._coord #FIXME change when _repr_ is done
        [92, 265, 295, 308, 319, 261, 303, 111, 89, 193, 275, 12, 262, 214, 46, 70]


        sage: from avisogenies_sage import *
        sage: F = GF(331); g = 2; n = 2
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: points = [(F(7), F(62))]
        sage: A = AbelianVariety(F, n, g, [328 , 213 , 75 , 1], check=True)
        sage: thc = AlgebraicToAnalyticThetaNullPoint(A)
        sage: MumfordToLevel2ThetaPoint(a, thc, points)._coord #FIXME change when _repr_ is done, Magma output
        [288, 101, 184, 91, 289, 74, 111, 10, 106, 54, 12, 0, 292, 48, 113, 243]

    """
    if thc2._level != 2:
        raise ValueError(F'Expected level-2 theta structure.')

    g = thc2._dimension

    if len(points) == 0:
        return thc2(0)

    K = PolynomialRing(parent(points[0][0]), 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)

    up = u
    points_p = list(points)

    V1 = {l for l, al in enumerate(a) if up(al) == 0}

    if len(points) == g and len(V1) == 0:
        return MumfordToTheta_2_Generic(a, thc2, points)

    V2 = set()
    for l, al in enumerate(a):
        if l not in V1:
            V2.add(l)
            up *= (x - al)
            points_p.append((al, 0))
            if up.degree() == g:
                break

    V = V1 | V2

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result
    U = {2*x for x in range(g+1)}
    B = frozenset(range(2*g + 1))

    th2p = [0]*2**(2*g)

    i = eta(g, U, normalized=True, idx=True)
    th2p[i] = 1 / constant_f2_level2(a, thc2, set(), C[frozenset()])

    for l in range(2*g + 1):
        ii = eta(g, U ^ {l}, normalized=True, idx=True)
        th2p[ii] = (-1)**g*up(a[l])
        th2p[ii] /= constant_f2_level2(a, thc2, {l}, C[frozenset([l])])

    for S in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(2, g+1)):
        S = frozenset(S)
        if V & S == set():
            YS = YS_fromMumford_Generic(g, a, S, points_p)
            ii = eta(g, U ^ S, normalized=True, idx=True)
            th2p[ii] = YS**2*(-1)**(g*len(S))
            th2p[ii] /= prod(up(a[l]) for l in S)
            th2p[ii] /= constant_f2_level2(a, thc2, S, C[S])
        elif V < S:
            Sp = B - S
            YS = YS_fromMumford_Generic(g, a, Sp, points_p)
            ii = eta(g, U ^ Sp, normalized=True, idx=True)
            th2p[ii] = YS**2*(-1)**(g*len(Sp))
            th2p[ii] /= prod(up(a[l]) for l in Sp)
            th2p[ii] /= constant_f2_level2(a, thc2, Sp, C[Sp])
        elif len(S) < 2*len(V & S): #TODO: Not tested
            ii = eta(g,U ^ S, normalized=True, idx=True)
            th2p[ii] = 0
        else: #TODO: Not tested
            deb = [(a[l],0) for l in V & S]
            fin = [points_p[i] for i in range(g) if points_p[i] not in deb]
            YS_sq = Y_fromMumford_with2torsion(g, a, S, deb + fin, V & S)
            ii = eta(g, U ^ S, normalized=True, idx=True)
            th2p[ii] = YS_sq*(-1)**(g*len(S - V))
            th2p[ii] /= prod(up(a[l]) for l in S - V)
            th2p[ii] /= constant_f2_level2(a, thc2, S, C[S])

    th2 = thc2(th2p)
    for l in V2:
        th2 = AddTwoTorsion(th2, eta(g,l))

    return th2

def MumfordToLevel4ThetaPoint(a, rac, thc, points):
    """
    Let D be a point in Jac(C)\\Theta. D can be writen as
    D = sum_1^d P_i - g P_infty
    Let points be the list of coordinates [x,y] of P_i
    Let a be the x-coordinates of the Weierstrass points of the curve
    Let thc be the theta constant of level 4

    Assume that all P_i are distinct if the divisor is either theta or has a
    ramification point in its support.

    Return the theta functions of level 4 associated to points

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: F = GF(83^2); z, = F.gens(); Fx.<X> = PolynomialRing(F)
        sage: g = 2; a = [F(0), 1, 3, 15, 20]; rac = sqrt(a[1] - a[0])
        sage: thc = [1,  37,  56, 57, 34*z + 43, 0, 50*z + 73, 0, 30, 2*z + 82, 0, 0, 16*z + 37, 0, 0, 61*z + 21]
        sage: thc = ThetaNullPoint_Analytic(4, [F(elem) for elem in thc], g)
        sage: u = (X-43)*(X-10); v = z^954*X + z^2518
        sage: points = sum(([(x, v(x))]*mult for x, mult in u.roots(u.splitting_field('t'))), [])
        sage: th = MumfordToLevel4ThetaPoint(a, rac, thc, points); th
        (78*z2 + 13 : 77*z2 + 26 : 43*z2 + 3 : 54*z2 + 67 : 77*z2 + 61 : 35*z2 + 2 : 31*z2 + 8 :
        19*z2 + 38 : 25*z2 + 9 : z2 + 65 : 17*z2 + 75 : 18*z2 + 38 : 50*z2 + 17 : 41*z2 + 6 : 18*z2 + 48 : 39*z2 + 73)
    """
    if thc._level != 4:
        raise ValueError(F'Expected level-4 theta structure.')

    g = thc._dimension
    thO = thc(0)

    if len(points) == 0:
        return thO

    F = TowerOfField([parent(elem) for elem in flatten(points) + a])
    points = [(F(x), F(y)) for (x,y) in points]
    a = [F(elem) for elem in a]

    K = PolynomialRing(F, 'x')
    x = K.gen()
    u = prod(x - point[0] for point in points)

    up = u
    points_p = list(points)

    V1 = {l for l, al in enumerate(a) if up(al) == 0}

    V2 = set()
    for l, al in enumerate(a):
        if l not in V1:
            if up.degree() == g:
                break
            V2.add(l)
            up *= (x - al)
            points_p.append([al, 0])

    V = V1 | V2

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result
    U = {2*x for x in range(g+1)}
    zg = eta_second(g, range(2*g +1))/2

    thp =  [0]*2**(2*g)

    idx = thc._char_to_idx
    done = set()
    for S1 in chain.from_iterable(combinations(range(2*g + 1), l) for l in [g, g+1]):
        if eta_second(g, U.symmetric_difference(S1), normalized=True) != 0:
            continue
        for S2 in chain.from_iterable(combinations(range(2*g + 1), l) for l in [g, g+1]):
            if eta_prime(g, U.symmetric_difference(S2), normalized=True) != 0:
                continue

            ee = eta(g, U.symmetric_difference(S1)) + eta(g, U.symmetric_difference(S2))
            e = normalize_eta(ee)
            i = idx(e)
            if i in done:
                continue
            done.add(i)

            # we use the dupplication formula. t will be the general term
            for S in chain.from_iterable(combinations(range(2*g + 1), r) for r in range(g+1)):
                S = frozenset(S)
                B = [S.symmetric_difference(S1).symmetric_difference(S2),
                     (S ^ U).symmetric_difference(S1), (S ^ U).symmetric_difference(S2), S]

                if any(2*len(V & Bi) > len(Bi) for Bi in B):
                    continue

                # we divide by f_Bi
                t = 1 / prod(eltEp_to_eltE(a, thc, constant_f(g,Bi,C[Bi]), rac) for Bi in B)

                W = V & frozenset.union(*B[:-1]) #TODO: Why not B[4]?

                if len(W) != 0:
                    # we multiply by Y_Bi'
                    t *= prodYp_fromMumford_with2torsion(g, a, B, points_p, W, C)

                    # we divide by the up(a_l)
                    for l in rangeS(2*g + 1, W):
                        nb = sum(l in Bi for Bi in B)
                        try:
                            t /= ((-1)**g*up(a[l]))**ZZ(nb/2)
                        except TypeError:
                            raise ValueError('Expected even value') #FIXME

                else:
                    # we multiply by Y_Bi'
                    for Bi in B:
                        if len(Bi) == 1:
                            l = next(iter(Bi))
                            t *= (-1)**g*up(F(a[l]))
                        elif len(Bi) >= 2 and len(Bi) <= 2*g-1:
                            if len(set(points_p)) == len(points_p):
                                t *= YS_fromMumford_Generic(g, a, Bi, points_p)
                            elif len(set(points_p)) == len(points_p)-1:
                                t *= YS_fromMumford_Delta(g, a, Bi, points_p)
                            else:
                                raise NotImplementedError('The case of non generic delta divisor is not implemented')
                            t *= sign_s_A(g, Bi, C)
                        elif len(Bi) == 2*g:
                            t *= prod(point[1] for point in points_p)
                            t *= sign_s_A(g, range(2*g + 1), C)
                            t *= (-1)**floor(g/2)
                            t *= (-1)**ZZ(eta_prime(g,C[Bi])*zg)
                        elif len(Bi) == 2*g + 1:
                            t *= prod(point[1] for point in points_p)
                            t *= sign_s_A(g, range(2*g + 1), C)
                            t *= (-1)**floor((g+1)/2)
                            t *= (-1)**ZZ(eta_prime(g,C[frozenset()])*zg)

                    # we divide by the up(a_l)
                    for l in range(2*g + 1):
                        nb = sum(l in Bi for Bi in B)
                        try:
                            t /= ((-1)**g*u(a[l]))**(ZZ(nb/2))
                        except TypeError:
                            raise ValueError('Expected even value') #FIXME
                # t is theta[UoB1] * theta[UoB2] * theta[UoB3] * theta[UoB4] /t_empty(z)^4

                # the sign in the theta (we have changed the caracteristic
                es_US1 = eta_second(g, U.symmetric_difference(S1))
                es_US2 = eta_second(g, U.symmetric_difference(S2))
                es_US = eta_second(g, U ^ S)
                t *= (-1)**ZZ(eta_prime(g,U ^ B[0])*(es_US1 + es_US2 + es_US - eta_second(g,U ^ B[0]))/2)
                t *= (-1)**ZZ(eta_prime(g,U ^ B[1])*(es_US1 + es_US - eta_second(g,U ^ B[1]))/2)
                t *= (-1)**ZZ(eta_prime(g,U ^ B[2])*(es_US2 + es_US - eta_second(g,U ^ B[2]))/2)

                # the sign in the duplication formulae
                t *= (-1)**ZZ(ee[:g]*es_US)

                thp[i] += t/2**g

            # scale the theta. i.e. constants used in doubling
            for elem in [S1, S2, U]:
                eelem = eta(g, U.symmetric_difference(elem))
                thp[i] *= sign_theta_normalized(eelem)/thO[idx(normalize_eta(eelem))]

            # sign when we have normalized the caracteristic
            thp[i] *= sign_theta_normalized(ee)

    th = thc(thp)
    for l in V2:
        th = AddTwoTorsion(th,eta(g,{l}))

    return th



##***** (7) Theta to Mumford *****//

#TODO: Test against Magma, add examples
def Ylm_fromTheta(a,rac,l,m,th,C):
    """
    Let D be a point in Jac(C)\\Theta
    D is represented by the theta functions th of level 4
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let rac be a root of a_1 - a_0
    Let C be the choice of sets in the definition of the f_A

    Compute the function Y_{l,m}
    """
    thc = th.abelian_variety()
    g = thc._dimension
    if l == m:
        raise ValueError(F'l(={l}) and m(={m}) have to be distinct')
    if thc._level != 4:
        raise ValueError(f'Expected a level-4 theta structure')

    U = {2*x for x in range(g+1)}

    thO = thc(0)
    th_empty_4 = IgusaTheorem([eta(g,U)]*4, [th,thO,thO,thO])

    if th_empty_4 == 0:
        raise ValueError('Divisor theta!') #FIXME

    sets = [frozenset([l,m]), frozenset([l]), frozenset([m]), frozenset()]
    th_prod = IgusaTheorem([eta(g, U ^ S) for S in sets], [th,thO,thO,thO])

    Y = sign_s_A(g, [l, m], C)
    Y *= prod(eltEp_to_eltE(a, thc, constant_f(g, S, C[S]), rac) for S in sets[:-1])
    Y /= eltEp_to_eltE(a, thc, constant_f(g, set(), C[frozenset()]), rac)**3

    Y *= th_prod/th_empty_4

    return Y

#TODO: Test against Magma, add examples
def ThetaToMumford_4_Generic(a, rac, th):
    """
    Let D be a point in Jac(C)\\Theta
    D is represented by the theta functions th of level 4
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let rac be a root of a_2-a_1
    Let thc be the theta constants of level 4

    Compute the Mumford polynomials associated to D
    """
    thc = th.abelian_variety()
    g = thc._dimension
    if thc._level != 4:
        raise ValueError(f'Expected a level-4 theta structure')

    F = TowerOfField([parent(elem) for elem in [th[0]] + a])
    K = PolynomialRing(F, 'x')
    x = K.gen()
    a = [F(elem) for elem in a]

    U = {2*x for x in range(g+1)}
    C = choice_of_all_C_Cosset(g) # all other choices should give the same result

    thO = thc(0)
    list_th = [th,thO,thO,thO]
    th_empty_4 = IgusaTheorem([eta(g,U)]*4, list_th)

    if th_empty_4 == 0:
        raise ValueError('Divisor theta!') #FIXME

    u_al = []
    eltE_empty = eltEp_to_eltE(a,thc,constant_f(g, set(), C[frozenset()]),rac)
    for l in range(g+1):
        Sl = frozenset([l])
        th_numer = IgusaTheorem([eta(g, U ^ Sl)]*2 + [eta(g,U)]*2, list_th)
        val = (-1)**g*th_numer/th_empty_4
        val *= eltEp_to_eltE(a,thc,constant_f(g, Sl, C[Sl]), rac)**2
        val /= eltE_empty**2
        u_al.append(val)

    u = K(0)
    for i, t in enumerate(u_al):
        t *= prod((x - a[j])/(a[i] - a[j]) for j in range(g+1) if j != i)
        u += t

    v_al = [F(0)]*g
    for l in range(g):
        for m in rangeS(g+1, [l]):
            t = Ylm_fromTheta(a, rac, l, m, th, C)
            t /= prod(a[m] - a[k] for k in range(g+1) if k not in [l, m])
            v_al[l] += t

    v = K(0)
    for i, t in enumerate(v_al):
        t *= prod((x - a[j])/(a[i] - a[j]) for j in range(g) if j != i)
        v += t

    return u, v

def ThetaToMumford_2_Generic(a, th2):
    """
    Let D be a point in Jac(C)\\Theta
    D is represented by the theta functions th2 of level 2
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let thc2 be the theta constants of level 2

    Compute the Mumford polynomials (u,v^2) associated to D

    EXAMPLES ::

        sage: from avisogenies_sage import *
        sage: F = GF(331); A = AbelianVariety(F, 2, 2, [328 , 213 , 75 , 1])
        sage: P = A([255 , 89 , 30 , 1])
        sage: thp = AlgebraicToAnalyticThetaPoint(P)
        sage: a = list(map(F, [0, 1, 2, 3, 4]))
        sage: ThetaToMumford_2_Generic(a, thp)
        (139*x^2 + 117*x + 157, 57*x^2 + 70*x + 210)

    """
    thc2 = th2.abelian_variety()
    g = thc2._dimension

    if thc2._level != 2:
        raise ValueError(f'Expected a level-2 theta structure')

    Ab = thc2._numbering
    idx = thc2._char_to_idx

    F = parent(th2[0])
    K = PolynomialRing(F, 'x')
    x = K.gen()
    a = [F(elem) for elem in a]

    U = frozenset(2*x for x in range(g+1))
    zg = eta_second(g, set(range(2*g+1)))/2

    C = choice_of_all_C_Cosset(g) # all other choices should give the same result

    idx_etaU = eta(g, U, normalized=True, idx=True)
    if th2[idx_etaU] == 0:
        raise ValueError('Divisor theta!') #FIXME

    u_al = []
    ct_f2_empty = constant_f2_level2(a, thc2, set(), C[frozenset()])
    ct_f2_U = constant_f2_level2(a, thc2, U, C[U])
    for l in range(g+1):
        Sl = frozenset([l])
        val = (-1)**g
        val *= th2[eta(g, U ^ Sl, normalized=True, idx=True)]
        val /= th2[idx_etaU]
        val *= constant_f2_level2(a, thc2, Sl, C[Sl])
        val /= ct_f2_empty
        u_al.append(val)

    # use Lagrange interpolation
    u = K(0)
    for i, t in enumerate(u_al):
        t *= prod((x - a[j])/(a[i] - a[j]) for j in range(g+1) if j!= i)
        u += t

    # we have u
    v2_al = [F(0)]*(2*g - 1)
    for l in range(2*g - 1):
        if l < g:
            V = set(range(g+1))
            V.remove(l)
        else:
            V = set(range(g))

        for m in V:
            t = th2[eta(g,U ^ {l,m}, normalized=True, idx=True)]
            t /= th2[idx_etaU]
            t *= constant_f2_level2(a, thc2, {l,m}, C[frozenset([l,m])])
            t /= ct_f2_empty
            t *= u(a[l])*u(a[m])
            t /= prod((a[m] - a[k])**2 for k in V - {m})
            v2_al[l] += t

        # Now compute the terms t corresponding to m <=> n
        for m, n in product(V, repeat=2):
            if n == m:
                continue
            t = sign_s_A(g,{l,m},C)*sign_s_A(g,{l,n},C)

            t *= th2[eta(g, U ^ {l}, normalized=True, idx=True)]
            t /= th2[idx_etaU]**3
            t *= constant_f2_level2(a, thc2, {l}, C[frozenset([l])])
            t /= ct_f2_empty**3

            # we need to compute s = t_lm(z) t_ln(z) t_m(z) t_n(z)
            s = 0
            for S in combinations(range(2*g + 1), g+1):
                S = frozenset(S)
                if l not in S or len(S & {m,n}) != 1:
                    continue
                e = eta(g, U ^ S ^ {l,m,n})
                r = 0 # r = theta[e](2z) theta[e](0) theta[0](0)^2
                for idxb, b in enumerate(Ab):
                    q = (-1)**ZZ(e[:g]*b[g:])
                    q *= th2[idx(b + e)]
                    q *= th2[idxb]
                    r += q/2**g

                # On multiplie r par la bonne constante dans la somme
                c = set()
                for st in [{l,m}, {l,n}, {m}, {n}]:
                    c.symmetric_difference_update(C[frozenset(st)])
                c.intersection_update(U)
                cst = (-1)**ZZ(eta_prime(g,c)*zg)
                cst /= prod((-1)**(i > j)*(a[j] - a[i]) for i, j in product(S - {l, m, n}, range(2*g + 1)) if j not in S | {m, n})
                cst *= ct_f2_U
                cst *= constant_f2_level2(a, thc2, S ^ {l,m,n}, C[S ^ {l,m,n}])
                r *= cst

                #the sign in the sum
                r *= (-1)**g
                r *= e_2(g, U, S)
                r *= ZZ(-1)**(eta_prime(g, l)*eta_second(g,S - {m,n}))
                r *= ZZ(-1)**(eta_prime(g, {m,n})*eta_second(g,S - {l}))
                r *= ZZ(-1)**(eta_prime(g, m)*eta_second(g, n))
                r *= e_2(g, {n}, S)

                s += r/2**g

            t *= s
            t /= prod(a[m] - a[k] for k in V if k != m)
            t /= prod(a[n] - a[k] for k in V if k != n)
            v2_al[l]+=t

    v2 = K(0)
    for i, t in enumerate(v2_al):
        t *= prod((x-a[j])/(a[i]-a[j]) for j in range(2*g - 1) if j != i)
        v2 += t

    return u, v2

#FIXME: Difference with funcion above? Do we need this or can we join them somehow?
#TODO: Test against Magma, add examples
def ThetaToMumford_2_algclose(a,th2):
    """
    Let D be a point in Jac(C).
    D is represented by the theta functions th2 of level 2
    Let a be the x-coordinate of th Weierstrass points of the curve

    Assume that the base field is algebraically closed

    Compute the Mumford polynomials (u,v^2) associated to D
    """
    thc2 = th2.abelian_variety()
    g = thc2._dimension

    if thc2._level != 2:
        raise ValueError(f'Expected a level-2 theta structure')

    # Ab = thc2._numbering
    U = {2*x for x in range(g+1)}
    th2p = th2

    V = set()
    idx_etaU = eta(g, U, normalized=True, idx=True)
    for l in range(2*g + 1):
        if th2p[idx_etaU] != 0:
            break
        V.add(l)
        th2p = AddTwoTorsion(th2p, eta(g, l))

    u, v2 = ThetaToMumford_2_Generic(a,th2p)

    K = parent(u)
    x = K.gen()

    for l in V:
        if (x - a[l]).divides(u):
            d = u.degree()
            u /= x - a[l]
            u = K(u)
            v = sqrt(v2)
            v2 = K(v2 + v2[2*d - 2]*u**2 - 2*v[d - 1]*v*u )
        else:
            d,e,f = XGCD(u, x - a[l])
            v = sqrt(v2)
            v2 = K(v2 + (e/d)**2*u*v2(a[l]) - 2*e/d*u*v*v(a[l]) )
            u *= x-a[l]

    return u,v2

#TODO: Test against Magma, add examples
def Level2ThetaPointToMumford(a, th2):
    """
    Let D be a point in Jac(C).
    D is represented by the theta functions th2 of level 2
    Let a be the x-coordinate of th Weierstrass points of the curve

    Note. We use an extension field of degree 2

    Compute the Mumford polynomials (u,v^2) associated to D
    """
    thc2 = th2.abelian_variety()
    g = thc2._dimension

    if thc2._level != 2:
        raise ValueError(f'Expected a level-2 theta structure')

    U = {2*x for x in range(g+1)}
    th2p = th2
    idx_etaU = eta(g, U, normalized=True, idx=True)
    V = set()
    for l in range(2*g + 1):
        if th2p[idx_etaU] != 0:
            break
        V.add(l)
        th2p = AddTwoTorsion(th2p, eta(g, l))

    u, v2 = ThetaToMumford_2_Generic(a, th2p)

    K = parent(u)

    F = parent(u[0])
    FF = F.extension(2)
    KK = PolynomialRing(FF, 'x')
    x = K.gen()

    for l in V:
        if (x - a[l]).divides(u):
            d = u.degree()
            u /= x - a[l]
            u = K(u)
            v = K(sqrt(KK(v2)))
            v2 = K(v2 + v2[2*d-2]*u**2 - 2*v[d-1]*v*u )
        else:
            d,e,f = XGCD(u, x - a[l])
            v = K(sqrt(KK(v2)))
            v2 = K(v2 + (e/d)**2*u*v2(a[l]) - 2*e/d*u*v*v(a[l]) )
            u *= x - a[l]

    return u,v2

#TODO: Test against Magma, add examples
def Level4ThetaPointToMumford(a, rac, th):
    """
    Let D be a point in Jac(C)
    D is represented by the theta functions th of level 4
    Let a be the x-coordinate of th Weierstrass points of the curve
    Let rac be a root of a_1 - a_0

    Compute the Mumford polynomials associated to D
    """
    thc = th.abelian_variety()
    g = thc._dimension

    if thc._level != 4:
        raise ValueError(f'Expected a level-4 theta structure')

    U = {2*x for x in range(g+1)}

    thO = thc(0)
    thp=th

    etas = [eta(g,U)]*4
    t_empty_p = IgusaTheorem(etas, [thp,thO,thO,thO])

    V = set()
    for l in range(2*g + 1):
        if t_empty_p != 0:
            break
        V.add(l)
        thp = AddTwoTorsion(thp,eta(g,l))
        t_empty_p = IgusaTheorem(etas, [thp,thO,thO,thO])

    u, v = ThetaToMumford_4_Generic(a, rac, thp)
    K = parent(u)
    x = K.gen()

    for l in V:
        if (x - a[l]).divides(u):
            u /= x - a[l]
            u = K(u)
            c = v.leading_coefficient()
            v -= c*u
        else:
            d,s,_ = XGCD(u,x-a[l])
            assert d != 0
            v -= s/d*u*v(a[l])
            u *= x - a[l]

    return u,v
