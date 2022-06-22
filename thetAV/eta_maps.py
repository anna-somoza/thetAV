"""
Half-integer characteristics and computations of sign with half-integer characteristics

Based on the work in [VanW]_ and the magma implementation by Romain Cosset.

AUTHORS:

- Anna Somoza (2021-22): initial implementation

.. todo::

    - Reformat info above.
    - Sort documentation by source (to maintain layout)

"""


# ****************************************************************************
#             Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#    Distributed under the terms of the GNU General Public License (GPL)
#    as published by the Free Software Foundation; either version 2 of
#    the License, or (at your option) any later version.
#                                    https://www.gnu.org/licenses/
# ****************************************************************************


from itertools import chain

from sage.functions.other import ceil, floor
from sage.modules.free_module_element import zero_vector
from sage.rings.all import ZZ


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

        sage: from thetAV.eta_maps import eta_prime
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
        return normalize_eta(v) if normalized else v
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

        sage: from thetAV.eta_maps import eta_second
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
        return normalize_eta(v) if normalized else v
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

        sage: from thetAV.eta_maps import eta
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
            return 0 if idx else V(0)
    except TypeError:
        ep = eta_prime(g, L)
        es = eta_second(g, L)
        v = V(list(chain(ep, es)))
        return ZZ(list(v), 2) if idx else v
    else:
        ep = sum((eta_prime(g, i) for i in L))
        es = sum((eta_second(g, i) for i in L))
        v = V(list(chain(ep, es)))
        if normalized:
            return ZZ([x%2 for x in v], 2) if idx else normalize_eta(v)
        return v


def normalize_eta(v):
    """
    It returns the vector `v` reduced mod 2ZZ^g, that is, with entries 0 or 1.

    EXAMPLES ::

        sage: from thetAV.eta_maps import eta, eta_second, normalize_eta
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

    See [VanW, Equation (8)]_ for more information on the quasi-periodicity of theta constants.

    It accepts both eta vectors and a tuple (g, L) that defines an acceptable input for `eta`.

    EXAMPLES ::

        sage: from thetAV.eta_maps import eta, sign_theta_normalized
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
    Computes e_star as defined in [VanW, page 3090]_.

    EXAMPLES ::

        sage: from thetAV.eta_maps import eta, e_star
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
    Compute e_2(eta(A1),eta(A2)) as defined in [VanW, page 3090]_.

    EXAMPLES ::

        sage: from thetAV.eta_maps import e_2
        sage: e_2(5, [0,1], [5,6])
        1

    """
    eta1 = eta(g, A1)
    eta2 = eta(g, A2)
    return ZZ((-1)**ZZ(eta2[:g]*eta1[g:] - eta1[:g]*eta2[g:]))
