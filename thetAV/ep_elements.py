"""
Morphism functionalities.


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

"""
This file contains functions to compute morphisms between hyperelliptic curves and the
corresponding abelian varieties (their jacobians) with theta functions of level 2 and 4.

The first half is from [VanW]_ and the last sections are algorithms from [Coss]_.
Based on the Magma implementation by Romain Cosset.

LAYOUT:
   
    3 - Manipulations of elements of Ep
    
    4 - twisted theta
    
    3 - Auxiliary functions
    
    4 - Expression of Ep
    
    6 - Mumford to Theta
    
    7 - Theta to Mumford

REFERENCES:

.. [VanW] P. Van Wamelen. Equations for the Jacobian of a hyperelliptic curve.
   Trans. Am. Math. Soc, 350(8), pp.3083-3106, 1998.

.. [Coss] R. Cosset. Applications des fonctions thêta à la cryptographie sur courbes hyperelliptiques.
   PhD thesis, Université Henri Poincaré – Nancy 1, 2011.


.. todo::

    - Reformat info above.
    - Sort documentation by source (to maintain layout)
    
"""

from collections import Counter, namedtuple

from sage.misc.all import prod
from sage.rings.all import ZZ, Integer

integer_types = (int, Integer)


class EpElement(namedtuple('EpElement', ['sign', 'power', 'numer', 'denom'], defaults=[1, 0, Counter(), Counter()])):
    """
    The element of E as defined in Definition 5.1.3 in [Coss]_, where the roots sqrt(a_i - a_j)
    are expressed in terms of theta constants and sqrt(a_1 - a_0).

    .. NOTE::

        The indexes are shifted to start at 0 with respect to the reference.

    EXAMPLES:

    In order to see the vector representation of the keys in `numer` and `denom` one can use the `str` or `print` methods ::

        sage: from thetAV.ep_elements import EpElement
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

            sage: from thetAV.ep_elements import EpElement
            sage: from collections import Counter
            sage: x = EpElement(numer=Counter([1,2,3]), denom=Counter([1,1,2,4])); x
            EpElement(sign=1, power=0, numer=Counter({1: 1, 2: 1, 3: 1}), denom=Counter({1: 2, 2: 1, 4: 1}))
            sage: x.clean_common()
            EpElement(sign=1, power=0, numer=Counter({3: 1}), denom=Counter({1: 1, 4: 1}))

        """
        return self._replace(numer=self.numer - self.denom, denom=self.denom - self.numer)

    def __mul__(self, other):
        """
        Multiply two elements of Ep, that is, multiply their signs, add their powers and multiply
        the numerators and denominators.

        EXAMPLES ::

            sage: from thetAV.ep_elements import EpElement
            sage: from collections import Counter
            sage: x = EpElement(sign=-1, power=2, numer=Counter([3]), denom=Counter([4]))
            sage: y = EpElement(sign=-1, power=3, numer=Counter([3]), denom=Counter([4, 5]))
            sage: x*y
            EpElement(sign=1, power=5, numer=Counter({3: 2}), denom=Counter({4: 2, 5: 1}))

        """
        elem = EpElement(self.sign * other.sign, self.power + other.power, self.numer + other.numer,
                         self.denom + other.denom)
        return elem.clean_common()

    def __str__(self):
        s = [f'sign={self.sign}', f'power={self.power}']
        n = 'numer={\n    '
        n += ',\n    '.join(sorted(f'{key.digits(2)}: {value}' for key, value in self.numer.items()))
        n += '\n}'
        s.append(n)
        d = 'denom={\n    '
        d += ',\n    '.join(sorted(f'{key.digits(2)}: {value}' for key, value in self.denom.items()))
        d += '\n}'
        s.append(d)
        return ',\n'.join(s)

    def __truediv__(self, other):
        """
        Divide two elements of Ep, that is, divide their signs, subtract their powers and
        cross-multiply the numerators and denominators.

        EXAMPLES ::

            sage: from thetAV.ep_elements import EpElement
            sage: from collections import Counter
            sage: x = EpElement(sign=-1, power=2, numer=Counter([3]), denom=Counter([4]))
            sage: y = EpElement(sign=-1, power=3, numer=Counter([3]), denom=Counter([4, 5]))
            sage: x/y
            EpElement(sign=1, power=-1, numer=Counter({5: 1}), denom=Counter())

        """
        elem = EpElement(self.sign * other.sign, self.power - other.power, self.numer + other.denom,
                         self.denom + other.numer)
        return elem.clean_common()

    def __pow__(self, b):
        """
        Compute the power of an element of Ep, that is, compute the power of the sign,
        the multiple of the power, and multiply the multiplicities of the elements in the numerator
        and denominator.

        EXAMPLES ::

            sage: from thetAV.ep_elements import EpElement
            sage: from collections import Counter
            sage: x = EpElement(sign=-1, power=2, numer=Counter([3]), denom=Counter([4]))
            sage: y = EpElement(sign=-1, power=3, numer=Counter([3]), denom=Counter([4, 5]))
            sage: x/y
            EpElement(sign=1, power=-1, numer=Counter({5: 1}), denom=Counter())

        """
        if b == 0:
            return EpElement()
        elif b < 0:
            denom = Counter({k: -b * v for k, v in self.numer.items() if b * v != 0})
            numer = Counter({k: -b * v for k, v in self.denom.items() if b * v != 0})
        else:
            numer = Counter({k: b * v for k, v in self.numer.items() if b * v != 0})
            denom = Counter({k: b * v for k, v in self.denom.items() if b * v != 0})
        elem = EpElement(self.sign ** b, self.power * b, numer, denom)

        return elem

    def evaluate(self, a, thc, rac=None):
        """
        Let self be an element of Ep. Evaluate self.

        INPUT:

        - ``self`` - an EpElement.
        - ``a`` - list of x-coordinates of the Weierstrass points.
        - ``thc`` - the theta null point associated to the jacobian of the curve.
        - ``rac`` - a root of <a_1 - a_0>

        EXAMPLES ::

            sage: from thetAV import KummerVariety
            sage: from thetAV.morphisms_aux import compatible_sqrt
            sage: g = 2; A = KummerVariety(GF(331), 2, [328 , 213 , 75 , 1])
            sage: thc = A.with_theta_basis('F(2,2)^2')
            sage: a = [0,1,4,6,7]
            sage: f = compatible_sqrt(g, 4, 2)
            sage: (f*f).evaluate(a, thc)
            249

        """
        level = thc.level()
        thO = thc(0)

        if level == 2:
            try:
                ff = self.sign * (a[1] - a[0]) ** ZZ(self.power / 2)
            except TypeError:
                raise ValueError('The power of sqrt(a_1 - a_0) in self is expected to be even.')

            try:
                ff *= prod(thO[elem] ** ZZ(multi / 2) for elem, multi in self.numer.items())
            except TypeError:  # If one of the exponents is not integer
                raise ValueError('All multiplicities in the numerator of self are expected to be even.')

            try:
                ff /= prod(thO[elem] ** ZZ(multi / 2) for elem, multi in self.denom.items())
            except TypeError:  # If one of the exponents is not integer
                raise ValueError('All multiplicities in the denominator of self are expected to be even.')

            return ff

        if level == 4:
            if rac is None:
                raise TypeError('Missing root of <a_2-a_1>.')
            ff = self.sign * rac ** self.power
            ff *= prod(thO[elem] ** multi for elem, multi in self.numer.items())
            ff /= prod(thO[elem] ** multi for elem, multi in self.denom.items())
            return ff

        raise NotImplementedError('Only implemented for level 2 and 4.')
