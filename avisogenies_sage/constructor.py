"""
Constructor for abelian varieties with extra structure.

AUTHORS:

- Anna Somoza (2021-22): initial implementation

"""

#*****************************************************************************
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************


from sage.modular.abvar.constructor import AbelianVariety as ModularAbelianVariety
from .theta_null_point import AbelianVariety_ThetaStructure

def AbelianVariety(*data, **kwargs):
    """
    Create the abelian variety corresponding to the given defining data.

    INPUT:

    An integer, string, newform, modsym space, congruence subgroup or tuple of congruence subgroups (see :func:`~sage:sage.modular.abvar.constructor.AbelianVariety` in Sagemath) or a theta
    structure (see :class:`~avisogenies_sage.abelian_variety.AbelianVariety_ThetaStructure`).

    OUTPUT: a modular abelian variety with extra structure.
    
    EXAMPLES:
    
    Giving the data of the theta structure associated to an Abelian Variety we can create an instance of :class:`~avisogenies_sage.abelian_variety.AbelianVariety_ThetaStructure`::
    
        sage: from avisogenies_sage import AbelianVariety
        sage: AbelianVariety(GF(331), 4, 1, [328,213,75,1])
        Abelian variety of dimension 1 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
    
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
    
        sage: from avisogenies_sage import *
        sage: F.<z> = GF(83^2)
        sage: T = [68, z + 33, 46, z + 33, 2*z + 29, 77*z + 58, 81*z + 31, 38*z + 16, 8, 67*z + 53, 48, 67*z + 53, 2*z + 29, 38*z + 16, 81*z + 31, 77*z + 58]
        sage: A = AbelianVariety(F, 4, 2, T, check=True)

    """
    if len(data) > 1:
        return AbelianVariety_ThetaStructure(*data, **kwargs)
    
    return ModularAbelianVariety(data[0])
