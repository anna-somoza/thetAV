# Avisogenies

The aim of this project is to recode all the functions of avisogenies with improvements in the algorithms and in Sagemath
In  particular we have now an algorithm to compute isogenies which is very efficient and simple to implement : it improves the preceding algorithms for l=3 mod 4 and for cyclic isogeny in general.

Type variété abélienne: thêta null point
Type Jacobienne (via un type courbe)

- Equations: Riemann relations, take a random point, test if a piont is on the AV;
- Equations for the moduli space of abelian varieties with theta structure ;
- Arithmetic: normal addition, differential addition, exponentiation, threewayadd,
  compatible addition (level 2), P \pm Q (level 2)
- Pairings: Tate, Weil
- Isogenies and cyclic isogenies
- conversation : curves <=> theta (Thomae + choice of sign), points (Mumford <=> theta)
- Isogeny graph : possible degrees of the points in the kernel, manage the extensions for
  theta + points in the kernel, compute symplectic basis of the l-torsion
- computation of the endomorphism ring

## Sagemath implementation
 [![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/git/https%3A%2F%2Fgitlab.inria.fr%2Froberdam%2Favisogenies/sage)

#### To install the Sage package
From the package directory, run

```sh
$ sage -pip install .
```

#### Usage
Once the package is installed, you can use it in Sagemath with:

```sh
sage: from avisogenies_sage import *
sage: FF = GF(331)
sage: pt = [26, 191, 70, 130, 256, 29, 255, 309, 272, 52, 15, 123, 99, 1, 94, 239];
sage: A = AbelianVariety(FF, 4, 2, [FF(t) for t in pt])
Abelian variety of dimension 2 with theta null point (26 : 191 : 70 : 130 : 256 : 29 : 255 : 309 : 272 : 52 : 15 : 123 : 99 : 1 : 94 : 239)
```
See also the [binder demo](https://mybinder.org/v2/git/https%3A%2F%2Fgitlab.inria.fr%2Froberdam%2Favisogenies/sage?filepath=.%2Fexample.ipynb
) or the file `example.sage`.
