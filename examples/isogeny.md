--
jupytext:
  formats: ipynb,md:myst
  text_representation:
    extension: .md
    format_name: myst
    format_version: 0.13
    jupytext_version: 1.15.2
kernelspec:
  display_name: SageMath 10.2
  language: sage
  name: sagemath
---

# Example for arithmetic on Kummer variety



```{code-cell}
``
from thetAV import *

p = 2 ** 3 * 3 ** 10 - 1
Fp2.<z2> = FiniteField(p ^ 2)
Fp4.<z4> = Fp2.extension(2)
R.<x> = Fp4[]
f = x ^ 6 - 1
C = HyperellipticCurve(f)
J = C.jacobian()
l = 3

X = KummerVariety.from_curve(C)

#symplectic basis for the 3^10-torsion
B = [J((x^2 + (405002*z2 + 466501)*x + 88295*z2 + 291900, (362808*z2 + 138216)*x + 372982*z2 + 250072)),
J((x^2 + (287867*z2 + 4229)*x + 394728*z2 + 274880, (56090*z2 + 230157)*x + 346060*z2 + 222757)),
J((x^2 + (461662*z2 + 112037)*x + 21802*z2 + 4627, (103471*z2 + 55999)*x + 273358*z2 + 351342)),
J((x^2 + (138821*z2 + 435594)*x + 277412*z2 + 415162, (246149*z2 + 305080)*x + 466236*z2 + 151400))]

# kernel for a 3^10-isogeny
r = [3,6,2]
R = [X(pt) for pt in [B[0] + r[0] * B[2] + r[1] * B[3], B[1] + r[1] * B[2] + r[2] * B[3]]]

# kernel for a (3,3)-isogeny
basis = [(3^9)*pt for pt in R]

fA, fR = X.isogeny(l, basis, R)
```

