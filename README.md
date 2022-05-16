[![Documentation Status](https://readthedocs.org/projects/avisogenies/badge/?version=latest)](https://avisogenies.readthedocs.io/en/latest/?badge=latest)

# Goal

The aim of AVisogeny is to have a set of tools as complete as possible to represent and compute with
Abelian varieties and their moduli space available in Sagemath. Our aim is to be as
general, efficient and user friendly as possible. We also want to lay the groundwork and
appeal to the community to developp extensions on top of our library.

In general, we represent the abelian
varieties (together with a very ample symmetric line bundle) with the projective
coordinates provided by a theta structure. In the special case that the abelian variety
$A$ is the jacobian of a curve $C$ other representations are available such as Mumford's
representation if $C$ is hyperelliptic: we want to make the switch between the different
representations as transparent as possible for the user.


This library borrows some of its code and has been much inspired by [avisogenies](https://gitlab.inria.fr/roberdam/avisogenies/).

# Introduction

Let $A$ be a dimension-$g$ abelian variety together with a (symmetric) ample line bundle $L$. We say that $L$ has level
$n>0$ if the kernel $K$ of the polarisation $\phi_L : A \rightarrow \hat{A}$ 
is isomorphic to $(\mathbb{Z}/n\mathbb{Z})^{2g}$. We have $\operatorname{dim} \Gamma(A,
L)=n^g$ and, if $t=(t_1, \ldots, t_{n^g})$ is a basis of sections of $\Gamma(A, L)$, we have a
projective morphism $\mu_t : A \rightarrow P^{n^g}$, $x \mapsto (t_i(x))$. By a Theorem of Lefschetz
this morphism is an embedding if $n\geq 3$. In practise, we consider even levels in order to be
able to use duplication and Riemann formulas for the arithmetic. As the dimension of the
ambiant space is $2^n-1$ if $n$ is the level, the lower level is the best for computations. Therefore, we mainly
work with:
- level 2: we obtain (generically) an embedding of the Kummer variety associated to $A$ that
  is the quotient of $A$ by the automorphism $(-1)$
- level 4 : we have an embedding of $A$ and the full arithmetic on it.

The polarisation $L$ induces a Weil paring on $K$.
Note that the embedding $\mu_t$ depends on the choice of the basis $t$. But the data of:
1) a symplectic decomposition of $K= K_1 \oplus K_2$ for the Weil pairing;
2) sections $s_1 : K_i \rightarrow G(L)$ where $G(L)$ is the theta group of $L$

defines a unique basis of $\Gamma(A, L)$. The data of 1) and 2) is called a *theta structure* after Mumford.

If $\Theta$ is a theta structure, we denote by $t_\Theta=(t_1, \ldots, t_{n^g})$ the unique
basis of $\Gamma(A,L)$ defined by $\Theta$ and $\mu_{t_\Theta} : A \rightarrow P^{n^g}$ the
morphism. The point $\mu_{t_\Theta}(0)=(t_i(0))$ is called the theta null point of
$(A,L,\Theta$). Its importance comes from the fact that, if $n\geq 4$, 
- the data of the theta null point is equivalent to the data of $(A, L, \Theta)$;
- it parametrises the Riemann equations which give equations for the embedding of $A$ into
  $P^{n^g}$ as well as the arithmetic of $A$.

# About this package

In our library, we manipulate the objects $(A, L, \Theta)$ where
- $A$ is a dimension-$g$ abelian variety over a field $k$;
- $L$ is a symmetric line bundle of level 2 or 4;
- $\Theta$ is a theta structure.

A triple $(A, L, \Theta)$ is given by the data of a theta null point that is a projective
point in $P^{n^g}$ defined over $k$.


Type variété abélienne: thêta null point
Type Jacobienne (via un type courbe)

- Equations: Riemann relations, take a random point, test if a point is on the AV;
- Equations for the moduli space of abelian varieties with theta structure ;
- Arithmetic: normal addition, differential addition, exponentiation, threewayadd,
  compatible addition (level 2), P \pm Q (level 2)
- Pairings: Tate, Weil
- Isogenies and cyclic isogenies
- conversation : curves <=> theta (Thomae + choice of sign), points (Mumford <=> theta)
- Isogeny graph : possible degrees of the points in the kernel, manage the extensions for
  theta + points in the kernel, compute symplectic basis of the l-torsion
- computation of the endomorphism ring

# To install the Sage package
From the package directory, run

```console
$ make install
```

# Usage
For examples on how to use the package, see the tutorials in the documentation or the folder `/examples/`.
