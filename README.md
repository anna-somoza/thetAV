<div class="row">
  <div class="column"><img src="docs/source/logo/logo.svg" align="left" title="thetAV" alt="logo for the thetAV package"></div>
  <div class="column"><h1 align="center">thetAV</h1>
<p align="center">
  A <a href="https://www.sagemath.org/">SageMath</a> package on abelian varieties with theta structure
</p>
<p align="center">      <a href="https://thetav.readthedocs.io/en/latest/?badge=latest">
         <img alt="Documentation Status" src="https://readthedocs.org/projects/thetav/badge/?version=latest">
      </a></p>
</div>
</div>

<!-- start elevator-pitch -->
The package <span style="color:var(--color-problematic)">**thetAV**</span> aims to implement a complete set of tools to represent and compute with Abelian varieties and their moduli space within SageMath.

We aim at making our package to be as general, efficient and user-friendly as possible. We also want to lay the groundwork and appeal to the community to contribute to our library and to develop new extensions on top of it.

This library borrows some of its code and has been much inspired by the Magma package [avisogenies].

[avisogenies]:https://gitlab.inria.fr/roberdam/avisogenies/

<!-- end elevator-pitch -->

# Functionality

In our library, we manipulate the objects $(A, L, \Theta)$ where
- $A$ is a dimension-$g$ abelian variety over a field $k$;
- $L$ is a symmetric line bundle of level 2 or 4;
- $\Theta$ is a theta structure.

A triple $(A, L, \Theta)$ is represented by the data of a theta null point, that is, a projective point in $\mathbb{P}^{n^g}$ defined over $k$. The points of $A$ are then also written as projective points in $\mathbb{P}^{n^g}$ defined over $k$.

We also provide methods to interface with other representations:

- Using different bases for the theta structure
- In the special case of Jacobians of hyperelliptic curves, compatibility with Mumford's representation.

This library also implements a full range of arithmetic operations over these abelian varieties, and computes isogenies between abelian varieties. See [the documentation](https://thetAV.readthedocs.io/en/latest/) for more details.

# Quickstart

<!-- start install -->
First of all, make sure that you have SageMath 9.5 or later.

**Install from TestPyPI**

thetAV is currently distributed on [TestPyPI]. You can install it with the command:

```console
$ sage -pip install -i https://test.pypi.org/simple/ thetAV
```

**Local installation from source**

1. Download the source from the repository:

```console
$ git clone https://github.com/anna-somoza/thetAV.git
```

2. Go to the package directory and run

```console
$ make install
```

[TestPyPI]:https://test.pypi.org/project/thetAV/
<!-- end install -->

# First steps
<!-- start examples -->
Once <span style="color:var(--color-problematic)">**thetAV**</span> is installed, open SageMath, import the module, and you are ready to create your first abelian variety with theta structure:

```sagecon
sage: from thetAV import *
sage: A = AbelianVariety(GF(331), 4, 1, [26, 191, 70, 130])
Abelian variety of dimension 1 with theta null point (26 : 191 : 70 : 130) defined over Finite Field of size 331
```
<!-- end examples -->

For more examples on how to use the package, see the [tutorials](https://thetAV.readthedocs.io/en/latest/tutorials/example.html) or have a look at the folder `/examples/`.
