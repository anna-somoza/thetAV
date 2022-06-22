# Setting

The data $(A, L, \Theta_n)$ of a dimension $g$ abelian variety together with an even level
$n$ theta structure provides us with a projective embedding $i : A \rightarrow
\mathbb{P}^{n^g-1}$. The data of the theta null point $i(0)$ is equivalent to that of the
theta structure $(A, L, \Theta_n)$. Note that if the level is $2$, we rather get an
embedding of the Kummer variety $K=A/(-1)$ associated to $A$.

If the level $n \geq 4$, from the theta null point, one can produce a complete set of
degree $2$ equations for the embedding $i(A)$ into $\mathbb{P}^{n^g-1}$ using Riemann equations. If the level is
$2$:
- for $g=1$ the theta coordinate directly gives a model of the Kummer line (no equation
  needed);
- for $g=2$, the embedding in $\mathbb{P}^3$ of $K$ is given by quadric equations parametrized by the theta null point.

Still using Riemann equations, it is possible to recover the arithmetic of $A$ or $K$.
This arithmetic goes far beyond the usual group law. Considering the projection
$\pi : \mathbb{A}^{n^g} \rightarrow \mathbb{P}^{n^g-1}$, we say that a point $\tilde{P}$ is an
affine lift of $P$ a projective point if $\pi(\tilde{P})=P$. Some arithmetic operations
with theta coordinates naturally deal with affine point rather than with projective one.
Not only, they make sense in the affine setting but they are also essential ingredient for certain
computations such as Tate and Weil pairings. In the following, we give short summary of all the
arithmetic operations that we have implemented in AVIsogeny by classifying them depending on
whether they are affine or projective, available in level $2$ or higher level.

## Summary of the arithmetic operations:

| Name of the operation     | Level    | Projective/Affine | Definition                                                                                         | AVIsogeny method              |
|:--------------------------|:---------|:------------------|:---------------------------------------------------------------------------------------------------|:------------------------------|
| Normal addition           | $\geq 4$ | projective        | $(P,Q) \rightarrow P +Q$                                                                           | P+Q                           | 
| Normal addition on Kummer | $2$      | projective        | $(P,Q) \rightarrow \{P+Q, P-Q\}$                                                                   | P+Q                           |
| Differentiel addition     | $\geq 2$ | affine            | $(\tilde{P},\tilde{Q}, \tilde{P-Q})\rightarrow \tilde{P+Q}$                                        | P.diff_add(Q, PmQ)            |
| Compatible addition       | $2$      | projective        | $P,Q,R, P+Q, R+Q, 2Q \ne 0  \rightarrow P+R$                                                       |                               | 
| Threeway addition         | $\geq 2$ | affine            | $\tilde{P}, \tilde{Q}, \tilde{R}, \tilde{P+Q}, \tilde{P+R}, \tilde{Q+R} \rightarrow \tilde{P+Q+R}$ | P.three_way_add(Q,R,PQ,QR,PR) |

Note that compatible addition works for level greater than $2$ but has no interest in this case because 
it can be replaced by a normal addition.



