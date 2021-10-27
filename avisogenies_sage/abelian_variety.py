"""
This module defines the base class of Abelian varieties with theta structure
as an abstract Scheme.

AUTHORS:

- Anna Somoza (2021)
"""

#*****************************************************************************
#       Copyright (C) 2021 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.categories.fields import Fields
_Fields = Fields()
from six import integer_types
from sage.rings.integer import Integer
from itertools import product, combinations_with_replacement
from sage.rings.all import IntegerRing, Zmod, PolynomialRing, FractionField
ZZ = IntegerRing()
from sage.structure.element import is_Vector
from sage.arith.misc import two_squares, four_squares

from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.schemes.generic.algebraic_scheme import AlgebraicScheme
from sage.schemes.generic.morphism import SchemeMorphism_point
from sage.schemes.generic.homset import SchemeHomset_points
from sage.structure.richcmp import richcmp_method, richcmp
from .av_point import AbelianVarietyPoint

#Note that there is a constructor with the name AbelianVariety. Either overwrite it
#or change name.
@richcmp_method
class AbelianVariety(AlgebraicScheme):
    """
    Base class for Abelian Varieties with theta structure.

    INPUT:

    -  ``R`` -- a field of definition

    -  ``n`` -- an integer; the level of the theta structure.

    -  ``g`` -- an integer; the dimension of the abelian variety.

    -  ``T`` -- a list of length n^g; the theta null point determining the abelian variety.

    EXAMPLES::

        sage: from avisogenies_sage import AbelianVariety
        sage: FF = GF(331)
        sage: A = AbelianVariety(FF, 2,2,[328,213,75,1]); A
        Abelian variety of dimension 2 with theta null point (328 : 213 : 75 : 1) defined over Finite Field of size 331
    """
    _point = AbelianVarietyPoint

    def __init__(self, R, n, g, T, check=False):
        """
        Initialize.
        """
        if is_Vector(T):
            T = list(T)
        if not isinstance(T, (list, tuple, SchemeMorphism_point)):
            raise TypeError(f"Argument (={T}) must be a list, a tuple, a vector or a point.")
        if not isinstance(n, integer_types + (Integer,)):
            raise TypeError(f"Argument (={n}) must be an integer.")
        if not isinstance(g, integer_types + (Integer,)):
            raise TypeError(f"Argument (={g}) must be an integer.")
        if len(T) != n**g:
            raise ValueError(f"T (={T}) must have length n^g (={n**g}).")

        D = Zmod(n)**g
        twotorsion = Zmod(2)**g
        if not D.has_coerce_map_from(twotorsion):
            from sage.matrix.constructor import identity_matrix
            c = twotorsion.hom(n//2*identity_matrix(g), D)
            D.register_coercion(c)

        if check:
            idx = lambda i : ZZ(list(i), n)
            dual = {}
            DD = [2*d for d in D]

            if any(T[idx(-i)] != val for i, val in zip(D, T)):
                raise ValueError('The given list does not define a valid thetanullpoint')

            for (idxi, i), (idxj, j) in product(enumerate(D), repeat=2):
                ii, jj, tt = reduce_twotorsion_couple(i, j);
                for idxchi, chi in enumerate(twotorsion):
                    el = (idxchi, idx(ii), idx(jj))
                    if el not in dual:
                        dual[el] = sum(eval_car(chi,t)*T[idx(ii + t)]*T[idx(jj + t)] for t in twotorsion)
                    dual[(idxchi, idxi, idxj)] = eval_car(chi,tt)*dual[el]

            for elem in combinations_with_replacement(combinations_with_replacement(enumerate(D),2), 2):
                ((idxi, i), (idxj, j)), ((idxk, k), (idxl, l)) = elem
                if i + j + k + l in DD:
                    m = D([ZZ(x)/2 for x in i + j + k + l])
                    for idxchi in range(len(twotorsion)):
                        el1 = (idxchi, idxi, idxj)
                        el2 = (idxchi, idxk, idxl)
                        el3 = (idxchi, idx(m-i), idx(m-j))
                        el4 = (idxchi, idx(m-k), idx(m-l))
                        if dual[el1]*dual[el2] != dual[el3]*dual[el4]:
                            raise ValueError('The given list does not define a valid thetanullpoint')

        PP = ProjectiveSpace(R, n**g -1)
        #Given a characteristic x in (Z/nZ)^g its theta constant is at position ZZ(x, n)
        #Given a coordinate i, T[i] corresponds to the theta constant with characteristic
        #i.digits(n, padto=g)
        self._dimension = g
        self._level = n
        self._ng = n**g

        AlgebraicScheme.__init__(self, PP)

        self._thetanullpoint = self(tuple(R(a) for a in T))
        self._D = D
        self._twotorsion = twotorsion
        self._riemann = {}
        if check:
            self._dual = dual
        else:
            self._dual = {}


    def __richcmp__(self, X, op):
        """
        Compare the Abelian Variety self to `X`.  If `X` is an Abelian Variety,
        then self and `X` are equal if and only if their theta null points are
        equal as projective points.

        TESTS::

            sage: from avisogenies_sage import AbelianVariety
            sage: FF = GF(331); FF2 = GF(331^2);
            sage: A = AbelianVariety(FF, 2,2,[328,213,75,1]);
            sage: B = AbelianVariety(FF2, 2,2,[328,213,75,1]);
            sage: A == B
            False
        """
        if not isinstance(X, AbelianVariety):
            return NotImplemented
        if self.base_ring() != X.base_ring():
            return False
        return richcmp(self._thetanullpoint._coords, X._thetanullpoint._coords, op)

    def _repr_(self):
        """
        Return a string representation of this Abelian variety.
        """
        return f"Abelian variety of dimension {self.dimension()} with theta null point {self.theta_null_point()} defined over {self.base_ring()}"

    def dimension(self):
        """
        Return the dimension of this Abelian Variety.
        """
        return self._dimension

    def level(self):
        """
        Return the level of the theta structure.
        """
        return self._level

    def theta_null_point(self):
        """
        Return the theta null points as a point of the abelian variety.
        """
        return self._thetanullpoint

    def change_ring(self, R):
        """
        Return the Abelian Variety over the ring `R`.

        INPUT:

        - ``R`` -- a field. The new base ring.

        OUTPUT:

        The Abelian Variety over the ring `R`.
        """
        return AbelianVariety(R, self.level(), self.dimension(), self.theta_null_point())

    def base_extend(self, R):
        """
        Return the natural extension of ``self`` over `R`

        INPUT:

        - ``R`` -- a field. The new base field.

        OUTPUT:

        The Abelian Variety over the ring `R`.
        """
        if R not in _Fields:
            raise TypeError(f"Argument (={R}) must be a field.")
        if self.base_ring() is R:
            return self
        if not R.has_coerce_map_from(self.base_ring()):
            raise ValueError(f'no natural map from the base ring (={self.base_ring()}) to R (={R})!')
        return self.change_ring(R)

    def _point_homset(self, *args, **kwds):
        return SchemeHomset_points(*args, **kwds)

    def equations(self):
        try:
            return self._eqns
        except AttributeError:
            F = self.base_ring()
            R = PolynomialRing(F, 'x', self._ng)
            FF = FractionField(R)
            x = R.gens()
            A = self.change_ring(FF)
            P = A.point(x, FF)
            D = self._D
            DD = [2*d for d in D]
            twotorsion = self._twotorsion
            idx = self._char_to_idx
            O = self._thetanullpoint

            eqns = []
            for elem in product(enumerate(D),repeat=4):
                (idxi, i), (idxj, j), (idxk, k), (idxl, l) = elem
                if i + j + k + l in DD:
                    m = D([ZZ(x)/2 for x in i + j + k + l])
                    for idxchi, chi in enumerate(twotorsion):
                        Pel1 = sum(eval_car(chi,t)*P[idx(i + t)]*P[idx(j + t)] for t in twotorsion)
                        Pel4 = sum(eval_car(chi,t)*P[idx(m - k + t)]*P[idx(m - l + t)] for t in twotorsion)
                        Oel2 = sum(eval_car(chi,t)*O[idx(k + t)]*O[idx(l + t)] for t in twotorsion)
                        Oel3 = sum(eval_car(chi,t)*O[idx(m - i + t)]*O[idx(m - j + t)] for t in twotorsion)
                        eq = Pel1*Oel2 - Oel3*Pel4
                        #TODO: check when it would give 0, and whether we gotta use it or not!
                        if eq!=0 and eq not in eqns:
                            eqns.append(eq)
            if eqns == [0]:
                eqns = []
            self._eqns = eqns
            return eqns

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

    def _idx_to_char(self, x, twotorsion=False):
        """
        Return the caracteristic in D that corresponds to a given integer index.
        """
        g = self._dimension
        if twotorsion:
            n = 2
            D = self._twotorsion
        else:
            n = self._level
            D = self._D
        return D(ZZ(x).digits(n, padto=g))

    def _char_to_idx(self, x, twotorsion=False):
        """
        Return the integer index that corresponds to a given caracteristic in D.
        """
        if twotorsion:
            n = 2
        else:
            n = self._level
        return ZZ(list(x), n)

    def riemann_relation(self, *data):
        """
        Computes the riemann relation associated to a given chi, i, j and stores it in P._riemann.
        Depends on which coordinates of P are zero.

        INPUT:

        -  ``P`` -- a theta null point

        -  ``chi`` -- a character, given by its dual element in Z(2) as a subset of Z(n).

        -  ``i`` -- the index of a coordinate of P. For now we are assuming that they are an
           element of Zmod(n)^g.

        -  ``j`` -- the index of a coordinate of P. For now we are assuming that they are an
           element of Zmod(n)^g.


        """
        idx = self._char_to_idx
        char = self._idx_to_char
        if len(data) == 1:
            idxchi, idxi, idxj = data[0]
            i = char(idxi)
            j = char(idxj)
            chi = char(idxchi,True)
        elif len(data) == 3:
            chi, i, j = data
            idxchi = idx(chi, True)
            idxi = idx(i)
            idxj = idx(j)
        else:
            raise TypeError("Input should be a tuple of length 3 or 3 elements.")

        D = self._D
        DD = [2*d for d in D]
        twotorsion = self._twotorsion
        if (idxchi, idxi, idxj) in self._riemann:
            return
        i, j, tij = reduce_twotorsion_couple(i,j)
         # we try to find k and l to apply the addition formulas such that
         # we can reuse the maximum the computations
         # for a differential addition, i == j (generically) and we take k = l = 0
         # for a normal addition, j = 0 so we take k = i, l = j.
        if i == j:
            k0 = D(0)
            l0 = D(0)
        else:
            k0 = i
            l0 = j

        for u, v in product(D,D):
            if u + v not in DD:
                continue
            k, l, _ = reduce_symtwotorsion_couple(k0 + u,l0 + v);
            el = (idxchi, idx(k), idx(l))
            if el not in self._dual:
                self._dual[el] = sum(eval_car(chi,t)*self._thetanullpoint[idx(k + t)]*self._thetanullpoint[idx(l + t)] for t in twotorsion)
            if self._dual[el] != 0:
                kk = k0 + u
                ll = l0 + v
                break
        else: #If we leave the for loop without encountering a break
            for t in twotorsion:
                self._riemann[(idxchi, idx(i + t), idx(j + t))] = []
            return
        kk0, ll0, tkl = reduce_symtwotorsion_couple(kk, ll)
        i2, j2, k2, l2 = get_dual_quadruplet(i, j, kk, ll)
        i20, j20, tij2 = reduce_twotorsion_couple(-i2, j2)
        k20, l20, tkl2 = reduce_twotorsion_couple(k2, l2)
        for t in twotorsion:
            self._riemann[(idxchi, idx(i + t), idx(j + t))] = [i, j, t, kk0, ll0, tkl, i20, j20, tij2, k20, l20, tkl2] #DIFF Maybe we only need to store the sum of all twotorsion.
        return

    def addition_formula(self, P, Q, L):
        """
        Given two points P and Q and a list L containing triplets [chi, i, j], compute
        sum_{t in Z(2)} chi(t) PpQ[i + t] PmQ[j + t]
        for every given triplet.
        """
        twotorsion = self._twotorsion
        idx = self._char_to_idx
        char = self._idx_to_char
        r = {}
        for el in L:
            if el in r:
                continue
            if el not in self._riemann: #Are we sure that this pair (i,j) is reduced as in riemann? Or it is not done like that? check.
                self.riemann_relation(el) #see if we prefer to pass the char, the idx, or both (as an argument with default evaluation?). We can also make it a function that returns said riemann relations, and if they are not computed yet, it computes them and then returns them! That would deal with 4 lines of code and also give a public method to access _riemann.
            IJ = self._riemann[el]
            if not len(IJ):
                raise ValueError("Can't compute the addition! Either we are in level 2 and computing a normal addition, or a differential addition with null even theta null points.")
            ci0, cj0 = IJ[0:2]
            k0, l0 = map(idx, IJ[3:5])
            ci20, cj20 = IJ[6:8]
            ck20, cl20 = IJ[9:11]
            tt = IJ[2] + IJ[5] + IJ[8] + IJ[11] #If we only want the addition, why not store _riemann only with that?

            chi = char(el[0], True)

            s1 = sum(eval_car(chi, t)*Q[idx(ci20 + t)]*Q[idx(cj20 + t)] for t in twotorsion)
            s2 = sum(eval_car(chi, t)*P[idx(ck20 + t)]*P[idx(cl20 + t)] for t in twotorsion)
            A = self._dual[(el[0], k0, l0)]
            # we prefer to store the data in Q because for a differential
            # addition we will have i2=j2=0, so  in level 4, we gain.
            # s1A = s1/A
            S = eval_car(chi, tt)*s2*s1/A
            for t in twotorsion:
                r[(el[0], idx(ci0+t), idx(cj0+t))] = eval_car(chi,t)*S
        return r

    #TODO: Fix all use of scale & general points
    def isogeny(self, l, Q, k, P=None ):
        """
        INPUT:

        - ``self`` -- An abelian variety given as a theta null point of level n and dimension g

        - ``l`` -- an integer

        - ``Q`` -- An univariate polynomial of degree l^g describing a l-torsion subgroup of A

        - ``P`` -- A point of the abelian variety given as a projective theta point

        - ``k`` -- a element of Zmod(n)^g

        """
        if self.level() == 2:
            if P != None:
                raise ValueError('Cannot compute the image of a point via the isogeny')
            #here do stuff taking into account the shape of q? depending on de degree of Q we gotta do different thinks, because it can be of the shape (x - a)*f^2
            if Q.degree() == l**self.dimension():
                poly = 1
                for f, m in Q.factor():
                    if m == 2:
                        poly*=f
                Q = poly
            assert 2*Q.degree() + 1 == l**self.dimension(), f'the input doesn\'t represent a valid {l}-torsion group of A={self}'
            S = Q.parent()
            B = S.quotient(Q)
            y, = B.gens()
            T = PolynomialRing(B, names='mu')
            mu, = T.gens()
            Q = self.point([1,y], B)
            compQ = Q.scale(mu, T)

            #TODO generalize to include the other two cases.
            sqfree = l.squarefree_part()
            l1 = ZZ((l/sqfree).sqrt())
            a, b = two_squares(sqfree)

            t1 = (l1*a)*compQ #Revise if these are the right equations to use
            t2 = (l1*b)*compQ
            idx = self._char_to_idx
            W = B((t1[idx(k)]*t2[0]).mod(mu**l - Q.compatible_lift(l))) # lth power of lambda
            P0 = self.theta_null_point()
            return P0[idx(k)]*P0[0] + 2*evaluate_formal_points(W)(0)

        sqfree = l.squarefree_part()
        l1 = ZZ((l/sqfree).sqrt())
        if sqfree == 1:
            return self._isogeny_1(l1, Q, P, k)
        try:
            a, b = two_squares(sqfree)
            return self._isogeny_twoSq(l, l1, a, b, Q, P, k)
        except ValueError:
            a, b, c, d = four_squares(sqfree)
            return self._isogeny_fourSq(l, l1, a, b, c, d, Q, P, k)

    def _isogeny_1(self, l1, Q, P, k):
        pass

    def _isogeny_twoSq(self, l, l1, a, b, Q, P, k): ##Maybe add a line "if P != None"?
        S = Q.parent()
        B = S.quotient(Q)
        y, = B.gens()
        IK = self.point([1,y], B) ##TODO: generalize this line to general g
        l1IK = l1*IK
        l1aP = (l1*a)*P
        eta = l1IK + l1aP ##what shall we do when the level is 2? can't do it
        T = PolynomialRing(B, names='mu')
        mu, = T.gens()
        etamu = eta.scale(mu, T)
        beta0 = mod(-b/a, l)
        eta1 = beta0*etamu
        D = self._D
        Zn = D.base_ring()
        M = l1*matrix(Zn, 2, 2, [a, b, -b, a])
        J = (column_matrix(Zn, [k, D(0)])*M.inverse()).columns()
        idx = self._char_to_idx
        delta = l1IK.compatible_lift(l1aP, eta, l)
        R = etamu[idx(D(J[0]))]*eta1[idx(D(J[1]))] #This should have factors of mu^l, that we replace by delta
        return evaluate_formal_points(B(R.mod(mu**l - delta)))

    def _isogeny_fourSq(self, l1, a, b, c, d, Q, P, k):
        #"Naive" implementation: Change to use three-way addition
        S = Q.parent().extend_variables('y0')
        B = S.quotient([q(v) for v in S.gens()])
        IK = [self.point([1,v], B) for v in B.gens()] ##TODO: generalize this line to general g
        l1IK = [l1*IKi for IKi in IK]
        l1aP = (l1*a)*P
        l1bP = (l1*b)*P
        eta1 = l1IK[0] + l1aP ##what shall we do when the level is 2? can't do it
        eta2 = l1IK[1] + l1bP
        eta12 = eta1 + eta2
        T = PolynomialRing(B, names='mu')
        mu1,mu2,mu12, = T.gens()
        etamu1 = eta1.scale(mu1, T)
        etamu2 = eta2.scale(mu2, T)
        etamu12 = eta12.scale(mu12, T)
        delta = [eta1**l - l1IK[0].compatible_lift(l1aP, eta1, l),
                 eta2**l - l1IK[1].compatible_lift(l1bP, eta2, l),
                 eta12**l - (l1IK[0] + l1IK[1]).compatible_lift((l1*(a+b))*P, eta1, l)]
        N = matrix(Zmod(l), 2, 2, [a, b, -b, a]).inverse()* matrix(Zmod(l), 2, 2, [c, d, -d, c])
        eta1 = N[0,0]*etamu1 + N[0,1]*etamu2
        eta2 = N[1,0]*etamu1 + N[1,1]*etamu2
        D = self._D
        Zn = D.base_ring()
        M = matrix(Zn, 4, 4, [a, b, -c, -d, b, a, -d, c, c, d, a, -b, d, -c, b, a])
        J = (column_matrix(Zn, [k]+[D(0)]*3)*M.inverse()).columns()
        idx = self._char_to_idx
        R = etamu1[idx(D(J[0]))]*etamu1[idx(D(J[1]))]*eta1[idx(D(J[2]))]*eta2[idx(D(J[3]))]
        for eq in delta:
            R = R.mod(eq)
        return evaluate_formal_points(B(R)) ##How does Evaluate work in this case?

##TODO: Warning, the twotorsion elements should be returned as elements in the twotorsion.
def reduce_sym(x):
    return min(x, -x)

def reduce_twotorsion(x):
    r = list(x)
    D = x.parent()
    halflevels =[i.order()//2 for i in D.gens()]
    n = D.rank()
    for i in range(n):
        if r[i] >= halflevels[i]:
            r[i] = r[i] - halflevels[i];
    return  D(r), x-D(r)

def reduce_symtwotorsion(x):
    x1, tx1 = reduce_twotorsion(x)
    x2, tx2 = reduce_twotorsion(-x)
    if x1 <= x2:
        return x1, tx1
    return x2, tx2

def reduce_symcouple(x,y):
    xred = reduce_sym(x)
    yred = reduce_sym(y)
    if xred < yred:
        return xred, yred
    return yred, xred

def reduce_twotorsion_couple(x,y):
    xred, tx = reduce_twotorsion(x)
    yred, ty = reduce_twotorsion(y)
    if xred < yred:
        return xred, y+tx, tx
    return yred, x+ty, ty

def reduce_symtwotorsion_couple(x,y):
    xred, tx = reduce_symtwotorsion(x)
    yred, ty = reduce_symtwotorsion(y)
    if xred < yred:
        return xred, reduce_sym(y+tx), tx
    return yred, reduce_sym(x+ty), ty

def get_dual_quadruplet(x, y, u, v):
    r = x + y + u + v
    z = r.parent()([ZZ(e)//2 for e in list(r)])
    xbis = z - x
    ybis = z - y
    ubis = z - u
    vbis = z - v
    return xbis, ybis, ubis, vbis

def eval_car(chi,t):
    if chi.parent() != t.parent():
        r = list(t)
        D = t.parent()
        twotorsion = chi.parent()
        halflevels =[i.order()//2 for i in D.gens()]
        n = D.rank()
        for i in range(n):
            r[i] = ZZ(r[i])/halflevels[i]
        t = twotorsion(r)
    return ZZ(-1)**(chi*t);

def evaluate_formal_points(w):
    B = w.parent()
    q = B.modulus()
    S = q.parent()
    u = S.gen()
    f = u*S(w.list())*q.derivative()
    return f//q
