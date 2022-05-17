from avisogenies_sage import *

p = 2 ^ 3 * 3 ^ 10 - 1
Fp2.<z2> = FiniteField(p ^ 2)
Fp4.<z4> = Fp2.extension(2)
R.<x> = Fp4[]
f = x ^ 6 - 1
C = HyperellipticCurve(f)
J = C.jacobian()
l = 3

X = AbelianVariety.from_curve(C, 2)

# symplectic basis for the 3^10-torsion
B = [J([x ^ 2 + (462063 * z2 + 443570) * x + 85858 * z2 + 111036, (22095 * z2 + 386770) * x +
        272855 * z2 + 25509]),
     J([x ^ 2 + (109814 * z2 + 369206) * x + 374718 * z2 + 19193,
        (159674 * z2 + 138181) * x + 145795 * z2 + 94117]),
     J([x ^ 2 + (181125 * z2 +
                 438109) * x + 277219 * z2 + 37337, (434269 * z2 + 116389) * x + 246253 * z2 + 340046]),
     J([x ^ 2 + (468216 * z2 + 431937) * x + 448009 * z2 + 314337, (279286 * z2 + 471878) * x +
        155581 * z2 + 298764])]

B_X = [X(pt) for pt in B]

# kernel for a 3^10-isogeny
r = [1,1,3];
R1 = B[0] + r[0] * B[2] + r[1] * B[3]
R2 = B[1] + r[1] * B[2] + r[2] * B[3]

R1_X = X(R1)
R2_X = X(R2)

# kernel for a (3,3)-isogeny

S1 = (3 ^ 9) * R1
S2 = (3 ^ 9) * R2
S12 = S1 + S2

S1_X = X(S1)
S2_X = X(S2)
S12_X = X(S12)


R = [R1_X]
basis = [S1_X, S2_X]

#X.isogeny_pt(3, basis)

F = X.base_ring()
g = X.dimension()
r = len(R) + 1
ng = X._ng


pts = []
deltas = []
for i, ei in enumerate(basis):
    Re = [(P + ei)[0] for P in R]
    Be = [(ei + ej)[0] for ej in basis[i+1:]]
    pts.append([ei] + Re + Be)
    deltas += ei.compatible_lift(l, R, Re)
    deltas += [eij.compatible_lift(l) for eij in Be]

# This is part of the input. When done with a formal point we obtain the expression for the isogeny
S = PolynomialRing(F, len(deltas), 'mu')
mus = S.gens()
T = S.quotient([mu ** l - delta for mu, delta in zip(mus, deltas)])
AT = X.change_ring(T)

from avisogenies_sage import tools
from functools import partial
from itertools import accumulate
from sage.misc.mrange import cantor_product
idx = partial(tools.idx, n=l)
Zl = Zmod(l)**g
B = Zl.basis()
Bidx = [idx(e) for e in B]
e0 = B[0]
lg = l**g

support = [range(l)]*g + [range(r)]
rows = list(accumulate((len(lst) for lst in pts)))

K = [[None]*lg for i in range(r)]
#In this loop we compute all combinations aiei with ai in [0,1]
#The other computations can happen as diff additions
#The cantor_product iterator guarantees that when we reach a certain element
#all the sub-sums are already inicialized
for *lst, j in cantor_product(*support):
    #print(lst, j)
    idxe = idx(lst)
    e = Zl(lst)
    ite = (i for i,t in enumerate(lst) if t)
    if e == 0:
        #print("Case 0")
        K[j][0] = AT(0) if j == 0 else AT(R[j-1])
        continue
    i0 = next(ite)  # first non-zero element
    if e in B: #i0 will be the index of the element in the basis
        #print("Case 1")
        rowi0 = rows[i0-1] if i0 != 0 else 0
        K[j][idxe] = AT(pts[i0][j]).scale(mus[rowi0 + j])
        continue
    k = next((i for i,t in enumerate(lst) if t>1), None)
    if k is None: #all elements are 0 or 1
        i1 = next(ite) #If we are here, this won't give an error because e!=0, e not in B, so there's at least two 1
        if j == 0 and next(ite,None) is None: #we only have two ones, so it's still given in the input
            #print("Case 2")
            rowi0 = rows[i0-1] if i0 != 0 else 0 #i0 < i1 by definition
            ij = r + i1 - i0 - 1
            K[0][idxe] = AT(pts[i0][ij]).scale(mus[rowi0 + ij])
            continue
        #print("Case 3")
        e0, e1 = B[i0], B[i1]
        idx0, idx1 = Bidx[i0], Bidx[i1]
        #P.three_way_add(Q, R, PQ, QR, PR)
        K[j][idxe] = K[0][idx0].three_way_add(K[0][idx1], K[j][idx(e - e0 - e1)], K[0][idx(e0 + e1)], K[j][idx(e - e0)], K[j][idx(e - e1)])
        continue
    #print("Case 4")
    ek = B[k]
    idxk = Bidx[k]
    K[j][idxe] = K[j][idx(e - ek)].diff_add(K[0][idxk], K[j][idx(e - 2*ek)])

img = []

for j in range(r):
    imgr = [0]*ng
    for i in range(ng):
        imgr[i] = sum(el[i] ** l for el in K[j]).lift()
    img.append(imgr)

fA = KummerVariety(F, g, img[0], check=True)
fR = [fA(el) for el in img[1:]]

B, KB = X.isogeny(l, [S1_X, S2_X, S12_X])

assert fA == B