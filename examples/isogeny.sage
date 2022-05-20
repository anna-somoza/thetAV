from avisogenies_sage import *

p = 2 ^ 3 * 3 ^ 10 - 1
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

S = PolynomialRing(Fp4, 4, 'x')

F = X.base_ring()
g = X.dimension()
ng = X._ng
r = len(R) + 1

test = copy(R[0])

pts = []
deltas = []
for i, ei in enumerate(basis):
    Re = [(P + ei)[0] for P in R]
    Be = [(ei + ej)[0] for ej in basis[i + 1:]]
    pts.append([ei] + Re + Be)
    deltas += ei.compatible_lift(l, R, Re)
    deltas += [eij.compatible_lift(l) for eij in Be]

S = PolynomialRing(F, len(deltas), 'mu')
mus = S.gens()
T = S.quotient([mu ** l - delta for mu, delta in zip(mus, deltas)])
AT = X.change_ring(T)

idx = partial(tools.idx, n=l)
Zl = Zmod(l) ** g
B = Zl.basis()
Bidx = [idx(e) for e in B]
lg = l ** g

support = [range(l)] * g + [range(r)]
rows = list(accumulate((len(lst) for lst in pts)))

K = [[None] * lg for i in range(r)]
# The cantor_product iterator guarantees that when we reach a certain element
# all the sub-sums are already initialized
for *lst, j in cantor_product(*support):
    idxe = idx(lst)
    e = Zl(lst)
    ite = (i for i, t in enumerate(lst) if t)
    if e == 0:
        K[j][0] = AT(0) if j == 0 else AT(R[j - 1])
        continue
    i0 = next(ite)  # first non-zero element
    if e in B:  # i0 will be the index of the element in the basis
        rowi0 = rows[i0 - 1] if i0 != 0 else 0
        K[j][idxe] = AT(pts[i0][j]).scale(mus[rowi0 + j])
        continue
    k = next((i for i, t in enumerate(lst) if t > 1), None)
    if k is None:  # all elements are 0 or 1, and sum is at least 2
        i1 = next(ite)
        if j == 0 and next(ite, None) is None:  # we only have two ones, so it's still given in the input
            rowi0 = rows[i0 - 1] if i0 != 0 else 0  # i0 < i1 by definition
            ij = r + i1 - i0 - 1
            K[0][idxe] = AT(pts[i0][ij]).scale(mus[rowi0 + ij])
            continue
        e0, e1 = B[i0], B[i1]
        idx0, idx1 = Bidx[i0], Bidx[i1]
        K[j][idxe] = K[0][idx0].three_way_add(K[0][idx1], K[j][idx(e - e0 - e1)], K[0][idx(e0 + e1)],
                                              K[j][idx(e - e0)], K[j][idx(e - e1)])
        continue
    ek = B[k]
    idxk = Bidx[k]
    K[j][idxe] = K[j][idx(e - ek)].diff_add(K[0][idxk], K[j][idx(e - 2 * ek)])

img = []
for j in range(r):
    imgr = [0] * ng
    for i in range(ng):
        imgr[i] = sum(el[i] ** l for el in K[j]).lift()
    img.append(imgr)

fA = KummerVariety(F, g, img[0])
fR = fA(img[1])