from avisogenies_sage import *

p = 2 ^ 3 * 3 ^ 10 - 1
Fp2.<z2> = FiniteField(p ^ 2)
Fp4.<z4> = Fp2.extension(2)
R.<x> = Fp4[]
f = x ^ 6 - 1
C = HyperellipticCurve(f)

A = AnalyticThetaNullPoint.from_curve(C, 2)  # F(2,2)^2, level 2

X = A.to_algebraic()  # "standard" basis
J = C.jacobian()

D = J([x ^ 2 + (462063 * z2 + 443570) * x + 85858 * z2 + 111036, (22095 * z2 + 386770) * x +
        272855 * z2 + 25509])
P = A(D)
PX = P.to_algebraic()


# symplectic basis for the 3^10-torsion
B = [J([x ^ 2 + (462063 * z2 + 443570) * x + 85858 * z2 + 111036, (22095 * z2 + 386770) * x +
        272855 * z2 + 25509]),
     J([x ^ 2 + (109814 * z2 + 369206) * x + 374718 * z2 + 19193,
        (159674 * z2 + 138181) * x + 145795 * z2 + 94117]),
     J([x ^ 2 + (181125 * z2 +
                 438109) * x + 277219 * z2 + 37337, (434269 * z2 + 116389) * x + 246253 * z2 + 340046]),
     J([x ^ 2 + (468216 * z2 + 431937) * x + 448009 * z2 + 314337, (279286 * z2 + 471878) * x +
        155581 * z2 + 298764])]

B_A = [A(pt) for pt in B]
B_X = [pt.to_algebraic() for pt in B_A]

# kernel for a 3^10-isogeny
import random

r = random.sample(range(3 ^ 10), 3)
R1 = B[0] + r[0] * B[2] + r[1] * B[3]
R2 = B[1] + r[1] * B[2] + r[2] * B[3]
R12 = R1 + R1

R1_A = A(R1)
R2_A = A(R2)
R12_A = A(R12)
R1_X = R1_A.to_algebraic()
R2_X = R2_A.to_algebraic()
R12_X = R12_A.to_algebraic()

# kernel for a (3,3)-isogeny
S1 = 3 ^ 9 * R1
S2 = 3 ^ 9 * R2
S12 = 3 ^ 9 * R12

S1_A = A(S1)
S2_A = A(S2)
S12_A = A(S12)

S1_X = S1_A.to_algebraic()
S2_X = S2_A.to_algebraic()
S12_X = S12_A.to_algebraic()

# And now we'd want to compute the isogeny associated to all this.
X0 = X

R = [R1_X, R2_X, R12_X]
S = [S1_X, S2_X, S12_X]
X.isogeny_pt(3, S)

for i in range(9, -1):
    X, R = X.isogeny_pt(3, S, points=R)
    S = [3 ^ i * P for P in R]
    assert all([3 * P == 0 for P in S])

# And then we'd want to recover HyperellipticCurve(X), and maybe some extra points in the curve/jacobian.