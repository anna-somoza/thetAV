from avisogenies_sage import *

#Example from Section 6 of 'Efficient Pairing Computation with theta functions'
#by David Lubicz and Damien Robert

FF = GF(331)
n = 2
g = 2

pt = [328 , 213 , 75 , 1]
A = AbelianVariety(FF, n, g, pt, check=True)

P_list = [255 , 89 , 30 , 1]
P = A(P_list, check=True)

R.<X> = PolynomialRing(FF)
poly = X^4 + 3*X^2 + 290*X + 3
FF2.<t> = poly.splitting_field()

Q_list = [158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
 155*t^3 + 84*t^2 + 15*t + 170, 1]
Q = A(Q_list, R=FF2, check=True)

P+Q

PmQ_list = (62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 ,
 258*t^3 + 39*t^2 + 313*t + 150 , 1)
PmQ = A.point(PmQ_list, R=FF2, check=True)

QP = Q.diff_add(P, PmQ)

l = 1889
P.pairing(l, Q, QP)
