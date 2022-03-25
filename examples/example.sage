from avisogenies_sage import *

#Example from Section 6 of 'Efficient Pairing Computation with theta functions'
#by David Lubicz and Damien Robert

FF = GF(331)
g = 2

pt = [328 , 213 , 75 , 1]
A = KummerVariety(FF, g, pt, check=True)

P_list = [255 , 89 , 30 , 1]
P = A(P_list)

R.<X> = PolynomialRing(FF)
poly = X^4 + 3*X^2 + 290*X + 3
FF2.<t> = poly.splitting_field()

Q_list = [158*t^3 + 67*t^2 + 9*t + 293, 290*t^3 + 25*t^2 + 235*t + 280,
 155*t^3 + 84*t^2 + 15*t + 170, 1]
A2 = A.change_ring(FF2)
Q = A2(Q_list)

A == A2 #False

A2(P)+Q

PmQ_list = (62*t^3 + 16*t^2 + 255*t + 129 , 172*t^3 + 157*t^2 + 43*t + 222 ,
 258*t^3 + 39*t^2 + 313*t + 150 , 1)
PmQ = A2(PmQ_list)

QP = Q.diff_add(A2(P), PmQ)

l = 1889
P.weil_pairing(l, Q, QP)
