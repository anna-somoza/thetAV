from avisogenies_sage import *
FF = GF(331)
FF2 = GF(331,2)
pt = [26, 191, 70, 130, 256, 29, 255, 309, 272, 52, 15, 123, 99, 1, 94, 239];
A = AbelianVariety(FF, 4, 2, [FF(t) for t in pt])
P0 = A(0)
Q = A([185, 88, 113, 263, 202, 118, 236, 261, 10, 158, 29, 208, 320, 125, 113, 215])
QQ = Q.diff_add(Q, P0)
