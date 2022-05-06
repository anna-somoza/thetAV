from avisogenies_sage import *

#***** In level 4 *****/

# First we define the curve in Rosenhain form and its Jacobian
F.<z> = GF(83^2)
Fx.<x> = PolynomialRing(F)

g = 2
a = [F(el) for el in [0, 1, 3, 15, 20]] # the roots of self
f = prod(x - al for al in a)
C = HyperellipticCurve(f)
J = Jacobian(C)(F)

# We need to fix a square root (might live in an extension of degree two).
rac = sqrt(a[1]-a[0])

# The Theta constants of the Jacobian.
thc = [0]*(2**(2*g))
idx = lambda s : ZZ(s, 2)
thc[idx([0,0,0,0])]=F(1)
thc[idx([0,0,1,1])]=z^1491
thc[idx([0,0,1,0])]=z^777
thc[idx([0,0,0,1])]=F(30)
thc[idx([1,0,0,0])]=F(37)
thc[idx([1,0,0,1])]=z^2058
thc[idx([0,1,0,0])]=F(56)
thc[idx([1,1,0,0])]=F(57)
thc[idx([0,1,1,0])]=z^609
thc[idx([1,1,1,1])]=z^1533
#If we indicate the original curve, then we can create point from points 
#of the Jacobian directly
thc = AnalyticThetaNullPoint(F, 4, g, thc, curve=C, wp=a, rac=rac)
thcC = AnalyticThetaNullPoint.from_curve(C, 4)

# Point from a Mumford divisor
u=(x-43)*(x-10)
v=z^954*x + z^2518
D = J([u,v])
thD = thc(D)

# From the theta constant values
th = [0]*(2**(2*g))
th[idx([0,0,0,0])] = z^1755
th[idx([0,0,1,1])] = z^1179
th[idx([0,0,1,0])] = z^977
th[idx([0,0,0,1])] = z^1105
th[idx([1,0,0,0])] = z^352
th[idx([1,0,0,1])] = z^1674
th[idx([0,1,0,0])] = z^2523
th[idx([1,1,0,0])] = z^5890
th[idx([0,1,1,0])] = z^5051
th[idx([1,1,1,1])] = z^5243
th[idx([0,1,0,1])] = z^4021
th[idx([0,1,1,1])] = z^4716
th[idx([1,0,1,0])] = z^139
th[idx([1,1,1,0])] = z^507
th[idx([1,0,1,1])] = z^2832
th[idx([1,1,0,1])] = z^3382
th = thc(th)

#TODO create comparison function for analytic classes
assert thD._coords == th._coords

#The reverse functionality
#TODO create as method of analytic classes
from avisogenies_sage.morphisms_level4 import Level4ThetaPointToMumford
uth,vth = Level4ThetaPointToMumford(a, rac, th) 

assert D == J([uth, vth])

#***** In level 2 *****/

# First we define the curve and its Kummer surface

F = GF(83^2)
z, = F.gens()
Fx.<x> = PolynomialRing(F)

g = 2
a = [F(el) for el in [0,1,3,15,20]] # the roots of self

f = prod(x - al for al in a)
C = HyperellipticCurve(f)
J = Jacobian(C)(F)

# The Theta constants of the Kummer surface.
thc2 = [0]*(2**(2*g))
idx = lambda s : ZZ(s, 2)
thc2[idx([0,0,0,0])] = F(1)
thc2[idx([0,0,1,1])] = z^2982
thc2[idx([0,0,1,0])] = z^1554
thc2[idx([0,0,0,1])] = F(70)
thc2[idx([1,0,0,0])] = F(41)
thc2[idx([1,0,0,1])] = F(76)
thc2[idx([0,1,0,0])] = F(65)
thc2[idx([1,1,0,0])] = F(12)
thc2[idx([0,1,1,0])] = z^1218
thc2[idx([1,1,1,1])] = z^3066
#If we indicate the original curve, then we can create point from points 
#of the Jacobian directly
thc2 = AnalyticThetaNullPoint(F, 2, g, thc2, curve=C, wp=a)


# Point from a Mumford divisor
u = (x-43)*(x-10)
v = (z^954*x + z^2518)
D = J([u,v])
th2D = thc2(D)


# From the theta constant values

th2 = [0]*(2**(2*g))
th2[idx([0,0,0,0])] = z^3608
th2[idx([0,0,1,1])] = z^5026
th2[idx([0,0,1,0])] = z^1654
th2[idx([0,0,0,1])] = z^6408
th2[idx([1,0,0,0])] = z^5576
th2[idx([1,0,0,1])] = z^3952
th2[idx([0,1,0,0])] = z^734
th2[idx([1,1,0,0])] = z^2674
th2[idx([0,1,1,0])] = z^3262
th2[idx([1,1,1,1])] = z^5436
th2[idx([0,1,0,1])] = F(82)
th2[idx([0,1,1,1])] = z^6258
th2[idx([1,0,1,0])] = z^4746
th2[idx([1,1,1,0])] = z^798
th2[idx([1,0,1,1])] = z^5082
th2[idx([1,1,0,1])] = F(2)
th2 = thc2(th2)

#TODO create comparison function for analytic classes
assert th2._coords == th2D._coords

#The reverse functionality
#TODO create as method of analytic classes
from avisogenies_sage.morphisms_level2 import Level2ThetaPointToMumford
uth,v2th = Level2ThetaPointToMumford(a, th2)
assert D == J([uth, sqrt(v2th)])


#***** Change of coordinates *****/

# The theta structure used in the morphisms' module is not the same as in the other
# modules of the package. The following functions act as conversion between the two.

# Let thc2 and th2 be the analytic theta constants and functions in level 2 
# given previously. We convert them to the classical representation.
n = 2 # the level is 2
P0 = thc2.to_algebraic()
#There is an optional parameter to give the algebraic representation of the theta constant.
P = th2.to_algebraic(P0)
#If it is not given, then it is computed internally
P = th2.to_algebraic()

# Let P0 and self be the theta constants and functions in level 2. We convert them
# in the analytic representation used in the morphisms module
thc2 = AnalyticThetaNullPoint.from_algebraic(P0)
#As in the opposite conversion, there is an optional parameter to give the analytic representation of the theta constant.
th2 = thc2(P)
#If it is not given, then it is computed internally
#from avisogenies_sage.analytic_theta_point import AnalyticThetaPoint
from avisogenies_sage.analytic_theta_point import AnalyticThetaPoint
th2 = AnalyticThetaPoint.from_algebraic(P)
