#************************* LAYOUT OF THE FILE ******************************/   
#***** In level 4
#***** In level 2
#***** Change of coordinates
#**************************************************************************/
#**************************************************************************/

#***** In level 4 *****/

# First we define the curve and its Jacobian
#
# A curve y^2=f(x) is defined by a list "a" containing the roots of f(x); it
# is important that f be of odd degree and "a" be ordered (the Theta constants
# depend on this ordering).
from avisogenies_sage import *

F = GF(83^2)
z, = F.gens()
Fx.<X> = PolynomialRing(F)

g = 2
a = [F(0), 1, 3, 15, 20] # the roots of f

# For instance, on may recover f(x) as follows:
#
#f = prod(X - al for al in a)
#C = HyperellipticCurve(f)

# We need to fix a square root (might live in an extension of degree two).
rac = sqrt(a[1]-a[0])

# The Theta constants of the Jacobian.
thc = [0]*(2**(2*g))
idx = lambda x : ZZ(x, 2)
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
thc[idx([0,1,0,1])]=F(0)
thc[idx([0,1,1,1])]=F(0)
thc[idx([1,0,1,0])]=F(0)
thc[idx([1,1,1,0])]=F(0)
thc[idx([1,0,1,1])]=F(0)
thc[idx([1,1,0,1])]=F(0)
thc = ThetaNullPoint_Analytic(4, thc, g)

# Now let's map some points between Mumford and Theta representation.

# Consider the Mumford divisor defined by:
u=(X-43)*(X-10)
v=z^954*X + z^2518

# The function takes as input the support of the divisor, which we compute now:
points = sum(([(x, v(x))]*mult for x, mult in u.roots(u.splitting_field('z'))), [])
th = MumfordToLevel4ThetaPoint(a, rac, thc, points) # returns the corresponding Theta functions

# Conversely, define the Theta functions
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
u,v = Level4ThetaPointToMumford(a, rac, th) # returns the corresponding Mumford polynomials


#***** In level 2 *****/

from avisogenies_sage import *

# First we define the curve and its Kummer surface
#
# A curve y^2=f(x) is defined by a list "a" containing the roots of f(x); it
# is important that f be of odd degree and "a" be ordered (the Theta constants
# depend on this ordering).
# First defined the curve and the Kummer Surface
F = GF(83^2)
z, = F.gens()
Fx.<X> = PolynomialRing(F)

g = 2
a = [F(el) for el in [0,1,3,15,20]] # the roots of f

# For instance, on may recover f(x) as follows:
#
#f = prod(X - al for al in a)
#C = HyperellipticCurve(f)

# The Theta constants of the Kummer surface.
thc2 = [0]*(2**(2*g))
idx = lambda x : ZZ(x, 2)
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
thc2[idx([0,1,0,1])] = F(0)
thc2[idx([0,1,1,1])] = F(0)
thc2[idx([1,0,1,0])] = F(0)
thc2[idx([1,1,1,0])] = F(0)
thc2[idx([1,0,1,1])] = F(0)
thc2[idx([1,1,0,1])] = F(0)
thc2 = ThetaNullPoint_Analytic(2, thc2, g)


# Now let's map some points between Mumford and Theta representation.


# Consider the Mumford divisor defined by:
u = (X-43)*(X-10)
v2 = (z^954*X + z^2518)^2
# The function takes as input the support of the divisor, which we compute now:
points = [(F(43),F(8)),(F(10),z^2982)] # the points in the support of the divisor
# Note that we could have used points = [[43,-8],[10,-z^2982]]
th2_S =  MumfordToLevel2ThetaPoint(a, thc2, points) # returns the corresponding Theta functions



# Conversely, define the Theta functions

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
u_S,v2_S = Level2ThetaPointToMumford(a, th2)# returns the corresponding Mumford polynomials (u,v^2)


#***** Change of coordinates *****/

# The theta structure used in the morphisms module is not the same as in the other 
# modules of the package. The following functions act as conversion between the two.

# Let thc2 and th2 be the analytic theta constants and functions in level 2 
# given previously. We convert them to the classical representation.
n = 2 # the level is 2
P0 = thc2.to_algebraic()
#There is an optional parameter to give the algebraic representation of the theta constant.
P = th2.to_algebraic(P0)
#If it is not given, then it is computed internally
P = th2.to_algebraic()

# Let P0 and P be the theta constants and functions in level 2. We convert them
# in the analytic representation used in the morphisms module
thc2 = AlgebraicToAnalyticThetaNullPoint(P0)
#As in the oposite conversion, there is an optional parameter to give the analytic representation of the theta constant.
th2 = AlgebraicToAnalyticThetaPoint(P0, thc2)
#If it is not given, then it is computed internally
th2 = AlgebraicToAnalyticThetaPoint(P0)
