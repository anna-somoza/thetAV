/************************* LAYOUT OF THE FILE ******************************/   
/***** In level 4
/***** In level 2
/***** Change of coordinates
/**************************************************************************/
/**************************************************************************/

/***** In level 4 *****/

// First we define the curve and its Jacobian
//
// A curve y^2=f(x) is defined by a list "a" containing the roots of f(x); it
// is important that f be of odd degree and "a" be ordered (the Theta constants
// depend on this ordering).

F:=GF(83^2);
Fx<X>:=PolynomialRing(F);

g:=2;
a:=[F!0,1,3,15,20]; // the roots of f

// For instance, on may recover f(x) as follows:
//
//f:=&*[X-a[x] : x in {1..(2*g+1)}];
//C:=HyperellipticCurve(f); 

// We need to fix a square root (might live in an extension of degree two).
rac:=Sqrt(a[2]-a[1]);

// The Theta constants of the Jacobian.
Ab:=AbelianGroup([2 : x in [1..2*g]]);
thc := AnalyticThetaNullPoint(4,AssociativeArray(Ab),Ab,2 : level2 := false);
thc`coord[Ab![0,0,0,0]]:=F!1;
thc`coord[Ab![0,0,1,1]]:=F.1^1491;
thc`coord[Ab![0,0,1,0]]:=F.1^777;
thc`coord[Ab![0,0,0,1]]:=F!30;
thc`coord[Ab![1,0,0,0]]:=F!37;
thc`coord[Ab![1,0,0,1]]:=F.1^2058;
thc`coord[Ab![0,1,0,0]]:=F!56;
thc`coord[Ab![1,1,0,0]]:=F!57;
thc`coord[Ab![0,1,1,0]]:=F.1^609;
thc`coord[Ab![1,1,1,1]]:=F.1^1533;
thc`coord[Ab![0,1,0,1]]:=F!0;
thc`coord[Ab![0,1,1,1]]:=F!0;
thc`coord[Ab![1,0,1,0]]:=F!0;
thc`coord[Ab![1,1,1,0]]:=F!0;
thc`coord[Ab![1,0,1,1]]:=F!0;
thc`coord[Ab![1,1,0,1]]:=F!0;

// Now let's map some points between Mumford and Theta representation.

// Consider the Mumford divisor defined by:
u:=(X-43)*(X-10); v:=F.1^954*X + F.1^2518;
// The function takes as input the support of the divisor, which we compute now:
points:={* [x[1],Evaluate(v,x[1])]^^x[2] : x in RootsInSplittingField(u) *};
points:=[ x : x in points];
th := MumfordToLevel4ThetaPoint(g, a, rac, thc, [p : p in points]); // returns the corresponding Theta functions

// Conversely, define the Theta functions
th := AnalyticThetaPoint(4,AssociativeArray(Ab),Ab);
th`coord[Ab![0,0,0,0]]:=F.1^1755;
th`coord[Ab![0,0,1,1]]:=F.1^1179;
th`coord[Ab![0,0,1,0]]:=F.1^977;
th`coord[Ab![0,0,0,1]]:=F.1^1105;
th`coord[Ab![1,0,0,0]]:=F.1^352;
th`coord[Ab![1,0,0,1]]:=F.1^1674;
th`coord[Ab![0,1,0,0]]:=F.1^2523;
th`coord[Ab![1,1,0,0]]:=F.1^5890;
th`coord[Ab![0,1,1,0]]:=F.1^5051;
th`coord[Ab![1,1,1,1]]:=F.1^5243;
th`coord[Ab![0,1,0,1]]:=F.1^4021;
th`coord[Ab![0,1,1,1]]:=F.1^4716;
th`coord[Ab![1,0,1,0]]:=F.1^139;
th`coord[Ab![1,1,1,0]]:=F.1^507;
th`coord[Ab![1,0,1,1]]:=F.1^2832;
th`coord[Ab![1,1,0,1]]:=F.1^3382;
u,v := Level4ThetaPointToMumford(g, a, rac, thc, th); // returns the corresponding Mumford polynomials


/***** In level 2 *****/


// First we define the curve and its Kummer surface
//
// A curve y^2=f(x) is defined by a list "a" containing the roots of f(x); it
// is important that f be of odd degree and "a" be ordered (the Theta constants
// depend on this ordering).
// First defined the curve and the Kummer Surface
F:=GF(83^2);
Fx<X>:=PolynomialRing(F);

g:=2;
a:=[F!0,1,3,15,20]; // the roots of f

// For instance, on may recover f(x) as follows:
//
//f:=&*[X-a[x] : x in {1..(2*g+1)}];
//C:=HyperellipticCurve(f); 

// The Theta constants of the Kummer surface.
Ab:=AbelianGroup([2 : x in [1..2*g]]);
thc2 := AnalyticThetaNullPoint(2,AssociativeArray(Ab),Ab,2 : level2:=true);
thc2`coord[Ab![0,0,0,0]]:=F!1;
thc2`coord[Ab![0,0,1,1]]:=F.1^2982;
thc2`coord[Ab![0,0,1,0]]:=F.1^1554;
thc2`coord[Ab![0,0,0,1]]:=F!70;
thc2`coord[Ab![1,0,0,0]]:=F!41;
thc2`coord[Ab![1,0,0,1]]:=F!76;
thc2`coord[Ab![0,1,0,0]]:=F!65;
thc2`coord[Ab![1,1,0,0]]:=F!12;
thc2`coord[Ab![0,1,1,0]]:=F.1^1218;
thc2`coord[Ab![1,1,1,1]]:=F.1^3066;
thc2`coord[Ab![0,1,0,1]]:=F!0;
thc2`coord[Ab![0,1,1,1]]:=F!0;
thc2`coord[Ab![1,0,1,0]]:=F!0;
thc2`coord[Ab![1,1,1,0]]:=F!0;
thc2`coord[Ab![1,0,1,1]]:=F!0;
thc2`coord[Ab![1,1,0,1]]:=F!0;


// Now let's map some points between Mumford and Theta representation.


// Consider the Mumford divisor defined by:
u:=(X-43)*(X-10); v2:=(F.1^954*X + F.1^2518)^2;
// The function takes as input the support of the divisor, which we compute now:
points:=[[F!43,8],[10,F.1^2982]]; // the points in the support of the divisor
// Note that we could have used points:=[[43,-8],[10,-F.1^2982]];
th2:= MumfordToLevel2ThetaPoint(g, a, thc2, points); // returns the corresponding Theta functions



// Conversely, define the Theta functions

th2 := AnalyticThetaPoint(2,AssociativeArray(Ab),Ab);
th2`coord[Ab![0,0,0,0]]:=F.1^3608;
th2`coord[Ab![0,0,1,1]]:=F.1^5026;
th2`coord[Ab![0,0,1,0]]:=F.1^1654;
th2`coord[Ab![0,0,0,1]]:=F.1^6408;
th2`coord[Ab![1,0,0,0]]:=F.1^5576;
th2`coord[Ab![1,0,0,1]]:=F.1^3952;
th2`coord[Ab![0,1,0,0]]:=F.1^734;
th2`coord[Ab![1,1,0,0]]:=F.1^2674;
th2`coord[Ab![0,1,1,0]]:=F.1^3262;
th2`coord[Ab![1,1,1,1]]:=F.1^5436;
th2`coord[Ab![0,1,0,1]]:=F!82;
th2`coord[Ab![0,1,1,1]]:=F.1^6258;
th2`coord[Ab![1,0,1,0]]:=F.1^4746;
th2`coord[Ab![1,1,1,0]]:=F.1^798;
th2`coord[Ab![1,0,1,1]]:=F.1^5082;
th2`coord[Ab![1,1,0,1]]:=F!2;
u,v2 := Level2ThetaPointToMumford(g, a, thc2, th2);// returns the corresponding Mumford polynomials (u,v^2)


/***** Change of coordinates *****/

// The theta coordinates used in morphismes.m are not the same as in the other 
// files. The following functions convert the coordinates.
// The level (2 or 4) is not specified by the user. However there are two 
// different functions depending whether we want to convert a point or a theta 
// null point


// Let thc2 and th2 be the analytic theta constants and functions in level 2 
// given previously. We convert them in the classical representation.
n:=2; // the level is 2
A:=AbelianGroup([n : x in [1..g]]); // we must fixed this otherwise magma would used different groups. 
P0:=AnalyticToAlgebraicThetaNullPoint(g,thc2,A);
P:=AnalyticToAlgebraicThetaPoint(g,th2,A);


// Let P0 and P be the theta constants and functions in level 2. We convert them
// in the analytic representation used in 
// morphismes.m
Ab:=AbelianGroup([2 : x in [1..2*g]]); // we must fix this otherwise magma would used different groups.
thc2 := AlgebraicToAnalyticThetaNullPoint(g,P0,Ab);
th2 := AlgebraicToAnalyticThetaPoint(g,P0,P,Ab);

