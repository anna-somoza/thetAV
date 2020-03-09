// AttachSpec("src/AVI.spec");
SetVerbose("AVIsogenies",4);

/* First an easy test ex 1*/

p:=271; F:=GF(p);  CI:=[F| 74, 36, 53, 155 ];
H:=HyperellipticCurveFromIgusaClebsch(CI);
J:=Jacobian(H);  
time r:=Genus2IsogenyGraph(J,[3]);
assert #Keys(r) eq 135;

/***** An interesting curve ex 2*****/

/*
The following curve is interesting. When we compute 7 isogenies from it, we often use some particular cases of the morphisms. For instance, we need to send some Theta divisor from the Mumford's coordinate to Theta coordinates.
*/

F:=GF(41);  FF<x>:=PolynomialRing(F);
f:=11*x^6 + 3*x^5 + 25*x^4 + 34*x^3 + 29*x^2 + 36*x + 19;      
J:=Jacobian(HyperellipticCurve(f));

time r:=Genus2IsogenyGraph(J,[7]);
assert #Keys(r) eq 8;
