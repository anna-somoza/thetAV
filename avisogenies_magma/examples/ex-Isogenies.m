// vim: set foldmethod=marker filetype=magma nocindent indentexpr= :

F<t>:=GF(3,6);
A<x>:=PolynomialRing(F);
f:= t^254 * x^6 + t^223 * x^5 + t^255 * x^4 + t^318 * x^3 + t^668 * x^2 + t^543 *  x + t^538; 
l:=7;
H:=HyperellipticCurve(f);
J:=Jacobian(H);

//The isogenies 
SetVerbose("AVIsogenies",4);
time r:=RationallyIsogenousCurvesG2(H,l);

SetVerbose("AVIsogenies",1);
time isograph,jacobians:=Genus2IsogenyGraph(J,[l]);

// Only the subgroups 
SetVerbose("AVIsogenies",4);
time R,Rgroup,precomp := RationalSymplecticTorsionSubgroups(J,l);

// Isogeny from a kernel
precomp["subgroups"]:=[R[1]]; // Set the kernel for the Isogeny to one of the possible subgroups (computed from RationalSymplecticTorsionSubgroups)
Remove(~precomp,"thetasubgroups"); // Remove some precomputations done for the other subgroups
time RationallyIsogenousCurvesG2(H,l:precomp:=precomp);

// Isogeny from a kernel 2
// Suppose that you have a kernel K obtained from somewhere else:
K:=R[1]; //the kernel whose isogeny we want to compute, given by two generators
         //here we take the previous kernel again, but this could be any
         //kernel given in Mumford coordinates

import "src/Arithmetic.m" : precompute_D;
import "src/Isogenies.m" : precompute_isogenies;
//warning: the import lines assume that we are in the avisogenies repository. Adapt the filenames otherwise
precomp:=AssociativeArray();
D:=AbelianGroup([2,2]);
//we have to do the following initialisations, this should probably be checked in RationallyIsogenousCurvesG2 so that we don't have to do this anymore...
precompute_D(D,~precomp);
precompute_isogenies(D,l,~precomp);
precomp["frob"]:=FrobeniusPoly(H);
precomp["subgroups"]:=[K];
time RationallyIsogenousCurvesG2(H,l:precomp:=precomp);

// Isogeny from a kernel 3
import "src/Isogenies.m" : precompute_isogenies;
// Suppose that you have a kernel K obtained directly in theta coordinate
K:=precomp["thetasubgroups"][1]; // This is just a convenient way to get a kernel in theta coordinates, in practice this would be supplied by the user
Dl:=Universe(K);
theta0:=K[Dl.0];
P0, precomp:=init_theta_null_point(theta0);
D:=precomp["D", "D"];
precompute_isogenies(D,l,~precomp);
IsogenieG2Theta(K,precomp: precomp_power:=true); //Only output the isogenous theta null point, not the curve

// From scratch. This is easily adapted for any genus.
  import "src/Arithmetic.m" : init_theta_null_point, init_theta_point, print_point;
  import "src/Isogenies.m" : precompute_isogenies, Isogenie;

  l:=3; g:=2; n:=2; // Or n:=4;
  // K should be [theta null point, theta coordinates of P, theta coordinates of Q, theta coordinates of P+Q]; where the theta coordinates should be a sequence respecting the numbering of Dg or an associative array indexed by Dg
  Dg:=AbelianGroup([n: i in [1..g]]);
  Dl:=AbelianGroup([l: i in [1..g]]);

  L:=AssociativeArray();
  precomp:=AssociativeArray();
  precompute_isogenies(Dg,l,~precomp);

  "- compute theta coordinates of points in K";
  P0:=init_theta_null_point(K[1]: numbering:= Dg);
  L[Dl.0]:=P0;
  for i in [1..g] do
    L[Dl.i]:=init_theta_point(K[i+1]: numbering:= Dg);
  end for;
  for i in [1..g-1] do
    for j in [i+1..g] do
      // Note: adjust for g>2
      L[Dl.i+Dl.j]:=init_theta_point(K[i+j+1]: numbering:= Dg);
    end for;
  end for;
  "- computing the isogeny";
  r,ltors:=Isogenie(L,precomp);
  print_point(r);

/************ For caracteristic 2, ordinary curve **********/
// Same as before //

F<t>:=GF(2,9);
A<x>:=PolynomialRing(F);
h := t^313*x^2 + t^347*x + t^106;
f := t^104*x^5 + t^351*x^4 + t^423*x^3 + t^405*x^2 + t^437*x + t^89;

l:=5;
H:=HyperellipticCurve(f,h);
J:=Jacobian(H);


//The isogenies 
SetVerbose("AVIsogenies",4);
time r:=RationallyIsogenousCurvesG2(H,l);

SetVerbose("AVIsogenies",1);
time isograph,jacobians:=Genus2IsogenyGraph(J,[l]);


// Only the subgroups. The options are because in carac 2 we can't be as clever.
SetVerbose("AVIsogenies",4);
time R,Rgroup,precomp := RationalSymplecticTorsionSubgroups(J,l: theta:=0,only_mumford:=true); 


// Isogeny from a kernel
precomp["subgroups"]:=[R[1]]; // Set the kernel for the Isogeny to one of the possible subgroups
Remove(~precomp,"thetasubgroups"); // Remove some precomputations done for the other subgroups
time RationallyIsogenousCurvesG2(H,l:precomp:=precomp);
