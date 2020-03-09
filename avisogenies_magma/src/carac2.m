/*
This file contains fonctions for isogenies computation in caracteristic 2.
We assume the curve to be ordinary and the level of theta function to be 2.

- Romain Cosset

For now it work only for genus 2 curves but some functions can be used also for
genus 1 (it lacks functions to convert from Weierstrass equation to "Rosenhain"
equation.
The arithmetic functions can be used in all dimension for level 2 coordinates.


See the two articles
  Gaudy, Lubicz
  Cosset, Robert
for references. //TODO les citer
 */

import "libav.m" : SumOfSquares,GetCastMinField,ConstructOverfield;





//****  Structure ****//

ThetaPoint_carac2:= recformat<
  coord,
  inv_coord, // the inverse coordinates
  numbering,

  lvl,
  g
>;

ThetaNullPoint_carac2:= recformat<
  coord,
  numbering, //the numbering map
  inv_coord,

  lvl,
  g,

  jacobian,
  curve
>;

/*
The zero of the abelian variety
 */
function ZeroPoint(lvl,g,numbering)
  if lvl ne 2 then error "Only implemented for level 2"; end if;

  R:=rec< ThetaPoint_carac2 | numbering:=numbering,
                              coord:=AssociativeArray(numbering),
                              lvl:=lvl,
                              g:=g >;
  for a in numbering do
    R`coord[a]:=0;
  end for;
  R`coord[numbering!0]:=1;

  return R;
end function;

/*
Check whether two ThetaPoints are equal or not.
We assume that the coordinates are projective and if the two points are equal
we return as a second argument the rapport Q/P
*/
function ComparePoints(P,Q)
  A:=P`numbering;

  c:={};
  for k in A do
    if P`coord[k] eq 0 and not Q`coord[k] eq 0 then
      return false,_;
    elif not P`coord[k] eq 0 and not Q`coord[k] eq 0 then
      c:=c join {Q`coord[k]/P`coord[k]};
    end if;
  end for;
  if #c eq 1 then return true,Rep(c); else return false,_; end if;
end function;

function IsZeroPoint(P)
  A:=P`numbering;
  return &and[IsZero(P`coord[a]) : a in A | a ne A!0 ];
end function;


/*
Cast the coordinates of P into the field F
P :: ThetaPoint_carac2 or ThetaNullPoint_carac2
F ::
 */
function CastCoordinates(P,F)
  newP:=P;
  A:=P`numbering;

  for a in A do newP`coord[a]:=F!P`coord[a]; end for;

  if assigned P`inv_coord then
    for a in A do newP`inv_coord[a]:=F!P`inv_coord[a]; end for;
  end if;

  return newP;
end function;




//**** Arithmetic ****//


/*
Compute 2P
point0 is the theta constants, not the zero of the variety.

TODO work only for level 2
TODO I'm sure it is correct in genus 1 and 2.
     Is it still the case in greater genus?
 */
function Doubling(P,point0)
  A:=P`numbering;

  R:=rec< ThetaPoint_carac2 | numbering:=A,
                              coord:=AssociativeArray(A),
                              lvl:=P`lvl,
                              g:=P`g >;

  R`coord[A!0]:=&+[P`coord[a]^4 : a in A];

  for b in A do
  if b ne A!0 then
    R`coord[b]:=0;
    set:={};
    for a in A do
    if a notin set then
      set:=set join {a,a+b};
      R`coord[b]+:=P`coord[a]*P`coord[a+b];
    end if;
    end for;
    R`coord[b]:=R`coord[b]^2 * point0`inv_coord[b];
  end if;
  end for;

  return R;
end function;

/*
Compute P+Q from P,Q and P-Q
Work if one (or more) coordinates of P-Q are zero.

TODO work only for level 2
TODO I'm sure it is correct in genus 1 and 2.
     Is it still the case in greater genus?
 */
function AddDiff_gen(P,Q,PmQ,point0)
  A:=P`numbering;
  F:=Parent(P`coord[A!0]);

  R:=rec< ThetaPoint_carac2 | numbering:=A,
                              coord:=AssociativeArray(A),
                              lvl:=P`lvl,
                              g:=P`g >;


  kbb_p:=AssociativeArray(A);
  for b in A do
    kbb_p[b]:=0;
    for a in A do
      kbb_p[b]+:=P`coord[a]*Q`coord[a+b];
    end for;
    kbb_p[b]:=kbb_p[b]^2;
  end for;

  if &and[kbb_p[b] eq 0 : b in A] then
    b0:=[b : b in A | PmQ`coord[b] ne 0][1];
    R`coord[b0]:=F!0;

    for b in A do
    if b ne b0 then
      kbb0:=0;
      set:={};
      for a in A do
      if a notin set then
        set:=set join {a,a+b+b0};
        kbb0+:=P`coord[b+b0+a]*P`coord[a]*Q`coord[b+b0+a]*Q`coord[a];
      end if;
      end for;
      kbb0*:=point0`inv_coord[b+b0];

      R`coord[b]:=kbb0/PmQ`coord[b0];
    end if;
    end for;

  else
    b0:=[b : b in A | kbb_p[b] ne 0][1];
    R`coord[b0]:= kbb_p[b0] / PmQ`coord[b0] ;

    for b in A do
    if b ne b0 then
      kbb0:=0;
      set:={};
      for a in A do
      if a notin set then
        set:=set join {a,a+b+b0};
        kbb0+:=P`coord[b+b0+a]*P`coord[a]*Q`coord[b+b0+a]*Q`coord[a];
      end if;
      end for;
      kbb0*:=point0`inv_coord[b+b0];

      R`coord[b]:=( kbb0/kbb_p[b0] - PmQ`coord[b]/PmQ`coord[b0]) * R`coord[b0];
    end if;
    end for;
  end if;
  return R;
end function;

/*
Compute P+Q from P,Q and P-Q
Work if the coordinate of P-Q are non zero (in particular it doesn't work if P-Q
is a 2 torsion point)

TODO work only for level 2
TODO I'm sure it is correct in genus 1 and 2.
     Is it still the case in greater genus?
 */
function AddDiff(P,Q,PmQ,point0)
  A:=P`numbering;

  if IsZeroPoint(PmQ) then
    return Doubling(P,point0);
  end if;


  R:=rec< ThetaPoint_carac2 | numbering:=A,
                              coord:=AssociativeArray(A),
                              lvl:=P`lvl,
                              g:=P`g >;

  if not assigned PmQ`inv_coord then
    if &or[PmQ`coord[b] eq 0 : b in A] then
      return AddDiff_gen(P,Q,PmQ,point0);
    end if;
    PmQ`inv_coord:=AssociativeArray(A);
    for b in A do PmQ`inv_coord[b]:=1/PmQ`coord[b]; end for;
  end if;

  for b in A do
    R`coord[b]:=0;
    for a in A do
      R`coord[b]+:=P`coord[a]*Q`coord[a+b];
    end for;
    R`coord[b]:=R`coord[b]^2;
    R`coord[b]*:= PmQ`inv_coord[b];
  end for;

  return R;
end function;


/*
Compute k*P
 */
function Diff_Mult(k,P,point0)
  if k eq 0 then return ZeroPoint(P`lvl,P`g,P`numbering); end if;
  if k lt 0 then k:=-k; end if;
  if k eq 1 then return P; end if;
  if k eq 2 then return Doubling(P,point0); end if;

  if not assigned P`inv_coord then
  if &and[P`coord[b] ne 0 : b in P`numbering] then
    P`inv_coord:=AssociativeArray(P`numbering);
    for a in P`numbering do
      P`inv_coord[a]:=1/P`coord[a];
    end for;
  end if;
  end if;

  kb := Reverse(IntegerToSequence(k,2));
  Pm:=P;
  Pp:=Doubling(P,point0);
  for i := 2 to #kb do
    Q:=AddDiff(Pp,Pm,P,point0);
    if kb[i] eq 1 then
      Pp:=Doubling(Pp,point0);
      Pm:=Q;
    else
      Pm:=Doubling(Pm,point0);
      Pp:=Q;
    end if;
  end for;

  return Pm;
end function;

/*
compute kP+Q
 */
function Diff_Mult_Add(k,P,PpQ,Q,point0)
  if k eq 0 then return Q; end if;

  if k lt 0 then
    PmQ:=AddDiff(P,Q,PpQ,point0);
    return Diff_Mult_Add(-k,P,PmQ,Q,point0);
  end if;

  if k eq 1 then return PpQ; end if;
  if k eq 2 then return AddDiff(PpQ,P,Q,point0); end if;

  if not assigned Q`inv_coord then
    Q`inv_coord:=AssociativeArray(Q`numbering);
    for a in Q`numbering do
      if Q`coord[a] eq 0 then error "Q`coord[a] eq 0, not yet implemented"; end if;
      Q`inv_coord[a]:=1/Q`coord[a];
    end for;
  end if;
  if not assigned PpQ`inv_coord then
    PpQ`inv_coord:=AssociativeArray(PpQ`numbering);
    for a in PpQ`numbering do
      if PpQ`coord[a] eq 0 then error "PpQ`coord[a] eq 0, not yet implemented"; end if;
      PpQ`inv_coord[a]:=1/PpQ`coord[a];
    end for;
  end if;

  kb := Reverse(IntegerToSequence(k,2));
  PpQm:=PpQ;
  PpQp:=AddDiff(PpQ,P,Q,point0);
  Pm:=P;
  Pp:=Doubling(P,point0);
  for i := 2 to #kb do
    R:=AddDiff(Pp,Pm,P,point0);
    if kb[i] eq 1 then
      PpQm:=AddDiff(PpQp,Pm,PpQ,point0);
      PpQp:=AddDiff(PpQp,Pp,Q,point0);
      Pp:=Doubling(Pp,point0);
      Pm:=R;
    else
      PpQm:=AddDiff(PpQm,Pm,Q,point0);
      PpQp:=AddDiff(PpQp,Pm,PpQ,point0);
      Pm:=Doubling(Pm,point0);
      Pp:=R;
    end if;
  end for;

  return PpQm;
end function;




//**** Arithmetic: module ****//


/*
Let ell an odd number
Let e=[e1,e2,e1+e2] be points of ell-torsion
Let P be another point and Pe=[P+e1,P+e2];

compute P+e1+e2
 */
function ExpandSBasis(e,P,Pe,ell,point0)
  Q:=Diff_Mult_Add(ell-1,e[2],Pe[2],P,point0); // P-e2
  R:=AddDiff(Pe[1],e[3],Q,point0); // P+2e1+e2
  E:=Doubling(e[1],point0); //2e1

  Q:=Diff_Mult_Add((ell+1) div 2,E,R,Pe[2],point0);
  return Q;
end function;

/*
Le e be a basis that generate a module E
Let z be a point. We want to compute z+E.

this function work for #e equal 1 or 2

Assume that we know the points z + sum(ep_i e_i) where ep_i in {0,1}


Let B be the group AbelianGroup([ell : i in [1..#e]])
The module E and z+E are indexed by B
*/
function AffineModule(e,ZE,B,point0)
  ell:=Invariants(B);
  r:=#ell;

  if r gt 2 then error "Not yet implemented"; end if;

  for i in [2..(ell[1]-1)] do
    ZE[i*B.1]:=AddDiff(ZE[(i-1)*B.1],e[1],ZE[(i-2)*B.1],point0);
  end for;

  if r eq 2 then
    for i in [2..(ell[1]-1)] do
      ZE[i*B.1+B.2]:=AddDiff(ZE[(i-1)*B.1+B.2],e[1],ZE[(i-2)*B.1+B.2],point0);
    end for;
    for j in [2..(ell[2]-1)] do
    for i in [0..(ell[1]-1)] do
      ZE[i*B.1+j*B.2]:=AddDiff(ZE[i*B.1+(j-1)*B.2],e[2],
                               ZE[i*B.1+(j-2)*B.2],point0);
    end for;
    end for;
  end if;

  return ZE;
end function;



/*
assume that ell P =0 and we know the coordinates up to a projective factor la_P

return ( la_P / la_0 )^ell
 */
function ProjFact_ell(ell,P,point0)
  lp:=ell div 2;
  Pp:=Diff_Mult(lp+1,P,point0);
  Pm:=Diff_Mult(-lp,P,point0);

  test,f:=ComparePoints(Pm,Pp);

  if not test then error "error: ell*P should be equal to zero"; end if;
  return f;
end function;

/*
assume that ell P =0 and we know the coordinates up to a projective factor

return ( la_{P+Q} / la_Q )^ell
*/
function ProjFact_ellQ(ell,P,PpQ,Q,point0)
  f:=ProjFact_ell(ell,P,point0);

  R:=Diff_Mult_Add(ell,P,PpQ,Q,point0);
  test,g:=ComparePoints(Q,R);

  if not test then error "error: ell*P should be equal to zero, PpQ should be P+Q"; end if;
  return g/f^(ell-1);
end function;


/*
For genus 1 and 2.
Let a be a positive integer. t=[b] or [b,c] idem
Compute the projectives factors for a*z+b e1 +c e2 with ell*e_i =0

We assume that the computation is done using ExpandSBasis and AffineModule.
If these functions are changed, check if this is still correct.
 */
function power_proj_factor(a,t,ell,B)
  la:=AssociativeArray(B);
  mu:=AssociativeArray(B);

  if #t eq 1 then
    la[B.1]:=t[1]*(t[1]-a);
    mu[B.1]:=a*t[1];
  elif #t eq 2 then
    b:=t[1]; c:=t[2];


    la[B.1]:=(ell^2-1);
    la[B.2]:= -(ell^2-1)*(ell-2)  div 2;
    la[B.1+B.2]:=(ell+1);
    mu[B.1]:=(ell+1);
    mu[B.2]:=-(ell^2+ell-2)  div 2;

    la[B.1]     *:= a*b*c;
    la[B.2]     *:= a*b*c;
    la[B.1+B.2] *:= a*b*c;
    mu[B.1]     *:= a*b*c;
    mu[B.2]     *:= a*b*c;


    la[B.1]+:=b*(b-a-c+a*c);
    la[B.2]+:=c*(c-a-b+a*b);
    mu[B.1]-:=a*b*(c-1);
    mu[B.2]-:=a*c*(b-1);
    la[B.1+B.2]-:=b*c*(a-1);
  else
    error "Not yet implemented";
  end if;

  return la,mu;
end function;




//**** Isogeny computation between abelian varieties ****//

/*
Let z be a point on a variety A.
Let e be a S-basis of a maximal simpletic subgroup of the ell-torsion.
The S-basis is indexed by B=(Z/2Z)^g
Let ze be the points z and z+e_i, also indexed by B.

Compute the image of z by the ell-isogeny associated to this subgroup
This function is similar to the odd characteristic case.

work for genus 1 and 2
 */
function Isogeny(ell,e,B,ze,point0)
  // assert IsPrime(ell); 
  assert ell ne 2;

  s:=SumOfSquares(ell);
  assert #s eq 2 or #s eq 4;

  if #s eq 2 then
    F:=Matrix(Integers(),2,2,[ [s[1],-s[2]],
                                [s[2], s[1]] ]);
    Fe:=Matrix(Integers(ell),2,2,[ [s[1],-s[2]],
                                   [s[2], s[1]] ]);
  else
    F:=Matrix(Integers(),4,4,[ [s[1],-s[2],-s[3],-s[4]],
                                [s[2], s[1],-s[4], s[3]],
                                [s[3], s[4], s[1],-s[2]],
                                [s[4],-s[3], s[2], s[1]] ]);
    Fe:=Matrix(Integers(ell),4,4,[ [s[1],-s[2],-s[3],-s[4]],
                                   [s[2], s[1],-s[4], s[3]],
                                   [s[3], s[4], s[1],-s[2]],
                                   [s[4],-s[3], s[2], s[1]] ]);
  end if;

  g:=ze[B!0]`g; assert g eq #Invariants(B);
  if g gt 3 then error "Not yet implemented"; end if;

  n:=ze[B!0]`lvl;
  if n ne 2 then error "Not yet implemented"; end if;

// compute ell-power of the projective factors for the S-basis
  la:=AssociativeArray(B);
  mu:=AssociativeArray(B);

  for b in B do if b ne B!0 then
    la[b]:=ProjFact_ell(ell,e[b],point0);
  end if; end for;
  for i in [1..g] do
    mu[B.i]:=ProjFact_ellQ(ell,e[B.i],ze[B.i],ze[B!0],point0);
  end for;

// compute z+e1+e2 if needed
  if g ge 2 then
    ze[B.1+B.2]:=ExpandSBasis([e[B.1],e[B.2],e[B.1+B.2]],ze[B!0],
                                [ze[B.1],ze[B.2]],ell,point0);
  end if;


  D:=AbelianGroup([ell : i in [1..g]]);


// compute the module
  M:=[];
  for k in s do
    kZE:=AssociativeArray(D);
    kZE[D!0]:=Diff_Mult(k,ze[B!0],point0);
    for i in [1..g] do
      kZE[D.i]:=Diff_Mult_Add(k,ze[B!0],ze[B.i],e[B.i],point0);
    end for;
    if g ge 2 then // FIXME for g gt 2
      kZE[D.1+D.2]:=Diff_Mult_Add(k,ze[B!0],ze[B.1+B.2],e[B.1+B.2],point0);
    end if;

    M:=M cat [AffineModule([e[B.i] : i in [1..g]],kZE,D,point0)];
  end for;


  A:=ze[B!0]`numbering;
  R:=rec< ThetaPoint_carac2 | numbering:=A,
                              coord:=AssociativeArray(A),
                              lvl:=ze[B!0]`lvl,
                              g:=g >;

  C:=CartesianProduct([D : i in [1..#s]]);

// take the isogeny
  for a in A do
    K:=Transpose( Matrix( Integers(),#s,g,
                          [Eltseq(a)] cat [Eltseq(A!0) : i in [1..(#s-1)]]
                          ) );
    JM:= K * Transpose(F); // it works at least for level 2.
    J:=[ &+[ JM[i,j]*A.i : i in [1..g] ] : j in [1..#s]];

    S:=0;
    for t in C do
      T:= Transpose( Matrix( Integers(ell),#s,g,
                             [Eltseq(t[i]) : i in [1..#s]] ) );
      TF:=T * Fe;
      if TF eq ZeroMatrix(Integers(ell),g,#s) then

        p:=1;
        for i in [1..#s] do
          p*:=M[i][ t[i] ]`coord[J[i]];
        end for;

        pla:=[]; pmu:=[];
        for i in [1..#s] do
          p1,p2:=power_proj_factor(s[i],Eltseq(t[i]),ell,B);
          pla:=pla cat [p1];
          pmu:=pmu cat [p2];
        end for;

        for b in B do if b ne B!0 then
          p/:=la[b]^((&+[pla[i][b] : i in [1..#s]]) div ell);
//assert IsDivisibleBy((&+[pla[i][b] : i in [1..#s]]) , ell);
        end if; end for;
        for j in [1..g] do
          p/:=mu[B.j]^((&+[pmu[i][B.j]: i in [1..#s]]) div ell);
//assert IsDivisibleBy((&+[pmu[i][B.j]: i in [1..#s]]) , ell);
        end for;

        S+:=p;
      end if;
    end for;

    R`coord[a]:=S;
  end for;


  return R;
end function;




/*
Let z be a point on a variety A.
Let e be a S-basis of a maximal simpletic subgroup of the ell-torsion.
The S-basis is indexed by B=(Z/2Z)^g
Let ze be the points z and z+e_i, also indexed by B.

Compute the theta constants of the isogenous abelian variety
To do that compute phi(z) and phi(2z). When we compute Doubling(phi(z)), we use
the theta constants associated to the variety.
We use an ugly trick (by defining UN) so that we can used other functions to
get the result.

It is not expected that the isogeny is rational. The points of e can live is an
extension field of the based field. The optional argument field is the expected
field where the theta constants of the isogenous variety live.

work for genus 1 and 2
 */
function IsogenousAV(ell,e,B,ze,point0 :
                     field:=Parent(e[B.1]`coord[0]))
  z2e:=AssociativeArray(B);
  z2e[B!0]:=Doubling(ze[B!0],point0);
  for i in [1..#Invariants(B)] do
    z2e[B.i]:=AddDiff(ze[B.i],ze[B!0],e[B.i],point0);
  end for;

  R := Isogeny(ell,e,B,ze ,point0);
  R2:= Isogeny(ell,e,B,z2e,point0);

// compare 2* R and R2 to get the theta constants.
  A:=ze[B!0]`numbering;
  g:=ze[B!0]`g;
  UN:=rec< ThetaNullPoint_carac2 | numbering:=A,
                                   coord:=AssociativeArray(A),
                                   inv_coord:=AssociativeArray(A),
                                   lvl:=2,
                                   g:=g >;
  for a in A do UN`coord[a]:=1; UN`inv_coord[a]:=1; end for;

  Q:=Doubling(R,UN);


  new0:=rec< ThetaNullPoint_carac2 | numbering:=A,
                                     coord:=AssociativeArray(A),
                                     inv_coord:=AssociativeArray(A),
                                     lvl:=2,
                                     g:=g >;

  test := &and[R2`coord[a] ne 0 : a in A];
  if not test then
    if g eq 2 then if &and[R2`coord[a] ne 0 : a in A | a ne A.1+A.2] then
      error "The isogenous variety is a product of two elliptic curves. Not yet implemented";
    end if; end if;
    error "One theta constant of the isogenous variety is zero. Don't know why.";
  end if;

  for a in A do
    temp := Q`coord[a]/R2`coord[a] * R2`coord[A!0]/Q`coord[A!0];
    new0`coord[a]:=field!temp;
    new0`inv_coord[a]:=1/new0`coord[a];
  end for;
  return new0;
end function;




//**** Link with curves ****//


/*
if g =1
  Let C be y^2 + x y = x(x+b)^2
  Let A be (Z/2Z)
if g = 2
  Let C the a curve y^2 + x(x+1) y = x(x+1) (f3 x^3 + f3 x^2 + f2 x + f1)
  Let A be (Z/2Z)^2

compute the theta constants of the abelian variety associated to C.

work for genus 1 and 2.
 */
function CurveRosenhainToThetaConstant(C,A)
  f,h:=HyperellipticPolynomials(C);
  g:=( Degree(f) -1) div 2;

  F:=BaseField(C);

  n:=Invariants(A)[1];
  assert n eq 2;

  point0:=rec< ThetaNullPoint_carac2 | numbering:=A,
                                       coord:=AssociativeArray(A),
                                       inv_coord:=AssociativeArray(A),
                                       lvl:=n,
                                       g:=g,
                                       jacobian:=Jacobian(C),
                                       curve:=C >;

  point0`coord[A!0]:=F!1;

  if g eq 1 then
    point0`coord[A.1]:=Sqrt(Coefficient(f,1));

  elif g eq 2 then
    FF<x>:=Parent(f);
    fp:=FF!(f/x/(x+1));
    assert Coefficient(fp,2) eq Coefficient(fp,3);

    fp0:=Sqrt( Coefficient(fp,0) );
    fp1:=Sqrt( Coefficient(fp,1) + Coefficient(fp,0) );
    fp2:=Sqrt( Coefficient(fp,2) );

    point0`coord[A.1+A.2]:=Sqrt(fp0*fp2);
    point0`coord[A.1    ]:=Sqrt(fp0*fp1);
    point0`coord[    A.2]:=Sqrt(fp1*fp2);
  else
    error "Not yet implemented";
  end if;

  for a in A do
    point0`inv_coord[a]:=1/point0`coord[a];
  end for;

  return point0;
end function;


/*
From the theta constants, get the equation of the underlying curve.
It is assumed that there is an underlying curve. If it is not the case, you will
either have a division by 0 or magma will say that the function
HyperellipticCurve didn't worked.

If g =1, C is y^2 + x y = x(x+b)^2

Work for genus 1 and 2.
 */
function ThetaConstantToCurveRosenhain(point0)
  g:=point0`g;
  F:=Parent(point0`coord[point0`numbering!0]);
  FF<x>:=PolynomialRing(F);


  A:=point0`numbering;

  if g eq 1 then
    bp:=point0`coord[A.1];
    return HyperellipticCurve(x*(x+bp)^2,x);
  elif g eq 2 then
    bp:=point0`coord[A.1+A.2];
    cp:=point0`coord[A.1];
    dp:=point0`coord[A.2];

    f0:=bp^2*cp^2/dp^2;
    f1:=f0+cp^2*dp^2/bp^2;
    f2:=bp^2*dp^2/cp^2;
    f3:=f2;
    fp:=f0+f1*x+f2*x^2+f3*x^3;
    return HyperellipticCurve(x*(x+1)*fp , x*(x+1));
  else
    error "Not yet implemented";
  end if;
end function;


/*
Let UV be the Mumford polynomial of a divisor in Jac(C) where C is the curve
  if g =1:  y^2 + x y = x(x+b)^2
  if g =2 : y^2 + x(x+1) y = x(x+1) (f3 x^3 + f3 x^2 + f2 x + f1)
Let Tc be the associated theta constants

Compute the theta function associated.

It is assuled that the divisor is generic. // TODO complete the function

Work for genus 1 and 2 and level 2.
 */
function MumfordToTheta(UV,Tc,g)

  U:=UV[1]; V:=UV[2];
  F:=Parent(Coefficient(U,0));

  A:=Tc`numbering;
  assert #A eq 2^g; // level 2

  lvl:=Tc`lvl;

  if lvl ne 2 then error "Only implemented for level 2"; end if;

  R:=rec< ThetaPoint_carac2 | numbering:=A,
                              coord:=AssociativeArray(A),
                              lvl:=lvl,
                              g:=g >;


  if g eq 1 then
    if Degree(U) eq 0 then
      R:=ZeroPoint(lvl,g,A);
    else
      R`coord[A!0]:=-Coefficient(U,0);
      R`coord[A.1]:=Tc`coord[A.1];
    end if;

  elif g eq 2 then
    if Degree(U) eq 0 then
      R:=ZeroPoint(lvl,g,A);

    elif Degree(U) eq 1 then
      u0:=Coefficient(U,0);

      bp:=Tc`coord[A.1+A.2];
      cp:=Tc`coord[A.1];
      dp:=Tc`coord[A.2];

      z:=F!0;
      t:=F!1;
      y:=Sqrt( bp^2*t^2*(1-u0)/dp^2/u0 );
      x:=Sqrt( bp^2*dp^2*y^2*t^2 / (cp^2*(bp^2*t^2+dp^2*y^2)) );

      R`coord[A!0]:=x;
      R`coord[A.1+A.2]:=y;
      R`coord[A.1]:=z;
      R`coord[A.2]:=t;
    else
      u0:=Coefficient(U,0);
      u1:=Coefficient(U,1);
      v0:=Coefficient(V,0);
      v1:=Coefficient(V,1);
      v0vb0:=v0*(u0+v0);

      bp:=Tc`coord[A.1+A.2];
      cp:=Tc`coord[A.1];
      dp:=Tc`coord[A.2];

      if v0 ne 0 then

//        f0:=bp^2*cp^2/dp^2;
//        f1:=f0+cp^2*dp^2/bp^2;
//        f2:=bp^2*dp^2/cp^2;

        z:=F!1;
        t:=Sqrt( u0*dp^2/cp^2 );
        y:=Sqrt( (u1-1-u0)*bp^2/cp^2 );

        x:=Sqrt( (v0vb0*dp^4/cp^4/t^2 -bp^2*(t^4+z^4)-dp^2*y^2*t^2)/dp^2 );

        R`coord[A!0]:=x;
        R`coord[A.1+A.2]:=y;
        R`coord[A.1]:=z;
        R`coord[A.2]:=t;

      else
        if u0 eq 0 then
          FF<X>:=Parent(U);
          nU:=X+u1; nV:=FF!(u1*v1); //nU:=FF!(U/X);
          nR:=MumfordToTheta([nU,nV],Tc,g);

          R`coord[A!0]:=nR`coord[A.1+A.2];
          R`coord[A.1+A.2]:=nR`coord[A!0];
          R`coord[A.1]:=nR`coord[A.2];
          R`coord[A.2]:=nR`coord[A.1];
        else
          z:=F!1;
          t:=Sqrt( u0*dp^2/cp^2 );
          y:=Sqrt( (u1-1-u0)*bp^2/cp^2 );
          x:=Sqrt( ( bp^2*(t^2+z^4)-dp^2*y^2*t^2 ) / (dp^2*z^2) );

          R`coord[A!0]:=x;
          R`coord[A.1+A.2]:=y;
          R`coord[A.1]:=z;
          R`coord[A.2]:=t;
        end if;
      end if;

    end if;

  else
    error "g>2, not yet implemented";
  end if;
  return R;
end function;



/*
Let P be a point over the abelian variety defined by the theta constants Tc in
level 2. Compute the mumford polynomial of the divisor.
Since we are in level 2, we work on A/{\pm 1}. Thus we cannot get the v
polynomial. We can only get v*w where w is the v polynomial of -P.

The curve is given by the equation
  if g = 1: y^2 + x y = x(x+b)^2
  if g = 2: y^2 + x(x+1) y = x(x+1) (f3 x^3 + f3 x^2 + f2 x + f1)

Work for genus 1 and level 2.
TODO: in genus 2, we return v*w(0). This should be fixed.
 */
function ThetaToMumford(P,Tc)
  g:=P`g;
  A:=P`numbering;

  F:=Parent(P`coord[P`numbering!0]);
  FF<X>:=PolynomialRing(F);

  if g eq 1 then
    if P`coord[A.1] eq 0 then return FF!1,F!0; end if; // zero
    x0:= Tc`coord[A.1]*P`coord[A!0]/P`coord[A.1];
    return X-x0,x0*(x0+Tc`coord[A.1])^2;
  elif g eq 2 then

    bp:=Tc`coord[A.1+A.2];
    cp:=Tc`coord[A.1];
    dp:=Tc`coord[A.2];

    x:=P`coord[A!0];
    y:=P`coord[A.1+A.2];
    z:=P`coord[A.1];
    t:=P`coord[A.2];

    if z eq 0 then
      den:=dp^2*y^2+bp^2*t^2;
      if den eq 0 then return FF!1,FF!0; end if; // zero
      u0:=bp^2*t^2/den;

      f0:=bp^2*cp^2/dp^2;
      f1:=f0+cp^2*dp^2/bp^2;
      f2:=bp^2*dp^2/cp^2;
      f3:=f2;
      v0vb0:=( f0 + f1*u0 + f2*u0^2 + f3*u0^3 ) * u0 * (u0+1);
      return X+u0,FF!v0vb0;
    end if;

    u0:=cp^2*t^2/dp^2/z^2;
    u1:=1+u0+cp^2*y^2/bp^2/z^2;

    v0vb0:=cp^4*t^2/dp^4/z^6 * (bp^2*(t^4+z^4) + dp^2*(x^2*z^2+y^2*t^2));

    return u0+X*u1+X^2,v0vb0; // TODO
  else
    error "g>2: not yet implemented";
  end if;
end function;





//**** Isogeny and curves ****//

/*
Check if the curve C is in good form (Rosenhain) for the isogeny
  if g = 1: y^2 + x y = x(x+b)^2
  if g = 2: y^2 + x(x+1) y = x(x+1) (f3 x^3 + f3 x^2 + f2 x + f1)
  if g > 2: Not yet implemented"
 */
function IsGoodForm(C)
  g:=Genus(C);
  f,h:=HyperellipticPolynomials(C);

  F:=BaseField(C);
  FF<x>:=PolynomialRing(F);

  if g eq 1 then
    if h ne x then return false; end if;
    if Degree(f) ne 3 and Coefficient(f,3) ne 1 then return false; end if;
    if Coefficient(f,0) ne 0 then return false; end if;
    if Coefficient(f,2) ne 0 then return false; end if;
  elif g eq 2 then
    if h ne x*(x+1) then return false; end if;
    if Degree(f) ne 5 then return false; end if;
    if not IsDivisibleBy(f,x*(x+1)) then return false; end if;
    if Coefficient(f,4) ne 0 then return false; end if;
  else
     error "g>2, not yet implemented";
  end if;
  return true;
end function;


/*
Let C: y^2+h(x)y=f(x) an hyperelliptic curve
  We assume that degree(h)<= g and Degree(f)=2g+1
  Note that f is not assumed to be monic
Let FF be an extension field of the base field F of the curve.

For the jacobian to be ordinary, h must be of degree g.

returns the new hyperelliptic curve newC over a field extension L/F,
  a function phi witch take a mumford divisor in Jac(C)(LL) and return its
    image in Jac(newC)(LL) where LL is an extension of FF containing L.
  a list [t1,t2] where
    t1 = true  iff we need to take a field extension
    t2 = true  iff we need to take the quadratic twist

Work only for genus 2.
 */
function WeierstrassToRosenhain(C,FF)
  f,h:=HyperellipticPolynomials(C);
  assert IsOdd( Degree(f) );
  g:=( Degree(f) -1) div 2;
  assert Degree(h) eq g;

  J:=Jacobian(C);
  F:=BaseField(C);

  if g eq 1 then
    error "getting the good equation for g=1 is not yet implemented. Do it by hand";
  elif g eq 2 then

    r,K:=RootsInSplittingField(h);
    assert #r eq 2; // otherwise it is not ordinary

    if K ne F then t1:=true; else t1:=false; end if;

    Kx<x>:=PolynomialRing(K);
    h2:=Coefficient(h,2);
    newh:=x*(x-1);
    newf:=Evaluate(f, (r[2][1]-r[1][1])*x+r[1][1] ) / (r[2][1]-r[1][1])^4 /h2^2;


    KK:=ConstructOverfield([FF,K]);
    KX<X>:=PolynomialRing(KK);
    newJ:=BaseChange(Jacobian(HyperellipticCurve(newf,newh)),KK);

    function phi1(P)
      if Degree(P[1]) eq 0 then
        return newJ!0;
      elif Degree(P[1]) eq 1 then
        u0:=Coefficient(P[1],0);
        return newJ![X - KK!( (-u0-r[1][1])/(r[2][1]-r[1][1]) ),
                     KX!( P[2]/(r[2][1]-r[1][1])^2/h2 ) ];
      else
        u0:=Coefficient(P[1],0);
        u1:=Coefficient(P[1],1);
        U:=X^2  +  X * u1 /(r[2][1]-r[1][1]) +
           (u0+r[1][1]*u1+r[1][1]^2) / (r[2][1]-r[1][1])^2;
        V:=Evaluate( P[2] , X*(r[2][1]-r[1][1])+r[1][1] )
            / (r[2][1]-r[1][1])^2/h2;
        return newJ![U,V];
      end if;
    end function;

    // we have the good h ie.  x*(x+1)

    g:=Sqrt(Evaluate(newf,1))*x + Sqrt(Evaluate(newf,0))*(x+1);
    newf:=newf+g^2+x*(x+1)*g;
    newJ:=BaseChange(Jacobian(HyperellipticCurve(newf,newh)),KK);

    function phi2(P)
      if Degree(P[1]) eq 0 then
        return newJ!0;
      elif Degree(P[1]) eq 1 then
        return newJ![P[1],P[2]+Evaluate(g,Coefficient(P[1],0))];
      else
        return newJ![P[1],P[2]+g];
        // TODO is it still correct if P[1] is a square?
      end if;
    end function;

    // f is now divisible by x*(x+1)


    c:=Coefficient(newf,4);
    r,L:=RootsInSplittingField(x^2+x+c);
    Lx<x>:=PolynomialRing(L);
    r:=r[1][1];
    newh:=x*(x-1);
    newf:=newf+ x^2*(x-1)^2*c;

    if L ne K then t2:=true; else t2:=false; end if;

    LL:=ConstructOverfield([KK,L]);
    LX<X>:=PolynomialRing(LL);
    newJ:=BaseChange(Jacobian(HyperellipticCurve(newf,newh)),LL);

    function phi3(P)
      if Degree(P[1]) eq 0 then
        return newJ!0;
      elif Degree(P[1]) eq 1 then
        return newJ![ LX!P[1], LX!P[2]+Evaluate(r*X*(X-1),Coefficient(P[1],0))];
      else
        return newJ![LX!P[1],LX!P[2]+r*X*(X-1)];
        // TODO is it still correct if P[1] is a square?
      end if;
    end function;


    function phi(P) return phi3(phi2(phi1(P))); end function;
    newC:=HyperellipticCurve(newf,newh);

    return newC,phi,[t1,t2];

  else
    error "g>2: not yet implemented";
  end if;
end function;


/*
Let C: y^2+x(x-1)y=x(x-1)(f3*x^3+f2*x^2+f1*x+f0) with f3=f2

Let info be an associative array indexed with strings
  test is a list [t1,t2] with
    t2 = true iff we want the quadratic twist of C
    t1 = true iff we used some quadratic extension FIXME
  BaseField is the expected field F for the curve.
  FrobPoly is the action of the frobenius on the curve C/F

return the weierstrass equation of the curve over the field F
 */
function RosenhainToWeierstrass(C,info)
  t1:=info["test"][1]; t2:=info["test"][2];
  F:=info["BaseField"];


  f,h:=HyperellipticPolynomials(C);
  l:=GetCastMinField(Eltseq(f));

  K:=Parent(l[1]);
  KK<x>:=PolynomialRing(K);
//  W:=HyperellipticCurve(KK!l,x*(x+1));

//  if IsSubfield(W, F) then W:=BaseChange(W,F); end if;

  newf:=f; newh:=h;
  if t2 then // W:=QuadraticTwist(W);
    L:=ext<K|2>;
    repeat
      repeat r:=Random(L); until Trace(r,K) ne 0;
      r/:=Trace(r,K);
    until r notin K;
    newf:=KK!(newf+(r^2+r)*newh^2);
  end if;

  FF<t>:=PolynomialRing(F);

  if not IsCoercible(FF,newf) then

    if t1 or not IsCoercible(F,Coefficient(newf,5)) then
      a:=1/Coefficient(newf,5);
      newf:=Evaluate(newf,a*x)/ a^4;
      newh:=x*(x+1/a);

      repeat
        repeat r:=Random(K); until Trace(r,F) ne 0;
        r/:=a*Trace(r,F);
      until r notin F;
      newh:=x^2 + x/a + (r*(r+1/a)); assert IsCoercible(FF,newh);
      newf:=Evaluate(newf,x+r);
    end if;

    if not IsCoercible(FF,newf) then

      repeat
        repeat r:=Random(K); until Trace(r,F) ne 0;
        r/:=Trace(r,F);
      until r notin F;

      h1:=Coefficient(newh,1);
      h0:=Coefficient(newh,0);

      f4:=Coefficient(newf,4); f42:=Trace(K!f4,F);
      f3:=Coefficient(newf,3); f32:=Trace(K!f3,F);
      f1:=Coefficient(newf,1); f12:=Trace(K!f1,F);


      R:=Roots(t^2+t+f42);
      a:=K!R[1][1];
      b:=a*h1+f32;
      c:=(b*h0+f12)/h1;

      g:=a*r*x^2 + b*r*x + c*r;
      newf:=newf + g^2 + g*newh;
    end if;

  end if;


  newf:=FF!newf; newh:=FF!newh;
  W:=HyperellipticCurve(newf,newh);

  if FrobeniusPoly(W) ne info["FrobPoly"] then
    W:=QuadraticTwist(W);
    assert FrobeniusPoly(W) eq info["FrobPoly"];
  end if;


  return W;
end function;





/*
Let J be a jacobian of a genus 2 curve.
Let ell be a prime number.
Let kernel be a list of g divisors of l-torsion that generate a rational
  isotropic subgroups.

Compute the jacobian of the ell-isogenous curve associated to kernel
*/
function IsogenousCurveG2_carac2(C,ell,kernel)
  // C :: CrvHyp, ell :: RngIntElt, kernel :: SeqEnum ) -> CrvHyp
  // {Compute the ell-isogenous curve associated to kernel}

  J:=Jacobian(C);
  g:=Genus(C);

  F:=BaseField(C);
  L:=BaseRing(kernel[1][1]);

  if not IsGoodForm(C) then
    // Put the curve in "Rosenhain form"
    info:=AssociativeArray();
    info["BaseField"]:=F;
    info["FrobPoly"]:= FrobeniusPoly(C);

    nC,phi,test:=WeierstrassToRosenhain(C,L);
    info["test"]:=test;

    newKernel:=[phi(x) : x in kernel];
    C2:=IsogenousCurveG2_carac2(nC, ell, newKernel);

    W:=RosenhainToWeierstrass(C2,info);
    return W;
  end if;

  // Find a good random element
  repeat
    z:=Random(BaseChange(J,L));
  until Order(z) notin {1,2,4,ell,2*ell};

  B:=AbelianGroup([2 : i in [1..g]]);
  e :=AssociativeArray(B);
  ze:=AssociativeArray(B);

  A:=AbelianGroup([2 : i in [1..g]]); // since we want to be in level 2
  point0:=CurveRosenhainToThetaConstant(C,A);

  ze[B!0]:=MumfordToTheta(z, point0,g);
  for b in B do if b ne B!0 then
    e[b]:=MumfordToTheta( &+[Eltseq(b)[i]*kernel[i] : i in [1..g]] , point0,g);
  end if; end for; // ok for genus 1 and 2.
  for i in [1..g] do
    ze[B.i]:=MumfordToTheta( z+kernel[i] , point0,g);
  end for;

  // get the theta constants of the isogenous variety
  new0:=IsogenousAV(ell,e,B,ze,point0);
  new0:=CastCoordinates(new0,F);

  // get the isogenous curve
  C2:=ThetaConstantToCurveRosenhain(new0);

  return C2;
end function;




/*
Let J be a jacobian of a genus 2 curve.
Let ell be a prime number.

precomp is an associatve array. See the documentation. We only use its parameter
  "subgroups".

The option curve_to_invariants is a function that choose a representative
systeme of invariants.
*/
function HasHyperellipticNormalForm_AVI_char2(H)
    f, h := HyperellipticPolynomials(H);
    if Degree(h) le 2 then
        return true, H;
    end if;
    bool, w := HasRoot(h);
    if bool then
        return true, Transformation(H,[0,1,1,w]);
    else
        return false, H;
    end if;
end function;

function RationallyIsogenousCurvesG2_carac2(H,ell : precomp:=AssociativeArray(), curve_to_invariants:=G2Invariants)
  // H :: CrvHyp, ell :: RngIntElt : precomp:=AssociativeArray(), curve_to_invariants:=G2Invariants ) -> CrvHyp
  // {In a field of characteristic 2, given a hyperelliptic curve H and a prime ell, returns the ell-isogenous curves}

  bool, H := HasHyperellipticNormalForm_AVI_char2(H);
  if not bool then
    return [], precomp;
  end if;
  J := Jacobian(H);
  if ell eq 2 then
    error "2-isogeny not yet implemented";
  end if;
  if not IsPrime(ell) then
    error "Non prime isogeny not yet implemented";
  end if;

  if not IsDefined(precomp,"subgroups") then
    IndentPush();
    vtime AVIsogenies,2: R,_,_:=RationalSymplecticTorsionSubgroups(J,ell: theta:=0,only_mumford:=true);
    IndentPop();
  else
    R:=precomp["subgroups"];
  end if;

  result:=[];
  for r in R do
    try
      vprint AVIsogenies, 3: "** Computing the",ell,"-isogeny";
      vtime AVIsogenies, 3: H2:=IsogenousCurveG2_carac2(H,ell,r);
      nInv:=curve_to_invariants(H2);
      Append(~result, <nInv,H2>);
    catch e
      "CAUGHT ERROR:", e;
    end try;
  end for;

  return result,precomp;
end function;

