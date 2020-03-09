/******************************************************************************/
/**** This file is specific to genus 2 curves and level 2.
/**** This file links the curves with the associated theta functions.
/**** The goal was to have efficient fomulae. Thus they can be ugly. For more
/**** simple/general formulae (g not 2, and/or level 4) see the file morphisms.m
/******************************************************************************/



/* Conversion between Mumford and Theta coordinates in genus 2
* - Romain Cosset
* - Damien Robert
*/

import "Arithmetic.m" : get_dual_coord,  precompute_D, init_theta_point, \
  init_theta_null_point;
import "libav.m" : MyCompositeField, TowerOfField, map_change, InvertGenListMontgomery;
import "libseq.m" : ConvertArray;


RootsInSplittingFieldOpt:=func<x | RootsInSplittingField(x: Optimize:=false)>;

//**** Rosenhain form ****//

/*
Let phi=precomp["HK","Hphi"] be an isomorphism of curve H -> Hn. Let P be a
divisor in Jac(H)
Compute phi(P) as a divisor in Jac(Hn)

It is assumed that H and Hn are hyperelliptic of genus 2 and that their h
poloynomial is 0

This function should not be used it itself.
*/
function JacHypMapFromCrvHypMap(P,precomp)
  phi:=precomp["HK","Hphi"];
  abcdw:=precomp["HK","Habcdw"];
  H:=Domain(phi);
  Hn:=Codomain(phi);

  _,h :=HyperellipticPolynomials(H );
  _,hn:=HyperellipticPolynomials(Hn);
  assert h  eq 0;
  assert hn eq 0;
  assert Genus(H) eq 2;

  PsInf:=precomp["HK","Hinfinity"]; // PointsAtInfinity(H);
  Jext:=precomp["HK","HnJ"]; //J2:=precomp["HK","HnJ2"];
  K:=BaseRing(Jext);
  abcdw:=[K!i: i in abcdw];
  a,b,c,d,w:=Explode(abcdw);


  if P[3] eq 0 then
    return Jext!0;

  elif P[3] eq 1 then // there is only one point at infinity on C
    assert #PsInf eq 1;
    x1:=-Coefficient(P[1],0);
    y1:=P[2];
    Q:=phi(H![x1,y1]);
    PtExtInf:=PointsAtInfinity(Hn)[1];
    return Jext!(Q-PtExtInf);

  elif P[3] eq 2 then
    if Degree(P[1]) eq 2 then
      //If P is a sum of rationnal points we compute phi(P) directly
      //Disc:=Discriminant(P[1]);
      // if IsSquare(Disc) then
      // else
      //else we find u with a resultant
        B<X>:=PolynomialRing(K);
        A<Y>:=PolynomialRing(B);
        Q:=(c*Y+d)*X-a*Y-b; // X =(aY+b)/(cY+d);
        incl:=hom<B -> A | Y>;
        u:=Resultant(incl(B!P[1]),Q);
        u:=u/Coefficient(u,Degree(u));

        // for v it's more complicated. Here is the magma code for the proof:
        // > B<alpha,beta,gamma,delta>:=RationalFunctionField(RationalField(),4);
        // > A<X,y1,y2,x1,x2,a,b,c,d>:=PolynomialRing(B,9);
        // > AA:=FieldOfFractions(A);
        // > f:=(y2-y1)/(x2-x1)*X + (y1*x2-y2*x1)/(x2-x1);
        // > phi:=hom<AA -> AA | [X,y1,y2,(a*x1+b)/(c*x1+d),(a*x2+b)/(c*x2+d),a,b,c,d]>;
        // > ff:=f@phi;
        // > ffnum:=Numerator(ff);
        // > ffden:=Denominator(ff);
        // > P1:=y2-y1-alpha*(x2-x1);
        // > P2:=(y1*x2-y2*x1)-beta*(x2-x1);
        // > P3:=(x1+x2)-gamma;
        // > P4:=x1*x2-delta;
        // > I:=ideal<A|[P1,P2,P3,P4]>;
        // > AI:=quo<A|I>;
        // > KI:=FieldOfFractions(AI);
        // > KI!ff;
        // (alpha*delta*X*c^2 + alpha*gamma*X*c*d + alpha*X*d^2 - alpha*delta*a*c +
        //   beta*a*d + (-alpha*gamma - beta)*b*c - alpha*b*d)/(a*d - b*c)
        // Nope, doesn't work, in magma y is of degree 3, so we need to use:
        //phi:=hom<AA -> AA | [X,y1/(c*x1+d)^3,y2/(c*x2+d)^3,(a*x1+b)/(c*x1+d),(a*x2+b)/(c*x2+d),a,b,c,d]>;
        // cf the ugly formula for v below...

        alpha:=K!Coefficient(P[2],1);
        beta:=K!Coefficient(P[2],0);
        gamma:=K!-Coefficient(P[1],1);
        delta:=K!Coefficient(P[1],0);
        //v:=w*(alpha*delta*X*c^2 + alpha*gamma*X*c*d + alpha*X*d^2 - alpha*delta*a*c + beta*a*d + (-alpha*gamma - beta)*b*c - alpha*b*d)/(a*d - b*c);
        if delta eq 0 then den:=0; else
        den:=(a*c^4*d + 2*gamma/delta*a*c^3*d^2
  + (gamma^2 + 2*delta)/delta^2*a*c^2*d^3 + 2*gamma/delta^2*a*c*d^4 +
  1/delta^2*a*d^5 - b*c^5 - 2*gamma/delta*b*c^4*d + (-gamma^2 -
  2*delta)/delta^2*b*c^3*d^2 - 2*gamma/delta^2*b*c^2*d^3 - 1/delta^2*b*c*d^4);
        end if;
        if delta eq 0 or den eq 0 then
          // When this happen P will usually be a sum of two rational points
          // "Trying to handle the special case:";
          // print P: Magma;
          //assert (#PsInf eq 1) or (#PsInf eq 2);
          R:=Roots(P[1]);
          if #R eq 0 then
            error "This should not happen!"; //TODO check this
          elif #R eq 1 then
            x1:=R[1][1];
            x2:=R[1][1];
          else
            x1:=R[1][1];
            x2:=R[2][1];
          end if;
          y1:=Evaluate(P[2],x1);
          y2:=Evaluate(P[2],x2);
          if #PsInf eq 0 then
            F0:=BaseField(H);
            F2:=ext<F0|2>;
            H2:=BaseExtend(H,2);
            Jext2:=BaseExtend(Jext,2);
            phi2:=map_change(phi,H2,Curve(Jext2));
            PsInf:=PointsAtInfinity(H2);
            if #PsInf eq 1 then PsInf:=[PsInf[1] : i in [1..2]]; end if;
            return Jext!Jext2![[phi2([x1,y1,1]),phi2([x2,y2,1])],[phi2(x) : x in PsInf]];
          else
            if #PsInf eq 1 then PsInf:=[PsInf[1] : i in [1..2]]; end if;
            return Jext![[phi([x1,y1,1]),phi([x2,y2,1])],[phi(x) : x in PsInf]];
          end if;
        end if;
        v:=w*
           ((-alpha*gamma*delta - beta*gamma^2 + beta*delta)/delta^2*X*c^3 +
  (-3*alpha*delta - 3*beta*gamma)/delta^2*X*c^2*d - 3*beta/delta^2*X*c*d^2 +
  alpha/delta^2*X*d^3 + (alpha*gamma*delta + beta*gamma^2 -
  beta*delta)/delta^2*a*c^2 + (2*alpha*delta + 2*beta*gamma)/delta^2*a*c*d +
  beta/delta^2*a*d^2 + (alpha*delta + beta*gamma)/delta^2*b*c^2 +
  2*beta/delta^2*b*c*d - alpha/delta^2*b*d^2)/den;
        return Jext![u,v];

    elif Degree(P[1]) eq 1 then
      R:=Roots(P[1]);
      x1:=R[1][1]; y1:=Evaluate(P[2],x1);
      x2:=1; y2:=Coefficient(P[2],3);
      if #PsInf eq 1 then PsInf:=[PsInf[1] : i in [1..2]]; end if;
      return Jext![[phi([x1,y1,1]),phi([x2,y2,0])],[phi(x) : x in PsInf]];

    elif Degree(P[1]) eq 0 and P[3] eq 0 then // This should never happen
      error "The case Degree(P[1]) eq 0 and P[3] eq 0 is illegal";
    elif Degree(P[1]) eq 0 and P[3] eq 1 then
      error "The case Degree(P[1]) eq 0 and P[3] eq 1 is illegal";
    else // Degree(P[1]) eq 0 and P[3] eq 2 then
      assert #PsInf eq 2;
      y:=Coefficient(P[2],3);
      assert H![1,y,0] in PsInf;
      return Jext![[phi([1,y,0])],[phi([1,-y,0])]];
    end if;

  /* Should never happen with magma representation
  else // P[3] eq 3.
    assert #PsInf eq 1;
    PsInf:=[PsInf[1] : i in [1..3]];
    if Degree(P[1]) eq 2 then
      R:=RootsInSplittingField(P[1]);
      if #R eq 0 then
error "Not yet implemented"; //TODO
      elif #R eq 1 then
        x1:=R[1][1];
        x2:=R[1][1];
      else
        x1:=R[1][1];
        x2:=R[2][1];
      end if;
      y1:=Evaluate(P[2],x1);
      y2:=Evaluate(P[2],x2);
      x3:=1;
      y3:=Coefficient(P[2],3);
      return Jext!J2![[phi([x1,y1,1]),phi([x2,y2,0]),phi([x3,y3,0])],
     [phi(x) : x in PsInf]];

    elif Degree(P[1]) eq 1 then
      R:=Roots(P[1]);
      x1:=R[1][1];
      y1:=Evaluate(P[2],x1);
      x2:=1;
      y2:=Coefficient(P[2],3);
      x3:=1;
      y3:=Coefficient(P[2],3);
      return Jext![[phi(H![x1,y1,1]),phi(H![x2,y2,0]),phi(H![x3,y3,0])],
       [phi(x) : x in PsInf]];

    else //Degree(P[1]) eq 0. This should never happen
      x:=1;
      y:=Coefficient(P[2],3);
      return Jext![[phi(H![x,y,0]),phi(H![x,y,0]),phi(H![x,y,0])],
       [phi(x) : x in PsInf]];
    end if;
    */
  end if;
end function;

/*
Compute a Rosenhain form of an hyperelliptic curve C of genus 2 over an
extension field K.

return newC,Ros,phi,[a,b,c,d,1/w];
  newC is the new curve in Rosenhain form
  Ros is the roots of the hyperelliptic polynomial of newC. Their order is
    important for the abel-jacobi map and thus in the Thomae and morphisms
    formulae. We put the roots 1,0 at the end of the sequences.
  phi is a map between C and newC (the curve are over the extension field K)
  [a,b,c,d,1/w] are the coefficients used in the map phi

It does not compute the morphism on the jacobian
*/
function RosenhainForm(C)
  IndentPush();
  assert Genus(C) eq 2;

  f:=HyperellipticPolynomials(C);
  vprint AVIsogenies, 4: "Find Weierstrass Points";
  vtime AVIsogenies, 4: R,K:=RootsInSplittingFieldOpt(f);
  KK<x>:=PolynomialRing(K);
  Rac:=[r[1] : r in R];

  if (#Rac eq 5) and (1 in Rac) and (0 in Rac) and (Coefficient(f,5) eq 1) then
    // we already have a Rosenhain form
    a:=1;b:=0;c:=0;d:=1; w:=1;
  elif #Rac eq 5 then
    wini:=Coefficient(f,5);
    a:=1/(Rac[2]-Rac[1]);
    b:=-a*Rac[1];
    c:=0;
    d:=1;
    lw,K:=RootsInSplittingField(x^2-wini/a^5);
    w:=lw[1][1];
  else
    wini:=Coefficient(f,6);
    c:=1;
    d:=-Rac[6];
    a:=(Rac[2]+d)/(Rac[2]-Rac[1]);
    b:=-a*Rac[1];
    sw:=(a*d-b*c)^5*c/(&*[c*r+d :  r in Rac | r ne Rac[6]]);
    lw,K:=RootsInSplittingField(x^2-wini/sw);
    w:=lw[1][1];
  end if;

// FIXME c'est quoi le commentaire suivant
  // to get points at infinity split Mumford's u
  //C:=BaseChange(C,CommonOverfield(K,ext<BaseRing(C)|2>));
  //newC,phi:=Transformation(C,[a,b,c,d],1/w,PolynomialRing(K)!0);
  C:=BaseChange(C,K);
  newC,phi:=Transformation(C,[a,b,c,d],1/w);

  //// We should be able to compute this directly as an homography on the
  //roots of C
  //vprint AVIsogenies, 4: "Second Roots";
  //vtime AVIsogenies, 4: Ros:=[x[1] : x in Roots(HyperellipticPolynomials(newC)) | x[1] ne 0 and x[1] ne 1];
  Ros:=[K|(a*x+b)/(c*x+d): x in Rac  |c*x+d ne 0];
  Ros:=[x: x in Ros | x ne 0 and x ne 1] cat [1,0];
  IndentPop();
  return newC,Ros,phi,[a,b,c,d,1/w];
end function;




//**** Level 2 and (2,2) manipulation ****//



/*
In genus 2! From a theta null point P0 of level 2, compute the square of theta
constants of level (2,2).

P0 :: ThetaNullPoint
The result is given as a list with the numbering of Gaudry.
*/
function lvl2_to_sqlvl22(P0)
  Z2:=P0`coord; D:=P0`numbering;
  A00:=D.0; A10:=D.1; A01:=D.2; A11:=D.1+D.2;

  assert P0`g eq 2; // assert genus = 2
  assert P0`l2; // level =2

  A:=(Z2[A00]+Z2[A11]+Z2[A10]+Z2[A01])/4;
  B:=(Z2[A00]+Z2[A11]-Z2[A10]-Z2[A01])/4;
  C:=(Z2[A00]-Z2[A11]+Z2[A10]-Z2[A01])/4;
  D:=(Z2[A00]-Z2[A11]-Z2[A10]+Z2[A01])/4;

  th1:=get_dual_coord(P0,A00,A00,A00)/4;
  th2:=get_dual_coord(P0,A00,A11,A00)/4;
  th3:=get_dual_coord(P0,A00,A10,A00)/4;
  th4:=get_dual_coord(P0,A00,A01,A00)/4;

  th5:=2*D*A+2*B*C;
  th7:=2*C*A+2*B*D;
  th8:=2*B*A+2*C*D;

  ith5,ith7,ith8:=Explode(InvertGenListMontgomery([th5,th7,th8]));

  th6 :=(th1*th4-th2*th3)*ith5;
  th9 :=(th1*th3-th2*th4)*ith7;
  th10:=(th1*th2-th3*th4)*ith8;

  Th:=[th1,th2,th3,th4,th5,th6,th7,th8,th9,th10];
  for th in Th do
    assert th ne 0;
  end for;
  return Th;
end function;

/*
In genus 2, compute the theta null point Z2 of level 2 from the squares of the
theta constants of level (2,2).

sZ22 is an associative array indexed by the abelian group (Z/2Z)^4
the result Z2 is an associative array indexed by (Z/2Z)^2
Ab_2 is the abelian group (Z/2Z)^2
*/
function sqlvl22_to_lvl2(sZ22,Ab_2)
  assert #Ab_2 eq 4;
  Z2:=AssociativeArray();
  for eb in Ab_2 do
    Z2[eb]:=0;
    for ea in Ab_2 do
      Z2[eb]+:=sZ22[Eltseq(ea) cat Eltseq(eb)];
    end for;
  end for;
  return Z2;
end function;





//**** Theta -> rosenhain ****//

/*
In genus 2, given the level 2 theta null point P0, compute the rosenhain
invariants of the corresponding hyperelliptic curve together with its twist.
Of curse it only works for non decomposable curves.

P0 :: ThetaNullPoint

return [nu,mu,la,1,0] which corresponds to the f polynomial
  f:=x*(x-1)*(x-la)*(x-mu)*(x-nu);
Thus the curve is y^2=f(x) or its twist
 */
function theta_null_to_rosenhain(P0)
  Z2:=P0`coord;
  D:=P0`numbering;
  A00:=D.0; A10:=D.1; A01:=D.2; A11:=D.1+D.2;
  assert P0`g eq 2; // assert genus = 2
  assert P0`l2; // assert level = 2

  // we should be dividing these numbers by 4,
  ///// but in fact it is by 16 because we multiply them by 4 in the addition.
  ///// not now any more
  // However, here it is homogeneous, so it works.
  al:=get_dual_coord(P0,A00,A00,A00);
  be:=get_dual_coord(P0,A00,A11,A00);
  ga:=get_dual_coord(P0,A00,A10,A00);
  de:=get_dual_coord(P0,A00,A01,A00);

  A:=(Z2[A00] + Z2[A11] + Z2[A10] + Z2[A01] )/4;
  B:=(Z2[A00] + Z2[A11] - Z2[A10] - Z2[A01] )/4;
  C:=(Z2[A00] - Z2[A11] + Z2[A10] - Z2[A01] )/4;
  D:=(Z2[A00] - Z2[A11] - Z2[A10] + Z2[A01] )/4;

  if A*B*C*D*de*be eq 0 then
    error "It doesn't work with decomposable curves. To be implemented";
  end if;

  CD_AB:=C*D/(A*B);
  if CD_AB^2 eq 1 then
   error "It doesn't work with decomposable curves. To be implemented";
  end if;
  ep_phi:=(1+CD_AB)/(1-CD_AB);

  ide:=1/de; ibe:=1/be;
  la:=al*ga*ide*ibe;
  mu:=ga*ide *ep_phi;
  nu:=al*ibe *ep_phi;

  //K<x>:=PolynomialRing(Parent(la));
  //f:=x*(x-1)*(x-la)*(x-mu)*(x-nu);
  return [nu,mu,la,1,0];
end function;





//**** Rosenhain -> theta ****//

/*
Let C be a curve in Rosenhain form of genus 2. Let Rac be the roots of the
hyperelliptic polynomial of C.
Assume that the roots are numbered (which means that Rac is a sequence) and
that the last ones are 1 and 0.
We apply Thomae formulae to get the squares of the theta constants of level
(2,2). Note that we need to extract some roots (and thus, go to an extension
field). We take random choices for the roots since it leads to isomorphic
varieties. See Cosset, Robert for details.
At last, we apply the function sqlvl22_to_lvl2 to get the level 2 theta null
point from the square of the theta constants of level (2,2).

We assume that we work over a finite field for the magma function
RootsInSplittingField
*/
function Z2_from_Rosenhain_fldfin(Rac,D)
  assert #Rac eq 5; // assert genus 2
  assert #D eq 4; // assert genus 2 and level 2

  assert Rac[4] eq 1; assert Rac[5] eq 0;
// TODO this still needed for computing theta_2. It should be possible to remove this. See the article Cosset, Robert

  sZ22:=AssociativeArray();

  sZ22[[0,0,0,0]]:=1; //th1

  t3:=(Rac[1]-Rac[4])*(Rac[3]-Rac[2])*(Rac[5]-Rac[2])/
      ((Rac[2]-Rac[4])*(Rac[3]-Rac[1])*(Rac[5]-Rac[1]));

  t4:=(Rac[1]-Rac[4])*(Rac[3]-Rac[2])*(Rac[5]-Rac[4])/
      ((Rac[1]-Rac[3])*(Rac[4]-Rac[2])*(Rac[5]-Rac[3]));

  t5:=(Rac[1]-Rac[2])*(Rac[1]-Rac[4])/
      ((Rac[1]-Rac[3])*(Rac[1]-Rac[5]));

  t7:=(Rac[1]-Rac[4])*(Rac[3]-Rac[4])*(Rac[5]-Rac[2])/
     ((Rac[1]-Rac[5])*(Rac[3]-Rac[5])*(Rac[4]-Rac[2]));

  K:=Universe(Rac);

  KK<x>:=PolynomialRing(K);
  r,K:=RootsInSplittingField(x^2-t3);
  sZ22[[0,0,1,0]]:=r[1][1];

  KK<x>:=PolynomialRing(K);
  r,K:=RootsInSplittingField(x^2-t4);
  sZ22[[0,0,0,1]]:=r[1][1];

  KK<x>:=PolynomialRing(K);
  r,K:=RootsInSplittingField(x^2-t5);
  sZ22[[1,0,0,0]]:=r[1][1];

  KK<x>:=PolynomialRing(K);
  r,K:=RootsInSplittingField(x^2-t7);
  sZ22[[0,1,0,0]]:=r[1][1];



  sZ22[[0,0,1,1]]:=sZ22[[0,0,1,0]]/(sZ22[[0,0,0,1]]*Rac[3]); //th2

  sZ22[[1,0,0,1]]:=( sZ22[[0,0,0,0]]*sZ22[[0,0,0,1]] -
         sZ22[[0,0,1,1]]*sZ22[[0,0,1,0]] ) / sZ22[[1,0,0,0]]; //th6
  sZ22[[1,1,0,0]]:=( sZ22[[0,0,0,0]]*sZ22[[1,0,0,0]] -
         sZ22[[0,0,0,1]]*sZ22[[1,0,0,1]] ) / sZ22[[0,1,0,0]]; //th8
  sZ22[[0,1,1,0]]:=( sZ22[[0,0,0,0]]*sZ22[[0,0,1,0]] -
         sZ22[[0,0,1,1]]*sZ22[[0,0,0,1]] ) / sZ22[[0,1,0,0]]; //th9
  sZ22[[1,1,1,1]]:=( sZ22[[0,0,1,1]]*sZ22[[1,0,0,0]] -
         sZ22[[0,0,1,0]]*sZ22[[1,0,0,1]] ) / sZ22[[0,1,0,0]]; //th10

  sZ22[[0,1,0,1]]:=0; //th11
  sZ22[[0,1,1,1]]:=0; //th12
  sZ22[[1,0,1,0]]:=0; //th13
  sZ22[[1,1,1,0]]:=0; //th14
  sZ22[[1,0,1,1]]:=0; //th15
  sZ22[[1,1,0,1]]:=0; //th16

  return sqlvl22_to_lvl2(sZ22, D);
end function;


/* Some precomputations that are used in the functions mumford_to_*
This is for the genus 2 and the level 2.

Let Rac be the list of the roots of an hyperelliptic polynomial f of degree 5.
Assume that the lat two ones are 1 and 0. Note: this is check in
Z2_from_Rosenhain_fldfin.

// TODO change the name of this function, it doesn't do what its name is.
// TODO pour cette fonction, on a vraiment besoin d'avoir Rac[4]=1, et Rac[5]=0. Je suis sur que l'on peut la programmer dans le cas general. Bon on en aura peut etre encore besoin dans Z2_from_Rosenhain_fldfin. A verifier.
 */
function theta_point_from_ros(Rac,precomp: init:="all")
  Z2:=Z2_from_Rosenhain_fldfin(Rac,precomp["D","D"]);
  P0:=init_theta_null_point(Z2: precomp:=precomp, init:=init);

  sthc:=lvl2_to_sqlvl22(P0);
  sth:=AssociativeArray();
  sth[[0,1,0,1]]:=sthc[1]/(sthc[5]*Rac[1]*(Rac[1]-Rac[3])); // th11
  sth[[0,1,1,1]]:=sthc[3]/(sthc[5]*Rac[2]*(Rac[2]-Rac[3])); // th12
  sth[[1,0,1,0]]:=sthc[10]/(sthc[5]*(Rac[3]-1)); // th13
  sth[[1,1,1,0]]:=sthc[10]/(sthc[8]*Rac[3]); // th14
  sth[[1,0,1,1]]:=sthc[6]/(sthc[10]*(Rac[3]-Rac[2])*(Rac[3]-Rac[1])); // th15
  alpha:=sthc[3]/(sthc[1]*sthc[10]*(Rac[3]-Rac[2])*Rac[2]*(Rac[1]-1));

  sth[[1,1,1,1]]:=sthc[10]*alpha;
  sth[[0,0,1,1]]:=sthc[2]*alpha;
  sth[[0,0,1,0]]:=sthc[3]*alpha;
  sth[[0,1,1,0]]:=sthc[9]*alpha;
  sth[[0,0,0,1]]:=sthc[4]*alpha;
  sth[[0,0,0,0]]:=sthc[1]*alpha;
  sth[[0,1,0,0]]:=sthc[7]*alpha;
  sth[[1,1,0,0]]:=sthc[8]*alpha;
  sth[[1,0,0,0]]:=sthc[5]*alpha;
  sth[[1,0,0,1]]:=sthc[6]*alpha;

  precompH:=precomp["H"];
  precompH["sqlvl22"]:=sthc;
  precompH["partial_sth"]:=sth;
  precompH["P0"]:=P0;
  precomp["H"]:=precompH;
  return P0,precomp;
end function;





//**** Mumford -> Theta ****//

/*
Let mumford=[u,v] be the mumford coordinates of a point of an hyperelliptic
curve given
  by  y^2 = f(x) = prod_{r in Rac} (x-r).
Assume that degree(f)=5
Assume that degree(u)=2

This function compute the squares of Y_lj as defined in Wamelen.
 */
function mumford_to_sY(mumford,precomp)
  u:=mumford[1]; v:=mumford[2];

  Rac:=precomp["HK","HRos"];
  assert #Rac eq 5;
  assert Coefficient(u,2) eq 1;

  v1:=Coefficient(v,1);
  v0:=Coefficient(v,0);

  x1x2:=Coefficient(u,0);
  x1px2:=-Coefficient(u,1);

  x1mx2s:=x1px2^2-4*x1x2;

  if x1mx2s eq 0 then
    // x1=x2  => y1=y2 so x,y are rational
    x:=-Coefficient(u,1)/2;
    y:=v1*x+v0;
    assert y ne 0; // otherwise we would have the double of a 2 torsion point

    K:=Parent(v1);
    sY:=ZeroMatrix(K,5,5);
    for l in [1..4] do
    for m in [(l+1)..5] do
      ijk:=Setseq({1..5} diff {l,m});
      s:=Rac[ijk[1]] + Rac[ijk[2]] + Rac[ijk[3]];
      sp:=Rac[ijk[1]]*Rac[ijk[2]] +
    Rac[ijk[2]]*Rac[ijk[3]] +
    Rac[ijk[3]]*Rac[ijk[1]];
      p:=Rac[ijk[1]] * Rac[ijk[2]] * Rac[ijk[3]];
      assert y^2 eq (x-Rac[l]) * (x-Rac[m]) * (x^3-s*x^2+sp*x-p);

      num0:=Rac[l]*Rac[m] * ( sp - s*2*x + 3*x^2 );
      num1:=-(Rac[l] + Rac[m]) * ( p - s*x^2 + 2*x^3);
      num2:=p*2*x - sp*x^2 + x^4;
      den:= 2 * y * (x-Rac[l]) * (x-Rac[m]);
      assert den ne 0;

      sY[l,m]:=((x-Rac[l])^2 * (x-Rac[m])^2 * (num0+num1+num2) / den)^2;

      sY[m,l]:=sY[l,m];
    end for;
    end for;

  else

    v1v0:=v1*v0;
    v1s:=v1^2;
    v0s:=v0^2;

    x1x2s:=x1x2^2;

    x1spx2s:=x1px2^2-2*x1x2;
    x1cpx2c:=x1spx2s*x1px2-x1x2*x1px2;
    x1qpx2q:=x1spx2s^2-2*x1x2s;


    y1y2:=v1s*x1x2+v1v0*x1px2+v0s;

    K:=Parent(v1);
    sY:=ZeroMatrix(K,5,5);
    for l in [1..4] do
    for m in [(l+1)..5] do

      coeff:=Rac[l]^2*Rac[m]^2;
      num2_0:=coeff * ( v1s*x1spx2s + 2*v1v0*x1px2 + 2*v0s);
      coeff:=-2*Rac[l]*Rac[m]*(Rac[l]+Rac[m]);
      num2_1:=coeff * ( v1s*x1px2*x1x2 + 2*v1v0*2*x1x2 + v0s*x1px2);
      coeff:=(Rac[l]+Rac[m])^2 + 2*Rac[l]*Rac[m];
      num2_2:=coeff * ( 2*v1s*x1x2s + 2*v1v0*x1x2*x1px2 + v0s*x1spx2s);
      coeff:=-2*(Rac[l]+Rac[m]);
      num2_3:=coeff*(v1s*x1x2s*x1px2+2*v1v0*x1x2*x1spx2s+v0s*x1cpx2c);
      num2_4:=v1s*x1x2s*x1spx2s+2*v1v0*x1x2*x1cpx2c+v0s*x1qpx2q;
      num2:=num2_0 + num2_1 + num2_2 + num2_3 + num2_4;
      num:=num2 - 2*y1y2*(x1x2-Rac[l]*x1px2+Rac[l]^2)
                  *(x1x2-Rac[m]*x1px2+Rac[m]^2);
      sY[l,m]:=num/x1mx2s;

      sY[m,l]:=sY[l,m];

    end for;
    end for;

  end if;

  return sY;
end function;

/*
Let mumford=[u,v] be the mumford coordinates of a point of an hyperelliptic
curve of genus 2.

Compute the squares of the theta functions of level (2,2) which correspond to
the point (u,v). Return them as an associative array indexed by (Z/2Z)^4.

Assume that u is of degree 2!
 */
function mumford_to_sqlvl22(mumford,precomp)
  u:=mumford[1]; v:=mumford[2];

  ros:=precomp["HK","HRos"];
  assert ros[4] eq 1;
  assert ros[5] eq 0;
  assert #ros eq 5;

  assert Degree(u) eq 2;
  assert Coefficient(u,2) eq 1;

  sthc:=precomp["HK","sqlvl22"];
  psth:=precomp["HK","partial_sth"];
  F:=Universe([Coefficient(u,i):i in [0..2]]);
  Embed(Universe(ros),F);
  evalu:=[Evaluate(u,F!a) : a in ros];

  if 0 in evalu then
//The non generic case where the divisor has a ramification point in its support
    k:=Parent(Coefficient(u,0));

    Ab:=AbelianGroup([2,2,2,2]);
    thc2 := AnalyticThetaNullPoint(2,AssociativeArray(Ab), Ab,2 : level2:=true);

    thc2`coord[Ab![0,0,0,0]]:=sthc[1];
    thc2`coord[Ab![0,0,1,1]]:=sthc[2];
    thc2`coord[Ab![0,0,1,0]]:=sthc[3];
    thc2`coord[Ab![0,0,0,1]]:=sthc[4];
    thc2`coord[Ab![1,0,0,0]]:=sthc[5];
    thc2`coord[Ab![1,0,0,1]]:=sthc[6];
    thc2`coord[Ab![0,1,0,0]]:=sthc[7];
    thc2`coord[Ab![1,1,0,0]]:=sthc[8];
    thc2`coord[Ab![0,1,1,0]]:=sthc[9];
    thc2`coord[Ab![1,1,1,1]]:=sthc[10];
    thc2`coord[Ab![0,1,0,1]]:=k!0;
    thc2`coord[Ab![0,1,1,1]]:=k!0;
    thc2`coord[Ab![1,0,1,0]]:=k!0;
    thc2`coord[Ab![1,1,1,0]]:=k!0;
    thc2`coord[Ab![1,0,1,1]]:=k!0;
    thc2`coord[Ab![1,1,0,1]]:=k!0;


    points:={*[x[1],Evaluate(v,x[1])]^^x[2] : x in RootsInSplittingField(u) *};
    points:=[ x : x in points];

    t:= MumfordToLevel2ThetaPoint(2, ros, thc2, points);

    sth:=AssociativeArray();
    for e in Ab do
      sth[Eltseq(e)]:=k!(t`coord[e]);
    end for;
    return sth;
  end if;

  // The generic case
  sth:=AssociativeArray();

  sth[[1,1,0,1]]:=1; // th16

  sth[[0,1,0,1]]:=evalu[1]*psth[[0,1,0,1]]; // th11
  sth[[0,1,1,1]]:=evalu[2]*psth[[0,1,1,1]]; // th12
  sth[[1,0,1,0]]:=evalu[4]*psth[[1,0,1,0]]; // th13
  sth[[1,1,1,0]]:=evalu[5]*psth[[1,1,1,0]]; // th14
  sth[[1,0,1,1]]:=evalu[3]*psth[[1,0,1,1]]; // th15

  sY:=mumford_to_sY(mumford,precomp);

  sth[[1,1,1,1]]:=sY[1,2]*psth[[1,1,1,1]]/(evalu[1]*evalu[2]);
  sth[[0,0,1,1]]:=sY[1,3]*psth[[0,0,1,1]]/(evalu[1]*evalu[3]);
  sth[[0,0,1,0]]:=sY[1,4]*psth[[0,0,1,0]]/(evalu[1]*evalu[4]);
  sth[[0,1,1,0]]:=sY[1,5]*psth[[0,1,1,0]]/(evalu[1]*evalu[5]);
  sth[[0,0,0,1]]:=sY[2,3]*psth[[0,0,0,1]]/(evalu[2]*evalu[3]);
  sth[[0,0,0,0]]:=sY[2,4]*psth[[0,0,0,0]]/(evalu[2]*evalu[4]);
  sth[[0,1,0,0]]:=sY[2,5]*psth[[0,1,0,0]]/(evalu[2]*evalu[5]);
  sth[[1,1,0,0]]:=sY[3,4]*psth[[1,1,0,0]]/(evalu[3]*evalu[4]);
  sth[[1,0,0,0]]:=sY[3,5]*psth[[1,0,0,0]]/(evalu[3]*evalu[5]);
  sth[[1,0,0,1]]:=sY[4,5]*psth[[1,0,0,1]]/(evalu[4]*evalu[5]);

  return sth;
end function;



/*
Let mumford=[u,v] be the mumford coordinates of a point of an hyperelliptic
curve.

Compute the theta functions of level 2 which correspond to the point (u,v).
 */
function mumford_to_lvl2(mumford,precomp)
  u:=mumford[1];
  v:=mumford[2];

  if Degree(u) eq 0 then
    return init_theta_point(precomp["HK","P0"]`coord);
  elif Degree(u) eq 1 then
    k:=Parent(Coefficient(u,0));

//points:={*[x[1],Evaluate(v,x[1])]^^x[2] : x in RootsInSplittingField(u) *};
//points:=[ x : x in points];
// since u is of degree 1:
    assert Coefficient(u,1) eq 1;
    points:=[[-Coefficient(u,0),k!v]];
    //points:=[[-Coefficient(u,0),k!Coefficient(v,0)]];

    Ab:=AbelianGroup([2,2,2,2]);
    sthc:=precomp["HK","sqlvl22"];
    thc2:= AnalyticThetaNullPoint(2,AssociativeArray(Ab),Ab,2 : level2:=true);

    thc2`coord[Ab![0,0,0,0]]:=sthc[1];
    thc2`coord[Ab![0,0,1,1]]:=sthc[2];
    thc2`coord[Ab![0,0,1,0]]:=sthc[3];
    thc2`coord[Ab![0,0,0,1]]:=sthc[4];
    thc2`coord[Ab![1,0,0,0]]:=sthc[5];
    thc2`coord[Ab![1,0,0,1]]:=sthc[6];
    thc2`coord[Ab![0,1,0,0]]:=sthc[7];
    thc2`coord[Ab![1,1,0,0]]:=sthc[8];
    thc2`coord[Ab![0,1,1,0]]:=sthc[9];
    thc2`coord[Ab![1,1,1,1]]:=sthc[10];
    thc2`coord[Ab![0,1,0,1]]:=k!0;
    thc2`coord[Ab![0,1,1,1]]:=k!0;
    thc2`coord[Ab![1,0,1,0]]:=k!0;
    thc2`coord[Ab![1,1,1,0]]:=k!0;
    thc2`coord[Ab![1,0,1,1]]:=k!0;
    thc2`coord[Ab![1,1,0,1]]:=k!0;

    t := MumfordToLevel2ThetaPoint(2, precomp["HK","HRos"], thc2, points);

    return AnalyticToAlgebraicThetaPoint(2,t,precomp["D","D"]);
  else // Degree(u) eq 2
    sth:=mumford_to_sqlvl22(mumford,precomp);
    return init_theta_point(sqlvl22_to_lvl2(sth,precomp["D","D"]));
  end if;
end function;

//**** precomputation for the conversion ****//

procedure precompute_H(H,~precomp)
  IndentPush();
    vprint AVIsogenies, 3: "Compute Rosenhain form:";
    vtime AVIsogenies, 3: Hn,Ros,phi,abcdw:=RosenhainForm(H);
    precompH:=AssociativeArray();
    precompH["H"]:=H; precompH["Hn"]:=Hn;
    precompH["HRos"]:=Ros; precompH["Hphi"]:=phi;
    precompH["Habcdw"]:=abcdw;
    precomp["H"]:=precompH;
    vprint AVIsogenies, 3: "Computing theta null point"; // of level 2
    vtime AVIsogenies, 3: P0,precomp:=theta_point_from_ros(Ros,precomp);
  IndentPop();
end procedure;

// TODO commentaires
procedure precompute_Hext(extension,~precomp: mycomposite:=false)
  IndentPush();
    Hn:=precomp["H","Hn"]; H:=precomp["H","H"]; phi:=precomp["H","Hphi"];
    P0coord:=precomp["H","P0"]`coord;
    K1:=Parent(P0coord[Rep(Keys(P0coord))]);
    K2:=extension;
    // field were live the points in the rosenhain
    K3:=BaseField(Hn);
    if Category(K2) eq RngIntElt then
      //if K2 is given as a degree rather than a field, we construct it as
      //a subfield of the composition extension. This way we don't need to
      //do an Embedding, and this should be faster
      k0:=LCM(Degree(K1),K2);
      vprint AVIsogenies,4: "Degrees. Ros:", Degree(K3), "P0:", Degree(K1), "Points:", K2, "Composition:",k0, "(K0 directly constructed)";
      K0:=ext<BaseField(H)|k0: Optimize:=false>;
      K2:=sub<K0|K2: Optimize:=false>;
    else
      k0:=LCM(Degree(K1),Degree(K2));
      vprint AVIsogenies,4: "Degrees. Ros:", Degree(K3), "P0:", Degree(K1), "Points:", Degree(K2), "Composition:",k0;
      if mycomposite then
      vtime AVIsogenies, 4 : K0,phi0:=MyCompositeField(K1,K2);
      else
      vtime AVIsogenies, 4 : K0:=TowerOfField([K2,K1]: Optimize:=false);
      end if;
    end if;

    precompHK:=AssociativeArray();
    H0:=BaseChange(H,K0);
    if mycomposite then
      a,b,c,d,w:=Explode([i@phi0: i in precomp["H","Habcdw"]]);
      precompHK["HRos"]:=[i@phi0: i in precomp["H","HRos"]];
      precompHK["sqlvl22"]:=[i@phi0: i in precomp["H","sqlvl22"]];
      precompHK["partial_sth"]:=ConvertArray(precomp["H","partial_sth"],phi0);
      precompHK["P0"]:=init_theta_null_point(
         ConvertArray(precomp["H","P0"]`coord,phi0) );
    else
      //phieqs:=DefiningEquations(phi);
      //Hn:=BaseChange(Hn,K0);
      //phi:=map< H0 -> Hn |phieqs: Check:=false>;
      //J:=Jacobian(Hn);
      a,b,c,d,w:=Explode(precomp["H","Habcdw"]);
      precompHK["HRos"]:=precomp["H","HRos"];
      precompHK["sqlvl22"]:=precomp["H","sqlvl22"];
      precompHK["partial_sth"]:=precomp["H","partial_sth"];
      precompHK["P0"]:=precomp["H","P0"];
    end if;
      Hn,phi:=Transformation(H0,[a,b,c,d],w);
      J:=Jacobian(Hn);
      precompHK["Hphi"]:=phi;
      precompHK["Habcdw"]:=[a,b,c,d,w];
      vtime AVIsogenies, 4 : PsInf:=PointsAtInfinity(H0);
      precompHK["Hinfinity"]:=PsInf;
      precompHK["HnJ"]:=J; precompHK["K2"]:=K2;
      precomp["HK"]:=precompHK;
  IndentPop();
end procedure;

function mumford_to_theta(P,precomp)
  Q:=JacHypMapFromCrvHypMap(P,precomp);
  R:=mumford_to_lvl2(Q,precomp);
  return R,Q;
end function;

procedure precompute_mumford_to_theta(~precomp,J,K)
  IndentPush();
  g:=Dimension(J); H:=Curve(J);
  if not IsDefined(precomp,"D") then
    vprint AVIsogenies, 3: "-- Precomputations for D";
    D:=AbelianGroup([2: i in [1..g]]);
    vtime AVIsogenies, 3: precompute_D(D,~precomp);
  end if;
  if not IsDefined(precomp,"H") then
    vprint AVIsogenies, 3: "-- Precomputations for H";
    vtime AVIsogenies, 3: precompute_H(H,~precomp);
  end if;

  if not IsDefined(precomp,"HK") then
    vprint AVIsogenies, 3: "-- Precomputations for Hext";
    vtime AVIsogenies, 3: precompute_Hext(K,~precomp);
  else
    P0coord:=precomp["H","P0"]`coord;
    K1:=Parent(P0coord[Rep(Keys(P0coord))]);
    if Category(K) eq RngIntElt then kk:=K; else kk:=Degree(K); end if;
      k0:=LCM(Degree(K1),kk);
      K0:=Degree(BaseField(precomp["HK","HnJ"]));
    if K0 mod k0 ne 0 then
      vprint AVIsogenies, 3: "-- We have to recompute Hext for a different field; old:", K0, "new:", k0;
      vtime AVIsogenies, 3: precompute_Hext(K,~precomp);
    end if;
  end if;
  IndentPop();
end procedure;

//**** Theta to Mumford  ****//
/*
g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
th2 :: ThetaPoint_analytic
intrinsic Level2ThetaPointToMumford(g::RngIntElt,a::SeqEnum,thc2::Rec,th2::Rec) -> Rec
*/
function lvl2_to_mumford(point,precomp)
  g:=2;
  Rac:=precomp["H","HRos"];
  P0:=precomp["H","P0"];
  DDg:=AbelianGroup([2: i in [1..2*2]]);
  P0an:=AlgebraicToAnalyticThetaNullPoint(g,P0,DDg);
  Pan:=AlgebraicToAnalyticThetaPoint(g,P0,point,DDg);
  return Level2ThetaPointToMumford(2,Rac,P0an,Pan);
end function;
