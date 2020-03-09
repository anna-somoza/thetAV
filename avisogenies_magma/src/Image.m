/* Computing the image of a point in theta coordinates
* - Damien Robert
*/

declare verbose AVIsogenies, 8;

import "Arithmetic.m" : init_theta_point, init_theta_null_point, precompute_D, get_nonzero_coord, compare_points, print_point;
import "libav.m" : GetCastMinField, SumOfSquares;
import "rosenhain.m" : theta_null_to_rosenhain, precompute_mumford_to_theta, \
    precompute_H, mumford_to_lvl2,lvl2_to_mumford;
import "Isogenies.m" : get_coeff_structure, compute_all_theta_torsion, JacobianOrTwist;

// the coefficients we need to compute the image of x are exactly what we would do to compute an isogeny in dimension g+1, except there is no projective factor for x. For now we cheat and we use the code already present in Isogenies.m to get the coefficients.
function get_image_coeff_structure(l,g)
  Dll:=AbelianGroup([l+1: i in [1..g+1]]);
  return get_coeff_structure(Dll);
end function;

function image_level_formula(D,Dl)
  Inv:=Invariants(D); g:=#Inv; n:=Inv[1];
  assert #Seqset(Inv) eq 1;// we assume that D=[n,n,n,n,...]

  Invl:=Invariants(Dl); l:=Invl[1];
  assert #Seqset(Invl) eq 1;// we assume that Dl=[l,l,l,l,....]
  assert #Invl eq g;

  assert Gcd(l,n) eq 1; // assert that n and l are coprime
  // assert IsPrime(l); // TODO is this needed?

  sumsquares:=SumOfSquares(l); r:=#sumsquares;
  A:=AbelianGroup([l: i in [1..r]]);
  B:=AbelianGroup([n: i in [1..r]]);

  if r eq 1 then
    a:=Explode(sumsquares);
    phi:=hom<A -> A | [a*A.1]>;
    phi2:=hom<B -> B | [a*B.1]>;
    //phi2 is used to compute a section of phi
  elif r eq 2 then
    a,b:=Explode(sumsquares);
    phi:=hom<A -> A | [a*A.1+b*A.2, -b*A.1+a*A.2]>;
    phi2:=hom<B -> B | [a*B.1+b*B.2, -b*B.1+a*B.2]>;
  elif r eq 4 then
    a,b,c,d:=Explode(sumsquares);
    phi:=hom<A -> A | [ a*A.1 + b*A.2 + c*A.3 + d*A.4,
                       -b*A.1 + a*A.2 - d*A.3 + c*A.4,
                       -c*A.1 + d*A.2 + a*A.3 - b*A.4,
                       -d*A.1 - c*A.2 + b*A.3 + a*A.4 ]>;
    phi2:=hom<B -> B | [ a*B.1 + b*B.2 + c*B.3 + d*B.4,
                        -b*B.1 + a*B.2 - d*B.3 + c*B.4,
                        -c*B.1 + d*B.2 + a*B.3 - b*B.4,
                        -d*B.1 - c*B.2 + b*B.3 + a*B.4 ]>;
  else
    error "Cardinality of sumsquares not supported";
  end if;

  vprint AVIsogenies, 7: "Computing Kernel";
  Kset:={A!i: i in Kernel(phi)};

  return Kset, phi, phi2;
end function;

// From the result of IsogenieG2, one can compute the image of a point
// point: point in Mumford whose image we want
// K: the generators of subgroup in Mumford coordinates for the isogeny
//// ltors: the points of K in theta coordinates
// coeffs: the corrective projective factors for ltors
intrinsic ImagePoint(point::JacHypPt,l::RngIntElt,K::SeqEnum :
  proj_coordinate:=0,
  curve_to_invariants:=func<x|G2Invariants(x)>,
  invariants_to_curve:=HyperellipticCurveFromG2Invariants)
  -> ThetaPoint,ThetaNullPoint
  {The image of a point via the corresponding isogeny}

  g:=#K;
  assert g eq 2;
  precomp:=AssociativeArray();
  D:=AbelianGroup([2,2]);
  precompute_D(D,~precomp);
  J:=Parent(point);
  H:=Curve(J);
  FK:=BaseField(Universe(K));
  precompute_mumford_to_theta(~precomp,H,FK);
  P0:=precomp["H","P0"];
  frob:=FrobeniusPoly(H);

  Dl:=AbelianGroup([l,l]);
  gen:=[Dl.i: i in [1..g]] cat [Dl.i+Dl.j: i,j in [1..g] | i lt j];
  abstract_coeff_x:=get_image_coeff_structure(l,g);
  Dll:=Universe(abstract_coeff_x);
  function inc1(i)
    el:=Eltseq(i) cat [0];
    return Dll!el;
  end function;
  function proj1(i)
    el:=Eltseq(i)[1..g];
    return Dl!el;
  end function;

  x:=mumford_to_lvl2(point,precomp);
  L:=AssociativeArray();
  L[Dll.0]:=P0;
  for i in [1..g] do
    L[Dll.i]:=mumford_to_lvl2(K[i],precomp);
  end for;
  L[Dll.(g+1)]:=x;
  for i in [1..g-1] do
    for j in [i+1..g] do
      L[Dll.i+Dll.j]:=mumford_to_lvl2(K[i]+K[j],precomp);
    end for;
  end for;
  for j in [1..g] do
    L[Dll.(g+1)+Dll.j]:=mumford_to_lvl2(point+K[j],precomp);
  end for;
  L:=compute_all_theta_torsion(L);

  l1:=l div 2; l11:=l1 +1;
  coeffs1:=[];
  for j in [1..#gen] do
    i:=gen[j];
    l11P:=L[inc1(Dl!Eltseq(l11*i))]`coord;
    l1P:=L[inc1(Dl!Eltseq(l1*i))]`coord;
    i0:=get_nonzero_coord(l11P);
    //beta ne 0 by definition, so alpha should not be equal to 0 either
    coeffs1[j]:=l1P[-i0]/l11P[i0];
  end for;
  coeffs2:=[];
  for i in [1..g] do
    lxP:=L[l*Dll.i+Dll.(g+1)]`coord;
    //print i,print_point(lxP);
    i0:=get_nonzero_coord(lxP);
    //beta ne 0 by definition, so alpha should not be equal to 0 either
    coeffs2[i]:=x`coord[i0]/lxP[i0];
    //cf Section 4.2, we need to correct by \lambda_i^(l(l-1))
    coeffs2[i]:=coeffs2[i]/coeffs1[i]^(l-1);
  end for;
  // we simulate a coeff of 1 for x
  coeffs:=coeffs1[1..g] cat [1] cat coeffs1[g+1..#coeffs1] cat coeffs2;
  //print coeffs;

  //Now we do the level formula, which look at lot like an isogeny level formula but for g+1.
  Kset,phi,phi2:=image_level_formula(D,Dl);
  //phi2:=precomp["l","phi2"];
  //phi:=precomp["l","phi"];
  B:=Domain(phi2); //Z/nZ^r
  squares:=SumOfSquares(l);
  r:=#squares;

  res:=AssociativeArray(D);
  resx:=AssociativeArray(D);
  preims:=AssociativeArray(D);
  for i in D do
    res[i]:=0;
    resx[i]:=0;
    I:=Eltseq(i);
    preim:=[D.0: i in [1..r]];
    for z in [1..g] do
      preimz:=Eltseq((B!([I[z]] cat [proj_coordinate: zz in [1..r-1]]))@@phi2);
      // preimz is a preimage on the z coordinate
      preim:=[ preim[i]+preimz[i]*D.z: i in [1..r]];
    end for;
    preims[i]:=preim;
  end for;
  preimx:=squares;

  for tuple in CartesianPower(Kset,g) do
    k:=[ &+[Eltseq(tuple[z])[i]*Dl.z: z in [1..g]]: i in [1..r]];
    k:=[inc1(z): z in k];
    kx:=[squares[i]*Dll.(g+1)+k[i]: i in [1..r]];
    s1:=Eltseq(&+[abstract_coeff_x[z]: z in k]);
    s1x:=Eltseq(&+[abstract_coeff_x[z]: z in kx]);
    s:=[]; sx:=[];
    for i in [1..#s1] do
      test,ss:=IsDivisibleBy(s1[i],l);
      assert test;
      test,ssx:=IsDivisibleBy(s1x[i],l);
      Append(~s,ss);
      Append(~sx,ssx);
    end for;
    // "-------";
    // k,kx,s;
    c:=&*[coeffs[i]^s[i]: i in [1..#s]];
    cx:=&*[coeffs[i]^sx[i]: i in [1..#s]];
    //print s,c;

    //print "-----";
    //kx;
    for i in D do
      //print i, sx;
      //print "c",c,"coeff", &*[L[kx[z]]`coord[preims[i,z]]: z in [1..r]];

      res[i]+:=c * &*[L[k[z]]`coord[preims[i,z]]: z in [1..r]];
      resx[i]+:=c * &*[L[kx[z]]`coord[preims[i,z]]: z in [1..r]];
    end for;
  end for;
  //print coeffs;

  y:=init_theta_point(resx);
  Q0:=init_theta_null_point(res);

  ros:=theta_null_to_rosenhain(Q0);
  AK<X>:=PolynomialRing(Universe(ros));
  f:=&*[X-i: i in ros];
  newH:=HyperellipticCurve(f);
  newAI:=curve_to_invariants(newH);
  nInv:=GetCastMinField(newAI);
  ChangeUniverse(~nInv,BaseRing(J));
  Jnew:=Jacobian(invariants_to_curve(nInv));
  Jnew:=JacobianOrTwist(Jnew,frob);

  precomp1:=AssociativeArray();
  D:=Universe(Keys(y`coord));
  precompute_D(D,~precomp1);
  precompute_H(Curve(Jnew),~precomp1);
  umumford,vmumford:=lvl2_to_mumford(y,precomp1);
  ymumford:=<umumford,vmumford>;

  return ymumford, Jnew,y, Q0;
end intrinsic;
