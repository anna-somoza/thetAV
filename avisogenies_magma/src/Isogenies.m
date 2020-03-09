/* Computing isogenies in theta coordinates
* - Damien Robert
*/

declare verbose AVIsogenies, 8;

import "Arithmetic.m" : diff_add_PQ, diff_add, IncludeSubgroup, \
    init_theta_null_point,  precompute_D, precompute_theta_point, \
    precompute_inverses, get_nonzero_coord, three_add, print_point;
import "libav.m" : GetCastMinField, SumOfSquares, InvertListMontgomery;
import "libseq.m" : CopyArray;
import "rosenhain.m" : theta_null_to_rosenhain, precompute_mumford_to_theta, \
    precompute_H;
import "Torsion.m" : set_l, precompute_abstract_subgroups, CardFromFrob, \
    mumford_subgroups_to_theta;
import "carac2.m" : RationallyIsogenousCurvesG2_carac2;

//**** Computing the torsion ****//

/* From e_i+e_j, compute all the points
\epsilon_1 e_1 + ... + \epsilon_g e_g
where the e_i are generators of a symplectic subgroup of the l-torsion.
*/

function init_all_theta_torsion(L)
  Dl:=Universe(Keys(L));
  P0:=L[Dl.0];
  Inv:=Invariants(Dl);
  g:=#Inv;

  procedure recursion(g,~toadd,~L)
    if g eq 2 then
      toadd:=[Dl.1+Dl.2];
    end if;
    if g gt 2 then
      toadd:=[];
      recursion(g-1,~toadd,~L);
      for i in toadd do
        i1:=Dl.(Rep([j: j in [1..g-1] |Eltseq(i)[j] ne 0]));
        //i1 is an element in the support of i
        i2:=i-i1;
        newi:=i+Dl.g;
        L[newi]:=three_add(L[i1],L[i2],L[Dl.g],L[i2+Dl.g],L[i1+Dl.g],L[i],P0);
      end for;
      toadd:=toadd cat [i+Dl.g: i in toadd] cat [Dl.i +Dl.g : i in [1..g-1]];
    end if;
  end procedure;
  toadd:=[];
  recursion(g,~toadd,~L);
  return L;
end function;

/*
From the points \epsilon_1 e_1 + ... + \epsilon_g e_g where the e_i are
generators of a symplectic subgroup of the l-torsion.
Compute all the subgroup with differential additions

L is an associative array indexed by the abelian group (Z/lZ)^g.
For each elements a=(a_1,...,a_g) in this group, we set L[e] :: ThetaPoint to be
the point a_1 e_1 + ... + a_g e_g
After computing all these elements, we return the completed L

isprefilled:=true => when L is already computed up to projective factors

Warning: if g \geq 3, then e_1+e_2+e_3 *HAS* to be computed as a Riemann
Relations with e_1, e_2, e_3, e_1+e_2, ... e_2+e_3.
 */
function compute_all_theta_torsion(L: isprefilled:=false)
  Dl:=Universe(Keys(L));
  P0:=L[Dl.0];
  Inv:=Invariants(Dl);
  g:=#Inv;

  for i in [1..g] do
    precompute_theta_point(~L[Dl.i],P0: init:="dadd",isQ:=true,onlyprod:=false);
  end for;

  L:=init_all_theta_torsion(L);

  for i in [1..g] do
    to_add:={Dl.0}; P:=L[Dl.i];
    for j in [1..g] do
      if j lt i then
        to_add:={alpha*Dl.j+beta: alpha in [0..Inv[j]-1], beta in to_add};
      elif j eq i then
      else
        to_add:={alpha*Dl.j+beta: alpha in [0..1], beta in to_add};
      end if;
    end for;
    //to_add = { alpha + \epsilon e_{i+1} + \epsilon e_{i+2} +...}
    //where alpha is any element with support in [e_1, ..., e_{i-1}]

    for k in [2..Inv[i]-1] do
      precompute_inverses(~L);
      for l in to_add do
        if isprefilled then
          L[l+k*Dl.i]:=diff_add_PQ( L[l+k*Dl.i] , L[l+(k-1)*Dl.i] ,
                                    P,L[l+(k-2)*Dl.i] , P0);
        else
          L[l+k*Dl.i]:= diff_add(L[l+(k-1)*Dl.i],P,L[l+(k-2)*Dl.i],P0);
          precompute_theta_point( ~L[l+k*Dl.i] , P0
                                  : init:="dadd", isQ:=false, onlyprod:=true);
        end if;
      end for;
    end for;
  end for;
  return L;
end function;

/*
P, Q :: ThetaPoint   are l-torsion points
PQ :: ThetaPoint  is for P+Q
P0 :: ThetaNullPoint
Dl ::  is the abelian group  (Z/lZ)^g.

returns all l-torsion points in an associative array L indexed by Dl
*/
function torsion_g2(Dl,P,Q,PQ,P0)
  assert P0`g eq 2;

  L:=AssociativeArray();
  L[Dl.0]:=P0;
  L[Dl.1]:=P;
  L[Dl.2]:=Q;
  L[Dl.1+Dl.2]:=PQ;
  return compute_all_theta_torsion(L);
end function;



/*
Find the "projective coefficients" that we get when computing pseudo-addition
for computing all points in a subgroup Dl.
See lemma 3.9 in Lubicz, Robert (computing isogenies between abelian varieties)

Dl is represented as an abelian group. For instance Dl is (Z/lZ)^g.
We assume that we know the points Dl.i and Dl.i+Dl.j. Let gen be this list.
For each element e of Dl, let r[e] be the projective coefficient. It is
represented as an element of a free abelian group A. Each coefficient of this
element is the power that appears in lemma 3.9 for the corresponding elements
of gen.

 */
function init_coeff_structure(coeffs)
  Dl:=Universe(Keys(coeffs));
  Inv:=Invariants(Dl);
  g:=#Inv;

  procedure recursion(g,~toadd,~coeffs)
    if g eq 2 then
      toadd:=[Dl.1+Dl.2];
    end if;
    if g gt 2 then
      toadd:=[];
      recursion(g-1,~toadd,~coeffs);
      for i in toadd do
        i1:=Dl.(Rep([j: j in [1..g-1] |Eltseq(i)[j] ne 0]));
        //i1 is an element in the support of i
        i2:=i-i1;
        newi:=i+Dl.g;
        coeffs[newi]:=-coeffs[i1]-coeffs[i2]-coeffs[Dl.g]+coeffs[i2+Dl.g]+coeffs[i1+Dl.g]+coeffs[i];
      end for;
      toadd:=toadd cat [i+Dl.g: i in toadd] cat [Dl.i +Dl.g : i in [1..g-1]];
    end if;
  end procedure;
  toadd:=[];
  recursion(g,~toadd,~coeffs);
  return coeffs;
end function;

/*
we can do that faster when we have computed the coeffs corresponding to
  D.1+D.2+D.3...
*/
function get_coeff_structure(Dl)
  Inv:=Invariants(Dl); g:=#Inv;

  gen:=[Dl.i: i in [1..g]] cat [Dl.i+Dl.j: i,j in [1..g] | i lt j];
  A:=AbelianGroup([0: i in [1..#gen]]);
  r:=AssociativeArray(Dl);
  r[Dl.0]:=A.0;
  for i in [1..#gen] do r[gen[i]]:=A.i; end for;
  r:=init_coeff_structure(r);

  for i in [1..g] do
    to_add:={Dl.0};
    for j in [1..g] do
      if j lt i then
        to_add:={alpha*Dl.j+beta: alpha in [0..Inv[j]-1], beta in to_add};
      elif j eq i then // TODO are we sure we do nothing
      else
        to_add:={alpha*Dl.j+beta: alpha in [0..1], beta in to_add};
      end if;
    end for;
    for k in [2..Inv[i]-1] do
      for l in to_add do
        r[l+k*Dl.i]:= 2*r[l+(k-1)*Dl.i]+2*r[Dl.i]-r[l+(k-2)*Dl.i];
      end for;
    end for;
  end for;
  return r,gen;
end function;

//**** Mapping for changing level ****//


/*
Let D be the abelian group (Z/nZ)^g and Dl the abelian group (Z/lZ)^g with n
coprime to l.

First decompose l as a sum of r squares. (it can be assumed that r le 4)
Associated to this decomposition is a matrix of M_{r x r}(Z)
This matrix acts on the abelian group A=(z/(nl)Z)^r by the map phi
Then phi acts theoricaly on the matrices in M_{r,g}(z/(nl)Z) and we find the
  kernel K0 of this application.
For each element i of D\subsets M_{r,g}(z/(nl)Z) we compute the premimages of
  [i]       if r=1
  [i,p]     if r=2
  [i,p,p,p] if r=4
where p is usually 0 (see bellow), by the application derived form phi:
  M_{r,g}(z/(nl)Z)  ->  M_{r,g}(z/(nl)Z)

For each element i in D we store the preimages of i as a list of vectors of r
elements in DDl=(z/(nl)Z)^g
preimages is an associative array indexed by elements of D that stores this.


p = proj_coordinate is usualy 0 but is allow to differ since // TODO explain why

return preimage and phi

 */
function level_formula(D,Dl)
  Inv:=Invariants(D); g:=#Inv; n:=Inv[1];
  assert #Seqset(Inv) eq 1;// we assume that D=[n,n,n,n,...]

  Invl:=Invariants(Dl); l:=Invl[1];
  assert #Seqset(Invl) eq 1;// we assume that Dl=[l,l,l,l,....]
  assert #Invl eq g;

  assert Gcd(l,n) eq 1; // assert that n and l are coprime
  // assert IsPrime(l); // TODO this should not be needed

  sumsquares:=SumOfSquares(l); r:=#sumsquares;
  A:=AbelianGroup([n*l: i in [1..r]]);
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


/*
Do some precomputation for computing (l,...,l)-isogenies.
Let D be an abelian group used to index the theta functions.
  For instance D is (Z/nZ)^g

First used level_formula to get the preimage of [i,***] for i in D by the
morphism of M_{r,g}(z/(nl)Z) associated to l.

For each elements in this preimage, the coefficient of the projective factor due to the coordinates being projective and the use of pseudo-addition in the change of level formulae are divisible by l. We compute them and put them in precompl["coeffs"]:=r;
See Cosset, Robert for informations.
*/
procedure precompute_isogenies(D,l,~precomp: save_mem:=0)
  IndentPush();
if not IsDefined(precomp,"l") then
  precomp["l"]:=AssociativeArray();
else
  precompl:=precomp["l"];
  if precompl["l"] ne l then precomp["l"]:=AssociativeArray(); end if;
end if;
  precompl:=precomp["l"];
  precompl["l"]:=l;
  if not IsDefined(precompl,"phi") then
    g:=#Invariants(D);
    Dl:=AbelianGroup([l: i in [1..g]]);

    vprint AVIsogenies, 7: "Computing preimages";
    vtime AVIsogenies, 7: Kset,phi,phi2:=level_formula(D,Dl);
    r:=#Eltseq(Rep(Kset));

    vprint AVIsogenies, 7: "Computing coeffs";
    vtime AVIsogenies, 7: coeffs,gen:=get_coeff_structure(Dl);

    if save_mem lt 1 then
      Inv:=Invariants(D); g:=#Inv;
      Invl:=Invariants(Dl);
      DDl:=AbelianGroup([Inv[i]*Invl[i]: i in [1..g]]); // (Z/lnZ)^g
      inc2:=IncludeSubgroup(Dl,DDl);

      K0:=[ [Eltseq(b)[i]*DDl.1: i in [1..r]]: b in Kset];
      for z in [2..g] do
        K0:=[ [a[i]+Eltseq(b)[i]*DDl.z: i in [1..r]]: a in K0, b in Kset];
      end for;
      precompl["K0"]:=K0;

      r:=AssociativeArray();
      A:=Parent(coeffs[0]);
      vprint AVIsogenies, 7: "Compute the coeffs corresponding to preimages";
      for pre in K0 do
        r[pre]:=A.0;
        s:=&+[coeffs[Eltseq(z@@inc2)]: z in pre];
        // s is l-divisible: get this:
        for i in [1..#Invariants(A)] do
          test,ss:=IsDivisibleBy(Eltseq(s)[i],l);
          assert test;
          r[pre]+:=ss*A.i;
        end for;
      end for;
      precompl["precoeffs"]:=r;
    end if;

    precompl["Kset"]:=Kset;
    precompl["phi"]:=phi;
    precompl["phi2"]:=phi2;
    precompl["coeffs"]:=coeffs;
    precompl["gen"]:=gen;
    precomp["l"]:=precompl;

  end if;
  IndentPop();
end procedure;

procedure precompute_l(D,l,~precomp: range:=[g..2*g] where g is
#Invariants(D), save_mem:=0)
  IndentPush();
  precompute_isogenies(D,l,~precomp: save_mem:=save_mem);
  precompute_abstract_subgroups(~precomp,l,#Invariants(D): range:=range);
  IndentPop();
end procedure;

/*
Let a and ainv be to element such that a*ainv=1
Let powers be a list of elements of Z.
We want to compute relatively quickly a to the power p for each p in power.

Return them as an insociative array indexed by the elements of powers.
 */
 /*
function precomp_power_inv(a,ainv,powers)
    assert a*ainv eq 1;
    list1:=Sort([i: i in powers | i gt 0]);
    list2:=Reverse(Sort([i: i in powers | i lt 0]));

    r:=AssociativeArray();
    r[0]:=1; r[list1[1]]:=a^list1[1];
    if not IsEmpty(list1) then
      for i in [2..#list1] do
        r[list1[i]]:=r[list1[i-1]]*a^(list1[i]-list1[i-1]);
      end for;
    end if;
    if not IsEmpty(list2) then
      r[list2[1]]:=ainv^(-list2[1]);
      for i in [2..#list2] do
        r[list2[i]]:=r[list2[i-1]]*ainv^(list2[i-1]-list2[i]);
      end for;
    end if;
    return r;
end function;
*/

//**** Changing level ****//

/*
It is assumed for this function that some precomputation have been done in a coherent way.

Let ltors be the points of a subgroup of the l-torsion computed in theta functions by compute_all_theta_torsion for instance.
This function procede to an isogeny and a change of level. See the formulae TODO in Cosset, Robert.
It returns the new theta functions of the same level than initially as an AssociativeArray.


// set precomp_power to true when you want to precompute the powers of the projective factors appearing in the pseudo-addition formulae.
// faster when l is big, but slower when l=3.
// Hum no it seems faster with l=3 still. Damien
 */
function change_level(ltors,precomp: precomp_power:=false,proj_coordinate:=0)
  Kset:=precomp["l","Kset"];
  coeffsformal:=precomp["l","coeffs"];
//coeffsformal: coefficient of the projective factors in the formula
  gen:=precomp["l","gen"];
  phi2:=precomp["l","phi2"];

  Dl:=Universe(Keys(ltors)); Dl0:=Universe(gen);
  //Dl0=Dl but stupid magma does not know it. It is for instance: (Z/lZ)^g
  D:=ltors[Dl.0]`numbering;   // for instance (Z/nZ)^g
  //A:=Universe(Kset); //Z/lnZ^r
  B:=Domain(phi2); //Z/nZ^r

  l:=Invariants(Dl)[1]; l1:=l div 2; l11:=l1 +1;
  Inv:=Invariants(D); g:=#Inv; n:=Inv[1];
  Invl:=Invariants(Dl); l:=Invl[1];
  DDl:=AbelianGroup([Inv[i]*Invl[i]: i in [1..g]]); // (Z/lnZ)^g
  inc1:=IncludeSubgroup(D,DDl);
  inc2:=IncludeSubgroup(Dl,DDl);
  r:=#Eltseq(Rep(Kset));

  // Determine the actual coeffs for the elements of gen
  coeffs_toinv:=[];
  for i in gen do
    l11P:=ltors[Dl!Eltseq(l11*i)]`coord;
    l1P:=ltors[Dl!Eltseq(l1*i)]`coord;
    i0:=get_nonzero_coord(l11P);
    //beta ne 0 by definition, so alpha should not be equal to 0 either
    alpha:=l1P[-i0]; beta:=l11P[i0];
    coeffs_toinv:=coeffs_toinv cat [alpha, beta];
  end for;
  coeffs_inv:=InvertListMontgomery(coeffs_toinv);
  coeffs:=[];
  inv_coeffs:=[];
  for i in [1..#gen] do
    alpha:=coeffs_toinv[2*i-1]; invalpha:=coeffs_inv[2*i-1];
    beta :=coeffs_toinv[2*i];   invbeta:= coeffs_inv[2*i];
    coeffs[i]:=alpha * invbeta; inv_coeffs[i]:=invalpha * beta;
  end for;
  //print coeffs;

  if precomp_power then // precomputations of the power of the coefficients
    coeffspowerlist:=[];
    invcoeffspowerlist:=[];
    for i in [1..#gen] do
      c:=1; d:=1; clist:=[]; dlist:=[];
      for j in [1..r*l] do
        c*:=coeffs[i];
        d*:=inv_coeffs[i];
        Append(~clist,c);
        Append(~dlist,d);
      end for;
      Append(~coeffspowerlist,clist);
      Append(~invcoeffspowerlist,dlist);
    end for;
  end if;

  // Get the theta null point of level ln from the l-torsion
  appltors:=AssociativeArray(DDl);
  for j in Dl do
    for k in D do
      i:=j@inc2+k@inc1;
      appltors[i]:=ltors[j]`coord[k];
    end for;
  end for;

  // apply the level-changed formula to get all the theta indexed by D of the isogenous variety.
  res:=AssociativeArray(D);
  preims:=AssociativeArray(D);
  for i in D do
    res[i]:=0;
    I:=Eltseq(i);
    preim:=[DDl.0: i in [1..r]];
    for z in [1..g] do
      preimz:=Eltseq((B!([I[z]] cat [proj_coordinate: zz in [1..r-1]]))@@phi2);
      // preimz is a preimage on the z coordinate
      preim:=[ preim[i]+preimz[i]*l*DDl.z: i in [1..r]];
    end for;
    preims[i]:=preim;
  end for;

  if IsDefined(precomp["l"],"K0") then
    //we did precomputations
    formalprecoeffs:=precomp["l","precoeffs"];
    precoeffs:=AssociativeArray();
    K0:=precomp["l","K0"];
    for k in K0 do
      s:=Eltseq(formalprecoeffs[k]);
      if precomp_power then
        c:=1;
        for i in [1..#s] do
          ss:=s[i];
          if ss gt 0 then
            c*:=coeffspowerlist[i,ss];
          elif ss lt 0 then
            c*:=invcoeffspowerlist[i,-ss];
          end if;
        end for;
      else
        r1:=[Max(i,0): i in s];
        r2:=[-Min(i,0): i in s];
        // print "--------------";
        // print r1;
        // print r2;
        // print coeffs;
        c:=&*[coeffs[i]^r1[i]: i in [1..#coeffs]]*
               &*[inv_coeffs[i]^r2[i]: i in [1..#coeffs]];
      end if;
      k0:=[DDl! Eltseq(k[z]): z in [1..r]];
      // print k0;
      // print "c",c;
      //print s,c;
      for i in D do
        // print "i",i;
        // print &*[appltors[preims[i,z]+k0[z]]: z in [1..r]];

        res[i]+:=c * &*[appltors[preims[i,z]+k0[z]]: z in [1..r]];
      end for;
    end for;

  else
    for tuple in CartesianPower(Kset,g) do
      //The projective coefficient does not depend on i in D because
      //changing level is a bijection on D so does not involve Dl

      k:=[ &+[Eltseq(tuple[z])[i]*DDl.z: z in [1..g]]: i in [1..r]];
      s1:=Eltseq(&+[coeffsformal[Dl0!Eltseq(z@@inc2)]: z in k]);
      s:=[];
      for i in [1..#s1] do
        test,ss:=IsDivisibleBy(s1[i],l);
        assert test;
        Append(~s,ss);
      end for;
      if precomp_power then
        c:=1;
        for i in [1..#s] do
          ss:=s[i];
          if ss gt 0 then
            c*:=coeffspowerlist[i,ss];
          elif ss lt 0 then
            c*:=invcoeffspowerlist[i,-ss];
          end if;
        end for;
      else
        r1:=[Max(i,0): i in s];
        r2:=[-Min(i,0): i in s];
        c:=&*[coeffs[i]^r1[i]: i in [1..#coeffs]]*
               &*[inv_coeffs[i]^r2[i]: i in [1..#coeffs]];
      end if;

      for i in D do
        res[i]+:=c * &*[appltors[preims[i,z]+k[z]]: z in [1..r]];
      end for;
    end for;
  end if;

  //print coeffs;
  //print_point(res);
  return res, coeffs;
end function;



//**** Isogeny computation ****//


/*
Compute an (l,...,l)-isogenous variety between two abelian varieties
represented by theta points of the same level.

L is an associative array indexed by the abelian group (Z/lZ)^g.
For each elements a=(a_1,...,a_g) in this group, we set L[e] :: ThetaPoint to be
the point a_1 e_1 + ... + a_g e_g
We assume that at least we have already computed L for the generators.

return P0 :: ThetaNullPoint for the new variety.
 */
function Isogenie(L,precomp: precomp_power:=true,isprefilled:=false)
  vprint AVIsogenies, 3: "Computing the l-torsion";
  vtime AVIsogenies, 3: ltors:=compute_all_theta_torsion(L: isprefilled:=isprefilled);
  vprint AVIsogenies, 3: "Changing level";
  vtime AVIsogenies, 3: r:=change_level(ltors,precomp :
                                        precomp_power:=precomp_power);

  P0, coeffs:=init_theta_null_point(r: init:="basic",precomp:=precomp);
  return P0, ltors, coeffs;
end function;


/*
In genus 2, compute an isogeny from an abelian variety (where we have done some
precomputation). The isogenies correspond to a kernel in theta coordinates
of the Kummer surface where a system of generators are the theta points given in r.

Return the theta null point of the isogeneous Kummer surface.
smallest field possible.
 */
function IsogenieG2Theta(r,precomp: precomp_power:=true)
  l:=precomp["l","l"];
  g:=precomp["D","g"];
  assert g eq 2;

  if Category(r) eq SeqEnum then
    P0:=precomp["H","P0"];
    Dl:=AbelianGroup([l,l]);
    P,Q,PQ:=Explode(r);
    L:=AssociativeArray();
    L[Dl.0]:=P0;
    L[Dl.1]:=P;
    L[Dl.2]:=Q;
    L[Dl.1+Dl.2]:=PQ;
  else
    L:=r;
  end if;

  if #Keys(L) eq l^g then prefilled:=true; else prefilled:=false; end if;

  //vtime AVIsogenies, 3:
  newP0, ltors, coeffs:=Isogenie(L,precomp: precomp_power:=precomp_power,
                             isprefilled:=prefilled);
  return newP0, ltors, coeffs;
end function;



/*
In genus 2, compute an isogeny from an abelian variety (where we have done some
precomputation). The isogenies correspond to a kernel where a systeme of
generators are the theta points given in r.

Return the invariants of the hyperelliptic curve (if it exists) over the
smallest field possible.

The option curve_to_invariants is a function that choose a representative systeme of invariants.
 */
function IsogenieG2(r,precomp: precomp_power:=true,
                               curve_to_invariants:=AbsoluteInvariants)
  IndentPush();
  newP0, ltors, coeffs:=IsogenieG2Theta(r, precomp: precomp_power:=precomp_power);
  // get the underlying hyperelliptic curve
  ros:=theta_null_to_rosenhain(newP0);
  K<x>:=PolynomialRing(Universe(ros));
  f:=&*[x-i: i in ros];
  newH:=HyperellipticCurve(f);

  vprint AVIsogenies, 3: "Absolute invariants";
  vtime AVIsogenies, 3: newAI:=curve_to_invariants(newH);
  IndentPop();
  return GetCastMinField(newAI), newP0, ltors, coeffs;
end function;


/*
Let J be a jacobian of an hyperelliptic curve H such that either J or
J2=Jacobian(twist(H)) has a fixed number of points n, specified by the frobenius

To check this, we compute n*P for totry random points P in J and P2 in J2.
If we can't conclude in this way, we just compute the frobenius polynomial of J
*/
function JacobianOrTwist(J,frob:totry:=3)
  n:=CardFromFrob(frob,1);
  H:=Curve(J);
  H2:=QuadraticTwist(H); J2:=Jacobian(H2);
  for t in [1..totry] do
    P:=Random(J);
    if n*P ne J!0 then return J2; end if;
    P2:=Random(J2);
    if n*P2 ne J2!0 then return J; end if;
  end for;
  if FrobeniusPoly(J) eq frob then return J;
  else return J2; end if;
end function;

function CurveOrTwist(H,frob:totry:=3)
  return JacobianOrTwist(Jacobian(H),frob: totry:=totry);
end function;

/*
FIXME comment this
 */
function RichelotTransform(G1, G2, G3)
  F:=BaseRing(G1);
  G1prim:=Derivative(G1); G2prim:=Derivative(G2); G3prim:=Derivative(G3);
  G1el:=Eltseq(G1); for i in [#G1el+1..3] do G1el[i]:=0; end for;
  G2el:=Eltseq(G2); for i in [#G2el+1..3] do G2el[i]:=0; end for;
  G3el:=Eltseq(G3); for i in [#G3el+1..3] do G3el[i]:=0; end for;
  M:=Matrix(F, 3, 3, [G1el,G2el,G3el]);
  Delta:=Determinant(M);
  L1:=G2prim*G3 - G2*G3prim;
  L2:=G3prim*G1 - G3*G1prim;
  L3:=G1prim*G2 - G1*G2prim;
  return Delta, L1, L2, L3;
end function;

/*
Given a hyperelliptic curve H and a prime l, returns the l-isogenous curves
We can give this functions some precomputations in precomp.
 */

intrinsic RationallyIsogenousJacobiansG2(J::JacHyp,l::RngIntElt :
    precomp:=AssociativeArray(), theta:=1, precomp_power:=true, ext_degree:=-1,
    curve_to_invariants:=func<x|G2Invariants(x)>,
    invariants_to_curve:=HyperellipticCurveFromG2Invariants,
    save_mem:=0) -> SeqEnum,Assoc
    {Given a genus 2 Jacobian J and a prime l, returns the (l,l)-isogenous Jacobians.}

  H:=Curve(J); g:=Genus(H);
  require g eq 2 : "Argument 1 must be the Jacobian of a genus 2 curve.";
  // require IsPrime(l) : "Argument 2 must be prime."; //TODO this should not be needed

  if Characteristic(BaseField(J)) eq 2 then
    result, precomp := RationallyIsogenousCurvesG2_carac2(H,l : precomp:=precomp);
    return [ <i[1],Jacobian(i[2])> : i in result ], precomp;
  end if;

  if not IsDefined(precomp,"thetasubgroups") then
    if not IsDefined(precomp,"subgroups") then
      IndentPush();
      vtime AVIsogenies,2: R,_,precomp :=
          RationalSymplecticTorsionSubgroups(J,l:precomp:=precomp, theta:=theta,
                                                 ext_degree:=ext_degree,
                                                 save_mem:=save_mem);
      IndentPop();
    else
      R:=precomp["subgroups"];
      if l ne 2 then
        vprint AVIsogenies,3: "  -- Convert the subgroup to theta coordinates";
        r:=Rep(R); K:=BaseField(Universe(r));
        precompute_mumford_to_theta(~precomp,J,K);
        vtime AVIsogenies,3: S,precomp:=mumford_subgroups_to_theta(l,R,precomp);
        precomp["thetasubgroups"]:=S;
      end if;
    end if;
  end if;
  result:=[];

  if l eq 2 then S:=R; else S:=precomp["thetasubgroups"]; end if;
  if IsEmpty(S) then return result, precomp; end if;

  if l eq 2 then // special case, we use the Richelot isogeny here
    for r in S do
      G1:=r[1][1];
      G2:=r[2][1];
      G3:=(r[1]+r[2])[1];
      f:=HyperellipticPolynomials(H);
      //G3:=f div (G1*G2);
      //if Gcd(G1,G2) ne 1 then continue r; end if;
      if G1*G2*G3 mod f ne 0 then continue r; end if;
      F:=BaseRing(J); AF<X>:=PolynomialRing(F);
      Delta,L1,L2,L3:=RichelotTransform(G1,G2,G3);
      if IsUnit(Delta) then
        Hiso:=HyperellipticCurve(AF!(L1*L2*L3/Delta));
        nInv:=curve_to_invariants(Hiso);
        Jnew:=Jacobian(Hiso);
        Append(~result, <nInv,JacobianOrTwist(Jnew,precomp["frob"])>);
      end if;
    end for;
    return result, precomp;
  end if;

  D:=precomp["D","D"];
  vprint AVIsogenies,2: "Computing the",#S,l,"-isogenies";
  IndentPush(); mytime:=Cputime();

  if not IsDefined(precomp["l"],"coeffs") then
    vprint AVIsogenies, 3: "** Precomputations for l=",l;
    vtime AVIsogenies, 3: precompute_isogenies(D,l,~precomp: save_mem:=save_mem);
  end if;

  for r in S do
    try
      vprint AVIsogenies, 3: "** Computing the",l,"-isogeny";
      vtime AVIsogenies, 3: nInv:=
               IsogenieG2(r,precomp : precomp_power:=precomp_power,
                                      curve_to_invariants:=curve_to_invariants);

      ChangeUniverse(~nInv,BaseRing(J));
      Jnew:=Jacobian(invariants_to_curve(nInv));
      Append(~result, <nInv,JacobianOrTwist(Jnew,precomp["frob"])>);
    catch e
      "CAUGHT ERROR:", e;
    end try;
  end for;
  IndentPop();
  vprint AVIsogenies,2: "Time:", Cputime(mytime);
  return result, precomp;
end intrinsic;

intrinsic RationallyIsogenousCurvesG2(H::CrvHyp,l::RngIntElt :
    precomp:=AssociativeArray(), theta:=1, precomp_power:=true, ext_degree:=-1,
    curve_to_invariants:=func<x|G2Invariants(x)>,
    invariants_to_curve:=HyperellipticCurveFromG2Invariants,
    save_mem:=0) -> SeqEnum,Assoc
    {Given a genus 2 curve H and a prime l, returns the (l,l)-isogenous curves}
    require Genus(H) eq 2 : "Argument 1 must be a genus 2 curve.";
    // require IsPrime(l) : "Argument 2 must be prime.";
    result,precomp:=RationallyIsogenousJacobiansG2(Jacobian(H),l :
      precomp:=precomp, theta:=theta, precomp_power:=precomp_power,
      ext_degree:=ext_degree,
      curve_to_invariants:=curve_to_invariants,
      invariants_to_curve:=invariants_to_curve,
      save_mem:=save_mem);
    return [<i[1],Curve(i[2])>: i in result], precomp;
end intrinsic;

//**** Isogenies graphs ****//


/*
FIXME comments
 */
procedure precompute_l_list(~precompl,prime_list: calc:=false,range:=[g..2*g] where g is 2, save_mem:=0)
  IndentPush();

  if not IsDefined(precompl,0) then
    precomp:=AssociativeArray();
    D:=AbelianGroup([2,2]);
    vprint AVIsogenies, 3: "-- Precomputations for D";
    vtime AVIsogenies, 3: precompute_D(D,~precomp);
    precompl[0]:=precomp;
  end if;

  precomp:=precompl[0];
  D:=precomp["D","D"];
  g:=Ngens(D);

  for l in prime_list do
    if IsDefined(precompl,l) then continue l; end if;
    precompl[l]:=precomp;
    set_l(l,~precompl[l]);
    if calc then
      vprint AVIsogenies,2: "** Precomputation for the prime", l;
    // Dl:=AbelianGroup([l: i in [1..g]]);
    // precompll:=AssociativeArray();
    // precompll["Dl"]:=Dl;
    // precompl[l,"l"]:=precompll;
      if l eq 2 then continue l; end if;
      vtime AVIsogenies,2: precompute_l(D,l,~precompl[l]: range:=range, save_mem:=save_mem);
    end if;
  end for;
  IndentPop();
end procedure;



/*
FIXME comments
 */
intrinsic Genus2IsogenyGraph(J::JacHyp,prime_list::[RngIntElt]:
  theta:=1, only_mumford:=false, structure:=true, ext_degrees:=[],
  precompl:=AssociativeArray(), frob:=0, save_mem:=0)
  -> Assoc, SeqEnum, SeqEnum
  {The isogenies graph of the Jacobian J for primes in prime_list.}

  g:=Dimension(J); H:=Curve(J);

  if Characteristic(BaseField(H)) eq 2 then
    theta:=0; only_mumford:=true;
  end if;

  nbiso:=0;

  precompute_l_list(~precompl,prime_list: save_mem:=save_mem);

  if frob eq 0 then
    IndentPush();
    vprint AVIsogenies,2: "** Frobenius:";
    vtime AVIsogenies,2: frob:=FrobeniusPoly(J);
    IndentPop();
  end if;

  I:=G2Invariants(H);
  jacobians:=AssociativeArray(); jacobians[I]:=J;
  isogn:=AssociativeArray(); // lists isogenous invariants
  tovisit:=[I];
  orig:=true;//orig = true is that it is our first step

  while not IsEmpty(tovisit) do
    vprint AVIsogenies,1: "**** GRAPH STATUS:",#Keys(jacobians),"nodes so far including",#tovisit,"yet to explore";
    I:=tovisit[#tovisit];
    Prune(~tovisit);
    J:=jacobians[I]; H:=Curve(J);
    vprint AVIsogenies,2: I;

    if I eq [0,0,0] then continue; end if;

    IndentPush();
    precomp:=precompl[0]; precomp["frob"]:=frob;


    if Characteristic(BaseField(H)) ne 2 then
      vprint AVIsogenies,2: "** Precomputations for H";
      vtime AVIsogenies,2: precompute_H(H,~precomp);
    end if;

    for l in prime_list do
      CopyArray(precompl[l],~precomp);

      if IsDefined(ext_degrees,l) then
        ext_degree:=ext_degrees[l];
      else
        ext_degree:=-1;
      end if;

      vtime AVIsogenies,2: R,_,pre :=
          RationalSymplecticTorsionSubgroups(J,l : precomp:=precomp,theta:=theta, only_mumford:=only_mumford, ext_degree:=ext_degree, save_mem:=save_mem);

      if #prime_list eq 1 and not orig and #R eq 1 and not structure then
      // if we have one kernel, we know that we are coming back in the graph,
      // so we don't need to compute this isogeny.
      // We compute it anyway if structure = true because I am too lazy to
      // search for the corresponding parent in the isogeny graph...
        break l;
      end if;

      vprint AVIsogenies,2: "** Computing ", l, "-isogenies";
      IndentPush();
      vtime AVIsogenies,2: res,pre:=RationallyIsogenousCurvesG2(H,l:precomp:=pre, theta:=theta, save_mem:=save_mem);
      CopyArray(pre,~precompl[l]:keys:=["l"]);
      IndentPop();

      nbiso+:=#res;
      isogn[I]:=[];
      for r in res do
        nInv:= r[1];  nH:=r[2]; nJ:=Jacobian(nH);
        Include(~isogn[I], <nInv,l>);
        if not nInv in Keys(jacobians) then
          vprint AVIsogenies,2: "New curve", nInv;
          jacobians[nInv]:=nJ;
          Include(~tovisit,nInv);
        end if;
      end for;

    end for;

    IndentPop();
    orig := false;
  end while;

  vprint AVIsogenies,1: "Computed", nbiso, "isogenies and found", #Keys(jacobians), "curves.";
  return isogn, jacobians, precompl;
end intrinsic;
