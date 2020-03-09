/* Computing the rational kernels of the Jacobian of a genus 2 curve
* - Gaëtan Bisson
* - Damien Robert
*/

import "libav.m" : degree_g_factors;
import "Arithmetic.m" : precompute_theta_point, point_from_basis_l2, pairing_PQ;
import "Isogenies.m" : compute_all_theta_torsion;
import "rosenhain.m" : mumford_to_theta, mumford_to_lvl2, \
    precompute_mumford_to_theta;



//****  Frobenius ****//

function FrobeniusPolyG2(J);
/* ReciprocalPolynomial(EulerFactor(J)) is too slow.
 * In genus 2, it is faster to compute #H and #J
 */
  if not assigned J`EulerFactor then
    H:=Curve(J);
    F := BaseRing(H); q := #F;
    // #H equals 1-t+q where t = trace of Frobenius
    N1:=#H; t := 1 + q - N1;
    // #J equals the 1-t+s-tq+q^2 = \chi_Frob(1)
    try N:=#J;
    catch e
      print "Cannot compute #J, computing #H/Fq^2 instead.";
      N2:=#BaseChange(H,ext<F|2>);
      N:=(N1^2+N2) div 2 - q;
    end try;
    s := N - 1 + t + t*q - q^2;
    z:=PolynomialRing(IntegerRing()).1;
    J`EulerFactor:=1 - t*z + s*z^2 - t*q*z^3 + q^2*z^4;
  end if;
  return ReciprocalPolynomial(J`EulerFactor);
end function;

intrinsic FrobeniusPoly(J::JacHyp) -> RngUPolElt
  {The characteristic polynomial of Frobenius.}
  if Dimension(J) eq 2 then return FrobeniusPolyG2(J); end if;
  return ReciprocalPolynomial(EulerFactor(J));
end intrinsic;

intrinsic FrobeniusPoly(H::CrvHyp) -> RngUPolElt
  {The characteristic polynomial of Frobenius.}
  J:=Jacobian(H);
  if Dimension(J) eq 2 then return FrobeniusPolyG2(J); end if;
  return ReciprocalPolynomial(EulerFactor(J));
end intrinsic;

intrinsic FrobeniusPoly(E::CrvEll) -> RngUPolElt
  {The characteristic polynomial of Frobenius.}
  return ReciprocalPolynomial(EulerFactor(E));
end intrinsic;

// Return the cardinal of the abelian variety in an extension of degree k,
// using the characteristic polynomial of the Frobenius.
function CardFromFrob(frob,k)
  R:=PolynomialRing(BaseRing(frob),2);
  return Integers()!Evaluate(Resultant(Evaluate(frob,R.1),R.1^k-R.2,R.1),[1,1]);
end function;

//**** Find where the l-torsion is defined ****//
// Returns the degree of an extension over which the full l-torsion of J is
// defined.
intrinsic GetFullTorsionExtension(l::RngIntElt,frob::RngUPolElt) -> RngIntElt
  {If A is an abelian variety with Frobenis polynomial frob,
  returns the degree of the extension which contains its full l-torsion.}
  kk:=1;
  P<x>:=PolynomialRing(ResidueClassRing(l));
  for f in Factorization(P!frob) do
    Q<y>:=quo<P|f[1]>;
    k:=#Q-1;
    for p in Factorization(k) do for i in [1..p[2]] do
      if y^(k div p[1]) eq 1 then k div:=p[1]; end if;
    end for; end for;
    if f[2] gt 1 then
      Q<y>:=quo<P|f[1]^f[2]>;
      k1:=k; y1:=y^k1; yy:=y1;
      while yy ne 1 do
        k+:=k1; yy*:=y1;
        if k gt #Q then return 0; end if;
      end while;
    end if;
    kk:=LCM(kk,k);
  end for;
  return kk;
end intrinsic;

/*
Returns the degree of an extension over which all rational subgroups of J
isomorphic to (Z/l)^g are defined.
If optimize is equal to true, we add the condition that the subgroup
have to be isotropic
*/
function GetRationalSquareTorsionExtension(l,frob: optimize:=true)
  IndentPush();
  g:=Degree(frob) div 2;
  p:=IntegerRing()!Root(Eltseq(frob)[1],g);// card(BaseField)
  P<x>:=PolynomialRing(ResidueClassRing(l));
  R<y>:=RationalFunctionField(ResidueClassRing(l));
  frobl:=P!frob; ybar:=p/y; conj:=hom<R->R|ybar>;
  D:=degree_g_factors(frobl,g);
  if IsEmpty(D) then IndentPop(); return 0; end if;
  k:=0;
  //frobl;F; [Evaluate(f[1],ybar): f in F];
  for d in D do
     // _,inv,_:=ExtendedGreatestCommonDivisor(x,frobl);
     // d*Evaluate(d,p*inv) mod frobl, Numerator(d*Evaluate(d,ybar)) mod frobl; "----";
    if optimize and Numerator(d*Evaluate(d,ybar)) mod frobl ne 0 then continue d; end if;
    if #Terms(d) ne 1 then
    //si d=x^n, alors aucune seul Fr^0 peut être l'identité
      if k eq 0 then k:=1; end if;
      kk:=1; xx:=x; xxx:=xx;
      while xxx ne 1 do kk+:=1; xxx:=(xxx*xx) mod d; end while;
      vprint AVIsogenies, 6: "Possible subgroup in degree", kk;
      k:=LCM(k,kk);
    end if;
  end for;
  IndentPop(); return k;
end function;





//**** Subgroup directly in theta ****//

/* We fix some notations: l is the torsion we are working for, Dl indice a
* kernel (so is AbelianGroup([l,l]) in dimension 2), and Dll indice the
* whole l-torsion (so is AbelianGroup([l,l,l,l]) in dimension 2.
* A "basis" B is the basis of the l-torsion of J in an extension that is
* sufficient for our purpose (usually, even if we want to find each
* kernels, we do not have to work with the degree where the full l-torsion
* is defined). So #B can be less than 2g.
*/

function point_from_basis_mumford(el,basis)
  el:=Eltseq(el);
  return &+[el[i]*basis[i]: i in [1..#el] | el[i] ne 0];
end function;

// For the following functions, since we call mumford_to_theta, then
// precomp should contain the informations from precompute_mumford_to_theta(~precomp,J,K)

// From a basis B in Mumford coordinates, compute all the points of l-torsion in theta coordinates, return them and store them in precomp["ltors_theta"]
function ThetaTorsionFromMumfordBasis(B,l,precomp: onlybasis:=false)
  IndentPush();
  J:=Parent(Rep(B)); H:=Curve(J); K:=BaseRing(J);
  gg:=2*Dimension(J);
  vprint AVIsogenies, 4: "Sending points to theta";
  currenttime:=Cputime();
  if not IsDefined(precomp,"ltors_theta") then
    precomp["ltors_theta"]:=AssociativeArray();
    Dll:=AbelianGroup([l: i in [1..gg]]);
  else
    Dll:=Universe(Keys(precomp["ltors_theta"]));
  end if;
  if not IsDefined(precomp,"ltors_basis-ros") then
    precomp["ltors_basis-ros"]:=[];
  end if;
  L:=precomp["ltors_theta"];
  Bros:=precomp["ltors_basis-ros"]; P0:=precomp["HK","P0"];
  L[Dll.0]:=P0;
  for i in [1..#B] do
    if not IsDefined(L,Dll.i) then
      Ptheta,Pros:=mumford_to_theta(B[i],precomp);
      Bros[i]:=Pros; L[Dll.i]:=Ptheta;
      precompute_theta_point(~L[Dll.i],P0: init:="dadd", isQ:=true, onlyprod:=false);
    end if;
  end for;
  D0:=AbelianGroup([2: i in B]);
  gen:={D0.i: i in [1..#B]};
  for i in D0 do
    if not i in gen or i eq D0.0 then
      t:=Eltseq(i) cat [0: i in [#B+1..gg]];
      if not IsDefined(L,Dll!t) then
        p:=&+[t[i]*Bros[i] : i in [1..#B]];
        L[Dll!t]:=mumford_to_lvl2(p,precomp);
        precompute_theta_point(~L[Dll!t],P0: init:="dadd", isQ:=true, onlyprod:=true);
      end if;
    end if;
  end for;
  vprint AVIsogenies, 4: Cputime(currenttime);
  if not onlybasis then
    vprint AVIsogenies, 4: "Computing the l-torsion";
    vtime AVIsogenies, 4: L:=compute_all_theta_torsion(L);
  end if;
  precomp["ltors_theta"]:=L;
  precomp["ltors_basis-ros"]:=Bros;
  IndentPop(); return L,precomp;
end function;

// Take a list of kernels given by their basis [P1,P2] in Mumford
// coordinates, Pi a point of l torsion. Compute [P1,P2,P1+P2] in theta
// coordinates
/* Warning: works only in genus 2! */

function mumford_subgroups_to_theta(l,kernels,precomp)
  g:=Dimension(Universe(Rep(kernels)));
  Dl:=AbelianGroup([l: i in [1..g]]);
  if IsEmpty(kernels) then return kernels; end if;
  P0:=precomp["HK","P0"];
  S:=[];
  for ker in kernels do
    s:=AssociativeArray();
    //Dl:=Universe(Keys(ker));
    P,JP:=mumford_to_theta(ker[1],precomp);
    Q,JQ:=mumford_to_theta(ker[2],precomp);
    PQ:=mumford_to_lvl2(JP+JQ,precomp);
    s[Dl.1]:=P; s[Dl.2]:=Q; s[Dl.1+Dl.2]:=PQ;
    s[Dl.0]:=P0;
    Append(~S,s);
  end for;
  return S,precomp;
end function;

/* given Dl=AbelianGroup([l,l]) fixed once and for all, an array encoding
* the points of l-torsion in theta coordinates (indiced by Dl), and kernels a list of "abstract"
* kernels given by their basis [P1,P2] where Pi is in Dl, compute the
* points corresponding to P1, P2 and P1+P2 in theta coordinates
*/
/* Warning: works only in genus 2! */



function abstract_subgroups_to_theta(Dl,ltors,kernels)
  if IsEmpty(kernels) then return kernels; end if;
  S:=[]; P0:=ltors[Universe(Keys(ltors)).0];
  for ker in kernels do
    s:=AssociativeArray();
    P,ltors:=point_from_basis_l2(ker[1],ltors);
    Q,ltors:=point_from_basis_l2(ker[2],ltors);
    PQ,ltors:=point_from_basis_l2(ker[1]+ker[2],ltors);
    s[Dl.1]:=P; s[Dl.2]:=Q; s[Dl.1+Dl.2]:=PQ; s[Dl.0]:=P0;
    Append(~S,s);
  end for;
  return S;
end function;





//****  Weil pairing ****//

// Computes the logarithmic (wrt zeta) Gram matrix of the basis B for the Weil pairing
function GetWeilPairing(B,l,precomp)
  // assert IsPrime(l); TODO: this should not be needed
  Zl:=GF(l);
  M:=ZeroMatrix(GF(l),#B,#B);
  if IsDefined(precomp,"zeta") then
    zeta:=precomp["zeta"];
    U:=precomp["zetalog"];
  else
    zeta:=1; U:=AssociativeArray();
    U[1]:=Zl!0; precomp["zetalog"]:=U;
  end if;
  for i,j in [1..#B] do
    if i eq j then
      M[i,j]:=Zl!0;
    elif j lt i then
      M[i,j]:=-M[j,i];
    else
      w:=WeilPairing(B[i],B[j],l);
      if w eq 1 then
        M[i,j]:=Zl!0;
      else
        if zeta eq 1 then
          zeta:=w;
          for k in [0..l-1] do U[zeta^k]:=Zl!k; end for;
          precomp["zeta"]:=zeta;
          precomp["zetalog"]:=U;
        end if;
        M[i,j]:=U[w];
      end if;
    end if;
  end for;
  return M,precomp;
end function;

// Computes the logarithmic (wrt zeta) vector of the Weil pairing of P
// against the points in B
function GetPointPairing(P,B,l,precomp)
  U:=precomp["zetalog"];
  return [U[WeilPairing(P,i,l)]:i in B];
end function;

// B is still in Mumford coordinates, but this time we compute the pairings
// using theta coordinates, it is usually much faster
function GetWeilPairingInTheta(B,l,precomp)
  L,precomp:=ThetaTorsionFromMumfordBasis(B,l,precomp: onlybasis:=true);
  // assert IsPrime(l); // TODO this should not be needed
  Dll:=Universe(Keys(L));
  J:=Parent(Rep(B)); H:=Curve(J); K:=BaseRing(J);
  gg:=2*Dimension(J); Zl:=GF(l);
  if IsDefined(precomp,"zeta") then
    zeta:=precomp["zeta"];
    U:=precomp["zetalog"];
  else
    zeta:=1; U:=AssociativeArray();
    U[1]:=Zl!0; precomp["zetalog"]:=U;
  end if;
  M:=ZeroMatrix(GF(l),gg,gg); P0:=precomp["HK","P0"];
  for i,j in [1..#B] do
    if i eq j then
      M[i,j]:=Zl!0;
    elif j lt i then
      M[i,j]:=-M[j,i];
    else
      P:=L[Dll.i]; Q:=L[Dll.j]; PQ:=L[Dll.i+Dll.j];
      w:=pairing_PQ(l,P,Q,PQ,P0);
      if w eq 1 then
        M[i,j]:=Zl!0;
      else
        if zeta eq 1 then
          zeta:=w;
          for i in [0..l-1] do U[zeta^i]:=Zl!i; end for;
          precomp["zeta"]:=zeta;
          precomp["zetalog"]:=U;
        end if;
        M[i,j]:=U[w];
      end if;
    end if;
  end for;
  return M,precomp;
end function;

// Compute the pairings between P and Q (in Mumford coordinates), using the
// theta pairing algorithm
function PairingInTheta(l,P,Q,precomp)
  Ptheta,Pros:=mumford_to_theta(P,precomp);
  Qtheta,Qros:=mumford_to_theta(Q,precomp);
  PQtheta:=mumford_to_lvl2(Pros+Qros,precomp);
  return pairing_PQ(l,Ptheta,Qtheta,PQtheta,precomp["HK","P0"]);
end function;

// Same as GetPointPairing, but using the theta pairing algorithm
function GetPointPairingInTheta(P,B,precomp)
  r:=[]; U:=precomp["zetalog"];
  Dll:=Universe(Keys(precomp["ltors_theta"]));
  l:=Invariants(Dll)[1];
  Ptheta,Pros:=mumford_to_theta(P,precomp);
  for i in [1..#B] do
    Q:=B[i]; Qros:=precomp["ltors_basis-ros"][i];
    Qtheta:=precomp["ltors_theta",Dll.i];
    PQtheta:=mumford_to_lvl2(Pros+Qros,precomp);
    Append(~r,U[pairing_PQ(l,Ptheta,Qtheta,PQtheta,precomp["HK","P0"])]);
  end for;
  return r;
end function;




//****  Generate (isotropic) subgroups ****//


// give the subgroups of rank 2 in Zl^gg
// Dll is AbelianGroup([l,l,l,l]) fixed once and for all
/* Warning: works only in genus 2! */

function GenerateSubgroupsG2(Dll,gg: isotropic:=true)
  gens:=[]; g:=2; compl:=#(Invariants(Dll))-gg;
  l:=Invariants(Dll)[1];
  for i0 in [1..gg-1] do
    for j0 in [i0+1..gg] do
      level :=[l: i in [i0+1..gg]];
      for x0 in [[z: z in alpha] : alpha in
        CartesianProduct([[0..i-1]: i in level])] do
        x:=[0: i in [1..i0-1]] cat [1] cat x0;
        if x[j0] ne 0 then continue x0; end if;
        level:=[l: i in [j0+1..gg]];
        for y0 in (IsEmpty(level) select [[]]
         else [[z: z in alpha] : alpha in
         CartesianProduct([[0..i-1]: i in level])]) do
          y:=[0: i in [1..j0-1]] cat [1] cat y0;
          if isotropic and gg gt g then
            if &+[x[i]*y[i+g]-x[i+g]*y[i]: i in [1..gg-g]] mod l ne 0 then
              continue y0;
            end if;
          end if;
          x:=x cat [0: i in [1..compl]];
          y:=y cat [0: i in [1..compl]];
          Append(~gens,[Dll!x,Dll!y]);
        end for;
      end for;
    end for;
  end for;
  return gens;
end function;

// B is a basis of the l-torsion, Dll as usual, and W is the GramMatrix of
// the Weil Pairings of elements from B, from GetWeilPairing or
// GetWeilPairingInTheta
// Compute the homomorphism of Dll which sends B to a symplectic basis
function SymplecticBasisFromPairingG2(B,Dll,W)
  l:=Invariants(Dll)[1];
  g:=Dimension(Universe(B)); gg0:=#B; gg:=2*g;
  if gg0 le 2 then
    return hom<Dll -> Dll| [Dll.i: i in [1..gg]]>;
  elif gg0 eq 3 then
    T:=IdentityMatrix(GF(l),gg);
    M:=W;
    if M[1,2] eq 0 and M[1,3] eq 0 then
      SwapColumns(~T,1,2);
      M:=Transpose(T)*W*T;
    end if;
    if M[1,3] eq 0  then
      SwapColumns(~T,2,3);
      M:=Transpose(T)*W*T;
    end if;
    MultiplyColumn(~T,1/M[1,3],3);
    M:=Transpose(T)*W*T;
    beta:=-M[1,2];
    alpha:=-M[2,3];
    AddColumn(~T,alpha, 1, 2);
    AddColumn(~T,beta, 3, 2);
    return hom<Dll -> Dll| [Dll!Eltseq([T[j,i]: j in [1..gg]]):i in [1..gg0]] cat [Dll.4]>;
  elif gg0 eq 4 then
    T:=IdentityMatrix(GF(l),gg);
    for i in [1..g] do
      M:=Transpose(T)*W*T;
      //e_g+i <- f_j st e_i/e_g+i = 1
      j:=i; repeat j+:=1; until M[i,j] ne 0 or j gt g;
      if j gt g then j:=g+i-1; repeat j+:=1; until M[i,j] ne 0; end if;
      MultiplyColumn(~T,1/M[i,j],j);
      SwapColumns(~T,j,g+i);
      M:=Transpose(T)*W*T;
      for k in [i+1..g] do
        // e_k   <- e_k   - (e_k  /e_g+i) e_i - (e_i/e_k  ) e_g+i
        // e_g+k <- e_g+k - (e_g+k/e_g+i) e_i - (e_i/e_g+k) e_g+i
        AddColumn(~T,-M[k  ,g+i], i  , k);
        AddColumn(~T,-M[i  ,k]  , g+i, k);
        AddColumn(~T,-M[g+k,g+i], i  , g+k);
        AddColumn(~T,-M[i  ,g+k], g+i, g+k);
      end for;
    end for;
    //T; "---"; M:=Transpose(T)*W*T; M;
    return hom<Dll -> Dll| [<Dll.i,Dll!Eltseq([T[j,i]: j in [1..gg]])>:i in [1..gg]]>;
  end if;
end function;

//W:=e(P,B_i) from GetPointPairing or GetPointPairingInTheta,
// fsymp:symplectic map to a symplectic basis from SymplecticBasisFromPairingG2
// returns the element in Dll corresponding to P via the basis B
// in genus 2, we use abstract_point_from_basis instead
function abstract_point_from_pairing(W,fsymp)
  g:=2; gg:=#W;
  Dll:=Domain(fsymp); gens:=Setseq(Generators(Dll));
  l:=Invariants(Dll)[1];
  T:=Matrix(GF(l),gg,gg, [ Eltseq(Dll.i@fsymp): i in [1..gg]]);
  M:=Matrix(GF(l),gg,1,W);
  M:=T*M; r:=[];
  for i in [1..gg] do
    if i le g then
      r[i]:=+M[i+g,1];
    else
      r[i]:=-M[i-g,1];
    end if;
  end for;
  return (Dll!r)@fsymp;
end function;





//****  Basis of the l-torsion ****//

/*
This compute a basis of J[l](\Fq^k) or eventually the l^d-torsion
  ldtors = -d -> just check the l^d-torsion
  ldtors = 0  -> compute the l^\infty torsion
  ldtors = d  -> compute the l^d tors
In genus 2, we use GetTorsionBasisG2 instead
Output: B a basis of the l-torsion
LB: a basis of the l^\infty-torsion, where
LB[i]=[P,lP,...,l^k P] whith l^{k+1}P=0
T: the map between Z/lZ^(2g) and J[l] given by the basis B
Note: LB may not give the full l^\infty torsion when ldtors=d because in
this case we stop as soon as we have a full l^d-torsion. Still in this
case, the l^d basis is given by
  LB[i][#LB[i]-d+1]
because B is always a basis of the l-torsion
Note: LB[i][#LB[i]] may not be B[i] due to the way we construct the l^infty
torsion; these points will give another basis indexed by LBAbstract in the
code. To be more precise: each time we find a new lineary independent
random point of l-torsion we update B until B is of cardinality 2*g. We may
not have a basis of the l^infty torsion yet so we continue to update LB
until we have a basis of the l^infty torsion.
*/
intrinsic GetTorsionBasis (J::JacHyp, l::RngIntElt, k::RngIntElt
  : frob:=FrobeniusPoly(J), ldtors:=0) -> SeqEnum
  {Computes a basis of the l-torsion group of J defined over an
  extension of degree k. See source code for optional arguments.}
  IndentPush();
  vprint AVIsogenies,5: l,"-torsion. k=", k, "ldtors=", ldtors;
  assert IsPrime(l); //TODO: relax this condition
  gg:=2*Dimension(J);
  F:=BaseRing(J); F2:=ext<F|k: Optimize:=false>;
  J:=BaseChange(J,F2);
  c:=CardFromFrob(frob,k); d:=Valuation(c,l); c:=c div l^d;
  vprint AVIsogenies, 5: "Points:", Round(Log(2,c)), d;
  B:=[Parent(J!0)|]; LB:=[];//backtracking info for the basis B
  Dl:=AbelianGroup([l: i in [1..gg]]); b:=0;//number of random points
  T:=AssociativeArray(); //we index the l-torsion by D
  invT:=AssociativeArray(); //we index D by the l-torsion
  T[Dl.0]:=J!0; invT[J!0]:=Dl.0;
  linfty:=0;
  LBAbstract:=[Dl.i : i in [1..gg]]; //the abstract backtracking basis
  while linfty lt d do
    //test if we already have the full l^d basis
    test1:=ldtors gt 0 and #B eq gg and &and[#LB[i] ge ldtors: i in [1..#B]];
    seq:=[d-#LB[i]: i in [1..#B] | #LB[i] le d];
    test2:=ldtors lt 0 and
           d-linfty lt ldtors*(gg-#B)+(IsEmpty(seq) select 0 else &+seq);
    if test1 or test2 then break; end if;

    P:=c*Random(J);
    vprint AVIsogenies, 5: "#B:", #B, "linf:", linfty, "#ltors:", #Keys(T);
    vprint AVIsogenies, 5: "************ New point **************";
    LP:=[]; b+:=1;
    while true do
      if P eq J!0 then vprint AVIsogenies, 5: "Bad Luck!"; break; end if;
      lP:=l*P; Insert(~LP,1,P);
      if lP eq J!0 then //P is a l-torsion point
        if P notin Keys(invT) then
          vprint AVIsogenies, 5: "New generator!";
          Append(~B,P);
          LB[#LB+1]:=LP;
          for i in Keys(T) do for j in [1..l-1] do
            ii:=i+j*Dl.#B; Q:=T[i]+j*P;
            T[ii]:=Q; invT[Q]:=ii;
          end for; end for;
          //we can update linfty
          linfty+:=#LP;
          break;
        else
        // we either backtrack, or update the basis B
          phi:=hom<Dl->Dl |LBAbstract>;
          Pabstract:=invT[P]@@phi; DP:=Eltseq(Pabstract);
          basis:=[i: i in [1..#B] | DP[i] ne 0];
          nP:=#LP; lvlbasis:=[#LB[i]: i in basis];
          max:=Max(lvlbasis);
          if nP le max then // we backtrack
            maxbasis:=[i: i in basis | #LB[i] ge nP];
            P:=LP[#LP]-&+[DP[i]*LB[i, nP]: i in maxbasis];
            //P:=LP[#LP]-&+[DP[i]*LB[i, Min(#LB[i],nP)]: i in basis];
            LP:=[];
            vprint AVIsogenies, 5: "Backtracking", nP, "steps";
            continue;
          else // we update B
            //the basis element we update
            //should it be the max or the min? I would say the min (because
            //linfty will grow higher), but I need to test that.
            // After some test, it does not change much
            //min:=Min(lvlbasis);
            i0:=Rep([i: i in basis | #LB[i] eq max]);
            LBAbstract[i0]:=invT[P];
            LB[i0]:=LP;
            vprint AVIsogenies, 5: "Found higher point";
            linfty+:=nP-max;
            break;
          end if;
        end if;
      end if;
      P:=lP;
    end while;
  end while;
  vprint AVIsogenies, 5: "#B:", #B, "linf:", linfty, "#ltors:", #Keys(T);
  vprint AVIsogenies, 5: "We did", b, "try";
  IndentPop();
  return B,LB,T; //invT;
end intrinsic;


//****  Basis of the l-torsion via pairings ****//

/*
P is a new potential basis point, B is the basis up to now
if P not in <B> then return true, and update B and precomp
otherwise return false, and the abstract element representing P in the basis B

Options:
 theta:
   theta=-1: Don't used pairing. Thus don't search for simplectic basis
   theta=0 : use the pairing in Mumford coordinates,
   theta=1 : use the theta coordinates pairing
 save_mem
   if save_mem=-1, don't use pairings at all, compute the whole l-torsion
    Otherwise use pairings. We still have the case where the basis found up
    to now B is isotropic.
   With save_mem<=1 we compute all the generated points and store them,
   (save_mem=1 is used in Isogenies.m)
   with save_mem=2 we recompute it each time.

Only work in dimension 2!
*/
function new_ltors_pointG2(P,B,precomp: theta:=1, save_mem:=0)
  ltors:=precomp["ltors"]; g:=2; gg:=2*g;
  //B:=precomp["ltors_basis"];
  Dll:=Universe(Keys(ltors)); Z:=IntegerRing();
  l:=Invariants(Dll)[1];
  if save_mem eq -1 then
    if P notin {ltors[i]: i in Keys(ltors)} then
      Append(~B,P);
      for i in Keys(ltors) do for j in [1..l-1] do
        ltors[i+j*Dll.#B]:=ltors[i]+j*P;
      end for; end for;
      precomp["ltors"]:=ltors;
      precomp["ltors_basis"]:=B;
      return true,B,precomp;
    else
      return false,Rep([i: i in Keys(ltors) | ltors[i] eq P]),precomp;
    end if;
  end if;
  if l eq 2 then theta:=0; end if;
  if IsEmpty(B) then
    Append(~B,P);
    for j in [1..l-1] do
       ltors[j*Dll.1]:=j*P;
    end for;
    precomp["ltors_basis"]:=B;
    precomp["ltors"]:=ltors;
    if theta eq 1 then
      Ptheta,Pros:=mumford_to_theta(P,precomp);
      L:=AssociativeArray();
      L[Dll.0]:=precomp["HK","P0"];
      L[Dll.1]:=Ptheta;
      Bros:=[];
      Bros[1]:=Pros;
      precomp["ltors_theta"]:=L;
      precomp["ltors_basis-ros"]:=Bros;
    end if;
    precomp["ltors_pairings"]:=ZeroMatrix(GF(l),4,4);
    return true,B,precomp;
  elif #B eq 1 then
    ltors:=precomp["ltors"];
    if P in {ltors[i]: i in Keys(ltors)} then
      return false,Rep([i: i in Keys(ltors) | ltors[i] eq P]), precomp;
    else
      if theta eq 0 then
        vprint AVIsogenies, 6: "Pairing in Weil";
        vtime AVIsogenies, 6: e:=WeilPairing(B[1],P,l);
      else
        Ptheta,Pros:=mumford_to_theta(P,precomp);
        L:=precomp["ltors_theta"];
        Bros:=precomp["ltors_basis-ros"];
        L[Dll.2]:=Ptheta; Bros[2]:=Pros;
        precomp["ltors_basis-ros"]:=Bros;
        Qtheta:=L[Dll.1]; PQtheta:=mumford_to_lvl2(Pros+Bros[1],precomp);
        L[Dll.1+Dll.2]:=PQtheta;
        precomp["ltors_theta"]:=L;
        vprint AVIsogenies, 6: "Pairing in theta";
        vtime AVIsogenies, 6: e:=pairing_PQ(l,Qtheta,Ptheta,PQtheta,precomp["HK","P0"]);
      end if;
      if e ne 1 then
        zeta:=e; U:=AssociativeArray();
        for i in [0..l-1] do U[zeta^i]:=GF(l)!i; end for;
        precomp["zeta"]:=zeta;
        precomp["zetalog"]:=U;
        Bpair:=precomp["ltors_pairings"];
        Bpair[1,2]:=1; Bpair[2,1]:=-1;
        precomp["ltors_pairings"]:=Bpair;
      end if;
      B[2]:=P;
      precomp["ltors_basis"]:=B;
      precomp["ltors"]:=ltors;
      return true,B,precomp;
    end if;
  elif #B eq 2 then
    if theta eq 0 then
      vprint AVIsogenies, 6: "Pairings in Weil";
      vtime AVIsogenies, 6: e1:=WeilPairing(B[1],P,l);
      vtime AVIsogenies, 6: e2:=WeilPairing(B[2],P,l);
    else
      Ptheta,Pros:=mumford_to_theta(P,precomp);
      L:=precomp["ltors_theta"];
      Bros:=precomp["ltors_basis-ros"];
      PQtheta1:=mumford_to_lvl2(Pros+Bros[1],precomp);
      vprint AVIsogenies, 6: "Pairings in Theta";
      vtime AVIsogenies, 6:e1:=pairing_PQ(l,L[Dll.1],Ptheta,PQtheta1,precomp["HK","P0"]);
      PQtheta2:=mumford_to_lvl2(Pros+Bros[2],precomp);
      vtime AVIsogenies, 6:e2:=pairing_PQ(l,L[Dll.2],Ptheta,PQtheta2,precomp["HK","P0"]);
    end if;
    W:=precomp["ltors_pairings"]; ee:=W[1,2];
    if ee eq 0 then
      if e1 eq 1 and e2 eq 1 then// P in <B>
        if save_mem le 1 and not IsDefined(ltors,Dll.1+Dll.2) then
          for i in Keys(ltors) do for j in [1..l-1] do
           ltors[i+j*Dll.2]:=ltors[i]+j*B[2];
          end for; end for;
          precomp["ltors"]:=ltors;
        end if;
        if save_mem le 1 then
          return false,Rep([i: i in Keys(ltors) | ltors[i] eq P]), precomp;
        else
          for i in Keys(ltors) do for j in [0..l-1] do
            if ltors[i]+j*B[2] eq P then
              return false, i+j*Dll.2, precomp;
            end if;
          end for; end for;
        end if;
      else
        if e1 eq 1 then zeta:=e2; else zeta:=e1; end if;
        U:=AssociativeArray();
        for i in [0..l-1] do U[zeta^i]:=GF(l)!i; end for;
        precomp["zeta"]:=zeta;
        precomp["zetalog"]:=U;
      end if;
    end if;
    U:=precomp["zetalog"];
    ee1:=U[e1]; ee2:=U[e2];
    if ee ne 0 then
      if P+(Z!ee2)*B[1]-(Z!ee1)*B[2] eq ltors[Dll.0] then
        return false,(-Z!ee2)*Dll.1+(Z!ee1)*Dll.2, precomp;
      end if;
    end if;
    // here we know that P is a new point
    Append(~B,P);
    if theta eq 1 then
      L:=precomp["ltors_theta"];
      Bros:=precomp["ltors_basis-ros"];
      L[Dll.3]:=Ptheta; Bros[3]:=Pros;
      L[Dll.1+Dll.3]:=PQtheta1; L[Dll.2+Dll.3]:=PQtheta2;
      precomp["ltors_theta"]:=L;
      precomp["ltors_basis-ros"]:=Bros;
    end if;
    W[1,3]:=ee1; W[3,1]:=-ee1;
    W[2,3]:=ee2; W[3,2]:=-ee2;
    precomp["ltors_pairings"]:=W;
    B[3]:=P; precomp["ltors_basis"]:=B;
    // determine symplectic basis
    T:=IdentityMatrix(GF(l),gg);
    M:=W;
    if M[1,2] eq 0 and M[1,3] eq 0 then
      SwapColumns(~T,1,2);
      M:=Transpose(T)*W*T;
    end if;
    if M[1,3] eq 0  then
      SwapColumns(~T,2,3);
      M:=Transpose(T)*W*T;
    end if;
    MultiplyColumn(~T,1/M[1,3],3);
    M:=Transpose(T)*W*T;
    beta:=-M[1,2]; alpha:=-M[2,3];
    AddColumn(~T,alpha, 1, 2); AddColumn(~T,beta, 3, 2);
    phi:=hom<Dll -> Dll| [Dll!Eltseq([T[j,i]: j in [1..gg]]):i in [1..3]] cat [Dll.4]>;
    R:=phi(Dll.2); RR:=point_from_basis_mumford(R,B);
    for j in [1..l-1] do
       ltors[j*R]:=j*RR;
    end for;
    precomp["ltors"]:=ltors;
    precomp["ltors_symplectic-basis"]:=T;
    return true,B,precomp;
  elif #B eq 3 then
    if theta eq 0 then
      vprint AVIsogenies, 6: "Pairings in Weil";
      vtime AVIsogenies, 6:e1:=WeilPairing(B[1],P,l);
      vtime AVIsogenies, 6:e2:=WeilPairing(B[2],P,l);
      vtime AVIsogenies, 6:e3:=WeilPairing(B[3],P,l);
    else
      Ptheta,Pros:=mumford_to_theta(P,precomp);
      L:=precomp["ltors_theta"];
      Bros:=precomp["ltors_basis-ros"];
      PQtheta1:=mumford_to_lvl2(Pros+Bros[1],precomp);
      vprint AVIsogenies, 6: "Pairings in Theta";
      vtime AVIsogenies, 6:e1:=pairing_PQ(l,L[Dll.1],Ptheta,PQtheta1,precomp["HK","P0"]);
      PQtheta2:=mumford_to_lvl2(Pros+Bros[2],precomp);
      vtime AVIsogenies, 6:e2:=pairing_PQ(l,L[Dll.2],Ptheta,PQtheta2,precomp["HK","P0"]);
      PQtheta3:=mumford_to_lvl2(Pros+Bros[3],precomp);
      vtime AVIsogenies, 6:e3:=pairing_PQ(l,L[Dll.3],Ptheta,PQtheta3,precomp["HK","P0"]);
    end if;
    U:=precomp["zetalog"];
    ee1:=U[e1]; ee2:=U[e2]; ee3:=U[e3];
    W:=precomp["ltors_pairings"];
    T:=precomp["ltors_symplectic-basis"];
    phi:=hom<Dll -> Dll| [Dll!Eltseq([T[j,i]: j in [1..gg]]):i in [1..3]] cat [Dll.4]>;
    M:=Matrix(GF(l),gg,1,[ee1,ee2,ee3,0]);
    M:=Transpose(T)*M;
    if M[2,1] eq 0 then //P is in B
      P1:=point_from_basis_mumford(Dll.1@phi,B);
      P3:=point_from_basis_mumford(Dll.3@phi,B);
      P:=P+(Z!M[3,1])*P1-(Z!M[1,1])*P3;
      coeff2:=Rep([i: i in Keys(ltors) | ltors[i] eq P]);
      return false, coeff2-(Z!M[3,1])*Dll.1@phi+(Z!M[1,1])*Dll.3@phi, precomp;
    else // P is a new point
      Append(~B,P);
      if theta eq 1 then
        L:=precomp["ltors_theta"]; Bros:=precomp["ltors_basis-ros"];
        L[Dll.4]:=Ptheta; Bros[4]:=Pros;
        L[Dll.1+Dll.4]:=PQtheta1; L[Dll.2+Dll.4]:=PQtheta2;
        L[Dll.3+Dll.4]:=PQtheta3;
        precomp["ltors_theta"]:=L; precomp["ltors_basis-ros"]:=Bros;
      end if;
      W[1,4]:=ee1; W[4,1]:=-ee1;
      W[2,4]:=ee2; W[4,2]:=-ee2;
      W[3,4]:=ee3; W[4,3]:=-ee3;
      precomp["ltors_pairings"]:=W;
      B[4]:=P; precomp["ltors_basis"]:=B;
      for i in [1..g] do
        M:=Transpose(T)*W*T;
        //e_g+i <- f_j st e_i/e_g+i = 1
        j:=i; repeat j+:=1; until M[i,j] ne 0 or j gt g;
        if j gt g then j:=g+i-1; repeat j+:=1; until M[i,j] ne 0; end if;
        MultiplyColumn(~T,1/M[i,j],j);
        SwapColumns(~T,j,g+i);
        M:=Transpose(T)*W*T;
        for k in [i+1..g] do
          // e_k   <- e_k   - (e_k  /e_g+i) e_i - (e_i/e_k  ) e_g+i
          // e_g+k <- e_g+k - (e_g+k/e_g+i) e_i - (e_i/e_g+k) e_g+i
          AddColumn(~T,-M[k  ,g+i], i  , k);
          AddColumn(~T,-M[i  ,k]  , g+i, k);
          AddColumn(~T,-M[g+k,g+i], i  , g+k);
          AddColumn(~T,-M[i  ,g+k], g+i, g+k);
        end for;
      end for;
    end if;
    precomp["ltors_symplectic-basis"]:=T;
    return true,B,precomp;
  elif #B eq 4 then
    r:=[]; U:=precomp["zetalog"];
    if theta eq 0 then
      vprint AVIsogenies, 6: "Pairings in Weil";
      vtime AVIsogenies, 6:r:=[U[WeilPairing(P,b,l)]: b in B];
    else
      Ptheta,Pros:=mumford_to_theta(P,precomp);
      vprint AVIsogenies, 6: "Pairings in Theta";
      for i in [1..#B] do
        Q:=B[i]; Qros:=precomp["ltors_basis-ros"][i];
        Qtheta:=precomp["ltors_theta",Dll.i];
        PQtheta:=mumford_to_lvl2(Pros+Qros,precomp);
        vtime AVIsogenies, 6: Append(~r,U[pairing_PQ(l,Ptheta,Qtheta,PQtheta,precomp["HK","P0"])]);
      end for;
    end if;
    g:=2; M:=Matrix(GF(l),gg,1,r);
    T:=precomp["ltors_symplectic-basis"];
    M:=Transpose(T)*M; r:=[];
    for i in [1..gg] do
      if i le g then
        r[i]:=+M[i+g,1];
      else
        r[i]:=-M[i-g,1];
      end if;
    end for;
    phi:=hom<Dll -> Dll| [Dll!Eltseq([T[j,i]: j in [1..gg]]):i in [1..gg]]>;
    return false,(Dll!r)@phi,precomp;
  end if;
end function;

//ldtors = -d -> just check the l^d-torsion
//ldtors = 0  -> compute the l^\infty torsion
//ldtors = d  -> compute the l^d tors
// Same as GetTorsionBasis, but use the function above to speed up things
// with pairings and save memory. The parameters are as GetTorsionBasis, or
// get passed to new_ltors_pointG2
// ltors_deg: the degree where the points of l-torsion are defined inside
// the extension of degree k we work with. Usually the points of l-torsion
// will be defined over a smaller subfield than the points of l^d-torsion,
// and we only need to compute pairings (and convert to theta) on this
// points, so we can work on this field for the conversion.
/* Only work in dimension 2!*/
function GetTorsionBasisG2(J,l,k:precomp:=AssociativeArray(), frob:=FrobeniusPoly(J),theta:=1, ldtors:=0, save_mem:=0, ltors_deg:=k)
  IndentPush();
  vprint AVIsogenies,5: l,"-torsion: k=", k, "k0=", ltors_deg, "ldtors=", ldtors, "theta=", theta, "save_mem=", save_mem;
  assert IsPrime(l); // TODO: relax this condition
  gg:=2*Dimension(J);
  if l eq 2 then theta:=0; end if;
    F:=BaseRing(J); F2:=ext<F|k: Optimize:=false>;
  //when we compute the l^d-torsion, for the pairings we work with points
  //of l-torsion, so we can't work with a lower degree
  Ftors:=ext<F|ltors_deg: Optimize:=false>;
  assert k mod ltors_deg  eq 0;
  Embed(Ftors,F2);
  if theta eq 1 and save_mem ne -1 then
    precompute_mumford_to_theta(~precomp,J,Ftors);
  end if;
  Jtors:=BaseChange(J,Ftors);
  J:=BaseChange(J,F2);
  c:=CardFromFrob(frob,k); d:=Valuation(c,l); c:=c div l^d;
  vprint AVIsogenies, 5: "Points:", Round(Log(2,c)), d;
  b:=0;//number of random points
  if not IsDefined(precomp,"ltors_basis") then
    Dll:=AbelianGroup([l: i in [1..gg]]);
    B:=[Parent(Jtors!0)|];
    LB:=[];//backtracking info for the basis B
    LBAbstract:=[Dll.i : i in [1..gg]]; //the abstract backtracking basis
    T:=AssociativeArray(); //we index the l-torsion by D
    T[Dll.0]:=Jtors!0;
    precomp["ltors"]:=T; precomp["ltors_basis"]:=B;
    precomp["ltors_backtrack"]:=LB;
    precomp["ltors_abstract_backtrack"]:=LBAbstract;
    linfty:=0;
  else
    //we update the precomputed data (in case they were computed in a
    //smaller field)
    B:=precomp["ltors_basis"];
    LB:=precomp["ltors_backtrack"];
    if not IsEmpty(LB) then
      linfty:=&+[#LB[i]: i in [1..#LB]];
    end if;

    //if we already have everything, we can leave, no need to coerce the
    //data in a bigger field
    test1:=ldtors gt 0 and #B eq gg and &and[#LB[i] ge ldtors: i in [1..#B]];
    seq:=[-ldtors-#LB[i]: i in [1..#B] | #LB[i] lt -ldtors];
    test2:=ldtors lt 0 and
           d-linfty lt -ldtors*(gg-#B)+(IsEmpty(seq) select 0 else &+seq);
    if test1 or test2 then
      IndentPop();
      return B,LB,precomp;
    end if;


    B:=[Jtors!i: i in precomp["ltors_basis"]];
    precomp["ltors_basis"]:=B;
    LB:=[[J!i: i in LB[j]]: j in [1..#LB]];
    LBAbstract:=precomp["ltors_abstract_backtrack"];
    ltors:=precomp["ltors"];
    Dll:=Universe(Keys(ltors));
    for i in Keys(ltors) do
      ltors[i]:=Jtors!ltors[i];
    end for;
    if IsDefined(precomp,"ltors_basis-ros") then
      Jros:=precomp["HK","HnJ"];
      Bros:=[Jros!i: i in precomp["ltors_basis-ros"]];
      precomp["ltors_basis-ros"]:=Bros;
    end if;
    precomp["ltors"]:=ltors;
  end if;
  while linfty lt d do
    test1:=ldtors gt 0 and #B eq gg and &and[#LB[i] ge ldtors: i in [1..#B]];
    seq:=[-ldtors-#LB[i]: i in [1..#B] | #LB[i] lt -ldtors];
    test2:=ldtors lt 0 and
           d-linfty lt -ldtors*(gg-#B)+(IsEmpty(seq) select 0 else &+seq);
    if test1 or test2 then break; end if;


    P:=c*Random(J);
    vprint AVIsogenies, 5: "#B:", #B, "linf:", linfty, "#ltors:", #Keys(precomp["ltors"]);
    vprint AVIsogenies, 5: "************ New point **************";
    LP:=[]; b+:=1;
    while true do
      if P eq J!0 then vprint AVIsogenies, 5: "Bad Luck!"; break; end if;
      lP:=l*P; Insert(~LP,1,P);
      if lP eq J!0 then //P is a l-torsion point
        new,res,precomp:=new_ltors_pointG2(Jtors!P,B,precomp: theta:=theta,
        save_mem:=save_mem);
        if new then
          vprint AVIsogenies, 5: "New generator!";
          B:=res;
          LB[#LB+1]:=LP;
          //we can update linfty
          linfty+:=#LP;
          break;
        else
          // we either backtrack, or update the basis B
          invTP:=res;
          phi:=hom<Dll->Dll |LBAbstract>;
          Pabstract:=invTP@@phi; DP:=Eltseq(Pabstract);
          basis:=[i: i in [1..#B] | DP[i] ne 0];
          nP:=#LP; lvlbasis:=[#LB[i]: i in basis];
          max:=Max(lvlbasis);
          if nP le max then // we backtrack
            maxbasis:=[i: i in basis | #LB[i] ge nP];
            P:=LP[#LP]-&+[DP[i]*LB[i, nP]: i in maxbasis];
            //P:=LP[#LP]-&+[DP[i]*LB[i, Min(#LB[i],nP)]: i in basis];
            LP:=[];
            vprint AVIsogenies, 5: "Backtracking", nP, "steps";
            continue;
          else // we update B
            //min:=Min(lvlbasis);
            i0:=Rep([i: i in basis | #LB[i] eq max]);
            LBAbstract[i0]:=invTP;
            LB[i0]:=LP;
            vprint AVIsogenies, 5: "Found higher point";
            //LB;LBAbstract;"-------------------------------";
            linfty+:=nP-max;
            break;
          end if;
        end if;
      end if;
      P:=lP;
    end while;
  end while;
  vprint AVIsogenies, 5: "#B:", #B, "linf:", linfty, "#ltors:", #Keys(precomp["ltors"]);
  vprint AVIsogenies, 5: "We did", b, "try";
  IndentPop();
  precomp["ltors_backtrack"]:=LB;
  precomp["ltors_abstract_backtrack"]:=LBAbstract;
  return B,LB,precomp; //invT,LB;
end function;

//**** Basis to l-torsion ****//

function basis_to_torsion(B,l)
  Dll:=AbelianGroup([l: i in [1..#B]]);
  J:=Universe(B); ltors:=AssociativeArray();
  ltors[Dll.0]:=J!0;
  for z in [1..#B] do
    for i in Keys(ltors) do for j in [1..l-1] do
      ltors[i+j*Dll.z]:=ltors[i]+j*B[z];
    end for; end for;
  end for;
  return ltors;
end function;


//**** Finding rational symplectic subgroups ****//

procedure precompute_abstract_subgroups(~precomp,l,g: range:=[g..2*g],
isotropic)
  gg:=2*g; Dll:=AbelianGroup([l: j in [1..gg]]);
  if not IsDefined(precomp,"l") then
    precomp["l"]:=AssociativeArray();
  end if;
  precompl:=precomp["l"];
  if not IsDefined(precompl,"abstract_subgroups") then
    precompl["abstract_subgroups"]:=AssociativeArray();
  end if;
  subgroups:=precompl["abstract_subgroups"];
  for i in range do
    vprint AVIsogenies,7: "Abstract",l,g,"subgroups in rank",i;
    // vtime AVIsogenies,7: subgroups[i]:=[[Dll!i: i in Generators(H`subgroup)]: H in Subgroups(Dll: Sub:=[l: i in [1..g]])];
    vtime AVIsogenies,7: subgroups[i]:=GenerateSubgroupsG2(Dll,i:
    isotropic:=isotropic);
  end for;
  precompl["abstract_subgroups"]:=subgroups;
  precomp["l"]:=precompl;
end procedure;


/* This is like abstract_point_from_pairing(W,fsymp)
   But if B is obtained from GetTorsionBasisG2, precomp already contains
the needed information

*/
function abstract_point_from_basis(P,B,precomp : theta:=1)
  ltors:=precomp["ltors"];
  Dll:=Universe(Keys(ltors));
  l:=Invariants(Dll)[1];
  if #Keys(ltors) eq l^#B then
    return Rep([i: i in Keys(ltors) | ltors[i] eq P]);
  else
      r,abstract:=new_ltors_pointG2(P,B,precomp : theta:=theta);
      assert not r;
      return abstract;
  end if;
end function;


/* From the basis B, compute the rationnal subgroups of rank g

theta=1 to use the theta pairing algorithm,
theta=0 to use the usual Weil
theta=-1 Don't used pairing. Thus don't search for simplectic basis

pairing with Mumford coordinates
isotropic=true to look only for isotropic subgroups
Return the kernels given by their basis, and the kernels given by their
basis in Dll, according to the basis B
*/
function RationalSymplecticSubgroups(l,B,F,precomp: theta:=1, isotropic:=true)
  J:=Universe(B); g:=Dimension(J);  gg:=2*g;
  precompute_abstract_subgroups(~precomp,l,g: range:=[#B], isotropic:=isotropic);
  Dllsubgroups:=precomp["l","abstract_subgroups",#B];
  //Dll:=Universe(Rep(Dllsubgroups));
  Dll:=Universe(Keys(precomp["ltors"]));
  R:=[]; Rabstract:=[];

  IndentPush();
  if not IsDefined(precomp,"ltors_pairings") then//if not we already have the weil matrix
    if theta eq 0  then
      vprint AVIsogenies, 3: "-- Computing Weil";
      vtime AVIsogenies, 3: M,precomp:=GetWeilPairing(B,l,precomp);
    elif theta eq -1 then
      M:=ZeroMatrix(GF(l),gg,gg);
      isotropic:=false;
    else
      vprint AVIsogenies, 3: "-- Computing Weil with the theta algo";
      vtime AVIsogenies, 3: M,precomp:=GetWeilPairingInTheta(B,l,precomp);
    end if;
    precomp["ltors_pairings"]:=M;
  else
    M:=precomp["ltors_pairings"];
  end if;

  if #B eq g then
    if M eq ZeroMatrix(GF(l),gg,gg) then
      for gen in Dllsubgroups do
        Hgen:=[Dll!Eltseq(i): i in gen];
        S:=[ point_from_basis_mumford(g,B): g in Hgen];
        Include(~R,S);  Include(~Rabstract,[Dll!i: i in Hgen]);
        IndentPop(); return R,Rabstract,precomp;
      end for;
    else
      IndentPop(); return R,Rabstract,precomp;
    end if;
  end if;

  vprint AVIsogenies, 3: "-- Computing the Frobenius of the basis";
  vtime AVIsogenies,3: frobs:=[abstract_point_from_basis(Frobenius(b,F),B,precomp : theta:=theta): b in B];
  im:=[Dll!Eltseq(frobs[i]): i in [1..#frobs]] cat [Dll.i: i in [#frobs+1..gg]];
  frobmap:=hom<Dll->Dll| im >;
  if isotropic and not IsDefined(precomp,"ltors_symplectic") then
    fsymp:=SymplecticBasisFromPairingG2(B,Dll,M);
    precomp["ltors_symplectic"]:=fsymp;
  end if;
  for gen in Dllsubgroups do
    if not isotropic then
      T:=[Eltseq(h) : h in gen];
      for ij in [<i,j>: i, j in [1..#T]|i lt j] do
        i,j:=Explode(ij);
        ii:=Matrix(GF(l),1,gg,T[i]);
        jj:=Matrix(GF(l),1,gg,T[j]);
        if (ii*M*Transpose(jj))[1,1] ne 0 then continue gen; end if;
      end for;
      Hgen:=[Dll!Eltseq(i): i in gen];
    else
      Hgen:=[(Dll!Eltseq(i))@fsymp: i in gen];
    end if;
    H:=sub<Dll|Hgen>;
    if &and[g@frobmap in H: g in Generators(H)] then
      // S: image of the abstract base of the group H in J
      S:=[ point_from_basis_mumford(g,B): g in Hgen];
      Include(~R,S);  Include(~Rabstract,Hgen);
    end if;
  end for;
  IndentPop(); return R,Rabstract,precomp;
end function;

//**** patching all ****//

procedure set_l(l,~precomp)
  if not IsDefined(precomp,"l") then
    precompl:=AssociativeArray();
  else
    precompl:=precomp["l"];
  end if;
  precompl["l"]:=l;
  precomp["l"]:=precompl;
end procedure;

/*
Compute the rational maximal isotropic subgroup of the l-torsion of a jacobian J
of an hyperellitic curve.
See 00.README

The options are
  precomp : see documentation
  theta : use theta or not for pairings. See other function for comments
  ext_degree : set the maximal degree of the extension where all the subgroups
               of J isomorphic to (Z/lZ)^g are defined.
         set it to -1 if you have no clue.
  only_mumford : set to true if you only want to use Mumford coordinates.
                 otherwise, use theta coordinates.
  save_mem : don't store the points in an isotropic subgroup for a time/memory tradeoff

if l=2 we work only in Mumford coordinates.



returns R,<B,Rabstract>,precomp with
  precomp : see documentation
  R is the list of subgroups represented as a sequence of generators. These
    generators are defined in general in an extension field
  B is a part of a simplectic basis of the l-torsion (we only compute the
    elements that can lead to rational subgroups)
  Rabstract is an abstract representation of the points of the kernel in terms of the basis B
 */
intrinsic RationalSymplecticTorsionSubgroups(J::JacHyp ,l::RngIntElt :
 precomp:=AssociativeArray() , theta:=1 , ext_degree:=-1 ,
 only_mumford:=false , save_mem:=0) -> SeqEnum,Tup,Assoc
 {The sequence of rational symplectic l-torsion subgroups of J.}

  vprint AVIsogenies, 2: "** Computing ", l, "-rational isotropic subgroups";
  if l eq 2 then
    theta:=-1; only_mumford:=true; save_mem:=-1; isotropic:=false;
  else
    isotropic:=true;
  end if;

  g:=Dimension(J); H:=Curve(J); F:=BaseRing(J);
  set_l(l,~precomp); Dl:=AbelianGroup([l: i in [1..g]]);
  if not IsDefined(precomp,"frob") then
    vprint AVIsogenies, 3: "-- Compute the frobenius";
    vtime AVIsogenies, 3: frob:=FrobeniusPoly(J);
    precomp["frob"]:=frob;
  end if;
  frob:=precomp["frob"];

  if ext_degree eq -1 then
    vprint AVIsogenies, 3: "-- Computing the degree";
    vtime AVIsogenies, 3: k:=GetRationalSquareTorsionExtension(l,frob);
  else
    k:=ext_degree;
  end if;

  //vtime AVIsogenies, 3: k:=GetFullTorsionExtension(l,frob);
  if k eq 0 then  // no subgroups possible
    precomp["subgroups"]:=[];
    if not only_mumford then
      precomp["thetasubgroups"]:=[];
    end if;
    return [],[],precomp;
  end if;

  // finding where the points of the kernel live
  vprint AVIsogenies, 3: "-- Computing the", l,"-torsion over extension of deg", k;
  vtime AVIsogenies, 3: B,_,precomp:=GetTorsionBasisG2(J,l,k:precomp:=precomp, frob:=frob, ldtors:=1, save_mem:=save_mem, theta:=theta);
  gg:=#B;
    //warning: if save_mem=-1, then we expect precomp["ltors"] to
    //have the full l-torsion. If not you must call precomp["ltors"]:=basis_to_torsion(B,l);
  K:=BaseRing(Universe(B));
  vprint AVIsogenies, 3: "!! Basis:", #B, "points in", K;
  if #B lt g then
    precomp["subgroups"]:=[];
    if not only_mumford then
      precomp["thetasubgroups"]:=[];
    end if;
    return [],[],precomp;
  end if;
  if theta eq 1 then
    precompute_mumford_to_theta(~precomp,J,K);
  end if;

  vprint AVIsogenies, 3: "-- Listing subgroups";
  vtime AVIsogenies, 3: R,Rabstract,precomp:=RationalSymplecticSubgroups(l,B,F,precomp: theta:=theta, isotropic:=isotropic);
  vprint AVIsogenies, 2: #R, "subgroups over", K;
  if #R eq 0 then
    precomp["subgroups"]:=[];
    if not only_mumford then
      precomp["thetasubgroups"]:=[];
    end if;
    return [],[],precomp;
  end if;

  S:=[];
  if not only_mumford then
    vprint AVIsogenies, 3: "-- Convert the subgroups to theta coordinates";
    if theta eq 0 then
      precompute_mumford_to_theta(~precomp,J,K);
    end if;
    if not IsDefined(precomp,"ltors_theta") then
      precomp["ltors_theta"]:=AssociativeArray();
    end if;
    thetabasis,precomp:=ThetaTorsionFromMumfordBasis(B,l,precomp: onlybasis:=true);
    vtime AVIsogenies, 3: S:=abstract_subgroups_to_theta(Dl,thetabasis,Rabstract);
  end if;
  precomp["subgroups"]:=R;
  if not only_mumford  then
    precomp["thetasubgroups"]:=S;
  end if;
  return R,<B,Rabstract>,precomp;
end intrinsic;

