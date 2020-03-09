/* The Shimura class group
* - Gaëtan Bisson
*/

SetKantPrecision(100); // for IsTotallyPositive to work

// Returns a (small) random quartic CM field - for debugging purposes

function RandomCMField()
  try
    return NumberField(FrobeniusPoly(Jacobian(HyperellipticCurve(
    PolynomialRing(FiniteField(RandomPrime(7)))![Random([1..128]) : i in [1..7]]))));
  catch e
    zero:=0;
  end try;
end function;

// Computes a possible CM type for the CM field
function GetCMType(K)
  assert IsPrimitive(K.1);
  L,l:=SplittingField(K);
  T:={};
  for s in l do
    if not s in {ComplexConjugate(t) : t in T} then Include(~T,s); end if;
  end for;
  return [hom<K->L | t> : t in T];
end function;

// We pick T[1] as a distinguished embedding of K in L.
// The tag "EMB" marks where this is used.

// Computes the reflex type of a CM type
function ReflexType(T)
  K:=Domain(Universe(T));
  L:=Codomain(Universe(T));
  assert IsPrimitive(K.1);
  P:=[t(K.1) : t in T];
  Q:=[g : g in Automorphisms(L) | g(P[1]) in P]; // EMB // induced CM type on L
  R:={q^-1 : q in Q};
  S:=[g : g in Automorphisms(L) | {g*r : r in R} eq R]; // S is the fixator of the
  U:=FixedField(L,S); assert IsPrimitive(U.1);          // primitive CM type inducing R
  V:=[hom<U->L | rU> : rU in {r(U.1) : r in R}];        // (which is V, the reflex type)
  return V;
end function;

// Computes the type norm map
function TypeNorm(T)
  Q:=ReflexType(T);
  K:=Domain(Universe(T));
  R:=Domain(Universe(Q));
  return map<K->R | x:->&*[t(x) : t in T]>;
end function;

// Computes the type norm map back from the reflex field
function ReflexTypeNorm(T)
  Q:=ReflexType(T);
  K:=Domain(Universe(T));
  R:=Domain(Universe(Q));
  return map<R->K | x:->&*[q(x) : q in Q]@@T[1]>; // EMB
end function;

// When X and Y are two Z-submodules of a number field K,
// this returns generators for their intersection.
function IntersectInField(K,Y,X)
        MX:=Matrix([Eltseq(K!x) : x in Basis(X)]);
        MY:=Matrix([Eltseq(K!x) : x in Basis(Y)]);
        n:=NumberOfRows(MY);
        m:=NumberOfRows(MX)+n;
        MYX:=Matrix([i le n select MY[i] else MX[i-n] : i in [1..m]]);
        l:=LCM([Denominator(i) : i in Eltseq(MYX)]);
        NYX:=ChangeRing(l*MYX,Integers());
        BYX:=Basis(Kernel(NYX));
        EYX:=Matrix([Eltseq(ChangeRing(b,Rationals()))[1..n] : b in BYX]);
        CYX:=EYX*MY;
        DYX:=[K!Eltseq(CYX[i]) : i in [1..NumberOfRows(CYX)]];
        return [Y!d : d in DYX];
end function;

// Induced reflex type norm on ideals
function ReflexTypeNormIdeal(O)
  K:=NumberField(O);
  T:=GetCMType(K);
  Q:=ReflexType(T);
  R:=Domain(Universe(Q));
  L:=Codomain(Universe(Q));
  return map<Parent(ideal<MaximalOrder(R)|1>)->Parent(ideal<O|1>)
  | x:->ideal<O|IntersectInField(L,O,&*[ideal<MaximalOrder(L)|[q(i) : i in Basis(x)]> : q in Q])>>;
end function;

// Computes the totally real subfield of an imaginary number field
function TotallyRealSubfield(K)
  r,s:=Signature(K); assert r eq 0;
  S:=[F[1] : F in Subfields(K) | Degree(F[1]) eq s and IsTotallyReal(F[1])];
  assert #S eq 1; return S[1];
end function;

// Computes the real norm map to the totally real subfield
function RealNorm(K)
  return map<K->TotallyRealSubfield(K) | x:->x*ComplexConjugate(x)>;
end function;

// Computes a map telling whether a unit of Codomain(RN) is the norm of a unit
// of K, aka Domain(RN), together with a set of representatives.
function UnitsModuloNorm(K,RN)
  G,M:=UnitGroup(K);
  G0,M0:=UnitGroup(Codomain(RN));
  NK:=sub<G0|[RN(M(g))@@M0 : g in Generators(G)]>; // subgroup of UG0
  RQ,RM:=quo<G0|NK>;                               // quotient group
  RR:=[M0(g@@RM) : g in RQ];                       // representatives
  RM:=map<Codomain(RN)->Booleans() | x:->x@@M0 in NK>;
  return RM,[r : r in RR | r in K];
end function;

// Computes a coset representative for the units of K modulo that of K0.
function UnitsModuloUnits(K,K0)
  G,M:=UnitGroup(K);
  G0,M0:=UnitGroup(K0);
  H0:=sub<G|[(K!(M0(g)))@@M : g in Generators(G0)]>;
  RQ,RM:=quo<G|H0>;
  RR:=[M(g@@RM) : g in RQ];
  return RR;
end function;

// Renamed from GroupC...
intrinsic PolarizedClassGroup(O::RngOrd) -> GrpAb, Map
  {Shimura's gothic C class group of polarized ideal classes;
  works somewhat with non-maximal orders.}
  K:=NumberField(O); assert IsPrimitive(K.1);
  Cc:=[g : g in Automorphisms(K) | g(K.1) eq ComplexConjugate(K.1)][1];
  RN:=RealNorm(K); K0:=Codomain(RN);
  RM,RR:=UnitsModuloNorm(K,RN);
  US:=UnitsModuloUnits(K,K0);

  vprint AVIsogenies : "  Computing class group...";
  CG,CM:=RingClassGroup(O); // Sometimes, CM is not surjective - beat it.
  vprint AVIsogenies : "  (size:",#CG,"elements)";
  vprint AVIsogenies : "  Computing elements of C...";
  function GetRho(I) // Possible values of rho such that (a,rho) is in C
    II:=Cc(I)*I;
if true then
    if not IsPrincipal(II) then return []; end if;
    f,g:=IsPrincipal(ideal<MaximalOrder(K0)|IntersectInField(K,MaximalOrder(K0),II)>);
    if not f then return []; end if;
    g:=K0!g;
else
    f,g:=IsPrincipal(II);
    if not f then return []; end if;
    g:=K0![g*u : u in US | g*u in K0][1];
end if;
    return [g*u : u in RR | IsTotallyPositive(g*u)];
  end function;
  cg:=[CM(g) : g in CG];
  S:=[s : s in &join{{<c,r> : r in GetRho(c)} : c in cg}];

  vprint AVIsogenies : "  Computing group structure of C...";
  function WhoIs(I,r) // Returns k such that <I,r>~=S[k] in C
    assert Cc(I)*I eq ideal<O|r>;
    for k in [1..#S] do
      if I@@CM ne S[k][1]@@CM then continue; end if;
      f,g:=IsPrincipal(Cc(S[k][1])*I); assert f;
      if RM(r*Cc(S[k][2])/RN(g)) then return k; end if;
    end for;
  end function;
  A:=FreeAbelianGroup(#S); R:=[]; c:=0;
  while #quo<A|R> gt #S do
    if c mod 17 eq 0 then printf "    %o/%o\n",#R,#S; end if; c+:=1;
    i:=Random(1,#S); j:=Random(1,#S);
    Include(~R,A.i+A.j-A.WhoIs(S[i][1]*S[j][1],S[i][2]*S[j][2]));
  end while;
  G,M:=quo<A|R>; assert #G eq #S;

  return G,map< CartesianProduct(Parent(ideal<O|1>),K0)->G
  | x:->M(A.WhoIs(x[1],x[2])) >;
end intrinsic;
