/* Computing endomorphism rings of abelian varieties
* - Gaëtan Bisson
*/

intrinsic EndomorphismRing(J::JacHyp : lattice:=AssociativeArray()) -> RngOrd
  {Compute an order isomorphic to the endomorphism ring
  of J via the method of Eisentrager and Lauter.}

  // Lots of room for improvement here:
  // - ascend the lattice of orders locally and recombine data
  // - reuse torsion computations
  // - etc.

/*
AttachSpec("../src/AVI.spec");
F:=FiniteField(17);
Fx<x>:=PolynomialRing(F);
f:=&+[Random(F)*x^i : i in [0..6]];
J:=Jacobian(HyperellipticCurve(f));
SetVerbose("AVIsogenies",5);
*/

  g:=Dimension(J);
  X:=FrobeniusPoly(J);
  if #Keys(lattice) gt 1 then L:=lattice; else L:=LatticeOfOrders(X); end if;

  K:=NumberField(Random(Keys(L)));
  assert Evaluate(X,K.1) eq 0;
  assert Basis(K) eq [K.1^i : i in [0..2*g-1]];
  _,q:=IsSquare(Norm(K.1)); q:=Integers()!q;
  M:=MaximalOrder(K);
  m:=sub<M|[K.1,q/K.1]>;
  assert GCD(Index(M,m),q) eq 1; // see GetFullTorsionExtension oops workaround below

  function Frobinou(e,b)
    bb:=b; ee:=e;
    while ee gt 0 do
      ee-:=1;
      bb:=Frobenius(bb,BaseRing(J));
    end while;
    return bb;
  end function;

  C:=[];
  for O in Keys(L) do
    c:=true;
    for d in [Eltseq(K!b) : b in Basis(O)] do
      n:=LCM([Denominator(f) : f in d]);
      for p in Factorization(n) do
        if q mod p[1] eq 0 then continue; end if; // GetFullTorsionExtension oops
        k:=GetFullTorsionExtension(p[1],X)*p[1]^(p[2]-1);
        B,BB:=GetTorsionBasis(J,p[1],k : frob:=X,ldtors:=p[2]);
        Jk:=BaseChange(J,ext<BaseRing(J)|k>);
        for b in [Jk!bb[p[2]] : bb in BB] do
          if &+[Integers()!(n*d[i])*Frobinou(i-1,b)
          : i in [1..2*g]] ne Jk!0 then c:=false; break d;
          end if;
        end for;
      end for;
    end for;
    if c then Append(~C,O); end if;
  end for;

  for c in &cat[&or[ccc in C : ccc in L[cc]] select [cc] else [] : cc in C] do
    Exclude(~C,c);
  end for;
  assert #C eq 1;
  return C[1];
end intrinsic;
