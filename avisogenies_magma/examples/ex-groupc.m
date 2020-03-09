// Returns a (small) random quartic CM field - for debugging purposes

function RandomCMField()
  try
    return NumberField(FrobeniusPoly(Jacobian(HyperellipticCurve(
    PolynomialRing(FiniteField(RandomPrime(7)))![Random([1..128]) : i in [1..7]]))));
  catch e
    zero:=0;
  end try;
end function;

F<x>:=PolynomialRing(FiniteField(31));
J:=Jacobian(HyperellipticCurve(10*x^6 + 25*x^5 + 24*x^4 + 23*x^3 + 27*x^2 + 23*x + 22));
// J:=Jacobian(HyperellipticCurve(&+[Random(F)*x^i : i in [0..6]]));
O:=MaximalOrder(NumberField(FrobeniusPoly(J)));
G,M:=PolarizedClassGroup(O);
print G;
// {M(i[1]) : i in Factorization(Domain(M)[1]!11)};

J:=Jacobian(HyperellipticCurveFromG2Invariants([FiniteField(1609)!500,1260,1148]));
O:=MaximalOrder(NumberField(FrobeniusPoly(J)));
G,M:=PolarizedClassGroup(O);
print G;
// { M(i[1]) : i in Factorization(Domain(M)[1]!3)};

K := RandomCMField();
O := MaximalOrder(K);
G,M:=PolarizedClassGroup(O);
print G;
L := Factorization(Domain(M)[1]!3);
// [ Norm(l[1])^l[2] : l in L ];
// [ M(l[1]) : l in L];

print "Omitted application of homomorphism M -- incorrect domain.";

