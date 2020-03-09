AttachSpec("../src/AVI.spec");
SetVerbose("AVIsogenies",1);
SetColumns(0);

// Prints the CM-structure of a given order.
// use as DrawLattice(Z,file : info:=InfoCM(3)>)
function InfoCM(l) 
	return function(o) 
		K:=NumberField(o); Cc:=[g : g in Automorphisms(K) | g(K.1) eq ComplexConjugate(K.1)][1];
		G,M:= PolarizedClassGroup(o);
		D:=[d[1] : d in Decomposition(o,l)];
		DD:=Set(D) join {i*j : i,j in D};
		Dl:={d : d in DD | Cc(d)*d eq ideal<o|l>};
		Sl:={M(<d,l>) : d in Dl}; Cl:=sub<G|Sl>;
		t:=Sprintf("GROUP sub<C|l>: %o\\n",Cl);
		t*:=Sprintf("GEN sub<C|l>: %o\\n",Sl);
		return t;
	end function;
end function;

function GetRandomGoodCurve(l)
	while true do
		q:=RandomPrime(7); F<x>:=PolynomialRing(FiniteField(q));
		if q le l then continue; end if;
		f:=&+[Random(BaseRing(F))*x^i : i in [0..6]];
		if Degree(f) lt 5 then continue; end if;
		s:=false; try
			H:=HyperellipticCurve(f); J:=Jacobian(H);
			X:=FrobeniusPoly(J);
			K:=NumberField(X); O:=MaximalOrder(K);
			assert not IsNormal(K);
			//assert Index(O,sub<O|[K.1,q/K.1]>) mod l ne 0;
			//assert ClassNumber(K) gt 5;
			assert GetFullTorsionExtension(l,X) lt 30;
		catch e s:=true; end try; if s then continue; end if;
		break;
	end while;
	return J;
end function;

function WriteOrdIsoCrv(J,l,file)
	R,H:=Genus2IsogenyGraph(J,[l]);

	i:=0;
	info:=AssociativeArray();
	L:=LatticeOfOrders(FrobeniusPoly(J));
	for o in Keys(L) do
		i+:=1;
		info[o]:=CodeToString(96+i);
	end for;

	vertices:=AssociativeArray();
	for r in Keys(R) do try
		print "=====>",H[r];
		vertices[r]:=info[EndomorphismRing(H[r] : lattice:=L)];
	catch e print e; end try; end for;

	DrawLattice(L,file*".ord.dot" : info:=func<l|info[l]>);
	DrawGraph(R,file*".iso.dot" : vertices:=vertices);
	Write(file*".crv.mag",J);
	return 0;
end function;

/*

while true do
	l:=Random([3,5,7,11,13]);
	J:=GetRandomGoodCurve(l);
	file:="graphs/IsoGraph."*IntegerToString(l)*"."*IntegerToString(Hash(J));
	printf "\n\n================================================================\n\n";
	printf "F<x>:=PolynomialRing(FiniteField(%o));\n",#BaseRing(J);
	printf "J:=Jacobian(HyperellipticCurve(%o));\n",HyperellipticPolynomials(Curve(J));
	printf "l:=%o;\n",l;
	WriteOrdIsoCrv(J,l,file);
end while;

System("cd graphs; ls *.ord*.dot | xargs -I{} dot -Tsvg -o {}.svg {}");
System("cd graphs; ls *.iso*.dot | xargs -I{} neato -Tsvg -o {}.svg {}");

*/
