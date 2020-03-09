// This is a database of curves with interesting isogeny graphs.
//
// General form of an entry: <l,q,[coefficients of f],[coefficients of h]>
// Where l is the degree of interesting isogenies, with initial variety
// the Jacobian of y^2+h(x)y=f(x) over the finite field with q elements.

cdb:=AssociativeArray();

// l splits as the product of two primes
// ==> circle-like graph as in genus one
cdb["cm_loop"]:={
	<3,19,[12,11,3,11,15,3],[]>,
	<3,31,[26,30,7,29,14,30],[]>
};

// l splits as the product of four primes
// ==> isogeny graph is a torus quadrangulation
cdb["cm_split4"]:={
	<3,23,[5,5,12,5,7,3,8],[]>,
	<5,97,[71,17,82,41,63,56,62],[]>,
	<5,103,[97,15,8,69,63,75,3],[]>,
	<7,41,[17,31,22,8,17,21,26],[]>,
	<7,59,[12,48,53,17,50,18,11],[]>,
	<7,61,[1,54,18,17,20,8,46],[]>,
	<7,61,[29,52,30,40,16,26,52],[]>,
	<7,79,[6,18,12,35,56,46,13],[]>,
	<7,83,[46,69,72,63,19,31,28],[]>,
	<7,97,[43,70,25,4,14,81,3],[]>,
	<7,109,[8,16,11,98,59,12,98],[]>,
	<7,109,[41,11,49,52,18,83,106],[]>
};

// l ramifies at (at least) one prime
// ==> moebius strips
cdb["cm_ramified"]:={
	<2,47,[11,43,31,6,16,18,3],[]>,
	<3,17,[2,12,6,4,2,6],[]>,
	<3,17,[4,1,16,5,5,12],[]>,
	<3,23,[21,1,11,10,6,14],[]>
};

// l divides the condcutor [O_K:Z[pi]]
// ==> volcano as in genus one
cdb["volcano_tree"]:={
	<3,61,[53,51,33,57,23,52,17],[]>,
	<3,61,[15,15,56,38,25,29,55],[]>,
	<3,61,[34,44,3,29,48,36,44],[]>,
	<3,61,[23,10,52,6,17,7,33],[]>
};

// l divides the condcutor [O_K:Z[pi]]
// ==> volcano with CM action at lower levels
cdb["volcano_cmg2"]:={
	<3,23,[5,5,12,5,7,3,8],[]>,
	<3,41,[25,26,33,3,24,18,10],[]>,
	<3,107,[71,95,90,93,106,56,21],[]>
};

// l divides the conductor [O_K:Z[pi]]
// ==> BIG volcanoes
cdb["volcano_big"]:={
	<3,71,[7,38,21,6,40,6,18],[]>,
	<3,181,[116,15,161,55,166,162,78],[]>
};


cdb_jacs:={};
for g in &join[cdb[i] : i in Keys(cdb)] do
	l:=g[1];
        F:=PolynomialRing(FiniteField(g[2]));
	f:=F!g[3];
	h:=F!g[4];
        J:=Jacobian(HyperellipticCurve(f,h));
	Include(~cdb_jacs,<l,J>);
end for;
