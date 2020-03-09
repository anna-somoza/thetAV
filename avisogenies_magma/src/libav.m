/* Used by other function in AVIsogenies, but not directly related to
* abelian varieties
* - Romain Cosset
* - Damien Robert
*/

//**** sum of squares ****//

/*
Let l an integer, compute the decomposition of l as a sum of squares with the
minimum number of terms.
return the decomposition as a list of integers in incresing order (the sum of
their square is l)

assert l>1
*/
function SumOfSquares(l)

  test,f:=IsSquare(l);
  if test then return [f]; end if; // l is already a square

  test,a,b:=NormEquation(1,l);
  if test then return Sort([a,b]); end if; // l is a sum of 2 squares

// we try to find an integer A which is the sum of 2 square such that l-A is
// also the sum of 2 squares.
  A:=1;
  while true do
    A+:=1;
    test,a,b:=NormEquation(1,A);
    if test then
      test,c,d:=NormEquation(1,l-A);
      if test then return Sort([a,b,c,d]); end if;
    end if;
  end while;
end function;



//**** Field manipulation ****//

/*
L is a sequence of elements in a finite field. Convert L as a sequence of
elements in the smallest possible field.
*/
function GetCastMinField(L)
  K:=Universe(L);
  M:=[sub<K|l> : l in L];
  K:=ext<PrimeField(K)|LCM([Degree(m) : m in M])>;
  for m in M do Embed(m,K); end for;
  return [K!l : l in L];
end function;

/*
Let l be a sequence of finite field. Construct the smaller field containing them
 */
function ConstructOverfield(l: Optimize:=true)
  F:=PrimeField(l[1]);
  d:=Lcm([Degree(i): i in l]);
  F2:=ext<F | d: Optimize:=Optimize>;
  return F2;
end function;


function TowerOfField(L: Optimize:=true)
  F:=L[1];
  for i in [2..#L] do
    deg1:=Degree(F); deg2:=Degree(L[i]);
    deg:=LCM(deg1,deg2) div deg1;
    F:=ext<F|deg: Optimize:=Optimize>;
    Embed(L[i],F);
  end for;
  return F;
end function;

function MyCompositeField(F1,F2: embed:=true)
        F:=PrimeField(F1);
        n1:=Degree(F1); n2:=Degree(F2);
        n:=GCD(n1,n2);
        if n1 eq n then
                F0<eta>:=F2;
                if F eq F1 then return F0,hom<F1->F0|>;
                else return F0,hom<F1->F0|eta>;
                end if;
        end if;
        FF1:=sub<F1|n>;
        //FF2:=sub<F2 |n :Optimize:=false>;
        P1:=MinimalPolynomial(F1.1,FF1);
        //P2:=MinimalPolynomial(F2.1,FF2);
        Embed(FF1,F2);
        vprint AVIsogenies,5: "Building composite extension";
        vtime AVIsogenies,5: F0<eta>:=ext<F2 | P1>;
        F1bis<zeta>:=ext<FF1 | P1>;
        phi1:=hom<F1 -> F1bis | zeta>;
        phi2:=hom<F1bis -> F0 | eta>;
        if embed then
                vprint AVIsogenies,5: "Embeddings";
                vtime AVIsogenies,5: Embed(F1,F1bis);
                vtime AVIsogenies,5: Embed(F1bis,F0);
        end if;
        return F0, phi1*phi2;
end function;





//** Inverses the element of a list by doing only one inversion **//

/*
get the inverses of the elements in the sequence L, by only doing one division
The principe is the following: we build a multiplication tree, we go
bottom to up to build the multiplications, and then up to bottom to construct
the inverses we want. The trees are indiced by tuples <n_1, n_2>
*/
function InvertListMontgomery(L)
  if IsEmpty(L) then return L; end if;
  T1:=AssociativeArray();
  T2:=AssociativeArray();
  n:=#L;
  function child(tuple)
    n_1:=tuple[1];
    n_2:=tuple[2];
    assert n_1 lt n_2;
    n:=Floor((n_1+n_2)/2);
    return <n_1, n>, <n+1,n_2>;
  end function;
  procedure build_T1(tuple,~T1)
    if tuple[1] eq tuple[2] then T1[tuple]:=L[tuple[1]];
    else
      tuple1, tuple2:=child(tuple);
      build_T1(tuple1,~T1);
      build_T1(tuple2,~T1);
      T1[tuple]:=T1[tuple1]*T1[tuple2];
    end if;
  end procedure;
  build_T1(<1,n>,~T1);
  T2[<1,n>]:=1/T1[<1,n>];
  procedure build_T2(tuple,~T2)
    if tuple[1] ne tuple[2] then
      rac:=T2[tuple];
      tuple1, tuple2:=child(tuple);
      T2[tuple1]:=rac*T1[tuple2];
      T2[tuple2]:=rac*T1[tuple1];
      build_T2(tuple1,~T2);
      build_T2(tuple2,~T2);
    end if;
  end procedure;
  build_T2(<1,n>,~T2);
  return [T2[<i,i>]: i in [1..n]];
end function;

// same as before, but when there are null elements or non initialized
// elements
function  InvertGenListMontgomery(L)
  if Category(L) eq SeqEnum then
    if IsEmpty(L) then return L; end if;
    list:=[i: i in [1..#L] | IsDefined(L,i) and L[i] ne 0 ];
    Invstrip:=InvertListMontgomery([L[i]: i in list]);
    inv:=L;
    for i in [1..#list] do
      inv[list[i]]:=Invstrip[i];
    end for;
    return inv;
  elif Category(L) eq Assoc then
    K:=Keys(L);
    if IsEmpty(K) then return L; end if;
    list:=[i: i in K | L[i] ne 0 ];
    Invstrip:=InvertListMontgomery([L[i]: i in list]);
    inv:=L;
    for i in [1..#list] do
      inv[list[i]]:=Invstrip[i];
    end for;
    return inv;
  else
    error "Category not supported";
  end if;
end function;

//** Changing map fields of definition **//
function map_change(f,A,B: Check:=false)
  r:=DefiningEquations(f);
  return map< A -> B | r: Check:=Check>;
end function;
function map_change_field(f,F: Check:=false)
  A:=Domain(f);
  B:=Codomain(f);
  return map_change(f, BaseChange(A,F), BaseChange(B,F): Check:=Check);
end function;


//** Compute all the divisors of degree g of a polynomial **//

function degree_g_factors(pol,g)
  F:=Factorization(pol);
  range:=CartesianProduct([ [0..f[2]]: f in F]);
  factors:={ el: el in range | &+[el[i]*Degree(F[i,1]): i in [1..#F]] eq g};
  return [ &*[F[i,1]^el[i]: i in [1..#F]]: el in factors ];
end function;
