/*
This file contains functions to compute morphisms between hyperelliptic curves
and the corresponding abelian varieties (their jacobians) with theta functions
of level 2 and 4.
- Romain Cosset

The first half is from Van Wamelen paper TODO
The last sections are functions from cosset thesis
*/
/************************* LAYOUT OF THE FILE ******************************/
/***** (1) Half-integer characteristics
/***** (2) Computations of sign with half-integer characteristics
/***** (3) Manipulations of elements of Ep
/***** (4) twisted theta
/**************************************************************************/
/***** (1) Structures
/***** (2) Change of coordinates
/***** (3) Auxiliary functions
/***** (4) Expression of Ep
/***** (5) Add two torsion
/***** (6) Mumford to Theta
/***** (7) Theta to Mumford
/*****
/**************************************************************************/
/**************************************************************************/

import "Arithmetic.m" : init_theta_point, init_theta_null_point;
import "libav.m": MyCompositeField, TowerOfField;
//***** (1) Half-integer characteristics *****//

/*
return the sum of L and M

g :: RngIntElt,L :: SeqEnum, M :: SeqEnum
 -> SeqEnum
 */
function sum_eta_half (g ,L ,M)
  assert (#L eq g) and (#M eq g) ; //"L and M should have g elements"
  return [L[i]+M[i] : i in [1..g]];
end function;

/*
return the sum of L and M

g :: RngIntElt,L :: SeqEnum, M :: SeqEnum
 -> SeqEnum
 */
function sum_eta (g ,L ,M)
  return [L[i]+M[i] : i in [1..(2*g)]];
end function;


/*
return the normalized sum of L and M

g :: RngIntElt,L :: SeqEnum, M :: SeqEnum
 -> SeqEnum
 */
function sum_eta_half_normalized (g ,L, M)
    S:=sum_eta_half(g,L,M);
    return [ Rationals() | (Integers()!(2*x) mod 2) / 2 : x in S ];
end function;


/*
return the normalized sum of L and M

g :: RngIntElt,L :: SeqEnum, M :: SeqEnum
 -> SeqEnum
 */
function sum_eta_normalized (g ,L ,M)
    S:=sum_eta(g,L,M);
    return [ Rationals() | (Integers()!(2*x) mod 2) / 2 : x in S ];
end function;


/*
 returns eta_prime as defined in Wamelen page 3089

g :: RngIntElt,i :: RngIntElt
 -> SeqEnum
 */
function eta_prime_int(g,i)
    assert i ge 0 and i le 2*g+1 ; // "i should be in [0..2g+1]";
    if i eq 0 then
        return [Rationals()|0:i in [1..g]];
    elif i eq 2*g+1 then
        return [Rationals()|0:i in [1..g]];
    end if;
    ih:=Ceiling(i / 2);
    v:=[Rationals()|0:k in [1..g]];
    v[ih]:=1/2;
    return v;
end function;



/*
{ returns eta_second as defined in Wamelen page 3089}

g :: RngIntElt,i :: RngIntElt
 -> SeqEnum
 */
function eta_second_int(g,i)
    assert i ge 0 and i le 2*g+1 ; //"i should be in [0..2g+1]";
    if i eq 0 then
        return [Rationals()|0:i in [1..g]];
    elif i eq 2*g+1 then
        return [1/2 : i in [1..g]];
    end if;
    ih:=Ceiling(i / 2);
    v:=[Rationals()|0:k in [1..g]];
    for j in [1..ih] do
        v[j]:=1/2;
    end for;
    v[ih]:=IsOdd(i) select 0 else 1/2;
    return v;
end function;



/*
{ returns eta as defined in Wamelen page 3089}

g :: RngIntElt,i :: RngIntElt
 -> SeqEnum
 */
function eta_int(g ,i )
    assert i ge 0 and i le 2*g+1 ; // "i should be in [0..2g+1]";
    if i eq 0 then
        return [Rationals()|0:i in [1..2*g]];
    elif i eq 2*g+1 then
        return [i le g select 0 else 1/2 : i in [1..2*g]];
    else
        return eta_prime_int(g,i) cat eta_second_int(g,i);
    end if;
end function;




//***** (2) Computations of sign with half-integer characteristics *****//



/*
{ returns the generalized eta as defined on a subset }

g :: RngIntElt,T :: SetEnum
 -> SeqEnum
 */
function eta_prime(g ,T )
  foo:=[0:i in [1..g]];
  for i in T do
    foo:=sum_eta_half(g,foo,eta_prime_int(g,i));
  end for;
  return foo;
end function;

/*
{ returns the normalized generalized eta as defined on a subset }

g :: RngIntElt,T :: SetEnum
 -> SeqEnum
 */
function eta_prime_normalized(g ,T )
  foo:=[0:i in [1..g]];
  for i in T do
    foo:=sum_eta_half_normalized(g,foo,eta_prime_int(g,i));
  end for;
  return foo;
end function;


/*
{ returns the generalized eta as defined on a subset }

g :: RngIntElt,T :: SetEnum
 -> SeqEnum
 */
function eta_second(g ,T)
  foo:=[0:i in [1..g]];
  for i in T do
    foo:=sum_eta_half(g,foo,eta_second_int(g,i));
  end for;
  return foo;
end function;


/*
{ returns the normalized generalized normalized eta as defined on a subset }

(g :: RngIntElt,T :: SetEnum
 -> SeqEnum
 */
function eta_second_normalized(g ,T)
  foo:=[0:i in [1..g]];
  for i in T do
    foo:=sum_eta_half_normalized(g,foo,eta_second_int(g,i));
  end for;
  return foo;
end function;


/*
{ returns the generalized eta as defined on a subset }

g :: RngIntElt,T :: SetEnum
 -> SeqEnum
 */
function eta(g ,T )
  foo:=[0:i in [1..2*g]];
  for i in T do
    foo:=sum_eta(g,foo,eta_int(g,i));
  end for;
  return foo;
end function;




 /*
{ returns the normalized generalized eta as defined on a subset }

g :: RngIntElt,T :: SetEnum
 -> SeqEnum
  */
function eta_normalized(g ,T )
  foo:=[0:i in [1..2*g]];
  for i in T do
    foo:=sum_eta_normalized(g,foo,eta_int(g,i));
  end for;
  return foo;
end function;


 /*
{ theta[eta]=sign * theta[eta_normalized] }

g :: RngIntElt,eta :: SeqEnum
 -> RngIntElt
  */
function sign_theta_normalized_eta(g,eta)
  en:=[ Rationals() | (Integers()!(2*x) mod 2) / 2 : x in eta ];

  p:=&+[en[i]*(eta[g+i]-en[g+i]) : i in [1..g]];
  return (-1)^Integers()!(2*p);
end function;

 /*
{ Abuse of notations }

g :: RngIntElt,A :: SetEnum
 -> RngIntElt
  */
function sign_theta_normalized(g ,A)
  eA:=eta(g,A);
  return sign_theta_normalized_eta(g,eA);
end function;





 /*
{ e_star as defined in Wamelen page 3090}

g :: RngIntElt, eta::SeqEnum
 -> RngIntElt
  */
function es(g , eta)

    foo:=Integers()!(4*&+[eta[i]*eta[i+g]:i in [1..g]]);
    return (-1)^foo;
end function;

 /*
{ notation abuse: compute e2(eta_A1,eta_A2) as defined in Wamelen page 3090 }

g :: RngIntElt, A1 :: SetEnum, A2 :: SetEnum
 -> RngIntElt
  */
function e2(g ,A1,A2)
  eta1:=eta(g,A1);
  eta2:=eta(g,A2);

  foo:=Integers()!(4*&+[eta2[i]*eta1[i+g]-eta1[i]*eta2[i+g]:i in [1..g]]);
  return (-1)^foo;
end function;












//***** (3) Manipulations of elements of Ep *****//




Elt_Ep := recformat<
  sign, // the "sign" of the expression (i.e: an element of k)
  power, // the power of sqrt(<a_1-a_2>) appearing in the expression
  numer, //
  denom
>;




/*
Two bad in can't be done without copying the data in magma
{ clean the commun factor in the numerator and denominator of an element of Ep}

a :: Rec
 -> Rec
 */
function clean_Elt_Ep(a)
  b:=a;
  intersection:=a`numer meet a`denom;

  for x in intersection do
    Exclude(~(b`numer), x);
    Exclude(~(b`denom), x);
  end for;

  return b;
end function;

 /*
Two bad in can't be done without copying the data in magma
{ multiply two elements of Ep}

a :: Rec , b :: Rec
 -> Rec
  */
function mult_Elt_Ep(a , b)
  c:=rec<Elt_Ep| sign:=(a`sign)*(b`sign),power:=a`power+b`power>;
  c`numer:=a`numer join b`numer;
  c`denom:=a`denom join b`denom;

  return clean_Elt_Ep(c);
end function;



 /*
Two bad in can't be done without copying the data in magma
{ divide two elements of Ep}

a :: Rec , b :: Rec
 -> Rec
  */
function div_Elt_Ep(a ,b)
  c:=rec<Elt_Ep| sign:=(a`sign)*(b`sign),power:=a`power-b`power>;
  c`numer:=a`numer join b`denom;
  c`denom:=a`denom join b`numer;

  return clean_Elt_Ep(c);
end function;



 /*
{ return the element of Ep corresponding to sqrt(a_1-a_j) given by definition2 page 11 as an element of Ep }

g :: RngIntElt,j :: RngIntElt
 -> Rec
  */
function bp_sqrt_1 (g ,j)

  assert j ne 1 ; // "the difference of branch point must be non zero";

  a:=rec<Elt_Ep|sign:=1>;


  if j eq 0 then
    a`denom:={**};
    a`numer:={**};
    a`power:=0;
  elif j eq 2 then
    a`denom:={**};
    a`numer:={**};
    a`power:=1;
  else

    V:={2,j};
    i:=3;
    while #V ne g+1 do
      if i ne j then V:=V join {i}; end if;
      i+:=1;
    end while;

    U:={2*x-1 : x in [1..(g+1)]};
    W:=U sdiff V;

    a`numer:={*eta_normalized(g,W sdiff {j}),eta_normalized(g,W sdiff {1,2})*};
    a`denom:={*eta_normalized(g,W sdiff {2}),eta_normalized(g,W sdiff {1,j})*};
    a`power:=1;


    a`sign:=sign_theta_normalized(g,W sdiff {0,j})
           *sign_theta_normalized(g,W sdiff {1,2})
           *sign_theta_normalized(g,W sdiff {0,2})
           *sign_theta_normalized(g,W sdiff {1,j});

  end if;

  return a;
end function;



 /*
{ return the numerator and the denominator of sqrt(a_j-a_i) given by definition2 page 11 as an element of Ep }

g :: RngIntElt,j :: RngIntElt,i :: RngIntElt
 -> Rec
  */
function bp_sqrt (g ,j ,i )

  assert j ne i ; // "the difference of branch point must be non zero";



  if j eq 1 then
    a:=bp_sqrt_1 (g,i);
  elif j*i eq 0 then
    a:=rec<Elt_Ep|sign:=1>;
    a`denom:={**};
    a`numer:={**};
    a`power:=0;
  else

    V:={1,i};
    k:=2;
    while #V ne g+1 do
      if k ne j then V:=V join {k}; end if;
      k+:=1;
    end while;

    U:={2*x-1 : x in [1..(g+1)]};
    W:=U sdiff V;

    a:=bp_sqrt_1(g,j);

    Include(~(a`numer),eta_normalized(g,W sdiff {0,i}));
    Include(~(a`numer),eta_normalized(g,W sdiff {1,j}));
    Include(~(a`denom),eta_normalized(g,W sdiff {0,1}));
    Include(~(a`denom),eta_normalized(g,W sdiff {i,j}));


    a`sign*:=sign_theta_normalized(g,W sdiff {0,i})
            *sign_theta_normalized(g,W sdiff {1,j})
            *sign_theta_normalized(g,W sdiff {0,1})
            *sign_theta_normalized(g,W sdiff {i,j});

  end if;

  a:=clean_Elt_Ep(a);

  return a;
end function;






//***** (4) twisted theta *****//

/*
{ return the expression of f_A as an element of Ep. It is defined by definition 3 page 13 }

g :: RngIntElt,A :: SetEnum,C :: SetEnum
 -> RngIntElt,RngIntElt,SeqEnum,SeqEnum
 */
function constant_f (g ,A ,C )

  f:=rec<Elt_Ep|sign:=1,power:=0>;


  B:={1..(2*g+1)};
  U:={2*x-1 : x in [1..(g+1)]};

  // The two theta constants which appears in the definition
  f`numer:={* eta_normalized(g,C) *};
  f`denom:={* eta_normalized(g,(U sdiff A) sdiff C) *};
  f`sign*:=sign_theta_normalized(g,C);
  f`sign*:=sign_theta_normalized(g,(U sdiff A) sdiff C);



// the four product of the definition
  if (#(A meet U) ne 0) and (#(U diff A) ne 0) then
    for i in (A meet U) do
    for k in (U diff A) do
      s := bp_sqrt (g,k,i);
      f:=mult_Elt_Ep(f,s);
    end for;
    end for;
  end if;

  if (#((B diff A) meet (B diff U)) ne 0) and (#(A diff U) ne 0) then
    for i in ((B diff A) meet (B diff U)) do
    for k in (A diff U) do
      s := bp_sqrt (g,k,i);
      f:=mult_Elt_Ep(f,s);
    end for;
    end for;
  end if;

  if (#((A sdiff C) meet (U sdiff C)) ne 0) and (#((U sdiff C) diff (A sdiff C)) ne 0) then
    for i in ((A sdiff C) meet (U sdiff C)) do
    for k in ((U sdiff C) diff (A sdiff C)) do
      s := bp_sqrt (g,k,i);
      f:=div_Elt_Ep(f,s);
    end for;
    end for;
  end if;

  if (#((B diff (A sdiff C)) meet (B diff (U sdiff C))) ne 0) and (#((A sdiff C) diff (U sdiff C)) ne 0) then
    for i in ((B diff (A sdiff C)) meet (B diff (U sdiff C))) do
    for k in ((A sdiff C) diff (U sdiff C)) do
      s := bp_sqrt (g,k,i);
      f:=div_Elt_Ep(f,s);
    end for;
    end for;
  end if;

  f:=clean_Elt_Ep(f);

  return f;
end function;





/*
{ Make a choice for the constant C in the definition ** of Cosset}

g :: RngIntElt,A :: SetEnum
 -> SetEnum
 */
function choice_of_C_Cosset(g ,A )

  assert #A le g+1 ; // "A should be of cardinal <= g+1 ";
  assert 0 notin A ; // "A should not contain 0 ";

  B:={0..(2*g+1)};
  U:={2*x-1 : x in [1..(g+1)]};

  if (#A eq g) or (#A eq g+1) then // |A|=g+1
    C:={};

  else
    n:=Floor((g+1-#A)/2);

    i:=1;Cp:={}; // 0 \in Cp  if 0 not in A
    while #Cp ne n do;
      if i notin (A join U) then Cp:=Cp join {i}; end if;
      i+:=1;
    end while;

    i:=1;Cpp:={};
    while #Cpp ne n do;
      if i in (U diff A) then Cpp:=Cpp join {i}; end if;
      i+:=1;
    end while;

    C:=Cp join Cpp;

  end if;

  return C;
end function;


 /*
{ Make a choice for all the constant C in the definition ** of Cosset}

g :: RngIntElt
 -> SetEnum
  */
function choice_of_all_C_Cosset(g)
  P:=PowerSet({1..(2*g+1)});

  C:=AssociativeArray(P);

  for A in Subsets({1..(2*g+1)}) do
    if #A le g then
      C[A]:=choice_of_C_Cosset(g,A);
    end if;
  end for;

  for A in Subsets({1..(2*g+1)}) do
    if #A ge g+1 then
      C[A]:=C[{1..(2*g+1)} diff A];
    end if;
  end for;

  return C;
end function;



/*
{ Compute the sign of s_A }

g :: RngIntElt, A :: SetEnum, C :: Assoc
 -> RngIntElt
 */
function sign_s_A(g ,A ,C )
  if #A eq 0 then return 1; end if;
  if #A eq 1 then return 1; end if;

  NN:=Integers();

  zg:=eta_second(g,{1..(2*g+1)});
  U:={2*x-1 : x in {1..(g+1)}};

  if #A ge 2*g then
    sA:=(-1)^( &+[ NN!(2*eta_prime(g,C[{}] meet U)[i]*zg[i]) : i in [1..g] ] );
    for l in {1..(2*g+1)} do
      sA*:=(-1)^( &+[ NN!(2*eta_prime(g,C[{l}] meet U)[i]*zg[i]):i in [1..g] ]);
    end for;
    return sA;
  end if;

  s:=#A;
  n:=Floor(s/2);


  sA:=(-1)^( &+[ NN!(2*eta_prime(g,C[A] meet U)[i]*zg[i]) : i in [1..g] ] );
  for l in A do
    sA*:=(-1)^( &+[ NN!(2*eta_prime(g,C[{l}] meet U)[i]*zg[i]) : i in [1..g] ]);
  end for;

  if IsOdd(s) then
    sA*:=(-1)^Floor((n+1)/2);
  else
    sA*:=(-1)^( &+[ NN!(2*eta_prime(g,C[{}] meet U)[i]*zg[i]) : i in [1..g] ] );
    sA*:=(-1)^Floor(n/2);
  end if;

  if s ge g then
    sA*:=(-1)^( &+[ NN!(2*eta_prime(g,C[A])[i]*zg[i]) : i in [1..g] ] );
  end if;


  return sA;
end function;















/**************************************************************************/

//***** (1) Structures *****//


/*
The element of E as defined in Cosset but the roots sqrt(a_i-a_j) are
expressed in terms of theta constants and sqrt(a_2-a_1) */
Elt_Ep := recformat<
  sign, // the "sign" of the expression (i.e: an element of k)
  power, // the power of sqrt(<a_1-a_2>) appearing in the expression
  numer, //
  denom
>;


ThetaPoint_analytic:= recformat<
  level, // an integer
  coord,
  numbering
>;


intrinsic AnalyticThetaPoint(
  level::RngIntElt,coord::Assoc,numbering::GrpAb) -> Rec
  {Some description goes here.}
  return rec< ThetaPoint_analytic |
    level := level, coord := coord, numbering := numbering >;
end intrinsic;


ThetaNullPoint_analytic:= recformat<
  level, // an integer
  coord,
  numbering, //the numbering map
  g,
  jacobian,
  curve,
  l2              // are we in level 2?
>;


intrinsic AnalyticThetaNullPoint(
  level::RngIntElt,coord::Assoc,numbering::GrpAb,g::RngIntElt : level2 := false) -> Rec
  {Some description goes here.}
  return rec< ThetaNullPoint_analytic |
    level := level, coord := coord,
    numbering := numbering, g := g, l2 := level2>;
end intrinsic;


//***** (2) Change of coordinates *****//

/*
Let thc be a theta null point given by analytic coordinates. Compute the
corresponding theta null point in algebraic coordinates

We use an ugly hack to avoid creating another abelian group for the new theta
null point.
Thus let A be the abelian group [2 : x in [1..g]] which is used to numbered the
algebraic theta functions

g :: RngIntElt
thc :: ThetaNullPoint_analytic
A :: GrpAb
*/
intrinsic AnalyticToAlgebraicThetaNullPoint(g::RngIntElt,thc::Rec,A::GrpAb) -> Rec
  {Compute the algebraic theta null point corrseponding to an analytic theta null point}

  point:=AssociativeArray(A);

  if thc`level eq 2 then
    for b in A do
      point[b]:=0;
      for a in A do point[b]+:=thc`coord[Eltseq(a) cat Eltseq(b)]; end for;
    end for;
    assert point[A!0] ne 0;
    return init_theta_null_point(point);

  else
    Ab:=thc`numbering;
    As:=AbelianGroup([2 : x in [1..g]]);
    NN:=Integers();

    for b in A do
      point[b]:=0;
      for a in As do
         sign:=(-1)^(&+[NN!(Eltseq(a)[i]*(Eltseq(b)[i]-(Eltseq(b)[i] mod 2))/2) : i in [1..g]]);
         point[b]+:=thc`coord[Ab!(Eltseq(a) cat Eltseq(b))]*sign;
      end for;
    end for;
    return init_theta_null_point(point);

  end if;
end intrinsic;

/*
Let th be a theta point given by analytic coordinates. Compute the corresponding
 theta point in algebraic coordinates

We use an ugly hack to avoid creating another abelian group for the new theta
null point.
Thus let A be the abelian group [2 : x in [1..g]] which is used to numbered the
algebraic theta functions

g :: RngIntElt
th :: ThetaPoint_analytic
A :: GrpAb
*/
intrinsic AnalyticToAlgebraicThetaPoint(g::RngIntElt,th::Rec,A::GrpAb) -> Rec
  {Some description goes here.}
  point:=AssociativeArray();

  if th`level eq 2 then
    for b in A do
      point[b]:=0;
      for a in A do point[b]+:=th`coord[Eltseq(a) cat Eltseq(b)]; end for;
    end for;
    return init_theta_point(point);

  else
    Ab:=th`numbering;
    As:=AbelianGroup([2 : x in [1..g]]);
    NN:=Integers();

    for b in A do
      point[b]:=0;
      for a in As do
        sign:=(-1)^(&+[NN!(Eltseq(a)[i]*(Eltseq(b)[i]-(Eltseq(b)[i] mod 2))/2) : i in [1..g]]);
        point[b]+:=th`coord[Ab!(Eltseq(a) cat Eltseq(b))]*sign;
      end for;
    end for;
    return init_theta_point(point);

  end if;
end intrinsic;

/*
Let thc be a theta null point given by algebraic coordinates. Compute the
corresponding theta null point in analytic coordinates

We use an ugly hack to avoid creating another abelian group for the new theta
null point.
Thus let Ab be the abelian group [2 : x in [1..g]] which is used to numbered the
analytic theta functions

g :: RngIntElt
thc :: ThetaNullPoint
A :: GrpAb
*/
intrinsic AlgebraicToAnalyticThetaNullPoint(g::RngIntElt,thc::Rec,Ab::GrpAb) -> Rec
  {Some description goes here.}
  A:=thc`numbering;

  if thc`l2 then
    t :=rec<ThetaNullPoint_analytic | coord:=AssociativeArray(Ab), level:=2,
                                      numbering:=Ab, g:=g, l2:=true>;
    for e in Ab do
      t`coord[e]:=0;
      for be in A do
        t`coord[e]+:=thc`coord[A!(Eltseq(e)[g+1..2*g])+be]*thc`coord[be]
              *(-1)^(&+[Eltseq(e)[i]*Eltseq(be)[i] : i in [1..g]]);
      end for;
      t`coord[e]/:=2^g;
    end for;

  else
    t :=rec<ThetaNullPoint_analytic | coord:=AssociativeArray(Ab), level:=4,
                          numbering:=Ab, g:=g, l2:=false>;
    As:=AbelianGroup([2 : x in [1..g]]);

    for e in Ab do
      t`coord[e]:=0;
      for be in As do
        c:=A!(Eltseq(e)[g+1..2*g]) + 2*A!Eltseq(be);
        t`coord[e]+:=thc`coord[c]*(-1)^(&+[Eltseq(e)[i]*Eltseq(be)[i] : i in [1..g]]);
      end for;
      t`coord[e]/:=2^g;
    end for;
  end if;

  return t;
end intrinsic;


/*
Let th be a theta point given by algebraic coordinates. Compute the
corresponding theta null point in analytic coordinates

We use an ugly hack to avoid creating another abelian group for the new theta
null point.
Thus let Ab be the abelian group [2 : x in [1..g]] which is used to numbered the
analytic theta functions

g :: RngIntElt
thc :: ThetaNullPoint
th :: ThetaPoint
A :: GrpAb
*/
intrinsic AlgebraicToAnalyticThetaPoint(g::RngIntElt,thc::Rec,th::Rec,Ab::GrpAb) -> Rec
  {Some description goes here.}
  A:=th`numbering;
  _,n:=IsPower(#A,g);

  if n eq 2 then
    t :=rec<ThetaPoint_analytic | coord:=AssociativeArray(Ab), level:=2,
                                   numbering:=Ab>;
    for e in Ab do
      t`coord[e]:=0;
      for be in A do
        t`coord[e]+:=th`coord[A!(Eltseq(e)[g+1..2*g])+be] * thc`coord[be]
              *(-1)^(&+[Eltseq(e)[i]*Eltseq(be)[i] : i in [1..g]]);
      end for;
      t`coord[e]/:=2^g;
    end for;

  else
    t :=rec<ThetaPoint_analytic | coord:=AssociativeArray(Ab), level:=4,
                          numbering:=Ab>;
    As:=AbelianGroup([2 : x in [1..g]]);

    for e in Ab do
      t`coord[e]:=0;
      for be in As do
        c:=A!(Eltseq(e)[g+1..2*g]) + 2*A!Eltseq(be);
        t`coord[e]+:=th`coord[c]*(-1)^(&+[Eltseq(e)[i]*Eltseq(be)[i] : i in [1..g]]);
      end for;
      t`coord[e]/:=2^g;
    end for;
  end if;

  return t;
end intrinsic;


//***** (3) Auxiliary functions *****//

/*
Transform a caracteristic in (1/2 Z^d )/Z^d into one in Z^d/2Z^d
eta :: SeqEnum
*/
function htg(eta)
  return [Integers()!(2*x) mod 2 : x in eta];
end function;

/*
Apply Igusa theorems to the theta with caracteristic given in the list A
The theta in the summation are taken from TH

g :: RngIntElt
A :: SeqEnum
Th :: SeqEnum
*/
function IgusaTheorem(g,A,TH)
  Ab:=TH[1]`numbering;

  n1:=[Integers()!(A[1][i]+A[2][i]+A[3][i]+A[4][i])/2 : i in [1..2*g]];
  n2:=[Integers()!(A[1][i]+A[2][i]-A[3][i]-A[4][i])/2 : i in [1..2*g]];
  n3:=[Integers()!(A[1][i]-A[2][i]+A[3][i]-A[4][i])/2 : i in [1..2*g]];
  n4:=[Integers()!(A[1][i]-A[2][i]-A[3][i]+A[4][i])/2 : i in [1..2*g]];

  p:=0;
  for a in Ab do
    ap:=[Eltseq(a)[i]/2 : i in  [1..2*g]];

    t:=(-1)^(Integers()!(&+[4*A[1][i]*ap[g+i] : i in [1..g]]));
    t*:=TH[1]`coord[[(htg(n1)[i]+Eltseq(a)[i]) mod 2 : i in [1..2*g]]];
    t*:=TH[2]`coord[[(htg(n2)[i]+Eltseq(a)[i]) mod 2 : i in [1..2*g]]];
    t*:=TH[3]`coord[[(htg(n3)[i]+Eltseq(a)[i]) mod 2 : i in [1..2*g]]];
    t*:=TH[4]`coord[[(htg(n4)[i]+Eltseq(a)[i]) mod 2 : i in [1..2*g]]];
    t*:=sign_theta_normalized_eta(g,sum_eta(g,n1,ap));
    t*:=sign_theta_normalized_eta(g,sum_eta(g,n2,ap));
    t*:=sign_theta_normalized_eta(g,sum_eta(g,n3,ap));
    t*:=sign_theta_normalized_eta(g,sum_eta(g,n4,ap));
    p+:=t;
  end for;

  return p/2^g;
end function;




//***** (4) Expression of Ep *****//

/*
Compute the constant f_S^2 from the theta constant of level 2


g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
A :: SetEnum
C :: SetEnum
 */
function constant_f2_level2(g,a,thc2,A,C)

  Ab:=thc2`numbering;

  U:={2*x-1 : x in [1..(g+1)]};
  B:={1..(2*g+1)};

  // the two theta constants which appear in the definition
  f2 :=thc2`coord[Ab!htg(eta_normalized(g,C))];
  f2/:=thc2`coord[Ab!htg(eta_normalized(g,(U sdiff A) sdiff C))];


// the four product of the definitions
  if (#(A meet U) ne 0) and (#(U diff A) ne 0) then
    for i in (A meet U) do
    for k in (U diff A) do
      f2*:=a[k]-a[i];
      if k lt i then f2*:=-1; end if;
    end for;
    end for;
  end if;

  if (#((B diff A) meet (B diff U)) ne 0) and (#(A diff U) ne 0) then
    for i in ((B diff A) meet (B diff U)) do
    for k in (A diff U) do
      f2*:=a[k]-a[i];
      if k lt i then f2*:=-1; end if;
    end for;
    end for;
  end if;

  if (#((A sdiff C) meet (U sdiff C)) ne 0) and (#((U sdiff C) diff (A sdiff C)) ne 0) then
    for i in ((A sdiff C) meet (U sdiff C)) do
    for k in ((U sdiff C) diff (A sdiff C)) do
      f2/:=a[k]-a[i];
      if k lt i then f2*:=-1; end if;
    end for;
    end for;
  end if;

  if (#((B diff (A sdiff C)) meet (B diff (U sdiff C))) ne 0) and (#((A sdiff C) diff (U sdiff C)) ne 0) then
    for i in ((B diff (A sdiff C)) meet (B diff (U sdiff C))) do
    for k in ((A sdiff C) diff (U sdiff C)) do
      f2/:=a[k]-a[i];
      if k lt i then f2*:=-1; end if;
    end for;
    end for;
  end if;


  return f2;
end function;



/*
Let f be an element of Ep. Evaluate f
rac is a root of <a_2-a_1>

g :: RngIntElt
a :: SeqEnum
rac ::
thc :: ThetaNullPoint_analytic
f :: Elt_Ep
 */
function eltEp_to_eltE(g,a,rac,thc,f)
  assert thc`level eq 4;
  Ab:=thc`numbering;

  ff:=f`sign*rac^f`power;

  for e in f`numer do
    ff*:=thc`coord[Eltseq(htg(e))];
  end for;

  for e in f`denom do
    ff/:=thc`coord[Eltseq(htg(e))];
  end for;

  return ff;
end function;


/*
Let f be an element of Ep such that in can be computed form the level 2.
Evaluate f

g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
f :: Elt_Ep
 */
function eltEp_to_eltE_lvl2(g,a,thc2,f)
  assert thc2`level eq 2;
  Ab:=thc2`numbering;

  assert IsCoercible(Integers(),f`power/2);

  ff:=f`sign*(a[2]-a[1])^(Integers()!(f`power/2));

  for e in MultisetToSet(f`numer) do
    m:=Multiplicity(f`numer,e);
    assert IsCoercible(Integers(),m/2);

    ff*:=thc2`coord[Ab!htg(e)]^(Integers()!(m/2));
  end for;

  for e in MultisetToSet(f`denom) do
    m:=Multiplicity(f`denom,e);
    assert IsCoercible(Integers(),m/2);

    ff/:=thc2`coord[Ab!htg(e)]^(Integers()!(m/2));
  end for;

  return ff;
end function;






//***** (5) Add two torsion *****//

/*
Add the two torsion points corresponding to the caracteristic eta to the theta
of level 2

g :: RngIntElt
th2 :: ThetaPoint_analytic
eta :: SeqEnum
 */
function AddTwoTorsion_lvl2(g,th2,eta)
  assert th2`level eq 2;
  Ab := th2`numbering;

  t:=th2;
  for e in Ab do
    t`coord[e]:=th2`coord[e + Ab!htg(eta)];
    t`coord[e]*:=(-1)^(Integers()!( &+[2*eta[i]*Eltseq(e)[g+i]: i in [1..g]] ));
  end for;

  return t;
end function;

/*
Add the two torsion points corresponding to the caracteristic eta to the theta
of level 4

g :: RngIntElt
th :: ThetaPoint_analytic
eta :: SeqEnum
 */
function AddTwoTorsion_lvl4(g,th,eta)
  assert th`level eq 4;
  Ab := th`numbering;

  t:=th;
  for e in Ab do
    t`coord[e]*:=(-1)^(Integers()!( &+[2*Eltseq(e)[i]*eta[g+i]: i in [1..g]] ));
    t`coord[e]*:=(-1)^(Integers()!( &+[2*eta[i]*Eltseq(e)[g+i]: i in [1..g]] ));
  end for;

  return t;
end function;










//***** (6) Mumford to Theta *****//



/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^g P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinate of th Weierstrass points of the curve

Assume that all P_i are distinct.

return the function Y_S

g :: RngIntElt
a :: SeqEnum
S :: SetEnum
points :: SeqEnum
 */
function YS_fromMumford_Generic(g,a,S,points)
  assert #S ge 2;
  assert #S le 2*g-1;
  assert #points eq g;
  assert #Seqset(points) eq g; // the divisor is not in Delta

  n:=Ceiling((#S-1)/2);

  YS:=0;
  for I in Subsets({1..g},n) do
    t:=1;
    for i in I do t*:=points[i][2]; end for; // prod y_i

    for k in {1..g} diff I do
      for l in S do t*:=points[k][1]-a[l]; end for; // (x_k-a_l)
      for i in I do t/:=points[i][1]-points[k][1]; end for; // (x_i-x_k)
    end for;
    YS+:=t;
  end for;

  return YS;
end function;


/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^g P_i - g P_infty
Assume that there exists i <=> j such that P_i = P_j but the other P_k are
  distinct
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinate of th Weierstrass points of the curve

return the function Y_S

g :: RngIntElt
a :: SeqEnum
S :: SetEnum
points :: SeqEnum
*/
function YS_fromMumford_Delta(g,a,S,points)
  assert #S ge 2;
  assert #S le 2*g-1;
  assert #points eq g;
  assert #Seqset(points) eq g-1;

  n:=Floor(#S/2);
  F:=TowerOfField([Parent(points[i][j]): i in [1..#points], j in [1..2]] cat [Universe(a)]);
  for i in [1..#points] do
    points[i][1]:=F!points[i][1];
    points[i][2]:=F!points[i][2];
  end for;
  a:=[F!a[i]: i in [1..2*g+1]];
  K<x,y>:=PolynomialRing(F,2);


  test:=true; i:=0;
  while test do
    i+:=1;
    for j in [i+1..g] do
      if points[j][1] eq points[i][1] then test:=false; end if;
    end for;
  end while;

  points:=[points[i],points[i]] cat Setseq(Seqset(points) diff {points[i]});

  Y:=0;

  for I in Subsets({3..g},n) do
    t:=1;
    for i in I do t*:=points[i][2]; end for;

    for k in {1..g} diff I do
      for l in S do t*:=points[k][1]-a[l]; end for;
      for i in I do t/:=points[i][1]-points[k][1]; end for;
    end for;
    Y+:=t;
  end for;

  if n ge 2 then
  for I in Subsets({3..g},n-2) do
    t:=1;
    for i in I do t*:=points[i][2]; end for;

    for k in {3..g} diff I do
      for l in S do t*:=points[k][1]-a[l]; end for;
      for i in I do t/:=points[i][1]-points[k][1]; end for;
      t/:=( points[1][1]-points[k][1] )^2;
    end for;
    Y+:=t;
  end for;
  end if;


  for I in Subsets({3..g},n-1) do
    t:=1;

    P:=&*[x-a[l] : l in {1..(2*g+1)} diff S] * &*[y-a[l] : l in S] -
       &*[y-a[l] : l in {1..(2*g+1)} diff S] * &*[x-a[l] : l in S];
    test,P:=IsDivisibleBy(P,x-y);
    assert test;
    t*:=Evaluate(P,[points[1][1],points[1][1]]);

    for l in S do t*:=(points[1][1]-a[l])^2; end for;

    t/:=2*points[1][2];
    for l in S do t/:=points[1][1]-a[l]; end for;

    for i in I do t*:=points[i][2]; end for;
    for i in I do t/:=points[i][1]-points[2][1]; end for;

    for k in {3..g} diff I do
      for l in S do t*:=points[k][1]-a[l]; end for;
      for i in I do t/:=points[i][1]-points[k][1]; end for;
      t/:=points[1][1]-points[k][1];
    end for;

    Y+:=t;
  end for;


  if g gt 2 then
  for I in Subsets({3..g},n-1) do

    t:=1;

    t*:=points[2][2];
    for i in I do t*:=points[i][2]; end for;
    for l in S do t*:=points[1][1]-a[l]; end for;

    for k in {3..g} diff I do
      for l in S do t*:=points[k][1]-a[l]; end for;
      for i in I do t/:=points[i][1]-points[k][1]; end for;
    end for;

    for i in I do t/:=(points[i][1]-points[2][1])^2; end for;
    for k in {3..g} diff I do t/:=(points[1][1]-points[k][1])^2; end for;

    if #I ge 1 then
      P:=&*[points[i][1]-x : i in I] * &*[y-points[k][1] : k in {3..g} diff I] -
         &*[points[i][1]-y : i in I] * &*[x-points[k][1] : k in {3..g} diff I];
    else
      P:=&*[y-points[k][1] : k in {3..g} diff I] -
         &*[x-points[k][1] : k in {3..g} diff I];
    end if;
    test,P:=IsDivisibleBy(P,x-y);
    assert test;
    t*:=Evaluate(P,[points[1][1],points[1][1]]);

    Y+:=t;
  end for;
  end if;

  return Y;
end function;





/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^g P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinate of th Weierstrass points of the curve
Let S=[S1,S2,S3,S4] with S1oS2oS3oS4=emptyset
Let C be the choice of sets in the definition of the f_A

Assume that all P_i are distinct.

Compute the function
  prod Y_Si' / prod a_l
where the second product is over l in V compted twice iff it appears in all Si

g :: RngIntElt
a :: SeqEnum
S :: SeqEnum
points :: SeqEnum
V :: SetEnum
C :: Assoc
 */
function prodYp_fromMumford_with2torsion(g,a,S,points,V,C);
  assert #points eq g;
  assert #V ge 1;
  assert #V le g;

  for j in [1..4] do
    assert #S[j] ge 2*#(V meet S[j]);
  end for;
  assert S[1] sdiff S[2] sdiff S[3] sdiff S[4] eq {};

  n:=[0,0,0,0];
  for j in [1..4] do
    n[j]:=Floor(#S[j]/2);
  end for;

  NN:=Integers();

  Bo:={1..(2*g+1)};
  zg:=eta_second(g,Bo);
  F:=TowerOfField([Parent(points[i][j]): i in [1..#points], j in [1..2]] cat [Universe(a)]);
  for i in [1..#points] do
  points[i][1]:=F!points[i][1];
    points[i][2]:=F!points[i][2];
  end for;
  a:=[F!a[i]: i in Bo];
  K<x>:=PolynomialRing(F);
  f:=&*[x-a[i] : i in Bo];
  u:=&*[x-points[i][1] : i in [1..g]];


  for l in V do
    assert Evaluate(u,F!a[l]) eq 0;
  end for;


// Let R a subset {1..g} which correspond to the index i such that P_i is the
// ramification point a_l with l in V
  R:={ Index(points,[a[l],0]) : l in V };


  W:={};
  for i in V do
    if (i in S[1]) and (i in S[2]) and (i in S[3]) and (i in S[4]) then
      W:=W join {i};
    end if;
  end for;

  ind_VmS:=[];
  for j in [1..4] do
    ind_VmS:=ind_VmS cat [{ Index(points,[a[l],0]) : l in V meet S[j] }];
  end for;

  Y:=0;
  for Ip1 in Subsets({1..g} diff R, n[1] - #(V meet S[1]) ) do
  for Ip2 in Subsets({1..g} diff R, n[2] - #(V meet S[2]) ) do
  for Ip3 in Subsets({1..g} diff R, n[3] - #(V meet S[3]) ) do
  for Ip4 in Subsets({1..g} diff R, n[4] - #(V meet S[4]) ) do
    I:=[ind_VmS[1] join Ip1,
  ind_VmS[2] join Ip2,
  ind_VmS[3] join Ip3,
  ind_VmS[4] join Ip4];
    t:=(-1)^(#W * #(V diff W));

    for l in V do for m in Bo diff V do t*:=a[l]-a[m]; end for; end for;
    for l in W do for m in Bo diff V do t*:=a[l]-a[m]; end for; end for;

    for j in [1..4] do
      for i in I[j] diff R do t*:=points[i][2]; end for;
    end for;

    for j in [1..4] do
    if #S[j] ge 2 then
      for k in {1..g} diff I[j] do
  for l in S[j] do t*:=points[k][1]-a[l]; end for;
        for i in I[j] do t/:=points[i][1]-points[k][1]; end for;
      end for;
    end if;
    end for;


    for k in {1..g} diff R do
      for l in V do t/:=points[k][1]-a[l]; end for;
    end for;

    for k in {1..g} diff R do
      for l in W do t/:=points[k][1]-a[l]; end for;
    end for;

    Y+:=t;
  end for;
  end for;
  end for;
  end for;



  //The sign
  for i in {1..4} do
    if #S[i] eq 1 then
      l:=Setseq(S[i])[1];
      Y*:=(-1)^g*Evaluate(u,a[l]);
    elif (#S[i] ge 2) and (#S[i] le 2*g-1) then
      Y*:=sign_s_A(g,S[i],C);
    elif #S[i] eq 2*g then
      Y*:=sign_s_A(g,{1..(2*g+1)},C);
      Y*:=(-1)^(Floor(g/2));
      Y*:=(-1)^( &+[NN!(2*eta_prime(g,C[S[i]])[x]*zg[x]) : x in [1..g]]);
    elif #S[i] eq 2*g+1 then
      Y*:=sign_s_A(g,{1..(2*g+1)},C);
      Y*:=(-1)^(Floor((g+1)/2));
      Y*:=(-1)^( &+[NN!(2*eta_prime(g,C[{}])[x]*zg[x]) : x in [1..g]]);
    end if;
  end for;

  return Y;
end function;






/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^g P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinate of th Weierstrass points of the curve

Assume that all P_i are distinct.
Assume that the first P_i are [a[l],0] with l in V
Assume that V is a subset S

Compute the function Y_S^2 / prod a_l  where the product is over l in V

g :: RngIntElt
a :: SeqEnum
S :: SetEnum
points :: SeqEnum
V :: SetEnum
 */
function Y_fromMumford_with2torsion(g,a,S,points,V);
  assert V subset S;
  assert #points eq g;
  assert #V ge 1;
  assert #S ge 2*#(V meet S);

  s:=#S;
  v:=#V;
  n:=Floor(s/2);

  for l in [1..v] do
    assert points[l][1] in {a[i] : i in V};
  end for;


  if v eq n then
    Y:=1;

    for l in V do
    for k in {1..(2*g+1)} diff V do
      Y*:=(a[l]-a[k]);
    end for;
    end for;

    for l in V do
    for k in {v+1..g} do
      Y/:=(points[k][1]-a[l]);
    end for;
    end for;


    for k in {v+1..g} do
      for l in S diff V do Y*:=(points[k][1]-a[l])^2; end for;
    end for;

    return Y;
  end if;

  Y:=0;
  for I in Subsets({v+1..g},n-v) do
  for J in Subsets({v+1..g},n-v) do
    t:=1;
    for i in I do t*:=points[i][2]; end for;
    for i in J do t*:=points[i][2]; end for;

    for l in V do
    for k in {1..(2*g+1)} diff V do
      t*:=(a[l]-a[k]);
    end for;
    end for;

    for l in V do
    for k in {v+1..g} do
      t/:=(points[k][1]-a[l]);
    end for;
    end for;

    for k in {v+1..g} diff I do
      for l in S diff V do t*:=points[k][1]-a[l]; end for;
      for i in I do t/:=(points[i][1]-points[k][1]); end for;
    end for;

    for k in {v+1..g} diff J do
      for l in S diff V do t*:=points[k][1]-a[l]; end for;
      for i in J do t/:=(points[i][1]-points[k][1]); end for;
    end for;

    Y+:=t;
  end for;
  end for;

  return Y;
end function;


/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^g P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinate of th Weierstrass points of the curve
Let thc2 be the theta constant of level 2

Return the theta functions of level 2 associated to points

g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
points :: SeqEnum
 */
function MumfordToTheta_2_Generic(g,a,thc2,points)
  assert thc2`level eq 2;
  assert #points eq g;

  Ab:=thc2`numbering; // (Z/2Z)^2g

  K<x>:=PolynomialRing(Parent(points[1][1]));
  u:=&*[x-points[i][1] : i in [1..g]];

  for l in [1..(2*g+1)] do
    assert Evaluate(u,a[l]) ne 0; // the divisor is generic
  end for;



  C:=choice_of_all_C_Cosset(g); // all other choices should give the same result
  U:={2*x-1 : x in [1..(g+1)]};




  th2:=rec<ThetaPoint_analytic|level:=2,numbering:=Ab,
                         coord:=AssociativeArray(Ab)>;


  e:=htg(eta_normalized(g,U));
  th2`coord[Ab!e]:=1/constant_f2_level2(g,a,thc2,{},C[{}]);


  for l in {1..(2*g+1)} do
    e:=htg(eta_normalized(g,U sdiff {l}));
    th2`coord[e]:=(-1)^g*Evaluate(u,a[l]);
    th2`coord[e]/:=constant_f2_level2(g,a,thc2,{l},C[{l}]);
  end for;

  for S in Subsets({1..(2*g+1)}) do
  if #S ge 2 and #S le g then
    if #Seqset(points) eq g then
      YS:=YS_fromMumford_Generic(g,a,S,points);
    elif #Seqset(points) eq g-1 then
      YS:=YS_fromMumford_Delta(g,a,S,points);
    else
    error "The case of non generic delta divisor is not yet implemented";
    end if;

    e:=htg(eta_normalized(g,U sdiff S));
    th2`coord[e]:=YS^2*(-1)^(g*#S);
    for l in S do th2`coord[e]/:=Evaluate(u,a[l]); end for;
    th2`coord[e]/:=constant_f2_level2(g,a,thc2,S,C[S]);
  end if;
  end for;

  return th2;
end function;


/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^g P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinate of th Weierstrass points of the curve
Let thc be the theta constant of level 4 associated to the curve C

Assume that all P_i are distinct.

Return the theta functions of level 4 associated to points

g :: RngIntElt
a :: SeqEnum
rac ::
thc2 :: ThetaNullPoint_analytic
points :: SeqEnum
*/

function MumfordToTheta_4_Generic(g,a,rac,thc,points)
  assert thc`level eq 4;
  assert #points eq g;


// 1 iff j is in S
  function delta(S,j)
    if j in S then return 1; else return 0; end if;
  end function;



  Ab:=thc`numbering; // (Z/2Z)^2g
  NN:=Integers();


  K<x>:=PolynomialRing(Parent(points[1][1]));
  u:=&*[x-points[i][1] : i in [1..g]];

  for l in [1..(2*g+1)] do
    assert Evaluate(u,a[l]) ne 0; // the divisor is generic
  end for;



  C:=choice_of_all_C_Cosset(g); // all other choices should give the same result
  U:={2*x-1 : x in [1..(g+1)]};
  zg:=eta_second(g,{1..(2*g+1)});



  th:=rec<ThetaPoint_analytic | level:=4,numbering:=Ab,
                          coord:=AssociativeArray(Ab)>;


  done:={};
  for S1 in Subsets({1..(2*g+1)},g) join Subsets({1..(2*g+1)},g+1) do
  if eta_second_normalized(g,U sdiff S1) eq [0 : x in [1..g]] then
  for S2 in Subsets({1..(2*g+1)},g) join Subsets({1..(2*g+1)},g+1) do
  if eta_prime_normalized(g,U sdiff S2) eq [0 : x in [1..g]] then

    ee:=sum_eta(g,eta(g,U sdiff S1),eta(g,U sdiff S2));
    e:=htg(ee);
    if e notin done then
      done:=done join {e};

      th`coord[e]:=0;
// we want this theta coordinates.

// we use the dupplication formula. t will be the general term
      for S in Subsets({1..(2*g+1)}) do
      if #S le g then

        B:=[S1 sdiff S2 sdiff S,
      U  sdiff S1 sdiff S,
      U  sdiff S2 sdiff S,
            S];

        t:=1;

        // we divide by f_Bi
        for i in {1..4} do
          t/:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,B[i],C[B[i]]));
        end for;


        // we multiply by Y_Bi'
        for i in {1..4} do
          if #B[i] eq 1 then
            l:=Setseq(B[i])[1];
            t*:=(-1)^g*Evaluate(u,a[l]);
          elif (#B[i] ge 2) and (#B[i] le 2*g-1) then
            t*:=YS_fromMumford_Generic(g,a,B[i],points);
            t*:=sign_s_A(g,B[i],C);
          elif #B[i] eq 2*g then
            t*:=&*[ points[i][2] : i in [1..g] ];
            t*:=sign_s_A(g,{1..(2*g+1)},C);
            t*:=(-1)^(Floor(g/2));
            t*:=(-1)^( &+[NN!(2*eta_prime(g,C[B[i]])[x]*zg[x]) : x in [1..g]]);
          elif #B[i] eq 2*g+1 then
            t*:=&*[ points[i][2] : i in [1..g] ];
            t*:=sign_s_A(g,{1..(2*g+1)},C);
            t*:=(-1)^(Floor((g+1)/2));
            t*:=(-1)^( &+[NN!(2*eta_prime(g,C[{}])[x]*zg[x]) : x in [1..g]]);
          end if;
        end for;


        // we divide by the u(a_l)
        for l in {1..(2*g+1)} do
      nb:=delta(B[1],l) + delta(B[2],l) + delta(B[3],l) + delta(B[4],l);
          assert IsEven(nb);
          t/:=( (-1)^g*Evaluate(u,a[l]) )^(Integers()!(nb/2));
    end for;
// t is theta[UoB1] * theta[UoB2] * theta[UoB3] * theta[UoB4] /t_empty(z)^4


      // the sign in the theta (we have changed the caracteristic
        t*:=(-1)^(&+[NN!(2*eta_prime(g,U sdiff B[1])[i]
        *(eta_second(g,U sdiff S1)[i] +
          eta_second(g,U sdiff S2)[i] +
          eta_second(g,U sdiff S)[i] -
          eta_second(g,U sdiff B[1])[i])
       ) : i in [1..g] ]);
        t*:=(-1)^(&+[NN!(2*eta_prime(g,U sdiff B[2])[i]
        *(eta_second(g,U sdiff S1)[i] +
          eta_second(g,U sdiff S)[i] -
          eta_second(g,U sdiff B[2])[i])
       ) : i in [1..g] ]);
        t*:=(-1)^(&+[NN!(2*eta_prime(g,U sdiff B[3])[i]
        *(eta_second(g,U sdiff S2)[i] +
          eta_second(g,U sdiff S)[i] -
          eta_second(g,U sdiff B[3])[i])
       ) : i in [1..g] ]);


      // the sign in the dupplication formulae
        t*:=(-1)^(&+[NN!(4*ee[i]*eta_second(g,U sdiff S)[i]) : i in [1..g] ]);



        th`coord[e]+:=t/2^g;
      end if;  // if #S le g then
      end for; // for S in Subsets({1..(2*g+1)}) do


      // scale the theta. i.e. constants used in doubling
      ep:=htg(eta_normalized(g,U sdiff S1));
      th`coord[e]*:=sign_theta_normalized(g,U sdiff S1) / thc`coord[Eltseq(ep)];
      ep:=htg(eta_normalized(g,U sdiff S2));
      th`coord[e]*:=sign_theta_normalized(g,U sdiff S2) / thc`coord[Eltseq(ep)];
      ep:=htg(eta_normalized(g,{}));
      th`coord[e]*:=sign_theta_normalized(g,{})  / thc`coord[Eltseq(ep)];


      // sign when we have normalized the caracteristic
      // Remember: e = htg(ee);
      th`coord[e]*:=(-1)^(&+[NN!(2*ee[i]*ee[g+i]-ee[i]*e[g+i]) : i in [1..g] ]);

    end if; // if e notin done
  end if;
  end for;
  end if;
  end for;

  return th;
end function;

/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^d P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinates of the Weierstrass points of the curve
Let thc2 be the theta constant of level 2

Assume that all P_i are distinct if the divisor is either theta or has a
ramification point in its support.

Return the theta functions of level 2 associated to points

g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
points :: SeqEnum
 */
intrinsic MumfordToLevel2ThetaPoint(
  g::RngIntElt,a::SeqEnum,thc2::Rec,points::SeqEnum) -> Rec
  {Some description goes here.}

  assert thc2`level eq 2;
  Ab:=thc2`numbering; // (Z/2Z)^2g

  if #points eq 0 then
    th2:=rec<ThetaPoint_analytic | level:=2, numbering:=Ab,
                             coord:=AssociativeArray(Ab) >;
    for e in Ab do th2`coord[e]:=thc2`coord[e]; end for;
    return th2;
  end if;


  K<x>:=PolynomialRing(Parent(points[1][1]));
  u:=&*[x-points[i][1] : i in [1..#points]];
  assert Degree(u) ge 1;

  up:=u;
  points_p:=points;

  V1:={};
  for l in [1..(2*g+1)] do
    if Evaluate(up,a[l]) eq 0 then V1:=V1 join {l}; end if;
  end for;




  if #points eq g and #V1 eq 0 then
    return MumfordToTheta_2_Generic(g,a,thc2,points);
  end if;



  V2:={}; l:=1;
  while Degree(up) lt g do
    if l notin V1 then
      V2:=V2 join {l};
      up*:=(x-a[l]);
      Append(~points_p,[a[l],0]);
    end if;
    l+:=1;
  end while;

  V:=V1 join V2;


  C:=choice_of_all_C_Cosset(g); // all other choices should give the same result
  U:={2*x-1 : x in [1..(g+1)]};


  th2p:=rec<ThetaPoint_analytic | level:=2, numbering:=Ab,
                            coord:=AssociativeArray(Ab) >;


  e:=htg(eta_normalized(g,U));
  th2p`coord[Ab!e]:=1/constant_f2_level2(g,a,thc2,{},C[{}]);


  for l in {1..(2*g+1)} do
    e:=htg(eta_normalized(g,U sdiff {l}));
    th2p`coord[e]:=(-1)^g*Evaluate(up,a[l]);
    th2p`coord[e]/:=constant_f2_level2(g,a,thc2,{l},C[{l}]);
  end for;

  for S in Subsets({1..(2*g+1)}) do
  if #S ge 2 and #S le g then
    if S meet V eq {} then
      YS:=YS_fromMumford_Generic(g,a,S,points_p);
      e:=htg(eta_normalized(g,U sdiff S));
      th2p`coord[e]:=YS^2*(-1)^(g*#S);
      for l in S do th2p`coord[e]/:=Evaluate(up,a[l]); end for;
      th2p`coord[e]/:=constant_f2_level2(g,a,thc2,S,C[S]);
    elif V subset S then
      Sp:={1..(2*g+1)} diff S;
      YS:=YS_fromMumford_Generic(g,a,Sp,points_p);
      e:=htg(eta_normalized(g,U sdiff Sp));
      th2p`coord[e]:=YS^2*(-1)^(g*#Sp);
      for l in Sp do th2p`coord[e]/:=Evaluate(up,a[l]); end for;
      th2p`coord[e]/:=constant_f2_level2(g,a,thc2,Sp,C[Sp]);
    elif #S lt 2*#(V meet S) then
      e:=htg(eta_normalized(g,U sdiff S));
      th2p`coord[e]:=0;
    else
      deb:=[[a[l],0] : l in V meet S];
      fin:=[points_p[i] : i in [1..g] | points_p[i] notin deb];
      YS_sq:=Y_fromMumford_with2torsion(g,a,S,deb cat fin,V meet S);
      e:=htg(eta_normalized(g,U sdiff S));
      th2p`coord[e]:=YS_sq*(-1)^(g*#(S diff V));
      for l in S diff V do th2p`coord[e]/:=Evaluate(up,a[l]); end for;
      th2p`coord[e]/:=constant_f2_level2(g,a,thc2,S,C[S]);
    end if;
  end if;
  end for;



  th2:=th2p;
  for l in V2 do
    th2:=AddTwoTorsion_lvl2(g,th2,eta(g,{l}));
  end for;

  return th2;
end intrinsic;

/*
Let D be a point in Jac(C)\Theta. D can be writen as
 D = sum_1^d P_i - g P_infty
Let points be the list of coordinates [x,y] of P_i
Let a be the x-coordinates of the Weierstrass points of the curve
Let thc be the theta constant of level 4

Assume that all P_i are distinct if the divisor is either theta or has a
ramification point in its support.

Return the theta functions of level 4 associated to points

g :: RngIntElt
a :: SeqEnum
thc :: ThetaNullPoint_analytic
points :: SeqEnum
 */
intrinsic MumfordToLevel4ThetaPoint(
  g::RngIntElt,a::SeqEnum,rac::FldElt,thc::Rec,points::SeqEnum) -> .
  {Some description goes here.}
  assert thc`level eq 4;

  Ab:=thc`numbering; // (Z/2Z)^2g

  if #points eq 0 then
    th:=rec<ThetaPoint_analytic | level:=4, numbering:=Ab,
                            coord:=AssociativeArray(Ab) >;
    for e in Ab do th`coord[e]:=thc`coord[e]; end for;
    return th;
  end if;


  NN:=Integers();
  Bo:={1..(2*g+1)};

  F:=TowerOfField([Parent(points[i][j]): i in [1..#points], j in [1..2]] cat [Universe(a)]);
  for i in [1..#points] do
    points[i][1]:=F!points[i][1];
    points[i][2]:=F!points[i][2];
  end for;
  a:=[F!a[i]: i in Bo];


  K<x>:=PolynomialRing(F);
  u:=&*[x-points[i][1] : i in [1..#points]];
  assert Degree(u) ge 1;

  up:=u;


  points_p:=points;

  V1:={};
  for l in [1..(2*g+1)] do
    if Evaluate(up,a[l]) eq 0 then V1:=V1 join {l}; end if;
  end for;



  V2:={}; l:=1;
  while Degree(up) lt g do
    if l notin V1 then
      V2:=V2 join {l};
      up*:=(x-a[l]);
      Append(~points_p,[a[l],0]);
    end if;
    l+:=1;
  end while;

  V:=V1 join V2;



// 1 iff j is in S
  function delta(S,j)
    if j in S then return 1; else return 0; end if;
  end function;



  C:=choice_of_all_C_Cosset(g); // all other choices should give the same result
  U:={2*x-1 : x in [1..(g+1)]};
  zg:=eta_second(g,{1..(2*g+1)});


  thp:=rec<ThetaPoint_analytic | level:=4, numbering:=Ab,
                           coord:=AssociativeArray(Ab) >;


  done:={};
  for S1 in Subsets({1..(2*g+1)},g) join Subsets({1..(2*g+1)},g+1) do
  if eta_second_normalized(g,U sdiff S1) eq [0 : x in [1..g]] then
  for S2 in Subsets({1..(2*g+1)},g) join Subsets({1..(2*g+1)},g+1) do
  if eta_prime_normalized(g,U sdiff S2) eq [0 : x in [1..g]] then

    ee:=sum_eta(g,eta(g,U sdiff S1),eta(g,U sdiff S2));
    e:=htg(ee);
    if e notin done then
      done:=done join {e};

      thp`coord[e]:=0;
// we want this theta coordinates.


// we use the dupplication formula. t will be the general term
      for S in Subsets({1..(2*g+1)}) do
      if #S le g then

        B:=[S1 sdiff S2 sdiff S,
      U  sdiff S1 sdiff S,
      U  sdiff S2 sdiff S,
            S];

        if ( 2*#(V meet B[1]) gt #B[1] ) or
     ( 2*#(V meet B[2]) gt #B[2] ) or
     ( 2*#(V meet B[3]) gt #B[3] ) or
     ( 2*#(V meet B[4]) gt #B[4] ) then

          t:=0;

        else // the t_Bi are non zero

          t:=1;

          // we divide by f_Bi
          for i in {1..4} do
            t/:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,B[i],C[B[i]]));
          end for;



          W:=(V meet B[1]) join (V meet B[2]) join (V meet B[3]);

      if #W ne 0 then

            // we multiply by Y_Bi'
            t*:=prodYp_fromMumford_with2torsion(g, a, B, points_p, W, C);

            // we divide by the up(a_l)
            for l in {1..(2*g+1)} do
            nb:=delta(B[1],l) + delta(B[2],l) + delta(B[3],l) + delta(B[4],l);
              assert IsEven(nb);
              if l notin W then
            if nb gt 0 then
                  t/:=( (-1)^g*Evaluate(up,F!a[l]) )^(Integers()!(nb/2));
                end if;
              end if;
         end for;
      else // if #W ne 0 then

            // we multiply by Y_Bi'
            for i in {1..4} do
            if #B[i] eq 1 then
                l:=Setseq(B[i])[1];
                t*:=(-1)^g*Evaluate(up,F!a[l]);
              elif (#B[i] ge 2) and (#B[i] le 2*g-1) then
                if #Seqset(points_p) eq #points_p then
                  t*:=YS_fromMumford_Generic(g,a,B[i],points_p);
                elif #Seqset(points_p) eq #points_p-1 then
                  t*:=YS_fromMumford_Delta(g,a,B[i],points_p);
                else
                  error "The case of non generic delta divisor is not yet implemented";
                end if;
                t*:=sign_s_A(g,B[i],C);
              elif #B[i] eq 2*g then
              t*:=&*[ points_p[i][2] : i in [1..g] ];
                t*:=sign_s_A(g,{1..(2*g+1)},C);
                t*:=(-1)^(Floor(g/2));
                t*:=(-1)^(&+[NN!(2*eta_prime(g,C[B[i]])[x]*zg[x]):x in [1..g]]);
              elif #B[i] eq 2*g+1 then
            t*:=&*[ points_p[i][2] : i in [1..g] ];
                t*:=sign_s_A(g,{1..(2*g+1)},C);
                t*:=(-1)^(Floor((g+1)/2));
                t*:=(-1)^( &+[NN!(2*eta_prime(g,C[{}])[x]*zg[x]) : x in [1..g]]);
              end if;
            end for;


            // we divide by the up(a_l)
            for l in {1..(2*g+1)} do
            nb:=delta(B[1],l) + delta(B[2],l) + delta(B[3],l) + delta(B[4],l);
              assert IsEven(nb);
              t/:=( (-1)^g*Evaluate(up,F!a[l]) )^(Integers()!(nb/2));
          end for;

          end if; // if #W ne 0 then


// t is theta[UoB1] * theta[UoB2] * theta[UoB3] * theta[UoB4] /t_empty(z)^4


          // the sign in the theta (we have changed the caracteristic
          t*:=(-1)^(&+[NN!(2*eta_prime(g,U sdiff B[1])[i]
              *(eta_second(g,U sdiff S1)[i] +
            eta_second(g,U sdiff S2)[i] +
            eta_second(g,U sdiff S)[i] -
            eta_second(g,U sdiff B[1])[i])
         ) : i in [1..g] ]);
          t*:=(-1)^(&+[NN!(2*eta_prime(g,U sdiff B[2])[i]
          *(eta_second(g,U sdiff S1)[i] +
            eta_second(g,U sdiff S)[i] -
            eta_second(g,U sdiff B[2])[i])
        ) : i in [1..g] ]);
          t*:=(-1)^(&+[NN!(2*eta_prime(g,U sdiff B[3])[i]
          *(eta_second(g,U sdiff S2)[i] +
            eta_second(g,U sdiff S)[i] -
            eta_second(g,U sdiff B[3])[i])
         ) : i in [1..g] ]);


        // the sign in the dupplication formulae
          t*:=(-1)^(&+[NN!(4*ee[i]*eta_second(g,U sdiff S)[i]) : i in [1..g] ]);


        end if; // are the t_Bi zero?


        thp`coord[e]+:=t/2^g;
      end if;  // if #S le g then
      end for; // for S in Subsets({1..(2*g+1)}) do


      // scale the theta. i.e. constants used in doubling
      ep:=htg(eta_normalized(g,U sdiff S1));
      thp`coord[e]*:=sign_theta_normalized(g,U sdiff S1) / thc`coord[Eltseq(ep)];
      ep:=htg(eta_normalized(g,U sdiff S2));
      thp`coord[e]*:=sign_theta_normalized(g,U sdiff S2) / thc`coord[Eltseq(ep)];
      ep:=htg(eta_normalized(g,{}));
      thp`coord[e]*:=sign_theta_normalized(g,{})  / thc`coord[Eltseq(ep)];


      // sign when we have normalized the caracteristic
      // Remember: e = htg(ee);
      thp`coord[e]*:=(-1)^(&+[NN!(2*ee[i]*ee[g+i]-ee[i]*e[g+i]): i in [1..g] ]);

    end if; // if e notin done
  end if;
  end for;
  end if;
  end for;

  th:=thp;
  for l in V2 do
    th:=AddTwoTorsion_lvl4(g,th,eta(g,{l}));
  end for;

  return th;
end intrinsic;


//***** (7) Theta to Mumford *****//



/*
Let D be a point in Jac(C)\Theta
  D is represented by the theta functions th of level 4
Let a be the x-coordinate of th Weierstrass points of the curve
Let rac be a root of a_2-a_1
Let thc be the theta constants of level 4
Let C be the choice of sets in the definition of the f_A

Compute the function Y_{l,m}

g :: RngIntElt
a :: SeqEnum
rac ::
thc :: ThetaNullPoint_analytic
l :: RngIntElt
m :: RngIntElt
th :: ThetaPoint_analytic
C :: Assoc
 */
function Ylm_fromTheta(g,a,rac,thc,l,m,th,C)
  assert l ne m;
  assert thc`level eq 4;
  assert  th`level eq 4;

  U:={2*x-1 : x in [1..(g+1)]};


  th_empty_4:=IgusaTheorem(g,[eta(g,U),eta(g,U),eta(g,U),eta(g,U)],
         [th,thc,thc,thc]);

  assert th_empty_4 ne 0; // we don't have a divisor Theta

  th_prod:=IgusaTheorem(g,[eta(g,U sdiff {l,m}),
         eta(g,U sdiff {l}),
         eta(g,U sdiff {m}),
         eta(g,U sdiff {})],
        [th,thc,thc,thc]);

  Y:=sign_s_A(g,{l,m},C);
  Y*:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,{l,m},C[{l,m}]));
  Y*:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,{l}  ,C[{l}]));
  Y*:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,{m}  ,C[{m}]));
  Y/:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,{}   ,C[{}]))^3;

  Y*:=th_prod/th_empty_4;

  return Y;
end function;




/*
Let D be a point in Jac(C)\Theta
  D is represented by the theta functions th of level 4
Let a be the x-coordinate of th Weierstrass points of the curve
Let rac be a root of a_2-a_1
Let thc be the theta constants of level 4

Compute the Mumford polynomials associated to D


g :: RngIntElt
a :: SeqEnum
rac ::
thc :: ThetaNullPoint_analytic
th :: ThetaPoint_analytic
 */
function ThetaToMumford_4_Generic(g,a,rac,thc,th)
  assert thc`level eq 4;
  assert  th`level eq 4;

  Ab:=th`numbering;

  F:=TowerOfField([Parent(th`coord[Eltseq(Ab!0)]),Universe(a)]);

  K<x>:=PolynomialRing(F);

  U:={2*x-1 : x in [1..(g+1)]};

  C:=choice_of_all_C_Cosset(g); // all other choices should give the same result


  th_empty_4:=IgusaTheorem(g,[eta(g,U),eta(g,U),eta(g,U),eta(g,U)],
         [th,thc,thc,thc]);

  assert th_empty_4 ne 0; // we don't have a divisor Theta


  u_al:=[F!0 : x in [1..(g+1)]];

  for l in {1..(g+1)} do
    th_numer:=IgusaTheorem(g, [ eta(g,U sdiff {l}),eta(g,U sdiff {l}),
              eta(g,U),eta(g,U) ] , [th,thc,thc,thc]);

    u_al[l]:=(-1)^g*th_numer/th_empty_4;
    u_al[l]*:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,{l},C[{l}]))^2;
    u_al[l]/:=eltEp_to_eltE(g,a,rac,thc,constant_f(g,{} ,C[{}]))^2;
  end for;

  u:=K!0;
  for i in {1..(g+1)} do
    t:=u_al[i];
    for j in ({1..(g+1)} diff {i}) do
      t*:=(x-F!a[j])/(F!a[i]-F!a[j]);
    end for;
    u+:=t;
  end for;


  v_al:=[F!0 : x in [1..g]];
  for l in {1..g} do
    V:={1..(g+1)} diff {l}; // #V=g   l notin V
    for m in V do
      t:=Ylm_fromTheta(g,a,rac,thc,l,m,th,C);
      for k in V diff {m} do t/:=(F!a[m]-F!a[k]); end for;
      v_al[l]+:=t;
    end for;
  end for;


  v:=K!0;
  for i in {1..g} do
    t:=v_al[i];
    for j in ({1..g} diff {i}) do
      t*:=(x-F!a[j])/(F!a[i]-F!a[j]);
    end for;
    v+:=t;
  end for;

  return u,v;
end function;















/*
Let D be a point in Jac(C)\Theta
  D is represented by the theta functions th2 of level 2
Let a be the x-coordinate of th Weierstrass points of the curve
Let thc2 be the theta constants of level 2

Compute the Mumford polynomials (u,v^2) associated to D


g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
th2 :: ThetaPoint_analytic
 */
function ThetaToMumford_2_Generic(g,a,thc2,th2)
  assert thc2`level eq 2;
  assert  th2`level eq 2;

  Ab:=thc2`numbering;

  NN:=Integers();
  F:=Parent(th2`coord[Ab!0]);
  K<x>:=PolynomialRing(F);

  U:={2*x-1 : x in [1..(g+1)]};
  zg:=eta_second(g,{1..(2*g+1)});

  C:=choice_of_all_C_Cosset(g); // all other choices should give the same result


  assert th2`coord[htg(eta_normalized(g,U))] ne 0;
  // we don't have a divisor Theta


  u_al:=[F!0 : x in [1..(g+1)]];

  for l in {1..(g+1)} do
    u_al[l]:=(-1)^g;
    u_al[l]*:=th2`coord[htg(eta_normalized(g,U sdiff {l}))];
    u_al[l]/:=th2`coord[htg(eta_normalized(g,U))];
    u_al[l]*:=constant_f2_level2(g,a,thc2,{l},C[{l}]);
    u_al[l]/:=constant_f2_level2(g,a,thc2,{} ,C[{}]);
  end for;

// use Lagrange interpolation
  u:=K!0;
  for i in {1..(g+1)} do
    t:=u_al[i];
    for j in ({1..(g+1)} diff {i}) do
      t*:=(x-a[j])/(a[i]-a[j]);
    end for;
    u+:=t;
  end for;
// we have u


  v2_al:=[F!0 : x in [1..(2*g-1)]];
  for l in {1..(2*g-1)} do
    V:={}; i:=1;
    while #V ne g do
      if i ne l then V:=V join {i}; end if;
      i+:=1;
    end while; // #V=g   l notin V

    for m in V do
      t :=th2`coord[htg(eta_normalized(g,U sdiff {l,m}))];
      t/:=th2`coord[htg(eta_normalized(g,U))];
      t*:=constant_f2_level2(g,a,thc2,{l,m},C[{l,m}]);
      t/:=constant_f2_level2(g,a,thc2,{} ,C[{}]);
      t*:=Evaluate(u,a[l])*Evaluate(u,a[m]);
      for k in V diff {m} do t/:=(a[m]-a[k])^2; end for;

      v2_al[l]+:=t;
    end for;

    // Now compute the terms t corresponding to m <=> n
    for m in V do
    for n in (V diff {m}) do
      t:=sign_s_A(g,{l,m},C)*sign_s_A(g,{l,n},C);

      t*:=th2`coord[htg(eta_normalized(g,U sdiff {l}))];
      t/:=th2`coord[htg(eta_normalized(g,U))]^3;
      t*:=constant_f2_level2(g,a,thc2,{l},C[{l}]);
      t/:=constant_f2_level2(g,a,thc2,{} ,C[{}])^3;

      // we need to compute s = t_lm(z) t_ln(z) t_m(z) t_n(z)
      s:=0;
      for S in Subsets({1..(2*g+1)},g+1) do
      if (l in S) and (#(S meet {m,n}) eq 1) then
        e:=eta(g,U sdiff S sdiff {l,m,n});



        r:=0; // r = theta[e](2z) theta[e](0) theta[0](0)^2
        for a in Ab do
    q:=(-1)^(NN!( &+[2*e[i]*Eltseq(a)[g+i] : i in [1..g]] ));
          q*:=th2`coord[Ab!Eltseq(htg(e))+a];
          q*:=th2`coord[a];
          r+:=q/2^g;
  end for;

        // On multiplie r par la bonne constante dans la somme

        c:= ( C[{l,m}] sdiff C[{l,n}] sdiff C[{m}] sdiff C[{n}] ) meet U;
        cst:=(-1)^(&+[NN!(2*eta_prime(g,c)[i]*zg[i]) : i in [1..g]]);
        for i in S diff {l,m,n} do
        for j in {1..(2*g+1)} diff (S join {m,n}) do
          if i gt j then
     cst/:=a[i]-a[j];
    else
     cst/:=a[j]-a[i];
          end if;
  end for;
  end for;

        cst*:=constant_f2_level2(g,a,thc2,U,C[U]);
        cst*:=constant_f2_level2(g,a,thc2,S sdiff {l,m,n},C[S sdiff {l,m,n}]);

        r*:=cst;
        // On a multiplie r par la bonne constante dans la somme

        //the sign in the sum
        r*:=(-1)^g;
        r*:=e2(g,U,S);
        r*:=es(g,eta_prime(g,{l}) cat eta_second(g,S diff {m,n}));
        r*:=es(g,eta_prime(g,{m,n}) cat eta_second(g,S diff {l}));
        r*:=es(g,eta_prime(g,{m}) cat eta_second(g,{n}));
        r*:=e2(g,{n},S);

        s+:=r/2^g;


      end if;
      end for; // for S in Subsets({1..(2*g+1)},g+1) do
      t*:=s;


      for k in V diff {m} do t/:=(a[m]-a[k]); end for;
      for k in V diff {n} do t/:=(a[n]-a[k]); end for;

      v2_al[l]+:=t;
    end for; // for m in V do
    end for; // for n in (V diff {m}) do


  end for; //  for l in {1..(2*g-1)} do



  v2:=K!0;
  for i in {1..(2*g-1)} do
    t:=v2_al[i];
    for j in ({1..(2*g-1)} diff {i}) do
      t*:=(x-a[j])/(a[i]-a[j]);
    end for;
    v2+:=t;
  end for;

  return u,v2;
end function;




/*
Let D be a point in Jac(C).
  D is represented by the theta functions th2 of level 2
Let a be the x-coordinate of th Weierstrass points of the curve
Let thc2 be the theta constants of level 2

Assume that the base field is algebraicly closed

Compute the Mumford polynomials (u,v^2) associated to D


g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
th2 :: ThetaPoint_analytic
 */
function ThetaToMumford_2_algclose(g,a,thc2,th2)
  assert thc2`level eq 2;
  assert  th2`level eq 2;

  Ab:=thc2`numbering;

  U:={2*x-1 : x in [1..(g+1)]};

  th2p:=th2;

  V:={}; l:=0;
  while th2p`coord[htg(eta_normalized(g,U))] eq 0 do
    l+:=1;
    assert l le 2*g+1;
    V:=V join {l};
    th2p:=AddTwoTorsion_lvl2(g,th2p,eta(g,{l}));
  end while;

  u,v2:=ThetaToMumford_2_Generic(g,a,thc2,th2p);


  K:=Parent(u);
  x:=K.1;

  for l in V do
    if IsDivisibleBy(u,x-a[l]) then
      d:=Degree(u);
      _,u:=IsDivisibleBy(u,x-a[l]);
      v:=Sqrt(v2);
      v2:=K!( v2 + Coefficient(v2,2*d-2)*u^2 - 2*Coefficient(v,d-1)*v*u );
    else
      d,e,f:=XGCD(u,x-a[l]);
      v:=Sqrt(v2);
      v2:=K!( v2 + (e/d)^2*u*Evaluate(v2,a[l]) - 2*e/d*u*v*Evaluate(v,a[l]) );
      u*:=x-a[l];
    end if;
  end for;


  return u,v2;
end function;



/*
Let D be a point in Jac(C).
  D is represented by the theta functions th2 of level 2
Let a be the x-coordinate of th Weierstrass points of the curve
Let thc2 be the theta constants of level 2

Note. We use an extension fields of degree 2

Compute the Mumford polynomials (u,v^2) associated to D


g :: RngIntElt
a :: SeqEnum
thc2 :: ThetaNullPoint_analytic
th2 :: ThetaPoint_analytic
*/
intrinsic Level2ThetaPointToMumford(g::RngIntElt,a::SeqEnum,thc2::Rec,th2::Rec) -> Rec
  {Some description goes here.}
  assert thc2`level eq 2;
  assert  th2`level eq 2;

  Ab:=thc2`numbering;

  U:={2*x-1 : x in [1..(g+1)]};

  th2p:=th2;

  V:={}; l:=0;
  while th2p`coord[htg(eta_normalized(g,U))] eq 0 do
    l+:=1;
    assert l le 2*g+1;
    V:=V join {l};
    th2p:=AddTwoTorsion_lvl2(g,th2p,eta(g,{l}));
  end while;

  u,v2:=ThetaToMumford_2_Generic(g,a,thc2,th2p);


  K:=Parent(u);
  x:=K.1;

  for l in V do
    if IsDivisibleBy(u,x-a[l]) then
      F:=Parent(Coefficient(u,0));
      FF:=ext<F|2>;
      KK:=PolynomialRing(FF);
      d:=Degree(u);
      _,u:=IsDivisibleBy(u,x-a[l]);
      v:=K!Sqrt(KK!v2);
      v2:=K!( v2 + Coefficient(v2,2*d-2)*u^2 - 2*Coefficient(v,d-1)*v*u );
    else
      F:=Parent(Coefficient(u,0));
      FF:=ext<F|2>;
      KK:=PolynomialRing(FF);
      d,e,f:=XGCD(u,x-a[l]);
      v:=K!Sqrt(KK!v2);
      v2:=K!( v2 + (e/d)^2*u*Evaluate(v2,a[l]) - 2*e/d*u*v*Evaluate(v,a[l]) );
      u*:=x-a[l];
    end if;
  end for;

  return u,v2;
end intrinsic;

/*
Let D be a point in Jac(C)
  D is represented by the theta functions th of level 4
Let a be the x-coordinate of th Weierstrass points of the curve
Let rac be a root of a_2-a_1
Let thc be the theta constants of level 4

Compute the Mumford polynomials associated to D

g :: RngIntElt
a :: SeqEnum
rac ::
thc :: ThetaNullPoint_analytic
th :: ThetaPoint_analytic
*/
intrinsic Level4ThetaPointToMumford(g::RngIntElt,a::SeqEnum,rac::FldElt,thc::Rec,th::Rec) -> Rec
  {}
  assert thc`level eq 4;
  assert  th`level eq 4;

  Ab:=th`numbering;
  assert Ab eq thc`numbering;

  U:={2*x-1 : x in [1..(g+1)]};

  thp:=th;

  t_empty_p:=IgusaTheorem(g,[eta(g,U) : i in [1..4]],[thp,thc,thc,thc]);

  V:={}; l:=0;
  while t_empty_p eq 0 do
    l+:=1;
    assert l le 2*g+1;
    V:=V join {l};
    thp:=AddTwoTorsion_lvl4(g,thp,eta(g,{l}));
    t_empty_p:=IgusaTheorem(g,[eta(g,U) : i in [1..4]],[thp,thc,thc,thc]);
  end while;

  u,v:=ThetaToMumford_4_Generic(g,a,rac,thc,thp);
  K:=Parent(u);
  x:=K.1;

  for l in V do
    if IsDivisibleBy(u,x-a[l]) then
      _,u:=IsDivisibleBy(u,x-a[l]);
      c:=Coefficient(v,Degree(v));
      v:=v-c*u;
    else
      del,s,_:=XGCD(u,x-a[l]);
      assert del ne 0;
      v:=v-s/del*u*Evaluate(v,a[l]);
      u*:=x-a[l];
    end if;
  end for;

  return u,v;
end intrinsic;



