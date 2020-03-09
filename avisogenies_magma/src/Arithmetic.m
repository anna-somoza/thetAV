/* Arithmetic of theta and theta null points
* - Damien Robert
*/
import "libseq.m" : SequenceToArray;
import "libav.m" : InvertGenListMontgomery;

//****  Structure ****//

ThetaPoint:= recformat<
  coord,
  inv_coord, // the inverse coordinates
  prod_coord, //theta[i]theta[j]
  mixed_coord, // \sum_caracteres theta[i]theta[j]/\sum theta[k](0)theta[l](0)
  numbering
>;

ThetaNullPoint:= recformat<
  coord,
  numbering, //the numbering map
  inv_coord,
  prod_coord,
  dual_coord,
  invdual_coord, //the inverse of the dual theta constants  \sum_caracteres theta_i(0) \theta_j(0)
  mixed_coord, //to handle a theta null point as a theta point

  g,
  jacobian,
  curve,

  twotorsion, //the two torsion part
//  couple_numbering, //the numbering map for tuple <i,j>
//  dual_numbering, //the corresponding numbering map
//  mixed_numbering, // the numbering for mixed coordinates
  riemann,         // the riemann relations to use, they will differ accross theta null points if some coordinates are 0

  car,              // the characters
  l2              // are we in level 2?
>;

__null_theta_null_point:=[];

//** Group manipulation for Riemann relations **//

// Compute the subgroup of 2 torsion inside D
function get_twotorsion(D)
    return sub<D | [(Invariants(D)[i] div 2)* D.i: i in [1..#Invariants(D)]]>;
end function;

// In the Riemann relations, compute the dual quadruplet of x,y,u,v
function get_dual_quadruplet(x,y,u,v)
  r:=x+y+u+v;
  z:=Parent(r)![e div 2 : e in Eltseq(r)];
  xbis:=(z-x); ybis:=(z-y);
  ubis:=(z-u); vbis:=(z-v);
  return xbis,ybis,ubis,vbis;
end function;

// evaluate a character chi at t, a point of 2 torsion
function eval_car(chi,t)
//return (-1)^(#[i: i in [1..#Eltseq(chi)] | Eltseq(chi)[i]*Eltseq(t)[i] ne 0]);
// a bit faster
  chi:=Eltseq(chi); t:=Eltseq(t);
  return (-1)^(#[i: i in [1..#chi] | chi[i] ne 0 and t[i] ne 0] mod 2);
end function;


/*
Let D and D2 be two abelian group. Assume that D represents a subgroup of D2 is
a canonical way.
For instance D=(Z/nZ)^g and D2=(Z/mZ)^g with n|m
It is assumed that D and D2 have the same dimension.
Compute the map that includes D into D2.
 */
function IncludeSubgroup(D,D2)
  levels:=Invariants(D); g:=#levels;
  levels2:=Invariants(D2);
  assert g eq #levels2;
  assert &and [IsDivisibleBy(levels2[i],levels[i]) : i in [1..g]];
  return hom< D->D2 | [(levels2[i] div levels[i])*D2.i : i in [1..g]] >;
end function;


//** Some functions for points handling **//

/*
Find a nonzero coordinates of a « point » p. p may be of different type.
Note that this function can be used in other contexts.
 */
function get_nonzero_coord(p)
  if Category(p) eq SeqEnum then
    return [i: i in [1..#p] | p[i] ne 0][1];
  elif Category(p) eq Assoc then
    for i in Keys(p) do
      if p[i] ne 0 then return i; end if;
    end for;
  else error "Category not supported in get_nonzero_coord";
  end if;
end function;


/*
Check whether two ThetaPoints or two ThetaNullPoint are equal or not.
If proj = true we assume that the coordinates are projective and if the two
points are equal we return as a second argument the rapport Q/P
*/
function compare_points(P,Q: proj:=true)
  KeysP:=Keys(P`coord);  // this is just to avoid computing it multiple times

  if not KeysP eq Keys(Q`coord) then return false,_; end if;

  if proj then
    c:={};
    for k in KeysP do
      if P`coord[k] eq 0 and not Q`coord[k] eq 0 then
        return false,_;
      elif not P`coord[k] eq 0 and not Q`coord[k] eq 0 then
        c:=c join {Q`coord[k]/P`coord[k]};
      end if;
    end for;
    if #c eq 1 then return true,Rep(c); else return false,_; end if;
  else
    for k in KeysP do
      if not P`coord[k] eq Q`coord[k] then return false,_; end if;
    end for;
    return true,_;
  end if;
end function;

function print_point(P)
  if Category(P) eq Rec  then
    return print_point(P`coord);
  else
    g:=NumberingMap(Universe(Keys(P)));
    return [P[i@@g]: i in [1..#(Keys(P))]];
  end if;
end function;

//** Reducing points **//
// These functions are used in Riemann relations, to use their symmetry and
// reduces the number of relations we have to compute

function reduce_sym(x)
  y:= -x;
  if Eltseq(x) le Eltseq(y) then return x; else return y; end if;
end function;

function reduce_twotorsion(x)
  r:=Eltseq(x); D:=Parent(x);
  halflevels:=[i div 2: i in Invariants(D)];
  n:=#halflevels;
  for i in [1..n] do
    if r[i] ge halflevels[i] then
      r[i]:=r[i]-halflevels[i];
    end if;
  end for;
  return  D!r, x-D!r;
end function;

function reduce_symtwotorsion(x)
  x1, tx1:=reduce_twotorsion(x);
  x2, tx2:=reduce_twotorsion(-x);
  if Eltseq(x1) le Eltseq(x2) then
    return x1, tx1;
  else
    return x2, tx2;
  end if;
end function;

function reduce_symcouple(x,y)
  D:=Parent(x);
  xred:=reduce_sym(x);
  yred:=reduce_sym(y);
  if Eltseq(xred) lt Eltseq(yred) then
    return xred, yred;
  else
    return yred, xred;
  end if;
end function;

function reduce_twotorsion_couple(x,y)
  xred, tx:=reduce_twotorsion(x);
  yred, ty:=reduce_twotorsion(y);
  if Eltseq(xred) lt Eltseq(yred) then
    return xred, y+tx, tx;
  else
    return yred, x+ty, ty;
  end if;
end function;

function reduce_symtwotorsion_couple(x,y)
  xred, tx:=reduce_symtwotorsion(x);
  yred, ty:=reduce_symtwotorsion(y);
  if Eltseq(xred) lt Eltseq(yred) then
    return xred, reduce_sym(y+tx), tx;
  else
    return yred, reduce_sym(x+ty), ty;
  end if;
end function;

//** some precomputations for the addition (used by rosenhain.m) **//
function get_dual_coord(point0,chi,i,j)
  i0,j0,t:=reduce_symtwotorsion_couple(i,j);
  return point0`dual_coord[<chi,i0,j0>]*point0`car[<chi,t>];
end function;

//// Set the invariants used for the addition
// precompute the inverse coordinates of a list of points
procedure precompute_inverses(~L)
  if Category(L) eq SeqEnum then
    D:=Rep(L)`numbering;
    parcours:=[1..#L];
  elif Category(L) eq Assoc then
    D:=L[Rep(Keys(L))]`numbering;
    parcours:=Keys(L);
  else
    error "Category not supported in precompute_inverses";
  end if;

  to_inv:=[i: i in parcours | not IsDefined(L[i]`inv_coord,D.0)];
  inv:=AssociativeArray();
  for i in to_inv do
    for j in D do
      inv[<i,j>]:=L[i]`coord[Eltseq(j)];
    end for;
  end for;
  inv:=InvertGenListMontgomery(inv);
  for i in to_inv do
    for j in D do
      L[i]`inv_coord[j]:=inv[<i,j>];
    end for;
  end for;
end procedure;

function get_precompute_inverses(L)
  precompute_inverses(~L);
  return L;
end function;

// store the product of coordinates of P
// along the couple in L
// twotorsion is the 2-torsion subgroup of the numbering group D
procedure set_product_coord(~P,L,twotorsion);
  Dp:=P`numbering;Inv:=Invariants(Dp);
  k:=Inv[1]/2;
  for i in L do
    if not IsDefined(P`prod_coord,i) then
      for t in twotorsion do
        //when we need one product, we usually need all of them up to a
        //translation of the two torsion for Riemann relations
         P`prod_coord[<i[1]+t,i[2]+t>]:=P`coord[Dp!Eltseq(i[1])+Dp![k*Eltseq(t)[i]:i in [1..#Eltseq(t)]]]*P`coord[Dp!Eltseq(i[2])+Dp![k*Eltseq(t)[i]:i in [1..#Eltseq(t)]]];
      end for;
    end if;
  end for;
end procedure;

///// For the addition/differential addition, we need to know the (inverse
//of the) dual coordinates of the theta null point. Howewer, we only need
//the <chi, 0, 0> dual coordinates for the differential addition, and the
//<chi, i, 0> for the normal addition (Generically). So we provide
//functions to compute theses.


// given the coordinates of point0, precompute what Riemann relations we
// have to use to compute \theta_i(x+y)\theta_j(x-y)
// These relations we use will depend on which coordinates in point0 is
// null
// for all couple (i,j) in L
// riemann is an associative array storing each dual riemann quadruplet
procedure precompute_riemann_relations(~point0,L)
  D:=point0`numbering;  g:=#Invariants(D);
  DD:=[2*i: i in D];
  twotorsion:=point0`twotorsion;
  r:=AssociativeArray();
  // r: the dual coordinates not computed.
  // Warning: at first we don't add the inverse to r, we only do it in the
  // end, in order to minimize the number of operations
  for ij in L do
    chi,i,j:=Explode(ij);
    if IsDefined(point0`riemann,<chi,i,j>) then continue ij; end if;
    i,j,tij:=reduce_twotorsion_couple(i,j);
    // we try to find k and l to apply the addition formulas such that
    // we can reuse the maximum the computations
    // for a differential addition, i eq j (generically) and we take k=l=0
    // for a normal addition, j=0 so we take k=i, l=j.
    if i eq j then
      k0:=D.0; l0:=D.0;
    else
      k0:=i; l0:=j;
    end if;
    found:=false; kk:=k0; ll:=l0;
    // we translate k and l till we find a non zero dual inverse coordinate
    for u,v in D do
      if (u+v) in DD then
        k,l:=reduce_symtwotorsion_couple(k0+u,l0+v);
        // we reduce k and l, because it only change the dual coordinate by
        // \pm 1
        el:=<chi,k,l>;
        if not IsDefined(point0`dual_coord, el) then
          if not IsDefined(r, el) then
            set_product_coord(~point0,[<k,l>],twotorsion);
            r[el]:=&+[point0`car[<chi,t>]*point0`prod_coord[<k+t,l+t>]:
              t in twotorsion];//*2^g;
/*
 * Dividing by #twotorsion is super important! It will affect each
 * differential addition by the same factor, so it does not affect
 * pairings, but it will affect the computation of a differential addition:
 * (P+Q)+P+Q and (P+Q)+(P+Q) won't give the same results since we don't do
 * the same number of differential addition. Hence the importance of having
 * a *true* differential addition
 * In fact I now do it on the differential addition, that was too confusing
 * to do it here only to gain a few mult by 1/2^g
 */
          end if;
          point0`dual_coord[el]:=r[el];
        end if;
        A:=point0`dual_coord[el];
        if A ne 0 then
          found:=true; kk:=k0+u; ll:=l0+v;
          break;
        end if;
      end if;
      if not found then
        point0`riemann[<chi,i,j>]:=[D| ];
      else
        kk0,ll0,tkl:=reduce_symtwotorsion_couple(kk,ll);
        i2,j2,k2,l2:=get_dual_quadruplet(i,j,kk,ll);
        i20,j20,tij2:=reduce_twotorsion_couple(-i2,j2);
        k20,l20,tkl2:=reduce_twotorsion_couple(k2,l2);
        for t in twotorsion do
          point0`riemann[<chi,i+t,j+t>]:=[i,j,t,kk0,ll0,tkl,i20,j20,tij2,k20,l20,tkl2];
        end for;
      end if;
    end for;
  end for;
  rr:=InvertGenListMontgomery(r);
  for el in Keys(r) do
      point0`invdual_coord[el]:=rr[el];
  end for;
end procedure;

/*
Let P0 :: ThetaNullPoint be a theta null point
Let P :: ThetaPoint or ThetaNullPoint
List :: [<chi,i,j>] with chi a character, i and j elements of the numbering group D

If P is used a lot for additions, precompute some of the associated values.

The idea is as follow: in addition_formula(P,Q,P0), we assume that Q lives
in the bigger field, so we check first if we have precomputed mixed
coordinates for Q, then for P.

isQ:=true  => precompute the values for P for usage in diff_add(-,P,-,P0).
   :=false => precompute for diff_add(P,-,-,P0)
onlyprod:=true => only compute the products
  Set these value to true if you want to do n>1 additions with P, but
  each time with a point that has already been precomputed
onlyprod:=false => to precompute the mixed_coordinates
 */
procedure precompute_addition(~P,P0, list: onlyprod:=false, isQ:=true)
  //precompute_riemann_relations(~P0,list);
  twotorsion:=P0`twotorsion;
  for ij in list do
    chi,i,j:=Explode(ij);
    if not IsDefined(P0`riemann, <chi,i,j>) then
      "ARGLLL we have to call precompute_riemann_relations (in precompute_addition) for", <chi,i,j>;
      precompute_riemann_relations(~P0, [<chi,i,j>]);
    end if;
    IJ:=P0`riemann[<chi,i,j>];
    if IsEmpty(IJ) then
      error "The precomputation for the riemann relations with", chi,i,j,
      "can't be done, the theta null point is 0.";
    end if;
    i0,j0,t0,k0,l0,tkl,i20,j20,tij2,k20,l20,tkl2:=Explode(IJ);
    if not isQ then i20:=k20;j20:=l20; end if;
    if onlyprod  then
      //we do the i2+t,j2+t in this function while we are at it
      set_product_coord(~P,[<i20,j20>],twotorsion);
    else
      //we always reduce the point before doing riemann relations, so this
      //is the precomputation we need, we correct with a character
      //afterwise
      if not IsDefined(P`mixed_coord,<chi,i20,j20,k0,l0>) then
        set_product_coord(~P,[<i20,j20>],twotorsion);
        P`mixed_coord[<chi,i20,j20,k0,l0>]:=
            &+[P0`car[<chi,t>]* P`prod_coord[<i20+t, j20+t>]:
                t in twotorsion ] * P0`invdual_coord[<chi,k0,l0>];
      end if;
    end if;
  end for;
end procedure;


// some precomputations associated to the numbering group D
procedure precompute_D(D,~precomp)
  red_twotors:=AssociativeArray(); red_symtwotors:=AssociativeArray();
  car:=AssociativeArray();
  D0:=get_twotorsion(D);
  for i,j in D0 do
    car[<i,j>]:=eval_car(i,j);
  end for;

  precompD:=AssociativeArray();
  precompD["car"]:=car;
  precompD["D"]:=D;
  precompD["twotorsion"]:=D0;
  precompD["g"]:=#Invariants(D);
  precomp["D"]:=precompD;
end procedure;




//** initializing theta points **//

function init_theta_null_point(point0: numbering:=AbelianGroup([0]), init:="isogenies", precomp:=AssociativeArray())
  if Category(point0) ne Assoc then
    point0:=SequenceToArray(Eltseq(point0),NumberingMap(numbering));
  end if;
  D:=Universe(Keys(point0)); Inv:=Invariants(D);
  if not IsDefined(precomp,"D") then
    precompute_D(D,~precomp);
  end if;
  car:=precomp["D","car"];
  D0:=precomp["D","twotorsion"];
  if D0 eq D then l2:=true; else l2:=false; end if;

  r:=rec< ThetaNullPoint|
  coord:=point0,
  inv_coord:=InvertGenListMontgomery(point0),
  prod_coord:=AssociativeArray(),
  dual_coord:=AssociativeArray(),
  invdual_coord:=AssociativeArray(),
  mixed_coord:=AssociativeArray(),
  numbering:=D,
  twotorsion:=D0,
  riemann:=AssociativeArray(),
  g:=#Inv,
  car:=car,
  l2:=l2
  >;
  if init eq "none" then
    precompute_riemann_relations(~r,[]);
  elif init eq "basic" then //for the conversion to rosenhain
    precompute_riemann_relations(~r,{<D.0,i,D.0>: i in D0});
  elif init eq "dadd" then
    //r`invdual_coord
    precompute_riemann_relations(~r,{<chi,i,i>: chi in
    D0, i in D});
  elif init eq "add" then
    precompute_riemann_relations(~r,{<chi,i,D.0>: chi in
    D0, i in D});
  elif init eq "all" then
    precompute_riemann_relations(~r,{<chi,i,j>: chi in
    D0, i,j in D});
  // isogenies="dadd"+ converting to rosenhain
  elif init eq "isogenies" then
    precompute_riemann_relations(~r,{<chi,i,i>: chi in
    D0, i in D} join {<D.0,i,D.0>: i in D});
  else
    error "Init method not recognized";
  end if;
  return r,precomp;
end function;

function init_theta_point(point: numbering:=AbelianGroup([0]))
  if Category(point) ne Assoc then
    point:=SequenceToArray(Eltseq(point),NumberingMap(numbering));
  end if;
  r:=rec< ThetaPoint|
  coord:=point,
  inv_coord:=AssociativeArray(),
  prod_coord:= AssociativeArray(),
  mixed_coord:=AssociativeArray(),
  numbering:=Universe(Keys(point))
  >;
  return r;
end function;



/*
Let P0 :: ThetaNullPoint be a theta null point
Let P :: ThetaPoint or ThetaNullPoint

Precompute some of the associated values of P.

init = dadd  :  use differential additions
     = add   :  use normal additions
     = all   :  to precompute everything (normally not usefull)
 */
procedure precompute_theta_point(~P,P0: init:="dadd", isQ:=true, onlyprod:=false)
  D:=P0`numbering;  D0:=P0`twotorsion;
  if init eq "none" then
    precompute_addition(~P,P0,[]: isQ:=isQ, onlyprod:=onlyprod);
  elif init eq "dadd" then
    precompute_addition(~P,P0,[<chi,i,i>: chi in D0, i in D]
			: isQ:=isQ, onlyprod:=onlyprod);
  elif init eq "add" then
    precompute_addition(~P,P0,[<chi,i,D.0>: chi in D0, i in D]
			: isQ:=isQ, onlyprod:=onlyprod);
  elif init eq "all" then
    precompute_addition(~P,P0,[<chi,i,j>: chi in D0, i,j in D]
			: isQ:=isQ, onlyprod:=onlyprod);
  else
    error "Init method not recognized";
  end if;
end procedure;




//** Additions **//

// For all chi,i,j in L, this compute \sum_{t in twotorsion} chi(t) (P+Q)_{i+t} (P-Q)_{j+t}
function addition_formula(P,Q,point0,L)
  //precompute_riemann_relations(~point0,L);
  D:=point0`numbering;
  twotorsion:=point0`twotorsion;
  Qpc:=Q`prod_coord; Ppc:=P`prod_coord;
  Qmc:=Q`mixed_coord;   Pmc:=P`mixed_coord;
  // Q should be the point living in the big field
  r:=AssociativeArray();
  for ij in L do
    chi,i,j:=Explode(ij);
    if IsDefined(r, <chi,i,j>) then continue ij; end if;
    // computing the result for i,j gives all the result for the i+t,j+t,
    // so we do these while we are at it
    if not IsDefined(point0`riemann, <chi,i,j>) then
      "ARGLLL we have to call precompute_riemann_relations for", <chi,i,j>;
      precompute_riemann_relations(~point0, [<chi,i,j>]);
    end if;
    IJ:=point0`riemann[<chi,i,j>];
    if IsEmpty(IJ) then
      error "Can't compute the addition! Either we are in level 2 and
        computing a normal addition, or a differential addition with null
        even theta null points.";
    end if;
    i0,j0,t0,k0,l0,tkl,i20,j20,tij2,k20,l20,tkl2:=Explode(IJ);
    tt:=tkl+tij2+tkl2;
    if IsDefined(Qmc,<chi,i20,j20,k0,l0>) then
      set_product_coord(~P,[<k20,l20>],twotorsion);
      S:=&+[point0`car[<chi,t>]* P`prod_coord[<k20+t, l20+t>]:
            t in twotorsion ]
              *Qmc[<chi,i20,j20,k0,l0>]*point0`car[<chi,tt>];
    elif IsDefined(Pmc,<chi,k20,l20,k0,l0>) then
      set_product_coord(~Q,[<i20,j20>],twotorsion);
      S:=&+[point0`car[<chi,t>]* Q`prod_coord[<i20+t, j20+t>]:
            t in twotorsion ]
              *Pmc[<chi,k20,l20,k0,l0>]*point0`car[<chi,tt>];
    else
      set_product_coord(~P,[<k20,l20>],twotorsion);
      set_product_coord(~Q,[<i20,j20>],twotorsion);
      s1:=&+[point0`car[<chi,t>]* Q`prod_coord[<i20+t, j20+t>]:
            t in twotorsion ];
      s2:=&+[point0`car[<chi,t>]* P`prod_coord[<k20+t, l20+t>]:
            t in twotorsion ];
      A:=point0`invdual_coord[<chi,k0,l0>];
      // we prefer to store the data in Q because for a differential
      // addition we will have i2=j2=0, so  in level 4, we gain.
      s1A:=s1*A;
      Qmc[<chi,i20,j20,k0,l0>]:=s1A;
      S:=s2*s1A*point0`car[<chi,tt>];
    end if;
    for t in twotorsion do
      r[<chi,i0+t,j0+t>]:=point0`car[<chi,t>]*S;
    end for;
  end for;
  return r;
end function;

// Given P, Q, P-Q or Q, P, P-Q, compute P+Q in affine coordinates The
// order is important: for optimizations, Q should be the point living in
// the largest field. In fact, generically, we try to only use the two
// torsion part of Q.
function diff_add(P,Q,PmQ,point0)
  PQ:=AssociativeArray();
  D:=point0`numbering;
  twotorsion:=point0`twotorsion;
  if IsEmpty(Keys(PmQ`inv_coord)) then
    PmQ`inv_coord:=InvertGenListMontgomery(PmQ`coord);
  end if; i0:=get_nonzero_coord(PmQ`coord);
  list:={};
  for i in D do
    if PmQ`coord[Eltseq(i)] eq 0 then
      j:=i0;
    else j:=i; end if;
    if PmQ`coord[Eltseq(i)] eq 0 and point0`l2  then
      list:=list join {<chi,i,j>:chi in twotorsion| eval_car(chi,i+j) eq 1};
    else
      list:=list join {<chi,i,j>:chi in twotorsion};
    end if;
  end for;
  r:=addition_formula(P,Q,point0,list);
  for i in D do
    if PmQ`coord[Eltseq(i)] eq 0 then j:=i0; else j:=i; end if;
    if PmQ`coord[Eltseq(i)] eq 0 and point0`l2 then
      cartosum:= {chi:chi in twotorsion | eval_car(chi,i+j) eq 1};
    else
      cartosum:=twotorsion;
    end if;
      PQ[i]:=&+[r[<chi,i,j>]: chi in cartosum]*
        PmQ`inv_coord[Eltseq(j)]/#cartosum;
  end for;
  if point0`l2 then
    for i in D do
    // in level 2, in this case we only computed
    // PQ[i]PmQ[j]+PQ[j]PmQ[i] so we correct to get PQ[i]
    // we have to do it here to be sure we have computed PQ[j]
      if PmQ`coord[Eltseq(i)] eq 0 then
          PQ[i]+:= - PQ[j]*PmQ`coord[Eltseq(i)]/PmQ`coord[Eltseq(j)];
      end if;
    end for;
  end if;
  return init_theta_point(PQ);
end function;

//// we have PQ from a normal addition, we would like to recover the
//differential addition. Here we only have to compute a single coefficient
//to find the correct projective factor
function diff_add_PQfactor(PQ,P,Q,PmQ,point0)
  D:=point0`numbering;
  Dpq:=PQ`numbering;
  Dpmq:=PmQ`numbering;
  k:=Invariants(Dpq)[1]/2;
  twotorsion:=point0`twotorsion;
  for i in D do
    lambda2:=&+[PQ`coord[Dpq!Eltseq(i)+Dpq![k*Eltseq(t)[i]:i in [1..#Eltseq(t)]]]*PmQ`coord[Dpmq!Eltseq(i)+Dpmq![k*Eltseq(t)[i]:i in [1..#Eltseq(t)]]]: t in twotorsion];
    if lambda2 eq 0 then continue i; end if;
    list:={<twotorsion.0,i,i>};
    r:=addition_formula(P,Q,point0,list);
    lambda1:=r[<twotorsion.0,i,i>]; //lambda= \sum PQ[i+t]PmQ[i+t]/2^g
    return lambda1/lambda2;
  end for;
  // sometime it does not suffice when PmQ has a 0 coordinate, meaning we should
  // try to do the addition formula for i,j in D
  // and handle the level 2 case
  // TODO!
  // in practise this never happen, so I just call diff_add in this case
  PQ2:=diff_add(P,Q,PmQ,point0);
  i0:=get_nonzero_coord(PQ2`coord);
  return PQ2`coord[i0]/PQ`coord[i0];
end function;
function diff_add_PQ(PQ,P,Q,PmQ,point0)
    D:=point0`numbering; PQn:=AssociativeArray();
    lambda:=diff_add_PQfactor(PQ,P,Q,PmQ,point0);
    for i in D do
      PQn[i]:=lambda*PQ`coord[Eltseq(i)];
    end for;
    return init_theta_point(PQn);
end function;

// Normal addition between P and Q
// We suppose that (P-Q)[affine_patch] ne 0
function add(P,Q,point0: affine_patch:=point0`numbering.0)
  D:=point0`numbering; i0:=affine_patch;
  PQ:=AssociativeArray();
  twotorsion:=point0`twotorsion;
  if point0`l2 then
    PmQ:=AssociativeArray();
    for i0 in D do
      for i1 in D do
        if i1 eq i0 then continue; end if;
        list:=[<chi,i,i0>:chi in twotorsion, i in D | eval_car(chi,i+i0) eq 1]
          cat [<chi,i,i1>:chi in twotorsion, i in D | eval_car(chi,i+i1) eq 1];
        r:=addition_formula(P,Q,point0,list);
        kappa0:=AssociativeArray();
        kappa1:=AssociativeArray();
        for i in D do
          cartosum:=[chi: chi in twotorsion | eval_car(chi,i+i0) eq 1];
          kappa0[i]:= &+[r[<chi,i,i0>]: chi in cartosum]/#cartosum;
          if i eq i0 and kappa0[i0] eq 0 then continue i0; end if;
          cartosum:=[chi: chi in twotorsion | eval_car(chi,i+i1) eq 1];
          kappa1[i]:= &+[r[<chi,i,i1>]: chi in cartosum]/#cartosum;
        end for;
        //kappa0[i0]:=kappa0[i0]/2; kappa1[i1]:=kappa1[i1]/2;
        F:=Parent(kappa0[i0]); A<X>:=PolynomialRing(F);
        invkappa0:=1/kappa0[i0]; PmQ[i0]:=F!1; PQ[i0]:=kappa0[i0];
        P:=X^2-2*kappa0[i1]*invkappa0*X+kappa1[i1]*invkappa0;
        roots:=[i[1]: i in Roots(P)];
        // it can happen that P and Q are not rationnal in the av but
        // rationnal in the kummer variety, so P+Q won't be rationnal
        if #roots eq 0 then
          roots:=[i[1]: i in RootsInSplittingField(P)];
        end if;
        if #roots eq 1 then roots:=[roots[1], roots[1]]; end if;
        PmQ[i1]:=roots[1]*PmQ[i0]; PQ[i1]:=roots[2]*PQ[i0];
        M:=Matrix([[PmQ[i0], PmQ[i1]],
                  [PQ[i0], PQ[i1]]]);
        if not IsInvertible(M) then continue i1; end if;
        for i in D do
          if i eq i0 or i eq i1 then continue i; end if;
          V:=Vector([kappa0[i], kappa1[i]]);
          W:=Solution(M,V);
          PmQ[i]:=W[2]; PQ[i]:=W[1];
        end for;
        return init_theta_point(PQ), init_theta_point(PmQ);
      end for;
    end for;
  else
    list:=[<chi,i,i0>:chi in twotorsion, i in D];
    r:=addition_formula(P,Q,point0,list);
    for i in D do
      PQ[i]:=&+[r[<chi,i,i0>]: chi in twotorsion];
    end for;
    if &and[PQ[i] eq 0: i in Keys(PQ)]  then
      f:=NumberingMap(D);
      return add(P,Q,point0: affine_patch:=(i0@f+1)@@f);
    end if;
    return init_theta_point(PQ);
  end if;
end function;

// the opposite of P
// set keep=false if you don't want to copy the precomputed values of P
function opp(P,point0: keep:=true)
  D:=point0`numbering;
  twotorsion:=point0`twotorsion;
  mPcoord:=AssociativeArray();
  for i in D do
    mPcoord[-i]:=P`coord[i];
  end for;
  mP:=init_theta_point(mPcoord);
  if keep then
  for i in Keys(P`inv_coord) do
      mP`inv_coord[-i]:=P`inv_coord[i];
  end for;
  for i in Keys(P`prod_coord) do
      mP`prod_coord[<-i[1],-i[2]>]:=P`prod_coord[i];
  end for;
  for i in Keys(P`mixed_coord) do
      mP`mixed_coord[<i[1],-i[2],-i[3],i[4],i[5]>]:=P`mixed_coord[i];
  end for;
  end if;
  return mP;
end function;




//** Multiplication **//

function diff_mult(k,P,point0)
  if k eq 0 then return point0;
  elif k lt 0 then return diff_mult(-k, opp(P,point0), point0);
  elif k eq 1 then return P;
  //elif k eq 2 then return diff_add(P,P,point0,point0);
  else
    precompute_theta_point(~P,point0: init:="dadd");
    P:=Explode(get_precompute_inverses([P]));
    mP:=opp(P,point0);
    nP := P; n1P:=diff_add(P,P,point0,point0);
    kb := Reverse(IntegerToSequence(k-1,2));
    for i := 2 to #kb do
      if kb[i] eq 1 then
       precompute_theta_point(~n1P,point0: init:="dadd");
       nn11P:=diff_add(n1P,n1P,point0,point0);
       nP:=diff_add(nP,n1P,mP,point0);
       n1P:=nn11P;
      else
       precompute_theta_point(~nP,point0: init:="dadd");
       nn1P:=diff_add(n1P,nP,P,point0);
       nP:=diff_add(nP,nP,point0,point0);
       n1P:=nn1P;
      end if;
    end for;
  end if;
  return n1P;
end function;

// return kP+Q, kP
// (if we don't need kP, then we don't need to compute kP, only (k/2)P, so
// we lose 2 differential additions. Could be optimized here.
function diff_multadd(k,P,PQ,Q,point0)
  if k eq 0 then return Q;
  elif k lt 0 then
    mP:=opp(P,point0);
    return diff_multadd(-k, mP, diff_add(Q,mP,PQ,point0),Q,point0);
  elif k eq 1 then return PQ,P;
  //elif k eq 2 then return diff_add(PQ,P,Q,point0),diff_add(P,P,point0,point0);
  else
    precompute_theta_point(~P,point0: init:="dadd");
    P,Q,PQ:=Explode(get_precompute_inverses([P,Q,PQ]));
    nPQ := PQ; n1PQ:=diff_add(PQ,P,Q,point0);
    nP := P; n1P:=diff_add(P,P,point0,point0);
    kb := Reverse(IntegerToSequence(k-1,2));
    for i := 2 to #kb do
      if kb[i] eq 1 then
       precompute_theta_point(~n1P,point0: init:="dadd");
       precompute_theta_point(~nP,point0: init:="dadd");
       nn11PQ:=diff_add(n1PQ,n1P,Q,point0);
       nPQ:=diff_add(n1PQ,nP,PQ,point0);
       n1PQ:=nn11PQ;

       nn11P:=diff_add(n1P,n1P,point0,point0);
       nP:=diff_add(n1P,nP,P,point0);
       n1P:=nn11P;
      else
       precompute_theta_point(~nP,point0: init:="dadd");
       nn1PQ:=diff_add(n1PQ,nP,PQ,point0);
       nPQ:=diff_add(nPQ,nP,Q,point0);
       n1PQ:=nn1PQ;

       nn1P:=diff_add(n1P,nP,P,point0);
       nP:=diff_add(nP,nP,point0,point0);
       n1P:=nn1P;
      end if;
    end for;
  end if;
  return n1PQ, n1P;
end function;

function mult(k,P,point0)
  if k eq 0 then return point0;
  elif k lt 0 then return mult(-k, opp(P,point0), point0);
  elif k eq 1 then return P;
  else
    kb := Reverse(IntegerToSequence(k,2));
    nP:=P;
    for i := 2 to #kb do
      // for doubling, chaine_add is faster than add
      nP:=diff_add(nP,nP,point0,point0);
      if kb[i] eq 1 then
        nP:=add(nP,P,point0);
      end if;
    end for;
    return nP;
  end if;
end function;




//** Pairing **//

function pairing_from_points(P,Q,lP,lQ,lPQ,PlQ,point0)
  r,k0P:=compare_points(lP,point0);
  assert r;
  r,k0Q:=compare_points(lQ,point0);
  assert r;
  r,k1P:=compare_points(PlQ,P);
  assert r;
  r,k1Q:=compare_points(lPQ,Q);
  assert r;
  return k1P*k0P/(k1Q*k0Q);
end function;

function pairing_PQ(l,P,Q,PQ,point0)
  lPQ,lP:=diff_multadd(l,P,PQ,Q,point0);
  PlQ,lQ:=diff_multadd(l,Q,PQ,P,point0);
  r,k0P:=compare_points(lP,point0);
  if not r then "Bad pairing!"; print print_point(P):Magma; end if;
  r,k0Q:=compare_points(lQ,point0);
  if not r then "Bad pairing!"; print print_point(Q):Magma; end if;
  r,k1P:=compare_points(PlQ,P);
  r,k1Q:=compare_points(lPQ,Q);
  return k1P*k0P/(k1Q*k0Q);
end function;

function pairing(l,P,Q,point0)
  PQ:=add(P,Q,point0);
  return pairing_PQ(l,P,Q,PQ,point0);
end function;



//** more powerfull additions **//

// General riemann relations
// Returnthe point X such that we have a Riemann relation on
// X,a, b,c // d,e f,g
function riemann(a,b,c,d,e,f,g,point0)
  D:=point0`numbering; twotorsion:=point0`twotorsion;
  DD:=[2*i: i in D];
  gg:=#Invariants(D);
  r:=AssociativeArray();
  for i in D do
    if IsDefined(r,i) then continue i; end if;
    if a`coord[i] ne 0 then j0:=i;  else j0:=D.0; end if;
    for j1 in D do
      j:=j0+j1; if a`coord[j] eq 0 then continue j1; end if;
      rj:=AssociativeArray();
      for chi in twotorsion do
        if i eq j then
          k0:=D.0; l0:=D.0;
        else
          k0:=i; l0:=j;
        end if;
        found:=false; k:=k0; l:=l0;
        // we translate k and l till we find a non zero dual inverse coordinate
        for u,v in D do
          if (u+v) in DD then
            kk,ll:=Explode(<k0+u,l0+v>);
            A:=&+[point0`car[<chi,t>]*b`coord[kk+t]*c`coord[ll+t]:
                  t in twotorsion];
          end if;
          if A ne 0 then
            found:=true;
            i2,j2,k2,l2:=get_dual_quadruplet(i,j,kk,ll);
            s1:=&+[point0`car[<chi,t>]* d`coord[i2+t]*e`coord[j2+t]:
              t in twotorsion ];
            s2:=&+[point0`car[<chi,t>]* f`coord[k2+t]*g`coord[l2+t]:
              t in twotorsion ];
            rj[chi]:=s1*s2/A;
            break;
          end if;
        end for;
        if not found then
          continue j1;
        end if;
      end for;
      for  t in twotorsion do
        r[i+t]:=&+[point0`car[<chi,t>]*rj[chi]: chi in twotorsion]
        /(2^gg*a`coord[j+t]);
      end for;
      break j1;
    end for;
  end for;
  return init_theta_point(r);
end function;

// return a+b+c (with the exact factor) from a,b,c,a+b,a+c,b+c
function three_add(a,b,c,bc,ac,ab,point0)
  return riemann(a,b,c,point0,bc,ac,ab,point0);
end function;

// compute aP_1 + bP_2 +cP_3 in level 2 when we have the sums for a,b,c \in
// {0,1}
function point_from_basis_l2(el,ltors)
  G:=Universe(Keys(ltors)); ell:=Eltseq(el);
  if IsDefined(ltors,G!ell) then return ltors[G!ell],ltors; end if;
  i0:=Max([i: i in [1..#ell] | ell[i] notin {0,1}]);
  ell1:=ell; ell1[i0]:=1;
  ell0:=ell; ell0[i0]:=0;
  P0:=ltors[G.0]; P:=ltors[G.i0];
  Q,ltors:=point_from_basis_l2(G!ell0,ltors);
  PQ,ltors:=point_from_basis_l2(G!ell1,ltors);
  r:=diff_multadd(ell[i0],P,PQ,Q,P0);
  return r,ltors;
end function;
