/* Lattice of orders and drawing isogenies graphs
* - Gaëtan Bisson
* - Damien Robert
*/

import "libseq.m" : TxtHash;


//**** Lattice of orders ****//

// Returns the minimal and maximal orders, namely Z[pi,\bar{pi}] and the
// integer ring of Q(pi).
function MinMaxOrder(pi)
  if Category(pi) eq FldNumElt then K:=Parent(pi);
  else K<pi>:=NumberField(pi); end if;
  OK:=MaximalOrder(K);
  _,p:=IsPower(Norm(pi),Degree(K) div 2);
  pibar:=p/pi;
  R:=sub<OK|[pi,pibar]>;
  return R,OK,K;
end function;

// Returns the set of orders just above O locally at L.
function OrdersJustAbove(O,L,OK,R)
  FG:=FreeAbelianGroup(Degree(NumberField(O)));
  OR,mO:=quo<FG|[FG!Eltseq(OK!x) : x in Basis(O)]>;
  Ord:={};
  S:=&cat[Subgroups(OR : Sub:=[l]) : l in L];
  for s in S do
    Include(~Ord,sub<OK|Basis(O) cat [OK!Eltseq((OR!g)@@mO) : g in Generators(s`subgroup)]>);
  end for;
  for j,h in Ord do if j ne h and j subset h then Exclude(~Ord,h); end if; end for;
  return Ord;
end function;

// Returns the set of orders just below O locally at L.
function OrdersJustBelow(O,L,OK,R)
  FG:=FreeAbelianGroup(Degree(NumberField(O)));
  OR,mO:=quo<FG|[FG!Eltseq(O!x) : x in Basis(R)]>;
  Ord:={};
  S:=&cat[&cat[Subgroups(OR : Quot:=t) : t in [[l],[l,l],[l,l,l]]] : l in L];
  for s in S do
    Include(~Ord,sub<OK|Basis(R) cat [O!Eltseq((OR!g)@@mO) : g in Generators(s`subgroup)]>);
  end for;
  Exclude(~Ord,O);
  for j,h in Ord do if j ne h and j subset h then Exclude(~Ord,j); end if; end for;
  return Ord;
end function;

// Computes the lattice of orders starting from the minimal one.
function LatticeOfOrdersUp(pi)
  R,OK,K:=MinMaxOrder(pi);
  L:=[l[1]: l in Factorization(Index(OK,R))];
  X:={}; Y:={R}; Z:=AssociativeArray();
  while Y ne {} do
    O:=Rep(Y);
    vprintf AVIsogenies, 4: "    current order index %o (%o orders seen and %o to come)\n",Index(OK,O),#X,#Y;
    Z[O]:=OrdersJustAbove(O,L,OK,R);
    for i in Z[O] do if not i in X then Include(~Y,i); end if; end for;
    Exclude(~Y,O); Include(~X,O);
  end while;
  return Z;
end function;

// Computes the lattice of orders starting from the maximal one.
function LatticeOfOrdersDown(pi)
  R,OK,K:=MinMaxOrder(pi);
  L:=[l[1]: l in Factorization(Index(OK,R))];
  X:={}; Y:={OK}; Z:=AssociativeArray(); Z[OK]:={};
  while Y ne {} do
    O:=Rep(Y);
    vprintf AVIsogenies, 4: "    current order index %o (%o orders seen and %o to come)\n",Index(O,R),#X,#Y;
    for o in OrdersJustBelow(O,L,OK,R) do
      if not IsDefined(Z,o) then Z[o]:={}; end if;
      Include(~Z[o],O);
      if not o in X then Include(~Y,o); end if;
    end for;
    Exclude(~Y,O);Include(~X,O);
  end while;
  return Z;
end function;

intrinsic LatticeOfOrders(pi::RngUPolElt : Orientation := "Down") -> SeqEnum
    {Remark: The lattice of orders is exponential in the
    number of divisors of the index [O_K:Z[\pi,\bar\pi]],
    so it would make sense to input a set of such divisors
    to bound the size of the lattice. --DRK}
    case Orientation:
    when "Up":
        return LatticeOfOrdersUp(pi);
    when "Down":
        return LatticeOfOrdersDown(pi);
    else
      require false: "Parameter \"Orientation\" must be in {\"Up\",\"Down\"}.";
    end case;
end intrinsic;

// Check if O is stable under complex conjugation
function StableUnderComplexConjugation(O)
  B:=Basis(O);
  for b in B do
    if not ComplexConjugate(b) in O then return false; end if;
  end for;
  return true;
end function;


function LabelOrders(orders)
  label:=AssociativeArray();
  if Category(orders) eq SetEnum then
    orders:=Setseq(orders);
  end if;
  // Finding the minimal order, yeah we could do it faster
  // be following the lattice backward...
  disc:=[Discriminant(o): o in orders];
  bool,pos:=Maximum(disc);
  R:=orders[pos];
  set:=Sort(Setseq(SequenceToSet(disc)));
  for d in set do
    ind:=[i: i in [1..#disc] | disc[i] eq d];
    ord:=[orders[i]: i in ind];
    o:=Rep(ord); index:=Index(o,R);
    if #ord eq 1 then
      label[o]:=IntegerToString(index);
    else
      for i in [1..#ord] do
        label[ord[i]]:=IntegerToString(index) *"-"*IntegerToString(i);
      end for;
    end if;
  end for;
  return label;
end function;


intrinsic DrawLattice(Z::Assoc,file::MonStgElt : info:=func<o|"">)
  {Writes a graphviz file describing the lattice of orders;
  compile with "dot -Tsvg -o file.dot.svg file.dot".}
  old:=GetColumns(); SetColumns(0);
  Write(file,"digraph bla {");
  for O in Keys(Z) do
    txt:=JoinString(Split(info(O),"\n")," ");
    Write(file,TxtHash(O)*" [label=\""*txt*"\",style=filled,height=.2,width=.2];");
    for O1 in Z[O] do
       Write(file,TxtHash(O1)*" -> "*TxtHash(O)*"[label="*IntegerToString(Index(O1,O))*"];");
    end for;
  end for;
  Write(file,"}");
  SetColumns(old);
end intrinsic;

//**** Draw isogeny graphs ****//

function CleanInfo(s)
  return JoinString(Split(s,"\n")," ");
end function;

intrinsic DrawGraph(graph::Assoc, file::MonStgElt : edges:=false, vertices:=AssociativeArray())
  {Writes a graphviz file describing the graph to file; compile with
  "neato -Tsvg -o file.dot.svg file.dot"; optionally labels the vertices
  and edges (with the second element of graph[*]).}
  old:=GetColumns(); SetColumns(0);
  Write(file,"graph bla {");
  Write(file,"splines=true;");
  for i in Keys(graph) do
    if IsDefined(vertices,i) then
      infoJac:=vertices[i];
    else
      infoJac:="";
    end if;
    infoJac:=CleanInfo(infoJac);
    Write(file,IntegerToString(Hash(i))*" [label=\""*infoJac*"\",style=filled,height=.2,width=.2];");
    for j in graph[i] do
      if Hash(<i,j[2]>) le Hash(j) then
        if edges then
          info:=Sprintf("%o",j[2]);
        else
          info:="";
        end if;
        info:=CleanInfo(info);
        Write(file,IntegerToString(Hash(i))*" -- "*IntegerToString(Hash(j[1]))*" [label=\""*info*"\"];");
      end if;
    end for;
  end for;
  Write(file,"}");
  SetColumns(old);
end intrinsic;
