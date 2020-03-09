/* Usefull tools for the rest of the AVIsogenies package
* - Damien Robert
*/

//**** AssociativeArray manipulation ****//

function SequenceToArray(A,f)
  r:=AssociativeArray();
  for i in Domain(f) do
    if IsDefined(A,i@f) then
      r[i]:=A[i@f];
    end if;
  end for;
  return r;
end function;


procedure CopyArray(orig,~dest: keys:=Keys(orig))
  for i in keys do
    dest[i]:=orig[i];
  end for;
end procedure;



/*
Let A be an associative array. Let phi be a map that can be applied to each
element of A
Create an associative array B whose Keys are the same as A but whose elements
are the image of the elements of A by phi.
 */
function ConvertArray(A,phi)
  B:=AssociativeArray();
  for i in Keys(A) do B[i]:=A[i]@phi; end for;
  return B;
end function;




//**** String manipulations and print functions ****//

function TxtHash(x)
  return IntegerToString(Hash(Sprintf("%o",x)));
end function;


intrinsic JoinString(list::SeqEnum[MonStgElt], sep::MonStgElt) -> MonStgElt
  {The concatenation of the strings of list with seperator sep.}
  if IsEmpty(list) then return ""; end if;
  s:=list[1]; list:=list[2..#list];
  for i in list do
    s *:=sep*i;
  end for;
  return s;
end intrinsic;
