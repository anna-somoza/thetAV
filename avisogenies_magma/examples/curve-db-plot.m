// ORDER OF MAGNITUDE:
// On a Core2 at 2.13GHz, the following takes about one hour.

load "curve-db.m";
load "ex-draw.m";

SetColumns(0);
SetVerbose("AVIsogenies",1);

for g in cdb_jacs do
	l:=g[1];
	J:=g[2];
	file:="curve-db-plot/IsoGraph."*IntegerToString(l)*"."*IntegerToString(Hash(J));
	try null:=Read(file*".crv.mag"); exist:=true; catch e exist:=false; end try;
	if exist then print file*" already exists; moving on..."; continue; end if;

	WriteOrdIsoCrv(J,l,file);
end for;

System("cd curve-db-plot; ls *.ord*.dot | xargs -I{} dot -Tsvg -o {}.svg {}");
System("cd curve-db-plot; ls *.iso*.dot | xargs -I{} neato -Tsvg -o {}.svg {}");
