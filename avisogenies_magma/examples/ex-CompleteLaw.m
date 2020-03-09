



/*
Create a random hyperelliptic curve of genus 2 over k with rationnal theta constants of level (2,2).

Returns the Rosenhain invariants of the curve and the theta constants of level (2,2) with the ordering of Gaudry.

May not terminate.
 */
function RandomCurve_thetaRationnal(k)
  repeat 

    repeat 
      la:=k!Random(k); 
    until IsSquare(la) and IsSquare(la-1) and not IsZero(la*(la-1));
    repeat 
      nu:=k!Random(k);
    until IsSquare(nu) and IsSquare(nu-1) and not IsZero(nu*(nu-1)*(nu-la));
 
    repeat 
      repeat 
        mu:=k!Random(k);
        Ros:=[0,1,la,mu,nu];
      until #Seqset(Ros) eq 5;

      test5:=IsPower(mu/la/nu,4);
      test3:=IsPower((la-1)*(nu-1)/(mu-1),4);
      test7:=IsPower((la-mu)*la/(la-nu)/(la-1),4);
      test4:=IsPower((nu-mu)*nu/(nu-1)/(nu-la),4);
    until test3 and test4 and test5 and test7;

    SqTheta:=[k!0 : i in [1..16]];
    SqTheta[1]:=k!1;


    SqTheta[3]:=Sqrt((Ros[1]-Ros[4])*(Ros[3]-Ros[2])*(Ros[5]-Ros[2])
                    /(Ros[2]-Ros[4])/(Ros[3]-Ros[1])/(Ros[5]-Ros[1]));
    SqTheta[4]:=Sqrt((Ros[1]-Ros[4])*(Ros[3]-Ros[2])*(Ros[5]-Ros[4])
                    /(Ros[1]-Ros[3])/(Ros[4]-Ros[2])/(Ros[5]-Ros[3]));
    SqTheta[5]:=Sqrt((Ros[1]-Ros[2])*(Ros[1]-Ros[4])
                    /(Ros[1]-Ros[3])/(Ros[1]-Ros[5]));
    SqTheta[7]:=Sqrt((Ros[1]-Ros[4])*(Ros[3]-Ros[4])*(Ros[5]-Ros[2])
                    /(Ros[1]-Ros[5])/(Ros[3]-Ros[5])/(Ros[4]-Ros[2]));

    if not IsSquare(SqTheta[3]) then SqTheta[3]*:=-1; end if;
    if not IsSquare(SqTheta[4]) then SqTheta[4]*:=-1; end if;
    if not IsSquare(SqTheta[5]) then SqTheta[5]*:=-1; end if;
    if not IsSquare(SqTheta[7]) then SqTheta[7]*:=-1; end if;


    SqTheta[6]:=SqTheta[1]*SqTheta[4]/SqTheta[5]/nu;
    SqTheta[8]:=SqTheta[1]*SqTheta[7]/SqTheta[5]/la;
    SqTheta[2]:=SqTheta[5]*SqTheta[6]/SqTheta[3]*(nu-1);
    SqTheta[9]:=SqTheta[5]*SqTheta[8]/SqTheta[3]*(la-1);
  
    SqTheta[10]:=(SqTheta[1]*SqTheta[2]-SqTheta[3]*SqTheta[4])/SqTheta[8];

  until IsSquare(SqTheta[10]);

// Ros;SqTheta;
  return Ros,[Sqrt(t) : t in SqTheta];
end function;



/******************************************************************************/


// first select the field
  q:=2011; 
  k:=GF(q);

// Either select a curve or do the following
  Ros,theta:=RandomCurve_thetaRationnal(k);
  kk<x>:=PolynomialRing(k);
  f:=&*[x-a : a in Ros];
  C:=HyperellipticCurve(f);
  JacC:=Jacobian(C);
print "Working with the",C;
print "Its theta constants are",theta;


// We first need the theta constant to have the structure of 
// AnalyticThetaNullPoint.
  Ab:=AbelianGroup([2,2,2,2]);
  th := AnalyticThetaNullPoint(4,AssociativeArray(Ab),Ab,2 : level2 := false);

  th`coord[Ab![0,0,0,0]]:=theta[1];
  th`coord[Ab![0,0,1,1]]:=theta[2];
  th`coord[Ab![0,0,1,0]]:=theta[3];
  th`coord[Ab![0,0,0,1]]:=theta[4];
  			     
  th`coord[Ab![1,0,0,0]]:=theta[5];
  th`coord[Ab![1,0,0,1]]:=theta[6];
  th`coord[Ab![0,1,0,0]]:=theta[7];
  th`coord[Ab![1,1,0,0]]:=theta[8];
  th`coord[Ab![0,1,1,0]]:=theta[9];
  th`coord[Ab![1,1,1,1]]:=theta[10];
  			
  th`coord[Ab![0,1,0,1]]:=theta[11];
  th`coord[Ab![0,1,1,1]]:=theta[12];
  th`coord[Ab![1,0,1,0]]:=theta[13];
  th`coord[Ab![1,1,1,0]]:=theta[14];
  th`coord[Ab![1,0,1,1]]:=theta[15];
  th`coord[Ab![1,1,0,1]]:=theta[16];


// Ok now we can find the coefficients. First find a suitable alpha.
  alpha:=FindAlpha(JacC,k);
  gamma:=CoefficientLawP(JacC,Ros,th,alpha);
print "The coefficients (with respect to Baily's) of a complete group law are",gamma;



// You can check that it works by doing the following:
 D1:=Random(Jacobian(C)); D2:=Random(Jacobian(C)); 
 additionP_fromMumford(D1, D2, theta, Ros, th, gamma);
// the result must be 1) well defined in P^15(k) 
//                    2) the theta (in Gaudry numbering) of D1+D2
