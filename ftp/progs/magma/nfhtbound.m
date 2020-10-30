// Height bounds over number fields: nfhtbound.m
//
//////////////////////////////////////////////////////////////////////////
//
// Copyright 2005-2007 John Cremona
// 
// This file contains functions to be used with the package Magma (see
// http://magma.maths.usyd.edu.au/magma/) V2.13
// 
// this is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by the
// Free Software Foundation; either version 2 of the License, or (at your
// option) any later version.
// 
// this file is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
// 
// You should have received a copy of the GNU General Public License
// along with this file; if not, write to the Free Software Foundation,
// Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
// 
//////////////////////////////////////////////////////////////////////////
//
// This file is in three parts:
//
// 1. Local heights for elements of a number field K
//
// Implementation of standard local and global height for elements of
// number fields
// 
// 2. Silverman's bounds
//
// Implementation of Silverman's bounds (upper and lower) on the
// difference between naive and canonical height of points on an elliptic
// curve defined over a number field, as in his paper "The difference between
// the Weil height and the canonical height on elliptic curves",
// Math. Comp. 55 (1990), 723-743.
//
//  3. Cremona-Prickett-Siksek (CPS) bounds
//
// Implementation of the CPS (Cremona-Prickett-Siksek) bounds for the
// same thing, as in their paper "Height Difference Bounds For Elliptic
// Curves over Number Fields", Journal of Number Theory 116(1)
// (2006), 42-68. 
//
///////////////////////////////////////////////////////////////////////////////
//
// 1. Local heights for elements of a number field K
//
// These are logarithmic heights; 
//   the height of x in K is really the height of [x:1] in P^1(K) 
//
////////////////////////////////////////////////////////////////////////////////////

intrinsic LocalHeight(x::FldNumElt, P::RngOrdIdl) -> FldPrElt
{Local logarithmic height of x at a prime P of a number field}
if x eq 0 then return 0; end if;
return -Degree(P)*Min(0,Valuation(x,P))*Log(Norm(P));
end intrinsic;

function MyDenominatorIdeal(x);
R:=Integers(Parent(x));
n:=Numerator(x)*R;
d:=Denominator(x)*R;
return d/(d+n);
end function;

function MyDenominatorIdeal(x);
return d/(d+n) where n is Numerator(x)*R 
               where d is Denominator(x)*R 
               where R is Integers(Parent(x));
end function;

intrinsic TotalNonArchLocalHeight(x::FldNumElt) -> FldPrElt
{Sum of local logarithmic heights of x at all non-archimedean places of a number field}
if x eq 0 then return 0; end if;
K:=Parent(x);
R:=Integers(K);
S:=Support(Numerator(x)*R) join Support(Denominator(x)*R);
if #S eq 0 then return 0; else
return &+([LocalHeight(x,P) : P in S]);
end if;
end intrinsic;

intrinsic ArchLocalHeight(x::FldNumElt, i::RngIntElt) -> FldPrElt
{Local logarithmic height of x at i'th embedding of a number field}
return Log(Max(1,Abs(Conjugate(x,i))));
end intrinsic;

intrinsic TotalArchLocalHeight(x::FldNumElt) -> FldPrElt
{Sum of local logarithmic heights of x at all archimedean places of a number field}
if x eq 0 then return 0; end if;
r,s:=Signature(Parent(x));
return &+([ArchLocalHeight(x,i) : i in [1..r]] cat
          [2*ArchLocalHeight(x,r+2*i-1) : i in [1..s]]);
end intrinsic;

intrinsic AbsLogHeight(x::FldNumElt) -> FldPrElt
{Absolute global logarithmic height of x}
return (TotalArchLocalHeight(x) + TotalNonArchLocalHeight(x))/Degree(Parent(x));
end intrinsic;

intrinsic AbsLogArchHeight(x::FldNumElt) -> FldPrElt
{Archimedean component of absolute global logarithmic height of x}
return (TotalArchLocalHeight(x))/Degree(Parent(x));
end intrinsic;

// Special versions for rational x:

intrinsic TotalNonArchLocalHeight(x::FldRatElt) -> FldPrElt
{Sum of local logarithmic heights of rational x at all non-archimedean places of Q}
return Log(Denominator(x));
end intrinsic;

intrinsic TotalArchLocalHeight(x::FldRatElt) -> FldPrElt
{Sum of local logarithmic heights of rational x at all archimedean places of Q}
return Log(Max(1,Abs(x)));
end intrinsic;

intrinsic AbsLogArchHeight(x::FldRatElt) -> FldPrElt
{Archimedean component of absolute global logarithmic height of rational x}
return Log(Max(1,Abs(x)));
end intrinsic;

intrinsic AbsLogHeight(x::FldRatElt) -> FldPrElt
{Absolute global logarithmic height of rational x}
return TotalArchLocalHeight(x) + TotalNonArchLocalHeight(x);
// = Log(Max(Abs(Numerator(x)),Denominator(x)));
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
//
// 2. Silverman's bounds
//
////////////////////////////////////////////////////////////////////////////////////

// This is double the formula in Silverman Math Comp 1990 page 725!

intrinsic FaltingsHeight(E::CrvEll) -> FldPrElt
{Faltings height of an elliptic curve over a number field}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
return AbsLogHeight(Discriminant(E))/6 + 
       AbsLogArchHeight(jInvariant(E))/6 + 
       AbsLogArchHeight(b2/12) + 
       (IsZero(b2) select 0 else Log(2))
 where b2:=bInvariants(E)[1];
end intrinsic;

// Again, compared with Silverman we have doubled everything since our
// canonical height is twice his.

// NB the constant 1.922 = 2*0.961 below is from Bremner's correction 
// to Silverman's paper; Silverman has 0.973 giving 2*0.973 = 1.946.

intrinsic SilvermanHeightBounds(E::CrvEll) -> SeqEnum
{Silverman's lower and upper bounds for height differences on an elliptic curve over a number field:
returns [l,u] where l le h(P)-h^(P) le u}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
mu:=FaltingsHeight(E);
return [-mu - 2.14, mu + AbsLogHeight(jInvariant(E))/12 + 1.922];
end intrinsic;

intrinsic SilvermanHeightBound(E::CrvEll) -> FldPrElt
{Silverman's upper bound for height differences on an elliptic curve over a number field:
an upper bound for h(P)-h^(P)}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
return SilvermanHeightBounds(E)[2];
end intrinsic;

intrinsic SilvermanUpperHeightBound(E::CrvEll) -> FldPrElt
{Silverman's upper bound for height differences on an elliptic curve over a number field:
an upper bound for h(P)-h^(P)}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
return SilvermanHeightBounds(E)[2];
end intrinsic;

intrinsic SilvermanLowerHeightBound(E::CrvEll) -> FldPrElt
{Silverman's lower bound for height differences on an elliptic curve over a number field:
a lower bound for h(P)-h^(P)}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
return SilvermanHeightBounds(E)[1];
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
//
//  3. Cremona-Prickett-Siksek (CPS) bounds
//
////////////////////////////////////////////////////////////////////////////////////

// (1) non-archimedan contributions

// The function alpha_v from CPS paper:

function alpha_v(cp,Kod)
if cp eq 1 then return 0; end if;
case Kod:
when KodairaSymbol("I0"):   return 0;
when KodairaSymbol("II"):   return 0;
when KodairaSymbol("III"):  return 1/2;
when KodairaSymbol("IV"):   return 2/3;
when KodairaSymbol("I0*"):  return 1;
when KodairaSymbol("II*"):  return 0;
when KodairaSymbol("III*"): return 3/2;
when KodairaSymbol("IV*"):  return 4/3;
else
n:=0; 
while true do 
n+:=1;
if Kod eq KodairaSymbol("I" cat IntegerToString(n)) 
then // type In
     return (IsEven(n) select n/4 else (n^2-1)/(4*n)); 
else
if Kod eq KodairaSymbol("I" cat IntegerToString(n) cat "*") 
then  // type I*n
      return (cp eq 2 select 1 else (n+4)/4);
end if;
end if;
end while;
end case;
end function;

intrinsic CPSLocalNonArch(E::CrvEll, P::RngOrdIdl) -> FldPrElt
{Local contribution at P to CPS upper height bound}
require Type(BaseField(E)) eq FldNum : "Base ring of E must be a number field";
require IsPrime(P) : "second argument must be a prime ideal";
return (Log(Norm(P))/Degree(BaseField(E))) * 
       (alpha_v(localdata[4],localdata[5]) + 
       (Valuation(Discriminant(E),P)-Valuation(Discriminant(minmodel),P))/6)
where localdata, minmodel := LocalInformation(E,P);
end intrinsic;

// Version over Q of the above:

intrinsic CPSLocalNonArch(E::CrvEll, P::RngIntElt) -> FldPrElt
{Local contribution at P to CPS upper height bound}
require Type(BaseField(E)) eq FldRat : "Base ring of E must be Q";
//require IsMinimalModel(E) : "E must be a minimal model";
require IsPrime(P) : "second argument must be a prime number";
return Log(P) *  alpha_v(localdata[4],localdata[5])
                 where localdata := LocalInformation(E,P);
end intrinsic;

intrinsic CPSTotalNonArch(E::CrvEll) -> FldPrElt
{Total non-archimedean contribution to CPS upper height bound for E}
K:=BaseField(E);
require Type(K) eq FldNum or Type(K) eq FldRat: "Base ring of E must be Q or a number field";
if Type(K) eq FldNum then
return &+[CPSLocalNonArch(E,P): P in Support((R!Discriminant(E))*R)]
where R:=Integers(BaseField(E));
else
//require IsMinimalModel(E) : "E must be a minimal model";
return &+[CPSLocalNonArch(E,P): P in PrimeDivisors(Integers()!Discriminant(E))];
end if;
end intrinsic;

function de_const(f,g) 
// f,g are real polys;  returns inf_{x\in[-1,1], f(x) ge 0} max{|f(x)|,|g(x)|}
// and sup of same
S := &cat[[r[1] : r in Roots(pol) | IsReal(r[1])] 
          : pol in [g,f+g,f-g,Derivative(f),Derivative(g)]];
S := [x : x in S | -1 le x and x le 1];
S := [x : x in S | Evaluate(f,x) ge 0];
S := [-1,1] cat S;
S := S cat [r[1] : r in Roots(f) | IsReal(r[1]) and -1 le r[1] and r[1] le 1]; 
if #S eq 0 then return []; else
return [Min(T),Max(T)] where T:={Max(Abs(Evaluate(f,x)),Abs(Evaluate(g,x))) : x in S};
end if;
end function;


intrinsic CPSReal(E::CrvEll, i::RngIntElt) -> FldPrElt
{Real Archimedean contribution to CPS lower and upper height bounds at i'th real place}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
bs:=bInvariants(E);
if Type(K) eq FldNum then // embed in R using i'th embedding of K
   r,s:=Signature(K);
   require 1 le i and i le r: "Invalid embedding number (must be Real)"; 
   bs:=[Conjugate(b,i) : b in bs];
else // K eq Q
   require i eq 1: "Invalid embedding number for Q (must be 1)"; 
end if;
b2,b4,b6,b8:=Explode(bs);
f:=Polynomial(RealField(),[b6,2*b4,b2,4]);
g:=Polynomial(RealField(),[-b8,-2*b6,-b4,0,1]);
F:=Polynomial(RealField(),Reverse([b6,2*b4,b2,4,0]));
G:=Polynomial(RealField(),Reverse([-b8,-2*b6,-b4,0,1]));
de:=de_const(f,g);
dded:=de_const(F,G);
del:=1/(#de eq 0 select dded[2] else Max(de[2],dded[2]));
eps:=1/(#de eq 0 select dded[1] else Min(de[1],dded[1]));
// "CPSReal returns ", [del, eps];
return [del, eps];
end intrinsic;

// Function to test if the square S=[a,b,r] intersects the closed unit disk
// S=[a,b,r] is the square [a,a+r]x[b,b+r] and is either [-1,-1,2] or contained in one quadrant
function SquareIntersectsDisk(S)
 a,b,r:=Explode(S);
 if r eq 2 then return true; end if; // for the square [-1,-1,2] only 
 a2:=a^2; b2:=b^2; ar2:=(a+r)^2; br2:=(b+r)^2;
 return (a2+b2 le 1) or (ar2+b2 le 1) or (a2+br2 le 1) or (ar2+br2 le 1);
end function;

// Function to test if the square S=[a,b,r] intersects the open unit disk

function SquareIntersectsOpenDisk(S)
 a,b,r:=Explode(S);
 if r eq 2 then return true; end if; // for the square [-1,-1,2] only 
 a2:=a^2; b2:=b^2; ar2:=(a+r)^2; br2:=(b+r)^2;
 allinside:= (a2+b2 lt 1) and (ar2+b2 lt 1) and (a2+br2 lt 1) and (ar2+br2 lt 1);
 alloutside:= (a2+b2 gt 1) and (ar2+b2 gt 1) and (a2+br2 gt 1) and (ar2+br2 gt 1);
 return not (allinside or alloutside);
end function;

function alphabeta(P,Q); // P,Q complex polynomials
 i:=BaseRing(P).1; 

 function h(z); 
    return Max(Abs(Evaluate(P,z)),Abs(Evaluate(Q,z)));
 end function;

 function E(z,eta); 
    return Max(&+[(eta^n)*Abs(Evaluate(Derivative(P,n),z))/Factorial(n) : n in [1..Degree(P)]],
	       &+[(eta^n)*Abs(Evaluate(Derivative(Q,n),z))/Factorial(n) : n in [1..Degree(Q)]]);
 end function;

 RefineAlphaBound:=function (mu,S,al);
  a,b,r:=Explode(S);
  //  "Entering S = ",S," with al=",al, " -- SquareIntersectsDisk(S): ",SquareIntersectsDisk(S);
  if not SquareIntersectsDisk(S) then return al; end if;
  u:=(a+r/2)+(b+r/2)*i;  eta:=r/Sqrt(2);
  if Abs(u) gt 1 then // find a corner of S in D
  eta*:=2;              u:=a+b*i;                     // BL corner
  if Abs(u) gt 1 then   u:=(a+r)+b*i;                 // BR corner
  if Abs(u) gt 1 then   u:=a+(b+r)*i;                 // TL corner
  if Abs(u) gt 1 then   u:=(a+r)+(b+r)*i;             // TR corner
  end if;  end if;  end if;  
  end if;
  // Now u is the centre or a corner of S and is in D
  if Abs(u) gt 1 then "Problem!  u = ",u," is outside the unit circle"; end if;
  //  "u = ",u; "eta = ",eta;
  hu:=h(u);
  if hu-E(u,eta) gt al*Exp(-mu) then  
    return al; 
  end if;
  if hu lt al then 
    al:=hu;  //  "al reduces to ",al;
  end if;
  al := $$(mu,[a,b,r/2],al);
  al := $$(mu,[a,b+r/2,r/2],al);
  al := $$(mu,[a+r/2,b,r/2],al);
  al := $$(mu,[a+r/2,b+r/2,r/2],al);
  // "Last returning al = ",al;
  return al;
 end function;

 RefineBetaBound:=function (mu,S,be);
  a,b,r:=Explode(S);
  //  "Entering S = ",S," with be=",be, " -- SquareIntersectsDisk(S): ",SquareIntersectsDisk(S);
  if not SquareIntersectsOpenDisk(S) then return be; end if;
  u:=(a+r/2)+(b+r/2)*i;  eta:=r/Sqrt(2);
  if Abs(u) gt 1 then // find a corner of S in D
  eta*:=2;              u:=a+b*i;                     // BL corner
  if Abs(u) gt 1 then   u:=(a+r)+b*i;                 // BR corner
  if Abs(u) gt 1 then   u:=a+(b+r)*i;                 // TL corner
  if Abs(u) gt 1 then   u:=(a+r)+(b+r)*i;             // TR corner
  end if;  end if;  end if;  
  end if;
  // Now u is the centre or a corner of S and is in D
  if Abs(u) gt 1 then "Problem!  u = ",u," is outside the unit circle"; end if;
  //  "u = ",u; "eta = ",eta;
  hu:=h(u);
  if hu-E(u,eta) lt be*Exp(-mu) then  
    return be;
  end if;
  if hu gt be then 
    be:=hu;    //  "be reduces to ",be;
  end if;
  be := $$(mu,[a,b,r/2],be);
  be := $$(mu,[a,b+r/2,r/2],be);
  be := $$(mu,[a+r/2,b,r/2],be);
  be := $$(mu,[a+r/2,b+r/2,r/2],be);
  // "Last returning be = ",be;
  return be;
 end function;


 mesh:=10;
  H:=[h((m+n*i)/mesh) : m,n in [-mesh..mesh] | m^2+n^2 le mesh^2];
  al:=Min(H);
  be:=Max(H);
 // "initial alpha = ",al;
 // "initial beta = ",be;
  al:= RefineAlphaBound(0.001,[-1,-1,2],al);
  be:= RefineBetaBound(0.001,[-1,-1,2],be);
 // "final alpha = ",al;
 // "final beta = ",be;
 return [al,be];
end function;

intrinsic CPSComplex(E::CrvEll, i::RngIntElt) -> FldPrElt
{Complex Archimedean contribution to CPS lower and upper height bounds at a complex place}
K:=BaseField(E);
require Type(K) eq FldNum: "Base field must be a number field";
// embed in C using i'th embedding of K, i between r+1 and r+s:
r,s:=Signature(K);
require r+1 le i and 1 le r+s: "Invalid embedding number (must be Complex)"; 
// Convert to Magma's numbering where complex conjugate embeddings are consecutive
 if i gt r then i:=2*i-r-1; end if;
b2,b4,b6,b8:=Explode([Conjugate(b,i) : b in bInvariants(E)]);
f:=Polynomial(ComplexField(),[b6,2*b4,b2,4]);
g:=Polynomial(ComplexField(),[-b8,-2*b6,-b4,0,1]);
F:=Polynomial(ComplexField(),Reverse([b6,2*b4,b2,4,0]));
G:=Polynomial(ComplexField(),Reverse([-b8,-2*b6,-b4,0,1]));
ab:=alphabeta(f,g);
AB:=alphabeta(F,G);
 // "CPSComplex(",i,") returns ", [1/Max(ab[2],AB[2]), 1/Min(ab[1],AB[1])];
return [1/Max(ab[2],AB[2]), 1/Min(ab[1],AB[1])];
end intrinsic;

intrinsic CPSHeightBounds(E::CrvEll) -> SeqEnum
{CPS's lower and upper bounds for height differences on an elliptic curve over a number field:
returns [l,u] where l le h(P)-h^(P) le u}
K:=BaseField(E);
require Type(K) eq FldNum or Type(K) eq FldRat: "Base ring of E must be Q or a number field";
if Type(K) eq FldRat then
   return [Log(l)/3, Log(u)/3 + CPSTotalNonArch(E)] 
   where   l,u:=Explode(CPSReal(E,1));
else
   r,s:=Signature(K);
   degs:=[1: i in [1..r]] cat [2: i in [r+1..r+s]];
   lulist:=[CPSReal(E,i) : i in [1..r]] cat [CPSComplex(E,i) : i in [r+1..r+s]];
   return[&+[degs[i]*Log(lulist[i][1]): i in [1..#lulist]]/(3*Degree(K)),
          &+[degs[i]*Log(lulist[i][2]): i in [1..#lulist]]/(3*Degree(K)) + CPSTotalNonArch(E)];
end if;
end intrinsic;

intrinsic CPSLowerHeightBound(E::CrvEll) -> FldPrElt
{CPS's lower bound for height differences on an elliptic curve over a number field:
returns l where l le h(P)-h^(P)}
return CPSHeightBounds(E)[1];
end intrinsic;

intrinsic CPSUpperHeightBound(E::CrvEll) -> FldPrElt
{CPS's upper bound for height differences on an elliptic curve over a number field:
returns u where h(P)-h^(P) le u}
return CPSHeightBounds(E)[2];
end intrinsic;

intrinsic CPSHeightBound(E::CrvEll) -> FldPrElt
{CPS's upper bound for height differences on an elliptic curve over a number field:
returns u where h(P)-h^(P) le u}
return CPSHeightBounds(E)[2];
end intrinsic;
