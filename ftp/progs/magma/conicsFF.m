//////////////////////////////////////////////////////////
//                                                      //
//           Solving conics over function fields        //
//                                                      //
//                                                      //
//    Authors:  John Cremona and David Roberts          //
//                                                      //
//    Functions for finding rational points on conics   //
//    defined over rational function fields, and        //
//    parametrizing all the points                      //
//                                                      //
//    Algorithm:  see Cremona and van Hoeij,            //
//                J T de Nombres de Bordeaux (to appear)//
//              + Simon for parametrization             //
//                                                      //
//    Last edited: 2006-07-20                           //
//                                                      //
//////////////////////////////////////////////////////////



// Some creation functions

intrinsic Conic(S::SeqEnum[RngElt]) -> CrvCon
{for a sequence of coefficients [a,b,c,d,e,f] returns the conic defined by
a*X^2+b*Y^2+c*Z^2+d*X*Y+e*Y*Z+f*X*Z or for a sequence [a,b,c] returns the
conic a*X^2+b*Y^2+c*Z^2}
require #S in [3,6]: "number of coefficents should equal 3 or 6";
P2<X,Y,Z>:=ProjectivePlane(Parent(S[1]));
if #S eq 3 then
eqn:=S[1]*X^2+S[2]*Y^2+S[3]*Z^2;
else eqn:=S[1]*X^2+S[2]*Y^2+S[3]*Z^2+S[4]*X*Y+S[5]*Y*Z+S[6]*X*Z;
end if;
require eqn ne 0: "Coefficients cannot all be zero";
C:=Scheme(P2,eqn);
require IsConic(C): "IsConic fails for this curve";
_,Con:=IsConic(C);
return Con;
end intrinsic;


intrinsic Matrix(C::CrvCon) -> AlgMatElt
{Returns the (symmetric) defining matrix M of the conic C
i.e. C is given by the equation [X,Y,Z]*M*[X,Y,Z]T where T denotes transpose.}
P:=ProjectivePlane(BaseRing(C));
f:=CoordinateRing(P)!DefiningPolynomial(C);
MC:=MonomialCoefficient;
S:=[MC(f,[2,0,0]),MC(f,[0,2,0]),MC(f,[0,0,2]),
MC(f,[1,1,0]),MC(f,[0,1,1]),MC(f,[1,0,1])];
M:=Matrix([[S[1],S[4]/2,S[6]/2],[S[4]/2,S[2],S[5]/2],[S[6]/2,S[5]/2,S[3]]]);
return M;
end intrinsic;


intrinsic Conic(M::AlgMatElt) -> CrvCon
{Returns the conic defined by the 3 x 3 matrix M}
require (NumberOfRows(M) eq 3) and (NumberOfColumns(M) eq 3):
"Argument must be a non-zero 3 x 3 matrix";
require M ne 0: "Matrix must be non-zero";
S:=[];
for i in [1..3] do S[i]:=M[i,i];
end for;
S[4]:=M[1,2]+M[2,1];S[5]:=M[2,3]+M[3,2];S[6]:=M[1,3]+M[3,1];
C:=Conic(S);
return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////




///////////////////////////////////////////////////////////////////
// Solving diagonal conics: non diagonal conics will reduce to   //
// this case by completing the square.                           //
// From conicFTdiag.m                                            //
///////////////////////////////////////////////////////////////////
//
// A function to solve diagonal conics over Q, just interfacing to the
// built-in magma function:
//
/////////////////////////////////////////////////////////////////
debug:=false;
function solve_conic_diag_Q(abc) // abc=[a,b,c] = diagonal coeffs
     a,b,c:=Explode(abc);
     Q:=FieldOfFractions(Parent(a));
     assert Type(Q) eq FldRat;
     a:=Q!a; b:=Q!b; c:=Q!c;
P2<X,Y,Z>:=ProjectivePlane(Q);
C0:=Curve(P2,a*X^2+b*Y^2+c*Z^2);
_,C:=IsConic(C0);
if not HasRationalPoint(C) then return false,_; end if;
Pl:=RationalPoint(C);
xl,yl,zl:=Explode(Eltseq(Pl));
dl:=Lcm(Denominator(xl),Denominator(yl));
xl*:=dl; yl*:=dl; zl*:=dl;
return true,[xl,yl,zl];
end function;

/////////////////////////////////////////////////////////////////
//
// A function to solve diagonal conics over a finite field, just
// interfacing to the built-in magma function:
//
/////////////////////////////////////////////////////////////////

function solve_conic_diag_Fq(abc) // abc=[a,b,c] = diagonal coeffs
     a,b,c:=Explode(abc);
     F:=Parent(a);
     assert Type(F) eq FldFin;
P2<X,Y,Z>:=ProjectivePlane(F);
C0:=Curve(P2,a*X^2+b*Y^2+c*Z^2);
_,C:=IsConic(C0);
if not HasRationalPoint(C) then return false,_; end if;
Pl:=RationalPoint(C);
xl,yl,zl:=Explode(Eltseq(Pl));
return true,[xl,yl,zl];
end function;

/////////////////////////////////////////////////////////////////
//
// Function to do square-free factorization of polynomials, i.e. 
// given f, write f=g*h^2 where g is squarefree.  Use Magma's
// SquareFreeFactorization() function
//
/////////////////////////////////////////////////////////////////

function SQFF(f)
    if Degree(f) lt 2 then return f,Parent(f)!1; end if;
    h:=&*[p[1]^(p[2] div 2) : p in SquareFreeFactorization(f) ];
    g:=f div h^2;
    assert f eq g*h^2;
    assert IsSquarefree(g);
    return g,h;
end function;


/////////////////////////////////////////////////////////////////
//
// Main function to solve diagonal conics; coefficients should lie in
// a field K which is either Q or finite or of the form F(T).  In the
// latter case we actually require a,b,c to be polynomials in F[T]
//
/////////////////////////////////////////////////////////////////
//
// I do not know how to test for this in Magma properly, so if the
// input has the wrong type the function will fail in strange ways.
//
/////////////////////////////////////////////////////////////////

function solve_conic_diag(abc) // abc=[a,b,c] = diagonal coeffs
a,b,c:=Explode(abc);
F:=FieldOfFractions(Universe(abc));
R:=Integers(F);
denom:=LCM([Denominator(F!x): x in abc]);
a,b,c:=Explode([R|x*denom: x in abc]);
FT:=Parent(a);
if 0 in abc then
  i:=Index(abc,0);
  r:=[FT|0,0,0]; r[i]:=1;
  return true,r;
  end if;

if debug then print "In solve_conic_diag() with [a,b,c] = ",abc," over ",FT; end if;
// Detect if the equation is defined over Q or a finite field where
// Magma already has conic-solving capability:

if Type(FT) eq FldRat or Type(FT) eq RngInt then
return solve_conic_diag_Q(abc);
end if;

if Type(FT) eq FldFin then
return solve_conic_diag_Fq(abc);
end if;

// Define the Base field F and the variable T such that the conic is
// defined over F(T):

T:=FT.1; F:=BaseRing(FT);

// Reduce to the case a*b*c square-free; Xscale, Yscale, Zscale store
// the scalings for the transformation back, and the flag scaled
// records whether or not any scaling has in fact been done:

scaled:=false;
Xscale:=1; Yscale:=1; Zscale:=1;
a0:=a; b0:=b; c0:=c;  // keep the original coefficients

// Reduction 1: remove any common factors of all three coefficients.
// No scaling of solution needed

g:=Gcd(Gcd(a,b),c);
if Degree(g) gt 0
then 
if debug then print "dividing out by a common factor ",g; end if;
a div:=g; b div:=g; c div:=g;
end if;

// Reduction 2: remove any square factors of all three coefficients.
// Scaling of solution needed

a1,a2:=SQFF(a);  // a=a1*a2^2 with a1 square-free
if Degree(a2) gt 0 then a:=a1; Yscale*:=a2; Zscale*:=a2; scaled:=true; end if;
b1,b2:=SQFF(b);  // b=b1*b2^2 with b1 square-free
if Degree(b2) gt 0 then b:=b1; Xscale*:=b2; Zscale*:=b2; scaled:=true; end if;
c1,c2:=SQFF(c);  // c=c1*c2^2 with c1 square-free
if Degree(c2) gt 0 then c:=c1; Xscale*:=c2; Yscale*:=c2; scaled:=true; end if;

// Reduction 3: remove any common factors of any two coefficients.
// Scaling of solution needed

while Degree(Gcd(a,b)) gt 0
    or Degree(Gcd(b,c)) gt 0
	or Degree(Gcd(a,c)) gt 0 
	do
	g:=Gcd(a,b);
    if Degree(g) gt 0
	then a div:=g; b div:=g; c*:=g;
	Zscale*:=g;
	scaled:=true;
    end if;
    g:=Gcd(b,c);
    if Degree(g) gt 0
	then b div:=g; c div:=g; a*:=g;
	Xscale*:=g;
	scaled:=true;
    end if;
    g:=Gcd(a,c);
    if Degree(g) gt 0
	then a div:=g; c div:=g; b*:=g;
	Yscale*:=g;
	scaled:=true;
    end if;
end while;

if debug then print "...after reducing, [a,b,c] = ",[a,b,c]; end if;

// Check that after all that we now have a "constant" equation:
// if so, use recursion

if Degree(a) eq 0 and Degree(b) eq 0 and Degree(c) eq 0
then
if debug then print "...constant coefficients!"; end if;
flag,Pl:=$$([F!a,F!b,F!c]);
if flag then 
// Coerce back into FT and rescale to original variables:
xsol:=FT!(Pl[1]);
ysol:=FT!(Pl[2]);
zsol:=FT!(Pl[3]);
if scaled then
 xsol*:=Xscale;
 ysol*:=Yscale;
 zsol*:=Zscale;
end if;
return true, [xsol,ysol,zsol];
else // flag is false: no solution
return false,_;
end if;
end if; // constant coefficient case

//
// Factorize the coefficients to find the bad places, and their degrees:
//

pa:=[p[1] : p in Factorization(a)];
dpa:=[Degree(p): p in pa];
if debug then print "a degrees: ",dpa;end if;
pb:=[p[1] : p in Factorization(b)];
dpb:=[Degree(p): p in pb];
if debug then print "b degrees: ", dpb; end if;
pc:=[p[1] : p in Factorization(c)];
dpc:=[Degree(p): p in pc];
if debug then print "c degrees: ", dpc; end if;

// Decide between case 0 (equal degree parities and no degree 1 bad
// place) and case 1 (unequal degree parities or a degree 1 bad place,
// in which case one degree 1 bad place (only) is removed from one of
// the support sets):

Case:=1;
da:=Degree(a);db:=Degree(b);dc:=Degree(c);
if (da-db) mod 2 eq 0 and (da-dc) mod 2 eq 0 then
Case:=0;
// but if there's a degree one factor of a,b, or c...
id:=Index(dpa,1);
if id ne 0 then  Case:=1; pa:=Remove(pa,id);
                 if debug then print "Removing linear factor from a, resetting Case to 1"; end if;
else
id:=Index(dpb,1);
if id ne 0 then Case:=1; pb:=Remove(pb,id);
                if debug then print "Removing linear factor from b, resetting Case to 1"; end if;
else
id:=Index(dpc,1);
if id ne 0 then Case:=1; pc:=Remove(pc,id);
           if debug then print "Removing linear factor from c, resetting Case to 1"; end if;
end if;
end if;
end if;
end if;

// Set A, B, C (the degrees of X,Y,Z in the solution):

A:=Ceiling((db+dc)/2)-Case;
B:=Ceiling((da+dc)/2)-Case;
C:=Ceiling((da+db)/2)-Case;
if debug then print "A=",A, " B=",B, " C=",C; end if;

// In case 0, solve the leading-coefficient equation:

if Case eq 0 then
la:=LeadingCoefficient(a);
lb:=LeadingCoefficient(b);
lc:=LeadingCoefficient(c);
if debug then print "Solving leading-coefficient conic with coeffs ",
      [la,lb,lc]," over ",Parent(la); end if;
if Type(Parent(la)) eq FldRat or Type(Parent(la)) eq RngInt then
flag,Pl:= solve_conic_diag_Q([la,lb,lc]);
else
if Type(Parent(la)) eq FldFin then
flag,Pl:= solve_conic_diag_Fq([la,lb,lc]);
else

// Use recursion: but first we must convert the leading coefficients
// from rational functions to polynomials.  This will cause a run-time
// error if the base field F is not suitable!
//
g:=Lcm([Denominator(l) : l in [la,lb,lc]]);
la:=Numerator(g*la);
lb:=Numerator(g*lb);
lc:=Numerator(g*lc);
flag,Pl:=$$([la,lb,lc]);
end if;
end if;

// If the leading coefficient equation has no solution, quit now:

if debug then print "Soluble? ",flag; end if;
if not flag then return false,_; end if;

// Otherwise use it to form the first three equations:

xl,yl,zl:=Explode(Pl);
if debug then print "leading coeff solution = ",Pl; end if;

// Matrix Mp will hold the coefficients of the linear equations to be
// solved; for technical reasons each equation is in a column of Mp.
// First we have 3 columns from the leading-coefficient conic solution
// (here case=0)
//
// Mplist is a list of such matrices, which will in the end be
// concatenated

Mp:=Transpose(Matrix([
	    [F!0 : i in [0..A-1]] cat [F!1] 
    cat     [F!0 : j in [0..B]]
    cat     [F!0 : k in [0..C]]
    cat     [F!-xl],
	    [F!0 : i in [0..A]]
    cat     [F!0 : j in [0..B-1]] cat [F!1] 
    cat     [F!0 : k in [0..C]]
    cat     [F!-yl],
	    [F!0 : i in [0..A]]
    cat     [F!0 : j in [0..B]]
    cat     [F!0 : k in [0..C-1]] cat [F!1] 
    cat     [F!-zl]
]
));
//"Matrix from l.c. condition = ",Mp;
Mplist:=<Mp>;
else // case=1
Mplist:=<>;
end if;

// Here ends the case=0/1 division

// Now make up the rest of the matrices of the linear system; each
// degree d factor of a, b or c contributes d more columns (except for
// a linear factor if we have excluded one earlier); the number of
// rows is A+B+C+3, and the number of extra columns is either deg(abc)
// or deg(abc)-1.

for p in pa do  // process p|a
d:=Degree(p);
//print "Processing factor ",p," of a of degree ",d;
Fp:=quo<FT|p>;
r:=(-(Fp!c)/(Fp!b));
//print "Taking square root of", r;
flag,r:=IsSquare(r);
//print "result: ",flag; if flag then print "sqrt = ",r; end if;
if not flag then return false,p; end if; // no local certificate
//  The following line is only for testing; it ensures that repeated
//  running of the same examples should give different solutions!
//r*:=Random({-1,1});
r:=FT!r;
assert ((b*r^2+c) mod p) eq 0;
// we have a local certificate, and construct d new columns:
Mp:=Matrix(
     [[F!0: l in [0..d-1]] : i in [0..A]]
     cat  [[F!Coefficient(T^j mod p,l): l in [0..d-1]] : j in [0..B]]
     cat  [[F!Coefficient(-r*T^k mod p,l): l in [0..d-1]] : k in [0..C]]
     cat  [[F!0: l in [0..d-1]] : l in [1..1-Case]]
);
Append(~Mplist,Mp);
end for;

for p in pb do // process p|b
d:=Degree(p);
//print "Processing factor ",p," of b of degree ",d;
Fp:=quo<FT|p>;
r:=(-(Fp!a)/(Fp!c));
//print "Taking square root of", r, " in ",Fp;
flag,r:=IsSquare(r);
//print "result: ",flag; if flag then print "sqrt = ",r; end if;
if not flag then return false,p; end if;
//r*:=Random({-1,1});
r:=FT!r;
assert ((c*r^2+a) mod p) eq 0;
// we have a local certificate, and construct d new columns:
Mp:=Matrix(
     [[F!Coefficient(-r*T^i mod p,l): l in [0..d-1]] : i in [0..A]]
 cat [[F!0: l in [0..d-1]] : j in [0..B]]
 cat  [[F!Coefficient(T^k mod p,l): l in [0..d-1]] : k in [0..C]]
 cat  [[F!0: l in [0..d-1]] : l in [1..1-Case]]
);
Append(~Mplist,Mp);
end for;

for p in pc do // process p|c
d:=Degree(p);
//print "Processing factor ",p," of c of degree ",d;
Fp:=quo<FT|p>;
r:=(-(Fp!b)/(Fp!a));
//print "Taking square root of", r;
flag,r:=IsSquare(r);
//print "result: ",flag; if flag then print "sqrt = ",r; end if;
if not flag then return false,p; end if;
//r*:=Random({-1,1});
r:=FT!r;
assert ((a*r^2+b) mod p) eq 0;
// we have a local certificate, and construct d new columns:
Mp:=Matrix(
     [[F!Coefficient(T^i mod p,l): l in [0..d-1]] : i in [0..A]]
 cat [[F!Coefficient(-r*T^j mod p,l): l in [0..d-1]] : j in [0..B]]
 cat [[F!0: l in [0..d-1]] : k in [0..C]]
 cat  [[F!0: l in [0..d-1]] : l in [1..1-Case]]
);
Append(~Mplist,Mp);
end for;

// Now Mplist contains all the equations we need to solve, as a list
// of matrices.  Concatenate them and find the kernel.  Since we know
// from theory that it has positive dimension, we pick out the first
// basis vector and convert it to a list:

K:=Eltseq(Kernel(HorizontalJoin(Mplist)).1);
//print "Kernel = ",K;

// The entries in K are the coefficients of the solution X,Y,Z (in
// that order); if we added 3 new variables for case 0 we can now
// ignore them.

xsol:=&+([0] cat [K[i]*T^(i-1) : i in [1..A+1]]);
ysol:=&+([0] cat [K[A+1+j]*T^(j-1) : j in [1..B+1]]);
zsol:=&+([0] cat [K[A+B+2+k]*T^(k-1) : k in [1..C+1]]);

// Rescale to original variables if necessary:

if scaled then
 xsol*:=Xscale;
 ysol*:=Yscale;
 zsol*:=Zscale;
end if;

// Remove any common factors:

g:=Gcd([xsol,ysol,zsol]);
if Degree(g) gt 0 then
  xsol div:=g; ysol div:=g; zsol div:=g;
end if;

// Check we do have a solution! (For debugging only) 

lhs:=a0*xsol^2+b0*ysol^2+c0*zsol^2;
if debug then print "LHS = ",lhs; end if;
assert lhs eq 0;

return true,[xsol,ysol,zsol];
end function; // solve_conic_diag()

//////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////
//     Function for solving "semi-diagonal" conics.     //
//////////////////////////////////////////////////////////

// Solve a conic of the form Y^2 = a*X^2 + b*X*Z + c*Z^2
function solve_semi(ABC); // ABC is [a,b,c] with the conic in the above form
// complete the square then solve and parametrize the diagonal conic
a,b,c:=Explode(ABC);
F:=FieldOfFractions(Parent(a));
C:=Conic([F|a,-1,c,0,0,b]);
flag,p:=solve_conic_diag([1,-a,a*c-b^2/4]);
if flag then
  x,y,z:=Explode(Eltseq(p));
  X:=(x-(b/2)*z)/a;
  p1:=[X,y,z];
  assert IsCoercible(C,p1);
  return true,p1;
  end if;
return false,_;
end function;

///////////////////////////////////////////////////////////
//             Function for general conics		 //
///////////////////////////////////////////////////////////

// Solve a conic of the form a*X^2 + b*Y^2 + c*Z^2 + d*X*Y + e*Y*Z + f*X*Z = 0
// reduces to solving a semi-diagonal conic by completing the square.

function solve_general(cfs);
a,b,c,d,e,f:=Explode(cfs);
K:=Universe(cfs);
C:=Conic(cfs);
if a eq 0 then return [K|1,0,0]; end if;
if b eq 0 then return [K|0,1,0]; end if;
if c eq 0 then return [K|0,0,1]; end if;

cfs_a:=[x/a: x in cfs];
_,b1,c1,d1,e1,f1:=Explode(cfs_a);
flag,p:=solve_semi([(d1^2)/4-b1,(d1*f1)/2-e1,(f1^2)/4-c1]);
if flag then
  u,w,v:=Explode(Eltseq(p));
  Y:=u; Z:=v; X:=w-((d1*u)/2+(f1*v)/2);
  assert IsCoercible(C,[X,Y,Z]);
  return true,[X,Y,Z];
  end if;
return false,_;
end function;

////////////////////////////////////////////////////////////
//              Parametrization of Conics                 //
////////////////////////////////////////////////////////////

primitivecoords:=function(p);
  p:=Eltseq(p);
  K:=Parent(p[1]);
  R:=RingOfIntegers(K);
  L:=LCM([Denominator(x): x in p]);
  p:=[R!(L*x): x in p];
  G:=GCD(p);
  p:=[R!(x/G): x in p];
  return(p);
end function;

ds_paramP:=function(Con,p);
// see Denis Simon - "Sur la parametrisation des
// solutions des equations quadratiques"

	if (p[1] eq 0) and (p[2] eq 0) then return Parametrization(Con,Con!p); end if;
	// above line is to temporarily avoid a bug when p is of the form [0,0,z];

FC:=DefiningEquation(Con);
MC:=Matrix(Con);
P<X,Y,Z>:=AmbientSpace(Con);
K:=FieldOfFractions(BaseRing(P));
R:=RingOfIntegers(K);

p:=primitivecoords(p);
G:=GCD(p);
p:=[R!(x/G): x in p];
assert GCD(p) eq 1;
a:=p[1];b:=p[2];c:=p[3];
g,u,v:=Xgcd(a,b);
assert g eq a*u+b*v;
h,w,z:=Xgcd(g,c);
assert h eq 1;
assert g*w+c*z eq 1;
M:=Matrix([[R|a,b,c],[R|-v,u,0],[R|-a*z/g,-b*z/g,w]]);
assert Determinant(M) eq 1;
Mt:=Transpose(M);

qp:=M*MC*Mt;
assert qp[1][1] eq 0;
qh:=Matrix([[qp[2][2],2*qp[2][3],qp[3][3]],[-2*qp[1][2],-2*qp[1][3],0],[0,-2*qp[1][2],-2*qp[1][3]]]);
q:=Mt*qh;
q1,q2,q3:=Explode(RowSequence(q));

P1:=ProjectiveSpace(K,1);
eq1:=q1[1]*P1.1^2+q1[2]*P1.1*P1.2+q1[3]*P1.2^2;
eq2:=q2[1]*P1.1^2+q2[2]*P1.1*P1.2+q2[3]*P1.2^2;
eq3:=q3[1]*P1.1^2+q3[2]*P1.1*P1.2+q3[3]*P1.2^2;
par:=[eq1,eq2,eq3];
m:=map<P1->Con|par>;

return m;
end function;



///////////////////////////////////////////////////////////
// intrinsics


intrinsic HasRationalPoint_FldFun(C::CrvCon) -> BoolElt,Pt
{Returns true if the Conic C has a point}

M:=Matrix(C);
K:=BaseRing(M);
require Characteristic(K) ne 2:
  "Base-ring of conic cannot have characteristic 2";
if IsDiagonal(M) then
  abc:=[M[i,i]: i in [1..3]];
  flag,p:=solve_conic_diag(abc);
  if flag then return true,C!p; end if;
  return false,_; end if;

if [M[1,2],M[2,1],M[2,3],M[3,2]] eq [K|0,0,0,0] then
  // semi-diagonal case
  a:=-M[2,2]; if a ne 0 then
    flag,p:=solve_semi([M[1,1]/a,2*M[1,3]/a,M[3,3]/a]);
    if flag then return true,C!p; end if;
    return false,_; end if;
  return true,C![0,1,0]; end if;

flag,p:=solve_general([M[1,1],M[2,2],M[3,3],2*M[1,2],2*M[2,3],2*M[1,3]]);
if flag then return true,C!p; end if;
return false,_;

end intrinsic;

///////////////////////////////////////////////////////////////

intrinsic DS_Parametrization(C::CrvCon) -> MapSch
  {Parametrization of the conic C}
flag,p:=HasRationalPoint_FldFun(C);
require flag: "C does not have a rational point";
return ds_paramP(C,p);
end intrinsic;

intrinsic DS_Parametrization(C::CrvCon,p::Pt) -> MapSch
  {Parametrization of the conic C with point p}
return ds_paramP(C,p);
end intrinsic;




