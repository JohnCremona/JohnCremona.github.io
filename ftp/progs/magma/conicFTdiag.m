/////////////////////////////////////////////////////////////////
// Solving Diagonal Conics over F(T) (by JEC following Mark van Hoeij,
// with the additional trick using degree 1 places)
/////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////
//
// A function to solve diagonal conics over Q, just interfacing to the
// built-in magma function:
//
/////////////////////////////////////////////////////////////////

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
FT:=Parent(a);
print "In solve_conic_diag() with [a,b,c] = ",abc," over ",FT;
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
print "dividing out by a common factor ",g;
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

print "...after reducing, [a,b,c] = ",[a,b,c];

// Check that after all that we now have a "constant" equation:
// if so, use recursion

if Degree(a) eq 0 and Degree(b) eq 0 and Degree(c) eq 0
then
print "...constant coefficients!";
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
print "a degrees: ",dpa;
pb:=[p[1] : p in Factorization(b)];
dpb:=[Degree(p): p in pb];
print "b degrees: ", dpb;
pc:=[p[1] : p in Factorization(c)];
dpc:=[Degree(p): p in pc];
print "c degrees: ", dpc;

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
                 print "Removing linear factor from a, resetting Case to 1";
else
id:=Index(dpb,1);
if id ne 0 then Case:=1; pb:=Remove(pb,id);
                print "Removing linear factor from b, resetting Case to 1";
else
id:=Index(dpc,1);
if id ne 0 then Case:=1; pc:=Remove(pc,id);
           print "Removing linear factor from c, resetting Case to 1";
end if;
end if;
end if;
end if;

// Set A, B, C (the degrees of X,Y,Z in the solution):

A:=Ceiling((db+dc)/2)-Case;
B:=Ceiling((da+dc)/2)-Case;
C:=Ceiling((da+db)/2)-Case;
print "A=",A, " B=",B, " C=",C;

// In case 0, solve the leading-coefficient equation:

if Case eq 0 then
la:=LeadingCoefficient(a);
lb:=LeadingCoefficient(b);
lc:=LeadingCoefficient(c);
print "Solving leading-coefficient conic with coeffs ",
      [la,lb,lc]," over ",Parent(la);
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

print "Soluble? ",flag;
if not flag then return false,_; end if;

// Otherwise use it to form the first three equations:

xl,yl,zl:=Explode(Pl);
print "leading coeff solution = ",Pl;

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
"LHS = ",lhs;
assert lhs eq 0;

return true,[xsol,ysol,zsol];
end function; // solve_conic_diag()

//////////////////////////////////////////////////////////////////////
//  end of function solve_conic_diag()
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//
// Test functions and examples
//
//////////////////////////////////////////////////////////////////////

// Function to construct a "random" polynomial over F of degree d:
// If char(F)=0 the coeffs are random between -d and +d
// If char(F)>0 the coeffs are random in F

function randpol(F,degbd)
if Characteristic(F) eq 0 then
   return Polynomial(F,[F!(Random(2*degbd)-degbd): i in [1..degbd]] cat [F!1]);
else
   return Polynomial(F,[Random(F): i in [1..degbd]] cat [F!1]);
end if;
end function;

//////////////////////////////////////////////////////////////////////
//  function test_diag() to test solve_conic_diag(), given a base
//  field F and a bound on the degrees of a,b,c
//
//////////////////////////////////////////////////////////////////////

function test_diag(F,d)
flag:=false;
repeat
a:=randpol(F,d);
b:=randpol(F,d);
c:=-a*randpol(F,d)^2-b*randpol(F,d)^2;
//c:=&*[fci[1] : fci in Factorization(c) | IsOdd(fci[2])]; 
abc:=[a,b,c];
print "*******************************";
print "Using diagonal algorithm...";
time flag,sol:= solve_conic_diag(abc);
if not flag then print abc,"--not soluble"; end if;
until flag;
print "solution to ",abc," is ",sol;
return abc,sol;
end function; //test_diag

/////////////////////////////////////////////////////////////////
//  EXAMPLES over Q(t1,t2)
/////////////////////////////////////////////////////////////////

Q:=RationalField();
Q1<t1>:=FunctionField(Q);
R2<t2>:=PolynomialRing(Q1);

/////////////////////////////////////////////////////////////////
//  EXAMPLE 1 IN THE PAPER
/////////////////////////////////////////////////////////////////
function example1diag()
a := 1;
b := 2*t2^2+ 2*t1*t2-t1^2;
c := -3*t2^4-4*t1*t2^3  + 8*t1^2*t2^2 + 16*t1^3*t2 - 48*t1^4;
flag,sol:=solve_conic_diag([a,b,c]);
assert flag;
"One solution (before scaling) is ",sol;
sol:=
[Lcm([Denominator(c): c in &cat[(Coefficients(s)): s in sol]])*ss:  ss in sol];

cco:=&cat&cat[[Coefficients(PolynomialRing(Q)!co): co in Coefficients(s)]: s in sol];
d:=Lcm([1] cat [Denominator(ci):ci in cco]);
g:=Gcd([Integers()!(d*ci) : ci in cco]);
sol:=[(d/g)*s: s in sol];
"Scaled solution: ", sol;
assert a*sol[1]^2+b*sol[2]^2+c*sol[3]^2 eq 0;

//Mark's solutions from Maple program:
msol1:=[t2^3+t1*t2^2 + 4*t1^2* t2 - 4*t1^3 , t2^2 - 4*t1^2 , t2];
assert a*msol1[1]^2+b*msol1[2]^2+c*msol1[3]^2 eq 0;
"Mark's solution 1: ", msol1;
msol2:=[ t2^3 + 2*t1^2 *t2 + 8*t1^3 , t2^2 + 2*t1 *t2 -4*t1^2 , t2+t1];
assert a*msol2[1]^2+b*msol2[2]^2+c*msol2[3]^2 eq 0;
"Mark's solution 2: ", msol2;

return sol;
end function;

/////////////////////////////////////////////////////////////////
//  EXAMPLE 2 IN THE PAPER
/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////
//procedure example2diag()
function example2diag()
/////////////////////////////////////////////////////////////////
a := t1^2+1;
b := -(t1^2+1)*t2^2 + (4*t1^2+4)*t2-1;
c := (2*t1^3-10*t1^2+2*t1-9)*t2^4 - (6*t1^3 + 6*t1-2)*t2^3+
     (t1^4-8*t1^3-2*t1^2-6*t1-2)*t2^2 - (4*t1^4+2*t1^2-2*t1-2)*t2 - 1;

flag,sol:=solve_conic_diag([a,b,c]);
assert flag;
"One solution (before scaling) is ",sol;
sol:=
[Lcm([Denominator(c): c in &cat[(Coefficients(s)): s in sol]])*ss:  ss in sol];

cco:=&cat&cat[[Coefficients(PolynomialRing(Q)!co) 
 : co in Coefficients(s)] : s in sol];
d:=Lcm([1] cat [Denominator(ci):ci in cco]);
g:=Gcd([Integers()!(d*ci) : ci in cco]);
sol:=[(d/g)*s: s in sol];
"Scaled solution: ", sol;
assert a*sol[1]^2+b*sol[2]^2+c*sol[3]^2 eq 0;

return sol;
end function;
//end procedure;

