//////////////////////////////////////////////////////////////////////
//
//	 Routines for manipulating ternary quadrics over F(T)
//	 minimization, reduction and solution
//
//////////////////////////////////////////////////////////////////////
// 1. General utilities (many not used later)
//////////////////////////////////////////////////////////////////////

function randpol(F,degbd)
if Characteristic(F) eq 0 then
     return Polynomial(F,[F!(Random(2*degbd)-degbd): i in [1..degbd]] cat [F!1]);
else
     return Polynomial(F,[Random(F): i in [1..degbd]] cat [F!1]);
end if;
end function;

function rand22(F,degbd)
return SymmetricMatrix([randpol(F,degbd) : i in [1..3]]);
end function;

function rand33(F,degbd)
return SymmetricMatrix([randpol(F,degbd) : i in [1..6]]);
end function;

// functions to convert between quadratic forms and symmetric matrices

function form2mat(f)
     FTXYZ:=Parent(f);
     return Matrix([[ (i eq j select 2 else 1) * 
                      MonomialCoefficient(f,FTXYZ.i*FTXYZ.j)
     :i in [1..3]]:j in [1..3]]);
end function;

function mat2form(M)
     FTXYZ:=PolynomialRing(BaseRing(Parent(M)),3);
     return &+ [ &+ [ M[i,j]*FTXYZ.i : i in [1..3] ] * FTXYZ.j : j in [1..3] ];
     end function;

function integermat(M)
 return Matrix([[Integers(BaseRing(Parent(M)))!M[i,j] 
                : j in [1..NumberOfColumns(M)]] 
                : i in [1..NumberOfRows(M)]]);
end function;

function divmat(M,c)
 return Matrix([[M[i,j] div c : j in [1..NumberOfColumns(M)]] 
                              : i in [1..NumberOfRows(M)]]);
end function;

function valmat(M,p)
 return Matrix([[M[i,j] eq 0 select -1 else Valuation(M[i,j],p) 
                : j in [1..NumberOfColumns(M)]] 
                : i in [1..NumberOfRows(M)]]);
end function;

// A is a mtrix over F[T] and p is an irreducible in F[T];
// returns A mod p as a matrix over F[T]/(p)
function matmodp(A,p)
    if Degree(p) gt 1 then
	Fp:=quo<BaseRing(A)|p>;
	return MatrixAlgebra(Fp,3)!A;
    else
	return Matrix([[A[i,j] mod p : j in [1..NumberOfColumns(A)]] 
	    : i in [1..NumberOfRows(A)]]);
    end if; 
end function; 
    
function makeprimitive(A)
 A*:=LCM([Denominator(A[i,j]):i,j in [1..3]]);
 g:=GCD([Numerator(A[i,j]):i,j in [1..3]]);
 return divmat(A,g);
end function;

function rankmodp(A,p)
     Fp:=quo<BaseRing(Parent(A))|p>;
     return Rank(MatrixAlgebra(Fp,3)!A);
     end function;

// Function to map a matrix over F[T] to a matrix over F specializing T to t0:

function Specialize(A,t0)
 return Matrix([[Evaluate(A[i,j],t0) : j in [1..NumberOfColumns(A)]] 
                              : i in [1..NumberOfRows(A)]]);
end function;

// 3x3 permutation matrix:

function permmat3(ijk)
     i,j,k:=Explode(ijk);
     return Matrix([ [ijk[i] eq j select 1 else 0 : j in [1..3]] : i in [1..3]]);
     end function;

// general permutation matrix:
function permmat(pi)
     n:=#GSet(Parent(pi));
     return Matrix([ [i^pi eq j select 1 else 0 : j in [1..n]] : i in [1..n]]);
end function;

function swaprows3(A,i,j)
     pi:=[k eq i select j else k eq j select i else k : k in [1..3]];
     P:=permmat3(pi); tP:=Transpose(P);
     return tP*A*P;
     end function;

// Given a subspace W of Fp^3, returns a matrix U in GL(3,F[T])
// s.t. the first dim(W) rows of U^-1 are a basis for W

function modpsub_to_unimod(W,p)
     //"Basis(W): ",     Basis(W);
     //"Basefield(W): ",     BaseField(W);
     R:=Parent(p); // should be F[T]
     //"R = ",R;
     vv:=[[R!wi : wi in Eltseq(w)] : w in Basis(W)];
     v,_,u:=SmithForm(Matrix(vv));
     u:=u^(-1);
     return u;
end function;

function badprimes(A)
return [p[1] : p in Factorization(Determinant(A))];
end function;


//////////////////////////////////////////////////////////////////////
// 2. Functions for minimizing at a prime p (irreducible in F[T])
//////////////////////////////////////////////////////////////////////

forward reduce33;

//debug_minim:=true;
debug_minim:=false;

// Reducing A when rank(A mod p) = 0

function rank0minim(A,p)
     assert rankmodp(A,p) eq 0;
     newA:=divmat(A,p);
     return true,newA,IdentityMatrix(BaseRing(A),3),p;
end function;

// Reducing A when rank(A mod p) = 1

function rank1minim(A,p)
     assert rankmodp(A,p) eq 1;
     Ap:=matmodp(A,p);
     kA:=Kernel(Ap);
     U:=DiagonalMatrix([1,1,p])*modpsub_to_unimod(kA,p);
if debug_minim then
     print Ap, U, matmodp(U*A*Transpose(U),p);
end if;
     newA:=divmat(U*A*Transpose(U),p);
     return true,newA,U,p;
end function;

// Reducing A when rank(A) (mod p) =2: returns false if p-adically insoluble

function rank2minim(A,p)
     Ap:=matmodp(A,p);
     assert Rank(Ap) eq 2;
     kA:=Kernel(Ap);
     U:=modpsub_to_unimod(kA,p);
     newA:=U*A*Transpose(U);
     Ap:=matmodp(newA,p);
     if debug_minim then
          print "first row/col should be 0 mod p:"; Ap;
	  print "with parent ",Parent(Ap);
      end if;
//    now row/col 1 of A mod p is 0

//    First see if a cross-reduction is possible:

     p2:=p^2;
     if newA[1,1] mod p2 eq 0 then
	 if debug_minim then
	     print "applying cross-reduction";
	 end if;
	 U:=DiagonalMatrix([1,p,p])*U;
	 newA:=divmat(U*A*Transpose(U),p2);
	 if debug_minim then 
	     //     print newA, U; 
	     print "rank2minim() returning";
	 end if;
	 return true,newA,U,p2;
     end if;
     
     if debug_minim then 
	 print "no cross-reduction possible";
     end if;

     //    analyse the bottom right 2x2 block
     //    if it represents 0 nontrivially we can make A[2,2]=0 mod p
     //    and minimize; otherwise A is insoluble p-adically.
     
     // see if A[2..3,2..3] represents 0 mod p
     
     R:=BaseRing(Parent(A));
     a:=Ap[2,2];
     if a eq 0 then // ok
	 V:=IdentityMatrix(R,3); 
	 if debug_minim then 
	     print "case 1:  V = ",V;
	 end if;
     else // arrange for A[2,2]=0 mod p
	 b:=Ap[2,3]; c:=Ap[3,3];
	 d2:=b*b-a*c;
	 if debug_minim then 
	     print "starting IsSquare(",d2,") over ",Parent(d2),"...";
	 end if;
	 flag,d:=IsSquare(d2);
	 if debug_minim then 
	     print "finished IsSquare(), returned ",flag;
	 end if;
	 if not flag then return false,_,_,_;
	 else
	     c2:=(-b+d); c3:=a;
	     assert a*c2^2+2*b*c2*c3+c*c3^2 eq 0;
	     c2:=R!c2;
	     c3:=R!c3;
	     g:=Gcd(c2,c3); 
	     if g ne 1 then c2 div:=g; c3 div:=g; end if;
	     _,_,u1:=SmithForm(Matrix([[c2,c3]]));
	     u1:=u1^(-1);  // has [c2,c3] as 1st column
	     V:=DirectSum(Matrix([[Parent(c2)!1]]),u1);
	     if debug_minim then 
		 print "case 2: V = ",V;
	     end if;
	 end if;  // soluble switch
     end if; // trivial case
     
     U:=V*U; 
     if debug_minim then 
	 print U, matmodp(U*A*Transpose(U),p);
     end if;
     U:=DiagonalMatrix([1,1,p])*U;
     if debug_minim then 
	 print U, U*A*Transpose(U), Determinant(U);
     end if;
     newA:=divmat(U*A*Transpose(U), p);
     if debug_minim then 
	 print "rank2minim() returning";
     end if;
     return true,newA,U,p;

end function;

// end of rank2minim

function minim012(A,p)
 r:= rankmodp(A,p); 
 assert r lt 3;     
if debug_minim then 
  print "rank mod p = ",r;
end if;
 case r:
  when 0: return rank0minim(A,p);
  when 1: return rank1minim(A,p);
  when 2: return rank2minim(A,p);
 end case;
if debug_minim then 
  print "minim012 returning";
end if;
end function;

forward minim33_with_support;

function minim33(A)
if IsDiagonal(A) then
   plist:=&cat[[p[1]: p in Factorization(A[i,i])] : i in [1,2,3]];
else
   detA:=Determinant(A);
   assert detA ne 0;
   plist:=[p[1]: p in Factorization(detA)];
end if;
   return minim33_with_support(A,plist);
end function;

function minim33_with_support(A,plist)
if debug_minim then 
   print "Minimizing matrix ",A," with support ",[BaseRing(A)!p: p in plist];
end if;
plist:=Setseq(Seqset(plist));
if debug_minim then 
    print "Degrees of bad places: ", [Degree(p) : p in plist];
end if;
   R:=BaseRing(Parent(A));
   U:=IdentityMatrix(R,3);
   f:=1;
   B:=A;  
   ok := true;

   while #plist gt 0 and ok do
   p:=plist[1];
if debug_minim then 
   print "Minimizing at ",p," of degree ",Degree(p);
end if;
   ok,B,U1,f1:=minim012(B,p);

   if not ok then 
if debug_minim then 
   print "Not locally soluble!"; 
end if;
   return false,_,_,_; 
//else // reduce as we go along
//if debug_minim then 
//   print "Reducing what we have so far..."; 
//end if;
//   B,V:=reduce33(B);
//   U1:=Transpose(V)*U1;
end if;

   U:=U1*U;
   f:=f1*f;
// N.B. B may still be singular mod p after one round of minimization
   if Determinant(B) mod p ne 0 then Exclude(~plist,p); end if;

// check
if debug_minim then 
     assert f*B eq U*A*Transpose(U);
end if;

   end while;

if debug_minim then 
   print "Finished minimization, returning";
end if;
   return true,B,U,f;
end function; // minim33_with_support

//////////////////////////////////////////////////////////////////////
// 3. Functions for reduction
//////////////////////////////////////////////////////////////////////

// LLL -- experimental only!

compdeg:=func<f,g|Degree(f)-Degree(g)>;

function LLLpoly(M)
     //n:=Degree(Parent(M));
n:=Round(Sqrt(Dimension(Parent(M))));
R:=BaseRing(Parent(M));
M_orig:=M;
"Entering LLLpoly, degrees are ", 
   [[Degree(M[i,j]): j in [1..n]] : i in [1..n]];
"Max degree = ",Max(&cat[[Degree(M[i,j]): j in [1..n]] : i in [1..n]]);
  // initial sorting
v,perm:=Sort([M[i,i] : i in [1..n]], compdeg);
"perm = ",perm, " of degree ",#GSet(Parent(perm));
U:=Parent(M)!permmat(perm^-1);
M:=Transpose(U)*M*U;
"After initial permutation, degrees are ", 
  [[Degree(M[i,j]): j in [1..n]] : i in [1..n]];
//
while true do
k:=1;
while k lt n do
// reduce degrees of M[k,j] for j>k:
if M[k,k] eq 0 then
"Zero entry on diagonal at position ",[k,k]," LLLpoly quits";
return M,U,k;
end if;
U1:=IdentityMatrix(R,n);
for j in [k+1..n] do
  U1[k,j]:=-(M[k,j] div M[k,k]);
end for;
M:=Transpose(U1)*M*U1;
U:=U*U1;
"After row reduction for k=",k," degrees are ",
  [[Degree(M[i,j]): j in [1..n]] : i in [1..n]];
// test to see if backtracking necessary
swap:=0;
for k1 in [k-1 .. 1 by -1] do
if compdeg(M[k1,k1],M[k,k]) gt 0 then // swap k,k1
swap:=1;
"Swapping positions ",k,", ",k1;
pi:=Parent(perm)!(k,k1);
U1:=Parent(M)!permmat(pi);
M:=Transpose(U1)*M*U1;
U:=U*U1;
k:=k1;
end if;
end for;
if swap eq 0 then k+:=1; end if;
end while;

v,perm:=Sort([M[i,i] : i in [1..n]], compdeg);
"final perm = ",perm, " moves ",Degree(perm)," entries";
if Degree(perm) eq 0 then // nothing changed, can return
return M,U;
else

U1:=Parent(U)!permmat(perm^-1);
U:=U*U1;
M:=Transpose(U1)*M*U1;
"After final permutation, degrees are ", 
  [[Degree(M[i,j]): j in [1..n]] : i in [1..n]];
end if;
end while;
end function;

//////////////////////////////////////////////////////////////////////
//
// Reduction of 2x2 symmetric polynomial matrices
//
//////////////////////////////////////////////////////////////////////

// Normally makes deg(a) smallest where M=[a,b;b,c], but if backwards
// eq true then makes c smallest

//debug_reduce2 := true;
debug_reduce2 := false;

function reduce22(M,backwards)

if debug_reduce2 then
  print "Reducing 2x2...";
  print M;
  print "Degrees: ",  [[Degree(M[i,j]): j in [1..2]] : i in [1..2]];
if backwards then print "(backwards)"; end if;
end if;

M_orig:=M;
I2:=IdentityMatrix(BaseRing(Parent(M)),2);
flip:=Parent(M)!Matrix([[0,1],[1,0]]);
U:=Parent(M)!I2;

a,b,_,c:=Explode(Eltseq(M));

D:=b*b-a*c;

if D eq 0 then
if debug_reduce2 then
  print "D = 0";
  print "a,b,c = ",a,b,c;
end if;

if b eq 0 then
if a eq 0 then 
   if backwards then  return Matrix([[c,0],[0,0]]),flip; 
   else               return M,I2; 
   end if;
end if;
if c eq 0 then 
   if backwards then  return M,I2;
   else               return Matrix([[0,0],[0,a]]),flip; 
   end if;
end if;
end if; // b eq 0

if M[1,1] eq 0 then
  _,P,_:=SmithForm(Matrix([[M[2,2]],[-M[1,2]]]));
else
  _,P,_:=SmithForm(Matrix([[-M[1,2]],[M[1,1]]]));
end if;
U*:=P^(-1);
SwapColumns(~U,1,2);
//"starting matrix multiplication...";
M:=Transpose(U)*M*U;
//"...done";
if backwards then 
    SwapColumns(~U,1,2);
    SwapColumns(~M,1,2);
    SwapRows(~M,1,2);
    assert M[1,2] eq 0 and M[1,1] eq 0;
else
    assert M[1,2] eq 0 and M[2,2] eq 0;
end if;
return M,U;                // a=b=0

end if; // D eq 0

Dsquare,d:=IsSquare(D);
if Dsquare then // make c=0
if debug_reduce2 then
print "D is a square";  //  print D," = d^2 where d = ",d;
end if;

if M[1,1] eq 0 then 
 SwapColumns(~M,1,2);
 SwapRows(~M,1,2);
// M:=flip*M*flip; 
 U:=flip;
else
 if M[2,2] ne 0 then
  V:=P^(-1) where _,P,_:=SmithForm(Matrix([[b+d],[-a]]));
//"starting matrix multiplication...";
//Parent(U);Parent(V);Parent(M);
  M:=Transpose(V)*M*V;
  U*:=V;
//"...done";
  assert M[1,1] eq 0;
 SwapColumns(~M,1,2);
 SwapRows(~M,1,2);
 SwapColumns(~U,1,2);
//  M:=flip*M*flip; U*:=flip;
  assert M[2,2] eq 0;
 end if;  //  c neq 0
end if;   //  a eq 0

// Now c=0; we reduce a mod b: (note b ne 0 since D ne 0)
assert M[2,2] eq 0;
q:=M[1,1] div (2*M[1,2]);
temp:=q*M[2,2];
M[1,1]+:=q*(temp-2*M[1,2]);
M[1,2]-:=temp; M[2,1]:=M[1,2];
U[1,1]-:=q*U[1,2];
U[2,1]-:=q*U[2,2];
// V:=Parent(U)!Matrix([[1,0],[-q,1]]);
// M:=Transpose(V)*M*V;
// U*:=V;
assert (M[2,2] eq 0) and (Degree(M[1,1]) lt Degree(M[1,2]));
if debug_reduce2 then
  print "reduce22 returning";
end if;
if backwards then return flip*M*flip,U*flip; // c=0
else              return M,U;                // a=0
end if;

end if; // D square

// Now general case where D ne 0 and D non-square...

if debug_reduce2 then
print "D is not a square";
end if;

while Degree(M[1,2]) ge Degree(M[1,1])
or    Degree(M[1,2]) ge Degree(M[2,2])
do

if Degree(M[1,2]) ge Degree(M[1,1]) then
//"starting div...";
q := M[1,2] div M[1,1];
//"...done";
// V:=Matrix([[1,-q],[0,1]]);
// M:=Transpose(V)*M*V; 
// U*:=V;
temp:=q*M[1,1];
M[2,2]+:=q*(temp-2*M[1,2]);
M[1,2]-:=temp; M[2,1]:=M[1,2];
U[1,2]-:=q*U[1,1];
U[2,2]-:=q*U[2,1];
end if;

if debug_reduce2 then
  print "Degrees: ",  [[Degree(M[i,j]): j in [1..2]] : i in [1..2]];
end if;

if Degree(M[1,2]) ge Degree(M[2,2]) then
//"starting div...";
q := M[1,2] div M[2,2];
//"...done";
// V:=Matrix([[1,0],[-q,1]]);
// M:=Transpose(V)*M*V; 
// U*:=V;
temp:=q*M[2,2];
M[1,1]+:=q*(temp-2*M[1,2]);
M[1,2]-:=temp; M[2,1]:=M[1,2];
U[1,1]-:=q*U[1,2];
U[2,1]-:=q*U[2,2];
end if;

if debug_reduce2 then
  print "Degrees: ",  [[Degree(M[i,j]): j in [1..2]] : i in [1..2]];
end if;
end while;

// Now b has degree less than both a and c, but we may need to flip a,c
if (Degree(M[1,1]) lt Degree(M[2,2])) eq backwards then
 SwapColumns(~M,1,2);
 SwapRows(~M,1,2);
 SwapColumns(~U,1,2);
// M:=flip*M*flip; U*:=flip;
end if;

if debug_reduce2 then
  print "reduce22 returning ";
  print "Degrees: ",  [[Degree(M[i,j]): j in [1..2]] : i in [1..2]];
  assert M eq Transpose(U)*M_orig*U;
if backwards then
assert Degree(M[1,2]) lt Degree(M[2,2]) and Degree(M[2,2]) le Degree(M[1,1]);
  else
assert Degree(M[1,2]) lt Degree(M[1,1]) and Degree(M[1,1]) le Degree(M[2,2]);
end if;

end if;
return M,U;
end function; // reduce22

//////////////////////////////////////////////////////////////////////
//
// Reduction of 3x3 symmetric polynomial matrices (after Gauss)
//
//////////////////////////////////////////////////////////////////////

//debug_reduce3:=true;
debug_reduce3:=false;

function reduce33(M)
if debug_reduce3 then
print "Reducing matrix"; //,M;
  print "Degrees: ",  [[Degree(M[i,j]): j in [1..3]] : i in [1..3]];
end if;

M_orig:=M;
I3:=IdentityMatrix(BaseRing(Parent(M)),3);
U:=Parent(M)!I3;

D:=Determinant(M);
if D eq 0 then
print "reduce33 not implemented for singular matrices!";
return M,I3;
end if;
DegD:=Degree(D);

//A1    := Submatrix(M,1,1,2,2);
//A3star: =Submatrix(Adjoint(M),2,2,2,2);
while 3*Degree(M[1,1]) gt DegD 
//or 3*Degree(Determinant(Submatrix(M,1,1,2,2))) gt 2*DegD
or 3*Degree(M[1,1]*M[2,2]-M[1,2]^2)  gt 2*DegD
do

_,V:=reduce22(Submatrix(M,1,1,2,2),false);
V:=DirectSum(V,Matrix([[BaseRing(V)!1]]));
//"starting matrix multiplication...";
M:=SymmetricMatrix([
	     M[1,1]*V[1,1]^2 + 2*M[1,2]*V[1,1]*V[2,1] + M[2,2]*V[2,1]^2,
             M[1,1]*V[1,1]*V[1,2] + (V[1,1]*V[2,2]+V[1,2]*V[2,1])*M[1,2] +
                    M[2,2]*V[2,1]*V[2,2],
             M[1,1]*V[1,2]^2 + 2*M[1,2]*V[1,2]*V[2,2] + M[2,2]*V[2,2]^2,
             M[1,3]*V[1,1] + M[2,3]*V[2,1],
             M[1,3]*V[1,2] + M[2,3]*V[2,2],
             M[3,3]]);
//M:=Transpose(V)*M*V;
U*:=V;
//"...done";

if debug_reduce3 then
  print "After Step B, degrees are: ",  
  [[Degree(M[i,j]): j in [1..3]] : i in [1..3]];
end if;

M2:=SymmetricMatrix([M[1,1]*M[3,3]-M[1,3]^2,
                     M[1,2]*M[3,1]-M[1,1]*M[3,2],
                     M[1,1]*M[2,2]-M[1,2]^2]);
_,V:=reduce22(M2,true);
detV:=V[1,1]*V[2,2]-V[1,2]*V[2,1];
V:=Matrix([[V[2,2],-V[2,1]],[-V[1,2],V[1,1]]]); // Adjoint(Transpose(V)));
//"starting matrix multiplication...";
M:=SymmetricMatrix([
detV^2*      M[1,1],
detV*        (M[1,2]*V[1,1] + M[1,3]*V[2,1]),
	     M[2,2]*V[1,1]^2 + 2*M[2,3]*V[1,1]*V[2,1] + M[3,3]*V[2,1]^2,
detV*        (M[1,2]*V[1,2] + M[1,3]*V[2,2]),
             M[2,2]*V[1,1]*V[1,2] + (V[1,1]*V[2,2]+V[1,2]*V[2,1])*M[2,3] +
                    M[3,3]*V[2,1]*V[2,2],
             M[2,2]*V[1,2]^2 + 2*M[2,3]*V[1,2]*V[2,2] + M[3,3]*V[2,2]^2]);
V:=DirectSum(Matrix([[detV]]),V);
//M:=Transpose(V)*M*V;
U*:=V;
//"...done";

if debug_reduce3 then
  print "After Step A, degrees are: ",  
  [[Degree(M[i,j]): j in [1..3]] : i in [1..3]];
end if;

end while;;

if debug_reduce3 then
  print "At end of pre-reduction, degrees are: ",  
  [[Degree(M[i,j]): j in [1..3]] : i in [1..3]];
d1:=Degree(M[1,1]);
d2:=Degree(Determinant(Submatrix(M,1,1,2,2)));
print "Degrees of leading minors are ",d1,d2,DegD;
assert  3*d1 le DegD;
assert  3*d2 le 2*DegD;
end if;

if M[1,1] eq 0 then 
if debug_reduce3 then
print "reduce33 exiting having made (1,1) entry 0";
end if;
assert Transpose(U)*M_orig*U eq M;
return M,U; 
end if;

q1:=M[1,2] div M[1,1];
q2:=M[1,3] div M[1,1];
V:=Parent(U)!Matrix([[1,-q1,-q2],[0,1,0],[0,0,1]]);
//"starting matrix multiplication...";
M:=Transpose(V)*M*V;
U*:=V;
//"...done";

if debug_reduce3 then
  print "After penultimate reduction, degrees are: ",  
  [[Degree(M[i,j]): j in [1..3]] : i in [1..3]];
d1:=Degree(M[1,1]);
d2:=Degree(Determinant(Submatrix(M,1,1,2,2)));
print "Degrees of leading minors are ",d1,d2,DegD;
assert  3*d1 le DegD;
assert  3*d2 le 2*DegD;
end if;

if M[2,2] eq 0 then 
if debug_reduce3 then
print "reduce33 exiting having made (2,2) entry 0";
end if;
assert Transpose(U)*M_orig*U eq M;
return M,U; 
end if;

// Now reduce the bottom RH 2x2 matrix
_,V:=reduce22(Submatrix(M,2,2,2,2),false);
V:=DirectSum(Matrix([[BaseRing(V)!1]]),V);
//"starting matrix multiplication...";
M:=Transpose(V)*M*V;
U*:=V;
//"...done";

if debug_reduce3 then
  print "After ultimate reduction, degrees are: ",  
  [[Degree(M[i,j]): j in [1..3]] : i in [1..3]];
d1:=Degree(M[1,1]);
d2:=Degree(Determinant(Submatrix(M,1,1,2,2)));
print "Degrees of leading minors are ",d1,d2,DegD;
assert  3*d1 le DegD;
assert  3*d2 le 2*DegD;
end if;

assert Transpose(U)*M_orig*U eq M;
return M,U;

end function; // reduce33

// symmetrix square representation
function rho3(U)
return Matrix([[a^2,2*a*b,b^2],[a*c,a*d+b*c,b*d],[c^2,2*c*d,d^2]])
 where a,b,c,d:=Explode(Eltseq(U));
end function;

//////////////////////////////////////////////////////////////////////
//
// Function to solve a conic given a 3x3 symmetric matrix
//
// returns flag,C,U,fac,sol where
//
// flag is false if there is no solution
//               or (TEMPORARY) if recursion is needed; in this case
//               C=U'*A*U/fac is diagonal & constant
// if flag is true, sol is a solution and again fac*C=U'*A*U where
//               C is 
//
//////////////////////////////////////////////////////////////////////

function sol33(A)

FT:=Parent(A[1,1]);
//"In sol33() with A = ",A," over ",FT;

if Type(FT) eq FldRat or Type(FT) eq RngInt then

P2<X,Y,Z>:=ProjectivePlane(Q);
C0:=Curve(P2,mat2form(A));
_,C:=IsConic(C0);
if not HasRationalPoint(C) then return false,_,_,_,_; end if;
Pl:=RationalPoint(C);
xl,yl,zl:=Explode(Eltseq(Pl));
dl:=Lcm(Denominator(xl),Denominator(yl));
xl*:=dl; yl*:=dl; zl*:=dl;
return true,I,I,1,Matrix(3,1,[xl,yl,zl]) where I:=IdentityMatrix(Q,3);

else if Type(FT) eq FldFin then

P2<X,Y,Z>:=ProjectivePlane(FT);
C0:=Curve(P2,mat2form(A));
_,C:=IsConic(C0);
if not HasRationalPoint(C) then return false,_,_,_,_; end if;
Pl:=Matrix(3,1,Eltseq(RationalPoint(C)));
return true,I,I,1,Pl where I:=IdentityMatrix(FT,3);
end if;
end if;

F:=BaseRing(FT);
dA:=Degree(Determinant(A));
flag,B,U,fac:= minim33(A);
if not flag then print "--not soluble"; return false,_,_,_,_; end if;
print "A=",A," successfully minimised";
"Degree of determinant was ",dA;
//print " Det(U) = ",Determinant(U);
assert fac*B eq U*A*Transpose(U);
print "Minimal model = ",B;
dB:=Degree(Determinant(B));
"Degree of determinant is now",dB;

if B[1,1] eq 0 or B[2,2] eq 0 then
C:=B;U:=Transpose(U);
else
 C,V:=reduce33(B);
 assert C eq Transpose(V)*B*V;
 U:=Transpose(U)*V;
 assert fac*C eq Transpose(U)*A*U;
end if;

if C[1,1] eq 0
then
else
if C[2,2] eq 0 
then
V:=Parent(U)!Matrix([[0,1,0],[1,0,0],[0,0,1]]);
C:=V*C*V;
U*:=V;
else
if C[3,3] eq 0
then
V:=Parent(U)!Matrix([[0,0,1],[0,1,0],[1,0,0]]);
C:=V*C*V;
U*:=V;
else

    print "Now C = ",C;
    print "Need to use recursion to complete!";
// NB At this point we DO NOT USE the diagonal matrix C=U'AU over the
// base field at all!  But we DO use the matrix U which has the
// property that U'AU is constant (up to a scalar factor).  The fact
// that this constant is diagonal also irrelevant!  We only need that
// U'AU is constant, for then from *any* solution to *any*
// specialization of A will give a generic solution to A, provided only
// that the corresponding specialization of U is nonsingular

// Find a good specialization:

t0:=F!-1;
repeat
if IsFinite(F) then
t0:=Random(F);
else
t0+:=1;
end if;
print "Trying specialization at ",t0;
U0:=Specialize(U,t0);
until Determinant(U0) ne 0;
print "t0 = ",t0," is good: solving specialization at ",t0," recursively...";

// Solve the specialization recursively:

A0:=Specialize(A,t0);
if Type(Parent(A0[1,1])) eq FldFunRat then
// clear denominators and scale to polynomials:
g:=Lcm([Denominator(a) : a in Eltseq(A0)]);
A0:=Matrix(3,3,[Numerator(g*a) : a in Eltseq(A0)]);
end if;

time flag,C0,V0,fac0,sol0:= $$(A0);
if not flag then return false,_,_,_,_; end if;

// recover solution to original
assert (Transpose(sol0)*A0*sol0)[1,1] eq 0;
print "found solution ",sol0," to specialized conic";
U0inv:=Parent(U)!Adjoint(U0); // scaled inverse -- entries are in polynomial ring!
sol:=U*U0inv*(Parent(ColumnSubmatrix(U,1,1))!sol0);
print sol," is a solution to current conic";

// move the solution to [1,0,0]:
_,V,_:=SmithForm(sol);
V:=V^(-1);
C:=Transpose(V)*A*V;
U:=V; fac :=1;

end if;
end if;
end if;

assert  C[1,1] eq 0;
print "One solution found, matrix transformed to have 0 in (1,1) position";

// The following formula is from Denis Simon's "Sur la parametrization
// des solutions des equations quadratiques", Lemme 2.1.  An
// equivalent formula can be found in JEC's undergraduate lecture
// notes on "Rational Points on Curves".

V:=Matrix([[C[2,2],2*C[2,3],C[3,3]],
           [-2*C[1,2],-2*C[1,3],0],
           [0,-2*C[1,2],-2*C[1,3]]]);
DetC:=Determinant(C);
C:=Transpose(V)*C*V;
U*:=V;
C:=divmat(C,-4*DetC);
fac*:=(-4*DetC);
assert fac*C eq Transpose(U)*A*U;
print " normalized model = ",C;
//print " U = ",U;
//print " Det(U) = ",Determinant(U);

// Now reduce the parametrizing quadratics (whose coefficients are
// given by the rows of U):
M2:=Matrix([[U[1,1],U[1,2]/2],[U[1,2]/2,U[3,3]]]);
//"About to reduce M2 "; //,M2;
_,U2:=reduce22(M2,false);
//"done";
//"Reduced version is ",Transpose(U2)*M2*U2;
V:=rho3(U2);
print "Det(V)=",Determinant(V);
C:=Transpose(V)*C*V;
U*:=V;

sol:=ColumnSubmatrix(U,1,1);

// Now sol is a solution

g:=Gcd([sol[i,1] : i in [1,2,3]]);
//"gcd = ",g;
sol:=divmat(sol,g);
if Type(F) eq FldFin then
return true,C,U,fac,sol;
end if;

sol*:=Lcm([1] cat [Denominator(c) : c in Coefficients(sol[1,1])]);
sol*:=Lcm([1] cat [Denominator(c) : c in Coefficients(sol[2,1])]);
sol*:=Lcm([1] cat [Denominator(c) : c in Coefficients(sol[3,1])]);
g := Gcd([Numerator(c) : c in &cat([Coefficients(sol[i,1]):i in [1,2,3]])]);
sol:=Matrix([[sol[i,1] div g] : i in [1,2,3]]);

return true,C,U,fac,sol;

end function; // sol33

// Test function given base field F and degree bound:

function test33(F,b)
     flag:=false; count:=0; maxtries:=1000;
repeat
repeat A:=rand33(F,b); 
       dA:=Degree(Determinant(A));
until Determinant(A) ne 0;
print "*******************************";
count+:=1;
flag,B,U,fac:= minim33(A);
if not flag then print "--not soluble #",count; end if;
until flag or count gt maxtries;
if not flag 
then print "Giving up after ",maxtries," attempts"; 
     return false; 
end if;
print "A=",A," successfully minimised";
"Degree of determinant is ",dA;
assert fac*B eq U*A*Transpose(U);
//print "Minimal model = ",B;
dB:=Degree(Determinant(B));
"Degree of determinant is ",dB;

return sol33(B);

C,V:=reduce33(B);
"Reduced model = ",C;
dC:=Degree(Determinant(C));
"Degree of determinant is ",dC;
assert C eq Transpose(V)*B*V;
U:=Transpose(U)*V;
assert fac*C eq Transpose(U)*A*U;
return C,U,fac;

end function; //test33


/////////////////////////////////////////////////////////////////
// Mark van Hoeij's examples
/////////////////////////////////////////////////////////////////

Q1<t1>:=FunctionField(Q);
R2<t2>:=PolynomialRing(Q1);

/////////////////////////////////////////////////////////////////
//procedure example1()
function example1()
/////////////////////////////////////////////////////////////////
a := 1;
b := 2*t2^2+ 2*t1*t2-t1^2;
c := -3*t2^4-4*t1*t2^3  + 8*t1^2*t2^2 + 16*t1^3*t2 - 48*t1^4;
M0:=DiagonalMatrix([a,b,c]);
M:=M0;
time flag,C,U,fac,sol:=sol33(M);
assert flag;
"One solution (after reduction, before Q-scaling) is ",sol;
//"C = ",C;
//"U = ",U;
//"fac = ",fac;
c:=&cat&cat[[Coefficients(PolynomialRing(Q)!c) 
 : c in Coefficients(sol[i,1])] : i in [1,2,3]];
d:=Lcm([1] cat [Denominator(ci):ci in c]);
g:=Gcd([Integers()!(d*ci) : ci in c]);
sol*:=(d/g);
"Scaled solution: ", sol;
Transpose(sol)*M0*sol;

//Mark's solutions:
msol:=[t2^3+t1*t2^2 + 4*t1^2* t2 - 4*t1^3 , t2^2 - 4*t1^2 , t2];
sol2:=Matrix([[m] : m in msol]);
"Mark's solution 1: ", sol2;
msol:=[ t2^3 + 2*t1^2 *t2 + 8*t1^3 , t2^2 + 2*t1 *t2 -4*t1^2 , t2+t1];
sol2:=Matrix([[m] : m in msol]);
"Mark's solution 2: ", sol2;

return sol;
//end procedure;
end function;

/////////////////////////////////////////////////////////////////
//procedure example2()
function example2()
/////////////////////////////////////////////////////////////////
a := t1^2+1;
b := -(t1^2+1)*t2^2 + (4*t1^2+4)*t2-1;
c := (2*t1^3-10*t1^2+2*t1-9)*t2^4 - (6*t1^3 + 6*t1-2)*t2^3+
     (t1^4-8*t1^3-2*t1^2-6*t1-2)*t2^2 - (4*t1^4+2*t1^2-2*t1-2)*t2 - 1;
M0:=DiagonalMatrix([a,b,c]);
M:=M0;
"Original diagonal matrix over Q(t1,t2) is ",M;

if false then
//if true then

time flag,A,U:=sol33(M);
l:=Lcm([1] cat [Denominator(Q1!A[i,i]) : i in [1,2,3]]);
a,b,c:=Explode([PolynomialRing(Q)!(l*Q1!A[i,i]) : i in [1,2,3]]);

l:=Lcm([1] cat [Denominator(co) : co in Coefficients(a) cat Coefficients(b) cat Coefficients(c)]);
a*:=l;
b*:=l;
c*:=l;

V:=IdentityMatrix(Parent(a),3);
while Degree(Gcd(a,b)) gt 0 or Degree(Gcd(b,c)) gt 0 or Degree(Gcd(a,c)) gt 0 
do
g:=Gcd(a,b);
if Degree(g) gt 0
then a div:=g; b div:=g; c*:=g;
V*:=DiagonalMatrix([1,1,g]);
end if;
g:=Gcd(b,c);
if Degree(g) gt 0
then b div:=g; c div:=g; a*:=g;
V*:=DiagonalMatrix([g,1,1]);
end if;
g:=Gcd(a,c);
if Degree(g) gt 0
then a div:=g; c div:=g; b*:=g;
V*:=DiagonalMatrix([1,g,1]);
end if;
end while;
l:=Lcm([1] cat [Denominator(co) : co in Coefficients(a) cat Coefficients(b) cat Coefficients(c)]);
a*:=l;
b*:=l;
c*:=l;
M:=DiagonalMatrix([a,b,c]);
"After first round, new diagonal matrix over Q(x) is ",M;
time flag,_,_,_,sol:=sol33(M);
assert flag;
"One solution (in new coords, before scaling) is ",sol;


c:=&cat&cat[[Coefficients(PolynomialRing(Q)!c) 
 : c in Coefficients(sol[i,1])] : i in [1,2,3]];
d:=Lcm([1] cat [Denominator(ci):ci in c]);
g:=Gcd([Integers()!(d*ci) : ci in c]);
sol*:=(d/g);
"Scaled solution: ", sol;

sol:=U*(Parent(U)!V)*Matrix([[R2!sol[1,1]],[R2!sol[2,1]],[R2!sol[3,1]]]);

g:=Gcd([PolynomialRing(Q)!co : co in &cat[Coefficients(sol[i,1]) 
   : i in [1,2,3]]]);
sol:=Matrix([[sol[i,1] div g] : i in [1,2,3]]);

else

time flag,A,U,fac,sol:=sol33(M);
c:=&cat&cat[[Coefficients(PolynomialRing(Q)!c) 
 : c in Coefficients(sol[i,1])] : i in [1,2,3]];
d:=Lcm([1] cat [Denominator(ci):ci in c]);
g:=Gcd([Integers()!(d*ci) : ci in c]);
sol*:=(d/g);

//sol:=U*(Parent(U)!V)*Matrix([[R2!sol[1,1]],[R2!sol[2,1]],[R2!sol[3,1]]]);

g:=Gcd([PolynomialRing(Q)!co : co in &cat[Coefficients(sol[i,1]) 
   : i in [1,2,3]]]);
sol:=Matrix([[sol[i,1] div g] : i in [1,2,3]]);
"Scaled solution: ", sol;

end if;  // if false

"One solution (in original coords) is ",sol;

assert (Transpose(sol)*M0*sol)[1,1] eq 0;
return sol;
end function;
//end procedure;

