// Taken from CrvHyp/selmer.m

// Some preliminary stuff on classes mod squares in p-adic fields

// Find smallest positive integer d such that d*x is integral.
function Denom(x)
  // x::FldNumElt
  // f := AbsoluteMinimalPolynomial(x);
  // return LCM([Denominator(c) : c in Coefficients(f)]);
  den1 := LCM([Denominator(c) : c in Eltseq(x)]);
  O := Integers(Parent(x));
  x1 := O!(den1*x);
  num := GCD(den1, GCD(ChangeUniverse(Eltseq(x1), Integers())));
  return ExactQuotient(den1, num), O!(x1/num);
end function;

intrinsic MyResidueClassField(pid::RngOrdIdl) -> FldFin, Map
{ Given a prime ideal, returns the residue field Order(pid)/pid
  together with the reduction map from the ring of pid-integral
  elements in the corresponding number field to the residue field. 
    This map has an inverse.}
// Type checking on two possible argument types:

if Type(pid) eq RngOrdIdl then
  // return ResidueClassField(Order(pid), pid);
  O := Order(pid);
  K := FieldOfFractions(O);
  F, m := ResidueClassField(O, pid);
  p := Minimum(pid);
  e := ChineseRemainderTheorem(pid, ideal<O | O!p>/pid^RamificationIndex(pid),
                               O!1, O!0);
  f := function(x)
         if x eq 0 then return F!0; end if;
         v := Valuation(x, pid);
         error if v lt 0, 
               "Error in reduction modulo a prime ideal:",
                x, "is not integral with respect to", pid;
         if v gt 0 then return F!0; end if;
         den := Denom(x);
         v := Valuation(den, p);
         y := x * e^v; // y is now p-integral and = x mod pid
         den := Denom(y);
         error if den mod p eq 0,
               "Something´s wrong in MyResidueClassField in selmer.m!";
         return m(O!(den*y))/F!den;
       end function;
  return F, map< K -> F | x :-> f(x), y :-> y @@ m >;
elif Type(pid) eq RngInt then
  O := Integers();
  K := FieldOfFractions(O);
  p := Generator(pid);
  // require IsPrime(p): "The ideal must be a prime ideal.";
  F, m := ResidueClassField(O, pid);
  f := function(x)
         if x eq 0 then return F!0; end if;
         v := Valuation(x, p);
         error if v lt 0, 
               "Error in reduction modulo a prime ideal:",
                x, "is not integral with respect to", pid;
         if v gt 0 then return F!0; end if;
         return (F!Numerator(x))/F!Denominator(x);
       end function;
  return F, map< K -> F | x :-> f(x), y :-> y @@ m >;
end if;
  error if false, "Unrecognized argument in MyResidueClassField";
end intrinsic;


// We represent a p-adic field by the following data:
// + a number field K;
// + a prime ideal in O, the integers of K, lying above p.
// From these, we deduce
// + a uniformizer;
// + a homomorphism K^* -->> finite elementary abelian 2-group with
//   kernel the elements that are squares in the completion.

// Return the map  K^* -> a GF(2)-vector space 

intrinsic  MakeModSquares(K::FldNum, pid::RngOrdIdl) -> ModTupFld, Map
{ (K::FldNum, pid::prime ideal in K)
    Returns a GF(2)-vector space V and a map K^* -> V
    with kernel the elements that are squares in the completion. }
  O := Integers(K);
  p := Minimum(pid);
  e := RamificationIndex(pid, p);
  f := Degree(pid);
  _, pi := TwoElementNormal(pid);
  F, m := MyResidueClassField(pid);
  if IsOdd(p) then
    V := KSpace(GF(2), 2); // the codomain of our homomorphism
    h := map< K -> V | x :-> V![GF(2) | v, IsSquare(m(y)) select 0 else 1]
                             where y := x/(pi^v)
                             where v := Valuation(x, pid)>;
  else
    // p = 2
    
    // c is a pid-adic square and a pid-unit, but lies in all other
    // prime ideals above 2 in O. 
    c := ChineseRemainderTheorem(pid^(2*e+1), ideal<O | O!2>/pid^e, O!1, O!0);
    // Our elementary abelian 2-group K_pid^*/(K_pid^*)^2 has rank 2 + e*f.
    V := KSpace(GF(2), 2 + e*f);
    // A pid-unit is a square in K_pid iff it is a square in R.
    R := quo<O | pid^(2*e+1)>;
    // reps is a lift to O of an F_2-basis of F.
    reps := [ R!((F![ i eq j select 1 else 0 : i in [1..f] ]) @@ m)
               : j in [1..f] ];
    // A basis of pid-units modulo squares is given by
    //  [ 1 + r*pi^(2*i-1) : r in reps, i in [1..e] ] cat [ unr ] ,
    // where unr = 1 + 4*u such that the absolute trace of the image
    // of u in the residue field is non-zero. Together with pi itself,
    // we get a basis of pid-adics modulo squares.
    sc := function(y) // y in K is a pid-unit
            r := [GF(2) | ];
            // Make y integral without changing its class mod squares
            dy := Denom(y);
            if IsEven(dy) then
              y *:= c^Valuation(dy, 2);
              dy := Denom(y);
              error if IsEven(dy),
                    "Something is wrong in MakeModSquares in selmer.m!";
            end if;
            y := (dy mod 8)*O!(dy*y);
            z := (R!y)^(2^f-1); // put it into 1 + pid
            for i := 1 to e do
              // Determine contribution of (1 + ?*pi^(2*i-1))
              seq := Eltseq(m((K!O!(z - 1))/pi^(2*i-1)));
              r cat:= seq;
              for j := 1 to f do
                if seq[j] ne 0 then
                  z *:= 1 + reps[j]*(R!pi)^(2*i-1);
                end if;
              end for;
              if i lt e then
                // Determine contribution of (1 + ?*pi^i)^2
                z2 := Sqrt(m((K!O!(z - 1))/pi^(2*i)));
                z *:= (1 + (R!(z2 @@ m))*(R!pi)^i)^2;
              else
                // Determine unramified contribution
                r cat:= [AbsoluteTrace(m((K!O!(z - 1))/K!4))];
              end if;
            end for;
            return r;
          end function; 
    h := map< K -> V | x :-> V!([GF(2) | v] cat sc(x/pi^v))
                             where v := Valuation(x, pid)>;
  end if;
  return V, h;
end intrinsic;    

// This function returns a function that, given an element x of O, returns
// as a first value true or false, depending on whether x is a square in
// the completion of O at pid or not. A second value is returned when the
// first vakue is false; it indicates modulo which power of the uniformizer
// it can be recognized that x is a non-square.
intrinsic MakeIsSquare(pid::RngOrdIdl) -> UserProgram
{ Given a prime ideal in some order O, return a function that decides
  whether its argument (an element of O) is a square in the completion
  of O at pid. }
  O := Order(pid);
  p := Minimum(pid);
  e := RamificationIndex(pid, p);
  f := Degree(pid);
  _, pi := TwoElementNormal(pid);
  F, m := ResidueClassField(pid); // works OK for RngOrdIdl's
  if IsOdd(p) then
    return function(x)
             if x eq 0 then return true, _; end if;
             v := Valuation(x, pid);
             if IsEven(v) then return IsSquare(m(x/pi^v)), v+1;
             else return false, v+1;
             end if;
           end function;
  else
    // p = 2
    R := quo<O | pid^(2*e+1)>;
    K := FieldOfFractions(O);
    // c is a pid-adic square and a pid-unit, but lies in all other
    // prime ideals above 2 in O. 
    c := ChineseRemainderTheorem(pid^(2*e+1), ideal<O | O!2>/pid^e, O!1, O!0);
    return function(x)
             if x eq 0 then return true, _; end if;
             v := Valuation(x, pid);
             if IsOdd(v) then return false, v+1; end if;
             // Normalize
             y := (K!x)/pi^v;
             // Make y integral without changing its class mod squares
             dy := Denom(y);
             if IsEven(dy) then
               y *:= c^Valuation(dy, 2);
               dy := Denom(y);
               error if IsEven(dy),
                     "Something is wrong in MakeIsSquare in selmer.m!";
             end if;
             y := (dy mod 8)*O!(dy*y);
             z := (R!y)^(2^f-1); // put it into 1 + pid            
             for i := 1 to e do
               if Valuation(O!(z-1), pid) lt 2*i then
                 // There is some contribution of (1 + ?*pi^(2*i-1))
                 return false, v + 2*i;
               end if;
               z1 := (K!O!(z - 1))/pi^(2*i);
               if i lt e then
                 // Eliminate contribution of (1 + ?*pi^i)^2
                 z *:= (1 + (R!(Sqrt(m(z1)) @@ m))*(R!pi)^i)^2;
               elif AbsoluteTrace(m(z1)) ne 0 then
                 // We have an unramified non-square
                 return false, v + 2*e + 1;
               end if;
             end for;
             return true, _;
           end function;
  end if;
end intrinsic;    

intrinsic MakeIsSquare(p::RngIntElt) -> UserProgram
{ Given a prime number p, return a function that decides
  whether its argument (an integer) is a square in Z_p. }
  require IsPrime(p): "p must be a prime number";
  if p eq 2 then
    return function(x)
             if x eq 0 then return true, _; end if;
             v := Valuation(x, 2);
             if IsOdd(v) then return false, v+1; end if;
             x /:= 2^v;
             x := Numerator(x)*Denominator(x);
             if x mod 4 eq 3 then return false, v+2; end if;
             if x mod 8 eq 5 then return false, v+3; end if;
             return true, _;
           end function;
 else
   return function(x)
            if x eq 0 then return true, _; end if;
            v := Valuation(x, p);
            if IsOdd(v) then return false, v+1; end if;
            x /:= p^v;
            x := Numerator(x)*Denominator(x);
            return IsSquare(GF(p)!x), v+1;
          end function;
  end if;
end intrinsic;

intrinsic MakeIsSquare(I::RngInt) -> UserProgram
{ Given a prime ideal pZ in the integers, return a function that decides
  whether its argument (an integer) is a square in Z_p. }
  return MakeIsSquare(Generator(I));
end intrinsic;

intrinsic  MakeModSquares(K::FldNum, p::RngIntElt)  -> ModTupFld, Map
{ (K::FldNum, p::rational prime)
    Returns a GF(2)-vector space V and a map K^* -> V
    with kernel the elements that are squares in all the completions of K 
    at primes above p. } 
  Plist:=[f[1] : f in Factorization(p*Integers(K))];
  S2Fp_pairs:=[<S2Fp,lp> where S2Fp,lp:=MakeModSquares(K,P) : P in Plist];
  S2Fp,emb,proj:=DirectSum([t[1] : t in S2Fp_pairs]);
  f := function(x)
         return &+[emb[i](S2Fp_pairs[i,2](x)) : i in [1..#S2Fp_pairs]];
       end function;
  return S2Fp,f;
end intrinsic;
