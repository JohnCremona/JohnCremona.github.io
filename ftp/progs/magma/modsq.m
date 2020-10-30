freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//          Maps for Qp^*/(Qp^*)^2 for p=infty,2 or odd primes        //
//                           John Cremona                             //
//                                                                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// Last change: Sun May  5 16:50:43 BST 2002

// A couple of utility functions

function ValUn(a)
     //     p:=UniformizingElement(Parent(a));
     p:=Parent(a).1;
     v:=Valuation(a);
     u:=a / (p^v);
     return v,u;
end function;

function getnonsq(p)
// p should be an odd prime!
// A deterministic function to return a non-square mod p
     if p mod 4 eq 3 then return -1; end if;
     if p mod 8 eq 5 then return 2; end if;
// that leaves p mod 8 eq 1:
     ans:=3;
     while IsSquare(GF(p)!ans) do ans+:=1; end while;
     return ans;
end function;

// the main function

intrinsic Qpchar(p::RngIntElt) -> Map, Map
{Given a prime p or 0, returns two maps between 
   Q_p^*/(Q_p^*)^2 and VectorSpace(GF(2),d)
   where d=1,2 or 3 for p=0,odd or 2.}
 require IsZero(p) or IsPrime(p) : "argument must be a prime or 0";
     if p eq 0 then 
         Rstar:={!x in RealField() | x ne 0 !};
         GF21:=VectorSpace(GF(2),1);
         Rchar:=map<Rstar-> GF21 | 
                    x:-> GF21![x gt 0 select 0 else 1]>;
         Rchar_inv:=map<GF21->Rstar|x:->x eq GF21![0] select 1 else -1>;
     return Rchar,Rchar_inv; 
     end if;

     Qpstar:={!x in pAdicField(p) | x ne 0 !};

     if p eq 2 then 
     function char4(x) 
          return Valuation((x-1)/2) gt 0 select 0 else 1; 
     end function;
     function char8(x) 
          return Valuation((x^2-1)/8) gt 0 select 0 else 1; 
     end function;
     GF23:=VectorSpace(GF(2),3);
     return map<Qpstar->GF23|
            x:-> GF23![v mod 2, char4(u), char8(u)] 
                 where v,u:=ValUn(x)>,
            pmap<GF23->Qpstar | 
                  {<v, 2^Integers()!i*(-1)^Integers()!j*5^Integers()!k
                          where i,j,k:=Explode(Eltseq(v))> : v in GF23}>;
     end if;

     unsq:=getnonsq(p);
     GF22:=VectorSpace(GF(2),2);
     return map<Qpstar->GF22 | 
            x:-> GF22![v mod 2, IsSquare(u) select 0 else 1] 
                 where v,u:=ValUn(x)>,
            pmap<GF22->Qpstar | {<v,p^Integers()!i*unsq^Integers()!j
                          where i,j:=Explode(Eltseq(v))> : v in GF22}>;
end intrinsic;
