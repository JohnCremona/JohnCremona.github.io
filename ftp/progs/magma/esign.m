// Sign of functional equation for an elliptic curve over Q
//
// Taken partly from Odile Lecacheux's GP code, partly translated by
// JEC from the pari C code in elliptic.c from pari-2.1.3
//
// For the theory, see
//
// Halberstadt, Emmanuel. Signes locaux des courbes elliptiques en 2 et 3.
// (French) [Local root numbers of elliptic curves for $p=2$ or $3$]
// C. R. Acad. Sci. Paris Sér. I Math. 326 (1998), no. 9, 1047--1052.
//

// utility function for converting Kodaira codes to the Pari coding

function PariKodairaCode(Kod)
     case Kod:
when KodairaSymbol("I0"): return 1;
when KodairaSymbol("II"): return 2;
when KodairaSymbol("III"): return 3;
when KodairaSymbol("IV"): return 4;
when KodairaSymbol("I0*"): return -1;
when KodairaSymbol("II*"): return -2;
when KodairaSymbol("III*"): return -3;
when KodairaSymbol("IV*"): return -4;
else
n:=0; while true do n+:=1;
if Kod eq KodairaSymbol("I" cat IntegerToString(n)) 
then return n+4; end if;
if Kod eq KodairaSymbol("I" cat IntegerToString(n) cat "*") 
then return -n-4; end if;
end while;
end case;
end function;

// LOCAL ROOT NUMBERS, D'APRES HALBERSTADT halberst@math.jussieu.fr 

// translated by JEC from the pari C code in elliptic.c from pari-2.1.3

//  p = 2 or 3 for the neron function

function neron(e, p)
  nv:=LocalInformation(e,p); // <p,val(disc),val(cond),c_p,Kod>
  // Convert to Pari's numerical coding for ease of translation below
  kod:=PariKodairaCode(nv[5]);
  c4,c6:=Explode(cInvariants(e));
  d:=Discriminant(e);
  v4:=Valuation(c4,p);
  v6:=Valuation(c6,p);
  vd:=Valuation(d,p);
  if p gt 3 then return 0; end if; // should not occur
  if p eq 3 then
      if Abs(kod) gt 4 then return 1; end if;
 case kod:
  when  -1,1:
     return IsOdd(v4) select 2 else 1;
  when  -3,3:
    return (2*v6 gt vd+3) select 2 else 1;
  when  -4,2:
    return case<vd mod 6 | 4: 3,  5: 4, 
                           default: v6 mod 3 eq 1 select 2 else 1>;
  else
    return case<vd mod 6 | 0:2, 1:3, default: 1>;
  end case;

  else // p=2

   if kod gt 4 then return 1; end if;
 case kod:
   when 1: return v6 gt 0 select 2 else 1;
   when 2: return vd eq 4 select 1 else 
                  vd eq 7 select 3 else 
                  v4 eq 4 select 2 else 4;
   when 3: return case<vd| 6: 3,  8: 4,  9:  5,
	                   default:  v4 eq 5 select 2 else 1>;
	  when 4: return v4 gt 4 select 2 else 1;
	  when -1: return case<vd| 9: 2, 10: 4,
                                   default:  v4 gt 4 select 3 else 1>;
	  when -2: return case<vd| 12: 2,  14: 3, default: 1>;
	  when -3: return case<vd| 12: 2, 14: 3, 15: 4, default: 1>;
	  when -4: return v6 eq 7 select 2 else 1;
	  when -5: return (v6 eq 7 or v4 eq 6) select 2 else 1;
	  when -6: return case<vd| 12: 2,  13: 3,  
                                   default: v4 eq 6 select 2 else 1>;
	  when -7: return (vd eq 12 or v4 eq 6) select 2 else 1;
	  else return v4 eq 6 select 2 else 1;
end case;
end if;
end function;

function pValuation(n,p)
     return e,(n div p^e) where e is Valuation(n,p);
end function;

function LocalRootNumber2(e)
  if not IsMinimalModel(e) then e:=MinimalModel(e); end if;
  n2:=neron(e,2); 
  nv:=LocalInformation(e,2); // <p,val(disc),val(cond),c_p,Kod>
  // Convert to Pari's numerical coding for ease of translation below
  kod:=PariKodairaCode(nv[5]);
     //     print nv,kod;
  a1,a2,a3,a4,a6:=Explode(ChangeUniverse(aInvariants(e),Integers()));
  c4,c6:=Explode(ChangeUniverse(cInvariants(e),Integers()));

  if c4 eq 0 then v4:=12; u:=0;
  else v4,u:=pValuation(c4,2); u:=u mod 64;
  end if;

  if c6 eq 0 then v6:=12; v:=0;
  else v6,v:=pValuation(c6,2); v:=v mod 64;
  end if;

  d1:=tmp mod 64 where _,tmp:=pValuation(Integers()!Discriminant(e),2);
  x1:=u+v+v;

  if kod ge 5 then
    return IsOdd(a2+a3) select 1 else -1;
  end if;

  if kod lt -9 then 
    return n2 eq 2 select -KroneckerSymbol(-1,v) else -1;
  end if;

  case kod:
    when 1: return 1;
    when 2:
    case n2:
	when 1:
	case v4:
	    when 4: return KroneckerSymbol(-1,u);
	    when 5: return 1;
	    else return -1;
	    end case;
	when 2: return (v6 eq 7) select 1 else -1;
	when 3: return (v mod 8 eq 5 or (u*v) mod 8 eq 5) select 1 else -1;
        when 4: if (v4 gt 5) then return KroneckerSymbol(-1,v); end if;
	        return (v4 eq 5) select -KroneckerSymbol(-1,u) else -1;
    end case;
    when 3:
    case n2:
	when 1: return -KroneckerSymbol(2,u*v);
	when 2: return -KroneckerSymbol(2,v);
	when 3: y1:=(u-(c6 div 32)) mod 16;
	  return (y1 eq 7 or y1 eq 11) select 1 else -1;
	when 4: return (v mod 8 eq 3 or (2*u+v) mod 8 eq 7) select 1 else -1;
	when 5: return v6 eq 8 select KroneckerSymbol(2,x1) 
                               else KroneckerSymbol(-2,u);
    end case;
    when -1:
    case n2:
	when 1: return -KroneckerSymbol(2,x1);
	when 2: return (v mod 8 eq 7) or (x1 mod 32 eq 11) select 1 else -1;
	when 3: return v4 eq 6 select 1 else -1;
        when 4: if (v4 gt 6) then return KroneckerSymbol(-1,v); end if;
	        return v4 eq 6 select -KroneckerSymbol(-1,u*v) else -1;
    end case;
    when -2: return n2 eq 1 select KroneckerSymbol(-2,v) 
                            else KroneckerSymbol(-1,v);
    when -3:
    case n2:
        when 1: y1:=(u-2*v) mod 64; if (y1 lt 0) then y1+:=64; end if;
	  return (y1 eq 3) or (y1 eq 19) select 1 else -1;
	when 2: return KroneckerSymbol(2*KroneckerSymbol(-1,u),v);
	when 3: return -KroneckerSymbol(-1,u)*KroneckerSymbol(-2*KroneckerSymbol(-1,u),u*v);
	when 4: return v6 eq 11 select KroneckerSymbol(-2,x1) else -KroneckerSymbol(-2,u);
	end case;
    when -5:
      if (n2 eq 1) then return x1 mod 32 eq 23 select 1 else -1;
      else return -KroneckerSymbol(2,2*u+v);
      end if;
    when -6:
    case n2:
	when 1: return 1;
	when 2: return v6 eq 10 select 1 else -1;
	when 3: return (u mod 16 eq 11) or ((u+4*v) mod 16 eq 3) select 1 else -1;
	end case;
    when -7:
      if (n2 eq 1) then return 1;
      else
        y1:= (u+(c6 div 256)) mod 16;
	if (v6 eq 10) then return (y1 eq 9) or (y1 eq 13) select 1 else -1;
	else return (y1 eq 9) or (y1 eq 5) select 1 else -1;
	end if;
      end if;
    when -8: return n2 eq 2 select KroneckerSymbol(-1,v*d1) else -1;
    when -9: return n2 eq 2 select -KroneckerSymbol(-1,d1) else -1;
    else return -1;
  end case;
end function;

function LocalRootNumber3(e)
  if not IsMinimalModel(e) then e:=MinimalModel(e); end if;
  n2:=neron(e,3); 
  nv:=LocalInformation(e,3); // <p,val(disc),val(cond),c_p,Kod>
  // Convert to Pari's numerical coding for ease of translation below
  kod:=PariKodairaCode(nv[5]);
  c4,c6:=Explode(ChangeUniverse(cInvariants(e),Integers()));

  if c4 eq 0 then v4:=12; u:=0;
  else v4,u:=pValuation(c4,3); u:=u mod 81;
  end if;

  if c6 eq 0 then v:=0;
  else _,v:=pValuation(c6,3); v:=v mod 81;
  end if;

  d1:=tmp mod 81 where _,tmp:=pValuation(Integers()!Discriminant(e),3);

  r6:=v mod 9; K4:=KroneckerSymbol(u,3); K6:=KroneckerSymbol(v,3);
  if (kod gt 4) then return K6; end if;
  case kod:
    when 1, 3, -3: return 1;
    when 2:
    case n2:
	when 1: return (r6 eq 4 or r6 gt 6) select 1 else -1;
	when 2: return -K4*K6;
	when 3: return 1;
	when 4: return -K6;
    end case;
    when 4:
    case n2:
	when 1: return K6*KroneckerSymbol(d1,3);
	when 2: return -K4;
	when 3: return -K6;
    end case;
    when -2: return n2 eq 2 select 1 else K6;
    when -4:
    case n2:
	when 1:
	  if (v4 eq 4) then 
            return (r6 eq 4 or r6 eq 8) select 1 else -1;
	  else 
            return (r6 eq 1 or r6 eq 2) select 1 else -1;
          end if;
	when 2: return -K6;
	when 3: return (r6 eq 2 or r6 eq 7) select 1 else -1;
	when 4: return K6;
    end case;
    else return -1;
end case;
end function;

intrinsic LocalRootNumber(e::CrvEll,p::RngIntElt) -> RngIntElt
{Given E, an elliptic curve over Q, and a prime number p, returns +1 or -1, 
being the "local root number"  of E at p.}
    require Type(BaseRing(e)) eq FldRat :
        "Universe of argument 1 must be defined over the rationals";
    require IsPrime(p) or p eq 0: "Argument 2 must be 0 or a prime.";
if p eq 0 then return -1; end if;  // local factor at infinite prime
if not IsMinimalModel(e) then e:=MinimalModel(e); end if;
if p eq 2 then return LocalRootNumber2(e); end if;
if p eq 3 then return LocalRootNumber3(e); end if;
if Valuation(Conductor(e),p) eq 1 then 
 return -KroneckerSymbol(-Integers()!cInvariants(e)[2],p);
end if;
if Valuation(jInvariant(e),p) lt 0 then 
  return KroneckerSymbol(-1,p); 
end if;
ep:=12 div Gcd(12,Valuation(Discriminant(e),p));
z:=ep eq 4 select 2 else IsEven(ep) select 1 else 3;
return KroneckerSymbol(-z,p);
end intrinsic;

intrinsic GlobalRootNumber(e::CrvEll) -> RngIntElt
{Given E, an elliptic curve over Q, returns +1 or -1, being the "global root number" 
or sign of the functional equation of L(E,s).}
    require Type(BaseRing(e)) eq FldRat :
        "Universe of argument must be defined over the rationals";
     if not IsMinimalModel(e) then e:=MinimalModel(e); end if;
     return (-1) * &*[LocalRootNumber(e,p) : p in BadPrimes(e)];
end intrinsic;

