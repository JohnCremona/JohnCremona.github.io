intrinsic DividePoint(pt::PtEll,m::RngIntElt) -> BoolElt, PtEll
{Given an point P on an elliptic curve E and a positive integer m, returns either true,Q if P=m*Q has a solution Q in E, else false,_ .}
require m gt 0 : "Argument 2 must be a positive integer";
     E:=Curve(pt);
     if pt eq E!0 then return true,pt; end if;
     a1,a2,a3,a4,a6:=Explode(aInvariants(E));
     R:=BaseRing(E);
     Rx<X>:=FunctionField(R);
     Rxy<Y>:=PolynomialRing(Rx);
     F<y>:=quo<Rxy | Y^2+(a1*X+a3)*Y-(X^3+a2*X^2+a4*X+a6)>;
     EF:=BaseChange(E,F);
     genpt:=EF![X,y];
     genpt2:=m*genpt;
     X2:=Rx!(Rxy!genpt2[1]);
     Y2:=Rxy!genpt2[2];
     NX2:=Numerator(X2);
     DX2:=Denominator(X2);    
     NY2:=DX2^2*Y2;
     eqn1:=NX2-pt[1]*DX2;
     cY2:=Coefficients(Y2);
     ans:= [E![rx,Evaluate((pt[2]-cY2[1])/cY2[2],rx)] : rx in [re[1] : re in Roots(eqn1)]];
     if #ans gt 0 then return true,ans[1];  else return false,_; end if;
end intrinsic;
