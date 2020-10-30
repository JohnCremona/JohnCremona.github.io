/****************************************************
 * Reduction of ternary cubics -- a first attempt.
 *
 * Michael Stoll, 2002-02-21
 ****************************************************/

/****************************************************
 We associate to a nonsingular ternary cubic C(x,y,z)
 a positive definite quadratic form Q(x,y,z).
 
 This is done as follows. 
 Let H(x,y,z) = det(matrix of second partial derivatives of C)
 be the Hessian of C. Then the intersection of C and H
 consists of 9 distinct points, the flexes of C.
 Three of them are real, the others come in three complex
 conjugate pairs. There are twelve lines each containing
 three of the flexes, coming in four triples of lines
 that do not meet in a flex. One of these triples has all
 three lines real, call them L_11, L_12, L_13. Another one
 has one line real, call it L_21, and two complex conjugate
 lines, call them L_22 and L_23. Then our form Q spans
 the one-dimensional intersection of the spaces spanned by
 L_11^2, L_12^2 and L_13^2, and by L_21^2 and L_22 L_23,
 respectively.
 
 This Q is positive definite and (as a Hermitian form) 
 a covariant of C (up to scaling); in fact the unique
 (real) Hermitian covariant of C.
 
 Q defines a lattice which we can Minkowski-reduce.
 Applying the corresponding transformations to C, we
 obtain a reduced curve.
 
 I.e., C is reduced if Q is reduced if the lattice
 defined by Q is Minkowski-reduced.
 ****************************************************/

declare verbose TernaryReduce, 3;

// Find real and complex flexes of a ternary cubic over Q
intrinsic Flexes(C::RngMPolElt) -> SeqEnum
{Finds the real and complex flexes of a ternary cubic over Q.}
  P := Parent(C);
  require Rank(P) eq 3 and forall{m : m in Monomials(C) | TotalDegree(m) eq 3}:
          "C must be a ternary cubic form.";
  vprintf TernaryReduce, 1: "Flexes: C = %o\n", C;
  // compute Hessian
  H := Determinant(Matrix([[Derivative(Derivative(C,i),j) : j in [1..3]]
                            : i in [1..3]]));
  vprintf TernaryReduce, 2: "  Hessian H = %o\n", H;
  I := ideal<P | C, H>;
  B := Reverse(GroebnerBasis(I));
  vprintf TernaryReduce, 3: "  GroebnerBasis =\n%o\n", B;
  require Evaluate(B[1], [0,P.2,P.3]) eq B[1]:
          "Something didn't work with the Groebner Basis.";
  fact := Factorisation(B[1]);
  flexes := [];
  P1 := PolynomialRing(CoefficientRing(P));
  PC := PolynomialRing(ComplexField());
  for pair in fact do
    require pair[2] eq 1: "C is singular.";
    f := pair[1];
    vprintf TernaryReduce, 2: "  Looking at f = %o\n", f;
    if f eq P.3 then
      pol := GCD([Evaluate(B[i], [P1.1, 1, 0]) : i in [2..#B]]);
      new := [[r[1], 1, 0] : r in Roots(pol, ComplexField())];
      vprintf TernaryReduce, 3: "  New flexes:\n%o\n", new;
      flexes cat:= new;
    else
      f := Evaluate(f, [0, P1.1, 1]);
      if #B eq 2 then
        for rt in Roots(f, ComplexField()) do
          require rt[2] eq 1: "C is singular.";
          vprintf TernaryReduce, 2: "  Looking at root %o of f.\n", rt[1];
          pol := Evaluate(B[2], [PC.1, rt[1], 0]);
          new := [[r[1], rt[1], 1] : r in Roots(pol)];
          vprintf TernaryReduce, 3: "  New flexes:\n%o\n", new;
          flexes cat:= new;
        end for;
      else
        // work generically
        if Degree(f) eq 1 then
          root := -Coefficient(f, 0);
          pol1 := GCD([Evaluate(B[i], [P1.1, root, 1]) : i in [2..#B]]);
          for rt in Roots(f, ComplexField()) do
            require rt[2] eq 1: "C is singular.";
            vprintf TernaryReduce, 2: "  Looking at root %o of f.\n", rt[1];
            new := [[r[1], rt[1], 1] : r in Roots(pol1, ComplexField())];
            vprintf TernaryReduce, 3: "  New flexes:\n%o\n", new;
            flexes cat:= new;
          end for;          
        else
          K := ext<Rationals() | f>;
          if Evaluate(f, K.1) ne 0 then
            root := Roots(f, K)[1,1];
          else
            root := K.1;
          end if;
          PK := PolynomialRing(K);
          pol1 := GCD([Evaluate(B[i], [PK.1, root, 1]) : i in [2..#B]]);
          for rt in Roots(f, ComplexField()) do
            require rt[2] eq 1: "C is singular.";
            vprintf TernaryReduce, 2: "  Looking at root %o of f.\n", rt[1];
            m := hom< K -> ComplexField() | rt[1] >;
            pol := PC![m(c) : c in Coefficients(pol1)];
            new := [[r[1], rt[1], 1] : r in Roots(pol)];
            vprintf TernaryReduce, 3: "  New flexes:\n%o\n", new;
            flexes cat:= new;
          end for;
        end if;
      end if;
    end if;
  end for;
  require #flexes eq 9: "Did not find exactly nine flexes.";
  flexes := [fl : fl in flexes | IsReal(fl[1]) and IsReal(fl[2])]
              cat [fl : fl in flexes | not IsReal(fl[1]) or not IsReal(fl[2])];
  vprintf TernaryReduce, 1: "Flexes: %o\n", flexes;
  return flexes;
end intrinsic;


// Given the flexes, find the lines
intrinsic LinesFromFlexes(flexes::SeqEnum) -> SeqEnum
{Given a sequence of nine flexes of a ternary cubic, finds the
 line through the 3 real flexes, its complementary factor, and
 the three real lines through a real and two complex flexes.}
  require #flexes eq 9: "Must have nine flexes.";
  // first find complex conjugate pairs
  freal := flexes[[1,2,3]];
  require forall{fl : fl in freal | IsReal(fl[1]) and IsReal(fl[2])
                                    and IsReal(fl[3])}:
          "First three flexes must be real.";
  fcomplex := [];
  frest := flexes[[4..9]];
  while #fcomplex lt 3 do
    new := frest[#frest];
    Append(~fcomplex, new);
    Prune(~frest);
    min, pos := Minimum([&+[Norm(ComplexConjugate(new[i])-fl[i]) : i in [1..3]]
                          : fl in frest]);
    require min lt 1.0e-6: "Flexes appear not to be complex conjugate.";
    Exclude(~frest, frest[pos]);
  end while;
  P3 := PolynomialRing(RealField(), 3);
  normalise := function(line)
                 _, pos := Maximum([Norm(a) : a in line]);
                 norm := Sqrt(&+[Norm(a) : a in line])
                           * line[pos]/Modulus(line[pos]);
                 return [a/norm : a in line];
               end function;
  line := function(pt1, pt2)
            Ker := Kernel(Matrix([[pt1[i], pt2[i]] : i in [1..3]]));
            assert Dimension(Ker) eq 1;
            line := Eltseq(Basis(Ker)[1]);
            return normalise(line);
          end function;
  lines := [line(freal[1],freal[2]),
            line(freal[2],freal[3]),
            line(freal[3],freal[1])];
  liner := normalise([&+[l[i] : l in lines] : i in [1..3]]);
  vprintf TernaryReduce, 3: "  Real line: %o\n", liner;
  linec := [[Real(a) : a in line(fl, [ComplexConjugate(c) : c in fl])]
             : fl in fcomplex];
  vprintf TernaryReduce, 3: "  Real triple of lines:\n%o\n", linec;
  linetest1 := line(fcomplex[1], fcomplex[2]);
  linetest2 := line(fcomplex[1], [ComplexConjugate(c) : c in fcomplex[2]]);
  vprintf TernaryReduce, 3:
          "  Possible complex lines:\n  %o\n  %o\n", linetest1, linetest2;
  m1 := Min(Norm(&+[linetest1[i]*fcomplex[3,i] : i in [1..3]]),
            Norm(&+[linetest1[i]*ComplexConjugate(fcomplex[3,i])
                     : i in [1..3]]));
  m2 := Min(Norm(&+[linetest2[i]*fcomplex[3,i] : i in [1..3]]),
            Norm(&+[linetest2[i]*ComplexConjugate(fcomplex[3,i])
                     : i in [1..3]]));
  require Min(m1, m2) lt 1.0e-10: "Lines do not fit.";
  vprintf TernaryReduce, 3: 
          "  Values of two possible lines at third point: %o, %o\n", m1, m2;
  linet := m1 lt m2 select linetest1 else linetest2;
  compl := Norm(linet[1])*P3.1^2 + Norm(linet[2])*P3.2^2 + Norm(linet[3])*P3.3^2
            + 2*Real(linet[1]*ComplexConjugate(linet[2]))*P3.1*P3.2
            + 2*Real(linet[1]*ComplexConjugate(linet[3]))*P3.1*P3.3
            + 2*Real(linet[2]*ComplexConjugate(linet[3]))*P3.2*P3.3;
  vprintf TernaryReduce, 3: "  Complementary factor:\n%o\n", compl;
  return [&+[liner[i]*P3.i : i in [1..3]], compl]
           cat [&+[l[i]*P3.i : i in [1..3]] : l in linec];
end intrinsic;

function orthonorm(basis)
  for i := 1 to #basis do
    s := [&+[basis[j,k]*basis[i,k] : k in [1..#basis[i]]] : j in [1..i-1]];
    if i gt 1 then
      basis[i] := [basis[i,k] - &+[s[j]*basis[j,k] : j in [1..#s]]
                    : k in [1..#basis[i]]];
    end if;
    n := Sqrt(&+[a^2 : a in basis[i]]);
    basis[i] := [a/n : a in basis[i]];
  end for;
  return basis;
end function;

// Now find the form from the lines
intrinsic CovariantFromLines(lines::[RngMPolElt]) -> RngMPolElt
{Finds the covariant positive definite Hermitian form from the
 given lines through the flexes of a ternary cubic.}
  require Rank(Universe(lines)) eq 3: "Lines must be ternary forms.";
  require #lines eq 5: "Need five forms.";
  require forall{i : i in [1..5] | 
              forall{m : m in Monomials(lines[i]) | TotalDegree(m) eq degs[i]}}
            where degs := [1, 2, 1, 1, 1]:
          "Need forms of degrees 1, 2, 1, 1, 1.";
  // look for element in space <lines[1]^2, lines[2]> that is closest to
  // <lines[3]^2, lines[4]^2, lines[5]^2>
  mons := MonomialsOfDegree(Universe(lines), 2);
  w1 := [ MonomialCoefficient(lines[1]^2, mon) : mon in mons ];
  w2 := [ MonomialCoefficient(lines[2], mon) : mon in mons ];
  // orthonormalise
  vprintf TernaryReduce, 2: "  First basis:\n  %o\n  %o\n", w1, w2;
  w := orthonorm([w1, w2]);
  vprintf TernaryReduce, 2: "  orthonormalised:\n  %o\n  %o\n", w[1], w[2];
  // basis of other space
  v1 := [ MonomialCoefficient(lines[3]^2, mon) : mon in mons ];
  v2 := [ MonomialCoefficient(lines[4]^2, mon) : mon in mons ];
  v3 := [ MonomialCoefficient(lines[5]^2, mon) : mon in mons ];
  // orthonormalise
  vprintf TernaryReduce, 2: "  Second basis:\n  %o\n  %o\n  %o\n", v1, v2, v3;
  v := orthonorm([v1, v2, v3]);
  vprintf TernaryReduce, 2: "  orthonormalised:\n  %o\n  %o\n  %o\n",
                            v[1], v[2], v[3];
  // look at cos(phi)*w[1] + sin(phi)*w[2] such that distance to <v>
  // is minimal. Leads to
  scmat := [[&+[wi[k]*vj[k] : k in [1..#mons]] : wi in w] : vj in v];
  vprintf TernaryReduce, 3: "  Scalar products matrix:\n%o\n", scmat;
  phi := 1/2*Arctan2(&+[a[1]*a[2] : a in scmat],
                     1/2*&+[a[1]^2 - a[2]^2 : a in scmat]);
  cphi := Cos(phi); sphi := Sin(phi);
  qs1 := [cphi*w[1,k] + sphi*w[2,k] : k in [1..#mons]];
  qs2 := [-sphi*w[1,k] + cphi*w[2,k] : k in [1..#mons]];
  ls1 := [cphi*a[1] + sphi*a[2] : a in scmat];
  ls2 := [-sphi*a[1] + cphi*a[2] : a in scmat];
  dist1 := 1 + &+[l^2 : l in ls1]
             - 2*&+[ls1[i]*(cphi*scmat[i,1] + sphi*scmat[i,2])
                     : i in [1..#ls1]];
  dist2 := 1 + &+[l^2 : l in ls2]
             - 2*&+[ls2[i]*(-sphi*scmat[i,1] + cphi*scmat[i,2])
                     : i in [1..#ls2]];
  if dist1 lt dist2 then
    qs := qs1; ls := ls1; dist := dist1;
  else
    qs := qs2; ls := ls2; dist := dist2;
  end if;
  vprintf TernaryReduce, 2: "  Nearest vector in first space:\n  %o\n", qs;
  vv := [&+[ls[i]*v[i,k] : i in [1..#ls]] : k in [1..#mons]];
  vprintf TernaryReduce, 3: "  Nearest vector in second space:\n  %o\n", vv;
  Q := &+[qs[i]*mons[i] : i in [1..#mons]];
  if MonomialCoefficient(Q, Parent(Q).1^2) lt 0 then Q := -Q; end if;
  return Q, dist;
end intrinsic;

intrinsic Covariant(C::RngMPolElt) -> RngMPolElt
{Computes the positive definite Hermitian covariant of a ternary cubic
 as a real quadratic form.}
  return CovariantFromLines(LinesFromFlexes(Flexes(C)));
end intrinsic;

intrinsic Reduce(C::RngMPolElt) -> RngMPolElt, AlgMatElt
{Computes a reduced form in the SL_3(Z)-equivalence class of C.}
  // get covariant
  Q := Covariant(C);
  // set up lattice
  P := Parent(Q);
  Qmat := Matrix([[(i eq j select 1 else 0.5)*MonomialCoefficient(Q, P.i*P.j)
                     : j in [1..3]] : i in [1..3]]);
  // now reduce lattice
  Qred, trans := LLLGram(Qmat);
  PC := Parent(C);
  Cred := Evaluate(C, [&+[PC.i*trans[i,j] : i in [1..3]] : j in [1..3]]);
  return Cred, trans;
end intrinsic;
