/****************************************************
 * Reduction of intersections of two quadric surfaces
 *
 * Michael Stoll, 2002-02-26, 2002-04-23
 ****************************************************/

/****************************************************
 We associate to a pair of quadrics Q1,Q2 in four variables
 a positive definite quadratic form Q(x,y,z,w).
 
 This is done as follows. 
 The curve described by Q1 = Q2 = 0 is fixed by a subgroup
 of PGL_4 isomorphic to Z/4Z x Z/4Z, generated by matrices
 M_1 and M_2, which we can assume to have determinant 1
 (then M_1^4 = M_2^4 = I, and both matrices have eigenvalues
 1, i, -1, -i). There is a unique Hermitian form Q (up to
 scaling) that is fixed by this group.
 
 This Q is positive definite and (as a Hermitian form) 
 a covariant of <Q1,Q2> (up to scaling); in fact the unique
 (real) Hermitian covariant of <Q1,Q2>.
 
 Q defines a lattice which we can Minkowsi-reduce.
 Applying the corresponding transformations to <Q1,Q2>, we
 obtain a reduced curve.
 
 I.e., <Q1,Q2> is reduced if Q is reduced if the lattice
 defined by Q is Minkowski-reduced.
 ****************************************************/

declare verbose Q4Reduce, 3;

// Some functions to reduce 4x4 symmetric matrices w.r.t. SL(4,Z)
// in an ad-hoc manner

function em(i,j,k) // elementary matrix
  return IdentityMatrix(Integers(),4)
          + Matrix(4, [(ii eq i and jj eq j) select k else 0
                          : ii,jj in [1..4]]);
end function;

// set up a list of (monoid) generators
gs1 := [em(i,j,1) : i,j in [1..4] | i ne j];
gs2 := [em(i,j,-1) : i,j in [1..4] | i ne j];
gens1 := gs1 cat gs2;

// gens2 is the set of all words of legth at most 2
gens2 := gens1 cat [gs1[i]*gs1[j] : j in [i..#gs1], i in [1..#gs1]]
               cat [gs1[i]*gs2[j] : i,j in [1..#gs1] | i ne j]
               cat [gs2[i]*gs2[j] : j in [i..#gs2], i in [1..#gs2]];

// a measure for the size of a matrix
function siz(m)
  return Max([Abs(c) : c in Eltseq(m)]);
end function;

// red0 repeatedly applies the matrices in gens in an attempt to
// reduce the size of m
function red0(m,gens)
  s1 := siz(m);
  trans1 := IdentityMatrix(Integers(), 4);
  m1 := m;
  repeat
    s := s1;
    vprintf Q4Reduce, 3: "Size now = %o\n", s;
    ms := [Transpose(g)*m*g : g in gens];
    s1, pos := Min([siz(mm) : mm in ms]);
    trans := trans1;
    trans1 := trans*gens[pos];
    m := m1;
    m1 := ms[pos];
  until s1 ge s;
  return m, trans;
end function;

function redg1(m)
  return red0(m, gens1);
end function;

function redg2(m)
  return red0(m, gens2);
end function;

// do the same with two matrices simultaneously
function red0two(mat1, mat2, gens)
  s1 := siz(mat1) + siz(mat2);
  trans1 := IdentityMatrix(Integers(), 4);
  m1 := mat1; m2 := mat2;
  repeat
    s := s1;
    vprintf Q4Reduce, 3: "Size now = %o\n", s;
    ms := [<Transpose(g)*mat1*g, Transpose(g)*mat2*g> : g in gens];
    s1, pos := Min([siz(mm[1]) + siz(mm[2]) : mm in ms]);
    trans := trans1;
    trans1 := trans*gens[pos];
    mat1 := m1; mat2 := m2;
    m1 := ms[pos,1]; m2 := ms[pos,2];
  until s1 ge s;
  return mat1, mat2, trans;
end function;

function redg1two(m1, m2)
  return red0two(m1, m2, gens1);
end function;

function redg2two(m1, m2)
  return red0two(m1, m2, gens2);
end function;

function tr(m,i,j,k)
  return Transpose(e)*m*e
           where e := em(i,j,k);
end function;

// this attempts reduction by `completing the square' steps
function red(m)
  // m: symmetric integral 4x4 matrix
  flag := true;
  size := siz(m);
  op := IdentityMatrix(Integers(), 4);
  count := 10;
  while flag and count gt 0 do
    flag := false;
    for i := 1 to 4 do
      if m[i,i] ne 0 then
        for j := 1 to 4 do
          if i ne j then
            cof := -Round(m[i,j]/m[i,i]);
            if cof ne 0 then
              flag := true;
              m := tr(m, i,j,cof);
              op := op*em(i,j,cof);
            end if;
          end if;
        end for;
      end if;
    end for;
    newsize := siz(m);
    vprintf Q4Reduce, 3: "red: size now = %o\n", newsize;
    if newsize ge size then count -:= 1; end if;
    size := newsize;
  end while;
  return m, op;
end function;

function red2(m1,m2)
  size := Max(siz(m1), siz(m2));
  op := IdentityMatrix(Integers(), 4);
  count := 10;
  while count gt 0 do
    m1, tr := red(m1);
    m2 := Transpose(tr)*m2*tr;
    op := op*tr;
    m2, tr := red(m2);
    m1 := Transpose(tr)*m1*tr;
    op := op*tr;
    newsize := Max(siz(m1), siz(m2));
    vprintf Q4Reduce, 3: "red2: size now = %o\n", newsize;
    if newsize ge size then count -:= 1; end if;
    size := newsize;
  end while;
  return m1,m2,op;
end function;

function redm(m)
  s1 := siz(m);
  trans := IdentityMatrix(Integers(), 4);
  repeat
    s := s1;
    m, tr := red(m);
    trans := trans*tr;
    m, tr := redg2(m);
    trans := trans*tr;
    s1 := siz(m);
  until s1 ge s;
  return m, trans;
end function;

// put the various approaches together
function redmtwo(m1, m2)
  s1 := siz(m1) + siz(m2);
  trans := IdentityMatrix(Integers(), 4);
  repeat
    s := s1;
    m1, m2, tr := red2(m1, m2);
    trans := trans*tr;
    m1, m2, tr := redg2two(m1, m2);
    trans := trans*tr;
    s1 := siz(m1) + siz(m2);
  until s1 ge s;
  return m1, m2, trans;
end function;

// Write my own Kernel function, since I got a runtime error:
// Runtime error in 'Kernel': ideal min. den != 1
function Kernel4(mat)
  // find linear combination of columns that vanishes
  // so operate on rows
  V := KSpace(CoefficientRing(Parent(mat)), 4);
  rows := [V![mat[i,j] : j in [1..4]] : i in [1..4]];
  for j := 1 to 3 do
    if forall{r : r in rows | r[j] eq 0} then
      return sub<V | V![i eq j select 1 else 0 : i in [1..4]]>;
    end if;
    if rows[j,j] eq 0 then
      if forall(k){i : i in [j+1..4] | rows[i,j] eq 0} then
        return sub<V | V![(i eq j) select 1 
                            else (i lt j) select -rows[i,j]
                            else 0 : i in [1..4]]>;
      end if;
      // k := Rep({i : i in [j+1..4] | rows[i,j] ne 0});
      r := rows[k]; rows[k] := rows[j]; rows[j] := r;
    end if;
    rows[j] *:= 1/rows[j,j];
    for i := 1 to 4 do
      if i ne j then
        rows[i] -:= rows[i,j]*rows[j];
      end if;
    end for;
  end for;
  // now matrix has form [[1,0,0,a], [0,1,0,b], [0,0,1,c], [0,0,0,d]]
  // check that d = 0
  if rows[4,4] ne 0 then
    return sub<V | >;
  else
    return sub<V | V![-rows[1,4], -rows[2,4], -rows[3,4], 1]>;
  end if;
end function;

function Q2mat(Q)
  P4 := Parent(Q);
  return Matrix([[MonomialCoefficient(Q, P4.i*P4.j)*(i eq j select 1 else 1/2)
                    : j in [1..4]] : i in [1..4]]);
end function;

function mat2Q(mat, P4)
  return &+[P4.i*mat[i,j]*P4.j : i,j in [1..4]];
end function;

intrinsic Covariant(Q1::RngMPolElt, Q2::RngMPolElt) -> AlgMatElt
{Compute the covariant of the pair of quadratic forms Q1, Q2.}
  P4 := Parent(Q1);
  R := CoefficientRing(P4);
  require Parent(Q2) eq P4: "Both forms must live in the same ring.";
  require Rank(P4) eq 4: "Forms must be in four variables.";
  require forall{m : m in Monomials(Q1) | TotalDegree(m) eq 2}
           and forall{m : m in Monomials(Q2) | TotalDegree(m) eq 2}:
          "Forms must be quadratic forms.";
  vprintf Q4Reduce, 1: "Covariant(%o, %o)\n", Q1, Q2;
  return Covariant(Q2mat(Q1), Q2mat(Q2));
end intrinsic;

intrinsic Covariant(mat1::AlgMatElt, mat2::AlgMatElt) -> AlgMatElt
{Compute the covariant of a pair of symmetric 4x4 matrices.}
  R := CoefficientRing(mat1);
  require R cmpeq CoefficientRing(mat2):
          "Matrices must live over the same ring.";
  require NumberOfRows(mat1) eq 4 and NumberOfColumns(mat1) eq 4
           and NumberOfRows(mat2) eq 4 and NumberOfColumns(mat2) eq 4:
          "Matrices must be 4x4 square matrices.";
  require Transpose(mat1) eq mat1 and Transpose(mat2) eq mat2:
          "Matrices must be symmetric.";
  vprintf Q4Reduce, 1: "Covariant of pair of matrices:\n%o\n%o\n", mat1, mat2;
  // Get size of entries
  size := Log(Max([Abs(c) : c in Eltseq(mat1) cat Eltseq(mat2) | c ne 0]))
           / Log(10);
  _, oldprec := HasAttribute(FldPr, "Precision");
  _, oldoprec := HasAttribute(FldPr, "OutputPrecision");
  AssertAttribute(FldPr, "Precision", Max(Floor(size) + 30, oldprec));
  AssertAttribute(FldPr, "OutputPrecision", Max(10, oldoprec));
  // First step: find singular quadrics in pencil and their vertices
  R := FieldOfFractions(R);
  P2 := PolynomialRing(R, 2);
  P1 := PolynomialRing(R);
  det := Determinant(P2.1*ChangeRing(mat1, P2) + P2.2*ChangeRing(mat2, P2));
  fdet := Factorisation(det);
  vprintf Q4Reduce, 3: "  Factorisation of determinant is\n %o\n", fdet;
  require forall{p : p in fdet | p[2] eq 1}: "Pencil is singular.";
  fdet := [p[1] : p in fdet];
  vert := [];
  sing := [MatrixAlgebra(ComplexField(), 4) | ];
  for f in fdet do
    if f eq P2.2 then
      ker := Kernel(mat1);
      assert Dimension(ker) eq 1;
      Append(~sing, mat1);
      Append(~vert, Eltseq(Basis(ker)[1]));
    elif TotalDegree(f) eq 1 then
      mat := MonomialCoefficient(f, P2.2)*mat1
              - MonomialCoefficient(f, P2.1)*mat2;
      ker := Kernel(mat);
      assert Dimension(ker) eq 1;
      Append(~sing, mat);
      Append(~vert, Eltseq(Basis(ker)[1]));
    else
      f1 := Evaluate(f, [P1.1, 1]);
      K := ext<R | f1>;
      assert Evaluate(f1, K.1) eq 0;
      mat := K.1*ChangeRing(mat1, K) + ChangeRing(mat2, K);
      ker := Kernel4(mat);
      assert Dimension(ker) eq 1;
      v := Eltseq(Basis(ker)[1]);
      homs := [hom<K -> ComplexField() | r[1]> 
                : r in Roots(f1, ComplexField())];
      sing cat:= [Matrix([[h(mat[i,j]) : j in [1..4]] : i in [1..4]])
                   : h in homs];
      vert cat:= [[h(c) : c in v] : h in homs];
    end if;
  end for;
  vprintf Q4Reduce, 2: 
          "  Vertices of singular quadrics in pencil:\n%o\n", vert;
  // Now set up matrix that transforms vertices to standard position
  PC4<[X]> := PolynomialRing(ComplexField(), 4);
  trans1 := Matrix(vert);
  trans2 := trans1^-1;
  singt := [trans1*s*Transpose(trans1) : s in sing];
  singt1 := [DiagonalMatrix([i eq j select 0 else singt[i,j,j]
                             : j in [1..4]])
              : i in [1..4]];
  check := func<mat | &+[Norm(mat[i,j]) : i,j in [1..4]] lt 1.0e-20>;
  assert forall{i : i in [1..4] | check(singt[i] - singt1[i])};
  vprintf Q4Reduce, 2: "  Transformed singular quadrics:\n%o\n",
                       [&+[s[i,i]*PC4.i^2 : i in [1..4]] : s in singt1];
  // Normalise the last three singular quadrics to start with x1^2
  three := [[singt1[i,j,j]/singt1[i,1,1] : j in [1..4]] : i in [2..4]];
  // Compute covariant
  covt := [1] cat [Sqrt(Modulus(&*[three[i,j+1] : i in [1..3] | i ne j]))
                    : j in [1..3]];
  vprintf Q4Reduce, 2: "  Transformed covariant:\n%o\n",
                       &+[covt[i]*PC4.i^2 : i in [1..4]];
  // Transform back
  conj := func<mat | Matrix([[ComplexConjugate(mat[i,j]) : j in [1..4]]
                               : i in [1..4]])>;
  covmat := conj(trans2)*DiagonalMatrix(covt)*Transpose(trans2);
  // Verify that matrix is real symmetric
  assert check(covmat - Transpose(covmat)) and check(covmat - conj(covmat));
  covmat := Matrix([[Real(covmat[i,j]) : j in [1..4]] : i in [1..4]]);
  covmat +:= Transpose(covmat);
  covmat *:= 1/Sqrt(&+[Norm(c) : c in Eltseq(covmat)]);
  vprintf Q4Reduce, 1: "Covariant is %o\n", 
                       &+[covmat[i,j]*PC4.i*PC4.j : i,j in [1..4]];
  AssertAttribute(FldPr, "Precision", oldprec);
  AssertAttribute(FldPr, "OutputPrecision", oldoprec);
  return ChangeRing(covmat, RealField());
end intrinsic;

intrinsic Reduce(Q1::RngMPolElt, Q2::RngMPolElt : AdHocOnly := false, NoAdHoc := false)
  -> RngMPolElt, RngMPolElt, AlgMatElt
{Computes a reduced pencil in the SL_4(Z)-equivalence class of <Q1, Q2>.}
  P4 := Parent(Q1);
  R := CoefficientRing(P4);
  require Parent(Q2) eq P4: "Both forms must live in the same ring.";
  require Rank(P4) eq 4: "Forms must be in four variables.";
  require forall{m : m in Monomials(Q1) | TotalDegree(m) eq 2}
           and forall{m : m in Monomials(Q2) | TotalDegree(m) eq 2}:
          "Forms must be quadratic forms.";
  mat1 := Q2mat(Q1);
  mat2 := Q2mat(Q2);
  if NoAdHoc then
    vprintf Q4Reduce, 1: " Not running ad-hoc reduction.\n";
  elif R cmpeq Integers() or R cmpeq Rationals() 
      and forall{c : c in Eltseq(mat1) cat Eltseq(mat2) | IsIntegral(c)}
  then
    vprintf Q4Reduce, 1: " Running ad-hoc reduction procedure...\n";
    mat1 := ChangeRing(mat1, Integers());
    mat2 := ChangeRing(mat2, Integers());
    // first run ad-hoc reduction
    mat1, mat2, trans := redmtwo(mat1, mat2);
    trans := Transpose(trans);
    Q1 := Evaluate(Q1, [&+[P4.i*trans[i,j] : i in [1..4]] : j in [1..4]]);
    Q2 := Evaluate(Q2, [&+[P4.i*trans[i,j] : i in [1..4]] : j in [1..4]]);
    vprintf Q4Reduce, 2: " Forms after ad-hoc reduction:\n Q1 = %o\n Q2 = %o\n",
                         Q1, Q2;
  else
    vprintf Q4Reduce, 1: " Matrices are non-integral ==> no ad-hoc reduction.\n";
    trans := IdentityMatrix(Integers(), 4);
  end if;
  if AdHocOnly then
    return Q1, Q2, trans;
  end if;
  // do it twice to allow for rounding errors
  for j := 1 to 2 do
    // get covariant
    Qmat := Covariant(Q1, Q2);
    // now reduce lattice
    Qred, trans1 := LLLGram(Qmat);
    Q1 := Evaluate(Q1, [&+[P4.i*trans1[i,j] : i in [1..4]] : j in [1..4]]);
    Q2 := Evaluate(Q2, [&+[P4.i*trans1[i,j] : i in [1..4]] : j in [1..4]]);
    trans := trans1*trans;
  end for;
  return Q1, Q2, trans;
end intrinsic;
