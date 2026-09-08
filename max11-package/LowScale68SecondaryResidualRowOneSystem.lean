import LowScale68SecondaryResidualDouble

/-! # Residual row-one extraction from the literal lower system

After the cubic translation `C=A^2/3+c` and the residual translation
`D=A*B/3+d`, the second irreducible one-form of the constant-Jacobian
polynomial system is exactly the residual row plus the constant-load row.
This file is independent of `LowScale68SecondaryResidualDescent`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualRowOneSystem68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 2000000 in
/-- Linearity of the second one-form after both coordinate changes. -/
theorem cubicRowOnePolynomial68_residualSplit
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) :
    let C0 := (1 / 3 : k) • A ^ 2 + c
    let D0 := (1 / 3 : k) • (A * B) + d
    let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
    lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D0 E0) C0 D0 E0 =
      secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
    (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
      A B C0 D0 E0) C0 D0 E0 = _
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e]

set_option maxHeartbeats 3000000 in
/-- After translating `D=A*B/3+d`, every constant-load contribution to the
second one-form lies strictly below the next `3g` residual face. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        12 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have hsmall' : 2 * g < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall' hA hB hc hD he'
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 6 * n := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlD : (Ul * derivative D).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hTlE : (Tl * derivative E).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hDUl : (D * derivative Ul).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  compute_degree
  omega

/-- The residual second one-form equation extracted from the integrated
row after `C=A^2/3+c` and `D=A*B/3+d`. -/
theorem polynomialSecondaryResidualRowOne68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X])
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0) :
    secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  simpa using
    (cubicRowOnePolynomial68_residualSplit
      l alpha beta gamma delta epsilon zeta eta A B c d e).symm.trans
      hrowOne

/-- The same residual equation, read off the full constant-Jacobian
polynomial system after both coordinate reconstructions. -/
theorem integratedPolynomialLowerSystem68_residualRowOne
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E c d e : k[X])
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD : D = (1 / 3 : k) • (A * B) + d)
    (hE : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  have hrowOne := hsys.rowOne
  rw [hC0, hD, hE] at hrowOne
  exact polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta A B c d e hrowOne

#print axioms cubicRowOnePolynomial68_residualSplit
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace
#print axioms polynomialSecondaryResidualRowOne68
#print axioms integratedPolynomialLowerSystem68_residualRowOne

end SecondaryResidualRowOneSystem68

end Max11DegreeRoutes
