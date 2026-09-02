import Fable610ScaleTwoAlignedEleventhFaceScratch

/-! # Literal twelfth aligned face row for normalized `(6,10)` scale two

This compact layer consumes exactly the next unused Keller coefficient,
degree `3`.  It deliberately does not invent the expected weight-`30`
defect: no multiplier identity for that defect is exposed upstream yet.
All earlier chamber, divisor, and root packets can be threaded through the
generic preservation theorem below without unpacking or reselecting any
witness.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

/-- The literal degree-`3` coefficient of the `(6,10)` Keller Jacobian.
Its antidiagonal is `(0,4),(1,3),(2,2),(3,1),(4,0)` before taking the
`y`-derivative. -/
def alignedTwelfthJacobianRow610 {K : Type*} [CommRing K]
    (p q : K[X][Y]) : K[X] :=
  (p.coeff 3).derivative * q.coeff 1 +
      (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
      (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
      (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
    ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
      (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
      (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
      p.coeff 1 * (q.coeff 3).derivative)

/-- Exact next unused row.  No face equation or earlier defect is needed to
extract it; those data are therefore preserved rather than normalized away. -/
theorem alignedTwelfthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    alignedTwelfthJacobianRow610 p q = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 3) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (3 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by
    decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff
  simp only [alignedTwelfthJacobianRow610]
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC2, hC3, hC4]
  linear_combination hcoeff

/-- Normalized source-facing degree-`3` packet.  The Jacobian constant is
the original Keller witness, and no new polynomial witness is introduced. -/
theorem normalized610ScaleTwo_alignedTwelfthFace_literalPacket
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ j : K, j ≠ 0 ∧
      bivariateJacobian p q = Polynomial.C (Polynomial.C j) ∧
      alignedTwelfthJacobianRow610 p q = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact ⟨j, hj, hjac,
    alignedTwelfthCoefficientJacobianRow_610 hp hq hjac⟩

/-- Definitionally preserves an arbitrary earlier residual packet while
attaching the new literal row.  In particular callers may instantiate `R`
with the full eleventh square chamber, nonsquare chamber, chamber dichotomy,
or root packet: every existential witness and every alternative is retained
verbatim. -/
theorem normalized610ScaleTwo_alignedTwelfthFace_preserves
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]} {R : Prop}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hR : R) :
    R ∧
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       ∃ j : K, j ≠ 0 ∧
         bivariateJacobian p q = Polynomial.C (Polynomial.C j) ∧
         alignedTwelfthJacobianRow610 p q = 0) := by
  exact ⟨hR,
    normalized610ScaleTwo_alignedTwelfthFace_literalPacket
      hsource haligned⟩

end Max11DegreeRoutes
