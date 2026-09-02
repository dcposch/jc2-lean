import Sol610ScaleTwoAlignedFifteenthFinalRowScratch

/-! # Final Keller row on the aligned-square `(6,10)` branch

Untracked working note.  No tracked file was edited.

The scale-two discriminator splits every normalized `(6,10)` source into
the aligned face `N = 5 p₅ H² - 3 q₉ = 0` and the nonzero face `N ≠ 0`.
The nonzero face is a different first-face (its linear-root chamber is
already closed, and its multiple-root chamber is empty).  This file
opens only the aligned face, and only to consume the last unused
Jacobian coefficient on the aligned *square* branch.

## Square branch: last unused row

On `H = h₀²` the Sol aligned tower has already consumed every positive-
degree Jacobian coefficient of a normalized aligned source: Fable faces
through the degree-`4` eleventh row, the Sol twelfth degree-`3` row, the
odd weight-`65` thirteenth, and the degree-`1` aligned-square fourteenth.
The next and last unused coefficient is the degree-`0` Keller row

`p₀' q₁ - p₁ q₀' = C j`

with the original nonzero Keller constant `j`.  Unlike every higher
aligned row it is inhomogeneous, so it is not a first integral and it
clears no further defect.  Combining it with the already-landed
weight-`5`, weight-`30`, weight-`65`, and weight-`70` first integrals
gives an exhausted square packet: there is no unused Jacobian
coefficient below degree `0`.

Evaluating the last row at the unique root of the forced linear scale
`h₀` yields the boundary residual

`p₀'(a) q₁(a) - p₁(a) q₀'(a) = j`,  `j ≠ 0`,

which separates the two cross-products.  No allocation on the square
jet forces both products to vanish, so this file does **not** claim
`False` for the square chamber.

## Nonsquare branch

A nonsquare aligned branch exists:
`normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet`
together with the chamber dichotomy.  The Sol twelfth literal
degree-`3` row attaches to every aligned source, including nonsquare.
The Sol thirteenth/fourteenth/fifteenth modules are square-only (the
odd-weight clearing uses a square root of `H`).  The degree-`0` Keller
coefficient itself is chamber-free and is recorded here on the
nonsquare source as well.  The unused nonsquare rows are therefore the
degree-`2` and degree-`1` coefficients, together with the carried
eleventh residue `alignedEleventhNonsquareResidue610 = 0`.  The
nonsquare chamber is **not closed**.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000

/-! ## Chamber-free last Keller coefficient -/

section AlignedFinalKellerRow610

variable {K : Type*} [Field K] [CharZero K]

/-- Source-facing final-row packet on the exact normalized aligned
source.  The last coefficient does not use the square presentation; the
imported square predecessor supplies the higher aligned-square rows. -/
theorem normalized610ScaleTwo_alignedFinalKellerRow
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ j : K, j ≠ 0 ∧
      (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  refine ⟨j, hj, ?_⟩
  exact source610_degreeZeroJacobianRow p q j hD

end AlignedFinalKellerRow610

/-! ## Exhausted aligned-square packet -/

section AlignedSquareExhaustedPacket610

variable {K : Type*} [Field K] [CharZero K]

/-- Scale two of a square core forces the local scale to be linear. -/
theorem alignedSquare610_h0_natDegree_eq_one
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) :
    h0.natDegree = 1 := by
  have h2 : (h0 ^ 2).natDegree = 2 := by
    rw [← hHsq]
    exact hsource.2.1
  rw [natDegree_pow] at h2
  omega

/-- A degree-one polynomial over a field has a root in the ground field. -/
theorem alignedSquare610_exists_root
    (h0 : K[X]) (hdegree : h0.natDegree = 1) :
    ∃ a : K, h0.eval a = 0 := by
  obtain ⟨c, hc, d, hlinear⟩ := natDegree_eq_one.mp hdegree
  refine ⟨-d / c, ?_⟩
  rw [← hlinear]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  field_simp [hc]
  ring

set_option maxHeartbeats 16000000 in
/-- Exhausted aligned-square packet: the landed first-integral ladder of
weights `5`, `30`, `65`, and `70`, the consumed degree-`1` row, and the
last Keller coefficient.  No unused Jacobian row remains on this
branch. -/
theorem normalized610ScaleTwo_alignedSquare_exhaustedPacket
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ κ c xi nu : K,
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) =
          Polynomial.C c * H ^ 30 ∧
        localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) 0 =
          Polynomial.C xi * h0 ^ 65 ∧
        localClearedFourteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) =
          Polynomial.C nu * h0 ^ 70 ∧
        (p.coeff 1).derivative * q.coeff 1 +
            (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
          ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
            p.coeff 1 * (q.coeff 1).derivative) = 0) ∧
      ∃ j : K, j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  dsimp only at haligned ⊢
  refine ⟨?jet, ?row⟩
  · obtain ⟨κ, c, xi, hM, hthirty, hsixtyfive, hdeg1row⟩ :=
      normalized610ScaleTwo_alignedFourteenthSquareSource_610
        hsource haligned hh0 hHsq
    rcases hsource with
      ⟨_hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    have hp : p.natDegree = 6 := by
      simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
    have hq : q.natDegree = 10 := by
      simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
    have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
    have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
    obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hD : GCD369SourceXDeriv p * derivative q -
        derivative p * GCD369SourceXDeriv q =
          Polynomial.C (Polynomial.C j) := by
      simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv]
        using hjac
    obtain ⟨nu, hnu⟩ :=
      alignedSquareSource610_fourteenthClearedDefect_exists
        p q H h0 j hp hq hh0 hHsq hp6' hq10' haligned hD
    exact ⟨κ, c, xi, nu, hM, hthirty, hsixtyfive, hnu, hdeg1row⟩
  · exact normalized610ScaleTwo_alignedFinalKellerRow hsource haligned

/-- Root evaluation of the last Keller row on the aligned square
branch.  The forced linear scale has a unique root `a`, the row becomes
the inhomogeneous boundary relation `p₀'(a) q₁(a) - p₁(a) q₀'(a) = j`,
and `j ≠ 0` separates the two cross-products.  This is the precise
residual of the branch: the Jacobian tower is exhausted and no live
allocation is contradicted. -/
theorem normalized610ScaleTwo_alignedSquare_finalRow_atRoot
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a j : K),
      h0.natDegree = 1 ∧ h0.eval a = 0 ∧ j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
            (p.coeff 1).eval a *
              ((q.coeff 0).derivative).eval a = j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hdeg1 :=
    alignedSquare610_h0_natDegree_eq_one hsource hh0 hHsq
  obtain ⟨a, hroot⟩ := alignedSquare610_exists_root h0 hdeg1
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleTwo_alignedFinalKellerRow hsource haligned
  have hroweval : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
    have h := congrArg (Polynomial.eval a) hrow
    simpa only [p, q, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] using h
  refine ⟨a, j, hdeg1, hroot, hj, hrow, hroweval, ?_⟩
  intro heq
  apply hj
  have hj0 : j = 0 := by
    rw [← hroweval, heq, sub_self]
  exact hj0

end AlignedSquareExhaustedPacket610

/-! ## Nonsquare aligned branch: exists, open -/

section AlignedNonsquareStatus610

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 16000000 in
/-- Status of the aligned nonsquare chamber.  The chamber exists (the
eleventh-face packet is inhabited whenever `H` is not a polynomial
square), the chamber-free degree-`3` twelfth row and the last Keller
coefficient attach to the same source, and the unused rows on this
chamber are the degree-`2` and degree-`1` Jacobian coefficients
together with the carried eleventh residue.  No closure is claimed. -/
theorem normalized610ScaleTwo_alignedNonsquare_openPacket
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
        alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 ∧
        alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0)
            κ κ₅ κ₇ = 0) ∧
      (∃ j : K, j ≠ 0 ∧
        bivariateJacobian p q = Polynomial.C (Polynomial.C j) ∧
          alignedTwelfthJacobianRow610 p q = 0 ∧
          (p.coeff 0).derivative * q.coeff 1 -
              p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j) := by
  dsimp only at haligned ⊢
  refine ⟨?eleventh, ?rows⟩
  · obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf,
        ht1, ht2, hu, ht3, hv, _hq0, _hq1, _hq2, _hD0, _hE, _hF0, _hG,
        _hI0, _hJ, _hL0, _hO, hΛ0, hres⟩ :=
      normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf, ht1,
      ht2, hu, ht3, hv, hΛ0, hres⟩
  · rcases hsource with
      ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hp : p.natDegree = 6 := by
      simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
    have hq : q.natDegree = 10 := by
      simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
    have hD : GCD369SourceXDeriv p * derivative q -
        derivative p * GCD369SourceXDeriv q =
          Polynomial.C (Polynomial.C j) := by
      simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv]
        using hjac
    exact ⟨j, hj, hjac,
      alignedTwelfthCoefficientJacobianRow_610 hp hq hjac,
      source610_degreeZeroJacobianRow p q j hD⟩

end AlignedNonsquareStatus610

#print axioms normalized610ScaleTwo_alignedFinalKellerRow
#print axioms alignedSquare610_h0_natDegree_eq_one
#print axioms alignedSquare610_exists_root
#print axioms normalized610ScaleTwo_alignedSquare_exhaustedPacket
#print axioms normalized610ScaleTwo_alignedSquare_finalRow_atRoot
#print axioms normalized610ScaleTwo_alignedNonsquare_openPacket

end Max11DegreeRoutes
