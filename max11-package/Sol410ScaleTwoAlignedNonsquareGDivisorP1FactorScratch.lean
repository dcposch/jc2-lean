import Sol410ScaleTwoAlignedNonsquareGDivisorLowerThirdScratch

/-! # The ninth defect forces `H ∣ p₁` on the `(4,10)` divisor limb

After cancellation of the literal common `H¹²`, the ninth defect restricts
at either simple root of `H` to a nonzero scalar times `p₁³`.  This gives
the full quadratic divisor without any transverse-degree assumption.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section P1FactorAlgebra410

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 8000000 in
/-- The exact ninth row forces the next source coefficient to contain `H`. -/
theorem alignedFinal_gDivisor_p1Factor410
    (H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 g1 r : K[X])
    (κ κ3 κ5 κ7 : K)
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hp3 : p3 = H ^ 2 * g1)
    (hp2 : p2 = H * r)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ = 0)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM5 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ = 0)
    (hM6 : alignedSixthDefect410 H p0 p1 p2 p3 q4 q5 q6 q7 κ =
      Polynomial.C κ5 * H ^ 9)
    (hM7 : alignedSeventhDefect410 H p0 p1 p2 p3 q3 q4 q5 q6 q7 κ = 0)
    (hM8 : alignedEighthDefect410 H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ7 * H ^ 12)
    (hM9 : alignedNinthDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ = 0) :
    ∃ s : K[X], p1 = H * s := by
  let R9 : K[X] :=
    (983040 : K[X]) * p0 ^ 2 * g1 * H ^ 2 -
      (1048576 : K[X]) * q1 * H +
      (1966080 : K[X]) * p0 * p1 * r * H +
      (327680 : K[X]) * p1 ^ 3 -
      (491520 : K[X]) * p0 * p1 * g1 ^ 2 * H ^ 2 -
      (491520 : K[X]) * p0 * r ^ 2 * g1 * H ^ 2 -
      (491520 : K[X]) * p1 ^ 2 * r * g1 * H -
      (163840 : K[X]) * p1 * r ^ 3 * H +
      (245760 : K[X]) * p0 * r * g1 ^ 3 * H ^ 3 +
      (122880 : K[X]) * p1 ^ 2 * g1 ^ 3 * H ^ 2 +
      (368640 : K[X]) * p1 * r ^ 2 * g1 ^ 2 * H ^ 2 +
      (61440 : K[X]) * r ^ 4 * g1 * H ^ 2 -
      (30720 : K[X]) * p0 * g1 ^ 5 * H ^ 4 -
      (153600 : K[X]) * p1 * r * g1 ^ 4 * H ^ 3 -
      (102400 : K[X]) * r ^ 3 * g1 ^ 3 * H ^ 3 +
      (17920 : K[X]) * p1 * g1 ^ 6 * H ^ 4 +
      (53760 : K[X]) * r ^ 2 * g1 ^ 5 * H ^ 4 -
      (11520 : K[X]) * r * g1 ^ 7 * H ^ 5 +
      (880 : K[X]) * g1 ^ 9 * H ^ 6 +
      Polynomial.C κ * ((262144 : K[X]) * p0 * p1 * H) -
      Polynomial.C κ7 * ((4 : K[X]) * g1 * H ^ 2) -
      Polynomial.C κ5 * ((512 : K[X]) * p1 * H) -
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * g1 * H ^ 2 +
        (6144 : K[X]) * p1 * r * H -
        (1536 : K[X]) * p1 * g1 ^ 2 * H ^ 2 -
        (1536 : K[X]) * r ^ 2 * g1 * H ^ 2 +
        (768 : K[X]) * r * g1 ^ 3 * H ^ 3 -
        (96 : K[X]) * g1 ^ 5 * H ^ 4)
  have hM9raw := hM9
  simp only [alignedNinthDefect410] at hM9raw
  rw [hM8, hM7, hM6, hM5, hM4, hM2, hp3, hp2] at hM9raw
  have hR9 : R9 = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hH)
    dsimp only [R9]
    linear_combination hM9raw
  have hsimple : ∀ x : K, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq hx
  have hroot : ∀ x : K, H.eval x = 0 → p1.eval x = 0 := by
    intro x hx
    have hrow := congrArg (fun w : K[X] => w.eval x) hR9
    dsimp only [R9] at hrow
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat] at hrow
    rw [hx] at hrow
    norm_num at hrow
    exact hrow
  exact dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hroot

end P1FactorAlgebra410

/-- Source-facing `p₁` divisor on the same `g,f,g₁,r` witnesses. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorP1Factor
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H g f g1 r : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hg : g = H * g1)
    (hp3deep :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = H ^ 2 * g1)
    (hp2deep :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 2 = H * r)
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    ∃ s : K[X],
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧ p.coeff 1 = H * s := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ3, κ5, κ7, _κ9, _κ11, _g, _f, _hp3, hM2, hM4,
      hM5, hM6, hM7, hM8, hM9, _hM10, _hM11, _hM12, _hgf,
      _hblock⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  obtain ⟨s, hs⟩ := alignedFinal_gDivisor_p1Factor410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
      (q.coeff 5) (q.coeff 6) (q.coeff 7) g1 r κ κ3 κ5 κ7
      hsource.1 hsource.2.1 hnsq hp3deep hp2deep hM2 hM4 hM5 hM6 hM7
      hM8 hM9
  exact ⟨s, hg, hp3deep, hp2deep, hf, hs⟩

#print axioms alignedFinal_gDivisor_p1Factor410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorP1Factor

end Max11DegreeRoutes
