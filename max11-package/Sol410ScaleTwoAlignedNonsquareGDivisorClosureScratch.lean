import Sol410ScaleTwoAlignedNonsquareGDivisorTwelfthDeepScratch

/-! # Closure of the aligned `(4,10)` `H ∣ g` limb

After the ninth row has forced `p₁ = Hs`, its same exact defect forces
`q₁ = Ht₁`.  The untouched degree-zero Keller row is then divisible by the
nonconstant quadratic `H`, contradicting its nonzero constant value.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 8000000 in
/-- Once `p₁` has acquired the quadratic factor, the same ninth defect forces
the last coefficient used by the terminal Keller row to acquire it as well. -/
theorem alignedFinal_gDivisor_q1Factor410
    [IsAlgClosed K]
    (H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 g1 r s : K[X])
    (κ κ3 κ5 κ7 : K)
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hp3 : p3 = H ^ 2 * g1)
    (hp2 : p2 = H * r) (hp1 : p1 = H * s)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ = 0)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM5 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ = 0)
    (hM6 : alignedSixthDefect410 H p0 p1 p2 p3 q4 q5 q6 q7 κ =
      Polynomial.C κ5 * H ^ 9)
    (hM7 : alignedSeventhDefect410 H p0 p1 p2 p3 q3 q4 q5 q6 q7 κ = 0)
    (hM8 : alignedEighthDefect410 H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ7 * H ^ 12)
    (hM9 : alignedNinthDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ =
      0) :
    ∃ t1 : K[X], q1 = H * t1 := by
  let Q9 : K[X] :=
    (983040 : K[X]) * p0 ^ 2 * g1 * H - (1048576 : K[X]) * q1 +
      (1966080 : K[X]) * p0 * s * r * H +
      (327680 : K[X]) * s ^ 3 * H ^ 2 -
      (491520 : K[X]) * p0 * s * g1 ^ 2 * H ^ 2 -
      (491520 : K[X]) * p0 * r ^ 2 * g1 * H -
      (491520 : K[X]) * s ^ 2 * r * g1 * H ^ 2 -
      (163840 : K[X]) * s * r ^ 3 * H +
      (245760 : K[X]) * p0 * r * g1 ^ 3 * H ^ 2 +
      (122880 : K[X]) * s ^ 2 * g1 ^ 3 * H ^ 3 +
      (368640 : K[X]) * s * r ^ 2 * g1 ^ 2 * H ^ 2 +
      (61440 : K[X]) * r ^ 4 * g1 * H -
      (30720 : K[X]) * p0 * g1 ^ 5 * H ^ 3 -
      (153600 : K[X]) * s * r * g1 ^ 4 * H ^ 3 -
      (102400 : K[X]) * r ^ 3 * g1 ^ 3 * H ^ 2 +
      (17920 : K[X]) * s * g1 ^ 6 * H ^ 4 +
      (53760 : K[X]) * r ^ 2 * g1 ^ 5 * H ^ 3 -
      (11520 : K[X]) * r * g1 ^ 7 * H ^ 4 +
      (880 : K[X]) * g1 ^ 9 * H ^ 5 +
      Polynomial.C κ * ((262144 : K[X]) * p0 * s * H) -
      Polynomial.C κ7 * ((4 : K[X]) * g1 * H) -
      Polynomial.C κ5 * ((512 : K[X]) * s * H) -
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * g1 * H +
        (6144 : K[X]) * s * r * H -
        (1536 : K[X]) * s * g1 ^ 2 * H ^ 2 -
        (1536 : K[X]) * r ^ 2 * g1 * H +
        (768 : K[X]) * r * g1 ^ 3 * H ^ 2 -
        (96 : K[X]) * g1 ^ 5 * H ^ 3)
  have hM9raw := hM9
  simp only [alignedNinthDefect410] at hM9raw
  rw [hM8, hM7, hM6, hM5, hM4, hM2, hp3, hp2, hp1] at hM9raw
  have hQ9 : Q9 = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 13 hH)
    dsimp only [Q9]
    linear_combination hM9raw
  have hsimple : ∀ x : K, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq hx
  have hroot : ∀ x : K, H.eval x = 0 → q1.eval x = 0 := by
    intro x hx
    have hev := congrArg (fun w : K[X] => w.eval x) hQ9
    dsimp only [Q9] at hev
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat] at hev
    rw [hx] at hev
    norm_num at hev
    exact hev
  exact dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hroot

section Source410

variable [IsAlgClosed K]

/-- The `H ∣ g` allocation branch is impossible on the original normalized
source.  The contradiction uses the original nonzero Keller constant and no
degree bound in `X`. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisor_false
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
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r) : False := by
  dsimp only at haligned hp3deep hp2deep
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨s, _l, _hg, _hp3, _hp2, _hf, hs, _hl⟩ :=
    normalized410ScaleTwo_alignedNonsquare_gDivisorComplement
      hsource hnsq haligned hg hp3deep hp2deep hf
  obtain ⟨κ, κ3, κ5, κ7, _κ9, _κ11, _g0, _f0, _hp30, hM2, hM4,
      hM5, hM6, hM7, hM8, hM9, _hM10, _hM11, _hM12, _hgf0,
      _hblock12⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  obtain ⟨t1, ht1⟩ := alignedFinal_gDivisor_q1Factor410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
      (q.coeff 5) (q.coeff 6) (q.coeff 7) g1 r s κ κ3 κ5 κ7
      hsource.1 hsource.2.1 hnsq hp3deep hp2deep hs hM2 hM4 hM5 hM6
      hM7 hM8 hM9
  obtain ⟨j, hj, hfinal⟩ :=
    normalized410ScaleTwo_alignedFinalKellerRow hsource haligned
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hsource.1, hsource.2.1]
    decide
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root H hdegne
  have hev := congrArg (fun w : K[X] => w.eval x) hfinal
  rw [hs, ht1] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C] at hev
  rw [hx, zero_mul] at hev
  norm_num at hev
  exact hj hev.symm

end Source410

#print axioms alignedFinal_gDivisor_q1Factor410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisor_false

end Max11DegreeRoutes
