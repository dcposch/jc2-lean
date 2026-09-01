import Sol410ScaleTwoAlignedNonsquareGDivisorEleventhAllocationScratch

/-! # The `(4,10)` twelfth row after the second quadratic descent -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

def alignedTwelfthDeepLeft410
    (H s r g1 f : K[X]) : K[X] :=
  (3200 : K[X]) *
      ((143 : K[X]) * H ^ 3 * g1 ^ 6 -
        (572 : K[X]) * H ^ 2 * r * g1 ^ 4 +
        (528 : K[X]) * H * r ^ 2 * g1 ^ 2 - (64 : K[X]) * r ^ 3) *
      f ^ 3 +
    (51200 : K[X]) * H * s * g1 *
      ((187 : K[X]) * H ^ 2 * g1 ^ 4 -
        (664 : K[X]) * H * r * g1 ^ 2 + (432 : K[X]) * r ^ 2) * f ^ 2 +
    (314572800 : K[X]) * H * s ^ 2 * r ^ 2 * f +
    (209715200 : K[X]) * H ^ 2 * s ^ 3 * r * g1

def alignedTwelfthDeepRight410
    (H p0 s r g1 f : K[X]) (κ3 κ7 κ11 : K) : K[X] :=
  -(334233600 : K[X]) * H * s ^ 2 * r * f ^ 2 -
    (183500800 : K[X]) * H ^ 2 * s ^ 3 * g1 * f +
    (78643200 : K[X]) * p0 * r ^ 2 * f ^ 2 +
    (314572800 : K[X]) * H * p0 * s * r * g1 * f -
    (104857600 : K[X]) * H ^ 2 * s ^ 4 +
    (1258291200 : K[X]) * H * p0 * s ^ 2 * r -
    Polynomial.C κ3 * ((245760 : K[X]) * r ^ 2 * f ^ 2) -
    Polynomial.C κ3 * ((983040 : K[X]) * H * s * r * g1 * f) -
    Polynomial.C κ3 * ((3932160 : K[X]) * H * s ^ 2 * r) -
    (68812800 : K[X]) * H * s ^ 2 * f ^ 3 +
    (68812800 : K[X]) * p0 * r * f ^ 3 +
    (176947200 : K[X]) * H * p0 * s * g1 * f ^ 2 +
    (629145600 : K[X]) * H * p0 * s ^ 2 * f -
    (314572800 : K[X]) * p0 ^ 2 * r * f -
    (629145600 : K[X]) * H * p0 ^ 2 * s * g1 +
    Polynomial.C κ7 * ((1280 : K[X]) * r * f) +
    Polynomial.C κ7 * ((2560 : K[X]) * H * s * g1) -
    Polynomial.C κ3 * ((215040 : K[X]) * r * f ^ 3) -
    Polynomial.C κ3 * ((552960 : K[X]) * H * s * g1 * f ^ 2) -
    Polynomial.C κ3 * ((1966080 : K[X]) * H * s ^ 2 * f) +
    Polynomial.C κ3 * ((1966080 : K[X]) * p0 * r * f) +
    Polynomial.C κ3 * ((3932160 : K[X]) * H * p0 * s * g1) +
    (12902400 : K[X]) * p0 * f ^ 4 -
    (117964800 : K[X]) * p0 ^ 2 * f ^ 2 +
    (838860800 : K[X]) * p0 ^ 3 - Polynomial.C κ11 * (1 : K[X]) +
    Polynomial.C κ7 * ((480 : K[X]) * f ^ 2) -
    Polynomial.C κ7 * ((10240 : K[X]) * p0) -
    Polynomial.C κ3 * ((40320 : K[X]) * f ^ 4) +
    Polynomial.C κ3 * ((737280 : K[X]) * p0 * f ^ 2) -
    Polynomial.C κ3 * ((7864320 : K[X]) * p0 ^ 2)

/-- Root-leading constraint left by the twelfth row. -/
def alignedTwelfthDeepConstraint410
    (p0 r : K[X]) (κ3 κ7 κ11 : K) : K[X] :=
  Polynomial.C κ11 +
    (7864320 : K[X]) * Polynomial.C κ3 * p0 ^ 2 -
    (3932160 : K[X]) * Polynomial.C κ3 * p0 * r ^ 2 +
    (491520 : K[X]) * Polynomial.C κ3 * r ^ 4 +
    (10240 : K[X]) * Polynomial.C κ7 * p0 -
    (2560 : K[X]) * Polynomial.C κ7 * r ^ 2 -
    (838860800 : K[X]) * p0 ^ 3 +
    (629145600 : K[X]) * p0 ^ 2 * r ^ 2 -
    (157286400 : K[X]) * p0 * r ^ 4 +
    (13107200 : K[X]) * r ^ 6

set_option maxHeartbeats 8000000 in
theorem alignedNonsquareTwelfth_deepSolved_410
    (H p0 p1 p2 g f g1 r s : K[X]) (κ3 κ7 κ11 : K)
    (hH : H ≠ 0)
    (hg : g = H * g1) (hp2 : p2 = H * r) (hp1 : p1 = H * s)
    (hblk :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 -
            (572 : K[X]) * p2 * g ^ 4 +
            (528 : K[X]) * p2 ^ 2 * g ^ 2 - (64 : K[X]) * p2 ^ 3) *
            f ^ 3 +
        (51200 : K[X]) * p1 * g *
          ((187 : K[X]) * g ^ 4 - (664 : K[X]) * p2 * g ^ 2 +
            (432 : K[X]) * p2 ^ 2) * f ^ 2 +
        (314572800 : K[X]) * p1 ^ 2 * p2 ^ 2 * f +
        (209715200 : K[X]) * p1 ^ 3 * p2 * g =
      H * (-(334233600 : K[X]) * p1 ^ 2 * p2 * f ^ 2 -
        (183500800 : K[X]) * p1 ^ 3 * g * f +
        (78643200 : K[X]) * p0 * p2 ^ 2 * f ^ 2 +
        (314572800 : K[X]) * p0 * p1 * p2 * g * f -
        (104857600 : K[X]) * p1 ^ 4 +
        (1258291200 : K[X]) * p0 * p1 ^ 2 * p2 -
        Polynomial.C κ3 * ((245760 : K[X]) * p2 ^ 2 * f ^ 2) -
        Polynomial.C κ3 * ((983040 : K[X]) * p1 * p2 * g * f) -
        Polynomial.C κ3 * ((3932160 : K[X]) * p1 ^ 2 * p2) +
        H * (-(68812800 : K[X]) * p1 ^ 2 * f ^ 3 +
          (68812800 : K[X]) * p0 * p2 * f ^ 3 +
          (176947200 : K[X]) * p0 * p1 * g * f ^ 2 +
          (629145600 : K[X]) * p0 * p1 ^ 2 * f -
          (314572800 : K[X]) * p0 ^ 2 * p2 * f -
          (629145600 : K[X]) * p0 ^ 2 * p1 * g +
          Polynomial.C κ7 * ((1280 : K[X]) * p2 * f) +
          Polynomial.C κ7 * ((2560 : K[X]) * p1 * g) -
          Polynomial.C κ3 * ((215040 : K[X]) * p2 * f ^ 3) -
          Polynomial.C κ3 * ((552960 : K[X]) * p1 * g * f ^ 2) -
          Polynomial.C κ3 * ((1966080 : K[X]) * p1 ^ 2 * f) +
          Polynomial.C κ3 * ((1966080 : K[X]) * p0 * p2 * f) +
          Polynomial.C κ3 * ((3932160 : K[X]) * p0 * p1 * g) +
          H * ((12902400 : K[X]) * p0 * f ^ 4 -
            (117964800 : K[X]) * p0 ^ 2 * f ^ 2 +
            (838860800 : K[X]) * p0 ^ 3 -
            Polynomial.C κ11 * ((1 : K[X])) +
            Polynomial.C κ7 * ((480 : K[X]) * f ^ 2) -
            Polynomial.C κ7 * ((10240 : K[X]) * p0) -
            Polynomial.C κ3 * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C κ3 * ((737280 : K[X]) * p0 * f ^ 2) -
            Polynomial.C κ3 * ((7864320 : K[X]) * p0 ^ 2))))) :
    alignedTwelfthDeepLeft410 H s r g1 f =
      alignedTwelfthDeepRight410 H p0 s r g1 f κ3 κ7 κ11 := by
  rw [hg, hp2, hp1] at hblk
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  simp only [alignedTwelfthDeepLeft410, alignedTwelfthDeepRight410]
  linear_combination hblk

theorem alignedNonsquareTwelfth_deepRootConstraint_410
    (H p0 s r g1 f : K[X]) (κ3 κ7 κ11 x : K)
    (hquot : alignedTwelfthDeepLeft410 H s r g1 f =
      alignedTwelfthDeepRight410 H p0 s r g1 f κ3 κ7 κ11)
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r)
    (hx : H.eval x = 0) :
    (alignedTwelfthDeepConstraint410 p0 r κ3 κ7 κ11).eval x = 0 := by
  have hfroot : f.eval x = -(4 : K) * r.eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) hf
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hx, zero_mul] at hev
    linear_combination hev
  have hev := congrArg (fun w : K[X] => w.eval x) hquot
  simp only [alignedTwelfthDeepLeft410, alignedTwelfthDeepRight410,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hev
  rw [hx, hfroot] at hev
  norm_num at hev
  simp only [alignedTwelfthDeepConstraint410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_ofNat]
  linear_combination hev

theorem alignedNonsquareTwelfth_deepConstraintDivisor_410
    [IsAlgClosed K]
    (H p0 s r g1 f : K[X]) (κ3 κ7 κ11 : K)
    (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hquot : alignedTwelfthDeepLeft410 H s r g1 f =
      alignedTwelfthDeepRight410 H p0 s r g1 f κ3 κ7 κ11)
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r) :
    H ∣ alignedTwelfthDeepConstraint410 p0 r κ3 κ7 κ11 := by
  have hsimple : ∀ x : K, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq hx
  apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
  intro x hx
  exact alignedNonsquareTwelfth_deepRootConstraint_410
    H p0 s r g1 f κ3 κ7 κ11 x hquot hf hx

section Source410

variable [IsAlgClosed K]

theorem normalized410ScaleTwo_alignedNonsquare_gDivisorTwelfthDeep
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
    ∃ (κ3 κ7 κ11 : K) (s l d : K[X]),
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧ p.coeff 1 = H * s ∧
        g * f + (8 : K[X]) * p.coeff 1 = H * l ∧
        alignedTwelfthDeepConstraint410 (p.coeff 0) r κ3 κ7 κ11 = H * d := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨s, l, _hg, _hp3, _hp2, _hf, hs, hl⟩ :=
    normalized410ScaleTwo_alignedNonsquare_gDivisorComplement
      hsource hnsq haligned hg hp3deep hp2deep hf
  obtain ⟨_κ, κ3, _κ5, κ7, _κ9, κ11, g0, f0, hp30, _hM2, _hM4,
      _hM5, _hM6, _hM7, _hM8, _hM9, _hM10, _hM11, _hM12, hgf0,
      hblock12⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  have hp3external : p.coeff 3 = H * g := by
    calc
      p.coeff 3 = H ^ 2 * g1 := hp3deep
      _ = H * (H * g1) := by ring
      _ = H * g := by rw [hg]
  have hg0 : g0 = g := by
    apply mul_left_cancel₀ hsource.1
    calc
      H * g0 = p.coeff 3 := hp30.symm
      _ = H * g := hp3external
  have hgfExternal : g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f := by
    rw [hg, hp2deep, hf]
    ring
  have hf0 : f0 = f := by
    apply mul_left_cancel₀ hsource.1
    calc
      H * f0 = g0 ^ 2 - (4 : K[X]) * p.coeff 2 := hgf0.symm
      _ = g ^ 2 - (4 : K[X]) * p.coeff 2 := by rw [hg0]
      _ = H * f := hgfExternal
  rw [hg0, hf0] at hblock12
  have hquot := alignedNonsquareTwelfth_deepSolved_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) g f g1 r s κ3 κ7 κ11
      hsource.1 hg hp2deep hs hblock12
  obtain ⟨d, hd⟩ := alignedNonsquareTwelfth_deepConstraintDivisor_410
    H (p.coeff 0) s r g1 f κ3 κ7 κ11 hsource.2.1 hnsq hquot hf
  exact ⟨κ3, κ7, κ11, s, l, d, hg, hp3deep, hp2deep, hf, hs, hl, hd⟩

end Source410

#print axioms alignedNonsquareTwelfth_deepSolved_410
#print axioms alignedNonsquareTwelfth_deepConstraintDivisor_410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorTwelfthDeep

end Max11DegreeRoutes
