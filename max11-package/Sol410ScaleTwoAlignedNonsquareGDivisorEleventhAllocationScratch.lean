import Sol410ScaleTwoAlignedNonsquareGDivisorEleventhDeepScratch

/-! # Two-root allocation of the deep `(4,10)` eleventh row -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial lift of the scalar companion factor from the deep eleventh
row. -/
def alignedEleventhDeepCompanionPoly410
    (p0 r : K[X]) (κ3 κ7 : K) : K[X] :=
  -(1536 : K[X]) * Polynomial.C κ3 * p0 +
    (384 : K[X]) * Polynomial.C κ3 * r ^ 2 - Polynomial.C κ7 +
    (245760 : K[X]) * p0 ^ 2 - (122880 : K[X]) * p0 * r ^ 2 +
    (15360 : K[X]) * r ^ 4

@[simp] theorem alignedEleventhDeepCompanionPoly_eval410
    (p0 r : K[X]) (κ3 κ7 x : K) :
    (alignedEleventhDeepCompanionPoly410 p0 r κ3 κ7).eval x =
      alignedEleventhRootCompanion410 (p0.eval x) (r.eval x) κ3 κ7 := by
  simp only [alignedEleventhDeepCompanionPoly410,
    alignedEleventhRootCompanion410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]

section Source410

variable [IsAlgClosed K]

/-- Allocate the new terminal/companion product across the two actual roots
of `H`.  On the terminal-divisor branch the already named quotient `l` also
acquires a second factor of `H`; both transverse orientations remain literal.
-/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorEleventhAllocation
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
    ∃ (κ3 κ7 : K) (s l : K[X]) (x y : K),
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧ p.coeff 1 = H * s ∧
        g * f + (8 : K[X]) * p.coeff 1 = H * l ∧
        x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
        let T := (2 : K[X]) * s - r * g1
        let C := alignedEleventhDeepCompanionPoly410 (p.coeff 0) r κ3 κ7
        (∃ t l1 : K[X], T = H * t ∧ l = H * l1) ∨
          (∃ c : K[X], C = H * c) ∨
          ((T.eval x = 0 ∧ C.eval x ≠ 0 ∧
              T.eval y ≠ 0 ∧ C.eval y = 0) ∨
            (T.eval x ≠ 0 ∧ C.eval x = 0 ∧
              T.eval y = 0 ∧ C.eval y ≠ 0)) := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨κ3, κ7, s, l, _hg, _hp3, _hp2, _hf, hs, hl, hquot,
      hrootSplit⟩ :=
    normalized410ScaleTwo_alignedNonsquare_gDivisorEleventhDeep
      hsource hnsq haligned hg hp3deep hp2deep hf
  have hdeg : H.natDegree = 2 := hsource.2.1
  have hsimple : ∀ z : K, H.eval z = 0 → H.derivative.eval z ≠ 0 :=
    fun z hz => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq hz
  obtain ⟨x, y, hxy, hx, hy⟩ :=
    alignedFinal_rootPair_exists410 H hdeg hsimple
  let T : K[X] := (2 : K[X]) * s - r * g1
  let C : K[X] := alignedEleventhDeepCompanionPoly410 (p.coeff 0) r κ3 κ7
  have hpx : T.eval x * C.eval x = 0 := by
    have hsplit := hrootSplit x hx
    rcases hsplit with hT | hC
    · apply mul_eq_zero.mpr (Or.inl ?_)
      simpa only [T, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat] using hT
    · apply mul_eq_zero.mpr (Or.inr ?_)
      simpa only [C, alignedEleventhDeepCompanionPoly_eval410] using hC
  have hpy : T.eval y * C.eval y = 0 := by
    have hsplit := hrootSplit y hy
    rcases hsplit with hT | hC
    · apply mul_eq_zero.mpr (Or.inl ?_)
      simpa only [T, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat] using hT
    · apply mul_eq_zero.mpr (Or.inr ?_)
      simpa only [C, alignedEleventhDeepCompanionPoly_eval410] using hC
  have halloc := alignedFinal_twoRootProduct_allocation410
    H T C hdeg hsimple x y hxy hx hy hpx hpy
  have hlexpand : l = H * g1 ^ 3 + (4 : K[X]) * T := by
    apply mul_left_cancel₀ hsource.1
    rw [← hl, hg, hs, hf]
    dsimp only [T]
    ring
  refine ⟨κ3, κ7, s, l, x, y, hg, hp3deep, hp2deep, hf, hs, hl,
    hxy, hx, hy, ?_⟩
  rcases halloc with hT | hC | htrans
  · obtain ⟨t, ht⟩ := hT
    refine Or.inl ⟨t, g1 ^ 3 + (4 : K[X]) * t, ht, ?_⟩
    rw [hlexpand, ht]
    ring
  · obtain ⟨c, hc⟩ := hC
    exact Or.inr (Or.inl ⟨c, hc⟩)
  · exact Or.inr (Or.inr htrans)

end Source410

#print axioms alignedEleventhDeepCompanionPoly_eval410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorEleventhAllocation

end Max11DegreeRoutes
