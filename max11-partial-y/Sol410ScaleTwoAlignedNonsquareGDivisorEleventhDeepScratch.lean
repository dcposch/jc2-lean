import Sol410ScaleTwoAlignedNonsquareGDivisorEleventhRootFactorScratch

/-! # The `(4,10)` eleventh row after the second quadratic descent

This is the exact quotient of the already source-backed eleventh block after
`g = H g₁`, `p₂ = H r`, and `p₁ = H s`.  No witness is reselected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Left side after cancelling the literal common `H³` from the eleventh
block on `g = H g₁`, `p₂ = H r`, `p₁ = H s`. -/
def alignedEleventhDeepLeft410
    (H s r g1 f : K[X]) : K[X] :=
  (1280 : K[X]) * g1 *
      ((39 : K[X]) * H ^ 2 * g1 ^ 4 -
        (104 : K[X]) * H * r * g1 ^ 2 + (48 : K[X]) * r ^ 2) * f ^ 3 +
    (30720 : K[X]) * s *
      ((33 : K[X]) * H ^ 2 * g1 ^ 4 -
        (72 : K[X]) * H * r * g1 ^ 2 + (16 : K[X]) * r ^ 2) * f ^ 2 +
    (3932160 : K[X]) * H ^ 2 * s ^ 2 * g1 ^ 3 * f +
    (5242880 : K[X]) * H * s ^ 3 *
      ((3 : K[X]) * H * g1 ^ 2 - (4 : K[X]) * r)

/-- Right side of the same cancelled eleventh block. -/
def alignedEleventhDeepRight410
    (H p0 s r g1 f : K[X]) (κ3 κ7 : K) : K[X] :=
  H * (((((983040 : K[X]) * p0 - Polynomial.C κ3 * (3072 : K[X])) *
          g1 ^ 2 - (2949120 : K[X]) * s ^ 2) * g1 * f ^ 2) +
      (((15728640 : K[X]) * p0 - Polynomial.C κ3 * (49152 : K[X])) *
        s * g1 ^ 2 * f) +
      (((62914560 : K[X]) * p0 - Polynomial.C κ3 * (196608 : K[X])) *
        g1 * s ^ 2)) +
    (((491520 : K[X]) * p0 - Polynomial.C κ3 * (1536 : K[X])) *
      g1 * f ^ 3) +
    (((3932160 : K[X]) * p0 - Polynomial.C κ3 * (12288 : K[X])) *
      s * f ^ 2) +
    (Polynomial.C κ3 * ((1536 : K[X]) * p0) + Polynomial.C κ7 -
      (245760 : K[X]) * p0 ^ 2) *
      ((64 : K[X]) * g1 * f + (512 : K[X]) * s)

set_option maxHeartbeats 8000000 in
/-- Exact `H³` cancellation of the source-backed eleventh block. -/
theorem alignedNonsquareEleventh_deepSolved_410
    (H p0 p1 p2 g f g1 r s : K[X]) (κ3 κ7 : K)
    (hH : H ≠ 0)
    (hg : g = H * g1) (hp2 : p2 = H * r) (hp1 : p1 = H * s)
    (hblk :
      (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
            (104 : K[X]) * p2 * g ^ 2 + (48 : K[X]) * p2 ^ 2) * f ^ 3 +
          (30720 : K[X]) * p1 *
            ((33 : K[X]) * g ^ 4 - (72 : K[X]) * p2 * g ^ 2 +
              (16 : K[X]) * p2 ^ 2) * f ^ 2 +
          (3932160 : K[X]) * p1 ^ 2 * g ^ 3 * f +
          (5242880 : K[X]) * p1 ^ 3 *
            ((3 : K[X]) * g ^ 2 - (4 : K[X]) * p2) =
        H * (((((983040 : K[X]) * p0 -
              Polynomial.C κ3 * (3072 : K[X])) * g ^ 2 -
              (2949120 : K[X]) * p1 ^ 2) * g * f ^ 2) +
          (((15728640 : K[X]) * p0 -
              Polynomial.C κ3 * (49152 : K[X])) * p1 * g ^ 2 * f) +
          (((62914560 : K[X]) * p0 -
              Polynomial.C κ3 * (196608 : K[X])) * g * p1 ^ 2) +
          H * ((((491520 : K[X]) * p0 -
                Polynomial.C κ3 * (1536 : K[X])) * g * f ^ 3) +
            (((3932160 : K[X]) * p0 -
                Polynomial.C κ3 * (12288 : K[X])) * p1 * f ^ 2) +
            (Polynomial.C κ3 * ((1536 : K[X]) * p0) +
                Polynomial.C κ7 - (245760 : K[X]) * p0 ^ 2) *
              ((64 : K[X]) * g * f + (512 : K[X]) * p1)))) :
    alignedEleventhDeepLeft410 H s r g1 f =
      alignedEleventhDeepRight410 H p0 s r g1 f κ3 κ7 := by
  rw [hg, hp2, hp1] at hblk
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  simp only [alignedEleventhDeepLeft410, alignedEleventhDeepRight410]
  linear_combination hblk

/-- At either root of `H`, the deep quotient is exactly the scalar leading
factor isolated in the preceding file. -/
theorem alignedNonsquareEleventh_deepRootLeading_410
    (H p0 s r g1 f : K[X]) (κ3 κ7 x : K)
    (hquot : alignedEleventhDeepLeft410 H s r g1 f =
      alignedEleventhDeepRight410 H p0 s r g1 f κ3 κ7)
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r)
    (hx : H.eval x = 0) :
    alignedEleventhRootLeading410
      (p0.eval x) (s.eval x) (r.eval x) (g1.eval x) κ3 κ7 = 0 := by
  have hfroot : f.eval x = -(4 : K) * r.eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) hf
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hx, zero_mul] at hev
    linear_combination hev
  have hev := congrArg (fun w : K[X] => w.eval x) hquot
  simp only [alignedEleventhDeepLeft410, alignedEleventhDeepRight410,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hev
  rw [hx, hfroot] at hev
  norm_num at hev
  simp only [alignedEleventhRootLeading410]
  linear_combination hev

/-- Rootwise split of the deep eleventh row into the next terminal quotient
and the new companion factor. -/
theorem alignedNonsquareEleventh_deepRootSplit_410
    (H p0 s r g1 f : K[X]) (κ3 κ7 x : K)
    (hquot : alignedEleventhDeepLeft410 H s r g1 f =
      alignedEleventhDeepRight410 H p0 s r g1 f κ3 κ7)
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r)
    (hx : H.eval x = 0) :
    (2 * s.eval x - r.eval x * g1.eval x) = 0 ∨
      alignedEleventhRootCompanion410 (p0.eval x) (r.eval x) κ3 κ7 = 0 := by
  exact alignedEleventhRootLeading_split410 _ _ _ _ _ _
    (alignedNonsquareEleventh_deepRootLeading_410
      H p0 s r g1 f κ3 κ7 x hquot hf hx)

section Source410

variable [IsAlgClosed K]

/-- Source-facing deep eleventh packet on the exact `g,f,g₁,r` witnesses
selected by the preceding allocation.  The older eleventh packet's
existential witnesses are proved equal by cancellation of the same nonzero
quadratic `H`; they are not silently reselected. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorEleventhDeep
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
    ∃ (κ3 κ7 : K) (s l : K[X]),
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧ p.coeff 1 = H * s ∧
        g * f + (8 : K[X]) * p.coeff 1 = H * l ∧
        alignedEleventhDeepLeft410 H s r g1 f =
          alignedEleventhDeepRight410 H (p.coeff 0) s r g1 f κ3 κ7 ∧
        ∀ x : K, H.eval x = 0 →
          (2 * s.eval x - r.eval x * g1.eval x) = 0 ∨
            alignedEleventhRootCompanion410
              ((p.coeff 0).eval x) (r.eval x) κ3 κ7 = 0 := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨s, l, _hg, _hp3, _hp2, _hf, hs, hl⟩ :=
    normalized410ScaleTwo_alignedNonsquare_gDivisorComplement
      hsource hnsq haligned hg hp3deep hp2deep hf
  obtain ⟨_κ, κ3, _κ5, κ7, _κ9, _κ11, g0, f0, hp30, hM2, hM4,
      hM5, _hM6, hM7, hM8, hM9, _hM10, hM11, _hM12, hgf0,
      _hblock12⟩ :=
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
  have hcore := alignedNonsquareEleventh_core_410
    hsource.1 hp30 hM2 hM4 hM5 hM7 hM8 hM9 hM11
  have hblock := alignedNonsquareEleventh_solved_410 hsource.1 hcore hgf0
  rw [hg0, hf0] at hblock
  have hquot := alignedNonsquareEleventh_deepSolved_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) g f g1 r s κ3 κ7
      hsource.1 hg hp2deep hs hblock
  refine ⟨κ3, κ7, s, l, hg, hp3deep, hp2deep, hf, hs, hl, hquot, ?_⟩
  intro x hx
  exact alignedNonsquareEleventh_deepRootSplit_410
    H (p.coeff 0) s r g1 f κ3 κ7 x hquot hf hx

end Source410

#print axioms alignedNonsquareEleventh_deepSolved_410
#print axioms alignedNonsquareEleventh_deepRootLeading_410
#print axioms alignedNonsquareEleventh_deepRootSplit_410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorEleventhDeep

end Max11DegreeRoutes
