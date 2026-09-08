import Sol410ScaleTwoAlignedFinalRootPacketScratch

/-! # First scalar split at the aligned `(4,10)` final root

The nonsquare chamber ends in a perfect-cube product.  This file consumes that
product without choosing a new root: either the quadratic coordinate itself
vanishes (and hence so does `p₂`), or the complementary linear factor is zero.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- Exact two-branch reduction of the nonsquare terminal product. -/
theorem alignedFinal_nonsquareProduct_split410
    {K : Type*} [Field K] [CharZero K]
    (g f p1 p2 : K)
    (hquad : g ^ 2 = (4 : K) * p2)
    (hprod : g ^ 3 * (g * f + (8 : K) * p1) ^ 3 = 0) :
    (g = 0 ∧ p2 = 0) ∨
      (g ≠ 0 ∧ g * f + (8 : K) * p1 = 0) := by
  by_cases hg : g = 0
  · left
    refine ⟨hg, ?_⟩
    rw [hg] at hquad
    norm_num at hquad
    exact hquad
  · right
    refine ⟨hg, ?_⟩
    have hfactor : (g * f + (8 : K) * p1) ^ 3 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 3 hg)
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hfactor

/-- Same-root source inventory after consuming the nonsquare perfect cube.
At its coordinate endpoint `p₃` gains a second zero at the selected root. -/
def AlignedFinalRootRefinedPacket410 {K : Type*} [Field K]
    (p q : K[X][Y]) (H : K[X]) : Prop :=
  ∃ (a j : K), j ≠ 0 ∧ H.eval a = 0 ∧
    (p.coeff 3).eval a = 0 ∧
    (q.coeff 8).derivative.eval a = 0 ∧
    ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
        (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
    ((∃ (h0 u v : K[X]) (mu : K),
        h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
        p.coeff 3 = h0 ^ 2 * u ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        u.eval a ^ 6 * v.eval a ^ 3 = 0 ∧
        ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
          (v.eval a = 0 ∧ mu = 0))) ∨
      ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
        ∃ g f : K[X], p.coeff 3 = H * g ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
          g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          ((g.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
              (p.coeff 3).derivative.eval a = 0) ∨
            (g.eval a ≠ 0 ∧
              g.eval a * f.eval a +
                (8 : K) * (p.coeff 1).eval a = 0))))

/-- Refine the terminal packet without changing its source or selected root. -/
theorem alignedFinalRootPacket_refine410
    {K : Type*} [Field K] [CharZero K]
    {p q : K[X][Y]} {H : K[X]}
    (hpacket : AlignedFinalRootPacket410 p q H) :
    AlignedFinalRootRefinedPacket410 p q H := by
  rcases hpacket with ⟨a, j, hj, hHa, hp3a, hq8da, hrow, hchamber⟩
  refine ⟨a, j, hj, hHa, hp3a, hq8da, hrow, ?_⟩
  rcases hchamber with hsquare | hnonsquare
  · exact Or.inl hsquare
  · rcases hnonsquare with ⟨hnsq, g, f, hp3, hgf, hga, hprod⟩
    refine Or.inr ⟨hnsq, g, f, hp3, hgf, hga, ?_⟩
    rcases alignedFinal_nonsquareProduct_split410
        (g.eval a) (f.eval a) ((p.coeff 1).eval a)
        ((p.coeff 2).eval a) hga hprod with hzero | hnonzero
    · left
      refine ⟨hzero.1, hzero.2, ?_⟩
      rw [hp3, Polynomial.derivative_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, hHa, hzero.1,
        mul_zero, zero_mul, add_zero]
    · exact Or.inr hnonzero

set_option maxHeartbeats 2000000 in
/-- The nonsquare perfect-cube relation holds at every root of the exact
quadratic core, not merely at one existentially selected root. -/
theorem normalized410ScaleTwo_alignedNonsquare_allRootProduct
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ g f : K[X], p.coeff 3 = H * g ∧
      g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
      ∀ a : K, H.eval a = 0 →
        g.eval a ^ 3 *
          (g.eval a * f.eval a +
            (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpacket :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  dsimp only at hpacket
  rcases hpacket with
    ⟨_kappa, _kappa3, _kappa5, _kappa7, _kappa9, _kappa11, g, f,
      hp3, _hM2, _hM4, _hM6, _hM8, _hM10, _hM12, _hM14, _hM16,
      _hM18, _hM20, hgf, hblock⟩
  refine ⟨g, f, hp3, hgf, ?_⟩
  intro a hHa
  have hga : g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
    have hev := congrArg (fun w : K[X] => w.eval a) hgf
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hHa, zero_mul] at hev
    linear_combination hev
  have hbtie :
      (457600 : K) * g.eval a ^ 6 * f.eval a ^ 3 -
        (1830400 : K) * (p.coeff 2).eval a * g.eval a ^ 4 * f.eval a ^ 3 +
        (9574400 : K) * (p.coeff 1).eval a * g.eval a ^ 5 * f.eval a ^ 2 +
        (1689600 : K) * (p.coeff 2).eval a ^ 2 * g.eval a ^ 2 * f.eval a ^ 3 -
        (33996800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a *
          g.eval a ^ 3 * f.eval a ^ 2 -
        (204800 : K) * (p.coeff 2).eval a ^ 3 * f.eval a ^ 3 +
        (22118400 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 *
          g.eval a * f.eval a ^ 2 +
        (314572800 : K) * (p.coeff 1).eval a ^ 2 *
          (p.coeff 2).eval a ^ 2 * f.eval a +
        (209715200 : K) * (p.coeff 1).eval a ^ 3 *
          (p.coeff 2).eval a * g.eval a = 0 := by
    have hev := congrArg (fun w : K[X] => w.eval a) hblock
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev
    rw [hHa] at hev
    norm_num at hev
    linear_combination hev
  have hcube : (102400 : K) *
      (g.eval a ^ 3 *
        (g.eval a * f.eval a +
          (8 : K) * (p.coeff 1).eval a) ^ 3) = 0 := by
    linear_combination hbtie +
      (-(355200 : K) * g.eval a ^ 4 * f.eval a ^ 3 +
        (409600 : K) * (p.coeff 2).eval a * g.eval a ^ 2 * f.eval a ^ 3 -
        (7116800 : K) * (p.coeff 1).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
        (51200 : K) * (p.coeff 2).eval a ^ 2 * f.eval a ^ 3 +
        (5529600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a *
          g.eval a * f.eval a ^ 2 +
        (19660800 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 2 * f.eval a +
        (78643200 : K) * (p.coeff 1).eval a ^ 2 *
          (p.coeff 2).eval a * f.eval a +
        (52428800 : K) * (p.coeff 1).eval a ^ 3 * g.eval a) * hga
  exact (mul_eq_zero.mp hcube).resolve_left (by norm_num)

#print axioms alignedFinal_nonsquareProduct_split410
#print axioms alignedFinalRootPacket_refine410
#print axioms normalized410ScaleTwo_alignedNonsquare_allRootProduct

end Max11DegreeRoutes
