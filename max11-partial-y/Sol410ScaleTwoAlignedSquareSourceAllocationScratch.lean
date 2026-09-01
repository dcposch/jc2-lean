import Sol410ScaleTwoAlignedSquareComplementSourceClosureScratch
import Sol410ScaleTwoAlignedSquareDeepEleventhAllocationScratch

/-! # Source allocation after the aligned-square complement closure -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

set_option maxHeartbeats 8000000 in
/-- On the exact supplied square factor, the complement root is impossible.
The same source witness therefore lies on the `u`-factor limb.  The exact
ninth quotient is split there, and the tenth row closes both alternatives by
forcing the quotient `r=p2/h0` to acquire a second `h0` factor. -/
theorem normalized410ScaleTwo_alignedSquare_sourceAllocation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    ∃ (x : K) (u v g r r1 : K[X]),
      h0.eval x = 0 ∧
      p.coeff 3 = h0 ^ 2 * u ∧
      u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
      u = h0 * g ∧ p.coeff 2 = h0 * r ∧ r = h0 * r1 ∧
      ((p.coeff 1).eval x = 0 ∨
        (g.eval x = 0 ∧ r1.eval x = 0)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hdeg : h0.natDegree = 1 := by
    have hdegree := congrArg Polynomial.natDegree hHsq
    rw [hsource.2.1, Polynomial.natDegree_pow] at hdegree
    omega
  have hdegne : h0.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hh0, hdeg]
    decide
  obtain ⟨x, hxroot⟩ := IsAlgClosed.exists_root h0 hdegne
  have hx : h0.eval x = 0 := hxroot
  have hpacket := normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
    hsource hh0 hHsq haligned
  dsimp only at hpacket
  obtain ⟨κ, μ, κ3, μ2, κ5, μ3, κ7, μ4, κ9, μ5, κ11,
    u, v, _s16, _s25, _s26, _s27, _s28, _s29, _s30, _s31, _s32, _s33,
    hp3, hM2, hM4, hM6, hM8, hM10, hM12, hM14, hM16, hM18, hM20,
    hv, _hq0, hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7, _hd8, _hd9,
    _hpin, _hcross⟩ := hpacket
  have hkilla : u.eval x ^ 2 = (4 : K) * (p.coeff 2).eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) hv
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hx, zero_mul] at hev
    linear_combination hev
  have hev1 := congrArg (fun w : K[X] => w.eval x) hd1
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat] at hev1
  rw [hx, zero_mul] at hev1
  have hval : (102400 : K) * (u.eval x ^ 6 * v.eval x ^ 3) = 0 := by
    linear_combination hev1 +
      (-(355200 : K) * u.eval x ^ 4 * v.eval x ^ 3 +
        (409600 : K) * (p.coeff 2).eval x * u.eval x ^ 2 * v.eval x ^ 3 -
        (51200 : K) * (p.coeff 2).eval x ^ 2 * v.eval x ^ 3) * hkilla
  have hu6v3 : u.eval x ^ 6 * v.eval x ^ 3 = 0 :=
    (mul_eq_zero.mp hval).resolve_left (by norm_num)
  by_cases hux : u.eval x = 0
  · obtain ⟨g, r, hu, hp2, _hninth⟩ := alignedSquareUFactor_allocation410
      H h0 u v (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
        (q.coeff 6) (q.coeff 7) κ μ κ3 μ2 κ5 μ3 κ7 μ4 hh0 hdeg
        hHsq hp3 hM2 hM4 hM6 hM8 hM10 hM12 hM14 hv x hx hux
    have hrx := alignedSquareUFactor_tenthRootKill410
      H h0 u g r (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
        (q.coeff 5) (q.coeff 6) (q.coeff 7)
        κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 hh0 hHsq hp3 hM2 hM4 hM6 hM8
        hM10 hM12 hM14 hM16 hu hp2 x hx
    have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
      obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
      intro y hy
      rw [← hlinear] at hx hy
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] at hx hy
      have hcy : c * (y - x) = 0 := by linear_combination hy - hx
      exact sub_eq_zero.mp ((mul_eq_zero.mp hcy).resolve_left hc)
    obtain ⟨r1, hr⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
      rw [hrootUnique y hy]
      exact hrx)
    have hp2deep : p.coeff 2 = h0 ^ 2 * r1 := by
      calc
        p.coeff 2 = h0 * r := hp2
        _ = h0 * (h0 * r1) := by rw [hr]
        _ = h0 ^ 2 * r1 := by ring
    have hsplit10 := alignedSquareDeepTenth_rootSplit410
      H h0 u g r1 (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
        (q.coeff 5) (q.coeff 6) (q.coeff 7)
        κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 hh0 hHsq hp3 hM2 hM4 hM6 hM8
        hM10 hM12 hM14 hM16 hu hp2deep x hx
    have hsplit11 := alignedSquareDeepEleventh_rootSplit410
      H h0 u g r1 (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
        (q.coeff 6) (q.coeff 7) κ μ κ3 μ2 κ5 μ3 κ7 μ4 μ5 hh0 hHsq
        hp3 hM2 hM4 hM6 hM10 hM12 hM14 hM18 hu hp2deep x hx
    have hdeep : (p.coeff 1).eval x = 0 ∨
        (g.eval x = 0 ∧ r1.eval x = 0) := by
      rcases hsplit10 with hgx | hp1x
      · rcases hsplit11 with hp1x | hrel
        · exact Or.inl hp1x
        · right
          refine ⟨hgx, ?_⟩
          rw [hgx] at hrel
          norm_num at hrel
          exact hrel
      · exact Or.inl hp1x
    exact ⟨x, u, v, g, r, r1, hx, hp3, hv, hu, hp2, hr, hdeep⟩
  · have hv3 : v.eval x ^ 3 = 0 :=
      (mul_eq_zero.mp hu6v3).resolve_left (pow_ne_zero 6 hux)
    have hvx : v.eval x = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hv3
    exact (normalized410ScaleTwo_alignedSquare_complement_false
      hsource hh0 hHsq haligned hp3 hv x hx hux hvx).elim

#print axioms normalized410ScaleTwo_alignedSquare_sourceAllocation

end Max11DegreeRoutes
