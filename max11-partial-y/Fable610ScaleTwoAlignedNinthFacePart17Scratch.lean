import Fable610ScaleTwoAlignedNinthFacePart15Scratch
import Fable610ScaleTwoAlignedNinthFacePart14Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Root data of the consumed degree-`6` row: at scale two the common
core has a root where the jet `p₅, q₉, q₈, q₇, p₄, q₆` vanishes and
the seventh-face pins hold; in the square chamber the ninth-row head,
the eighth-face `u₂` root product, and the eighth-face combined-row
cubic RESOLVE the residual branch to `e₂(a) = 0` UNCONDITIONALLY,
refined by `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)`, and in the nonsquare
chamber the cubic head pins `t₂(a) = 6 g₁(a) t₁(a)`, refining the
carried `p₂` pin to `27 p₂(a) = g₁(a)² t₁(a)`. -/
theorem normalized610ScaleTwo_alignedNinthFace_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 5).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (q.coeff 7).eval a = 0 ∧ (p.coeff 4).eval a = 0 ∧
      (q.coeff 6).eval a = 0 ∧
      ((∃ h0 w1 f2 e1 e2 e3 : K[X], ∃ κ μ : K, h0 ≠ 0 ∧ H = h0 ^ 2 ∧
          h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          e2 = h0 * e3 ∧
          alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
            Polynomial.C κ * H ^ 5 ∧
          alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 ∧
          3 * f2.eval a = w1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = w1.eval a ^ 3 ∧
          e2.eval a = 0 ∧
          (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0))) ∨
        (∃ g1 f t1 t2 u t3 : K[X], p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
          3 * f.eval a = g1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = g1.eval a ^ 3 ∧
          81 * (p.coeff 2).eval a =
            g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a ∧
          t2.eval a = 6 * g1.eval a * t1.eval a ∧
          27 * (p.coeff 2).eval a = g1.eval a ^ 2 * t1.eval a)) := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hH
      simp [hHsq, hzero]
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, μA, κ₃A, νA, w, r, w1', f1', hp5w, hq9, hq8, hq7,
      htie4, hq6, hw1', hf1', _hq5', _hF5⟩ := hpacket5
    have hpacket9 :=
      normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket9
    obtain ⟨κB, μB, κ₃B, νB, κ₅B, ν₂B, κ₇B, κ₈B, μ₃B, w1, f2, e1, e2,
      u2, e3, _hμ₃, hM9, hp5w1, hp4f2, he1, he2, hu2, _hR8, he3, _h27,
      hR9, hQ9, hD9, _hE, _hF, _hG, _hI, _hJ, _hL⟩ := hpacket9
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hr : r = h0 ^ 2 *
        ((270 : K[X]) * f2 ^ 2 - (90 : K[X]) * f2 * w1' ^ 2 +
          (10 : K[X]) * w1' ^ 4) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
      rw [hp4f2, hw1'] at htie4
      linear_combination -htie4
    have hra : r.eval a = 0 := by
      rw [hr, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hpin1 : 3 * f2.eval a = w1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = w1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hev1 := congrArg (fun t : K[X] => t.eval a) hu2
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_ofNat] at hev1
    rw [hroot, zero_mul] at hev1
    have h1 : w1.eval a *
        (e2.eval a - 3 * e1.eval a * w1.eval a) = 0 := by
      linear_combination hev1
    have hevQ9 := congrArg (fun t : K[X] => t.eval a) hQ9
    simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevQ9
    rw [hroot] at hevQ9
    have h2 : 1280 * e1.eval a *
        (3 * e1.eval a * w1.eval a - e2.eval a) *
        (6 * e1.eval a * w1.eval a - e2.eval a) +
        189 * μB * w1.eval a ^ 5 = 0 := by
      linear_combination -hevQ9
    have hevR9 := congrArg (fun t : K[X] => t.eval a) hR9
    simp only [alignedNinthSquarePeeledRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevR9
    rw [hroot] at hevR9
    have h9 : 276480 * e1.eval a ^ 3 * w1.eval a ^ 3 -
        5120 * e2.eval a ^ 3 - 189 * μB * w1.eval a ^ 6 = 0 := by
      linear_combination hevR9
    obtain ⟨hv0, hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f2, e1, e2, e3, κB, μB, hh0, hHsq, hroot, hp5w1,
        hp4f2, he1, he2, he3, hM9, hD9, hpin1, hpin2, hv0, hbranch⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp5w1, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (7 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun t : K[X] => t.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
    · rw [hp4f2, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      have h486 : (486 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 6).eval a = 0 := by
        linear_combination hev + hra
      exact (mul_eq_zero.mp h486).resolve_left
        (by norm_num : (486 : K) ≠ 0)
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, κ₃A, g1', f', _hp5', hq9, hq8, hq7, _hf', hq6, _hq5',
      _hD0', _hE', _hF0'⟩ := hpacket5
    have hpacket9 :=
      normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket9
    obtain ⟨κB, κ₃B, κ₅B, κ₇B, g1, f, t1, t2, u, t3, _hM9, hp5, hf,
      ht1, ht2, hu, ht3, _hq1, _hq2, _hD0, _hE, _hF0, _hG, _hI0, _hJ,
      _hL0⟩ := hpacket9
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hpin1 : 3 * f.eval a = g1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = g1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hp2pin : 81 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 2).eval a) =
        g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) hu
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have ht2pin : t2.eval a = 6 * g1.eval a * t1.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht3
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hp2ref : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 2).eval a) =
        g1.eval a ^ 2 * t1.eval a := by
      linear_combination (3⁻¹ : K) * hp2pin +
        (3⁻¹ : K) * g1.eval a * ht2pin
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨g1, f, t1, t2, u, t3, hp5, hf, ht1, ht2, hu, ht3, hpin1,
        hpin2, hp2pin, ht2pin, hp2ref⟩⟩
    · rw [hp5, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun t : K[X] => t.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
    · rw [hf, Polynomial.eval_mul, hroot, zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (486 : K) ≠ 0)

end Max11DegreeRoutes
