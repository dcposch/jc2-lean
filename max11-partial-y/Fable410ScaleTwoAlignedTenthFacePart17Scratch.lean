import Fable410ScaleTwoAlignedTenthFacePart16Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Extended root data of the consumed degree-`2` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order), and the NEW degree-`2` content splits by
chamber.  The square chamber gains the NEW value tie
`4096 u(a)⁵ v(a)³ = 7 μ u(a)⁸`, whose clash with the sixth face's
product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a factor-`255`
mismatch) RE-DERIVES the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`, plus `s₁₇(a) = 0`, the
`s₁₇`/`s₁₈` ties, the μ₄-loaded tie on `s₂₂`, and the `μ₅` value tie —
the first aligned root tie seeing `μ₅`.  The nonsquare chamber's block
dies at `a` and collapses on the quadratic kill to the perfect-cube
product `g(a)² (g(a) f(a) + 8 p₁(a))³ = 0` — an independent
re-derivation of the eighth face's pin content as a product kill; no
new pin is claimed.  Both dichotomy branches are preserved. -/
theorem normalized410ScaleTwo_alignedEleventhRow_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a : K) (κ : K), H.eval a = 0 ∧
      (8 : K[X]) * q.coeff 8 =
        H * ((15 : K[X]) * p.coeff 3 ^ 2 +
          (20 : K[X]) * p.coeff 2 * H ^ 2 + Polynomial.C κ * H ^ 3) ∧
      (p.coeff 3).eval a = 0 ∧
      (q.coeff 8).derivative.eval a = 0 ∧
      ((∃ (μ μ₂ μ₃ μ₄ κ₃ κ₇ μ₅ : K)
          (h0 u v s₁₇ s₁₈ s₂₂ s₂₄ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
                (104 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((13923 : K[X]) * u ^ 8 -
                  (148512 : K[X]) * p.coeff 2 * u ^ 6 +
                  (524160 : K[X]) * p.coeff 2 ^ 2 * u ^ 4 -
                  (645120 : K[X]) * p.coeff 2 ^ 3 * u ^ 2 +
                  (143360 : K[X]) * p.coeff 2 ^ 4) = h0 * s₁₇ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (4096 : K) * u.eval a ^ 5 * v.eval a ^ 3 =
            (7 : K) * μ * u.eval a ^ 8 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₁₇.eval a =
            -(491520 : K) * (p.coeff 1).eval a * u.eval a ^ 4 *
              v.eval a ^ 2 ∧
          s₁₇.eval a = 0 ∧
          s₁₈.eval a =
            -(3932160 : K) * (p.coeff 1).eval a ^ 2 * u.eval a ^ 3 *
                v.eval a -
              (5376 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 5 -
              (20 : K) * μ₂ * u.eval a ^ 6 ∧
          s₂₂.eval a =
            ((98304 : K) * κ₃ * (p.coeff 0).eval a + (64 : K) * κ₇ -
                (15728640 : K) * (p.coeff 0).eval a ^ 2) *
                u.eval a * v.eval a -
              (2752512 : K) * μ * (p.coeff 0).eval a *
                (p.coeff 1).eval a * u.eval a -
              (10240 : K) * μ₂ * (p.coeff 0).eval a * u.eval a ^ 2 +
              (40960 : K) * μ₂ * (p.coeff 1).eval a ^ 2 -
              (768 : K) * μ₃ * (p.coeff 1).eval a * u.eval a -
              (4 : K) * μ₄ * u.eval a ^ 2 ∧
          μ₅ = s₂₄.eval a -
            (5505024 : K) * μ * (p.coeff 0).eval a ^ 2 -
            (3072 : K) * μ₃ * (p.coeff 0).eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (1280 : K) * g.eval a * ((39 : K) * g.eval a ^ 4 -
                  (104 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
                  (48 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 3 +
                (30720 : K) * (p.coeff 1).eval a *
                  ((33 : K) * g.eval a ^ 4 -
                    (72 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
                    (16 : K) * (p.coeff 2).eval a ^ 2) *
                  f.eval a ^ 2 +
                (3932160 : K) * (p.coeff 1).eval a ^ 2 *
                  g.eval a ^ 3 * f.eval a +
                (5242880 : K) * (p.coeff 1).eval a ^ 3 *
                  ((3 : K) * g.eval a ^ 2 -
                    (4 : K) * (p.coeff 2).eval a) = 0 ∧
            g.eval a ^ 2 * (g.eval a * f.eval a +
                (8 : K) * (p.coeff 1).eval a) ^ 3 = 0)) := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  rcases hsource with
    ⟨hH, _hHdeg2, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hclear := alignedSecondDefect_clearing_410 hM
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hHne
      simp [hHsq, hzero]
    obtain ⟨μ, _hμ2, hDform⟩ :=
      ninthPower_squareChamber_form_410 hH hHsq hrel
    have hdeg1 : h0.natDegree = 1 := by
      have hdegree := congrArg Polynomial.natDegree hHsq
      rw [hHdegree, Polynomial.natDegree_pow] at hdegree
      omega
    have hkill0 : ∀ b : K, h0.eval b = 0 → (p.coeff 3).eval b = 0 := by
      intro b hb
      apply alignedThird_rootKill_p3_410 hrel
      rw [hHsq]
      simp only [Polynomial.eval_pow, hb]
      norm_num
    obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
    obtain ⟨u, hu, _hq6⟩ :=
      alignedSquareFourth_descent_410 hh0 hdeg1 hcore
    have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
    obtain ⟨κ₄, hM6rel⟩ :=
      alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
      fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
    obtain ⟨κ₅, hM8form⟩ :=
      alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore6 :=
      alignedSquareSixth_core_410 hh0 hHsq hp3 hDform hM4 hM6form hM8form
    obtain ⟨v, hv, _hq4⟩ :=
      alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
      twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
    have hcore7 :=
      alignedSquareSeventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form
    obtain ⟨s, hs, _hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore7 hv
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₈, hM14rel⟩ :=
      alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₄, _hμ₄2, hM14form⟩ :=
      twentySeventhPower_squareChamber_form_410 hh0 hHsq hM14rel
    obtain ⟨κ₁₀, hM18rel⟩ :=
      alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₅, _hμ₅2, hM18form⟩ :=
      thirtyThirdPower_squareChamber_form_410 hh0 hHsq hM18rel
    have hcore11 :=
      alignedSquareEleventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM10form hM12form hM14form hM18form
    obtain ⟨s₁₇, s₁₈, s₁₉, s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hd1, hd2, hd3, hd4,
      hd5, hd6, hd7, hd8, hpin⟩ :=
      alignedSquareEleventh_solved_410 hh0 hcore11 hv
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hHroot : H.eval a = 0 := by
      rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hp3, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hHroot
    have hp3d : (p.coeff 3).derivative.eval a = 0 :=
      derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hp3 hroot
    have hkilla : u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hv
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hμtie : (80 : K) * u.eval a * v.eval a ^ 3 =
        μ * ((35 : K) * u.eval a ^ 4 -
          (336 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
          (1344 : K) * (p.coeff 2).eval a ^ 2) := by
      have hev := congrArg (fun w : K[X] => w.eval a) hs
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hkilltie : u.eval a *
        ((16 : K) * v.eval a ^ 3 - (7 : K) * μ * u.eval a ^ 3) = 0 := by
      linear_combination (1 / 5 : K) * hμtie -
        (336 / 5 : K) * μ * (p.coeff 2).eval a * hkilla
    have hd1a :
        (1280 : K) * u.eval a * ((39 : K) * u.eval a ^ 4 -
              (104 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
              (48 : K) * (p.coeff 2).eval a ^ 2) * v.eval a ^ 3 -
          μ * ((13923 : K) * u.eval a ^ 8 -
            (148512 : K) * (p.coeff 2).eval a * u.eval a ^ 6 +
            (524160 : K) * (p.coeff 2).eval a ^ 2 * u.eval a ^ 4 -
            (645120 : K) * (p.coeff 2).eval a ^ 3 * u.eval a ^ 2 +
            (143360 : K) * (p.coeff 2).eval a ^ 4) = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd1
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hnewtie : (4096 : K) * u.eval a ^ 5 * v.eval a ^ 3 =
        (7 : K) * μ * u.eval a ^ 8 := by
      linear_combination (1 / 5 : K) * hd1a -
        ((32 / 5 : K) * ((1120 : K) * μ * (p.coeff 2).eval a ^ 3 -
          (4760 : K) * μ * (p.coeff 2).eval a ^ 2 * u.eval a ^ 2 +
          (2905 : K) * μ * (p.coeff 2).eval a * u.eval a ^ 4 -
          (434 : K) * μ * u.eval a ^ 6 -
          (480 : K) * (p.coeff 2).eval a * u.eval a * v.eval a ^ 3 +
          (920 : K) * u.eval a ^ 3 * v.eval a ^ 3)) * hkilla
    have hdich : (u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
        (v.eval a = 0 ∧ μ = 0) := by
      by_cases hu : u.eval a = 0
      · refine Or.inl ⟨hu, ?_⟩
        have h4 : (4 : K) * (p.coeff 2).eval a = 0 := by
          rw [← hkilla, hu]
          ring
        exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
      · have h16 : (16 : K) * v.eval a ^ 3 -
            (7 : K) * μ * u.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp hkilltie).resolve_left hu
        have h1785 : ((1785 : K) * μ) * u.eval a ^ 8 = 0 := by
          linear_combination hnewtie - (256 : K) * u.eval a ^ 5 * h16
        have h1785μ : (1785 : K) * μ = 0 :=
          (mul_eq_zero.mp h1785).resolve_right (pow_ne_zero 8 hu)
        have hμ0 : μ = 0 :=
          (mul_eq_zero.mp h1785μ).resolve_left (by norm_num)
        have h16v : (16 : K) * v.eval a ^ 3 = 0 := by
          rw [hμ0] at h16
          linear_combination h16
        have hv3 : v.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp h16v).resolve_left (by norm_num)
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        exact Or.inr ⟨hv0, hμ0⟩
    have hs17raw : s₁₇.eval a =
        -(491520 : K) * (p.coeff 1).eval a * u.eval a ^ 4 *
          v.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd2
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev +
        (30720 : K) * (p.coeff 1).eval a * v.eval a ^ 2 *
          ((4 : K) * (p.coeff 2).eval a - (17 : K) * u.eval a ^ 2) *
          hkilla
    have hs17kill : s₁₇.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs17raw, hu0]; ring
      · rw [hs17raw, hv0]; ring
    have hs18tie : s₁₈.eval a =
        -(3932160 : K) * (p.coeff 1).eval a ^ 2 * u.eval a ^ 3 *
            v.eval a -
          (5376 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 5 -
          (20 : K) * μ₂ * u.eval a ^ 6 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd3
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        (40 : K) * ((10752 : K) * μ * (p.coeff 1).eval a *
            (p.coeff 2).eval a * u.eval a -
          (5376 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 3 -
          (64 : K) * μ₂ * (p.coeff 2).eval a ^ 2 +
          (152 : K) * μ₂ * (p.coeff 2).eval a * u.eval a ^ 2 -
          (39 : K) * μ₂ * u.eval a ^ 4) * hkilla
    have hs22tie : s₂₂.eval a =
        ((98304 : K) * κ₃ * (p.coeff 0).eval a + (64 : K) * κ₇ -
            (15728640 : K) * (p.coeff 0).eval a ^ 2) *
            u.eval a * v.eval a -
          (2752512 : K) * μ * (p.coeff 0).eval a *
            (p.coeff 1).eval a * u.eval a -
          (10240 : K) * μ₂ * (p.coeff 0).eval a * u.eval a ^ 2 +
          (40960 : K) * μ₂ * (p.coeff 1).eval a ^ 2 -
          (768 : K) * μ₃ * (p.coeff 1).eval a * u.eval a -
          (4 : K) * μ₄ * u.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd7
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        (8 : K) * ((2560 : K) * μ₂ * (p.coeff 0).eval a + μ₄) * hkilla
    have hμ₅tie : μ₅ = s₂₄.eval a -
        (5505024 : K) * μ * (p.coeff 0).eval a ^ 2 -
        (3072 : K) * μ₃ * (p.coeff 0).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hpin
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      linear_combination hev
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, μ₃, μ₄, κ₃, κ₇, μ₅, h0, u, v, s₁₇, s₁₈, s₂₂, s₂₄,
        hh0, hHsq, hroot, hp3, hv, hd1, hp3d, hkilla, hnewtie, hdich,
        hs17raw, hs17kill, hs18tie, hs22tie, hμ₅tie⟩⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    obtain ⟨_hκ₂, hD0⟩ :=
      ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
    have hsimple : ∀ b : K, H.eval b = 0 → H.derivative.eval b ≠ 0 :=
      fun b hb =>
        nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq hb
    have hkill : ∀ b : K, H.eval b = 0 → (p.coeff 3).eval b = 0 :=
      fun b hb => alignedThird_rootKill_p3_410 hrel hb
    obtain ⟨g, hg⟩ :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple hkill
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₄, hM6rel⟩ :=
      alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₄, hM60⟩ :=
      fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
    obtain ⟨κ₅, hM8form⟩ :=
      alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore6 :=
      alignedNonsquareSixth_core_410 hH hg hD0 hM4 hM60 hM8form
    obtain ⟨f, hf, _hq4⟩ :=
      alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₆, hM100⟩ :=
      twentyFirstPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM10rel
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₈, hM14rel⟩ :=
      alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₈, hM140⟩ :=
      twentySeventhPower_nonsquareChamber_kill_410 hH hHdegree hnsq
        hM14rel
    obtain ⟨κ₁₀, hM18rel⟩ :=
      alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₁₀, hM180⟩ :=
      thirtyThirdPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM18rel
    have hcore11 :=
      alignedNonsquareEleventh_core_410 hH hg hD0 hM4 hM60 hM100
        hM12form hM140 hM180
    have hblk := alignedNonsquareEleventh_solved_410 hH hcore11 hf
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hHne, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hg, Polynomial.eval_mul, hroot, zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hroot
    have hkilla : g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hf
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hbtie : (1280 : K) * g.eval a * ((39 : K) * g.eval a ^ 4 -
            (104 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
            (48 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 3 +
        (30720 : K) * (p.coeff 1).eval a *
          ((33 : K) * g.eval a ^ 4 -
            (72 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
            (16 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 2 +
        (3932160 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 3 *
          f.eval a +
        (5242880 : K) * (p.coeff 1).eval a ^ 3 *
          ((3 : K) * g.eval a ^ 2 - (4 : K) * (p.coeff 2).eval a) =
        0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hblk
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hcube : (20480 : K) * (g.eval a ^ 2 *
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3) =
        0 := by
      linear_combination hbtie -
        (1280 : K) * ((23 : K) * f.eval a ^ 3 * g.eval a ^ 3 -
          (12 : K) * f.eval a ^ 3 * g.eval a * (p.coeff 2).eval a +
          (408 : K) * f.eval a ^ 2 * g.eval a ^ 2 *
            (p.coeff 1).eval a -
          (96 : K) * f.eval a ^ 2 * (p.coeff 1).eval a *
            (p.coeff 2).eval a +
          (4096 : K) * (p.coeff 1).eval a ^ 3) * hkilla
    have hprod : g.eval a ^ 2 * (g.eval a * f.eval a +
        (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 :=
      (mul_eq_zero.mp hcube).resolve_left (by norm_num)
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hbtie, hprod⟩⟩

#print axioms normalized410ScaleTwo_alignedEleventhRow_rootData

end Max11DegreeRoutes
