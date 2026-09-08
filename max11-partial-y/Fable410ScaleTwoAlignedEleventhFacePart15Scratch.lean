import Fable410ScaleTwoAlignedEleventhFacePart14Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Extended root data of the consumed degree-`1` row: at scale two
the common core has a root `a` where the previous jet dies
(`p₃(a) = 0`, `q₈` to second order), and the NEW degree-`1` content
splits by chamber.  The square chamber gains the NEW value tie as a
PURE PRODUCT KILL `u(a)⁶ v(a)³ = 0` — the first aligned root tie that
is itself a product kill — so the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)` follows DIRECTLY (via
the sixth face's product kill), plus the double unconditional peel
kills `s₂₅(a) = 0` AND `s₂₆(a) = 0`, the μ₄-loaded tie on `s₃₂`, the
`κ₁₁` value tie, the ninth face's `q₀` tie, the eighth face's `q₁`
tie, and the `κ₇`-free `q₁`-backwire combination — the first aligned
root tie linking `κ₁₁` to a solved `q`-letter.  The nonsquare
chamber's block dies at `a` and collapses on the quadratic kill to the
perfect-cube product `g(a)³ (g(a) f(a) + 8 p₁(a))³ = 0` — an
independent re-derivation of the eighth face's pin content; no new pin
is claimed.  Both dichotomy branches are preserved. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_rootData
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
      ((∃ (μ μ₂ μ₃ μ₄ κ₃ κ₅ κ₇ κ₉ κ₁₁ : K)
          (h0 u v s₉ s₁₆ s₂₅ s₂₆ s₃₂ s₃₃ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
          h0 * s₂₅ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          u.eval a ^ 6 * v.eval a ^ 3 = 0 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₂₅.eval a =
            -(39321600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2 -
            μ * ((35840 : K) * (p.coeff 2).eval a ^ 3 * u.eval a * v.eval a) ∧
          s₂₅.eval a = 0 ∧
          s₂₆.eval a =
            -(314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * v.eval a +
            μ * ((349440 : K) * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2) -
            μ * ((286720 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 3) ∧
          s₂₆.eval a = 0 ∧
          s₃₂.eval a =
            -μ₄ * ((640 : K) * (p.coeff 1).eval a) -
            μ₂ * ((1638400 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a) ∧
          κ₁₁ =
            (838860800 : K) * (p.coeff 0).eval a ^ 3 -
            κ₇ * ((10240 : K) * (p.coeff 0).eval a) -
            κ₃ * ((7864320 : K) * (p.coeff 0).eval a ^ 2) -
            s₃₃.eval a ∧
          (4194304 : K) * (q.coeff 0).eval a =
            (524288 : K) * κ * (p.coeff 0).eval a ^ 2 -
              (2048 : K) * κ₅ * (p.coeff 0).eval a - κ₉ -
              s₁₆.eval a ∧
          (1048576 : K) * (q.coeff 1).eval a =
            s₉.eval a - (4 : K) * κ₇ * u.eval a -
              (512 : K) * κ₅ * (p.coeff 1).eval a -
              (6144 : K) * κ₃ * (p.coeff 0).eval a * u.eval a +
              (983040 : K) * (p.coeff 0).eval a ^ 2 * u.eval a +
              (262144 : K) * κ * (p.coeff 0).eval a *
                (p.coeff 1).eval a ∧
          u.eval a * κ₁₁ =
            (2684354560 : K) * (p.coeff 0).eval a *
                (q.coeff 1).eval a -
              (1677721600 : K) * (p.coeff 0).eval a ^ 3 * u.eval a +
              (7864320 : K) * κ₃ * (p.coeff 0).eval a ^ 2 * u.eval a +
              (1310720 : K) * κ₅ * (p.coeff 0).eval a *
                (p.coeff 1).eval a -
              (671088640 : K) * κ * (p.coeff 0).eval a ^ 2 *
                (p.coeff 1).eval a -
              (2560 : K) * (p.coeff 0).eval a * s₉.eval a -
              s₃₃.eval a * u.eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (457600 : K) * g.eval a ^ 6 * f.eval a ^ 3 -
                (1830400 : K) * (p.coeff 2).eval a * g.eval a ^ 4 * f.eval a ^ 3 +
                (9574400 : K) * (p.coeff 1).eval a * g.eval a ^ 5 * f.eval a ^ 2 +
                (1689600 : K) * (p.coeff 2).eval a ^ 2 * g.eval a ^ 2 * f.eval a ^ 3 -
                (33996800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
                (204800 : K) * (p.coeff 2).eval a ^ 3 * f.eval a ^ 3 +
                (22118400 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * g.eval a * f.eval a ^ 2 +
                (314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * f.eval a +
                (209715200 : K) * (p.coeff 1).eval a ^ 3 * (p.coeff 2).eval a * g.eval a = 0 ∧
            g.eval a ^ 3 * (g.eval a * f.eval a +
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
    have hcore9 :=
      alignedSquareNinth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form hM14form
    obtain ⟨s₅, s₆, s₇, s₈, s₉, _hn1, _hn2, _hn3, _hn4, _hn5, hq1⟩ :=
      alignedSquareNinth_solved_410 hh0 hcore9 hv
    obtain ⟨κ₉, hM16⟩ :=
      alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore10 :=
      alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form hM14form hM16
    obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, _ht1, _ht2, _ht3, _ht4,
      _ht5, _ht6, _ht7, hq0⟩ :=
      alignedSquareTenth_solved_410 hh0 hcore10 hv
    obtain ⟨κ₁₁, hM20rel⟩ :=
      alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore12 :=
      alignedSquareTwelfth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM10form hM12form hM14form hM20rel
    obtain ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hd1, hd2, hd3,
      _hd4, _hd5, _hd6, _hd7, _hd8, hd9, hpin⟩ :=
      alignedSquareTwelfth_solved_410 hh0 hcore12 hv
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
    have hev1 := congrArg (fun w : K[X] => w.eval a) hd1
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev1
    rw [hroot, zero_mul] at hev1
    have hval : (102400 : K) *
        (u.eval a ^ 6 * v.eval a ^ 3) = 0 := by
      linear_combination hev1 +
        (-(355200 : K) * u.eval a ^ 4 * v.eval a ^ 3 +
      (409600 : K) * (p.coeff 2).eval a * u.eval a ^ 2 * v.eval a ^ 3 -
      (51200 : K) * (p.coeff 2).eval a ^ 2 * v.eval a ^ 3) * hkilla
    have hu6v3 : u.eval a ^ 6 * v.eval a ^ 3 = 0 :=
      (mul_eq_zero.mp hval).resolve_left (by norm_num)
    have hdich : (u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
        (v.eval a = 0 ∧ μ = 0) := by
      by_cases hu : u.eval a = 0
      · refine Or.inl ⟨hu, ?_⟩
        have h4 : (4 : K) * (p.coeff 2).eval a = 0 := by
          rw [← hkilla, hu]
          ring
        exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
      · have hv3 : v.eval a ^ 3 = 0 := by
          rcases mul_eq_zero.mp hu6v3 with h6 | h3
          · exact absurd
              (pow_eq_zero_iff (by norm_num : (6 : ℕ) ≠ 0) |>.mp h6) hu
          · exact h3
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        have h16 : (16 : K) * v.eval a ^ 3 -
            (7 : K) * μ * u.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp hkilltie).resolve_left hu
        have h7 : (7 : K) * μ * u.eval a ^ 3 = 0 := by
          rw [hv3] at h16
          linear_combination -h16
        have hμ0 : μ = 0 := by
          have h7u := (mul_eq_zero.mp h7).resolve_right
            (pow_ne_zero 3 hu)
          exact (mul_eq_zero.mp h7u).resolve_left (by norm_num)
        exact Or.inr ⟨hv0, hμ0⟩
    have hev2 := congrArg (fun w : K[X] => w.eval a) hd2
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev2
    rw [hroot, zero_mul] at hev2
    have hs25raw : s₂₅.eval a =
        -(39321600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2 -
          μ * ((35840 : K) * (p.coeff 2).eval a ^ 3 * u.eval a * v.eval a) := by
      linear_combination hev2 +
        (-(9574400 : K) * (p.coeff 1).eval a * u.eval a ^ 3 * v.eval a ^ 2 -
      (4300800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * u.eval a * v.eval a ^ 2) * hkilla
    have hs25kill : s₂₅.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs25raw, hu0]; ring
      · rw [hs25raw, hv0]; ring
    have hev3 := congrArg (fun w : K[X] => w.eval a) hd3
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev3
    rw [hroot, zero_mul] at hev3
    have hs26tie : s₂₆.eval a =
        -(314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * v.eval a +
          μ * ((349440 : K) * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2) -
          μ * ((286720 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 3) := by
      linear_combination hev3
    have hs26kill : s₂₆.eval a = 0 := by
      rcases hdich with ⟨_, hp20⟩ | ⟨hv0, hμ0⟩
      · rw [hs26tie, hp20]; ring
      · rw [hs26tie, hv0, hμ0]; ring
    have hev9 := congrArg (fun w : K[X] => w.eval a) hd9
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev9
    rw [hroot, zero_mul] at hev9
    have hs32tie : s₃₂.eval a =
        -μ₄ * ((640 : K) * (p.coeff 1).eval a) -
          μ₂ * ((1638400 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a) := by
      linear_combination hev9
    have hevP := congrArg (fun w : K[X] => w.eval a) hpin
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hevP
    have hk11tie : κ₁₁ =
        (838860800 : K) * (p.coeff 0).eval a ^ 3 -
          κ₇ * ((10240 : K) * (p.coeff 0).eval a) -
          κ₃ * ((7864320 : K) * (p.coeff 0).eval a ^ 2) -
        s₃₃.eval a := by
      linear_combination hevP
    have hevQ0 := congrArg (fun w : K[X] => w.eval a) hq0
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hevQ0
    have hq0tie : (4194304 : K) * (q.coeff 0).eval a =
        (524288 : K) * κ * (p.coeff 0).eval a ^ 2 -
          (2048 : K) * κ₅ * (p.coeff 0).eval a - κ₉ -
          s₁₆.eval a := by
      linear_combination hevQ0
    have hevQ1 := congrArg (fun w : K[X] => w.eval a) hq1
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hevQ1
    rw [hroot, zero_mul] at hevQ1
    have hq1tie : (1048576 : K) * (q.coeff 1).eval a =
        s₉.eval a - (4 : K) * κ₇ * u.eval a -
          (512 : K) * κ₅ * (p.coeff 1).eval a -
          (6144 : K) * κ₃ * (p.coeff 0).eval a * u.eval a +
          (983040 : K) * (p.coeff 0).eval a ^ 2 * u.eval a +
          (262144 : K) * κ * (p.coeff 0).eval a *
            (p.coeff 1).eval a := by
      linear_combination hevQ1
    have hq1combo : u.eval a * κ₁₁ =
        (2684354560 : K) * (p.coeff 0).eval a * (q.coeff 1).eval a -
          (1677721600 : K) * (p.coeff 0).eval a ^ 3 * u.eval a +
          (7864320 : K) * κ₃ * (p.coeff 0).eval a ^ 2 * u.eval a +
          (1310720 : K) * κ₅ * (p.coeff 0).eval a *
            (p.coeff 1).eval a -
          (671088640 : K) * κ * (p.coeff 0).eval a ^ 2 *
            (p.coeff 1).eval a -
          (2560 : K) * (p.coeff 0).eval a * s₉.eval a -
          s₃₃.eval a * u.eval a := by
      linear_combination u.eval a * hk11tie -
        (2560 : K) * (p.coeff 0).eval a * hq1tie
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, μ₃, μ₄, κ₃, κ₅, κ₇, κ₉, κ₁₁, h0, u, v, s₉, s₁₆,
        s₂₅, s₂₆, s₃₂, s₃₃, hh0, hHsq, hroot, hp3, hv, hd1, hp3d,
        hkilla, hu6v3, hdich, hs25raw, hs25kill, hs26tie, hs26kill,
        hs32tie, hk11tie, hq0tie, hq1tie, hq1combo⟩⟩
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
    obtain ⟨κ₁₁, hM20rel⟩ :=
      alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore12 :=
      alignedNonsquareTwelfth_core_410 hH hg hD0 hM4 hM60 hM100
        hM12form hM140 hM20rel
    have hblk := alignedNonsquareTwelfth_solved_410 hH hcore12 hf
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
    have hbtie :
        (457600 : K) * g.eval a ^ 6 * f.eval a ^ 3 -
          (1830400 : K) * (p.coeff 2).eval a * g.eval a ^ 4 * f.eval a ^ 3 +
          (9574400 : K) * (p.coeff 1).eval a * g.eval a ^ 5 * f.eval a ^ 2 +
          (1689600 : K) * (p.coeff 2).eval a ^ 2 * g.eval a ^ 2 * f.eval a ^ 3 -
          (33996800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
          (204800 : K) * (p.coeff 2).eval a ^ 3 * f.eval a ^ 3 +
          (22118400 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * g.eval a * f.eval a ^ 2 +
          (314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * f.eval a +
          (209715200 : K) * (p.coeff 1).eval a ^ 3 * (p.coeff 2).eval a * g.eval a = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hblk
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hcube : (102400 : K) * (g.eval a ^ 3 *
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3) =
        0 := by
      linear_combination hbtie +
        (-(355200 : K) * g.eval a ^ 4 * f.eval a ^ 3 +
      (409600 : K) * (p.coeff 2).eval a * g.eval a ^ 2 * f.eval a ^ 3 -
      (7116800 : K) * (p.coeff 1).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
      (51200 : K) * (p.coeff 2).eval a ^ 2 * f.eval a ^ 3 +
      (5529600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * g.eval a * f.eval a ^ 2 +
      (19660800 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 2 * f.eval a +
      (78643200 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a * f.eval a +
      (52428800 : K) * (p.coeff 1).eval a ^ 3 * g.eval a) * hkilla
    have hprod : g.eval a ^ 3 * (g.eval a * f.eval a +
        (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 :=
      (mul_eq_zero.mp hcube).resolve_left (by norm_num)
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hbtie, hprod⟩⟩


end Max11DegreeRoutes
