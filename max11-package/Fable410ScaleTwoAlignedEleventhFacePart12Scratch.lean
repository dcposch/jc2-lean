import Fable410ScaleTwoAlignedEleventhFacePart11Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact square-chamber twelfth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free form `M₂₀ = κ₁₁ H¹⁸`, the ninth face's solved `q₀` row
carrying `s₁₆`, the NEW μ-free leading divisibility carrying `s₂₅`,
the explicit peels producing `s₂₆` through `s₃₃`, the `p₀`-cubic
constant pin, and the GLOBAL `q₀`-backwire cross-tie eliminating the
`p₀`-cubic between the two pins.  The constants are preserved, not
cleared. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ μ₅ κ₁₁ : K)
      (u v s₁₆ s₂₅ s₂₆ s₂₇ s₂₈ s₂₉ s₃₀ s₃₁ s₃₂ s₃₃ : K[X]),
      p.coeff 3 = h0 ^ 2 * u ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₂ * h0 ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = Polynomial.C μ₃ * h0 ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₄ * h0 ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₅ * h0 ^ 33 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (4194304 : K[X]) * q.coeff 0 =
          Polynomial.C κ * ((524288 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C κ₅ * ((2048 : K[X]) * p.coeff 0) -
            Polynomial.C κ₉ - s₁₆ ∧
        (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
            (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
        h0 * s₂₅ ∧
        s₂₅ + (51200 : K[X]) * (p.coeff 1) * u *
          ((187 : K[X]) * u ^ 4 - (664 : K[X]) * (p.coeff 2) * u ^ 2 +
            (432 : K[X]) * (p.coeff 2) ^ 2) * v ^ 2 +
          Polynomial.C μ * ((35840 : K[X]) * (p.coeff 2) ^ 3 * u * v) = h0 * s₂₆ ∧
        s₂₆ +
          (314572800 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) ^ 2 * v -
          Polynomial.C μ * ((349440 : K[X]) * (p.coeff 2) ^ 2 * u * v ^ 2) +
          Polynomial.C μ * ((286720 : K[X]) * (p.coeff 1) * (p.coeff 2) ^ 3) = h0 * s₂₇ ∧
        s₂₇ +
          (334233600 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) * v ^ 2 +
          (209715200 : K[X]) * (p.coeff 1) ^ 3 * (p.coeff 2) * u -
          (78643200 : K[X]) * (p.coeff 0) * (p.coeff 2) ^ 2 * v ^ 2 -
          Polynomial.C μ₂ * ((6400 : K[X]) * (p.coeff 2) ^ 2 * u * v) -
          Polynomial.C μ * ((495040 : K[X]) * (p.coeff 2) * u * v ^ 3) -
          Polynomial.C μ * ((6236160 : K[X]) * (p.coeff 1) * (p.coeff 2) ^ 2 * v) +
          Polynomial.C κ₃ * ((245760 : K[X]) * (p.coeff 2) ^ 2 * v ^ 2) = h0 * s₂₈ ∧
        s₂₈ +
          (68812800 : K[X]) * (p.coeff 1) ^ 2 * v ^ 3 +
          (183500800 : K[X]) * (p.coeff 1) ^ 3 * u * v -
          (68812800 : K[X]) * (p.coeff 0) * (p.coeff 2) * v ^ 3 -
          (314572800 : K[X]) * (p.coeff 0) * (p.coeff 1) * (p.coeff 2) * u * v -
          Polynomial.C μ₂ * ((35200 : K[X]) * (p.coeff 2) * u * v ^ 2) -
          Polynomial.C μ₂ * ((51200 : K[X]) * (p.coeff 1) * (p.coeff 2) ^ 2) -
          Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) -
          Polynomial.C μ * ((8547840 : K[X]) * (p.coeff 1) * (p.coeff 2) * v ^ 2) -
          Polynomial.C μ * ((6881280 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) * u) +
          Polynomial.C κ₃ * ((215040 : K[X]) * (p.coeff 2) * v ^ 3) +
          Polynomial.C κ₃ * ((983040 : K[X]) * (p.coeff 1) * (p.coeff 2) * u * v) = h0 * s₂₉ ∧
        s₂₉ -
          (12902400 : K[X]) * (p.coeff 0) * v ^ 4 -
          (176947200 : K[X]) * (p.coeff 0) * (p.coeff 1) * u * v ^ 2 +
          (104857600 : K[X]) * (p.coeff 1) ^ 4 -
          (1258291200 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * (p.coeff 2) +
          Polynomial.C μ₃ * ((960 : K[X]) * (p.coeff 2) * u * v) -
          Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) -
          Polynomial.C μ₂ * ((486400 : K[X]) * (p.coeff 1) * (p.coeff 2) * v) -
          Polynomial.C μ * ((1921920 : K[X]) * (p.coeff 1) * v ^ 3) -
          Polynomial.C μ * ((8601600 : K[X]) * (p.coeff 1) ^ 2 * u * v) +
          Polynomial.C μ * ((3440640 : K[X]) * (p.coeff 0) * (p.coeff 2) * u * v) +
          Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) +
          Polynomial.C κ₃ * ((552960 : K[X]) * (p.coeff 1) * u * v ^ 2) +
          Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2)) = h0 * s₃₀ ∧
        s₃₀ -
          (629145600 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * v +
          (314572800 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 2) * v +
          Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) +
          Polynomial.C μ₃ * ((7680 : K[X]) * (p.coeff 1) * (p.coeff 2)) -
          Polynomial.C μ₂ * ((156800 : K[X]) * (p.coeff 1) * v ^ 2) -
          Polynomial.C μ₂ * ((409600 : K[X]) * (p.coeff 1) ^ 2 * u) +
          Polynomial.C μ * ((2580480 : K[X]) * (p.coeff 0) * u * v ^ 2) -
          Polynomial.C μ * ((9175040 : K[X]) * (p.coeff 1) ^ 3) +
          Polynomial.C μ * ((27525120 : K[X]) * (p.coeff 0) * (p.coeff 1) * (p.coeff 2)) -
          Polynomial.C κ₇ * ((1280 : K[X]) * (p.coeff 2) * v) +
          Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 1) ^ 2 * v) -
          Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 0) * (p.coeff 2) * v) = h0 * s₃₁ ∧
        s₃₁ +
          (117964800 : K[X]) * (p.coeff 0) ^ 2 * v ^ 2 +
          (629145600 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 1) * u +
          Polynomial.C μ₄ * ((80 : K[X]) * u * v) +
          Polynomial.C μ₃ * ((5760 : K[X]) * (p.coeff 1) * v) +
          Polynomial.C μ₂ * ((204800 : K[X]) * (p.coeff 0) * u * v) +
          Polynomial.C μ * ((20643840 : K[X]) * (p.coeff 0) * (p.coeff 1) * v) -
          Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) -
          Polynomial.C κ₇ * ((2560 : K[X]) * (p.coeff 1) * u) -
          Polynomial.C κ₃ * ((737280 : K[X]) * (p.coeff 0) * v ^ 2) -
          Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 0) * (p.coeff 1) * u) = h0 * s₃₂ ∧
        s₃₂ +
          Polynomial.C μ₄ * ((640 : K[X]) * (p.coeff 1)) +
          Polynomial.C μ₂ * ((1638400 : K[X]) * (p.coeff 0) * (p.coeff 1)) = h0 * s₃₃ ∧
        Polynomial.C κ₁₁ =
          (838860800 : K[X]) * (p.coeff 0) ^ 3 -
            Polynomial.C κ₇ * ((10240 : K[X]) * (p.coeff 0)) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * (p.coeff 0) ^ 2) - s₃₃ ∧
        Polynomial.C κ * Polynomial.C κ₁₁ =
          (6710886400 : K[X]) * p.coeff 0 * q.coeff 0 +
            Polynomial.C κ₅ * ((3276800 : K[X]) * p.coeff 0 ^ 2) +
            Polynomial.C κ₉ * ((1600 : K[X]) * p.coeff 0) +
            (1600 : K[X]) * p.coeff 0 * s₁₆ -
            Polynomial.C κ * Polynomial.C κ₃ * ((7864320 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C κ * Polynomial.C κ₇ * ((10240 : K[X]) * p.coeff 0) -
            Polynomial.C κ * s₃₃ := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
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
  obtain ⟨u, hu, _hq6⟩ := alignedSquareFourth_descent_410 hh0 hdeg1 hcore
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
  obtain ⟨v, hv, _hq4⟩ := alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
    twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14rel⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₄, _hμ₄2, hM14form⟩ :=
    twentySeventhPower_squareChamber_form_410 hh0 hHsq hM14rel
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₅, _hμ₅2, hM18form⟩ :=
    thirtyThirdPower_squareChamber_form_410 hh0 hHsq hM18rel
  have hcore10 :=
    alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form hM14form hM16
  obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, _ht1, _ht2, _ht3, _ht4,
    _ht5, _ht6, _ht7, hq0⟩ := alignedSquareTenth_solved_410 hh0 hcore10 hv
  obtain ⟨κ₁₁, hM20rel⟩ :=
    alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore12 :=
    alignedSquareTwelfth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM10form hM12form hM14form hM20rel
  obtain ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hd1, hd2, hd3,
    hd4, hd5, hd6, hd7, hd8, hd9, hpin⟩ :=
    alignedSquareTwelfth_solved_410 hh0 hcore12 hv
  have hcross : Polynomial.C κ * Polynomial.C κ₁₁ =
      (6710886400 : K[X]) * p.coeff 0 * q.coeff 0 +
        Polynomial.C κ₅ * ((3276800 : K[X]) * p.coeff 0 ^ 2) +
        Polynomial.C κ₉ * ((1600 : K[X]) * p.coeff 0) +
        (1600 : K[X]) * p.coeff 0 * s₁₆ -
        Polynomial.C κ * Polynomial.C κ₃ *
          ((7864320 : K[X]) * p.coeff 0 ^ 2) -
        Polynomial.C κ * Polynomial.C κ₇ *
          ((10240 : K[X]) * p.coeff 0) -
        Polynomial.C κ * s₃₃ := by
    linear_combination Polynomial.C κ * hpin -
      (1600 : K[X]) * p.coeff 0 * hq0
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, κ₁₁, u, v, s₁₆, s₂₅,
    s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hp3, hDform, hM4, hM6form,
    hM8form, hM10form, hM12form, hM14form, hM16, hM18form, hM20rel, hv,
    hq0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hpin, hcross⟩

end Max11DegreeRoutes
