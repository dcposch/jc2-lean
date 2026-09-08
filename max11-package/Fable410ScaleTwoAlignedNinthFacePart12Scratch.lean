import Fable410ScaleTwoAlignedNinthFacePart11Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact square-chamber tenth packet of a normalized aligned scale-two
`(4,10)` source: the identifying chamber data, the chamber-free form
`M₁₆ = κ₉ H¹⁵`, the NEW μ-loaded septic divisibility
`16 (143 u⁴ - 264 p₂ u² + 48 p₂²) v³ - μ (663 u⁷ - 6552 p₂ u⁵
+ 20160 p₂² u³ - 17920 p₂³ u) = h₀ s₁₀`, the explicit peels producing
`s₁₁` through `s₁₆`, and the solved row with no `h₀`-suppressed tail.
The constants `μ`, `κ₃`, `μ₂`, `κ₅`, `μ₃`, `κ₇`, `μ₄`, and `κ₉` are
preserved, not cleared. -/
theorem normalized410ScaleTwo_alignedTenthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ : K)
      (u v s₁₀ s₁₁ s₁₂ s₁₃ s₁₄ s₁₅ s₁₆ : K[X]),
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
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (16 : K[X]) * ((143 : K[X]) * u ^ 4 -
              (264 : K[X]) * p.coeff 2 * u ^ 2 +
              (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
            Polynomial.C μ *
              ((663 : K[X]) * u ^ 7 -
                (6552 : K[X]) * p.coeff 2 * u ^ 5 +
                (20160 : K[X]) * p.coeff 2 ^ 2 * u ^ 3 -
                (17920 : K[X]) * p.coeff 2 ^ 3 * u) = h0 * s₁₀ ∧
        s₁₀ + (15360 : K[X]) * p.coeff 1 * u *
            ((3 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) * v ^ 2 =
          h0 * s₁₁ ∧
        s₁₁ + (245760 : K[X]) * p.coeff 1 ^ 2 * u ^ 2 * v -
            Polynomial.C μ *
              (p.coeff 1 * ((10080 : K[X]) * u ^ 4 -
                (53760 : K[X]) * p.coeff 2 * u ^ 2 +
                (43008 : K[X]) * p.coeff 2 ^ 2)) -
            Polynomial.C μ₂ *
              (u * ((77 : K[X]) * u ^ 4 -
                (560 : K[X]) * p.coeff 2 * u ^ 2 +
                (960 : K[X]) * p.coeff 2 ^ 2)) = h0 * s₁₂ ∧
        s₁₂ - (((61440 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (192 : K[X])) * u ^ 2 -
              (61440 : K[X]) * p.coeff 1 ^ 2) * v ^ 2 +
            (655360 : K[X]) * p.coeff 1 ^ 3 * u = h0 * s₁₃ ∧
        s₁₃ - ((10240 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (32 : K[X])) * v ^ 3 -
            ((983040 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (3072 : K[X])) * p.coeff 1 * u * v -
            Polynomial.C μ *
              ((86016 : K[X]) * p.coeff 0 * p.coeff 2 * u -
                (17920 : K[X]) * p.coeff 0 * u ^ 3 +
                (43008 : K[X]) * p.coeff 1 ^ 2 * u) -
            Polynomial.C μ₂ *
              ((960 : K[X]) * p.coeff 1 * u ^ 2 -
                (2560 : K[X]) * p.coeff 1 * p.coeff 2) -
            Polynomial.C μ₃ *
              ((24 : K[X]) * p.coeff 2 * u - (5 : K[X]) * u ^ 3) =
          h0 * s₁₄ ∧
        s₁₄ - ((3932160 : K[X]) * p.coeff 0 -
            Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 ^ 2 =
          h0 * s₁₅ ∧
        s₁₅ - (Polynomial.C κ₃ * ((6144 : K[X]) * p.coeff 0) +
              Polynomial.C κ₇ * (4 : K[X]) -
              (983040 : K[X]) * p.coeff 0 ^ 2) * v +
            Polynomial.C μ * ((344064 : K[X]) * p.coeff 0 * p.coeff 1) +
            Polynomial.C μ₂ * ((2560 : K[X]) * p.coeff 0 * u) +
            Polynomial.C μ₃ * ((96 : K[X]) * p.coeff 1) +
            Polynomial.C μ₄ * u = h0 * s₁₆ ∧
        (4194304 : K[X]) * q.coeff 0 =
          Polynomial.C κ * ((524288 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C κ₅ * ((2048 : K[X]) * p.coeff 0) -
            Polynomial.C κ₉ - s₁₆ := by
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
  have hkill0 : ∀ a : K, h0.eval a = 0 → (p.coeff 3).eval a = 0 := by
    intro a ha
    apply alignedThird_rootKill_p3_410 hrel
    rw [hHsq]
    simp only [Polynomial.eval_pow, ha]
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
  have hcore10 :=
    alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form hM14form hM16
  obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, hd1, hd2, hd3, hd4, hd5,
    hd6, hd7, hq0⟩ := alignedSquareTenth_solved_410 hh0 hcore10 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, u, v, s₁₀, s₁₁, s₁₂, s₁₃,
    s₁₄, s₁₅, s₁₆, hp3, hDform, hM4, hM6form, hM8form, hM10form,
    hM12form, hM14form, hM16, hv, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
    hq0⟩

end Max11DegreeRoutes
