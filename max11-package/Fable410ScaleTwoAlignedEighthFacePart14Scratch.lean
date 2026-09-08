import Fable410ScaleTwoAlignedEighthFacePart13Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact square-chamber ninth packet of a normalized aligned scale-two
`(4,10)` source: the identifying chamber data, the half-integral form
`M₁₄ = μ₄ h₀²⁷` with `μ₄² = κ₈` (honest residual), the NEW μ-loaded
divisibility
`80 u (11 u² - 12 p₂) v³ - μ (273 u⁶ - 2520 p₂ u⁴ + 6720 p₂² u²
- 3584 p₂³) = h₀ s₅`, the explicit peels producing `s₆`, `s₇`, `s₈`,
`s₉`, and the solved linear row.  The constants `μ`, `κ₃`, `μ₂`, `κ₅`,
`μ₃`, `κ₇`, and `μ₄` are preserved, not cleared, and `q₁` carries no
`h₀` factor. -/
theorem normalized410ScaleTwo_alignedNinthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ : K) (u v s₅ s₆ s₇ s₈ s₉ : K[X]),
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
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (80 : K[X]) * u *
              ((11 : K[X]) * u ^ 2 - (12 : K[X]) * p.coeff 2) * v ^ 3 -
            Polynomial.C μ *
              ((273 : K[X]) * u ^ 6 -
                (2520 : K[X]) * p.coeff 2 * u ^ 4 +
                (6720 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                (3584 : K[X]) * p.coeff 2 ^ 3) = h0 * s₅ ∧
        s₅ + (2560 : K[X]) * p.coeff 1 *
            ((7 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) * v ^ 2 =
          h0 * s₆ ∧
        s₆ + (122880 : K[X]) * p.coeff 1 ^ 2 * u * v -
            Polynomial.C μ₂ *
              ((35 : K[X]) * u ^ 4 - (240 : K[X]) * p.coeff 2 * u ^ 2 +
                (320 : K[X]) * p.coeff 2 ^ 2) -
            Polynomial.C μ *
              (p.coeff 1 *
                ((4480 : K[X]) * u ^ 3 -
                  (21504 : K[X]) * p.coeff 2 * u)) = h0 * s₇ ∧
        s₇ - ((30720 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (96 : K[X])) * u * v ^ 2 +
            (327680 : K[X]) * p.coeff 1 ^ 3 = h0 * s₈ ∧
        s₈ - ((491520 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (1536 : K[X])) * p.coeff 1 * v -
            Polynomial.C μ₂ * ((640 : K[X]) * p.coeff 1 * u) -
            Polynomial.C μ *
              ((86016 : K[X]) * p.coeff 0 * p.coeff 2 +
                (43008 : K[X]) * p.coeff 1 ^ 2 -
                (10752 : K[X]) * p.coeff 0 * u ^ 2) +
            Polynomial.C μ₃ *
              ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * p.coeff 2)) =
          h0 * s₉ ∧
        (1048576 : K[X]) * q.coeff 1 =
          s₉ - Polynomial.C κ₇ * ((4 : K[X]) * u) -
            Polynomial.C κ₅ * ((512 : K[X]) * p.coeff 1) -
            Polynomial.C κ₃ * ((6144 : K[X]) * p.coeff 0 * u) +
            (983040 : K[X]) * p.coeff 0 ^ 2 * u +
            Polynomial.C κ * ((262144 : K[X]) * p.coeff 0 * p.coeff 1) -
            h0 * (Polynomial.C μ₄ +
              Polynomial.C μ₂ * ((2560 : K[X]) * p.coeff 0)) := by
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
  have hcore9 :=
    alignedSquareNinth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form hM14form
  obtain ⟨s₅, s₆, s₇, s₈, s₉, hd1, hd2, hd3, hd4, hd5, hq1⟩ :=
    alignedSquareNinth_solved_410 hh0 hcore9 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, u, v, s₅, s₆, s₇, s₈, s₉, hp3,
    hDform, hM4, hM6form, hM8form, hM10form, hM12form, hM14form, hv,
    hd1, hd2, hd3, hd4, hd5, hq1⟩

end Max11DegreeRoutes
