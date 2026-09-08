import Fable410ScaleTwoAlignedTenthFacePart13Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact square-chamber eleventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
half-integral form `M₁₈ = μ₅ h₀³³` with `μ₅² = κ₁₀` (honest residual),
the NEW μ-loaded octic divisibility carrying `s₁₇`, the explicit peels
producing `s₁₈` through `s₂₄`, and the constant pin
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`.  The constants `μ`, `κ₃`,
`μ₂`, `κ₅`, `μ₃`, `κ₇`, `μ₄`, `κ₉`, and `μ₅` are preserved, not
cleared. -/
theorem normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ μ₅ : K)
      (u v s₁₇ s₁₈ s₁₉ s₂₀ s₂₁ s₂₂ s₂₃ s₂₄ : K[X]),
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
        s₁₇ + (30720 : K[X]) * p.coeff 1 *
            ((33 : K[X]) * u ^ 4 - (72 : K[X]) * p.coeff 2 * u ^ 2 +
              (16 : K[X]) * p.coeff 2 ^ 2) * v ^ 2 = h0 * s₁₈ ∧
        s₁₈ + (3932160 : K[X]) * p.coeff 1 ^ 2 * u ^ 3 * v -
            Polynomial.C μ *
              ((209664 : K[X]) * p.coeff 1 * u ^ 5 -
                (1290240 : K[X]) * p.coeff 1 * p.coeff 2 * u ^ 3 +
                (1720320 : K[X]) * p.coeff 1 * p.coeff 2 ^ 2 * u) -
            Polynomial.C μ₂ *
              ((1540 : K[X]) * u ^ 6 -
                (12320 : K[X]) * p.coeff 2 * u ^ 4 +
                (26880 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                (10240 : K[X]) * p.coeff 2 ^ 3) = h0 * s₁₉ ∧
        s₁₉ - (((983040 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (3072 : K[X])) * u ^ 2 -
              (2949120 : K[X]) * p.coeff 1 ^ 2) * u * v ^ 2 +
            (5242880 : K[X]) * p.coeff 1 ^ 3 *
              ((3 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) =
          h0 * s₂₀ ∧
        s₂₀ - ((491520 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (1536 : K[X])) * u * v ^ 3 -
            ((15728640 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (49152 : K[X])) *
              p.coeff 1 * u ^ 2 * v +
            Polynomial.C μ *
              ((322560 : K[X]) * p.coeff 0 * u ^ 4 -
                (1720320 : K[X]) * p.coeff 0 * p.coeff 2 * u ^ 2 +
                (1376256 : K[X]) * p.coeff 0 * p.coeff 2 ^ 2 -
                (860160 : K[X]) * p.coeff 1 ^ 2 * u ^ 2 +
                (1376256 : K[X]) * p.coeff 1 ^ 2 * p.coeff 2) -
            Polynomial.C μ₂ *
              ((17920 : K[X]) * p.coeff 1 * u ^ 3 -
                (61440 : K[X]) * p.coeff 1 * p.coeff 2 * u) +
            Polynomial.C μ₃ *
              ((90 : K[X]) * u ^ 4 -
                (480 : K[X]) * p.coeff 2 * u ^ 2 +
                (384 : K[X]) * p.coeff 2 ^ 2) = h0 * s₂₁ ∧
        s₂₁ - ((3932160 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 * v ^ 2 -
            ((62914560 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (196608 : K[X])) *
              p.coeff 1 ^ 2 * u = h0 * s₂₂ ∧
        s₂₂ - (Polynomial.C κ₃ * ((98304 : K[X]) * p.coeff 0) +
              Polynomial.C κ₇ * (64 : K[X]) -
              (15728640 : K[X]) * p.coeff 0 ^ 2) * u * v +
            Polynomial.C μ *
              ((2752512 : K[X]) * p.coeff 0 * p.coeff 1 * u) -
            Polynomial.C μ₂ *
              ((81920 : K[X]) * p.coeff 0 * p.coeff 2 -
                (30720 : K[X]) * p.coeff 0 * u ^ 2 +
                (40960 : K[X]) * p.coeff 1 ^ 2) +
            Polynomial.C μ₃ * ((768 : K[X]) * p.coeff 1 * u) -
            Polynomial.C μ₄ *
              ((32 : K[X]) * p.coeff 2 - (12 : K[X]) * u ^ 2) =
          h0 * s₂₃ ∧
        s₂₃ - Polynomial.C κ₃ *
              ((786432 : K[X]) * p.coeff 0 * p.coeff 1) -
            Polynomial.C κ₇ * ((512 : K[X]) * p.coeff 1) +
            (125829120 : K[X]) * p.coeff 0 ^ 2 * p.coeff 1 =
          h0 * s₂₄ ∧
        Polynomial.C μ₅ =
          s₂₄ - Polynomial.C μ * ((5505024 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C μ₃ * ((3072 : K[X]) * p.coeff 0) := by
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
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, u, v, s₁₇, s₁₈, s₁₉,
    s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hp3, hDform, hM4, hM6form, hM8form,
    hM10form, hM12form, hM14form, hM16, hM18form, hv, hd1, hd2, hd3,
    hd4, hd5, hd6, hd7, hd8, hpin⟩

#print axioms normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet

end Max11DegreeRoutes
