import Fable410ScaleTwoAlignedEleventhFacePart12Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact nonsquare-chamber twelfth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free form `M₂₀ = κ₁₁ H¹⁸` (no parity kill), and the `q`-free
block identity on the fifth face's divisibility `g² - 4 p₂ = H f`
whose `H²`-part ties `κ₁₁` two levels deep. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ κ₉ κ₁₁ : K) (g f : K[X]),
      p.coeff 3 = H * g ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        ((3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * (p.coeff 2) * g ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * g ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * f ^ 3 +
          (51200 : K[X]) * (p.coeff 1) * g *
            ((187 : K[X]) * g ^ 4 - (664 : K[X]) * (p.coeff 2) * g ^ 2 +
              (432 : K[X]) * (p.coeff 2) ^ 2) * f ^ 2 +
          (314572800 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) ^ 2 * f +
          (209715200 : K[X]) * (p.coeff 1) ^ 3 * (p.coeff 2) * g =
          H * (-(334233600 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) * f ^ 2 -
            (183500800 : K[X]) * (p.coeff 1) ^ 3 * g * f +
            (78643200 : K[X]) * (p.coeff 0) * (p.coeff 2) ^ 2 * f ^ 2 +
            (314572800 : K[X]) * (p.coeff 0) * (p.coeff 1) * (p.coeff 2) * g * f -
            (104857600 : K[X]) * (p.coeff 1) ^ 4 +
            (1258291200 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * (p.coeff 2) -
            Polynomial.C κ₃ * ((245760 : K[X]) * (p.coeff 2) ^ 2 * f ^ 2) -
            Polynomial.C κ₃ * ((983040 : K[X]) * (p.coeff 1) * (p.coeff 2) * g * f) -
            Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2)) +
          H * (-(68812800 : K[X]) * (p.coeff 1) ^ 2 * f ^ 3 +
              (68812800 : K[X]) * (p.coeff 0) * (p.coeff 2) * f ^ 3 +
              (176947200 : K[X]) * (p.coeff 0) * (p.coeff 1) * g * f ^ 2 +
              (629145600 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * f -
              (314572800 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 2) * f -
              (629145600 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 1) * g +
              Polynomial.C κ₇ * ((1280 : K[X]) * (p.coeff 2) * f) +
              Polynomial.C κ₇ * ((2560 : K[X]) * (p.coeff 1) * g) -
              Polynomial.C κ₃ * ((215040 : K[X]) * (p.coeff 2) * f ^ 3) -
              Polynomial.C κ₃ * ((552960 : K[X]) * (p.coeff 1) * g * f ^ 2) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 1) ^ 2 * f) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 0) * (p.coeff 2) * f) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 0) * (p.coeff 1) * g) +
            H * ((12902400 : K[X]) * (p.coeff 0) * f ^ 4 -
                (117964800 : K[X]) * (p.coeff 0) ^ 2 * f ^ 2 +
                (838860800 : K[X]) * (p.coeff 0) ^ 3 -
                Polynomial.C κ₁₁ * ((1 : K[X])) +
                Polynomial.C κ₇ * ((480 : K[X]) * f ^ 2) -
                Polynomial.C κ₇ * ((10240 : K[X]) * (p.coeff 0)) -
                Polynomial.C κ₃ * ((40320 : K[X]) * f ^ 4) +
                Polynomial.C κ₃ * ((737280 : K[X]) * (p.coeff 0) * f ^ 2) -
                Polynomial.C κ₃ * ((7864320 : K[X]) * (p.coeff 0) ^ 2))))) := by
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
  obtain ⟨_hκ₂, hD0⟩ :=
    ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha =>
      nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq ha
  have hkill : ∀ a : K, H.eval a = 0 → (p.coeff 3).eval a = 0 :=
    fun a ha => alignedThird_rootKill_p3_410 hrel ha
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
    twentySeventhPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM14rel
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₁₀, hM180⟩ :=
    thirtyThirdPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM18rel
  obtain ⟨κ₁₁, hM20rel⟩ :=
    alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore12 :=
    alignedNonsquareTwelfth_core_410 hH hg hD0 hM4 hM60 hM100 hM12form
      hM140 hM20rel
  have hblk := alignedNonsquareTwelfth_solved_410 hH hcore12 hf
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, κ₁₁, g, f, hg, hD0, hM4, hM60, hM8form,
    hM100, hM12form, hM140, hM16, hM180, hM20rel, hf, hblk⟩

end Max11DegreeRoutes
