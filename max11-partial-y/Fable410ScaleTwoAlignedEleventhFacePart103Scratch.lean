import Fable410ScaleTwoAlignedEleventhFacePart102Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`1` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` the row yields a `q`-free block
identity whose `H²`-part carries the tied constant block
`κ₁₁ + 7864320 κ₃ p₀² + 10240 κ₇ p₀ - 838860800 p₀³` — `κ₁₁` is tied
two `H`-levels deep, not solved.  The block collapses at the core
root to the perfect-cube product `102400 g³ (g f + 8 p₁)³`. -/
theorem alignedNonsquareTwelfth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 : K[X]} {κ₃ κ₇ κ₁₁ : K}
    (hH : H ≠ 0)
    (hcore :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
            (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (51200 : K[X]) * H * a1 * g *
            ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
              (432 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
        (((12902400 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 4 -
              Polynomial.C κ₃ * ((40320 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 4) -
              (68812800 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (68812800 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 -
              Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3) -
              (334233600 : K[X]) * a1 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (78643200 : K[X]) * a0 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
          H * ((176947200 : K[X]) * a0 * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (183500800 : K[X]) * a1 ^ 3 * g * (g ^ 2 - (4 : K[X]) * a2) +
              (314572800 : K[X]) * a0 * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2) -
              Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2)) -
              (209715200 : K[X]) * a1 ^ 3 * a2 * g) +
          H ^ 2 * (-(117964800 : K[X]) * a0 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              Polynomial.C κ₇ * ((480 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
              (629145600 : K[X]) * a0 * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
              (314572800 : K[X]) * a0 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) +
              Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
              (104857600 : K[X]) * a1 ^ 4 +
              (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
              Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
          H ^ 3 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * g +
              Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g)) +
          H ^ 4 * ((838860800 : K[X]) * a0 ^ 3 -
              Polynomial.C κ₁₁ * ((1 : K[X])) -
              Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
              Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
          (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) * f ^ 3 +
      (51200 : K[X]) * a1 * g *
        ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
          (432 : K[X]) * a2 ^ 2) * f ^ 2 +
      (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * f +
      (209715200 : K[X]) * a1 ^ 3 * a2 * g =
      H * (-(334233600 : K[X]) * a1 ^ 2 * a2 * f ^ 2 -
        (183500800 : K[X]) * a1 ^ 3 * g * f +
        (78643200 : K[X]) * a0 * a2 ^ 2 * f ^ 2 +
        (314572800 : K[X]) * a0 * a1 * a2 * g * f -
        (104857600 : K[X]) * a1 ^ 4 +
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * f ^ 2) -
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * f) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) +
      H * (-(68812800 : K[X]) * a1 ^ 2 * f ^ 3 +
          (68812800 : K[X]) * a0 * a2 * f ^ 3 +
          (176947200 : K[X]) * a0 * a1 * g * f ^ 2 +
          (629145600 : K[X]) * a0 * a1 ^ 2 * f -
          (314572800 : K[X]) * a0 ^ 2 * a2 * f -
          (629145600 : K[X]) * a0 ^ 2 * a1 * g +
          Polynomial.C κ₇ * ((1280 : K[X]) * a2 * f) +
          Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) -
          Polynomial.C κ₃ * ((215040 : K[X]) * a2 * f ^ 3) -
          Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * f ^ 2) -
          Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * f) +
          Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * f) +
          Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g) +
        H * ((12902400 : K[X]) * a0 * f ^ 4 -
            (117964800 : K[X]) * a0 ^ 2 * f ^ 2 +
            (838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) +
            Polynomial.C κ₇ * ((480 : K[X]) * f ^ 2) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * f ^ 2) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2)))) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing twelfth-row packets -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Source-facing weight-`18` integral of a normalized aligned
scale-two `(4,10)` source: the degree-`1` row is consumed into
`M₂₀ = κ₁₁ H¹⁸` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows.  Only the terminal
degree-`0` Keller-constant row remains unused. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ κ₁₁ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₆ * H ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₈ * H ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₁₀ * H ^ 33 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        ∀ a : K, H.eval a = 0 →
          (p.coeff 3).eval a = 0 ∧
            (q.coeff 8).derivative.eval a = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
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
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₄, hM6⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₅, hM8⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₆, hM10⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₇, hM12⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₀, hM18⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₁, hM20⟩ :=
    alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀, κ₁₁,
    aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    hM14, hM16, hM18, hM20,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

end Max11DegreeRoutes
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
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`1`
aligned row: the square chamber carries the chamber-free form
`M₂₀ = κ₁₁ H¹⁸` and the NEW μ-free leading divisibility carrying
`s₂₅` on the fifth face's divisibility; the nonsquare chamber carries
the same chamber-free form and the fifth face's divisibility — the
first aligned row whose integral shape is IDENTICAL in both chambers.
Neither chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ κ₁₁ : K) (u v s₂₅ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₁₁ * H ^ 18 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
          h0 * s₂₅) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₁₁ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₁₁ * H ^ 18 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, κ₁₁, u, v, s₁₆, s₂₅,
      s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hp3, hM2f, _hM4, _hM6f,
      _hM8, _hM10f, _hM12f, _hM14f, _hM16f, _hM18f, hM20f, hv, _hq0,
      hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7, _hd8, _hd9, _hpin,
      _hcross⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₁₁, u, v, s₂₅, hp3, hM2f,
      hM20f, hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, κ₁₁, g, f, hg, _hM2z, _hM4, _hM6z, _hM8,
      _hM10z, _hM12f, _hM14z, _hM16f, _hM18z, hM20f, hf, _hblk⟩ :=
      hpacket
    exact Or.inr ⟨hnsq, κ, κ₁₁, g, f, hg, hM20f, hf⟩

end Max11DegreeRoutes
