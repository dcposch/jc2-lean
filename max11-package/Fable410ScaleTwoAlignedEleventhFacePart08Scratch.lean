import Fable410ScaleTwoAlignedEleventhFacePart07Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`1` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains
`h₀³`, and the peel is NINE deep: the NEW μ-FREE leading divisibility
`3200 (143 u⁶ - 572 p₂ u⁴ + 528 p₂² u² - 64 p₂³) v³ = h₀ s₂₅`, the
explicit peels producing `s₂₆` through `s₃₃` (`s₃₁` is loaded with
`μ₄`), and — with no letter left to solve — the SECOND aligned
CONSTANT PIN, now a `p₀`-cubic:
`C κ₁₁ = 838860800 p₀³ - 7864320 κ₃ p₀² - 10240 κ₇ p₀ - s₃₃`. -/
theorem alignedSquareTwelfth_solved_410 {K : Type*} [Field K]
    [CharZero K] {h0 u v a0 a1 a2 : K[X]} {μ κ₃ μ₂ μ₃ κ₇ μ₄ κ₁₁ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
            (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (51200 : K[X]) * h0 ^ 2 * a1 * u *
            ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
              (432 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
        ((Polynomial.C μ * ((123760 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 4) +
              Polynomial.C μ * ((495040 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
              Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2))) +
          h0 * ((12902400 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 4 -
              Polynomial.C κ₃ * ((40320 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 4) -
              (68812800 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (68812800 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 -
              Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) -
              (334233600 : K[X]) * a1 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (78643200 : K[X]) * a0 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 * (Polynomial.C μ₂ * ((13200 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
              Polynomial.C μ * ((1921920 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
              Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3)) +
          h0 ^ 3 * ((176947200 : K[X]) * a0 * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (183500800 : K[X]) * a1 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2) +
              (314572800 : K[X]) * a0 * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2) -
              Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
              (209715200 : K[X]) * a1 ^ 3 * a2 * u) +
          h0 ^ 4 * (-Polynomial.C μ₃ * ((720 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C μ₂ * ((156800 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              Polynomial.C μ * ((2580480 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
              Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u)) +
          h0 ^ 5 * (-(117964800 : K[X]) * a0 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              Polynomial.C κ₇ * ((480 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              (629145600 : K[X]) * a0 * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
              (314572800 : K[X]) * a0 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) +
              Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
              (104857600 : K[X]) * a1 ^ 4 +
              (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
              Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
          h0 ^ 6 * (-Polynomial.C μ₄ * ((80 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ₃ * ((5760 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
              Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
              Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
              Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2)) +
          h0 ^ 7 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * u +
              Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u)) +
          h0 ^ 8 * (-Polynomial.C μ₄ * ((640 : K[X]) * a1) -
              Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1)) +
          h0 ^ 9 * ((838860800 : K[X]) * a0 ^ 3 -
              Polynomial.C κ₁₁ * ((1 : K[X])) -
              Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
              Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₂₅ s₂₆ s₂₇ s₂₈ s₂₉ s₃₀ s₃₁ s₃₂ s₃₃ : K[X],
      (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
          (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) * v ^ 3 =
      h0 * s₂₅ ∧
      s₂₅ + (51200 : K[X]) * a1 * u *
        ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
          (432 : K[X]) * a2 ^ 2) * v ^ 2 +
        Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * v) = h0 * s₂₆ ∧
      s₂₆ +
        (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * v -
        Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * v ^ 2) +
        Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3) = h0 * s₂₇ ∧
      s₂₇ +
        (334233600 : K[X]) * a1 ^ 2 * a2 * v ^ 2 +
        (209715200 : K[X]) * a1 ^ 3 * a2 * u -
        (78643200 : K[X]) * a0 * a2 ^ 2 * v ^ 2 -
        Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * v) -
        Polynomial.C μ * ((495040 : K[X]) * a2 * u * v ^ 3) -
        Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * v) +
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * v ^ 2) = h0 * s₂₈ ∧
      s₂₈ +
        (68812800 : K[X]) * a1 ^ 2 * v ^ 3 +
        (183500800 : K[X]) * a1 ^ 3 * u * v -
        (68812800 : K[X]) * a0 * a2 * v ^ 3 -
        (314572800 : K[X]) * a0 * a1 * a2 * u * v -
        Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * v ^ 2) -
        Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) -
        Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) -
        Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * v ^ 2) -
        Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u) +
        Polynomial.C κ₃ * ((215040 : K[X]) * a2 * v ^ 3) +
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * v) = h0 * s₂₉ ∧
      s₂₉ -
        (12902400 : K[X]) * a0 * v ^ 4 -
        (176947200 : K[X]) * a0 * a1 * u * v ^ 2 +
        (104857600 : K[X]) * a1 ^ 4 -
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 +
        Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * v) -
        Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) -
        Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * v) -
        Polynomial.C μ * ((1921920 : K[X]) * a1 * v ^ 3) -
        Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * v) +
        Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * v) +
        Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) +
        Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * v ^ 2) +
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) = h0 * s₃₀ ∧
      s₃₀ -
        (629145600 : K[X]) * a0 * a1 ^ 2 * v +
        (314572800 : K[X]) * a0 ^ 2 * a2 * v +
        Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) +
        Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) -
        Polynomial.C μ₂ * ((156800 : K[X]) * a1 * v ^ 2) -
        Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
        Polynomial.C μ * ((2580480 : K[X]) * a0 * u * v ^ 2) -
        Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) +
        Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2) -
        Polynomial.C κ₇ * ((1280 : K[X]) * a2 * v) +
        Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * v) -
        Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * v) = h0 * s₃₁ ∧
      s₃₁ +
        (117964800 : K[X]) * a0 ^ 2 * v ^ 2 +
        (629145600 : K[X]) * a0 ^ 2 * a1 * u +
        Polynomial.C μ₄ * ((80 : K[X]) * u * v) +
        Polynomial.C μ₃ * ((5760 : K[X]) * a1 * v) +
        Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * v) +
        Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * v) -
        Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) -
        Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) -
        Polynomial.C κ₃ * ((737280 : K[X]) * a0 * v ^ 2) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u) = h0 * s₃₂ ∧
      s₃₂ +
        Polynomial.C μ₄ * ((640 : K[X]) * a1) +
        Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1) = h0 * s₃₃ ∧
      Polynomial.C κ₁₁ =
        (838860800 : K[X]) * a0 ^ 3 -
          Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
          Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2) - s₃₃ := by
  obtain ⟨s₃₃, hs9⟩ : ∃ w : K[X],
      w = (838860800 : K[X]) * a0 ^ 3 -
        Polynomial.C κ₁₁ * ((1 : K[X])) -
        Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
        Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2) := ⟨_, rfl⟩
  obtain ⟨s₃₂, hs8⟩ : ∃ w : K[X],
      w = -Polynomial.C μ₄ * ((640 : K[X]) * a1) -
        Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1) + h0 * s₃₃ := ⟨_, rfl⟩
  obtain ⟨s₃₁, hs7⟩ : ∃ w : K[X],
      w = -(117964800 : K[X]) * a0 ^ 2 * v ^ 2 -
        (629145600 : K[X]) * a0 ^ 2 * a1 * u -
        Polynomial.C μ₄ * ((80 : K[X]) * u * v) -
        Polynomial.C μ₃ * ((5760 : K[X]) * a1 * v) -
        Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * v) -
        Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * v) +
        Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) +
        Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
        Polynomial.C κ₃ * ((737280 : K[X]) * a0 * v ^ 2) +
        Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u) + h0 * s₃₂ := ⟨_, rfl⟩
  obtain ⟨s₃₀, hs6⟩ : ∃ w : K[X],
      w = (629145600 : K[X]) * a0 * a1 ^ 2 * v -
        (314572800 : K[X]) * a0 ^ 2 * a2 * v -
        Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) -
        Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
        Polynomial.C μ₂ * ((156800 : K[X]) * a1 * v ^ 2) +
        Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) -
        Polynomial.C μ * ((2580480 : K[X]) * a0 * u * v ^ 2) +
        Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
        Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2) +
        Polynomial.C κ₇ * ((1280 : K[X]) * a2 * v) -
        Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * v) +
        Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * v) + h0 * s₃₁ := ⟨_, rfl⟩
  obtain ⟨s₂₉, hs5⟩ : ∃ w : K[X],
      w = (12902400 : K[X]) * a0 * v ^ 4 +
        (176947200 : K[X]) * a0 * a1 * u * v ^ 2 -
        (104857600 : K[X]) * a1 ^ 4 +
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
        Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * v) +
        Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) +
        Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * v) +
        Polynomial.C μ * ((1921920 : K[X]) * a1 * v ^ 3) +
        Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * v) -
        Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * v) -
        Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) -
        Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * v ^ 2) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) + h0 * s₃₀ := ⟨_, rfl⟩
  obtain ⟨s₂₈, hs4⟩ : ∃ w : K[X],
      w = -(68812800 : K[X]) * a1 ^ 2 * v ^ 3 -
        (183500800 : K[X]) * a1 ^ 3 * u * v +
        (68812800 : K[X]) * a0 * a2 * v ^ 3 +
        (314572800 : K[X]) * a0 * a1 * a2 * u * v +
        Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * v ^ 2) +
        Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
        Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) +
        Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * v ^ 2) +
        Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u) -
        Polynomial.C κ₃ * ((215040 : K[X]) * a2 * v ^ 3) -
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * v) + h0 * s₂₉ := ⟨_, rfl⟩
  obtain ⟨s₂₇, hs3⟩ : ∃ w : K[X],
      w = -(334233600 : K[X]) * a1 ^ 2 * a2 * v ^ 2 -
        (209715200 : K[X]) * a1 ^ 3 * a2 * u +
        (78643200 : K[X]) * a0 * a2 ^ 2 * v ^ 2 +
        Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * v) +
        Polynomial.C μ * ((495040 : K[X]) * a2 * u * v ^ 3) +
        Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * v) -
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * v ^ 2) + h0 * s₂₈ := ⟨_, rfl⟩
  obtain ⟨s₂₆, hs2⟩ : ∃ w : K[X],
      w = -(314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * v +
        Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * v ^ 2) -
        Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3) + h0 * s₂₇ := ⟨_, rfl⟩
  obtain ⟨s₂₅, hs1⟩ : ∃ w : K[X],
      w = -(9574400 : K[X]) * a1 * u ^ 5 * v ^ 2 +
        (33996800 : K[X]) * a1 * a2 * u ^ 3 * v ^ 2 -
        (22118400 : K[X]) * a1 * a2 ^ 2 * u * v ^ 2 -
        Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * v) + h0 * s₂₆ := ⟨_, rfl⟩
  refine ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9]
    linear_combination hcore
  · rw [hs1]
    ring
  · rw [hs2]
    ring
  · rw [hs3]
    ring
  · rw [hs4]
    ring
  · rw [hs5]
    ring
  · rw [hs6]
    ring
  · rw [hs7]
    ring
  · rw [hs8]
    ring
  · rw [hs9]
    ring

/-! ## Nonsquare chamber -/

end Max11DegreeRoutes
