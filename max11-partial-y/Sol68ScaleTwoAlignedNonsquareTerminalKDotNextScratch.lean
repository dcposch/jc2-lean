import Sol68ScaleTwoAlignedNonsquareTerminalDerivativeFactorsScratch

/-! # The next quotient below the transverse terminal derivative -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

section TerminalKDotPolynomials68

variable {k : Type*} [Field k] [CharZero k]

def terminalScaledW68 (H A0 C0 : k[X]) (gamma : k) : k[X] :=
  C (4 / 9 : k) * C0 - C (4 / 27 : k) * A0 ^ 2 +
    C (2 / 3 * gamma : k) * H ^ 2

def terminalScaledPhi68
    (H A0 b1 C0 E0 : k[X]) (gamma epsilon : k) : k[X] :=
  -C (8 / 27 : k) * (H * b1) ^ 2 + C (8 / 3 : k) * E0 +
    C (2 * epsilon : k) * H ^ 3 + C (40 / 81 : k) * A0 ^ 3 -
    C (16 / 9 : k) * A0 * C0 - C (4 / 3 * gamma : k) * A0 * H ^ 2

def terminalKDotLoadQuotient68
    (H A0 b1 C0 d1 E0 w1 phi1 : k[X])
    (alpha gamma epsilon eta : k) : k[X] :=
  -C (1 / 6 : k) * A0 * phi1 - C (2 : k) * C0 * w1 +
    C (44 / 81 : k) * H * A0 * b1 ^ 2 -
    C (16 / 9 : k) * H * b1 * d1 - C alpha * E0 -
    C (4 / 3 * gamma : k) * H * C0 +
    C (2 / 9 * gamma : k) * H * A0 ^ 2 -
    C epsilon * H ^ 2 * A0 - C (4 * eta : k) * H ^ 3

def terminalKDotNext68
    (H E0 V0 c0 R1 : k[X]) : k[X] :=
  V0.derivative - c0 * E0.derivative + H.derivative * R1

/-- The load combination `-4V+3cE` gains one core factor from the already
known terminal `W` and `Phi` quotients. -/
theorem terminalLoadCombination_factor_68
    (H A0 b1 C0 d1 E0 w1 phi1 : k[X])
    (alpha gamma epsilon eta : k)
    (hW : terminalScaledW68 H A0 C0 gamma = H * w1)
    (hPhi : terminalScaledPhi68 H A0 b1 C0 E0 gamma epsilon = H * phi1) :
    -C (4 : k) *
          terminalVNumerator68 H A0 b1 C0 d1 E0 alpha gamma epsilon eta +
        C (3 : k) * terminalCShiftNumerator68 H A0 alpha * E0 =
      H * terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
        alpha gamma epsilon eta := by
  apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
  have hW' := congrArg (algebraMap k[X] (RatFunc k)) hW
  have hPhi' := congrArg (algebraMap k[X] (RatFunc k)) hPhi
  dsimp only [terminalScaledW68, terminalScaledPhi68,
    terminalVNumerator68, terminalCShiftNumerator68,
    terminalKDotLoadQuotient68] at hW' hPhi' ⊢
  simp only [map_add, map_sub, map_neg, map_mul, map_pow,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hW' hPhi' ⊢
  ring_nf at hW' hPhi' ⊢
  linear_combination (-2 * algebraMap k[X] (RatFunc k) C0) * hW' +
    (-1 / 6 * algebraMap k[X] (RatFunc k) A0) * hPhi'

/-- Therefore the apparent leading transverse derivative numerator is itself
divisible by `H`; `k1` is its exact next quotient. -/
theorem terminalTransverseDerivative_next_factor_68
    (H A0 b1 C0 d1 E0 w1 phi1 : k[X])
    (alpha gamma epsilon eta : k)
    (hW : terminalScaledW68 H A0 C0 gamma = H * w1)
    (hPhi : terminalScaledPhi68 H A0 b1 C0 E0 gamma epsilon = H * phi1) :
    let c0 := terminalCShiftNumerator68 H A0 alpha
    let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 alpha gamma epsilon eta
    let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
      alpha gamma epsilon eta
    terminalTransverseDerivativeNumerator68 H E0 V0 c0 =
      H * terminalKDotNext68 H E0 V0 c0 R1 := by
  let c0 := terminalCShiftNumerator68 H A0 alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 alpha gamma epsilon eta
  let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
    alpha gamma epsilon eta
  change terminalTransverseDerivativeNumerator68 H E0 V0 c0 =
    H * terminalKDotNext68 H E0 V0 c0 R1
  have hload := terminalLoadCombination_factor_68 H A0 b1 C0 d1 E0
    w1 phi1 alpha gamma epsilon eta hW hPhi
  change -C (4 : k) * V0 + C (3 : k) * c0 * E0 = H * R1 at hload
  dsimp only [terminalTransverseDerivativeNumerator68,
    terminalVDerivativeNumerator68, terminalEDerivativeNumerator68,
    terminalKDotNext68]
  calc
    H * V0.derivative - C 4 * H.derivative * V0 -
        c0 * (H * E0.derivative - C 3 * H.derivative * E0) =
      H * (V0.derivative - c0 * E0.derivative) +
        H.derivative * (-C 4 * V0 + C 3 * c0 * E0) := by ring
    _ = H * (V0.derivative - c0 * E0.derivative +
        H.derivative * R1) := by rw [hload]; ring

/-- The next root face on either transverse component. -/
theorem terminalRefinedBranch_kOne_residual_68
    (r b d w eDot k1 : k) (hr : r ≠ 0)
    (hrow : b * w * eDot - d * k1 = 0)
    (hbranch :
      (w = (2 / 27 : k) * r * b ∧ d = -(5 / 36 : k) * r ^ 2 * b) ∨
      (w = -(2 / 27 : k) * r * b ∧ d = -(1 / 36 : k) * r ^ 2 * b)) :
    (b = 0 ∨ 8 * b * eDot + 15 * r * k1 = 0) ∨
      (b = 0 ∨ 3 * r * k1 - 8 * b * eDot = 0) := by
  rcases hbranch with ⟨hw, hd⟩ | ⟨hw, hd⟩
  · left
    rw [hw, hd] at hrow
    have hfac : r * b * (8 * b * eDot + 15 * r * k1) = 0 := by
      linear_combination 108 * hrow
    rcases mul_eq_zero.mp hfac with hr0 | hbface
    · rcases mul_eq_zero.mp hr0 with hrzero | hb
      · exact Or.inl (hr hrzero).elim
      · exact Or.inl hb
    · exact Or.inr hbface
  · right
    rw [hw, hd] at hrow
    have hfac : r * b * (3 * r * k1 - 8 * b * eDot) = 0 := by
      linear_combination 108 * hrow
    rcases mul_eq_zero.mp hfac with hr0 | hbface
    · rcases mul_eq_zero.mp hr0 with hrzero | hb
      · exact Or.inl (hr hrzero).elim
      · exact Or.inl hb
    · exact Or.inr hbface

end TerminalKDotPolynomials68

end Max11DegreeRoutes
