import Sol68ScaleTwoAlignedNonsquareAfterLowerOneMixedAllocationScratch

/-! # The larger independent lower row at the pure load wall -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section TerminalLowerZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalLowerZeroSNumerator68
    (H A b d : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * d + C (4 / 9 : k) * A * b + C alpha * H * b

def terminalLowerZeroCDot68 (H C0 : k[X]) : k[X] :=
  H * C0.derivative - C 2 * H.derivative * C0

def terminalLowerZeroTDot68 (H T : k[X]) : k[X] :=
  H * T.derivative - C 3 * H.derivative * T

/-- Denominator clearing of the larger independent lower one-form
`U C' + 2T D' + 3S E' - 3B V' - 2C U' - D T'`. -/
def terminalLowerZeroCleared68
    (H A b C0 d E : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let S0 := terminalLowerZeroSNumerator68 H A b d alpha
  let T0 := terminalLowerOneTNumerator68 H A b C0 E alpha gamma epsilon
  let U0 := terminalLowerOneUNumerator68 H A b C0 d alpha gamma
  let V0 := terminalVNumerator68 H A b C0 d E alpha gamma epsilon eta
  U0 * terminalLowerZeroCDot68 H C0 +
    T0 * terminalLowerOneDTwoDot68 H d +
    C 3 * S0 * terminalEDerivativeNumerator68 H E -
    C 3 * b * terminalVDerivativeNumerator68 H V0 -
    C0 * terminalLowerOneUTwoDot68 H U0 -
    d * terminalLowerZeroTDot68 H T0

/-- Homogeneous clearing of the larger lower one-form. -/
theorem terminalLowerZeroCleared_of_scaled_values_68
    (h B C0 D S0 T U dC dD dE dV dU dT
      b c d s t u dc dd de dv du dt : k)
    (hB : h * B = b) (hC : h ^ 4 * C0 = c) (hD : h ^ 3 * D = d)
    (hS : h ^ 3 * S0 = s) (hT : h ^ 6 * T = t)
    (hU : h ^ 5 * U = u)
    (hdC : h ^ 6 * dC = dc) (hdD : 2 * h ^ 5 * dD = dd)
    (hdE : h ^ 8 * dE = de) (hdV : h ^ 10 * dV = dv)
    (hdU : 2 * h ^ 7 * dU = du) (hdT : h ^ 8 * dT = dt)
    (hrow : U * dC + 2 * T * dD + 3 * S0 * dE -
      3 * B * dV - 2 * C0 * dU - D * dT = 0) :
    u * dc + t * dd + 3 * s * de - 3 * b * dv - c * du - d * dt = 0 := by
  rw [← hB, ← hC, ← hD, ← hS, ← hT, ← hU,
    ← hdC, ← hdD, ← hdE, ← hdV, ← hdU, ← hdT]
  linear_combination h ^ 11 * hrow

def terminalLowerZeroUFive68
    (H A B C0 D : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * H * B * C0 + C (4 / 9 : k) * A * D -
    C (4 / 27 : k) * H * A ^ 2 * B + C alpha * H * D +
    C (2 / 3 * gamma : k) * H ^ 3 * B

def terminalLowerZeroSFive68
    (H A B D : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * D + C (4 / 9 : k) * H * A * B +
    C alpha * H ^ 2 * B

def terminalLowerZeroDDFive68 (H D : k[X]) : k[X] :=
  (C 2 * C 5 - C 3) * H.derivative * D + C 2 * H * D.derivative

def terminalLowerZeroUDFive68 (H U5 : k[X]) : k[X] :=
  (C 2 * C 5 - C 5) * H.derivative * U5 + C 2 * H * U5.derivative

/-- The quotient after removing the five automatic core factors. -/
def terminalLowerZeroFive68
    (H A B C0 D E : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let S5 := terminalLowerZeroSFive68 H A B D alpha
  let T0 := terminalLowerOneTNumerator68 H A (H ^ 6 * B) C0 E
    alpha gamma epsilon
  let U5 := terminalLowerZeroUFive68 H A B C0 D alpha gamma
  let V0 := terminalVNumerator68 H A (H ^ 6 * B) C0 (H ^ 5 * D) E
    alpha gamma epsilon eta
  U5 * terminalLowerZeroCDot68 H C0 +
    T0 * terminalLowerZeroDDFive68 H D +
    C 3 * S5 * terminalEDerivativeNumerator68 H E -
    C 3 * H * B * terminalVDerivativeNumerator68 H V0 -
    C0 * terminalLowerZeroUDFive68 H U5 -
    D * terminalLowerZeroTDot68 H T0

theorem terminalLowerZero_factor_five_68
    (H A b C0 d E B D : k[X]) (alpha gamma epsilon eta : k)
    (hb : b = H ^ 6 * B) (hd : d = H ^ 5 * D) :
    terminalLowerZeroCleared68 H A b C0 d E alpha gamma epsilon eta =
      H ^ 5 * terminalLowerZeroFive68 H A B C0 D E
        alpha gamma epsilon eta := by
  rw [hb, hd]
  have hS : terminalLowerZeroSNumerator68 H A (H ^ 6 * B) (H ^ 5 * D)
      alpha = H ^ 5 * terminalLowerZeroSFive68 H A B D alpha := by
    simp only [terminalLowerZeroSNumerator68, terminalLowerZeroSFive68]
    ring
  have hU : terminalLowerOneUNumerator68 H A (H ^ 6 * B) C0 (H ^ 5 * D)
      alpha gamma = H ^ 5 *
        terminalLowerZeroUFive68 H A B C0 D alpha gamma := by
    simp only [terminalLowerOneUNumerator68, terminalLowerZeroUFive68]
    ring
  have hpow5 : (H ^ 5).derivative = C 5 * H ^ 4 * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hDD : terminalLowerOneDTwoDot68 H (H ^ 5 * D) =
      H ^ 5 * terminalLowerZeroDDFive68 H D := by
    simp only [terminalLowerOneDTwoDot68, terminalLowerZeroDDFive68,
      derivative_mul, hpow5]
    ring
  have hUD : terminalLowerOneUTwoDot68 H
      (terminalLowerOneUNumerator68 H A (H ^ 6 * B) C0 (H ^ 5 * D)
        alpha gamma) = H ^ 5 * terminalLowerZeroUDFive68 H
          (terminalLowerZeroUFive68 H A B C0 D alpha gamma) := by
    rw [hU]
    simp only [terminalLowerOneUTwoDot68, terminalLowerZeroUDFive68,
      derivative_mul, hpow5]
    ring
  simp only [terminalLowerZeroCleared68, terminalLowerZeroFive68]
  rw [hS, hDD, hUD, hU]
  ring

/-- The leading face of the fivefold quotient cancels; its first derivative
is the genuinely new scalar `(3/2) D₄ (H')² Φ₁`. -/
theorem terminalLowerZeroFive_derivative_factor_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 + C (3 / 8 : k) * H * phi +
      H ^ 2 * (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H ^ 6 * B)) ^ 2
    (terminalLowerZeroFive68 H A B C0 D E
      alpha gamma epsilon eta).derivative.eval a =
        (3 / 2 : k) * D.eval a * (H.derivative.eval a) ^ 2 * phi.eval a := by
  dsimp only
  simp only [terminalLowerZeroFive68, terminalLowerZeroUFive68,
    terminalLowerZeroSFive68, terminalLowerZeroDDFive68,
    terminalLowerZeroUDFive68, terminalLowerZeroCDot68,
    terminalLowerZeroTDot68, terminalLowerOneTNumerator68,
    terminalEDerivativeNumerator68, terminalVDerivativeNumerator68,
    terminalVNumerator68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

theorem terminalLowerZero_pureLoadWall_impossible_68
    (H A b C0 d E b5 d4 phi w : k[X])
    (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hd4 : d4.eval a ≠ 0) (hphi : phi.eval a ≠ 0)
    (hb : b = H ^ 6 * b5) (hd : d = H ^ 5 * d4)
    (hC : C0 = C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k)))
    (hE : E = C (1 / 27 : k) * A ^ 3 + C (3 / 8 : k) * H * phi +
      H ^ 2 * (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H ^ 6 * b5)) ^ 2)
    (hlower : terminalLowerZeroCleared68 H A b C0 d E
      alpha gamma epsilon eta = 0) : False := by
  have hfactor := terminalLowerZero_factor_five_68
    H A b C0 d E b5 d4 alpha gamma epsilon eta hb hd
  have hH : H ≠ 0 := by
    intro hzero
    rw [hzero, derivative_zero, eval_zero] at hh
    exact hh rfl
  have hfive : terminalLowerZeroFive68 H A b5 C0 d4 E
      alpha gamma epsilon eta = 0 := by
    have hz : H ^ 5 * terminalLowerZeroFive68 H A b5 C0 d4 E
        alpha gamma epsilon eta = 0 := by rw [← hfactor, hlower]
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 5 hH)
  have hzero : (terminalLowerZeroFive68 H A b5 C0 d4 E
      alpha gamma epsilon eta).derivative.eval a = 0 := by
    rw [hfive, derivative_zero, eval_zero]
  rw [hC, hE,
    terminalLowerZeroFive_derivative_factor_68 H A b5 d4 phi w
      alpha gamma epsilon eta a ha] at hzero
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hd4) (pow_ne_zero 2 hh)) hphi) hzero

end TerminalLowerZeroAlgebra68

end Max11DegreeRoutes
