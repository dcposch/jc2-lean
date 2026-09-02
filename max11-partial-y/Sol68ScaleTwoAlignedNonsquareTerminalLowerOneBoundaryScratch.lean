import Sol68ScaleTwoAlignedNonsquareTerminalRZeroXZeroFifthRowScratch

/-! # Exact lower-row-one boundary for the aligned nonsquare terminal residual -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7000000

section TerminalLowerOneClearing68

variable {k : Type*} [Field k] [CharZero k]

/-- Numerator of aligned `U` in the common odd denominator `h⁵`. -/
def terminalLowerOneUNumerator68
    (H A b C0 d : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * b * C0 + C (4 / 9 : k) * A * d -
    C (4 / 27 : k) * A ^ 2 * b + C alpha * H * d +
    C (2 / 3 * gamma : k) * H ^ 2 * b

/-- Numerator of aligned `T` in the common even denominator `H³`. -/
def terminalLowerOneTNumerator68
    (H A b C0 E : k[X]) (alpha gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * E + C (2 / 9 : k) * H ^ 2 * b ^ 2 +
    C (4 / 9 : k) * A * C0 - C (4 / 81 : k) * A ^ 3 +
    C alpha * H * C0 + C (2 / 3 * gamma : k) * H ^ 2 * A +
    C epsilon * H ^ 3

def terminalLowerOneDTwoDot68 (H d : k[X]) : k[X] :=
  C 2 * H * d.derivative - C 3 * H.derivative * d

def terminalLowerOneUTwoDot68 (H U : k[X]) : k[X] :=
  C 2 * H * U.derivative - C 5 * H.derivative * U

/-- Twice the denominator-cleared lower row
`U dD + 2T dE - 2C dV - D dU`.  This is the exact base-polynomial identity
whose transport is not currently exported by the nonsquare source API. -/
def terminalLowerOneCleared68
    (H A b C0 d E : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let U := terminalLowerOneUNumerator68 H A b C0 d alpha gamma
  let T := terminalLowerOneTNumerator68 H A b C0 E alpha gamma epsilon
  let V := terminalVNumerator68 H A b C0 d E alpha gamma epsilon eta
  H ^ 2 * U * terminalLowerOneDTwoDot68 H d +
    C 4 * T * terminalEDerivativeNumerator68 H E -
    C 4 * C0 * terminalVDerivativeNumerator68 H V -
    H ^ 2 * d * terminalLowerOneUTwoDot68 H U

/-- The first local coefficient of the independently cleared lower row is a
nonzero cube of `p₂`; no terminal-row jets enter it. -/
theorem terminalRZeroXZero_lowerOneCleared_thirdDerivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0) :
    (((terminalLowerOneCleared68 H
      (terminalGReducedA68 H r X)
      (terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      alpha gamma epsilon eta).derivative).derivative).derivative.eval a =
        (32 / 3 : k) * (H.derivative.eval a) ^ 4 * (p2.eval a) ^ 3 := by
  simp only [terminalLowerOneCleared68, terminalLowerOneUNumerator68,
    terminalLowerOneTNumerator68, terminalLowerOneDTwoDot68,
    terminalLowerOneUTwoDot68, terminalVDerivativeNumerator68,
    terminalEDerivativeNumerator68, terminalVNumerator68,
    terminalGReducedA68, terminalGReducedB68, terminalGReducedC68,
    terminalGReducedD68, terminalGReducedE68, derivative_add,
    derivative_sub, derivative_neg, derivative_mul, derivative_pow,
    derivative_C, derivative_ofNat, C_ofNat_poly, eval_add, eval_sub,
    eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero, ha, hr,
    hx, hy, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
  ring

theorem terminalRZeroXZero_impossible_of_lowerOneCleared_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlower : terminalLowerOneCleared68 H
      (terminalGReducedA68 H r X)
      (terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      alpha gamma epsilon eta = 0) : False := by
  have hzero :
      (((terminalLowerOneCleared68 H
        (terminalGReducedA68 H r X)
        (terminalGReducedB68 r X Yd)
        (terminalGReducedC68 H r X Yd p2)
        (terminalGReducedD68 H r X Yd p1 p2)
        (terminalGReducedE68 H r X Yd p0 p1 p2)
        alpha gamma epsilon eta).derivative).derivative).derivative.eval a = 0 := by
    rw [hlower, derivative_zero, derivative_zero, derivative_zero, eval_zero]
  rw [terminalRZeroXZero_lowerOneCleared_thirdDerivative_factor_68
    H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr hx hy] at hzero
  have hne : (32 / 3 : k) * (H.derivative.eval a) ^ 4 *
      (p2.eval a) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hh))
      (pow_ne_zero 3 hu)
  exact hne hzero

end TerminalLowerOneClearing68

section TerminalLowerOneSourceBoundary68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

/-- The source API does expose the exact independent row in the quadratic
extension.  What is missing is solely its denominator-cleared polynomial
transport to `terminalLowerOneCleared68`. -/
theorem NonsquareAlignedSourceCurveData68.terminalLowerOneRawSourceIdentity
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    let ck := algebraMap k F68
    let d := quadraticDerivation46 H
    let T := integratedT68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) (ck S.epsilon)
    let U := integratedU68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) 0 0
    let V := integratedV68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) 0 (ck S.epsilon) (ck S.eta)
    U * d S.D + 2 * T * d S.E - 2 * S.C0 * d V - S.D * d U = 0 := by
  exact (S.residualPacket).2.2.2.1

/-- Exact missing API, stated as a proposition over the actual source
coordinates rather than as an axiom. -/
def NonsquareAlignedSourceCurveData68.TerminalLowerOneClearedTransport
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r X Yd : k[X]) : Prop :=
  terminalLowerOneCleared68 H
    (terminalGReducedA68 H r X)
    (terminalGReducedB68 r X Yd)
    (terminalGReducedC68 H r X Yd (p.coeff 2))
    (terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2))
    (terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2))
    S.alpha S.gamma S.epsilon S.eta = 0

/-- Once the precise missing transport is supplied, the independently
available lower row closes every nonzero-`W` terminal residual immediately. -/
theorem NonsquareAlignedSourceCurveData68.terminalResidual_impossible_of_lowerOneTransport
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    {r X Yd : k[X]} (htransport : S.TerminalLowerOneClearedTransport H r X Yd)
    (a : k) (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : (p.coeff 2).eval a ≠ 0) :
    False := by
  exact terminalRZeroXZero_impossible_of_lowerOneCleared_68
    H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.alpha S.gamma S.epsilon S.eta a ha hr hx hy hh hu htransport

end TerminalLowerOneSourceBoundary68

end Max11DegreeRoutes
