import Sol68ScaleTwoAlignedNonsquareTerminalGNextScratch

/-! # The mixed-root residual after terminal G deletion -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section TerminalRZeroJetAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalRZeroI4Jet68
    (h x y u rd v : k) : k :=
  -h * y ^ 3 - 1458 * h * x * y * u - 59049 * rd * u ^ 2 +
    177147 * h * u * v

def terminalRZeroLastJet68
    (h u rd v : k) : k :=
  (-rd * u + 3 * h * v) * h ^ 2 * u ^ 2

/-- A root on the `r=0`, `b₁≠0` side of the mixed allocation is forced
onto one exact first-jet component. -/
theorem terminalRZero_nonzeroB_firstJetPacket_68
    (h x y u rd v : k) (hh : h ≠ 0) (hy : y ≠ 0)
    (hI : terminalRZeroI4Jet68 h x y u rd v = 0)
    (hL : terminalRZeroLastJet68 h u rd v = 0) :
    u ≠ 0 ∧ -rd * u + 3 * h * v = 0 ∧ y ^ 2 + 1458 * x * u = 0 := by
  have hu : u ≠ 0 := by
    intro hu0
    dsimp only [terminalRZeroI4Jet68] at hI
    rw [hu0] at hI
    simp only [mul_zero, zero_pow, OfNat.zero_ne_ofNat, add_zero] at hI
    have hy3 : y ^ 3 ≠ 0 := pow_ne_zero 3 hy
    exact (mul_ne_zero hh hy3) (by linear_combination -hI)
  have hlin : -rd * u + 3 * h * v = 0 := by
    dsimp only [terminalRZeroLastJet68] at hL
    rcases mul_eq_zero.mp hL with hleft | hu2
    · exact (mul_eq_zero.mp hleft).resolve_right (pow_ne_zero 2 hh)
    · exact (pow_ne_zero 2 hu hu2).elim
  refine ⟨hu, hlin, ?_⟩
  dsimp only [terminalRZeroI4Jet68] at hI
  have hfac : h * y * (y ^ 2 + 1458 * x * u) = 0 := by
    linear_combination -hI + 59049 * u * hlin
  exact (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero hh hy)

end TerminalRZeroJetAlgebra68

section TerminalRZeroReducedRows68

variable {k : Type*} [Field k] [CharZero k]

/-- First derivative of the quotient `I₄` row on `r(a)=0`. -/
theorem terminalRZero_reduced_I4_derivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0) :
    ((terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2).derivative).eval a =
      (8 / 531441 : k) * terminalRZeroI4Jet68
        (H.derivative.eval a) (X.eval a) (Yd.eval a) (p2.eval a)
        (r.derivative.eval a) (p1.eval a) := by
  simp only [terminalGReducedB68, terminalGReducedPhi68,
    terminalGReducedW68, terminalGReducedD68, terminalRZeroI4Jet68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, ha, hr, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
  ring

/-- The first last-row derivative is identically zero here; the second is the
first informative coefficient. -/
theorem terminalRZero_reduced_lastRow_secondDerivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0) :
    let b := terminalGReducedB68 r X Yd
    let d := terminalGReducedD68 H r X Yd p1 p2
    let w := terminalGReducedW68 H r X Yd p2 gamma
    let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
    let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
      alpha gamma epsilon eta
    (((b * w * eDot - d * k1).derivative).derivative).eval a =
      (8 / 27 : k) * terminalRZeroLastJet68
        (H.derivative.eval a) (p2.eval a) (r.derivative.eval a)
        (p1.eval a) := by
  dsimp only
  simp only [terminalGReducedKOne68, terminalGReducedEDot68,
    terminalGReducedA68, terminalGReducedB68, terminalGReducedC68,
    terminalGReducedD68, terminalGReducedE68, terminalGReducedW68,
    terminalGReducedPhi68, terminalKDotNext68,
    terminalCShiftNumerator68, terminalVNumerator68,
    terminalKDotLoadQuotient68, terminalEDerivativeNumerator68,
    terminalRZeroLastJet68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hr, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

/-- Exact reduced-source packet for the only genuinely mixed local branch.
It shows why the first allocation argument does not yet globalize: the branch
survives only on a rigid codimension-three first-jet locus. -/
theorem terminalRZero_reduced_nonzeroB_packet_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta j a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0)
    (hb : (terminalGReducedB68 r X Yd).eval a ≠ 0)
    (hI4 : terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2 = 0)
    (hrow :
      let b := terminalGReducedB68 r X Yd
      let d := terminalGReducedD68 H r X Yd p1 p2
      let w := terminalGReducedW68 H r X Yd p2 gamma
      let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
      let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
        alpha gamma epsilon eta
      b * w * eDot - d * k1 = C j * H ^ 5) :
    p2.eval a ≠ 0 ∧
      -r.derivative.eval a * p2.eval a +
          3 * H.derivative.eval a * p1.eval a = 0 ∧
      (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0 := by
  have hy : Yd.eval a ≠ 0 := by
    intro hy0
    apply hb
    dsimp only [terminalGReducedB68]
    simp only [eval_mul, eval_sub, eval_C, eval_ofNat, hr, hy0, zero_mul,
      sub_zero, mul_zero]
  have hI4d :
      ((terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2).derivative).eval a = 0 := by
    rw [hI4, derivative_zero, eval_zero]
  have hIfactor := terminalRZero_reduced_I4_derivative_factor_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr
  rw [hI4d] at hIfactor
  have hIzero : terminalRZeroI4Jet68
      (H.derivative.eval a) (X.eval a) (Yd.eval a) (p2.eval a)
      (r.derivative.eval a) (p1.eval a) = 0 := by
    have hc : (8 / 531441 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hIfactor.symm).resolve_left hc
  dsimp only at hrow
  have hrow2 :
      ((((terminalGReducedB68 r X Yd *
          terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedEDot68 H r X Yd p0 p1 p2 -
        terminalGReducedD68 H r X Yd p1 p2 *
          terminalGReducedKOne68 H r X Yd p0 p1 p2
            alpha gamma epsilon eta).derivative).derivative).eval a) = 0 := by
    have hd := congrArg (fun f : k[X] => f.derivative.derivative.eval a) hrow
    simpa [derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_C, derivative_ofNat, C_ofNat_poly, ha] using hd
  have hLfactor := terminalRZero_reduced_lastRow_secondDerivative_factor_68
    H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr
  dsimp only at hLfactor
  rw [hrow2] at hLfactor
  have hLzero : terminalRZeroLastJet68
      (H.derivative.eval a) (p2.eval a) (r.derivative.eval a)
      (p1.eval a) = 0 := by
    have hc : (8 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hLfactor.symm).resolve_left hc
  exact terminalRZero_nonzeroB_firstJetPacket_68
    (H.derivative.eval a) (X.eval a) (Yd.eval a) (p2.eval a)
    (r.derivative.eval a) (p1.eval a) hh hy hIzero hLzero

end TerminalRZeroReducedRows68

end Max11DegreeRoutes
