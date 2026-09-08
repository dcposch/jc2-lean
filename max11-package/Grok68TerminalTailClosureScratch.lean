import Grok68TerminalTailRowTwoScratch
import Grok68ScaleZeroResidualThinScratch
import Grok68VanishingAUniformCertificateScratch

/-! # Closure of the `(6,8)` scale-zero terminal tail

Untracked working note. No tracked file was edited.

Parent `Grok68TerminalTailRowTwoScratch` lands the scalar certificates,
I4/I3 faces at every `t ≥ 0`, compensated `Fc`, row-two `J`
factorisation, `alpha`/`eta` cancellation, `H`-support extra, and the
leading `Q`/`de`/`Y` coefficients.  This file assembles the coefficient
comparison at `max(11n-3g, 2g-3n-2t)-1` (and `Y` at its top on the
meeting cell), split on `5g ? 14n+2t`.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

Exact gain: coefficient assembly on `D>0` (all three cells, including
meeting `Y` at `12n-3g`) and constant-`B` `de`-higher; source-facing
`fiveToSix_terminalTail_cusp_impossible_of_closable68`;
`fiveToSix_largeTerminal_allNonzero_cusp_impossible68`; vanishing-A
open residual; `fiveToSix_terminalTail_impossible68` on both cusp
branches under the iterate drop bounds and the closable-cell split;
`fiveToSix_terminalZero_impossible68` on `n=30` and on source `d=0`
with `n≤120`.
Next unused row: constant-`B` `Q`-higher / meeting I3-at-`deg c=n`
(`ABd`/`ce` convolution, or `ε` mix of `B A'` at `2n-1`).
Residual: beyond-wall constant-`B` cusp with `t ≥ n/2` (including the
`n=60`, `g=180` terminal-zero successor); unaligned `n=90`
staggered support. `IntegratedPolynomialLowerSystem68Exclusion` is
not closed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalTailClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Degree dictionary -/

theorem fiveToSix_terminalTail_window_bounds68
    (n g t : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) :
    2 * n ≤ g ∧ g ≤ 3 * n ∧ g ≤ 4 * n ∧
      1 ≤ 11 * n - 3 * g ∧ 1 ≤ 2 * g - 3 * n - 2 * t := by
  obtain ⟨hw5, hw6⟩ := hwindow
  omega

theorem fiveToSix_terminalTail_Dpos_below_TJ68
    (n g t : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hDpos : g < 3 * n) :
    let D := 3 * n - g
    let Cc := 4 * n - g
    let V := g - 2 * n - t
    let Q := 11 * n - 3 * g
    let TJ := max Q (2 * g - 3 * n - 2 * t)
    let K := TJ - 1
    0 < D ∧ 0 < Cc ∧ 1 ≤ Q ∧ Q ≤ TJ ∧
      2 * n + D < Q ∧
      2 * D + V + 1 < Q ∧
      D + Cc < Q ∧
      V < Q := by
  intro D Cc V Q TJ K
  obtain ⟨hw5, hw6⟩ := hwindow
  have hD : 0 < D := by dsimp only [D]; omega
  have hC : 0 < Cc := by dsimp only [Cc]; omega
  have hQpos : 1 ≤ Q := by dsimp only [Q]; omega
  have hQTJ : Q ≤ TJ := le_max_left _ _
  have hAFc : 2 * n + D < Q := by dsimp only [D, Q]; omega
  have hEx : 2 * D + V + 1 < Q := by dsimp only [D, V, Q]; omega
  have hBc : D + Cc < Q := by dsimp only [D, Cc, Q]; omega
  have hV : V < Q := by dsimp only [V, Q]; omega
  exact ⟨hD, hC, hQpos, hQTJ, hAFc, hEx, hBc, hV⟩

private theorem natDegree_mul_derivative_le_terminalTail68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 0 < v) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (by omega)
  have hmul := natDegree_mul_le.trans (Nat.add_le_add hu hd)
  omega

private theorem natDegree_derivative_mul_le_terminalTail68
    (p q : k[X]) (u v : ℕ)
    (hu : 0 < u) (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (derivative p * q).natDegree ≤ u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hmul := natDegree_mul_le.trans (Nat.add_le_add hd hq)
  omega

/-! ## Translated load remainder -/

set_option maxHeartbeats 8000000 in
theorem fiveToSix_terminalTail_load_rowTwo_split68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 0 0 0
          A B c ((1 / 3 : k) • (A * B) + d) e +
        cubicLoadRowTwoPolynomial68 0 0 0 gamma 0 0 0 0
          A B c ((1 / 3 : k) • (A * B) + d) e +
        cubicLoadRowTwoPolynomial68 0 0 0 0 0 epsilon 0 0
          A B c ((1 / 3 : k) • (A * B) + d) e +
        cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 8000000 in
theorem fiveToSix_terminalTail_load_rowTwo_gamma68 (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 1 0 0 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e =
      (2 / 3 : k) •
        ((2 : k) • (A * derivative d) -
          (2 : k) • (B * derivative c) -
          (2 : k) • (c * derivative B) -
          d * derivative A) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 8000000 in
theorem fiveToSix_terminalTail_load_rowTwo_epsilon68 (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 1 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e =
      (1 / 3 : k) •
        ((2 : k) • (A * derivative B) -
          B * derivative A +
          (6 : k) • derivative d) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 8000000 in
theorem fiveToSix_terminalTail_load_rowTwo_smul_gamma68
    (gamma : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 gamma 0 0 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e =
      gamma • cubicLoadRowTwoPolynomial68 0 0 0 1 0 0 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 8000000 in
theorem fiveToSix_terminalTail_load_rowTwo_smul_epsilon68
    (epsilon : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 epsilon 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e =
      epsilon • cubicLoadRowTwoPolynomial68 0 0 0 0 0 1 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

theorem fiveToSix_terminalTail_load_rowTwo_translated68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      (2 / 3 * gamma : k) •
        ((2 : k) • (A * derivative d) -
          (2 : k) • (B * derivative c) -
          (2 : k) • (c * derivative B) -
          d * derivative A) +
      (1 / 3 * epsilon : k) •
        ((2 : k) • (A * derivative B) -
          B * derivative A +
          (6 : k) • derivative d) := by
  rw [fiveToSix_terminalTail_load_rowTwo_split68,
    cubicLoadRowTwoPolynomial68_alpha_cancel68,
    cubicLoadRowTwoPolynomial68_eta_cancel68,
    fiveToSix_terminalTail_load_rowTwo_smul_gamma68,
    fiveToSix_terminalTail_load_rowTwo_smul_epsilon68,
    fiveToSix_terminalTail_load_rowTwo_gamma68,
    fiveToSix_terminalTail_load_rowTwo_epsilon68]
  simp only [zero_add, add_zero, smul_smul]
  ring

/-! ## Compensated I3 remainder `Rc` -/

theorem fiveToSix_terminalTail_Rc_of_I3_constant68
    (gamma epsilon i3 : k) (A B c d e : k[X])
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rc := R + (9 / 2 * gamma : k) • e
    Rc = (9 / 8 : k) • C i3 - (9 / 4 * epsilon : k) • c +
      (3 / 4 * gamma : k) • B ^ 2 := by
  intro R Rc
  have hI3 :
      cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
          A B c ((1 / 3 : k) • (A * B) + d) e =
        secondaryResidualInvariantThreePolynomial68 A B c d e +
          (2 * epsilon : k) • c + (4 * gamma : k) • e -
            (2 / 3 * gamma : k) • B ^ 2 := by
    simpa using
      (cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates
        gamma epsilon 0 A B c d e)
  have hform :
      secondaryResidualInvariantThreePolynomial68 A B c d e +
          (2 * epsilon : k) • c + (4 * gamma : k) • e -
            (2 / 3 * gamma : k) • B ^ 2 =
        (8 / 9 : k) • R + (2 * epsilon : k) • c +
          (4 * gamma : k) • e - (2 / 3 * gamma : k) • B ^ 2 := by
    dsimp only [R, secondaryResidualInvariantThreePolynomial68]
    module
  have hI3' : (8 / 9 : k) • R + (2 * epsilon : k) • c +
      (4 * gamma : k) • e - (2 / 3 * gamma : k) • B ^ 2 = C i3 := by
    rw [← hform, ← hI3, hi3]
  have hRc : (8 / 9 : k) • Rc =
      (8 / 9 : k) • R + (4 * gamma : k) • e := by
    dsimp only [Rc]
    module
  have hlin : (8 / 9 : k) • Rc =
      C i3 - (2 * epsilon : k) • c + (2 / 3 * gamma : k) • B ^ 2 := by
    linear_combination hRc + hI3'
  have hscale : Rc = (9 / 8 : k) • ((8 / 9 : k) • Rc) := by
    module
  rw [hscale, hlin]
  module

theorem fiveToSix_terminalTail_Rc_natDegree68
    (gamma epsilon i3 : k) (A B c d e : k[X]) (n g : ℕ)
    (hg : 2 * n ≤ g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rc := R + (9 / 2 * gamma : k) • e
    Rc.natDegree ≤ 4 * n - g := by
  intro R Rc
  have h := fiveToSix_terminalTail_Rc_of_I3_constant68 gamma epsilon i3
    A B c d e hi3
  dsimp only [R, Rc] at h ⊢
  rw [h]
  compute_degree
  omega

/-! ## Row-one core and `Y` factorisation -/

def FiveToSixTerminalTailRowOneCore68 (A B c d e : k[X]) : k[X] :=
  (2 : k) • (A ^ 2 * B * derivative d) +
    (2 : k) • (A ^ 2 * derivative B * d) +
    (2 : k) • (A * derivative A * B * d) -
    (6 : k) • (A * c * derivative e) -
    (6 : k) • (A * derivative c * e) -
    (2 : k) • (derivative A * B ^ 2 * c) +
    (3 : k) • (derivative A * d ^ 2) +
    (6 : k) • (c ^ 2 * derivative c) -
    (18 : k) • (e * derivative e)

def FiveToSixTerminalTailRowOneExtra68 (A B c d e : k[X]) : k[X] :=
  -(3 : k) • (B ^ 2 * derivative e) +
    (3 : k) • (B * c * derivative d) +
    (3 : k) • (B * derivative c * d) +
    (9 : k) • (derivative B * c * d)

theorem secondaryResidualRowOnePolynomial68_terminalTail_core_extra68
    (A B c d e : k[X]) :
    secondaryResidualRowOnePolynomial68 A B c d e =
      (-4 / 27 : k) •
        (FiveToSixTerminalTailRowOneCore68 A B c d e +
          FiveToSixTerminalTailRowOneExtra68 A B c d e) := by
  unfold secondaryResidualRowOnePolynomial68
    FiveToSixTerminalTailRowOneCore68
    FiveToSixTerminalTailRowOneExtra68
  congr 1
  module

theorem fiveToSix_terminalTail_rowOne_core_factor68 (A B c d e : k[X]) :
    let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    FiveToSixTerminalTailRowOneCore68 A B c d e =
      -(2 : k) • (A * derivative R) + derivative Y := by
  intro R Y
  let Xc := -(A * B * d) + (3 : k) • (c * e)
  have hsq (p : k[X]) :
      derivative (p ^ 2) = (2 : k) • (p * derivative p) := by
    rw [show p ^ 2 = p * p by ring, derivative_mul,
      show derivative p * p = p * derivative p by ring]
    module
  have hcube (p : k[X]) :
      derivative (p ^ 3) = (3 : k) • (p ^ 2 * derivative p) := by
    rw [show p ^ 3 = p * p ^ 2 by ring, derivative_mul, hsq]
    rw [show derivative p * p ^ 2 = p ^ 2 * derivative p by ring]
    have hm : p * ((2 : k) • (p * derivative p)) =
        (2 : k) • (p ^ 2 * derivative p) := by
      rw [mul_smul_comm]
      congr 1
      ring
    rw [hm]
    module
  have hX : derivative Xc =
      -(derivative A * B * d + A * derivative B * d +
          A * B * derivative d) +
        (3 : k) • (derivative c * e + c * derivative e) := by
    dsimp only [Xc]
    simp only [derivative_add, derivative_neg, derivative_smul,
      derivative_mul, mul_add, add_mul, mul_assoc]
    module
  have hcoreX :
      FiveToSixTerminalTailRowOneCore68 A B c d e =
        -(2 : k) • (A * derivative Xc) -
          (2 : k) • (derivative A * B ^ 2 * c) +
          (3 : k) • (derivative A * d ^ 2) +
          (6 : k) • (c ^ 2 * derivative c) -
          (18 : k) • (e * derivative e) := by
    rw [hX]
    simp only [FiveToSixTerminalTailRowOneCore68]
    rw [show A ^ 2 = A * A by ring]
    simp only [mul_add, mul_sub, add_mul, sub_mul, mul_smul_comm,
      smul_mul_assoc, smul_add, smul_sub, smul_smul, mul_assoc, mul_neg,
      neg_mul, smul_neg, neg_smul, neg_neg]
    module
  have hR : R = Xc - B ^ 2 * c + (3 / 2 : k) • d ^ 2 := by
    dsimp only [R, Xc]
  have hFder : derivative R =
      derivative Xc - derivative (B ^ 2 * c) +
        (3 / 2 : k) • derivative (d ^ 2) := by
    dsimp only [R, Xc]
    simp only [derivative_add, derivative_sub, derivative_smul]
  have hYder : derivative Y =
      -(2 : k) • (derivative A * B ^ 2 * c + A * derivative (B ^ 2 * c)) +
        (3 : k) • (derivative A * d ^ 2 + A * derivative (d ^ 2)) +
        (6 : k) • (c ^ 2 * derivative c) -
        (18 : k) • (e * derivative e) := by
    dsimp only [Y]
    simp only [derivative_add, derivative_sub, derivative_neg,
      derivative_smul, derivative_mul]
    rw [hcube c, hsq e]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, smul_sub,
      smul_smul, mul_add, mul_sub, add_mul, sub_mul, mul_assoc]
    module
  rw [hcoreX, hFder, hYder]
  simp only [mul_add, mul_sub, mul_smul_comm, smul_mul_assoc, smul_add,
    smul_sub, smul_smul, mul_assoc]
  module

theorem fiveToSix_terminalTail_rowOne_cancelled68
    (gamma : k) (A B c d e : k[X]) :
    let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rc := R + (9 / 2 * gamma : k) • e
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    let Extra := FiveToSixTerminalTailRowOneExtra68 A B c d e
    secondaryResidualRowOnePolynomial68 A B c d e +
        (4 / 3 * gamma : k) • (A * derivative e) =
      (-4 / 27 : k) •
        (derivative Y - (2 : k) • (A * derivative Rc) + Extra) := by
  intro R Rc Y Extra
  have hcore :=
    secondaryResidualRowOnePolynomial68_terminalTail_core_extra68 A B c d e
  have hfactor := fiveToSix_terminalTail_rowOne_core_factor68 A B c d e
  have hC :
      FiveToSixTerminalTailRowOneCore68 A B c d e =
        -(2 : k) • (A * derivative Rc) + derivative Y +
          (9 * gamma : k) • (A * derivative e) := by
    have hbase :
        FiveToSixTerminalTailRowOneCore68 A B c d e =
          -(2 : k) • (A * derivative R) + derivative Y := by
      simpa [R, Y] using hfactor
    rw [hbase]
    dsimp only [Rc]
    simp only [derivative_add, derivative_smul, mul_add, mul_smul_comm,
      smul_mul_assoc, smul_add, smul_sub, smul_smul]
    module
  rw [hcore, hC]
  dsimp only [Extra]
  module

/-! ## First coefficient of `J` on `D > 0` -/

theorem fiveToSix_terminalTail_J_coeff_Dpos68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hDpos : g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hi4 : ∃ i4 : k,
      cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    let TJ := max (11 * n - 3 * g) (2 * g - 3 * n - 2 * t)
    J.coeff TJ = 0 := by
  intro J TJ
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let Extra := FiveToSixTerminalTailRowTwoExtra68 A B c d e
  let D := 3 * n - g
  let Cc := 4 * n - g
  let V := g - 2 * n - t
  let Q := 11 * n - 3 * g
  let K := TJ - 1
  obtain ⟨i4, hi4⟩ := hi4
  have harith :=
    fiveToSix_terminalTail_Dpos_below_TJ68 n g t hn hwindow htle hDpos
  rcases harith with ⟨hDpos', hCpos, hQpos, hQTJ, hAFc, hEx, hBc, hVlt⟩
  have hbound {u : ℕ} (hu : u < Q) : u < K + 1 := by
    have : Q ≤ TJ := hQTJ
    omega
  have hsumK {u : ℕ} (hu : u < Q) : u - 1 < K := by
    have := hbound hu
    omega
  have hFcdeg : Fc.natDegree ≤ D := by
    dsimp only [Fc, F, D]
    exact fiveToSix_terminalTail_Fc_natDegree68 gamma epsilon i4 A B c d e
      n g hB hi4
  have hA' : A.natDegree ≤ 2 * n := hA
  have hB' : B.natDegree ≤ D := by dsimp only [D]; exact hB
  have hc' : c.natDegree ≤ Cc := by dsimp only [Cc]; exact hc
  have hd' : d.natDegree ≤ V := by dsimp only [V]; exact hd
  have hBclt : (B * derivative c).natDegree < K :=
    lt_of_le_of_lt
      (natDegree_mul_derivative_le_terminalTail68 B c D Cc hB' hCpos hc')
      (hsumK hBc)
  have hcBlt : (c * derivative B).natDegree < K := by
    have := natDegree_derivative_mul_le_terminalTail68 B c D Cc hDpos'
      hB' hc'
    simpa [mul_comm] using lt_of_le_of_lt this (hsumK hBc)
  have hAB1lt : (derivative A * B).natDegree < K :=
    lt_of_le_of_lt
      (natDegree_derivative_mul_le_terminalTail68 A B (2 * n) D
        (by omega) hA' hB')
      (hsumK hAFc)
  have hAB2lt : (A * derivative B).natDegree < K :=
    lt_of_le_of_lt
      (natDegree_mul_derivative_le_terminalTail68 A B (2 * n) D hA'
        hDpos' hB')
      (hsumK hAFc)
  have hdlt : (derivative d).natDegree < K := by
    have hKpos : 0 < K := by
      have : 1 ≤ Q := hQpos
      have : Q ≤ TJ := hQTJ
      omega
    by_cases hV : V = 0
    · have : d.natDegree ≤ 0 := by omega
      have hd0 : derivative d = 0 := by
        rw [eq_C_of_natDegree_le_zero this, derivative_C]
      simp [hd0]
      exact hKpos
    · have hle : (derivative d).natDegree ≤ V - 1 :=
        (natDegree_derivative_le d).trans (by omega)
      exact lt_of_le_of_lt hle (hsumK hVlt)
  have hAFclt : (A * derivative Fc).natDegree < K := by
    have hdFc : (derivative Fc).natDegree ≤ D - 1 :=
      (natDegree_derivative_le Fc).trans (by omega)
    have hmul := natDegree_mul_le.trans (Nat.add_le_add hA' hdFc)
    have : 2 * n + (D - 1) = 2 * n + D - 1 := by omega
    rw [this] at hmul
    exact lt_of_le_of_lt hmul (hsumK hAFc)
  have hA'Fclt : (derivative A * Fc).natDegree < K :=
    lt_of_le_of_lt
      (natDegree_derivative_mul_le_terminalTail68 A Fc (2 * n) D
        (by omega) hA' hFcdeg)
      (hsumK hAFc)
  have hExlt : Extra.natDegree < K := by
    have hraw := fiveToSix_terminalTail_Extra_natDegree68 A B c d e n g t
      hB hd
    dsimp only [Extra, D, V] at hraw ⊢
    have : 2 * D + V < K := by
      have : 2 * D + V + 1 < Q := hEx
      have : Q ≤ TJ := hQTJ
      omega
    exact lt_of_le_of_lt hraw this
  have hload :=
    fiveToSix_terminalTail_load_rowTwo_translated68 alpha gamma epsilon
      eta A B c d e
  have hsum :
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0 := hrow
  rw [hload] at hsum
  have hcancel :=
    fiveToSix_terminalTail_rowTwo_cancelled68 gamma A B c d e
  have hBc0 : (B * derivative c).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hBclt
  have hcB0 : (c * derivative B).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hcBlt
  have hAB20 : (A * derivative B).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hAB2lt
  have hAB10 : (B * derivative A).coeff K = 0 := by
    simpa [mul_comm] using coeff_eq_zero_of_natDegree_lt hAB1lt
  have hd0 : (derivative d).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hdlt
  have hAdK :
      (secondaryResidualRowTwoPolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative d) -
          (2 / 3 * gamma : k) • (d * derivative A)).coeff K = 0 := by
    have hK := congrArg (fun p : k[X] => p.coeff K) hsum
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_zero,
      hBc0, hcB0, hAB20, hAB10, hd0, mul_zero, add_zero, sub_zero,
      zero_mul, neg_zero] at hK ⊢
    convert hK using 1
    ring
  have hJcomb :
      ((-4 / 27 : k) •
          (-(6 : k) • (A * derivative Fc) +
            (3 : k) • (derivative A * Fc) +
            (6 : k) • derivative J + Extra)).coeff K = 0 := by
    have hcancelK := congrArg (fun p : k[X] => p.coeff K) hcancel
    have hleft :
        (secondaryResidualRowTwoPolynomial68 A B c d e +
            (4 / 3 * gamma : k) • (A * derivative d) -
            (2 / 3 * gamma : k) • (d * derivative A)).coeff K =
          (secondaryResidualRowTwoPolynomial68 A B c d e).coeff K +
            (4 / 3 * gamma : k) * (A * derivative d).coeff K -
            (2 / 3 * gamma : k) * (d * derivative A).coeff K := by
      simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
    rw [← hcancelK]
    simpa [hleft] using hAdK
  have hAFc0 : (A * derivative Fc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hAFclt
  have hA'Fc0 : (derivative A * Fc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hA'Fclt
  have hEx0 : Extra.coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hExlt
  have hJ' : (derivative J).coeff K = 0 := by
    have hexp :
        ((-4 / 27 : k) •
            (-(6 : k) • (A * derivative Fc) +
              (3 : k) • (derivative A * Fc) +
              (6 : k) • derivative J + Extra)).coeff K =
          (-4 / 27 : k) *
            (-(6 : k) * (A * derivative Fc).coeff K +
              (3 : k) * (derivative A * Fc).coeff K +
              (6 : k) * (derivative J).coeff K + Extra.coeff K) := by
      simp only [coeff_add, coeff_smul, smul_eq_mul]
    have hred :
        (-4 / 27 : k) *
            (-(6 : k) * (A * derivative Fc).coeff K +
              (3 : k) * (derivative A * Fc).coeff K +
              (6 : k) * (derivative J).coeff K + Extra.coeff K) =
          (-4 / 27 : k) * ((6 : k) * (derivative J).coeff K) := by
      rw [hAFc0, hA'Fc0, hEx0]
      ring
    rw [hexp, hred] at hJcomb
    have h427 : (-4 / 27 : k) ≠ 0 := by norm_num
    have h6 : (6 : k) ≠ 0 := by norm_num
    have hJ6 : (6 : k) * (derivative J).coeff K = 0 :=
      (mul_eq_zero.mp hJcomb).resolve_left h427
    exact (mul_eq_zero.mp hJ6).resolve_left h6
  have hder : (derivative J).coeff K = ((K : k) + 1) * J.coeff (K + 1) := by
    rw [coeff_derivative, mul_comm]
  have hcast : ((K : k) + 1) ≠ 0 := by
    have hk : K + 1 ≠ 0 := by
      dsimp only [K, TJ]
      have : 1 ≤ Q := hQpos
      have : Q ≤ TJ := hQTJ
      omega
    have hc : ((K + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast hk
    push_cast at hc
    exact hc
  rw [hder] at hJ'
  have hJ0 : J.coeff (K + 1) = 0 :=
    (mul_eq_zero.mp hJ').resolve_left hcast
  have hK1 : K + 1 = TJ := by
    dsimp only [K]; omega
  rwa [hK1] at hJ0

/-! ## Chamber comparison on `D > 0` -/

theorem fiveToSix_terminalTail_Qhigher_false68
    (A B c d e : k[X]) (n g t : ℕ)
    (hQ : 5 * g < 14 * n + 2 * t)
    (hg : g ≤ 3 * n) (htle : 2 * n + t ≤ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hcusp : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hJ : ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
        (3 : k) • (d * e)).coeff (11 * n - 3 * g) = 0) :
    False := by
  have hde_lt : 2 * g - 3 * n - 2 * t < 11 * n - 3 * g := by omega
  have hdetop : (d * e).coeff (11 * n - 3 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by
      have := (natDegree_mul_le (p := d) (q := e)).trans
        (Nat.add_le_add hd he)
      have : (g - 2 * n - t) + (g - n - t) = 2 * g - 3 * n - 2 * t := by
        omega
      omega)
  have hQtop := fiveToSix_terminalTail_Q_coeff68 A B c n g hg hA hB hc
  have hQ0 :
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (1 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 = 0 := by
    have hJexp :
        ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
            (3 : k) • (d * e)).coeff (11 * n - 3 * g) =
          (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)).coeff (11 * n - 3 * g) -
            (3 : k) * (d * e).coeff (11 * n - 3 * g) := by
      simp only [coeff_sub, coeff_smul, smul_eq_mul]
    rw [hJexp, hdetop, mul_zero, sub_zero, hQtop] at hJ
    exact hJ
  exact fiveToSix_terminalTail_Q_cusp_false68
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    hb hc0 hcusp hQ0

theorem fiveToSix_terminalTail_Q_natDegree68
    (A B c : k[X]) (n g : ℕ)
    (hg : g ≤ 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)).natDegree ≤
      11 * n - 3 * g := by
  have hc2 : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    have h := (natDegree_pow (p := c) (n := 2)).le
    have : 2 * c.natDegree ≤ 2 * (4 * n - g) :=
      Nat.mul_le_mul_left 2 hc
    omega
  have hBc2 : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have := (natDegree_mul_le (p := B) (q := c ^ 2)).trans
      (Nat.add_le_add hB hc2)
    have : (3 * n - g) + 2 * (4 * n - g) = 11 * n - 3 * g := by omega
    omega
  have hB3 : (B ^ 3).natDegree ≤ 3 * (3 * n - g) := by
    have h := (natDegree_pow (p := B) (n := 3)).le
    have : 3 * B.natDegree ≤ 3 * (3 * n - g) :=
      Nat.mul_le_mul_left 3 hB
    omega
  have hAB3 : (A * B ^ 3).natDegree ≤ 11 * n - 3 * g := by
    have := (natDegree_mul_le (p := A) (q := B ^ 3)).trans
      (Nat.add_le_add hA hB3)
    have : 2 * n + 3 * (3 * n - g) = 11 * n - 3 * g := by omega
    omega
  exact (natDegree_sub_le _ _).trans
    (max_le hBc2 ((natDegree_smul_le _ _).trans hAB3))

theorem fiveToSix_terminalTail_deHigher_false68
    (A B c d e : k[X]) (n g t : ℕ)
    (hde : 14 * n + 2 * t < 5 * g)
    (hg : g ≤ 3 * n) (htle : 2 * n + t ≤ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hd0 : d.coeff (g - 2 * n - t) ≠ 0)
    (he0 : e.coeff (g - n - t) ≠ 0)
    (hJ : ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
        (3 : k) • (d * e)).coeff (2 * g - 3 * n - 2 * t) = 0) :
    False := by
  have hQlt : 11 * n - 3 * g < 2 * g - 3 * n - 2 * t := by omega
  have hQtop :
      (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)).coeff
          (2 * g - 3 * n - 2 * t) = 0 :=
    coeff_eq_zero_of_natDegree_lt
      ((fiveToSix_terminalTail_Q_natDegree68 A B c n g hg hA hB hc).trans_lt
        hQlt)
  have hdetop := fiveToSix_terminalTail_de_coeff68 d e n g t (by omega) hd he
  have hde0 : (3 : k) * d.coeff (g - 2 * n - t) *
      e.coeff (g - n - t) = 0 := by
    have hJexp :
        ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
            (3 : k) • (d * e)).coeff (2 * g - 3 * n - 2 * t) =
          (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)).coeff
              (2 * g - 3 * n - 2 * t) -
            (3 : k) * (d * e).coeff (2 * g - 3 * n - 2 * t) := by
      simp only [coeff_sub, coeff_smul, smul_eq_mul]
    rw [hJexp, hQtop, hdetop, zero_sub] at hJ
    linear_combination -hJ
  have h3 : (3 : k) ≠ 0 := by norm_num
  have hde0' : (3 : k) * (d.coeff (g - 2 * n - t) *
      e.coeff (g - n - t)) = 0 := by
    convert hde0 using 1
    ring
  have hprod : d.coeff (g - 2 * n - t) * e.coeff (g - n - t) = 0 :=
    (mul_eq_zero.mp hde0').resolve_left h3
  exact hd0 ((mul_eq_zero.mp hprod).resolve_right he0)

/-! ## `D>0` cusp at offset `t`, excluding the meeting cell -/

theorem fiveToSix_terminalTail_Dpos_strict_false68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hDpos : g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (g - 2 * n - t) ≠ 0)
    (he0 : e.coeff (g - n - t) ≠ 0)
    (hcusp : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (huneq : 5 * g ≠ 14 * n + 2 * t)
    (hi4 : ∃ i4 : k,
      cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hJ0 :=
    fiveToSix_terminalTail_J_coeff_Dpos68 alpha gamma epsilon eta A B c d e
      n g t hn hwindow htle hDpos hA hB hc hd he hi4 hrow
  have hg : g ≤ 3 * n := by omega
  have htle' : 2 * n + t ≤ g := by omega
  by_cases hQ : 5 * g < 14 * n + 2 * t
  · have hTJ : max (11 * n - 3 * g) (2 * g - 3 * n - 2 * t) =
        11 * n - 3 * g := max_eq_left (Nat.le_of_lt (by omega))
    rw [hTJ] at hJ0
    exact fiveToSix_terminalTail_Qhigher_false68 A B c d e n g t hQ hg
      htle' hA hB hc hd he hb hc0 hcusp hJ0
  · have hde : 14 * n + 2 * t < 5 * g := by omega
    have hTJ : max (11 * n - 3 * g) (2 * g - 3 * n - 2 * t) =
        2 * g - 3 * n - 2 * t := max_eq_right (Nat.le_of_lt (by omega))
    rw [hTJ] at hJ0
    exact fiveToSix_terminalTail_deHigher_false68 A B c d e n g t hde hg
      htle' hA hB hc hd he hd0 he0 hJ0

/-! ## Source-facing extraction -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalTail_system_rowTwo68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hzeta : zeta = 0) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧
      secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
  intro n Ae Be Ce ce De Ee ee d
  have hgt3 : 3 * n < 2 * cubicDefectGap68 n Be ce De ee := by
    have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have : 5 * n < 2 * cubicDefectGap68 n Be ce De ee := by
      simpa [n, Ae, Be, Ce, ce, De, Ee, ee] using hglobal.1
    omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by simpa [n, Ae, Be, Ce, ce, De, Ee, ee] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n (cubicDefectGap68 n Be ce De ee) Ae Be ce De ee at data
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hwindow : 5 * n < 2 * cubicDefectGap68 n Be ce De ee ∧
      2 * cubicDefectGap68 n Be ce De ee ≤ 6 * n := by
    have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    exact ⟨hglobal.1, hglobal.2.1⟩
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n
      (cubicDefectGap68 n Be ce De ee) data.hn data.hg hwindow.1 data.hA
      data.hB data.hc data.hD data.he data.ha hI4
  have hrow :=
    fiveToSix_terminalTail_expanded_rowTwo68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys
  rw [hl, hbeta, hdelta, hzeta] at hrow
  exact ⟨hl, hbeta, hdelta, hrow⟩

/-! ## Meeting cell: `Y` at `12n-3g` on `D>0` -/

theorem fiveToSix_terminalTail_Extra1_natDegree68
    (A B c d e : k[X]) (n g t : ℕ)
    (hg : g ≤ 3 * n) (htle : 2 * n + t ≤ g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (FiveToSixTerminalTailRowOneExtra68 A B c d e).natDegree ≤
      5 * n - g - t := by
  unfold FiveToSixTerminalTailRowOneExtra68
  have hB2 : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    have h := (natDegree_pow (p := B) (n := 2)).le
    have : 2 * B.natDegree ≤ 2 * (3 * n - g) :=
      Nat.mul_le_mul_left 2 hB
    omega
  have he' : (derivative e).natDegree ≤ g - n - t := by
    have := natDegree_derivative_le e
    omega
  have h1 : (B ^ 2 * derivative e).natDegree ≤
      2 * (3 * n - g) + (g - n - t) :=
    (natDegree_mul_le).trans (Nat.add_le_add hB2 he')
  have hd' : (derivative d).natDegree ≤ g - 2 * n - t := by
    have := natDegree_derivative_le d
    omega
  have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
    (natDegree_mul_le).trans (Nat.add_le_add hB hc)
  have h2 : (B * c * derivative d).natDegree ≤
      (3 * n - g) + (4 * n - g) + (g - 2 * n - t) :=
    (natDegree_mul_le).trans (Nat.add_le_add hBc hd')
  have hc' : (derivative c).natDegree ≤ 4 * n - g := by
    have := natDegree_derivative_le c
    omega
  have hBdc : (B * derivative c).natDegree ≤
      (3 * n - g) + (4 * n - g) :=
    (natDegree_mul_le).trans (Nat.add_le_add hB hc')
  have h3 : (B * derivative c * d).natDegree ≤
      (3 * n - g) + (4 * n - g) + (g - 2 * n - t) :=
    (natDegree_mul_le).trans (Nat.add_le_add hBdc hd)
  have hBder : (derivative B).natDegree ≤ 3 * n - g := by
    have := natDegree_derivative_le B
    omega
  have hBcd : (derivative B * c).natDegree ≤
      (3 * n - g) + (4 * n - g) :=
    (natDegree_mul_le).trans (Nat.add_le_add hBder hc)
  have h4 : (derivative B * c * d).natDegree ≤
      (3 * n - g) + (4 * n - g) + (g - 2 * n - t) :=
    (natDegree_mul_le).trans (Nat.add_le_add hBcd hd)
  have hsum1 : 2 * (3 * n - g) + (g - n - t) = 5 * n - g - t := by omega
  have hsum2 : (3 * n - g) + (4 * n - g) + (g - 2 * n - t) =
      5 * n - g - t := by omega
  rw [hsum1] at h1
  rw [hsum2] at h2 h3 h4
  have hs1 := (natDegree_smul_le (-(3 : k)) _).trans h1
  have hs2 := (natDegree_smul_le (3 : k) _).trans h2
  have hs3 := (natDegree_smul_le (3 : k) _).trans h3
  have hs4 := (natDegree_smul_le (9 : k) _).trans h4
  exact (natDegree_add_le _ _).trans
    (max_le ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hs1 hs2)) hs3)) hs4)

set_option maxHeartbeats 8000000 in
theorem fiveToSix_terminalTail_load_rowOne_translated68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) :
    cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      (2 / 3 * gamma : k) •
        (B * derivative ((1 / 3 : k) • (A * B) + d) -
          ((1 / 3 : k) • (A * B) + d) * derivative B) +
      (4 / 3 * gamma : k) • (A * derivative e) -
      (4 / 3 * gamma : k) • (c * derivative c) +
      (2 / 3 * epsilon : k) • (A * derivative c) +
      (2 * epsilon : k) • derivative e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

theorem fiveToSix_terminalTail_D0_natDegree68
    (A B d : k[X]) (n g t : ℕ)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t) :
    ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hAB : (A * B).natDegree ≤ 5 * n - g := by
    have := (natDegree_mul_le (p := A) (q := B)).trans
      (Nat.add_le_add hA hB)
    have : 2 * n + (3 * n - g) = 5 * n - g := by omega
    omega
  have hABs : ((1 / 3 : k) • (A * B)).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans hAB
  have hd' : d.natDegree ≤ 5 * n - g := by
    have : g - 2 * n - t ≤ 5 * n - g := by omega
    omega
  exact (natDegree_add_le _ _).trans (max_le hABs hd')

theorem fiveToSix_terminalTail_Y_coeff_Dpos_meeting68
    (alpha gamma epsilon eta i3 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hDpos : g < 3 * n)
    (hmeet : 5 * g = 14 * n + 2 * t)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    let TY := 12 * n - 3 * g
    Y.coeff TY = 0 := by
  intro Y TY
  let D0 := (1 / 3 : k) • (A * B) + d
  let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2
  let Rc := R + (9 / 2 * gamma : k) • e
  let Extra := FiveToSixTerminalTailRowOneExtra68 A B c d e
  let D := 3 * n - g
  let Cc := 4 * n - g
  let K := TY - 1
  have hg2 : 2 * n ≤ g := by
    obtain ⟨hw5, hw6⟩ := hwindow
    omega
  have hTYpos : 1 ≤ TY := by
    dsimp only [TY]
    omega
  have hKpos : 0 < K := by
    dsimp only [K, TY]
    omega
  have hRcdeg : Rc.natDegree ≤ 4 * n - g := by
    dsimp only [Rc, R]
    exact fiveToSix_terminalTail_Rc_natDegree68 gamma epsilon i3 A B c d e
      n g hg2 hc hB hi3
  have hD0deg : D0.natDegree ≤ 5 * n - g :=
    fiveToSix_terminalTail_D0_natDegree68 A B d n g t hwindow htle hA hB hd
  have hbelow {u : ℕ} (hu : u < TY) : u < K + 1 := by
    dsimp only [K]
    omega
  have hsumK {u : ℕ} (hu : u < TY) : u - 1 < K := by
    have := hbelow hu
    omega
  have hARc : 2 * n + Cc < TY := by
    dsimp only [Cc, TY]
    omega
  have hEx1 : 5 * n - g - t + 1 < TY := by
    dsimp only [TY]
    omega
  have hBD0 : D + (5 * n - g) < TY := by
    dsimp only [D, TY]
    omega
  have hcc : 2 * Cc < TY := by
    dsimp only [Cc, TY]
    omega
  have hAc : 2 * n + Cc < TY := hARc
  have heK : g - n - t < TY := by
    dsimp only [TY]
    omega
  have hARclt : (A * derivative Rc).natDegree < K := by
    have hdRc : (derivative Rc).natDegree ≤ Cc - 1 :=
      (natDegree_derivative_le Rc).trans (by
        dsimp only [Cc]; omega)
    have hmul := natDegree_mul_le.trans (Nat.add_le_add hA hdRc)
    have : 2 * n + (Cc - 1) = 2 * n + Cc - 1 := by
      dsimp only [Cc]; omega
    rw [this] at hmul
    exact lt_of_le_of_lt hmul (hsumK hARc)
  have hExlt : Extra.natDegree < K := by
    have hg : g ≤ 3 * n := by omega
    have htle' : 2 * n + t ≤ g := by omega
    have hraw := fiveToSix_terminalTail_Extra1_natDegree68 A B c d e n g t
      hg htle' hB hc hd he
    dsimp only [Extra] at hraw ⊢
    have : 5 * n - g - t < K := by
      have : 5 * n - g - t + 1 < TY := hEx1
      dsimp only [K]
      omega
    exact lt_of_le_of_lt hraw this
  have hBD0lt :
      (B * derivative ((1 / 3 : k) • (A * B) + d)).natDegree < K := by
    have hDpos' : 0 < 5 * n - g := by
      obtain ⟨hw5, hw6⟩ := hwindow
      omega
    have := natDegree_mul_derivative_le_terminalTail68 B D0 D (5 * n - g)
      (by dsimp only [D]; exact hB) hDpos' hD0deg
    have hsum : D + (5 * n - g) - 1 < K := by
      have : D + (5 * n - g) < TY := hBD0
      dsimp only [K]
      omega
    simpa [D0] using (lt_of_le_of_lt this (by omega))
  have hD0Blt :
      (((1 / 3 : k) • (A * B) + d) * derivative B).natDegree < K := by
    have hDpos' : 0 < D := by dsimp only [D]; omega
    have := natDegree_derivative_mul_le_terminalTail68 B D0 D (5 * n - g)
      hDpos' (by dsimp only [D]; exact hB) hD0deg
    simpa [D0, mul_comm] using (lt_of_le_of_lt this (hsumK hBD0))
  have hcclt : (c * derivative c).natDegree < K := by
    have hCpos : 0 < Cc := by dsimp only [Cc]; omega
    have := natDegree_mul_derivative_le_terminalTail68 c c Cc Cc hc hCpos hc
    have : 2 * Cc - 1 < K := by
      have : 2 * Cc < TY := hcc
      dsimp only [K]
      omega
    omega
  have hAclt : (A * derivative c).natDegree < K :=
    lt_of_le_of_lt
      (natDegree_mul_derivative_le_terminalTail68 A c (2 * n) Cc hA
        (by dsimp only [Cc]; omega) hc)
      (hsumK hAc)
  have helt : (derivative e).natDegree < K := by
    by_cases hE : g - n - t = 0
    · have : e.natDegree ≤ 0 := by omega
      have he0 : derivative e = 0 := by
        rw [eq_C_of_natDegree_le_zero this, derivative_C]
      simp [he0]
      exact hKpos
    · have hle : (derivative e).natDegree ≤ g - n - t - 1 :=
        (natDegree_derivative_le e).trans (by omega)
      exact lt_of_le_of_lt hle (hsumK heK)
  have hload :=
    fiveToSix_terminalTail_load_rowOne_translated68 alpha gamma epsilon
      eta A B c d e
  have hsum :
      secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0 := hrow
  rw [hload] at hsum
  have hcancel :=
    fiveToSix_terminalTail_rowOne_cancelled68 gamma A B c d e
  have hBD00 :
      (B * derivative ((1 / 3 : k) • (A * B) + d)).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hBD0lt
  have hD0B0 :
      (((1 / 3 : k) • (A * B) + d) * derivative B).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hD0Blt
  have hcc0 : (c * derivative c).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hcclt
  have hAc0 : (A * derivative c).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hAclt
  have he0 : (derivative e).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt helt
  have hleftK :
      (secondaryResidualRowOnePolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative e)).coeff K = 0 := by
    have hK := congrArg (fun p : k[X] => p.coeff K) hsum
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_zero]
      at hK ⊢
    rw [hBD00, hD0B0, hcc0, hAc0, he0] at hK
    simp only [mul_zero, add_zero, sub_zero, zero_mul, neg_zero] at hK ⊢
    convert hK using 1
    ring
  have hYcomb :
      ((-4 / 27 : k) •
          (derivative Y - (2 : k) • (A * derivative Rc) + Extra)).coeff K =
        0 := by
    have hcancelK := congrArg (fun p : k[X] => p.coeff K) hcancel
    have hleft :
        (secondaryResidualRowOnePolynomial68 A B c d e +
            (4 / 3 * gamma : k) • (A * derivative e)).coeff K =
          (secondaryResidualRowOnePolynomial68 A B c d e).coeff K +
            (4 / 3 * gamma : k) * (A * derivative e).coeff K := by
      simp only [coeff_add, coeff_smul, smul_eq_mul]
    rw [← hcancelK]
    simpa [hleft] using hleftK
  have hARc0 : (A * derivative Rc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hARclt
  have hEx0 : Extra.coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hExlt
  have hY' : (derivative Y).coeff K = 0 := by
    have hexp :
        ((-4 / 27 : k) •
            (derivative Y - (2 : k) • (A * derivative Rc) + Extra)).coeff K =
          (-4 / 27 : k) *
            ((derivative Y).coeff K -
              (2 : k) * (A * derivative Rc).coeff K + Extra.coeff K) := by
      simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
    have hred :
        (-4 / 27 : k) *
            ((derivative Y).coeff K -
              (2 : k) * (A * derivative Rc).coeff K + Extra.coeff K) =
          (-4 / 27 : k) * (derivative Y).coeff K := by
      rw [hARc0, hEx0]
      ring
    rw [hexp, hred] at hYcomb
    have h427 : (-4 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hYcomb).resolve_left h427
  have hder : (derivative Y).coeff K = ((K : k) + 1) * Y.coeff (K + 1) := by
    rw [coeff_derivative, mul_comm]
  have hcast : ((K : k) + 1) ≠ 0 := by
    have hk : K + 1 ≠ 0 := by
      dsimp only [K, TY]
      omega
    have hc : ((K + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast hk
    push_cast at hc
    exact hc
  rw [hder] at hY'
  have hY0 : Y.coeff (K + 1) = 0 :=
    (mul_eq_zero.mp hY').resolve_left hcast
  have hK1 : K + 1 = TY := by
    dsimp only [K]; omega
  rwa [hK1] at hY0

theorem fiveToSix_terminalTail_meeting_false68
    (alpha gamma epsilon eta i3 i4 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hDpos : g < 3 * n)
    (hmeet : 5 * g = 14 * n + 2 * t)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (g - 2 * n - t) ≠ 0)
    (he0 : e.coeff (g - n - t) ≠ 0)
    (hcusp : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hg : g ≤ 3 * n := by omega
  have htle' : 2 * n + t ≤ g := by omega
  have hJ0raw :=
    fiveToSix_terminalTail_J_coeff_Dpos68 alpha gamma epsilon eta A B c d e
      n g t hn hwindow htle hDpos hA hB hc hd he ⟨i4, hi4⟩ hrow2
  have hTJ : max (11 * n - 3 * g) (2 * g - 3 * n - 2 * t) =
      11 * n - 3 * g := by
    apply max_eq_left
    omega
  have hJ0 :
      ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
          (3 : k) • (d * e)).coeff (11 * n - 3 * g) = 0 := by
    dsimp only at hJ0raw
    rwa [hTJ] at hJ0raw
  have hQtop := fiveToSix_terminalTail_Q_coeff68 A B c n g hg hA hB hc
  have hdetop := fiveToSix_terminalTail_de_coeff68 d e n g t htle' hd he
  have hJlead :
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (1 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 -
        (3 : k) * d.coeff (g - 2 * n - t) * e.coeff (g - n - t) = 0 := by
    have hidx : 2 * g - 3 * n - 2 * t = 11 * n - 3 * g := by omega
    have hJexp :
        ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
            (3 : k) • (d * e)).coeff (11 * n - 3 * g) =
          (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)).coeff (11 * n - 3 * g) -
            (3 : k) * (d * e).coeff (11 * n - 3 * g) := by
      simp only [coeff_sub, coeff_smul, smul_eq_mul]
    have hde' : (d * e).coeff (11 * n - 3 * g) =
        d.coeff (g - 2 * n - t) * e.coeff (g - n - t) := by
      rw [← hidx, hdetop]
    rw [hJexp, hQtop, hde'] at hJ0
    convert hJ0 using 1
    ring
  have hH := fiveToSix_terminalTail_H_face68 gamma epsilon i4 A B c d e
    n g t hn hwindow htle hB hc hd he hi4
  have hY0 :=
    fiveToSix_terminalTail_Y_coeff_Dpos_meeting68 alpha gamma epsilon eta i3
      A B c d e n g t hn hwindow htle hDpos hmeet hA hB hc hd he hi3 hrow1
  have hYtop := fiveToSix_terminalTail_Y_coeff_meeting68 A B c d e n g t
    hmeet hg htle' hA hB hc hd he
  have hYlead :
      -(2 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g) +
        (3 : k) * A.coeff (2 * n) * d.coeff (g - 2 * n - t) ^ 2 +
        (2 : k) * c.coeff (4 * n - g) ^ 3 -
        (9 : k) * e.coeff (g - n - t) ^ 2 = 0 := by
    dsimp only at hY0 hYtop
    rw [hYtop] at hY0
    exact hY0
  exact fiveToSix_terminalTail_leading_jet_false68
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (g - 2 * n - t)) (e.coeff (g - n - t))
    ha hb hc0 hd0 he0 hcusp hH hJlead hYlead

theorem fiveToSix_terminalTail_Dpos_false68
    (alpha gamma epsilon eta i3 i4 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hDpos : g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (g - 2 * n - t) ≠ 0)
    (he0 : e.coeff (g - n - t) ≠ 0)
    (hcusp : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  by_cases huneq : 5 * g ≠ 14 * n + 2 * t
  · exact fiveToSix_terminalTail_Dpos_strict_false68 alpha gamma epsilon eta
      A B c d e n g t hn hwindow htle hDpos hA hB hc hd he ha hb hc0 hd0 he0
      hcusp huneq ⟨i4, hi4⟩ hrow2
  · have hmeet : 5 * g = 14 * n + 2 * t := by omega
    exact fiveToSix_terminalTail_meeting_false68 alpha gamma epsilon eta i3
      i4 A B c d e n g t hn hwindow htle hDpos hmeet hA hB hc hd he ha hb
      hc0 hd0 he0 hcusp hi4 hi3 hrow2 hrow1

/-! ## Constant-`B` `de`-higher cell (`g = 3n`, `t < n/2`) -/

theorem fiveToSix_terminalTail_J_coeff_constantB_deHigher68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hD0 : g = 3 * n)
    (hde : 14 * n + 2 * t < 5 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hi4 : ∃ i4 : k,
      cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    let TJ := 2 * g - 3 * n - 2 * t
    J.coeff TJ = 0 := by
  intro J TJ
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let Extra := FiveToSixTerminalTailRowTwoExtra68 A B c d e
  let Cc := 4 * n - g
  let V := g - 2 * n - t
  let K := TJ - 1
  obtain ⟨i4, hi4⟩ := hi4
  have hB0 : B.natDegree ≤ 0 := by
    have : 3 * n - g = 0 := by omega
    omega
  have hBder : derivative B = 0 := by
    rw [eq_C_of_natDegree_le_zero hB0, derivative_C]
  have hFcdeg : Fc.natDegree ≤ 0 := by
    dsimp only [Fc, F]
    have := fiveToSix_terminalTail_Fc_natDegree68 gamma epsilon i4 A B c d e
      n g hB hi4
    have : 3 * n - g = 0 := by omega
    omega
  have hFcder : derivative Fc = 0 := by
    rw [eq_C_of_natDegree_le_zero hFcdeg, derivative_C]
  have hTJpos : 1 ≤ TJ := by
    dsimp only [TJ]
    omega
  have hKpos : 0 < K := by
    dsimp only [K, TJ]
    omega
  have hCpos : 0 < Cc := by
    dsimp only [Cc]
    omega
  have hBclt : (B * derivative c).natDegree < K := by
    have := natDegree_mul_derivative_le_terminalTail68 B c 0 Cc hB0 hCpos hc
    have : Cc - 1 < K := by
      dsimp only [Cc, K, TJ]
      omega
    omega
  have hcBlt : (c * derivative B).natDegree < K := by
    simp [hBder]
    exact hKpos
  have hAB1lt : (derivative A * B).natDegree < K := by
    have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hmul := natDegree_mul_le.trans (Nat.add_le_add hdA hB0)
    have : 2 * n - 1 < K := by
      dsimp only [K, TJ]
      omega
    omega
  have hAB2lt : (A * derivative B).natDegree < K := by
    simp [hBder]
    exact hKpos
  have hdlt : (derivative d).natDegree < K := by
    by_cases hV : V = 0
    · have : d.natDegree ≤ 0 := by
        dsimp only [V] at hV
        omega
      have hd0 : derivative d = 0 := by
        rw [eq_C_of_natDegree_le_zero this, derivative_C]
      simp [hd0]
      exact hKpos
    · have hle : (derivative d).natDegree ≤ V - 1 :=
        (natDegree_derivative_le d).trans (by
          dsimp only [V]; omega)
      have : V - 1 < K := by
        dsimp only [V, K, TJ]
        omega
      omega
  have hAFclt : (A * derivative Fc).natDegree < K := by
    simp [hFcder]
    exact hKpos
  have hA'Fclt : (derivative A * Fc).natDegree < K := by
    have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hmul := natDegree_mul_le.trans (Nat.add_le_add hdA hFcdeg)
    have : 2 * n - 1 < K := by
      dsimp only [K, TJ]
      omega
    omega
  have hExlt : Extra.natDegree < K := by
    have hraw := fiveToSix_terminalTail_Extra_natDegree68 A B c d e n g t
      hB hd
    dsimp only [Extra] at hraw ⊢
    have : 2 * (3 * n - g) + (g - 2 * n - t) < K := by
      dsimp only [K, TJ]
      omega
    exact lt_of_le_of_lt hraw this
  have hload :=
    fiveToSix_terminalTail_load_rowTwo_translated68 alpha gamma epsilon
      eta A B c d e
  have hsum :
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0 := hrow
  rw [hload] at hsum
  have hcancel :=
    fiveToSix_terminalTail_rowTwo_cancelled68 gamma A B c d e
  have hBc0 : (B * derivative c).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hBclt
  have hcB0 : (c * derivative B).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hcBlt
  have hAB20 : (A * derivative B).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hAB2lt
  have hAB10 : (B * derivative A).coeff K = 0 := by
    simpa [mul_comm] using coeff_eq_zero_of_natDegree_lt hAB1lt
  have hd0 : (derivative d).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hdlt
  have hAdK :
      (secondaryResidualRowTwoPolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative d) -
          (2 / 3 * gamma : k) • (d * derivative A)).coeff K = 0 := by
    have hK := congrArg (fun p : k[X] => p.coeff K) hsum
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_zero,
      hBc0, hcB0, hAB20, hAB10, hd0, mul_zero, add_zero, sub_zero,
      zero_mul, neg_zero] at hK ⊢
    convert hK using 1
    ring
  have hJcomb :
      ((-4 / 27 : k) •
          (-(6 : k) • (A * derivative Fc) +
            (3 : k) • (derivative A * Fc) +
            (6 : k) • derivative J + Extra)).coeff K = 0 := by
    have hcancelK := congrArg (fun p : k[X] => p.coeff K) hcancel
    have hleft :
        (secondaryResidualRowTwoPolynomial68 A B c d e +
            (4 / 3 * gamma : k) • (A * derivative d) -
            (2 / 3 * gamma : k) • (d * derivative A)).coeff K =
          (secondaryResidualRowTwoPolynomial68 A B c d e).coeff K +
            (4 / 3 * gamma : k) * (A * derivative d).coeff K -
            (2 / 3 * gamma : k) * (d * derivative A).coeff K := by
      simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
    rw [← hcancelK]
    simpa [hleft] using hAdK
  have hAFc0 : (A * derivative Fc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hAFclt
  have hA'Fc0 : (derivative A * Fc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hA'Fclt
  have hEx0 : Extra.coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hExlt
  have hJ' : (derivative J).coeff K = 0 := by
    have hexp :
        ((-4 / 27 : k) •
            (-(6 : k) • (A * derivative Fc) +
              (3 : k) • (derivative A * Fc) +
              (6 : k) • derivative J + Extra)).coeff K =
          (-4 / 27 : k) *
            (-(6 : k) * (A * derivative Fc).coeff K +
              (3 : k) * (derivative A * Fc).coeff K +
              (6 : k) * (derivative J).coeff K + Extra.coeff K) := by
      simp only [coeff_add, coeff_smul, smul_eq_mul]
    have hred :
        (-4 / 27 : k) *
            (-(6 : k) * (A * derivative Fc).coeff K +
              (3 : k) * (derivative A * Fc).coeff K +
              (6 : k) * (derivative J).coeff K + Extra.coeff K) =
          (-4 / 27 : k) * ((6 : k) * (derivative J).coeff K) := by
      rw [hAFc0, hA'Fc0, hEx0]
      ring
    rw [hexp, hred] at hJcomb
    have h427 : (-4 / 27 : k) ≠ 0 := by norm_num
    have h6 : (6 : k) ≠ 0 := by norm_num
    have hJ6 : (6 : k) * (derivative J).coeff K = 0 :=
      (mul_eq_zero.mp hJcomb).resolve_left h427
    exact (mul_eq_zero.mp hJ6).resolve_left h6
  have hder : (derivative J).coeff K = ((K : k) + 1) * J.coeff (K + 1) := by
    rw [coeff_derivative, mul_comm]
  have hcast : ((K : k) + 1) ≠ 0 := by
    have hk : K + 1 ≠ 0 := by
      dsimp only [K, TJ]
      omega
    have hc : ((K + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast hk
    push_cast at hc
    exact hc
  rw [hder] at hJ'
  have hJ0 : J.coeff (K + 1) = 0 :=
    (mul_eq_zero.mp hJ').resolve_left hcast
  have hK1 : K + 1 = TJ := by
    dsimp only [K]; omega
  rwa [hK1] at hJ0

theorem fiveToSix_terminalTail_constantB_deHigher_false68
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hD0 : g = 3 * n)
    (hde : 14 * n + 2 * t < 5 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hd0 : d.coeff (g - 2 * n - t) ≠ 0)
    (he0 : e.coeff (g - n - t) ≠ 0)
    (hi4 : ∃ i4 : k,
      cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hJ0 :=
    fiveToSix_terminalTail_J_coeff_constantB_deHigher68 alpha gamma epsilon
      eta A B c d e n g t hn hwindow htle hD0 hde hA hB hc hd he hi4 hrow
  have hg : g ≤ 3 * n := by omega
  have htle' : 2 * n + t ≤ g := by omega
  exact fiveToSix_terminalTail_deHigher_false68 A B c d e n g t hde hg
    htle' hA hB hc hd he hd0 he0 hJ0

/-! ## Source-facing faces, cusp, and named packets -/

theorem fiveToSix_terminalTail_cusp_indices68
    (n g t : ℕ)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) :
    5 * n - g - (7 * n - 2 * g + t) = g - 2 * n - t ∧
      6 * n - g - (7 * n - 2 * g + t) = g - n - t := by
  obtain ⟨hw5, hw6⟩ := hwindow
  omega

theorem fiveToSix_terminalTail_cusp_A_top68
    (A B c d e : k[X]) (n g s : ℕ)
    (hcusp : FiveToSixCuspEdge68 A B c d e n g s) :
    A.coeff (2 * n) ≠ 0 := by
  intro ha0
  have heq := hcusp.2.2.2.2
  rw [ha0, zero_mul, zero_add] at heq
  have h3 : (3 : k) ≠ 0 := by norm_num
  exact hcusp.2.1
    (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp heq).resolve_left h3))

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalTail_system_faces68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hzeta : zeta = 0) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧
      (∃ i4 : k,
        cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = C i4) ∧
      (∃ i3 : k,
        cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = C i3) ∧
      secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
          cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
            Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 ∧
      secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
          cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
            Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
  intro n Ae Be Ce ce De Ee ee d
  have hpack :=
    fiveToSix_terminalTail_system_rowTwo68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hpack with ⟨hl, hbeta, hdelta, hrow2⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n (cubicDefectGap68 n Be ce De ee) Ae Be ce De ee at data
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta, hdelta, hzeta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta, hzeta, hDrec] at hi3e
  have hrow1 :=
    fiveToSix_terminalTail_expanded_rowOne68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys
  rw [hl, hbeta, hdelta, hzeta] at hrow1
  exact ⟨hl, hbeta, hdelta, ⟨i4, hI4⟩, ⟨i3, hi3e⟩, hrow2, hrow1⟩

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalTail_cusp_impossible_of_closable68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (t : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hzeta : zeta = 0)
    (htle :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      t ≤ g - 2 * n)
    (hd :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ g - 2 * n - t)
    (he :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ee.natDegree ≤ g - n - t)
    (hcusp :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t))
    (hclosable :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < 3 * n ∨ 14 * n + 2 * t < 5 * g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change t ≤ g - 2 * n at htle
  change d.natDegree ≤ g - 2 * n - t at hd
  change ee.natDegree ≤ g - n - t at he
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t) at hcusp
  change g < 3 * n ∨ 14 * n + 2 * t < 5 * g at hclosable
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, ⟨i4, hi4⟩, ⟨i3, hi3⟩, hrow2, hrow1⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hidx := fiveToSix_terminalTail_cusp_indices68 n g t hwindow htle
  have ha : Ae.coeff (2 * n) ≠ 0 :=
    fiveToSix_terminalTail_cusp_A_top68 Ae Be ce d ee n g
      (7 * n - 2 * g + t) hcusp
  have hb : Be.coeff (3 * n - g) ≠ 0 := hcusp.1
  have hc0 : ce.coeff (4 * n - g) ≠ 0 := hcusp.2.1
  have hd0 : d.coeff (g - 2 * n - t) ≠ 0 := by
    rw [← hidx.1]; exact hcusp.2.2.1
  have he0 : ee.coeff (g - n - t) ≠ 0 := by
    rw [← hidx.2]; exact hcusp.2.2.2.1
  have hcuspEq :
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 := hcusp.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := data.hA
  have hB : Be.natDegree ≤ 3 * n - g := data.hB
  have hc : ce.natDegree ≤ 4 * n - g := data.hc
  rcases hclosable with hDpos | hde
  · exact fiveToSix_terminalTail_Dpos_false68 alpha gamma epsilon eta i3 i4
      Ae Be ce d ee n g t data.hn hwindow htle hDpos hA hB hc hd he ha hb
      hc0 hd0 he0 hcuspEq hi4 hi3 hrow2 hrow1
  · have hgle : g ≤ 3 * n := by
      obtain ⟨_, hw6⟩ := hwindow
      omega
    have hD0 : g = 3 * n := by
      have : ¬ g < 3 * n := by
        intro hlt
        exact fiveToSix_terminalTail_Dpos_false68 alpha gamma epsilon eta
          i3 i4 Ae Be ce d ee n g t data.hn hwindow htle hlt hA hB hc hd he
          ha hb hc0 hd0 he0 hcuspEq hi4 hi3 hrow2 hrow1
      omega
    exact fiveToSix_terminalTail_constantB_deHigher_false68 alpha gamma
      epsilon eta Ae Be ce d ee n g t data.hn hwindow htle hD0 hde hA hB hc
      hd he hd0 he0 ⟨i4, hi4⟩ hrow2

set_option maxHeartbeats 25000000 in
theorem fiveToSix_largeTerminal_allNonzero_cusp_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hres :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixLargeTerminalAllNonzeroCuspResidual68 zeta Ae Be ce d ee
        n g) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change FiveToSixLargeTerminalAllNonzeroCuspResidual68 zeta Ae Be ce d ee
    n g at hres
  rcases hres with ⟨_, _, _, hd, he, hzeta, hcusp⟩
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have htle : 0 ≤ g - 2 * n := by
    obtain ⟨hw5, hw6⟩ := hwindow
    omega
  have hclosable : g < 3 * n ∨ 14 * n + 2 * 0 < 5 * g := by
    obtain ⟨hw5, hw6⟩ := hwindow
    by_cases hD : g < 3 * n
    · exact Or.inl hD
    · have : g = 3 * n := by omega
      omega
  have hcusp0 :
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 0) := by
    simpa using hcusp
  exact fiveToSix_terminalTail_cusp_impossible_of_closable68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 0
    hterminal hsys hzeta htle hd he hcusp0 hclosable

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalTail_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hres :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixTerminalTailOpenResidual68 zeta Ae Be ce d ee n g)
    (hdrop :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      ∀ j, 0 < j → 60 * j ≤ g - 2 * n →
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 60 * j) →
          d.natDegree ≤ g - 2 * n - 60 * j ∧
            ee.natDegree ≤ g - n - 60 * j)
    (hclosable :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ∀ t, t ≤ g - 2 * n → g < 3 * n ∨ 14 * n + 2 * t < 5 * g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change FiveToSixTerminalTailOpenResidual68 zeta Ae Be ce d ee n g at hres
  change ∀ j, 0 < j → 60 * j ≤ g - 2 * n →
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 60 * j) →
        d.natDegree ≤ g - 2 * n - 60 * j ∧
          ee.natDegree ≤ g - n - 60 * j at hdrop
  change ∀ t, t ≤ g - 2 * n →
      g < 3 * n ∨ 14 * n + 2 * t < 5 * g at hclosable
  rcases hres with hbeyond | hwall
  · rcases hbeyond with ⟨_, _, hzeta, ⟨j, hjpos, hjle, hcusp⟩⟩
    have hbnd := hdrop j hjpos hjle hcusp
    exact fiveToSix_terminalTail_cusp_impossible_of_closable68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      (60 * j) hterminal hsys hzeta hjle hbnd.1 hbnd.2 hcusp
      (hclosable (60 * j) hjle)
  · rcases hwall with ⟨_, _, _, hd, he, hzeta, hcusp⟩
    have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
      ⟨hglobal.1, hglobal.2.1⟩
    have htle : 0 ≤ g - 2 * n := by
      obtain ⟨hw5, hw6⟩ := hwindow
      omega
    have hcusp0 :
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 0) := by
      simpa using hcusp
    exact fiveToSix_terminalTail_cusp_impossible_of_closable68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 0
      hterminal hsys hzeta htle hd he hcusp0 (hclosable 0 htle)

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_open_impossible68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (h : FiveToSixCuspZetaFirstSupportQZeroVanishingAOpenResidual68 alpha
      gamma epsilon zeta eta terminal A B c d e N G S) :
    False := by
  rcases h with ⟨hloaded, hq, _⟩
  exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_impossible68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal
    (fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S hloaded)
    hq

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hpacket :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixTerminalZeroPacket68 zeta d ee n g)
    (hclosed :
      let n := weightedRadius68 A B C0 D E
      n = 30 ∨
        (secondaryDDefectPolynomial68 A B D = 0 ∧
          n ≤ 120 ∧ 60 ≤ n)) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  change n = 30 ∨
      (secondaryDDefectPolynomial68 A B D = 0 ∧ n ≤ 120 ∧ 60 ≤ n)
    at hclosed
  rcases hclosed with hn30 | ⟨hd0, hnle, hn60⟩
  · exact fiveToSix_terminalZero_n30_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn30
  · have hzeta : zeta = 0 := hpacket.2.2.1
    have hfaces :=
      fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta
        epsilon zeta eta terminal A B C0 D E hterminal hsys hzeta
    exact fiveToSix_terminalZero_source_dZero_le_oneTwenty_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hfaces.1 hfaces.2.1 hfaces.2.2.1 hzeta hd0 hnle hn60

#print axioms fiveToSix_terminalTail_window_bounds68
#print axioms fiveToSix_terminalTail_Dpos_below_TJ68
#print axioms fiveToSix_terminalTail_load_rowTwo_translated68
#print axioms fiveToSix_terminalTail_Rc_of_I3_constant68
#print axioms fiveToSix_terminalTail_rowOne_core_factor68
#print axioms fiveToSix_terminalTail_rowTwo_cancelled68
#print axioms fiveToSix_terminalTail_J_coeff_Dpos68
#print axioms fiveToSix_terminalTail_Qhigher_false68
#print axioms fiveToSix_terminalTail_deHigher_false68
#print axioms fiveToSix_terminalTail_meeting_false68
#print axioms fiveToSix_terminalTail_Dpos_false68
#print axioms fiveToSix_terminalTail_constantB_deHigher_false68
#print axioms fiveToSix_terminalTail_system_faces68
#print axioms fiveToSix_terminalTail_cusp_impossible_of_closable68
#print axioms fiveToSix_largeTerminal_allNonzero_cusp_impossible68
#print axioms fiveToSix_terminalTail_impossible68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_open_impossible68
#print axioms fiveToSix_terminalZero_impossible68

end FiveToSixTerminalTailClosure68

end Max11DegreeRoutes

