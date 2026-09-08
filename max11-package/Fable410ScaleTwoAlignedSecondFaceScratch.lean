import Fable410ScaleTwoAlignedFaceScratch

/-! # Second aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedFaceScratch` opened the aligned face `N = 0` of
the normalized scale-two `(4,10)` source and consumed the degree-`11`
Keller row: `q₉ = (5/2) p₃ H³` solved the face, the weight-four defect
`M = 8 q₈ - 20 p₂ H³ - 15 p₃² H = κ H⁴` solved
`8 q₈ = H (15 p₃² + 20 p₂ H² + κ H³)`, and the honest chamber content
was the root-derivative tie `8 q₈'(a) = 15 p₃(a)² H'(a)` at core roots.
This file consumes the next unused aligned row, the degree-`10`
Jacobian coefficient — the first row that sees `p₁` and `q₇` — derived
here directly from the literal Keller bracket.

Substituting the two solved forms into the degree-`10` row collapses it
to a single weighted bracket of half-integral weight `9/2`: with the
weight-`9/2` defect

`M₂ = 5 p₃³ + 60 p₂ p₃ H² + 40 p₁ H⁴ + 4 κ p₃ H³ - 16 q₇ H`

(every monomial has exact `H`-weight `9/2`), the row becomes
`2 H M₂' - 9 M₂ H' = 0`.  The exact free-letter identity proved here is

`2 H M₂' - 9 M₂ H' + (8 p₃' R - 3 p₃ R') + (8 p₂ N' - 36 p₂' N)
  = 8 · row₁₀[p₄ = H², q₁₀ = H⁵]`

for the face residuals `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴` and
`N = 5 p₃ H³ - 2 q₉`, both of which vanish on the aligned face, so the
large substitution is handled through factored residual blocks instead
of a monolithic expansion.  The Wronskian argument then yields the
half-integral power relation

`M₂² = κ₂ H⁹`

— the aligned face regenerates, one level down, exactly the
square/ninth-power discriminator shape of the source face itself.  The
consequences split by chamber through the tracked UFD extraction
`squareCore_of_nonzero_imprimitiveRelation_410`:

* chamber-free: evaluating `M₂² = κ₂ H⁹` at any core root `a` kills
  `M₂(a) = 5 p₃(a)³`, so `p₃(a) = 0` — the `p₃` jet vanishes at every
  core root without any chamber hypothesis.  Combined with the
  degree-`11` root tie this forces `q₈'(a) = 0`, so `q₈` vanishes
  doubly at core roots chamber-free, resolving the previous face's
  detection residual (`q₈'(a) = 0 ↔ p₃(a) = 0`) affirmatively.
* nonsquare chamber (`H` a degree-two nonsquare): a nonzero constant in
  `M₂² = κ₂ H⁹` would force `H` to be a square, so `κ₂ = 0` is FORCED
  by parity and `M₂ = 0` identically.  The row therefore solves `q₇`:
  `16 q₇ = H² (5 g³ + 60 p₂ g + 40 p₁ H + 4 κ g H)` after the simple-root
  divisibility upgrade `p₃ = H g`, and the previously solved
  coefficients upgrade to `8 q₈ = H³ (15 g² + 20 p₂ + κ H)` and
  `q₉ = (5/2) g H⁴`.
* square chamber (`H = h₀²`): the extraction gives `M₂ = μ h₀⁹` with
  `μ² = κ₂`, an honest sign/scalar residual that is NOT cleared.  The
  linear-core divisibility gives `p₃ = h₀ t`, and the solved forms
  upgrade to `q₉ = (5/2) t h₀⁷`,
  `8 q₈ = h₀⁴ (15 t² + 20 p₂ h₀² + κ h₀⁴)`, and
  `16 q₇ = h₀ (5 t³ + 60 p₂ t h₀² + 4 κ t h₀⁴ + 40 p₁ h₀⁵ - μ h₀⁶)`.

Reused generic architecture: `squareCore_of_nonzero_imprimitiveRelation_410`
(tracked source face, the `(2,9)` UFD extraction),
`nonsquare_natDegree_two_derivative_ne_zero` and
`dvd_of_eval_eq_zero_of_simple_natDegree_two` (tracked `(6,8)` aligned
nonsquare architecture, generic in the degree pair), `C_ofNat_poly`,
and the previous face's solved forms and root tie.

No closure is claimed.  The weight-four constant `κ` remains uncleared;
the square chamber keeps the honest residuals `μ` (with `μ² = κ₂`) and
the free quotient `t`; the nonsquare chamber keeps the free quotient
`g`; `p₁, p₂` are constrained only through the solved forms; the zero
branches (`g = 0`, `t = 0`, `μ = 0`, `κ = 0`) are not excluded, and
neither chamber is excluded.  The next unused Keller row on the aligned
face is the degree-`9` Jacobian coefficient, the first row that sees
`p₀` and `q₆`.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient on the aligned face -/

/-- The third row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`10` Jacobian coefficient, the first row
that sees `p₁` and `q₇`.  It is derived directly from the Keller
bracket. -/
theorem alignedThirdCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 9).derivative +
        p.coeff 1 * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 10) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (10 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 10 :
      Finset (ℕ × ℕ)) =
      ({(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4),
        (7, 3), (8, 2), (9, 1), (10, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC7, hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Weight-`9/2` aligned defect -/

/-- Weight-`9/2` defect of the aligned `(4,10)` face:
`M₂ = 5 p₃³ + 60 p₂ p₃ H² + 40 p₁ H⁴ + 4 κ p₃ H³ - 16 q₇ H`.  Every
monomial has exact `H`-weight `9/2`; on the aligned face its square is
a polynomial first integral `M₂² = κ₂ H⁹` of the same ninth-power shape
as the source discriminator itself. -/
def alignedThirdDefect410 {K : Type*} [CommRing K]
    (H a1 a2 a3 b7 : K[X]) (κ : K) : K[X] :=
  (5 : K[X]) * a3 ^ 3 + (60 : K[X]) * a2 * a3 * H ^ 2 +
      (40 : K[X]) * a1 * H ^ 4 +
      (4 : K[X]) * Polynomial.C κ * a3 * H ^ 3 -
    (16 : K[X]) * b7 * H

set_option maxHeartbeats 8000000 in
/-- Exact free-letter combination of the degree-`10` Jacobian expression
with the weight-`9/2` bracket of `M₂`.  The two correction blocks are
the face residuals `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴` and
`N = 5 p₃ H³ - 2 q₉`, kept factored; both vanish on the aligned face. -/
theorem alignedThirdDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K] (H a1 a2 a3 b7 b8 b9 : K[X]) (κ : K) :
    (2 : K[X]) * H *
          (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
        (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
          H.derivative +
      ((8 : K[X]) * a3.derivative *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H - Polynomial.C κ * H ^ 4) -
        (3 : K[X]) * a3 *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H -
            Polynomial.C κ * H ^ 4).derivative) +
      ((8 : K[X]) * a2 *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9).derivative -
        (36 : K[X]) * a2.derivative *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9)) =
      (8 : K[X]) *
        ((H ^ 2).derivative * (b7 * (7 : K[X])) +
          a3.derivative * (b8 * (8 : K[X])) +
          a2.derivative * (b9 * (9 : K[X])) +
          a1.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b7.derivative +
          (a3 * (3 : K[X])) * b8.derivative +
          (a2 * (2 : K[X])) * b9.derivative +
          a1 * (H ^ 5).derivative)) := by
  simp only [alignedThirdDefect410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul, zero_mul, zero_add, mul_zero,
    add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face, with the degree-`11` row already consumed
(`M = κ H⁴`), the degree-`10` row is exactly the weight-`9/2` bracket
`2 H M₂' - 9 M₂ H' = 0`. -/
theorem alignedThirdDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    (2 : K[X]) * H *
        (alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (q.coeff 7) κ).derivative -
      (9 : K[X]) *
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedThirdCoefficientJacobianRow_410 hp hq hjac
  rw [hp4, hq10] at hrow
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC7, hC8, hC9, hC10, hC4, hC3, hC2] at hrow
  have hM' :
      (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
          (15 : K[X]) * p.coeff 3 ^ 2 * H = Polynomial.C κ * H ^ 4 := by
    simpa only [alignedSecondDefect410] using hM
  have hR :
      (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
          (15 : K[X]) * p.coeff 3 ^ 2 * H - Polynomial.C κ * H ^ 4 =
        0 := by
    linear_combination hM'
  have hid := alignedThirdDefect_weightedDerivative_identity_410
    H (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 7) (q.coeff 8)
    (q.coeff 9) κ
  rw [haligned, hR, hrow] at hid
  simpa only [Polynomial.derivative_zero, mul_zero, sub_zero, add_zero]
    using hid

/-! ## Half-integral ninth-power relation -/

/-- Generic Wronskian quotient for the weight-`9/2` bracket: over a
characteristic-zero field, `2 H D' - 9 D H' = 0` forces
`D² = C c * H⁹`. -/
theorem ninthPowerRelation_of_weightNineHalfRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (9 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 9 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (9 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
      Polynomial.C_eq_natCast 9
    rw [hC2, hC9]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 9) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (9 : K) * H ^ (9 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 9 =
          D * H ^ 8 *
            (Polynomial.C (9 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 9 hH) hW

/-- Half-integral power relation of the aligned `(4,10)` third row: the
weight-`9/2` defect squares to a scalar times `H⁹` — the source-face
discriminator shape reproduced one level down. -/
theorem alignedThirdDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₂ : K,
      alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 :=
  ninthPowerRelation_of_weightNineHalfRow_410 hH
    (alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Chamber-free root jet -/

/-- At every core root the ninth-power relation kills the value
`M₂(a) = 5 p₃(a)³`, so the `p₃` jet vanishes there chamber-free. -/
theorem alignedThird_rootKill_p3_410 {K : Type*} [Field K] [CharZero K]
    {H a1 a2 a3 b7 : K[X]} {κ κ₂ : K}
    (hrel : alignedThirdDefect410 H a1 a2 a3 b7 κ ^ 2 =
      Polynomial.C κ₂ * H ^ 9)
    {a : K} (ha : H.eval a = 0) : a3.eval a = 0 := by
  have hval := congrArg (fun f : K[X] => f.eval a) hrel
  simp only [Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_C, ha] at hval
  have h9 : (0 : K) ^ 9 = 0 := by norm_num
  rw [h9, mul_zero] at hval
  have hD0 : (alignedThirdDefect410 H a1 a2 a3 b7 κ).eval a = 0 :=
    sq_eq_zero_iff.mp hval
  simp only [alignedThirdDefect410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_ofNat, ha] at hD0
  have h5 : (5 : K) * a3.eval a ^ 3 = 0 := by linear_combination hD0
  have h3 : a3.eval a ^ 3 = 0 :=
    (mul_eq_zero.mp h5).resolve_left (by norm_num : (5 : K) ≠ 0)
  exact pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp h3

/-- Chamber-free second-order kill of `q₈`: the forced `p₃` root jet
turns the degree-`11` root tie `8 q₈'(a) = 15 p₃(a)² H'(a)` into
`q₈'(a) = 0`, resolving the previous face's detection residual. -/
theorem alignedThird_q8_secondOrderKill_410 {K : Type*}
    [Field K] [CharZero K] {H a1 a2 a3 b7 b8 : K[X]} {κ κ₂ : K}
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4)
    (hrel : alignedThirdDefect410 H a1 a2 a3 b7 κ ^ 2 =
      Polynomial.C κ₂ * H ^ 9)
    {a : K} (ha : H.eval a = 0) :
    b8.derivative.eval a = 0 := by
  have htie := alignedSecondDefect_rootDerivativeTie_410 hM ha
  have hp3 := alignedThird_rootKill_p3_410 hrel ha
  rw [hp3] at htie
  have h8 : (8 : K) * b8.derivative.eval a = 0 := by
    rw [htie]; ring
  exact (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : K) ≠ 0)

/-! ## Chamber quotients of the ninth-power relation -/

/-- Parity kill in the nonsquare chamber: a nonzero scalar in
`D² = C c * H⁹` would force the core to be a polynomial square via the
tracked `(2,9)` UFD extraction, so `c = 0` and `D = 0` identically. -/
theorem ninthPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 9) : c = 0 ∧ D = 0 := by
  have hc : c = 0 := by
    by_contra hc
    obtain ⟨h0, _lam, _hh0, _hlam, hHsq, _hD, _hlam2⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_410 hH hc hrel
    exact hnsq h0 hHsq
  refine ⟨hc, ?_⟩
  have hzero : D ^ 2 = 0 := by
    rw [hrel, hc, Polynomial.C_0, zero_mul]
  exact sq_eq_zero_iff.mp hzero

/-- In the square chamber `H = h₀²` the ninth-power relation resolves to
the literal half-integral form `D = C μ * h₀⁹` with `μ² = c`; the
scalar `μ` is an honest residual and is not cleared. -/
theorem ninthPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H h0 D : K[X]} {c : K}
    (hH : H ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 9) :
    ∃ μ : K, μ ^ 2 = c ∧ D = Polynomial.C μ * h0 ^ 9 := by
  by_cases hc : c = 0
  · have hzero : D ^ 2 = 0 := by
      rw [hrel, hc, Polynomial.C_0, zero_mul]
    refine ⟨0, by rw [hc]; norm_num, ?_⟩
    rw [sq_eq_zero_iff.mp hzero, Polynomial.C_0, zero_mul]
  · obtain ⟨h1, lam, _h1ne, _hlamne, hHsq', hDform, hlam2⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_410 hH hc hrel
    have hsq : h1 ^ 2 = h0 ^ 2 := by rw [← hHsq', ← hHsq]
    have hfac : (h1 - h0) * (h1 + h0) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with hminus | hplus
    · have h1eq : h1 = h0 := by linear_combination hminus
      refine ⟨lam, hlam2, ?_⟩
      rw [← h1eq]
      exact hDform
    · have h1eq : h1 = -h0 := by linear_combination hplus
      refine ⟨-lam, by linear_combination hlam2, ?_⟩
      rw [Polynomial.C_neg, hDform, h1eq]
      ring

/-- A degree-one core factor divides every polynomial that vanishes at
each of its roots. -/
theorem natDegree_one_dvd_of_root_kill_410 {K : Type*} [Field K]
    {h0 f : K[X]} (hdeg : h0.natDegree = 1)
    (hkill : ∀ a : K, h0.eval a = 0 → f.eval a = 0) : h0 ∣ f := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
  have hroot : h0.eval (-d / c) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    field_simp [hc]
    ring
  obtain ⟨u, hu⟩ := Polynomial.dvd_iff_isRoot.mpr (hkill _ hroot)
  refine ⟨Polynomial.C c⁻¹ * u, ?_⟩
  rw [← hlinear, hu]
  have h1 : Polynomial.C c * Polynomial.C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  have h2 : Polynomial.C (-d / c) =
      -(Polynomial.C d * Polynomial.C c⁻¹) := by
    rw [div_eq_mul_inv, neg_mul, Polynomial.C_neg, Polynomial.C_mul]
  calc
    (Polynomial.X - Polynomial.C (-d / c)) * u =
        (Polynomial.X + Polynomial.C d * Polynomial.C c⁻¹) * u := by
      rw [h2]; ring
    _ = (Polynomial.C c * Polynomial.C c⁻¹ * Polynomial.X +
          Polynomial.C d * Polynomial.C c⁻¹) * u := by
      rw [h1]; ring
    _ = (Polynomial.C c * Polynomial.X + Polynomial.C d) *
          (Polynomial.C c⁻¹ * u) := by
      ring

/-! ## Source-facing packets -/

/-- Chamber-free packet of the consumed degree-`10` row: the previous
face's solved forms, the half-integral power relation `M₂² = κ₂ H⁹`,
and the forced chamber-free root jet `p₃(a) = 0`, `q₈'(a) = 0` at every
core root. -/
theorem normalized410ScaleTwo_alignedThirdRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 ∧
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
  exact ⟨κ, κ₂, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Nonsquare-chamber packet of the consumed degree-`10` row: the
half-integral constant is FORCED to vanish by parity, the weight-`9/2`
defect dies identically, the simple-root core divides `p₃`, and all
three top coefficients resolve: `q₉ = (5/2) g H⁴`,
`8 q₈ = H³ (15 g² + 20 p₂ + κ H)`, and
`16 q₇ = H² (5 g³ + 60 p₂ g + 40 p₁ H + 4 κ g H)`. -/
theorem normalized410ScaleTwo_alignedThirdRow_nonsquareChamber_packet
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
    ∃ (κ : K) (g : K[X]),
      p.coeff 3 = H * g ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = 0 ∧
        q.coeff 9 = Polynomial.C (5 / 2 : K) * g * H ^ 4 ∧
        (8 : K[X]) * q.coeff 8 =
          H ^ 3 * ((15 : K[X]) * g ^ 2 + (20 : K[X]) * p.coeff 2 +
            Polynomial.C κ * H) ∧
        (16 : K[X]) * q.coeff 7 =
          H ^ 2 * ((5 : K[X]) * g ^ 3 + (60 : K[X]) * p.coeff 2 * g +
            (40 : K[X]) * p.coeff 1 * H +
            (4 : K[X]) * Polynomial.C κ * g * H) := by
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
  have hq9 := aligned_q9_solved_410 haligned
  have hclear := alignedSecondDefect_clearing_410 hM
  have hD0' :
      (5 : K[X]) * p.coeff 3 ^ 3 +
            (60 : K[X]) * p.coeff 2 * p.coeff 3 * H ^ 2 +
            (40 : K[X]) * p.coeff 1 * H ^ 4 +
            (4 : K[X]) * Polynomial.C κ * p.coeff 3 * H ^ 3 -
          (16 : K[X]) * q.coeff 7 * H = 0 := by
    simpa only [alignedThirdDefect410] using hD0
  refine ⟨κ, g, hg, hD0, ?_, ?_, ?_⟩
  · rw [hq9, hg]; ring
  · rw [hg] at hclear
    linear_combination hclear
  · apply mul_right_cancel₀ hH
    rw [hg] at hD0'
    linear_combination -hD0'

/-- Square-chamber packet of the consumed degree-`10` row: the
weight-`9/2` defect resolves to `M₂ = μ h₀⁹` with the honest residual
`μ`, the linear core divides `p₃`, and the top coefficients upgrade to
`q₉ = (5/2) t h₀⁷`, `8 q₈ = h₀⁴ (15 t² + 20 p₂ h₀² + κ h₀⁴)`, and
`16 q₇ = h₀ (5 t³ + 60 p₂ t h₀² + 4 κ t h₀⁴ + 40 p₁ h₀⁵ - μ h₀⁶)`. -/
theorem normalized410ScaleTwo_alignedThirdRow_squareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ : K) (t : K[X]),
      p.coeff 3 = h0 * t ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        q.coeff 9 = Polynomial.C (5 / 2 : K) * t * h0 ^ 7 ∧
        (8 : K[X]) * q.coeff 8 =
          h0 ^ 4 * ((15 : K[X]) * t ^ 2 +
            (20 : K[X]) * p.coeff 2 * h0 ^ 2 +
            Polynomial.C κ * h0 ^ 4) ∧
        (16 : K[X]) * q.coeff 7 =
          h0 * ((5 : K[X]) * t ^ 3 +
            (60 : K[X]) * p.coeff 2 * t * h0 ^ 2 +
            (4 : K[X]) * Polynomial.C κ * t * h0 ^ 4 +
            (40 : K[X]) * p.coeff 1 * h0 ^ 5 -
            Polynomial.C μ * h0 ^ 6) := by
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
  have hh0 : h0 ≠ 0 := by
    intro hzero
    apply hH
    rw [hHsq, hzero]
    ring
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
  have hq9 := aligned_q9_solved_410 haligned
  have hclear := alignedSecondDefect_clearing_410 hM
  have hD' :
      (5 : K[X]) * p.coeff 3 ^ 3 +
            (60 : K[X]) * p.coeff 2 * p.coeff 3 * H ^ 2 +
            (40 : K[X]) * p.coeff 1 * H ^ 4 +
            (4 : K[X]) * Polynomial.C κ * p.coeff 3 * H ^ 3 -
          (16 : K[X]) * q.coeff 7 * H = Polynomial.C μ * h0 ^ 9 := by
    simpa only [alignedThirdDefect410] using hDform
  refine ⟨κ, μ, t, ht, hDform, ?_, ?_, ?_⟩
  · rw [hq9, ht, hHsq]; ring
  · rw [ht, hHsq] at hclear
    linear_combination hclear
  · apply mul_right_cancel₀ (pow_ne_zero 2 hh0)
    rw [ht, hHsq] at hD'
    linear_combination -hD'

/-- Honest square/nonsquare chamber split of the consumed degree-`10`
row.  In the nonsquare chamber the half-integral constant is forced to
zero and `q₇` is solved outright; in the square chamber the residual
`μ` survives inside the solved `q₇`.  Neither chamber is excluded and
no closure is claimed. -/
theorem normalized410ScaleTwo_alignedThirdRow_chamberDichotomy
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
      ∃ (κ μ : K) (t : K[X]),
        p.coeff 3 = h0 * t ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          q.coeff 9 = Polynomial.C (5 / 2 : K) * t * h0 ^ 7 ∧
          (8 : K[X]) * q.coeff 8 =
            h0 ^ 4 * ((15 : K[X]) * t ^ 2 +
              (20 : K[X]) * p.coeff 2 * h0 ^ 2 +
              Polynomial.C κ * h0 ^ 4) ∧
          (16 : K[X]) * q.coeff 7 =
            h0 * ((5 : K[X]) * t ^ 3 +
              (60 : K[X]) * p.coeff 2 * t * h0 ^ 2 +
              (4 : K[X]) * Polynomial.C κ * t * h0 ^ 4 +
              (40 : K[X]) * p.coeff 1 * h0 ^ 5 -
              Polynomial.C μ * h0 ^ 6)) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g : K[X]),
        p.coeff 3 = H * g ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = 0 ∧
          q.coeff 9 = Polynomial.C (5 / 2 : K) * g * H ^ 4 ∧
          (8 : K[X]) * q.coeff 8 =
            H ^ 3 * ((15 : K[X]) * g ^ 2 + (20 : K[X]) * p.coeff 2 +
              Polynomial.C κ * H) ∧
          (16 : K[X]) * q.coeff 7 =
            H ^ 2 * ((5 : K[X]) * g ^ 3 +
              (60 : K[X]) * p.coeff 2 * g +
              (40 : K[X]) * p.coeff 1 * H +
              (4 : K[X]) * Polynomial.C κ * g * H)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    exact Or.inl ⟨h0, hh0, hHsq,
      normalized410ScaleTwo_alignedThirdRow_squareChamber_packet
        hsource hHsq haligned⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    exact Or.inr ⟨hnsq,
      normalized410ScaleTwo_alignedThirdRow_nonsquareChamber_packet
        hsource hnsq haligned⟩

/-- At scale two the common core has a root, and the consumed
degree-`10` row forces the full chamber-free root jet there: the `p₃`
jet dies, and the solved `q₉, q₈` vanish with `q₈` vanishing to second
order — the previous face's detection residual is resolved
affirmatively in both chambers. -/
theorem normalized410ScaleTwo_alignedThirdRow_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 3).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (q.coeff 8).derivative.eval a = 0 := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdeg : H.natDegree = 2 := hsource.2.1
  have hdeg : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hHne, hHdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdeg
  have hroot : H.eval a = 0 := ha
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
  have hq9 := aligned_q9_solved_410 haligned
  refine ⟨a, hroot, alignedThird_rootKill_p3_410 hrel hroot, ?_,
    alignedSecondDefect_eval_q8_eq_zero_410 hM hroot,
    alignedThird_q8_secondOrderKill_410 hM hrel hroot⟩
  simp [hq9, hroot]

#print axioms alignedThirdCoefficientJacobianRow_410
#print axioms alignedThirdDefect_weightedDerivative_identity_410
#print axioms alignedThirdDefectRow_eq_zero_410
#print axioms ninthPowerRelation_of_weightNineHalfRow_410
#print axioms alignedThirdDefectPowerRelation_410
#print axioms alignedThird_rootKill_p3_410
#print axioms alignedThird_q8_secondOrderKill_410
#print axioms ninthPower_nonsquareChamber_kill_410
#print axioms ninthPower_squareChamber_form_410
#print axioms natDegree_one_dvd_of_root_kill_410
#print axioms normalized410ScaleTwo_alignedThirdRow_packet
#print axioms normalized410ScaleTwo_alignedThirdRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedThirdRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedThirdRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedThirdRow_rootJet

end Max11DegreeRoutes
