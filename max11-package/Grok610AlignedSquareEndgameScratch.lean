import Grok610AlignedSquareFinalRowScratch

/-! # Endgame of the aligned-square `(6,10)` chamber

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareFinalRowScratch` exhausted the Jacobian tower on
the aligned face `N = 5 p₅ H² - 3 q₉ = 0` in the square chamber
`H = h₀²`: first integrals of weights `5`, `30`, `65`, `70`, the
degree-`1` row, and the last Keller row
`p₀' q₁ - p₁ q₀' = C j`.  Evaluating that row at the unique root `a`
of the forced linear scale yields
`p₀'(a) q₁(a) - p₁(a) q₀'(a) = j` with `j ≠ 0`, which separates the
two cross-products.  Unreduced, the weight-`5/30/65/70` identities
are tautological at `a` on the square jet `p₅(a) = p₄(a) = 0`.  The
live constraints on `p₀, p₁, q₀, q₁` sit in the *cancelled* peeled
rows of those integrals, exactly as in the committed `(4,10)` aligned
closure.

## Jet allocation (410 pattern)

The committed eleventh square packet already carries the divisor jet
`p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`, `3 f₂ - w₁² = h₀ e₁`,
`27 p₃ - w₁³ = h₀ e₂ = h₀² e₃`,
`w₁ (e₂ - 3 e₁ w₁) = h₀ u₂`.  At the unique root the eighth combined
row, the ninth peeled row, and the product identity force the same
branch that `alignedNinthSquareResolve_610` records:

`w₁(a) = 0  ∨  (μ = 0 ∧ e₁(a) = 0)`.

Because `h₀` is linear this upgrades to a global divisor on each
limb, the `(4,10)` `h₀ ∣ p₁` versus deep-divisor split.

## Valuation kill on the `μ = 0` limb

On `μ = 0` and `w₁(a) ≠ 0` one has `e₁ = h₀ e₁n`.  Substituting into
the committed ninth peeled row and cancelling one literal `h₀` leaves
the exact load `alignedSquareMuZeroNinthLoad610`, whose root value is
`-46080 w₁(a) (u₂(a) - 81 p₂(a))²`.  Thus `u₂(a) = 81 p₂(a)`.
Upgrading `u₂ = 81 p₂ + h₀ v` and cancelling one more `h₀` exposes
the head `135 ν w₁⁴`, so `ν = 0`: the fifth-defect constant dies.

## Honest residual; missing exact object

This file does **not** claim `False` for the square chamber.

* On the `μ = 0` limb the next unused exact object is
  `alignedSquareMuZeroNuZeroNinthLoad610`: the ninth quotient after
  the further substitution `ν = 0`, whose `h₀`-free head is
  `-5120 (4374 p₂ e₁n² w₁ - 1458 p₂ e₁n e₃ - 54 e₁n³ w₁³ + e₃³
  + 9 v² w₁)`.  Together with the matching eighth quotient head
  `1280 v²` this is the next 410-style cancellation
  (`v(a) = 0` and `e₃(a) = 6 e₁n(a) w₁(a)`), after which `ν₂ = 0`
  and a mixed `(p₁, q₁)` ninth/tenth pair remains against the Keller
  row.  Neither quotient is constructed here.
* On the `w₁(a) = 0` limb the missing object is
  `alignedSquareW1ZeroNinthLoad610`, the ninth quotient after
  `w₁ = h₀ w₁n`, whose `h₀²`-free head is
  `-46080 (6561 p₂² w₁n - 972 p₂ e₁² w₁n + 162 p₂ e₁ e₃
  + 21 e₁⁴ w₁n - 4 e₁³ e₃)`.

The Jacobian tower remains exhausted (no unused row below degree
`0`).  The nonsquare aligned chamber is not reopened.  No
total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000

/-! ## Unique root of the forced linear scale -/

section UniqueRoot610

variable {K : Type*} [Field K]

/-- A degree-one polynomial has at most one root. -/
theorem alignedSquare610_root_unique
    (h0 : K[X]) (hdegree : h0.natDegree = 1)
    {x y : K} (hx : h0.eval x = 0) (hy : h0.eval y = 0) : x = y := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  rw [← hlinear] at hx hy
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hx hy
  have hcx : c * (x - y) = 0 := by linear_combination hx - hy
  exact eq_of_sub_eq_zero
    ((mul_eq_zero.mp hcx).resolve_left hc)

end UniqueRoot610

/-! ## Exact ninth quotient on the `μ = 0` limb -/

/-- Exact quotient of the ninth peeled row after substituting the
`μ = 0` upgrades `e₁ = h₀ e₁n` and `e₂ = h₀ e₃` and cancelling one
literal `h₀`.  Its `h₀`-free head is `-46080 w₁ (u₂ - 81 p₂)²`. -/
def alignedSquareMuZeroNinthLoad610
    {K : Type*} [CommRing K]
    (h0 w1 e1n e3 u2 a0 a1 a2 b1 : K[X])
    (κ κ₃ ν κ₅ ν₂ κ₇ : K) : K[X] :=
  -((46080 : K[X]) * u2 ^ 2 * w1) + (7464960 : K[X]) * u2 * w1 * a2 -
    (302330880 : K[X]) * w1 * a2 ^ 2
  + h0 * ((135 : K[X]) * Polynomial.C ν * w1 ^ 4)
  + h0 ^ 2 *
    ((1813985280 : K[X]) * a1 * a2 - (22394880 : K[X]) * a1 * u2 +
      (44789760 : K[X]) * a2 * e1n ^ 2 * w1 -
      (7464960 : K[X]) * a2 * e1n * e3 -
      Polynomial.C κ * ((17915904 : K[X]) * a2 * e1n * w1) +
      Polynomial.C κ * ((2985984 : K[X]) * a2 * e3) +
      (276480 : K[X]) * e1n ^ 3 * w1 ^ 3 -
      (829440 : K[X]) * e1n ^ 2 * u2 * w1 +
      (184320 : K[X]) * e1n * e3 * u2 +
      Polynomial.C κ * ((221184 : K[X]) * e1n * u2 * w1) -
      (5120 : K[X]) * e3 ^ 3 -
      Polynomial.C κ * ((36864 : K[X]) * e3 * u2))
  + h0 ^ 3 *
    (-(Polynomial.C ν * ((233280 : K[X]) * a2)) +
      Polynomial.C ν * ((1080 : K[X]) * e1n * w1 ^ 2) +
      Polynomial.C ν * ((1440 : K[X]) * u2) -
      Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2))
  + h0 ^ 4 *
    (-((201553920 : K[X]) * a0 * e1n * w1) +
      (67184640 : K[X]) * a0 * e3 +
      Polynomial.C κ * ((80621568 : K[X]) * a0 * w1) -
      (33592320 : K[X]) * a1 * e1n ^ 2 +
      Polynomial.C κ * ((26873856 : K[X]) * a1 * e1n) -
      Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
      (1632586752 : K[X]) * b1 -
      (967680 : K[X]) * e1n ^ 4 * w1 +
      (184320 : K[X]) * e1n ^ 3 * e3 +
      Polynomial.C κ * ((552960 : K[X]) * e1n ^ 3 * w1) -
      Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * e3) +
      Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
      Polynomial.C κ₅ * ((384 : K[X]) * e3) -
      Polynomial.C κ₇ * ((36 : K[X]) * w1))
  + h0 ^ 5 *
    (Polynomial.C ν * ((2160 : K[X]) * e1n ^ 2) -
      Polynomial.C ν₂ * ((108 : K[X]) * e1n))

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 16000000 in
/-- Polynomial identity: the ninth peeled row on the `μ = 0` upgrades
is `h₀` times `alignedSquareMuZeroNinthLoad610`. -/
theorem alignedSquareMuZero_ninthFactor610
    (h0 w1 e1n e3 u2 a0 a1 a2 b1 : K[X])
    (κ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) u2 a0 a1
        a2 b1 κ 0 κ₃ ν κ₅ ν₂ κ₇ =
      h0 * alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3 u2 a0 a1 a2 b1
        κ κ₃ ν κ₅ ν₂ κ₇ := by
  apply Polynomial.funext
  intro z
  simp only [alignedNinthSquarePeeledRow610,
    alignedSquareMuZeroNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_zero, Polynomial.C_0, zero_mul, mul_zero, add_zero,
    sub_zero, zero_add]
  ring

set_option maxHeartbeats 8000000 in
/-- After cancelling the recorded `h₀` from the ninth row, the unique
root forces `u₂(a) = 81 p₂(a)` on the `μ = 0` limb. -/
theorem alignedSquareMuZero_ninthHeadKill610
    (h0 w1 e1n e3 u2 a0 a1 a2 b1 : K[X])
    (κ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hrow :
      alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) u2 a0
          a1 a2 b1 κ 0 κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 6)
    (x : K) (hx : h0.eval x = 0) (hw1x : w1.eval x ≠ 0) :
    u2.eval x = (81 : K) * a2.eval x := by
  have hfactor :=
    alignedSquareMuZero_ninthFactor610 h0 w1 e1n e3 u2 a0 a1 a2 b1 κ κ₃
      ν κ₅ ν₂ κ₇
  rw [hfactor] at hrow
  have hload :
      alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3 u2 a0 a1 a2 b1 κ κ₃
          ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 5 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3 u2 a0 a1 a2 b1
            κ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 := hrow
      _ = h0 * (Polynomial.C μ₃ * h0 ^ 5) := by ring
  have hloadx :=
    congrArg (fun w : K[X] => w.eval x) hload
  simp only [alignedSquareMuZeroNinthLoad610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  have hsq :
      (46080 : K) * w1.eval x *
        (u2.eval x - (81 : K) * a2.eval x) ^ 2 = 0 := by
    linear_combination -hloadx
  have h46080w : (46080 : K) * w1.eval x ≠ 0 :=
    mul_ne_zero (by norm_num) hw1x
  have hdiff :
      (u2.eval x - (81 : K) * a2.eval x) ^ 2 = 0 :=
    (mul_eq_zero.mp hsq).resolve_left h46080w
  exact eq_of_sub_eq_zero
    ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hdiff)

set_option maxHeartbeats 16000000 in
/-- After the further substitution `u₂ = 81 p₂ + h₀ v`, the `μ = 0`
ninth load is `h₀` times a polynomial whose constant term is
`135 ν w₁⁴`. -/
theorem alignedSquareMuZero_ninthLoad_uFactor610
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ κ₃ ν κ₅ ν₂ κ₇ : K) :
    alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
        (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ κ₃ ν κ₅ ν₂ κ₇ =
      h0 * ((135 : K[X]) * Polynomial.C ν * w1 ^ 4 + h0 *
        (-((46080 : K[X]) * w1 * v ^ 2) +
          (1813985280 : K[X]) * a1 * a2 -
          (22394880 : K[X]) * a1 * (h0 * v + (81 : K[X]) * a2) +
          (44789760 : K[X]) * a2 * e1n ^ 2 * w1 -
          (7464960 : K[X]) * a2 * e1n * e3 -
          Polynomial.C κ * ((17915904 : K[X]) * a2 * e1n * w1) +
          Polynomial.C κ * ((2985984 : K[X]) * a2 * e3) +
          (276480 : K[X]) * e1n ^ 3 * w1 ^ 3 -
          (829440 : K[X]) * e1n ^ 2 *
            (h0 * v + (81 : K[X]) * a2) * w1 +
          (184320 : K[X]) * e1n * e3 *
            (h0 * v + (81 : K[X]) * a2) +
          Polynomial.C κ * ((221184 : K[X]) * e1n *
            (h0 * v + (81 : K[X]) * a2) * w1) -
          (5120 : K[X]) * e3 ^ 3 -
          Polynomial.C κ * ((36864 : K[X]) * e3 *
            (h0 * v + (81 : K[X]) * a2)) + h0 *
        (-(Polynomial.C ν * ((233280 : K[X]) * a2)) +
          Polynomial.C ν * ((1080 : K[X]) * e1n * w1 ^ 2) +
          Polynomial.C ν * ((1440 : K[X]) *
            (h0 * v + (81 : K[X]) * a2)) -
          Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) + h0 *
        (-((201553920 : K[X]) * a0 * e1n * w1) +
          (67184640 : K[X]) * a0 * e3 +
          Polynomial.C κ * ((80621568 : K[X]) * a0 * w1) -
          (33592320 : K[X]) * a1 * e1n ^ 2 +
          Polynomial.C κ * ((26873856 : K[X]) * a1 * e1n) -
          Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
          (1632586752 : K[X]) * b1 -
          (967680 : K[X]) * e1n ^ 4 * w1 +
          (184320 : K[X]) * e1n ^ 3 * e3 +
          Polynomial.C κ * ((552960 : K[X]) * e1n ^ 3 * w1) -
          Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * e3) +
          Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
          Polynomial.C κ₅ * ((384 : K[X]) * e3) -
          Polynomial.C κ₇ * ((36 : K[X]) * w1) + h0 *
        (Polynomial.C ν * ((2160 : K[X]) * e1n ^ 2) -
          Polynomial.C ν₂ * ((108 : K[X]) * e1n)))))) := by
  simp only [alignedSquareMuZeroNinthLoad610]
  ring

set_option maxHeartbeats 8000000 in
/-- The second ninth cancellation on the `μ = 0` limb kills the
fifth-defect constant: `ν = 0`. -/
theorem alignedSquareMuZero_uFactor_nuKill610
    (h0 w1 e1n e3 v a0 a1 a2 b1 : K[X])
    (κ μ₃ κ₃ ν κ₅ ν₂ κ₇ : K)
    (hh0 : h0 ≠ 0)
    (hload :
      alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
          (h0 * v + (81 : K[X]) * a2) a0 a1 a2 b1 κ κ₃ ν κ₅ ν₂ κ₇ =
        Polynomial.C μ₃ * h0 ^ 5)
    (x : K) (hx : h0.eval x = 0) (hw1x : w1.eval x ≠ 0) :
    ν = 0 := by
  have hfactor :=
    alignedSquareMuZero_ninthLoad_uFactor610 h0 w1 e1n e3 v a0 a1 a2
      b1 κ κ₃ ν κ₅ ν₂ κ₇
  rw [hfactor] at hload
  have hsecond :
      (135 : K[X]) * Polynomial.C ν * w1 ^ 4 + h0 *
          (-((46080 : K[X]) * w1 * v ^ 2) +
            (1813985280 : K[X]) * a1 * a2 -
            (22394880 : K[X]) * a1 * (h0 * v + (81 : K[X]) * a2) +
            (44789760 : K[X]) * a2 * e1n ^ 2 * w1 -
            (7464960 : K[X]) * a2 * e1n * e3 -
            Polynomial.C κ * ((17915904 : K[X]) * a2 * e1n * w1) +
            Polynomial.C κ * ((2985984 : K[X]) * a2 * e3) +
            (276480 : K[X]) * e1n ^ 3 * w1 ^ 3 -
            (829440 : K[X]) * e1n ^ 2 *
              (h0 * v + (81 : K[X]) * a2) * w1 +
            (184320 : K[X]) * e1n * e3 *
              (h0 * v + (81 : K[X]) * a2) +
            Polynomial.C κ * ((221184 : K[X]) * e1n *
              (h0 * v + (81 : K[X]) * a2) * w1) -
            (5120 : K[X]) * e3 ^ 3 -
            Polynomial.C κ * ((36864 : K[X]) * e3 *
              (h0 * v + (81 : K[X]) * a2)) + h0 *
          (-(Polynomial.C ν * ((233280 : K[X]) * a2)) +
            Polynomial.C ν * ((1080 : K[X]) * e1n * w1 ^ 2) +
            Polynomial.C ν * ((1440 : K[X]) *
              (h0 * v + (81 : K[X]) * a2)) -
            Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) + h0 *
          (-((201553920 : K[X]) * a0 * e1n * w1) +
            (67184640 : K[X]) * a0 * e3 +
            Polynomial.C κ * ((80621568 : K[X]) * a0 * w1) -
            (33592320 : K[X]) * a1 * e1n ^ 2 +
            Polynomial.C κ * ((26873856 : K[X]) * a1 * e1n) -
            Polynomial.C κ₃ * ((3359232 : K[X]) * a1) -
            (1632586752 : K[X]) * b1 -
            (967680 : K[X]) * e1n ^ 4 * w1 +
            (184320 : K[X]) * e1n ^ 3 * e3 +
            Polynomial.C κ * ((552960 : K[X]) * e1n ^ 3 * w1) -
            Polynomial.C κ * ((110592 : K[X]) * e1n ^ 2 * e3) +
            Polynomial.C κ₅ * ((1152 : K[X]) * e1n * w1) -
            Polynomial.C κ₅ * ((384 : K[X]) * e3) -
            Polynomial.C κ₇ * ((36 : K[X]) * w1) + h0 *
          (Polynomial.C ν * ((2160 : K[X]) * e1n ^ 2) -
            Polynomial.C ν₂ * ((108 : K[X]) * e1n))))) =
        Polynomial.C μ₃ * h0 ^ 4 := by
    have hpow : Polynomial.C μ₃ * h0 ^ 5 =
        h0 * (Polynomial.C μ₃ * h0 ^ 4) := by ring
    exact mul_left_cancel₀ hh0 (hload.trans hpow)
  have hsecondx := congrArg (fun w : K[X] => w.eval x) hsecond
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_ofNat] at hsecondx
  rw [hx] at hsecondx
  norm_num at hsecondx
  exact hsecondx.resolve_right hw1x

/-! ## Source-facing square-chamber allocation and the `μ = 0` kill -/

set_option maxHeartbeats 16000000 in
/-- Unique root, exhausted packet, eleventh square jet, and the
410-style branch `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)`.  The last Keller
row at that root still separates the cross-products. -/
theorem normalized610ScaleTwo_alignedSquare_jetAllocation
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a j : K) (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K)
      (w1 f2 e1 e2 u2 e3 : K[X]),
      h0.natDegree = 1 ∧ h0.eval a = 0 ∧ j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
            (p.coeff 1).eval a *
              ((q.coeff 0).derivative).eval a = j ∧
        p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
        e2 = h0 * e3 ∧
        w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = Polynomial.C ν * h0 ^ 25 ∧
        alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 ∧
        e2.eval a = 0 ∧
        (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hdeg1 := alignedSquare610_h0_natDegree_eq_one hsource hh0 hHsq
  obtain ⟨a, hroot⟩ := alignedSquare610_exists_root h0 hdeg1
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleTwo_alignedFinalKellerRow hsource haligned
  have hroweval : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
    have h := congrArg (Polynomial.eval a) hrow
    simpa only [p, q, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] using h
  have hpacket :=
    normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
      hsource hh0 hHsq haligned
  dsimp only at hpacket
  obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, _κ₈, μ₃, _κ₉, _κ₁₀, _μ₄, w1, f2, e1,
    e2, u2, e3, _s2, _s4, _s5, _hμ₃, _hμ₄, hM, hp5w1, hp4f2, he1, he2,
    hu2, _hR8, he3, _h27, hR9, _hs2, _hR10x, _hs4, _hR11x, _hs5, _hmu8,
    hQ9, hD, _hE, hF, _hG, _hI, _hJ, _hL, _hO, _hΛ, _hΛ2⟩ := hpacket
  have hev1 := congrArg (fun t : K[X] => t.eval a) hu2
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_ofNat] at hev1
  rw [hroot, zero_mul] at hev1
  have h1 : w1.eval a *
      (e2.eval a - 3 * e1.eval a * w1.eval a) = 0 := by
    linear_combination hev1
  have hevQ9 := congrArg (fun t : K[X] => t.eval a) hQ9
  simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevQ9
  rw [hroot] at hevQ9
  have h2 : 1280 * e1.eval a *
      (3 * e1.eval a * w1.eval a - e2.eval a) *
      (6 * e1.eval a * w1.eval a - e2.eval a) +
      189 * μ * w1.eval a ^ 5 = 0 := by
    linear_combination -hevQ9
  have hevR9 := congrArg (fun t : K[X] => t.eval a) hR9
  simp only [alignedNinthSquarePeeledRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevR9
  rw [hroot] at hevR9
  have h9 : 276480 * e1.eval a ^ 3 * w1.eval a ^ 3 -
      5120 * e2.eval a ^ 3 - 189 * μ * w1.eval a ^ 6 = 0 := by
    linear_combination hevR9
  obtain ⟨he2a, hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
  exact ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
    hdeg1, hroot, hj, hrow, hroweval, hp5w1, hp4f2, he1, he2, he3, hu2,
    hM, hD, hF, hR9, he2a, hbranch⟩

set_option maxHeartbeats 16000000 in
/-- Square-chamber endgame reduction.  The unique root and the
410-style branch are recorded, the `w₁(a) = 0` limb upgrades to a
global divisor, and the complementary `μ = 0` limb is killed through
`u₂(a) = 81 p₂(a)` and `ν = 0`.  Neither limb is closed: the next
exact ninth/eighth quotients after `ν = 0`, and the ninth quotient
after `w₁ = h₀ w₁n`, are not constructed. -/
theorem normalized610ScaleTwo_alignedSquare_endgameReduction
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a j : K) (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K)
      (w1 f2 e1 e2 u2 e3 : K[X]),
      h0.natDegree = 1 ∧ h0.eval a = 0 ∧ j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
            (p.coeff 1).eval a *
              ((q.coeff 0).derivative).eval a = j ∧
        p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
        e2 = h0 * e3 ∧
        w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = Polynomial.C ν * h0 ^ 25 ∧
        alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 ∧
        (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0)) ∧
        (w1.eval a = 0 → ∃ w1n : K[X], w1 = h0 * w1n) ∧
        (w1.eval a ≠ 0 →
          μ = 0 ∧ ν = 0 ∧
            u2.eval a = (81 : K) * (p.coeff 2).eval a ∧
              alignedThirdDefect610 H (p.coeff 3) (p.coeff 4)
                  (p.coeff 5) (q.coeff 7) κ = 0 ∧
                alignedFifthDefect610 H (p.coeff 1) (p.coeff 2)
                    (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5)
                    (q.coeff 6) (q.coeff 7) κ = 0 ∧
                  ∃ e1n v : K[X],
                    e1 = h0 * e1n ∧
                      u2 = h0 * v + (81 : K[X]) * p.coeff 2) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
    hdeg1, hroot, hj, hrow, hroweval, hp5, hp4, he1, he2, he3, hu2, hM,
    hD, hF, hR9, _he2a, hbranch⟩ :=
    normalized610ScaleTwo_alignedSquare_jetAllocation hsource hh0 hHsq
      haligned
  refine ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
    hdeg1, hroot, hj, hrow, hroweval, hp5, hp4, he1, he2, he3, hu2, hM,
    hD, hF, hR9, hbranch, ?limbA, ?limbB⟩
  · intro hw1a
    obtain ⟨w1n, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w1 a hdeg1 hroot hw1a
    exact ⟨w1n, hw1⟩
  · intro hw1x
    have hμe1 : μ = 0 ∧ e1.eval a = 0 :=
      hbranch.resolve_left hw1x
    obtain ⟨hμ, he1a⟩ := hμe1
    obtain ⟨e1n, he1n⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 e1 a hdeg1 hroot he1a
    have hR9μ :
        alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n) (h0 * e3) u2
            (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ 0 κ₃ ν
            κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 := by
      simpa [hμ, he1n, he3] using hR9
    have hu2a :=
      alignedSquareMuZero_ninthHeadKill610 h0 w1 e1n e3 u2
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ₃ κ₃ ν κ₅
        ν₂ κ₇ hh0 hR9μ a hroot hw1x
    have hua :
        (u2 - (81 : K[X]) * p.coeff 2).eval a = 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      linear_combination hu2a
    obtain ⟨v, hv⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        (u2 - (81 : K[X]) * p.coeff 2) a hdeg1 hroot hua
    have hu : u2 = h0 * v + (81 : K[X]) * p.coeff 2 := by
      linear_combination hv
    have hload :
        alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
            (h0 * v + (81 : K[X]) * p.coeff 2) (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 5 := by
      have hfactor :=
        alignedSquareMuZero_ninthFactor610 h0 w1 e1n e3 u2
          (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν κ₅
          ν₂ κ₇
      apply mul_left_cancel₀ hh0
      calc
        h0 * alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3
              (h0 * v + (81 : K[X]) * p.coeff 2) (p.coeff 0)
              (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν κ₅ ν₂ κ₇ =
            h0 * alignedSquareMuZeroNinthLoad610 h0 w1 e1n e3 u2
              (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ κ₃ ν
              κ₅ ν₂ κ₇ := by rw [hu]
        _ = alignedNinthSquarePeeledRow610 h0 w1 (h0 * e1n)
              (h0 * e3) u2 (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (q.coeff 1) κ 0 κ₃ ν κ₅ ν₂ κ₇ := hfactor.symm
        _ = Polynomial.C μ₃ * h0 ^ 6 := hR9μ
        _ = h0 * (Polynomial.C μ₃ * h0 ^ 5) := by ring
    have hν : ν = 0 :=
      alignedSquareMuZero_uFactor_nuKill610 h0 w1 e1n e3 v
        (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ₃ κ₃ ν κ₅
        ν₂ κ₇ hh0 hload a hroot hw1x
    have hD0 :
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 := by
      simpa [hμ] using hD
    have hF0 :
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 := by
      simpa [hν] using hF
    exact ⟨hμ, hν, hu2a, hD0, hF0, e1n, v, he1n, hu⟩

/-- Exhausted square packet together with the jet-allocation endgame
reduction.  The Jacobian tower has no unused row below degree `0`.
The square chamber is not claimed empty. -/
theorem normalized610ScaleTwo_alignedSquare_endgamePacket
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ κ c xi nu : K,
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1) =
          Polynomial.C c * H ^ 30 ∧
        localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
          Polynomial.C xi * h0 ^ 65 ∧
        localClearedFourteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) =
          Polynomial.C nu * h0 ^ 70 ∧
        (p.coeff 1).derivative * q.coeff 1 +
            (p.coeff 0).derivative *
              (q.coeff 2 * Polynomial.C (2 : K)) -
          ((p.coeff 2 * Polynomial.C (2 : K)) *
              (q.coeff 0).derivative +
            p.coeff 1 * (q.coeff 1).derivative) = 0) ∧
      (∃ j : K, j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j) ∧
      (∃ (a : K) (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K)
        (w1 f2 e1 e2 u2 e3 : K[X]),
        h0.natDegree = 1 ∧ h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          e2 = h0 * e3 ∧
          w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
          alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
              (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
            Polynomial.C μ₃ * h0 ^ 6 ∧
          (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0)) ∧
          (w1.eval a = 0 → ∃ w1n : K[X], w1 = h0 * w1n) ∧
          (w1.eval a ≠ 0 →
            μ = 0 ∧ ν = 0 ∧
              u2.eval a = (81 : K) * (p.coeff 2).eval a ∧
                alignedFifthDefect610 H (p.coeff 1) (p.coeff 2)
                    (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5)
                    (q.coeff 6) (q.coeff 7) κ = 0)) := by
  dsimp only at haligned ⊢
  refine ⟨?exhausted, ?row, ?jet⟩
  · exact (normalized610ScaleTwo_alignedSquare_exhaustedPacket
      hsource hh0 hHsq haligned).1
  · exact (normalized610ScaleTwo_alignedSquare_exhaustedPacket
      hsource hh0 hHsq haligned).2
  · obtain ⟨a, j, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
      hdeg1, hroot, _hj, _hrow, _hroweval, hp5, hp4, he1, _he2, he3,
      hu2, _hM, _hD, _hF, hR9, hbranch, hA, hB⟩ :=
      normalized610ScaleTwo_alignedSquare_endgameReduction hsource
        hh0 hHsq haligned
    refine ⟨a, κ, μ, κ₃, ν, κ₅, ν₂, κ₇, μ₃, w1, f2, e1, e2, u2, e3,
      hdeg1, hroot, hp5, hp4, he1, he3, hu2, hR9, hbranch, hA, ?_⟩
    intro hw1x
    obtain ⟨hμ, hν, hu2a, _hD0, hF0, _e1n, _v, _he1n, _hu⟩ := hB hw1x
    exact ⟨hμ, hν, hu2a, hF0⟩

#print axioms alignedSquare610_root_unique
#print axioms alignedSquareMuZero_ninthFactor610
#print axioms alignedSquareMuZero_ninthHeadKill610
#print axioms alignedSquareMuZero_ninthLoad_uFactor610
#print axioms alignedSquareMuZero_uFactor_nuKill610
#print axioms normalized610ScaleTwo_alignedSquare_jetAllocation
#print axioms normalized610ScaleTwo_alignedSquare_endgameReduction
#print axioms normalized610ScaleTwo_alignedSquare_endgamePacket

end Max11DegreeRoutes

