import Fable410ScaleTwoAlignedThirdFaceScratch

/-! # Fourth aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedThirdFaceScratch` consumed the degree-`9`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the weight-six
chamber-free first integral `M₄ = κ₃ H⁶` of the fourth defect, the
square-chamber divisibility `p₃ = h₀² u`, and the solved sextic
coefficient `q₆`.  This file consumes the next unused aligned row, the
degree-`8` Jacobian coefficient — the first row that sees `q₅` — derived
here directly from the literal Keller bracket.

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, the
consumed degree-`10` bracket `2 H M₂' - 9 M₂ H' = 0`, and the consumed
degree-`9` bracket `H M₄' - 6 M₄ H' = 0`, the degree-`8` row is the
weighted derivative of the cleared fifth defect

`M₆ = 1920 p₀ p₃ H⁶ - 512 q₅ H⁵ + 1920 p₁ p₂ H⁶ + 480 p₁ p₃² H⁴
  + 480 p₂² p₃ H⁴ - 80 p₂ p₃³ H² + 6 p₃⁵
  + κ (128 p₁ H⁷ + 128 p₂ p₃ H⁵) - 6 p₃ M₄ - (21 p₃² + 56 p₂ H²) M₂`,

kept in factored form through the third defect `M₂` and the fourth
defect `M₄`, via the exact multiplier identity

`256 H⁴ · row₈[p₄ = H²] = (2 H M₆' - 15 M₆ H')
  + 18 p₃ (H M₄' - 6 M₄ H') + (72 p₂ H² + 63 p₃²) (2 H M₂' - 9 M₂ H')
  - 1152 H⁴ p₀' N + 256 H⁴ p₁' R - 32 H⁴ p₁ R'`.

On the aligned face every right-hand correction vanishes, so
`2 H M₆' = 15 M₆ H'` and the squared weight-`15/2` polynomial first
integral

`M₆² = κ₄ H¹⁵`

holds for a preserved constant `κ₄` — the odd fifteenth-power
discriminator shape regenerated a second time, two levels below the
ninth-power shape of the degree-`10` row.  The chambers of the previous
packets then specialize the consumed row honestly:

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`:
  the square root extraction gives `M₆ = μ₂ h₀¹⁵` with `μ₂² = κ₄`, an
  honest residual that is NOT cleared.  Cancelling `h₀¹⁰` solves the
  quintic row with NO `h₀` factor on `q₅` — the new letter sits at the
  same `h₀`-level as the quintic core:
  `512 q₅ = 6 u⁵ - 80 p₂ u³ + 480 p₂² u
  + h₀² (480 p₁ u² + 1920 p₁ p₂ + 128 κ p₂ u) - μ h₀³ (21 u² + 56 p₂)
  + h₀⁴ (1920 p₀ u + 128 κ p₁ - 6 κ₃ u) - μ₂ h₀⁵`.  No new divisibility
  and no new root kill appear; the honest root content is the value tie
  `512 q₅(a) = 6 u(a)⁵ - 80 p₂(a) u(a)³ + 480 p₂(a)² u(a)` at the core
  root.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = 0`, `M₄ = κ₃ H⁶`: the odd exponent forces
  `κ₄ = 0` by parity and `M₆ = 0` identically.  Cancelling `H⁵` solves
  the quintic row outright,
  `512 q₅ = 6 g⁵ - 80 p₂ g³ + 480 p₂² g
  + H (480 p₁ g² + 1920 p₁ p₂ + 128 κ p₂ g)
  + H² (1920 p₀ g + 128 κ p₁ - 6 κ₃ g)`; again `q₅` carries no `H`
  factor and the root tie is the same quintic
  `512 q₅(a) = 6 g⁵ - 80 p₂ g³ + 480 p₂² g` at `a` — the self-similar
  quintic core `2 w (3 w⁴ - 40 p₂ w² + 240 p₂²)` shared by both
  chambers.

Reused architecture: `dvd_of_sq_dvd_sq_poly` (tracked `(6,8)` aligned
second defect, the square-divisibility extraction),
`nonsquare_natDegree_two_derivative_ne_zero` and
`dvd_of_eval_eq_zero_of_simple_natDegree_two` (tracked `(6,8)` aligned
architecture, generic in the degree pair),
`natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, and the previous faces'
solved forms and chamber quotients.  The extended root jet is unchanged
through `q₆` (values `p₃, q₉, q₈, q₇, q₆` and derivatives `q₈', q₇'`
all vanish chamber-free; `p₃'(a) = 0` and `q₆'(a) = 0` in the square
chamber); the new degree-`8` content at the root is the honest `q₅`
value tie, NOT a vanishing.

No closure is claimed.  Both chambers remain open, the zero branches
(`u = 0`, `g = 0`, `μ = 0`, `μ₂ = 0`, `κ = 0`, `κ₂ = 0`, `κ₃ = 0`,
`κ₄ = 0`) are not excluded, and the constants are preserved where not
forced (`κ₄ = 0` is forced only in the nonsquare chamber).
`p₀, p₁, p₂` are constrained only through the solved forms.  The next
unused Keller row on the aligned face is the degree-`7` Jacobian
coefficient, the first row that sees `q₄`.  No total-degree or
twice-prime theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`8` Keller coefficient on the aligned face -/

/-- The fifth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`8` Jacobian coefficient, the first
aligned row that sees `q₅`.  It is derived directly from the Keller
bracket. -/
theorem alignedFifthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 7).derivative +
        p.coeff 1 * (q.coeff 8).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1), (8, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC5, hC6, hC7, hC8, hC9, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned fifth defect -/

/-- Cleared fifth defect of the degree-`8` aligned `(4,10)` row, kept
in factored form through the third defect `M₂` and the fourth defect
`M₄`:
`M₆ = 1920 p₀ p₃ H⁶ - 512 q₅ H⁵ + 1920 p₁ p₂ H⁶ + 480 p₁ p₃² H⁴
+ 480 p₂² p₃ H⁴ - 80 p₂ p₃³ H² + 6 p₃⁵ + κ (128 p₁ H⁷ + 128 p₂ p₃ H⁵)
- 6 p₃ M₄ - (21 p₃² + 56 p₂ H²) M₂`.  Every monomial has exact
`H`-weight `15/2`; on the aligned face its square is a polynomial first
integral of the odd fifteenth-power discriminator shape. -/
def alignedFifthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (1920 : K[X]) * a0 * a3 * H ^ 6 - (512 : K[X]) * b5 * H ^ 5 +
    (1920 : K[X]) * a1 * a2 * H ^ 6 +
    (480 : K[X]) * a1 * a3 ^ 2 * H ^ 4 +
    (480 : K[X]) * a2 ^ 2 * a3 * H ^ 4 -
    (80 : K[X]) * a2 * a3 ^ 3 * H ^ 2 + (6 : K[X]) * a3 ^ 5 +
    Polynomial.C κ *
      ((128 : K[X]) * a1 * H ^ 7 + (128 : K[X]) * a2 * a3 * H ^ 5) -
    (6 : K[X]) * a3 * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((21 : K[X]) * a3 ^ 2 + (56 : K[X]) * a2 * H ^ 2) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`8` Jacobian expression with the
weight-`15/2` bracket of `M₆`.  The corrections are the face residuals
`N = 5 p₃ H³ - 2 q₉` and `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴`, kept
factored, and the consumed degree-`10` and degree-`9` brackets of `M₂`
and `M₄`; every one of them vanishes on the aligned face. -/
theorem alignedFifthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K] (H a0 a1 a2 a3 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (256 : K[X]) * H ^ 4 *
        ((H ^ 2).derivative * (b5 * (5 : K[X])) +
          a3.derivative * (b6 * (6 : K[X])) +
          a2.derivative * (b7 * (7 : K[X])) +
          a1.derivative * (b8 * (8 : K[X])) +
          a0.derivative * (b9 * (9 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b5.derivative +
          (a3 * (3 : K[X])) * b6.derivative +
          (a2 * (2 : K[X])) * b7.derivative +
          a1 * b8.derivative)) =
      ((2 : K[X]) * H *
          (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
        (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
          H.derivative) +
        (18 : K[X]) * a3 *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((72 : K[X]) * a2 * H ^ 2 + (63 : K[X]) * a3 ^ 2) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) -
        (1152 : K[X]) * H ^ 4 * a0.derivative *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9) +
        (256 : K[X]) * H ^ 4 * a1.derivative *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H - Polynomial.C κ * H ^ 4) -
        (32 : K[X]) * H ^ 4 * a1 *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H -
            Polynomial.C κ * H ^ 4).derivative := by
  simp only [alignedFifthDefect410, alignedFourthDefect410,
    alignedThirdDefect410, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero, zero_add,
    add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face, with the consumed degree-`11`, degree-`10`,
and degree-`9` rows, the degree-`8` row is the weighted derivative
`2 H M₆' - 15 M₆ H' = 0`. -/
theorem alignedFifthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    (2 : K[X]) * H *
        (alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (15 : K[X]) *
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedFifthCoefficientJacobianRow_410 hp hq hjac
  rw [hp4] at hrow
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC5, hC6, hC7, hC8, hC9, hC4, hC3, hC2] at hrow
  have hR :
      (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
          (15 : K[X]) * p.coeff 3 ^ 2 * H - Polynomial.C κ * H ^ 4 =
        0 := by
    have hM' :
        (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
            (15 : K[X]) * p.coeff 3 ^ 2 * H = Polynomial.C κ * H ^ 4 := by
      simpa only [alignedSecondDefect410] using hM
    linear_combination hM'
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedFifthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hR, hB2, hB4] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Squared weight-`15/2` polynomial first integral -/

/-- Generic Wronskian quotient for the weight-`15/2` bracket: over a
characteristic-zero field, `2 H D' - 15 D H' = 0` forces
`D² = C c * H¹⁵`. -/
theorem fifteenthPowerRelation_of_weightFifteenHalfRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (15 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 15 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (15 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC15 : Polynomial.C (15 : K) = (15 : K[X]) :=
      Polynomial.C_eq_natCast 15
    rw [hC2, hC15]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 15) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (15 : K) * H ^ (15 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 15 =
          D * H ^ 14 *
            (Polynomial.C (15 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 15 hH) hW

/-- Squared weight-`15/2` polynomial first integral of the aligned
`(4,10)` fifth defect: `M₆² = κ₄ H¹⁵` — the odd fifteenth-power
discriminator shape, regenerated a second time below the ninth-power
shape of the degree-`10` row. -/
theorem alignedFifthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₄ : K,
      alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₄ * H ^ 15 :=
  fifteenthPowerRelation_of_weightFifteenHalfRow_410 hH
    (alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Chamber quotients of the fifteenth-power relation -/

/-- In the square chamber `H = h₀²` the fifteenth-power relation
resolves to the literal half-integral form `D = C μ * h₀¹⁵` with
`μ² = c`; the scalar `μ` is an honest residual and is not cleared. -/
theorem fifteenthPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 15) :
    ∃ μ : K, μ ^ 2 = c ∧ D = Polynomial.C μ * h0 ^ 15 := by
  have hdvd : (h0 ^ 15) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h30 := hrel
    rw [hF, hHsq] at h30
    apply mul_left_cancel₀ (pow_ne_zero 30 hh0)
    linear_combination h30
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ, hμ⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ]
    ring

/-- Parity kill in the nonsquare chamber: the odd exponent of the
fifteenth-power relation forces its constant to vanish, and with it the
whole fifth defect. -/
theorem fifteenthPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 15) : c = 0 ∧ D = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvd : (H ^ 7) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c * H, ?_⟩
    rw [hrel]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C c * H := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hH)
    have h14 := hrel
    rw [hG] at h14
    linear_combination h14
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C c := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hc : c = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [ha, zero_mul] at hev
    exact hev.symm
  refine ⟨hc, ?_⟩
  have hzero : D ^ 2 = 0 := by
    rw [hrel, hc, Polynomial.C_0, zero_mul]
  exact sq_eq_zero_iff.mp hzero

/-! ## Square chamber -/

/-- The consumed degree-`8` row in the square chamber: with the deep
divisibility `p₃ = h₀² u`, the resolved third and fourth defects, and
the square root `M₆ = μ₂ h₀¹⁵`, cancelling `h₀¹⁰` solves the quintic
row against the preserved constants `μ`, `κ₃`, and `μ₂`.  The new
letter `q₅` carries NO `h₀` factor — it sits at the same level as the
quintic core `6 u⁵ - 80 p₂ u³ + 480 p₂² u`. -/
theorem alignedSquareFifth_solved_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b5 b6 b7 : K[X]} {κ μ κ₃ μ₂ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15) :
    (512 : K[X]) * b5 =
      (6 : K[X]) * u ^ 5 - (80 : K[X]) * a2 * u ^ 3 +
        (480 : K[X]) * a2 ^ 2 * u +
        h0 ^ 2 * ((480 : K[X]) * a1 * u ^ 2 +
          (1920 : K[X]) * a1 * a2 +
          Polynomial.C κ * ((128 : K[X]) * a2 * u)) -
        Polynomial.C μ *
          (h0 ^ 3 * ((21 : K[X]) * u ^ 2 + (56 : K[X]) * a2)) +
        h0 ^ 4 * ((1920 : K[X]) * a0 * u +
          Polynomial.C κ * ((128 : K[X]) * a1) -
          Polynomial.C κ₃ * ((6 : K[X]) * u)) -
        Polynomial.C μ₂ * h0 ^ 5 := by
  have hM6' := hM6
  simp only [alignedFifthDefect410] at hM6'
  rw [hM2, hM4, hHsq, hp3] at hM6'
  apply mul_left_cancel₀ (pow_ne_zero 10 hh0)
  linear_combination -hM6'

/-! ## Nonsquare chamber -/

/-- The consumed degree-`8` row in the nonsquare chamber: with the
vanished third defect, the simple-root divisibility `p₃ = H g`, the
resolved fourth defect, and the parity-killed fifth defect, the quintic
coefficient is solved outright.  `q₅` carries no `H` factor: the
quintic core `6 g⁵ - 80 p₂ g³ + 480 p₂² g` sits at level zero. -/
theorem alignedNonsquareFifth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b5 b6 b7 : K[X]} {κ κ₃ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0) :
    (512 : K[X]) * b5 =
      (6 : K[X]) * g ^ 5 - (80 : K[X]) * a2 * g ^ 3 +
        (480 : K[X]) * a2 ^ 2 * g +
        H * ((480 : K[X]) * a1 * g ^ 2 + (1920 : K[X]) * a1 * a2 +
          Polynomial.C κ * ((128 : K[X]) * a2 * g)) +
        H ^ 2 * ((1920 : K[X]) * a0 * g +
          Polynomial.C κ * ((128 : K[X]) * a1) -
          Polynomial.C κ₃ * ((6 : K[X]) * g)) := by
  have hM6' := hM6
  simp only [alignedFifthDefect410] at hM6'
  rw [hM20, hM4, hg] at hM6'
  apply mul_left_cancel₀ (pow_ne_zero 5 hH)
  linear_combination -hM6'

/-! ## Source-facing fifth-row packets -/

/-- Source-facing squared weight-`15/2` integral of a normalized aligned
scale-two `(4,10)` source: the degree-`8` row is consumed into
`M₆² = κ₄ H¹⁵` on top of the previous aligned packet, together with the
chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedFifthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ : K,
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
  exact ⟨κ, κ₂, κ₃, κ₄, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber fifth packet of a normalized aligned scale-two
`(4,10)` source: the previous packet plus the square root
`M₆ = μ₂ h₀¹⁵` of the fifteenth-power integral and the solved quintic
row `512 q₅ = 6 u⁵ - 80 p₂ u³ + 480 p₂² u + h₀² (480 p₁ u² + 1920 p₁ p₂
+ 128 κ p₂ u) - μ h₀³ (21 u² + 56 p₂) + h₀⁴ (1920 p₀ u + 128 κ p₁
- 6 κ₃ u) - μ₂ h₀⁵`.  The constants `μ`, `κ₃`, and `μ₂` are preserved,
not cleared, and `q₅` carries no `h₀` factor. -/
theorem normalized410ScaleTwo_alignedFifthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ : K) (u : K[X]),
      p.coeff 3 = h0 ^ 2 * u ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        q.coeff 9 = Polynomial.C (5 / 2 : K) * u * h0 ^ 8 ∧
        (8 : K[X]) * q.coeff 8 =
          h0 ^ 6 * ((15 : K[X]) * u ^ 2 + (20 : K[X]) * p.coeff 2 +
            Polynomial.C κ * h0 ^ 2) ∧
        (16 : K[X]) * q.coeff 7 =
          h0 ^ 4 * ((5 : K[X]) * u ^ 3 +
            (60 : K[X]) * p.coeff 2 * u +
            (40 : K[X]) * p.coeff 1 * h0 ^ 2 +
            (4 : K[X]) * Polynomial.C κ * u * h0 ^ 2 -
            Polynomial.C μ * h0 ^ 3) ∧
        (128 : K[X]) * q.coeff 6 =
          h0 ^ 2 * ((240 : K[X]) * p.coeff 2 ^ 2 +
            (120 : K[X]) * p.coeff 2 * u ^ 2 -
            (5 : K[X]) * u ^ 4 + (320 : K[X]) * p.coeff 0 * h0 ^ 4 +
            (480 : K[X]) * p.coeff 1 * u * h0 ^ 2 +
            Polynomial.C κ *
              ((32 : K[X]) * p.coeff 2 * h0 ^ 2 +
                (16 : K[X]) * u ^ 2 * h0 ^ 2) -
            Polynomial.C μ * ((14 : K[X]) * u * h0 ^ 3) -
            Polynomial.C κ₃ * h0 ^ 4) ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₂ * h0 ^ 15 ∧
        (512 : K[X]) * q.coeff 5 =
          (6 : K[X]) * u ^ 5 - (80 : K[X]) * p.coeff 2 * u ^ 3 +
            (480 : K[X]) * p.coeff 2 ^ 2 * u +
            h0 ^ 2 * ((480 : K[X]) * p.coeff 1 * u ^ 2 +
              (1920 : K[X]) * p.coeff 1 * p.coeff 2 +
              Polynomial.C κ * ((128 : K[X]) * p.coeff 2 * u)) -
            Polynomial.C μ *
              (h0 ^ 3 * ((21 : K[X]) * u ^ 2 +
                (56 : K[X]) * p.coeff 2)) +
            h0 ^ 4 * ((1920 : K[X]) * p.coeff 0 * u +
              Polynomial.C κ * ((128 : K[X]) * p.coeff 1) -
              Polynomial.C κ₃ * ((6 : K[X]) * u)) -
            Polynomial.C μ₂ * h0 ^ 5 := by
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
  have hkill0 : ∀ a : K, h0.eval a = 0 → (p.coeff 3).eval a = 0 := by
    intro a ha
    apply alignedThird_rootKill_p3_410 hrel
    rw [hHsq]
    simp only [Polynomial.eval_pow, ha]
    norm_num
  obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
  obtain ⟨u, hu, hq6⟩ := alignedSquareFourth_descent_410 hh0 hdeg1 hcore
  have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
    fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
  have hq5 :=
    alignedSquareFifth_solved_410 hh0 hHsq hp3 hDform hM4 hM6form
  have hq9 := aligned_q9_solved_410 haligned
  have hclear := alignedSecondDefect_clearing_410 hM
  have hD' :
      (5 : K[X]) * p.coeff 3 ^ 3 +
            (60 : K[X]) * p.coeff 2 * p.coeff 3 * H ^ 2 +
            (40 : K[X]) * p.coeff 1 * H ^ 4 +
            (4 : K[X]) * Polynomial.C κ * p.coeff 3 * H ^ 3 -
          (16 : K[X]) * q.coeff 7 * H = Polynomial.C μ * h0 ^ 9 := by
    simpa only [alignedThirdDefect410] using hDform
  refine ⟨κ, μ, κ₃, μ₂, u, hp3, hDform, ?_, ?_, ?_, hq6, hM4,
    hM6form, hq5⟩
  · rw [hq9, hp3, hHsq]; ring
  · rw [hp3, hHsq] at hclear
    linear_combination hclear
  · apply mul_right_cancel₀ (pow_ne_zero 2 hh0)
    rw [hp3, hHsq] at hD'
    linear_combination -hD'

/-- Exact nonsquare-chamber fifth packet of a normalized aligned
scale-two `(4,10)` source: the previous packet plus the parity kill
`M₆ = 0` and the solved quintic row `512 q₅ = 6 g⁵ - 80 p₂ g³
+ 480 p₂² g + H (480 p₁ g² + 1920 p₁ p₂ + 128 κ p₂ g)
+ H² (1920 p₀ g + 128 κ p₁ - 6 κ₃ g)`.  No new divisibility on `g`
appears, and `q₅` carries no `H` factor. -/
theorem normalized410ScaleTwo_alignedFifthRow_nonsquareChamber_packet
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
    ∃ (κ κ₃ : K) (g : K[X]),
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
            (4 : K[X]) * Polynomial.C κ * g * H) ∧
        (128 : K[X]) * q.coeff 6 =
          H * ((320 : K[X]) * p.coeff 0 * H ^ 2 +
            (480 : K[X]) * p.coeff 1 * g * H +
            (240 : K[X]) * p.coeff 2 ^ 2 +
            (120 : K[X]) * p.coeff 2 * g ^ 2 -
            (5 : K[X]) * g ^ 4 +
            Polynomial.C κ *
              ((32 : K[X]) * p.coeff 2 * H +
                (16 : K[X]) * g ^ 2 * H) -
            Polynomial.C κ₃ * H ^ 2) ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        (512 : K[X]) * q.coeff 5 =
          (6 : K[X]) * g ^ 5 - (80 : K[X]) * p.coeff 2 * g ^ 3 +
            (480 : K[X]) * p.coeff 2 ^ 2 * g +
            H * ((480 : K[X]) * p.coeff 1 * g ^ 2 +
              (1920 : K[X]) * p.coeff 1 * p.coeff 2 +
              Polynomial.C κ * ((128 : K[X]) * p.coeff 2 * g)) +
            H ^ 2 * ((1920 : K[X]) * p.coeff 0 * g +
              Polynomial.C κ * ((128 : K[X]) * p.coeff 1) -
              Polynomial.C κ₃ * ((6 : K[X]) * g)) := by
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
  have hq6 := alignedNonsquareFourth_solved_410 hH hg hD0 hM4
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₄, hM60⟩ :=
    fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
  have hq5 := alignedNonsquareFifth_solved_410 hH hg hD0 hM4 hM60
  have hq9 := aligned_q9_solved_410 haligned
  have hclear := alignedSecondDefect_clearing_410 hM
  have hD0' :
      (5 : K[X]) * p.coeff 3 ^ 3 +
            (60 : K[X]) * p.coeff 2 * p.coeff 3 * H ^ 2 +
            (40 : K[X]) * p.coeff 1 * H ^ 4 +
            (4 : K[X]) * Polynomial.C κ * p.coeff 3 * H ^ 3 -
          (16 : K[X]) * q.coeff 7 * H = 0 := by
    simpa only [alignedThirdDefect410] using hD0
  refine ⟨κ, κ₃, g, hg, hD0, ?_, ?_, ?_, hq6, hM4, hM60, hq5⟩
  · rw [hq9, hg]; ring
  · rw [hg] at hclear
    linear_combination hclear
  · apply mul_right_cancel₀ hH
    rw [hg] at hD0'
    linear_combination -hD0'

/-- Honest square/nonsquare chamber split of the consumed degree-`8`
aligned row.  In the nonsquare chamber the fifteenth-power constant is
forced to zero by parity and `q₅` is solved outright; in the square
chamber the residual `μ₂` survives inside the solved `q₅`.  Neither
chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedFifthRow_chamberDichotomy
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
      ∃ (κ μ κ₃ μ₂ : K) (u : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₃ * H ^ 6 ∧
          alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C μ₂ * h0 ^ 15 ∧
          (512 : K[X]) * q.coeff 5 =
            (6 : K[X]) * u ^ 5 - (80 : K[X]) * p.coeff 2 * u ^ 3 +
              (480 : K[X]) * p.coeff 2 ^ 2 * u +
              h0 ^ 2 * ((480 : K[X]) * p.coeff 1 * u ^ 2 +
                (1920 : K[X]) * p.coeff 1 * p.coeff 2 +
                Polynomial.C κ * ((128 : K[X]) * p.coeff 2 * u)) -
              Polynomial.C μ *
                (h0 ^ 3 * ((21 : K[X]) * u ^ 2 +
                  (56 : K[X]) * p.coeff 2)) +
              h0 ^ 4 * ((1920 : K[X]) * p.coeff 0 * u +
                Polynomial.C κ * ((128 : K[X]) * p.coeff 1) -
                Polynomial.C κ₃ * ((6 : K[X]) * u)) -
              Polynomial.C μ₂ * h0 ^ 5) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₃ : K) (g : K[X]),
        p.coeff 3 = H * g ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = 0 ∧
          alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₃ * H ^ 6 ∧
          alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
          (512 : K[X]) * q.coeff 5 =
            (6 : K[X]) * g ^ 5 - (80 : K[X]) * p.coeff 2 * g ^ 3 +
              (480 : K[X]) * p.coeff 2 ^ 2 * g +
              H * ((480 : K[X]) * p.coeff 1 * g ^ 2 +
                (1920 : K[X]) * p.coeff 1 * p.coeff 2 +
                Polynomial.C κ * ((128 : K[X]) * p.coeff 2 * g)) +
              H ^ 2 * ((1920 : K[X]) * p.coeff 0 * g +
                Polynomial.C κ * ((128 : K[X]) * p.coeff 1) -
                Polynomial.C κ₃ * ((6 : K[X]) * g))) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedFifthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, u, hp3, hM2f, _hq9, _hq8, _hq7, _hq6, hM4,
      hM6f, hq5⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₃, μ₂, u, hp3, hM2f, hM4,
      hM6f, hq5⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedFifthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g, hg, hM20, _hq9, _hq8, _hq7, _hq6, hM4, hM60,
      hq5⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₃, g, hg, hM20, hM4, hM60, hq5⟩

/-- Extended root data of the consumed degree-`8` row: at scale two the
common core has a root where the full jet `p₃, q₉, q₈, q₇, q₆` vanishes
with `q₈` and `q₇` vanishing to second order, chamber-free; the square
chamber adds `p₃'(a) = 0` and `q₆'(a) = 0`.  The NEW degree-`8` content
is the honest value tie `512 q₅(a) = 6 w⁵ - 80 p₂ w³ + 480 p₂² w` at
the root for the chamber quotient `w` (`u` or `g`) — `q₅` does NOT
vanish and no new kill is claimed. -/
theorem normalized410ScaleTwo_alignedFifthRow_rootData
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
      (q.coeff 8).derivative.eval a = 0 ∧
      (q.coeff 7).eval a = 0 ∧
      (q.coeff 7).derivative.eval a = 0 ∧
      (q.coeff 6).eval a = 0 ∧
      ((∃ h0 u : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          (q.coeff 6).derivative.eval a = 0 ∧
          (512 : K) * (q.coeff 5).eval a =
            (6 : K) * u.eval a ^ 5 -
              (80 : K) * (p.coeff 2).eval a * u.eval a ^ 3 +
              (480 : K) * (p.coeff 2).eval a ^ 2 * u.eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g : K[X], p.coeff 3 = H * g ∧
            (512 : K) * (q.coeff 5).eval a =
              (6 : K) * g.eval a ^ 5 -
                (80 : K) * (p.coeff 2).eval a * g.eval a ^ 3 +
                (480 : K) * (p.coeff 2).eval a ^ 2 * g.eval a)) := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hHne
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedFifthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, u, hp3, _hM2f, hq9, hq8, hq7, hq6, _hM4,
      _hM6f, hq5⟩ := hpacket
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hp3d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        P).coeff 3).derivative.eval a = 0 :=
      derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hp3 hroot
    have hq8d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 8).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 6) hq8 hroot
      have h8 : (8 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 8).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : K) ≠ 0)
    have hq7d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 7).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 4) hq7 hroot
      have h16 : (16 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 7).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h16).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    have hq6d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 6).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hq6 hroot
      have h128 : (128 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 6).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h128).resolve_left
        (by norm_num : (128 : K) ≠ 0)
    have hq5tie : (512 : K) *
        (((Polynomial.Bivariate.equivMvPolynomial K).symm
          Q).coeff 5).eval a =
        (6 : K) * u.eval a ^ 5 -
          (80 : K) * (((Polynomial.Bivariate.equivMvPolynomial K).symm
            P).coeff 2).eval a * u.eval a ^ 3 +
          (480 : K) * (((Polynomial.Bivariate.equivMvPolynomial K).symm
            P).coeff 2).eval a ^ 2 * u.eval a := by
      have hev := congrArg (fun f : K[X] => f.eval a) hq5
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    refine ⟨a, ?_, ?_, ?_, ?_, hq8d, ?_, hq7d, ?_,
      Or.inl ⟨h0, u, hh0, hHsq, hroot, hp3, hp3d, hq6d, hq5tie⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp3, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (8 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (6 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (8 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (128 : K) ≠ 0)
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedFifthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g, hp3, _hM20, hq9, hq8, hq7, hq6, _hM4, _hM60,
      hq5⟩ := hpacket
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hHne, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hq8d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 8).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 3) hq8 hroot
      have h8 : (8 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 8).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : K) ≠ 0)
    have hq7d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 7).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hq7 hroot
      have h16 : (16 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 7).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h16).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    have hq5tie : (512 : K) *
        (((Polynomial.Bivariate.equivMvPolynomial K).symm
          Q).coeff 5).eval a =
        (6 : K) * g.eval a ^ 5 -
          (80 : K) * (((Polynomial.Bivariate.equivMvPolynomial K).symm
            P).coeff 2).eval a * g.eval a ^ 3 +
          (480 : K) * (((Polynomial.Bivariate.equivMvPolynomial K).symm
            P).coeff 2).eval a ^ 2 * g.eval a := by
      have hev := congrArg (fun f : K[X] => f.eval a) hq5
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    refine ⟨a, hroot, ?_, ?_, ?_, hq8d, ?_, hq7d, ?_,
      Or.inr ⟨hnsq, g, hp3, hq5tie⟩⟩
    · rw [hp3, Polynomial.eval_mul, hroot, zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (8 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (128 : K) ≠ 0)

#print axioms alignedFifthCoefficientJacobianRow_410
#print axioms alignedFifthDefect_weightedDerivative_identity_410
#print axioms alignedFifthDefectRow_eq_zero_410
#print axioms fifteenthPowerRelation_of_weightFifteenHalfRow_410
#print axioms alignedFifthDefectPowerRelation_410
#print axioms fifteenthPower_squareChamber_form_410
#print axioms fifteenthPower_nonsquareChamber_kill_410
#print axioms alignedSquareFifth_solved_410
#print axioms alignedNonsquareFifth_solved_410
#print axioms normalized410ScaleTwo_alignedFifthRow_packet
#print axioms normalized410ScaleTwo_alignedFifthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedFifthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedFifthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedFifthRow_rootData

end Max11DegreeRoutes
