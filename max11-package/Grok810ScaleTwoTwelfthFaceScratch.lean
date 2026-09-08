import Grok810ScaleTwoEleventhFaceScratch

/-! # Scale-two twelfth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the eleventh-face packet supplies the degree-`6`
Jacobian row and the two-component jet `v₀ = h v₁`, `s₀ = h s₁`,
`u₀ = h u₁`, `w₀ = h w₁`, `q₆ = h² b₆₂` together with `h⁸ ∣ q₉`.  On
the left the source-facing loads are `Gred, Vred, Wred, Xred`; on the
right, `t₀ = 0`, `4 s₁ = 5 v₁`, `4 w₁ = 5 u₁`,
`40 a₄ - 32 b₆₂ + 5 v₁² = 0`, `16 b₅ = 5 u₁ v₁`,
`16 b₆₂ v₁ + 10 u₁² - 5 v₁³ = 0`, and the alternative
`u₁ (5 v₁² - 8 b₆₂) = 0` refined into the `u₁ = 0` sibling
`32 w₂ - 40 u₂ = v₁ (10 t₁ - 9 λ)` together with the complementary
factor `8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`, `2 u₁² + v₁³ = 0`.

The next unused Keller coefficient is the degree-`5` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- E R' - 2 D S' - 3 C T' - 4 B U' - 5 A V' - 6 G W' = 0`.
Clearing the corresponding first integral against the remaining decic
coordinate produces a defect larger than the remaining exact jet, so
this file isolates that Jacobian identity and the strongest exact
source-facing refinement of the left component, the `u₁ = 0` sibling,
and the complementary factor.

On the left, the tenth-face seventh load factors as the alternative
`(t₀³ - 4 t₀ v₁ + 8 u₁) (11 t₀⁶ - 88 t₀⁴ v₁ - 256 t₀³ u₁
+ 320 t₀² v₁² + 1024 t₀ u₁ v₁ - 1024 u₁² - 512 v₁³) = 0`.  The first
factor solves `u₁` and upgrades the third-defect reduction to
`128 w₁ = 5 t₀ (24 v₁ - 5 t₀²)`.  Independently, the second and third
defects at the next order of the already-vanishing ninth-face
combinations force `m₁(a) + 9 λ t₀(a) = 0` and
`4 τ₁(a) + 9 λ t₀(a)² + 144 λ v₁(a) = 0` where
`32 s₁ - 40 v₁ - 5 t₀² = h m₁` and
`128 w₁ - 160 u₁ - 40 t₀ v₁ + 5 t₀³ = h τ₁`.  On the `u₁ = 0`
sibling the same second defect upgrades `4 s₁ = 5 v₁` to
`h² ∣ (4 s₁ - 5 v₁)`, and the seventh defect at the next order forces
`v₁³ (3 λ v₁ + 160 t₁ v₁ - 320 u₂) = 0`.  On the complementary factor
the second defect likewise supplies `h² ∣ (4 s₁ - 5 v₁)`, while the
third defect at the next order of `4 w₁ - 5 u₁ = h ω` forces
`8 ω(a) = v₁(a) (10 t₁(a) - 9 λ)`.  Neither factor is closed further:
no individual vanishing of `v₁, a₄, t₀, t₁, p₃, q₄` is claimed, and
the aligned face `N = 0` remains open.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The twelfth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the eleventh face
start at degree `5`. -/
theorem twelfthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Scalar algebra of the eleventh-face siblings -/

section TwelfthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- First factor of the left seventh-load eliminant. -/
def twelfthFace_leftF1_810 (t0 v1 u1 : F) : Prop :=
  t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1 = 0

/-- Second factor of the left seventh-load eliminant. -/
def twelfthFace_leftF2_810 (t0 v1 u1 : F) : Prop :=
  (11 : F) * t0 ^ 6 - (88 : F) * t0 ^ 4 * v1 -
      (256 : F) * t0 ^ 3 * u1 + (320 : F) * t0 ^ 2 * v1 ^ 2 +
    (1024 : F) * t0 * u1 * v1 - (1024 : F) * u1 ^ 2 -
      (512 : F) * v1 ^ 3 = 0

set_option maxHeartbeats 8000000 in
/-- The tenth-face fourth through seventh loads force the left
alternative `F₁ F₂ = 0`. -/
theorem twelfthFace_left_alternative810 (t0 v1 u1 a4 b62 b5 : F)
    (hG : tenthFace_Gred810 t0 v1 u1 a4 b62)
    (hV : tenthFace_Vred810 t0 v1 u1 a4 b62 b5)
    (hW : tenthFace_Wred810 t0 v1 u1 a4 b62 b5)
    (hX : tenthFace_Xred810 t0 v1 u1 a4 b62 b5) :
    twelfthFace_leftF1_810 t0 v1 u1 ∨
      twelfthFace_leftF2_810 t0 v1 u1 := by
  unfold tenthFace_Gred810 tenthFace_Vred810 tenthFace_Wred810
    tenthFace_Xred810 twelfthFace_leftF1_810 twelfthFace_leftF2_810
    at *
  have h2560 : (2560 : F) ≠ 0 := by norm_num
  have hid :
      ((3 : F) * t0 ^ 2 - (8 : F) * v1) *
            ((4177920 : F) * a4 * t0 ^ 3 -
              (11796480 : F) * a4 * t0 * v1 +
              (10485760 : F) * a4 * u1 +
              (7208960 : F) * b5 * t0 ^ 2 -
              (10485760 : F) * b5 * v1 -
              (6848512 : F) * b62 * t0 ^ 3 +
              (17301504 : F) * b62 * t0 * v1 -
              (12582912 : F) * b62 * u1 + (300960 : F) * t0 ^ 7 -
              (2675200 : F) * t0 ^ 5 * v1 +
              (4561920 : F) * t0 ^ 4 * u1 +
              (7096320 : F) * t0 ^ 3 * v1 ^ 2 -
              (15769600 : F) * t0 ^ 2 * u1 * v1 +
              (7208960 : F) * t0 * u1 ^ 2 -
              (5406720 : F) * t0 * v1 ^ 3 +
              (7208960 : F) * u1 * v1 ^ 2) +
          ((384 : F) * t0 ^ 5 - (8192 : F) * t0 ^ 3 * v1 -
              (12288 : F) * t0 ^ 2 * u1 +
            (24576 : F) * t0 * v1 ^ 2) *
            ((2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
              (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
              (320 : F) * v1 ^ 2) +
          ((95 : F) * t0 ^ 4 - (120 : F) * t0 ^ 2 * v1 +
              (640 : F) * t0 * u1 - (640 : F) * v1 ^ 2) *
            ((81920 : F) * a4 * t0 + (131072 : F) * b5 -
              (98304 : F) * b62 * t0 + (2912 : F) * t0 ^ 5 -
              (20480 : F) * t0 ^ 3 * v1 +
              (46080 : F) * t0 ^ 2 * u1 +
              (30720 : F) * t0 * v1 ^ 2 - (40960 : F) * u1 * v1) +
          ((416 : F) * t0 ^ 3 - (1280 : F) * t0 * v1 +
              (1024 : F) * u1) *
            (-(51200 : F) * a4 * t0 ^ 2 + (81920 : F) * a4 * v1 -
              (81920 : F) * b5 * t0 + (73728 : F) * b62 * t0 ^ 2 -
              (98304 : F) * b62 * v1 - (2800 : F) * t0 ^ 6 +
              (22080 : F) * t0 ^ 4 * v1 - (41600 : F) * t0 ^ 3 * u1 -
              (46080 : F) * t0 ^ 2 * v1 ^ 2 +
              (87040 : F) * t0 * u1 * v1 - (20480 : F) * u1 ^ 2 +
              (20480 : F) * v1 ^ 3) =
        (2560 : F) *
          ((t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) *
            ((11 : F) * t0 ^ 6 - (88 : F) * t0 ^ 4 * v1 -
              (256 : F) * t0 ^ 3 * u1 +
              (320 : F) * t0 ^ 2 * v1 ^ 2 +
              (1024 : F) * t0 * u1 * v1 - (1024 : F) * u1 ^ 2 -
              (512 : F) * v1 ^ 3)) := by
    ring
  have hprod :
      (2560 : F) *
          ((t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) *
            ((11 : F) * t0 ^ 6 - (88 : F) * t0 ^ 4 * v1 -
              (256 : F) * t0 ^ 3 * u1 +
              (320 : F) * t0 ^ 2 * v1 ^ 2 +
              (1024 : F) * t0 * u1 * v1 - (1024 : F) * u1 ^ 2 -
              (512 : F) * v1 ^ 3)) =
        0 := by
    rw [← hid]
    linear_combination ((3 : F) * t0 ^ 2 - (8 : F) * v1) * hX +
      ((384 : F) * t0 ^ 5 - (8192 : F) * t0 ^ 3 * v1 -
          (12288 : F) * t0 ^ 2 * u1 + (24576 : F) * t0 * v1 ^ 2) *
        hG +
      ((95 : F) * t0 ^ 4 - (120 : F) * t0 ^ 2 * v1 +
          (640 : F) * t0 * u1 - (640 : F) * v1 ^ 2) *
        hV +
      ((416 : F) * t0 ^ 3 - (1280 : F) * t0 * v1 + (1024 : F) * u1) *
        hW
  have hzero := (mul_eq_zero.mp hprod).resolve_left h2560
  exact mul_eq_zero.mp hzero

/-- On the first left factor, the third-defect reduction solves `w₁`. -/
theorem twelfthFace_leftF1_w1_810 (t0 v1 u1 w1 : F)
    (hF1 : twelfthFace_leftF1_810 t0 v1 u1)
    (hT : (128 : F) * w1 - (160 : F) * u1 - (40 : F) * t0 * v1 +
      (5 : F) * t0 ^ 3 = 0) :
    (128 : F) * w1 - (5 : F) * t0 * ((24 : F) * v1 - (5 : F) * t0 ^ 2) =
      0 := by
  unfold twelfthFace_leftF1_810 at hF1
  have hid :
      (128 : F) * w1 - (5 : F) * t0 *
            ((24 : F) * v1 - (5 : F) * t0 ^ 2) =
        (128 : F) * w1 - (160 : F) * u1 - (40 : F) * t0 * v1 +
          (5 : F) * t0 ^ 3 +
        (20 : F) *
          (t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) := by
    ring
  rw [hid]
  linear_combination hT + (20 : F) * hF1

/-- On the first left factor, the fourth-defect reduction specialises. -/
theorem twelfthFace_leftF1_G_810 (t0 v1 u1 a4 b62 : F)
    (hF1 : twelfthFace_leftF1_810 t0 v1 u1)
    (hG : tenthFace_Gred810 t0 v1 u1 a4 b62) :
    (2560 : F) * a4 - (2048 : F) * b62 - (45 : F) * t0 ^ 4 +
        (80 : F) * t0 ^ 2 * v1 + (320 : F) * v1 ^ 2 =
      0 := by
  unfold twelfthFace_leftF1_810 tenthFace_Gred810 at *
  have hid :
      (2560 : F) * a4 - (2048 : F) * b62 - (45 : F) * t0 ^ 4 +
          (80 : F) * t0 ^ 2 * v1 + (320 : F) * v1 ^ 2 =
        (2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
          (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
          (320 : F) * v1 ^ 2 -
        (80 : F) * t0 *
          (t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) := by
    ring
  rw [hid]
  linear_combination hG - (80 : F) * t0 * hF1

/-- Combining the next-order second and third defects on the left. -/
theorem twelfthFace_left_T_nextOrder810 (t0 v1 m1 tau1 : F)
    (lambda : F)
    (hM : m1 + (9 : F) * lambda * t0 = 0)
    (hT : (4 : F) * tau1 - (16 : F) * t0 * m1 +
        (144 : F) * lambda * v1 - (135 : F) * lambda * t0 ^ 2 =
      0) :
    (4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
      (144 : F) * lambda * v1 = 0 := by
  have hid :
      (4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
          (144 : F) * lambda * v1 =
        (4 : F) * tau1 - (16 : F) * t0 * m1 +
          (144 : F) * lambda * v1 - (135 : F) * lambda * t0 ^ 2 +
        (16 : F) * t0 * (m1 + (9 : F) * lambda * t0) := by
    ring
  rw [hid]
  linear_combination hT + (16 : F) * t0 * hM

/-- The unreduced seventh defect at the next `u₁ = 0` order, after
reducing by the ninth-face `M, G` and the eleventh-face `T, V`. -/
def twelfthFace_zeroU1_Xred810 (v1 t1 u2 b62 : F) (lambda : F) : Prop :=
  -(576 : F) * b62 * lambda * v1 - (6400 : F) * b62 * t1 * v1 +
      (5120 : F) * b62 * u2 + (195 : F) * lambda * v1 ^ 3 +
    (2800 : F) * t1 * v1 ^ 3 - (3200 : F) * u2 * v1 ^ 2 = 0

set_option maxHeartbeats 8000000 in
/-- The seventh defect at the next `u₁ = 0` order reduces to
`Xred`. -/
theorem twelfthFace_zeroU1_X_nextOrder810 (v1 s1 t1 u2 w2 a4 b62 b51 :
    F) (lambda : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 = 0)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hT : (32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 = 0)
    (hV : (2560 : F) * b51 + (576 : F) * lambda * b62 -
        (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
      (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1 = 0)
    (hX : -(6488064 : F) * a4 * lambda * v1 +
        (23068672 : F) * a4 * s1 * t1 -
        (36044800 : F) * a4 * t1 * v1 + (28835840 : F) * a4 * u2 -
        (14680064 : F) * a4 * w2 - (10485760 : F) * b51 * v1 +
        (17301504 : F) * b62 * t1 * v1 -
        (12582912 : F) * b62 * u2 + (2568192 : F) * lambda * v1 ^ 3 -
        (27394048 : F) * s1 * t1 * v1 ^ 2 +
        (23068672 : F) * s1 * u2 * v1 +
        (25681920 : F) * t1 * v1 ^ 3 -
        (34242560 : F) * u2 * v1 ^ 2 +
        (10092544 : F) * v1 ^ 2 * w2 = 0) :
    twelfthFace_zeroU1_Xred810 v1 t1 u2 b62 lambda := by
  unfold twelfthFace_zeroU1_Xred810
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have hid :
      (5 : F) *
          (-(6488064 : F) * a4 * lambda * v1 +
            (23068672 : F) * a4 * s1 * t1 -
            (36044800 : F) * a4 * t1 * v1 +
            (28835840 : F) * a4 * u2 - (14680064 : F) * a4 * w2 -
            (10485760 : F) * b51 * v1 +
            (17301504 : F) * b62 * t1 * v1 -
            (12582912 : F) * b62 * u2 +
            (2568192 : F) * lambda * v1 ^ 3 -
            (27394048 : F) * s1 * t1 * v1 ^ 2 +
            (23068672 : F) * s1 * u2 * v1 +
            (25681920 : F) * t1 * v1 ^ 3 -
            (34242560 : F) * u2 * v1 ^ 2 +
            (10092544 : F) * v1 ^ 2 * w2) +
        (4096 : F) *
          (-(576 : F) * b62 * lambda * v1 -
            (6400 : F) * b62 * t1 * v1 + (5120 : F) * b62 * u2 +
            (195 : F) * lambda * v1 ^ 3 +
            (2800 : F) * t1 * v1 ^ 3 - (3200 : F) * u2 * v1 ^ 2) =
        (45056 : F) *
            ((64 : F) * b62 * t1 - (105 : F) * t1 * v1 ^ 2 +
              (80 : F) * u2 * v1) *
            ((32 : F) * s1 - (40 : F) * v1) -
          (32768 : F) *
            ((9 : F) * lambda * v1 + (45 : F) * t1 * v1 -
              (40 : F) * u2) *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) +
          (28672 : F) * (-(64 : F) * b62 + (65 : F) * v1 ^ 2) *
            ((32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
              (9 : F) * lambda * v1) -
          (20480 : F) * v1 *
            ((2560 : F) * b51 + (576 : F) * lambda * b62 -
              (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
              (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1) +
          (90112 : F) * t1 *
            ((32 : F) * s1 - (40 : F) * v1) *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) -
          (57344 : F) *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) *
            ((32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
              (9 : F) * lambda * v1) := by
    ring
  have hsum :
      (5 : F) *
          (-(6488064 : F) * a4 * lambda * v1 +
            (23068672 : F) * a4 * s1 * t1 -
            (36044800 : F) * a4 * t1 * v1 +
            (28835840 : F) * a4 * u2 - (14680064 : F) * a4 * w2 -
            (10485760 : F) * b51 * v1 +
            (17301504 : F) * b62 * t1 * v1 -
            (12582912 : F) * b62 * u2 +
            (2568192 : F) * lambda * v1 ^ 3 -
            (27394048 : F) * s1 * t1 * v1 ^ 2 +
            (23068672 : F) * s1 * u2 * v1 +
            (25681920 : F) * t1 * v1 ^ 3 -
            (34242560 : F) * u2 * v1 ^ 2 +
            (10092544 : F) * v1 ^ 2 * w2) +
        (4096 : F) *
          (-(576 : F) * b62 * lambda * v1 -
            (6400 : F) * b62 * t1 * v1 + (5120 : F) * b62 * u2 +
            (195 : F) * lambda * v1 ^ 3 +
            (2800 : F) * t1 * v1 ^ 3 - (3200 : F) * u2 * v1 ^ 2) =
        0 := by
    rw [hid, hM, hG, hT, hV]
    ring
  have hR :
      (4096 : F) *
          (-(576 : F) * b62 * lambda * v1 -
            (6400 : F) * b62 * t1 * v1 + (5120 : F) * b62 * u2 +
            (195 : F) * lambda * v1 ^ 3 +
            (2800 : F) * t1 * v1 ^ 3 - (3200 : F) * u2 * v1 ^ 2) =
        0 := by
    linear_combination hsum - (5 : F) * hX
  exact (mul_eq_zero.mp hR).resolve_left h4096

/-- The tenth-face sixth load on `u₁ = 0` together with the next
seventh defect force `v₁³ (3 λ v₁ + 160 t₁ v₁ - 320 u₂) = 0`. -/
theorem twelfthFace_zeroU1_seventh_product810 (v1 t1 u2 b62 : F)
    (lambda : F)
    (hW : (16 : F) * b62 * v1 - (5 : F) * v1 ^ 3 = 0)
    (hX : twelfthFace_zeroU1_Xred810 v1 t1 u2 b62 lambda) :
    v1 ^ 3 *
        ((3 : F) * lambda * v1 + (160 : F) * t1 * v1 -
          (320 : F) * u2) =
      0 := by
  unfold twelfthFace_zeroU1_Xred810 at hX
  have h5 : (5 : F) ≠ 0 := by norm_num
  have hid :
      (5 : F) *
          (v1 ^ 3 *
            ((3 : F) * lambda * v1 + (160 : F) * t1 * v1 -
              (320 : F) * u2)) =
        v1 *
            (-(576 : F) * b62 * lambda * v1 -
              (6400 : F) * b62 * t1 * v1 + (5120 : F) * b62 * u2 +
              (195 : F) * lambda * v1 ^ 3 +
              (2800 : F) * t1 * v1 ^ 3 - (3200 : F) * u2 * v1 ^ 2) -
          (-(36 : F) * lambda * v1 - (400 : F) * t1 * v1 +
              (320 : F) * u2) *
            ((16 : F) * b62 * v1 - (5 : F) * v1 ^ 3) := by
    ring
  have hcomb :
      (5 : F) *
          (v1 ^ 3 *
            ((3 : F) * lambda * v1 + (160 : F) * t1 * v1 -
              (320 : F) * u2)) =
        0 := by
    rw [hid]
    linear_combination v1 * hX -
      (-(36 : F) * lambda * v1 - (400 : F) * t1 * v1 +
          (320 : F) * u2) *
        hW
  exact (mul_eq_zero.mp hcomb).resolve_left h5

/-- The complementary third defect at the next order of
`4 w₁ - 5 u₁ = ω h` is `8 ω = v₁ (10 t₁ - 9 λ)`. -/
theorem twelfthFace_comp_T_nextOrder810 (v1 s1 t1 omega : F)
    (lambda : F)
    (hM : (4 : F) * s1 - (5 : F) * v1 = 0)
    (hT : (128 : F) * omega - (512 : F) * s1 * t1 +
        (480 : F) * t1 * v1 + (144 : F) * lambda * v1 = 0) :
    (8 : F) * omega - (10 : F) * t1 * v1 + (9 : F) * lambda * v1 =
      0 := by
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hid :
      (16 : F) *
          ((8 : F) * omega - (10 : F) * t1 * v1 +
            (9 : F) * lambda * v1) =
        (128 : F) * omega - (512 : F) * s1 * t1 +
          (480 : F) * t1 * v1 + (144 : F) * lambda * v1 +
        (128 : F) * t1 * ((4 : F) * s1 - (5 : F) * v1) := by
    ring
  have hcomb :
      (16 : F) *
          ((8 : F) * omega - (10 : F) * t1 * v1 +
            (9 : F) * lambda * v1) =
        0 := by
    rw [hid]
    linear_combination hT + (128 : F) * t1 * hM
  exact (mul_eq_zero.mp hcomb).resolve_left h16

/-! ## Extra-`h` substitutions on the complementary third defect and
the `u₁ = 0` seventh defect -/

/-- Cofactor of `h` in the sixth-jet third defect after the extra right
vanishing `t₀ = h t₁`. -/
def twelfthFace_comp_thirdCof810 (h t1 v1 s1 w1 u1 : F[X])
    (lambda : F) : F[X] :=
  -(640 : F[X]) * u1 + (512 : F[X]) * w1 +
    (-(512 : F[X]) * s1 * t1 + (480 : F[X]) * t1 * v1 +
      (144 : F[X]) * Polynomial.C lambda * v1) * h +
    ((100 : F[X]) * t1 ^ 3 -
        (135 : F[X]) * Polynomial.C lambda * t1 ^ 2) * h ^ 3

theorem twelfthFace_comp_third_mul_h
    (h t1 v1 s1 w1 u1 : F[X]) (lambda : F) :
    thirdJetParen810_leftCofactor h (h * t1) v1 s1 w1 u1 lambda =
      twelfthFace_comp_thirdCof810 h t1 v1 s1 w1 u1 lambda := by
  simp only [thirdJetParen810_leftCofactor, twelfthFace_comp_thirdCof810]
  ring

theorem twelfthFace_comp_thirdCof_omega
    (h t1 v1 s1 w1 u1 omega : F[X]) (lambda : F)
    (homega : (4 : F[X]) * w1 - (5 : F[X]) * u1 = h * omega) :
    twelfthFace_comp_thirdCof810 h t1 v1 s1 w1 u1 lambda =
      h *
        ((128 : F[X]) * omega - (512 : F[X]) * s1 * t1 +
          (480 : F[X]) * t1 * v1 +
          (144 : F[X]) * Polynomial.C lambda * v1 +
          ((100 : F[X]) * t1 ^ 3 -
              (135 : F[X]) * Polynomial.C lambda * t1 ^ 2) *
            h ^ 2) := by
  simp only [twelfthFace_comp_thirdCof810]
  have hid :
      -(640 : F[X]) * u1 + (512 : F[X]) * w1 =
        (128 : F[X]) * ((4 : F[X]) * w1 - (5 : F[X]) * u1) := by
    ring
  rw [hid, homega]
  ring

theorem eval_twelfthFace_comp_Tcof810
    (h t1 v1 s1 omega : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((128 : F[X]) * omega - (512 : F[X]) * s1 * t1 +
          (480 : F[X]) * t1 * v1 +
          (144 : F[X]) * Polynomial.C lambda * v1 +
          ((100 : F[X]) * t1 ^ 3 -
              (135 : F[X]) * Polynomial.C lambda * t1 ^ 2) *
            h ^ 2) =
      (128 : F) * Polynomial.eval root omega -
        (512 : F) * Polynomial.eval root s1 * Polynomial.eval root t1 +
        (480 : F) * Polynomial.eval root t1 *
          Polynomial.eval root v1 +
        (144 : F) * lambda * Polynomial.eval root v1 := by
  simp [hroot]

/-- Cofactor of `h⁴` in the sixth-jet seventh defect after the extra
`u₁ = 0` vanishing `t₀ = h t₁`, `u₁ = h u₂`, `w₁ = h w₂`,
`b₅ = h b₅₁`. -/
def twelfthFace_zeroU1_Xcof810
    (h t1 v1 s1 w2 u2 a4 a3 a2 a1 b62 b51 b4 b3 : F[X])
    (lambda : F) : F[X] :=
  -(6488064 : F[X]) * a4 * Polynomial.C lambda * v1 +
    (23068672 : F[X]) * a4 * s1 * t1 -
    (36044800 : F[X]) * a4 * t1 * v1 + (28835840 : F[X]) * a4 * u2 -
    (14680064 : F[X]) * a4 * w2 - (10485760 : F[X]) * b51 * v1 +
    (17301504 : F[X]) * b62 * t1 * v1 -
    (12582912 : F[X]) * b62 * u2 +
    (2568192 : F[X]) * Polynomial.C lambda * v1 ^ 3 -
    (27394048 : F[X]) * s1 * t1 * v1 ^ 2 +
    (23068672 : F[X]) * s1 * u2 * v1 +
    (25681920 : F[X]) * t1 * v1 ^ 3 -
    (34242560 : F[X]) * u2 * v1 ^ 2 +
    (10092544 : F[X]) * v1 ^ 2 * w2 +
    (-(16777216 : F[X]) * a3 * s1 + (28835840 : F[X]) * a3 * v1) *
      h +
    ((7704576 : F[X]) * a4 * Polynomial.C lambda * t1 ^ 2 -
        (8388608 : F[X]) * b4 * t1 +
      (7208960 : F[X]) * b51 * t1 ^ 2 -
        (6848512 : F[X]) * b62 * t1 ^ 3 -
      (13001472 : F[X]) * Polynomial.C lambda * t1 ^ 2 * v1 ^ 2 +
        (15409152 : F[X]) * Polynomial.C lambda * t1 * u2 * v1 -
      (3244032 : F[X]) * Polynomial.C lambda * u2 ^ 2 +
        (30818304 : F[X]) * s1 * t1 ^ 3 * v1 -
      (27394048 : F[X]) * s1 * t1 ^ 2 * u2 -
        (19261440 : F[X]) * t1 ^ 3 * v1 ^ 2 +
      (38522880 : F[X]) * t1 ^ 2 * u2 * v1 -
        (23969792 : F[X]) * t1 ^ 2 * v1 * w2 -
      (18022400 : F[X]) * t1 * u2 ^ 2 +
        (20185088 : F[X]) * t1 * u2 * w2) *
      h ^ 2 +
    (-(6488064 : F[X]) * a3 * Polynomial.C lambda * t1 -
        (1802240 : F[X]) * a3 * t1 ^ 2 +
      (16777216 : F[X]) * b3) * h ^ 3 +
    ((4718592 : F[X]) * a2 * Polynomial.C lambda +
        (5242880 : F[X]) * a2 * t1 +
      (9480240 : F[X]) * Polynomial.C lambda * t1 ^ 4 * v1 -
        (8667648 : F[X]) * Polynomial.C lambda * t1 ^ 3 * u2 -
      (6741504 : F[X]) * s1 * t1 ^ 5 -
        (2106720 : F[X]) * t1 ^ 5 * v1 +
      (1203840 : F[X]) * t1 ^ 4 * u2 +
        (6741504 : F[X]) * t1 ^ 4 * w2) *
      h ^ 4 +
    (-(20971520 : F[X]) * a1) * h ^ 5 +
    (-(1698543 : F[X]) * Polynomial.C lambda * t1 ^ 6 +
        (1617660 : F[X]) * t1 ^ 7) *
      h ^ 6

set_option maxHeartbeats 16000000 in
theorem twelfthFace_seventh_zeroU1_mul_h
    (h t1 v1 s1 w2 u2 a4 a3 a2 a1 b62 b51 b4 b3 : F[X])
    (lambda : F) :
    seventhJetParen810 h (h * t1) (h * v1) (h * s1) (h ^ 2 * w2)
        (h ^ 2 * u2) a4 a3 a2 a1 (h ^ 2 * b62) (h * b51) b4 b3
        lambda =
      h ^ 4 *
        twelfthFace_zeroU1_Xcof810 h t1 v1 s1 w2 u2 a4 a3 a2 a1 b62
          b51 b4 b3 lambda := by
  simp only [seventhJetParen810, twelfthFace_zeroU1_Xcof810]
  ring

theorem eval_twelfthFace_zeroU1_Xcof810
    (h t1 v1 s1 w2 u2 a4 a3 a2 a1 b62 b51 b4 b3 : F[X])
    (lambda : F) (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (twelfthFace_zeroU1_Xcof810 h t1 v1 s1 w2 u2 a4 a3 a2 a1 b62
          b51 b4 b3 lambda) =
      -(6488064 : F) * Polynomial.eval root a4 * lambda *
          Polynomial.eval root v1 +
        (23068672 : F) * Polynomial.eval root a4 *
          Polynomial.eval root s1 * Polynomial.eval root t1 -
        (36044800 : F) * Polynomial.eval root a4 *
          Polynomial.eval root t1 * Polynomial.eval root v1 +
        (28835840 : F) * Polynomial.eval root a4 *
          Polynomial.eval root u2 -
        (14680064 : F) * Polynomial.eval root a4 *
          Polynomial.eval root w2 -
        (10485760 : F) * Polynomial.eval root b51 *
          Polynomial.eval root v1 +
        (17301504 : F) * Polynomial.eval root b62 *
          Polynomial.eval root t1 * Polynomial.eval root v1 -
        (12582912 : F) * Polynomial.eval root b62 *
          Polynomial.eval root u2 +
        (2568192 : F) * lambda * (Polynomial.eval root v1) ^ 3 -
        (27394048 : F) * Polynomial.eval root s1 *
          Polynomial.eval root t1 * (Polynomial.eval root v1) ^ 2 +
        (23068672 : F) * Polynomial.eval root s1 *
          Polynomial.eval root u2 * Polynomial.eval root v1 +
        (25681920 : F) * Polynomial.eval root t1 *
          (Polynomial.eval root v1) ^ 3 -
        (34242560 : F) * Polynomial.eval root u2 *
          (Polynomial.eval root v1) ^ 2 +
        (10092544 : F) * (Polynomial.eval root v1) ^ 2 *
          Polynomial.eval root w2 := by
  simp [twelfthFace_zeroU1_Xcof810, hroot]

end TwelfthFaceScalars810

/-! ## Source-facing twelfth-face packet -/

section NonzeroTwelfthFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local twelfth-face packet: the eleventh-face split together
with the refinement of the left component and both right-alternative
siblings. -/
theorem nonzeroFace810_linearRoot_twelfthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X],
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                  (u1.eval a) →
              (128 : k) * w1.eval a -
                  (5 : k) * t0.eval a *
                    ((24 : k) * v1.eval a -
                      (5 : k) * (t0.eval a) ^ 2) =
                0)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            (16 : k) * b62.eval a * v1.eval a +
                (10 : k) * (u1.eval a) ^ 2 -
              (5 : k) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 sigma : k[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    (32 : k) * w2.eval a - (40 : k) * u2.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (2560 : k) * b51.eval a +
                        (576 : k) * lambda * b62.eval a -
                        (640 : k) * t1.eval a * b62.eval a -
                        (45 : k) * lambda * (v1.eval a) ^ 2 +
                        (400 : k) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : k) * u2.eval a * v1.eval a = 0 ∧
                    (v1.eval a) ^ 3 *
                        ((3 : k) * lambda * v1.eval a +
                          (160 : k) * t1.eval a * v1.eval a -
                          (320 : k) * u2.eval a) =
                      0) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a = 0 ∧
                (8 : k) * (p.coeff 4).eval a -
                    (3 : k) * (v1.eval a) ^ 2 = 0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 = 0 ∧
                ∃ (t1 omega sigma : k[X]),
                  t0 = h0 * t1 ∧
                    (4 : k[X]) * w1 - (5 : k[X]) * u1 =
                      h0 * omega ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    h0 ^ 2 ∣ ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    (8 : k) * omega.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0)))) := by
  obtain ⟨alpha, hMrel⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨gamma, hTrel⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨etaX, hXrel⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_eleventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred, hWred,
      hXred, hp6_4, hq8_6, hp5_2, hq7_4⟩ := hleft
    have halt :=
      twelfthFace_left_alternative810 (t0.eval a) (v1.eval a)
        (u1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hGred hVred hWred hXred
    have hMeval :
        ((32 : k[X]) * s1 - (40 : k[X]) * v1 -
            (5 : k[X]) * t0 ^ 2).eval a = 0 := by
      have : (32 : k) * s1.eval a - (40 : k) * v1.eval a -
          (5 : k) * (t0.eval a) ^ 2 = 0 := by
        linear_combination hM
      simpa using this
    have hTeval :
        ((128 : k[X]) * w1 - (160 : k[X]) * u1 -
            (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3).eval a =
          0 := by
      simpa using hTred
    obtain ⟨m1, hm1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        ((32 : k[X]) * s1 - (40 : k[X]) * v1 - (5 : k[X]) * t0 ^ 2) a
        hh0degree hroot hMeval
    obtain ⟨tau1, htau1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        ((128 : k[X]) * w1 - (160 : k[X]) * u1 -
          (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3) a
        hh0degree hroot hTeval
    have hMsubst :
        localClearedSecondDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
            (h0 ^ 5 * s0) lambda =
          localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda := by
      simp only [ht0, hv0, hs0]
    have hTsubst :
        localClearedThirdDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
            (h0 * u0) (h0 ^ 5 * s0) (h0 ^ 3 * w0) lambda =
          localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
      simp only [ht0, hv0, hu0, hs0, hw0]
    have hMparen :
        secondJetParen810 h0 t0 v0 s0 lambda =
          Polynomial.C alpha * h0 ^ 3 :=
      secondJetParen810_eq_of_power h0 t0 v0 s0 lambda alpha hh0
        (hMsubst.trans hMrel)
    have hTparen :
        thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
          Polynomial.C gamma * h0 ^ 4 :=
      thirdJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 lambda
        gamma hh0 (hTsubst.trans hTrel)
    have hMleft :
        secondJetParen810 h0 t0 v0 s0 lambda =
          h0 * secondJetParen810_leftCofactor h0 t0 v1 s1 lambda := by
      simpa [hv1, hs1] using
        secondJetParen810_left_mul_h h0 t0 v1 s1 lambda
    have hTleft :
        thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
          h0 * thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
            lambda := by
      simpa [hv1, hs1, hw1, hu1] using
        thirdJetParen810_left_mul_h h0 t0 v1 s1 w1 u1 lambda
    have hMcof :
        secondJetParen810_leftCofactor h0 t0 v1 s1 lambda =
          Polynomial.C alpha * h0 ^ 2 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C alpha * h0 ^ 3 =
          h0 * (Polynomial.C alpha * h0 ^ 2) := by ring
      rw [← hMleft, hMparen, hscale]
    have hTcof :
        thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda =
          Polynomial.C gamma * h0 ^ 3 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C gamma * h0 ^ 4 =
          h0 * (Polynomial.C gamma * h0 ^ 3) := by ring
      rw [← hTleft, hTparen, hscale]
    have hMexp :
        secondJetParen810_leftCofactor h0 t0 v1 s1 lambda =
          h0 * m1 + (9 : k[X]) * Polynomial.C lambda * t0 * h0 := by
      simp only [secondJetParen810_leftCofactor]
      have : (32 : k[X]) * s1 - (40 : k[X]) * v1 -
          (5 : k[X]) * t0 ^ 2 = h0 * m1 := hm1
      linear_combination this
    have hTunred :
        -(512 : k[X]) * s1 * t0 + (480 : k[X]) * t0 * v1 -
            (640 : k[X]) * u1 + (512 : k[X]) * w1 +
          (100 : k[X]) * t0 ^ 3 =
          (4 : k[X]) *
              ((128 : k[X]) * w1 - (160 : k[X]) * u1 -
                (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3) -
            (16 : k[X]) * t0 *
              ((32 : k[X]) * s1 - (40 : k[X]) * v1 -
                (5 : k[X]) * t0 ^ 2) := by
      ring
    have hTexp :
        thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda =
          h0 *
            ((4 : k[X]) * tau1 - (16 : k[X]) * t0 * m1 +
              (144 : k[X]) * Polynomial.C lambda * v1 -
              (135 : k[X]) * Polynomial.C lambda * t0 ^ 2) := by
      simp only [thirdJetParen810_leftCofactor]
      rw [hTunred, hm1, htau1]
      ring
    have hM1 :
        m1.eval a + (9 : k) * lambda * t0.eval a = 0 := by
      have hpoly :
          h0 * (m1 + (9 : k[X]) * Polynomial.C lambda * t0) =
            Polynomial.C alpha * h0 ^ 2 := by
        calc
          h0 * (m1 + (9 : k[X]) * Polynomial.C lambda * t0) =
              h0 * m1 +
                (9 : k[X]) * Polynomial.C lambda * t0 * h0 := by
            ring
          _ = secondJetParen810_leftCofactor h0 t0 v1 s1 lambda :=
            hMexp.symm
          _ = Polynomial.C alpha * h0 ^ 2 := hMcof
      have hred :
          m1 + (9 : k[X]) * Polynomial.C lambda * t0 =
            Polynomial.C alpha * h0 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C alpha * h0 ^ 2 =
            h0 * (Polynomial.C alpha * h0) := by ring
        rw [hpoly, hscale]
      have := congrArg (fun r : k[X] => Polynomial.eval a r) hred
      simpa [hroot] using this
    have hT1raw :
        (4 : k) * tau1.eval a - (16 : k) * t0.eval a * m1.eval a +
            (144 : k) * lambda * v1.eval a -
          (135 : k) * lambda * (t0.eval a) ^ 2 = 0 := by
      have hpoly :
          h0 *
              ((4 : k[X]) * tau1 - (16 : k[X]) * t0 * m1 +
                (144 : k[X]) * Polynomial.C lambda * v1 -
                (135 : k[X]) * Polynomial.C lambda * t0 ^ 2) =
            Polynomial.C gamma * h0 ^ 3 := by
        rw [← hTexp, hTcof]
      have hred :
          (4 : k[X]) * tau1 - (16 : k[X]) * t0 * m1 +
              (144 : k[X]) * Polynomial.C lambda * v1 -
              (135 : k[X]) * Polynomial.C lambda * t0 ^ 2 =
            Polynomial.C gamma * h0 ^ 2 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C gamma * h0 ^ 3 =
            h0 * (Polynomial.C gamma * h0 ^ 2) := by ring
        rw [hpoly, hscale]
      have := congrArg (fun r : k[X] => Polynomial.eval a r) hred
      simpa [hroot] using this
    have hT1 :=
      twelfthFace_left_T_nextOrder810 (t0.eval a) (v1.eval a)
        (m1.eval a) (tau1.eval a) lambda hM1 hT1raw
    have hF1w :
        twelfthFace_leftF1_810 (t0.eval a) (v1.eval a) (u1.eval a) →
          (128 : k) * w1.eval a -
              (5 : k) * t0.eval a *
                ((24 : k) * v1.eval a -
                  (5 : k) * (t0.eval a) ^ 2) =
            0 := fun hF1 =>
      twelfthFace_leftF1_w1_810 (t0.eval a) (v1.eval a) (u1.eval a)
        (w1.eval a) hF1 hTred
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred,
        hWred, hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt,
        ⟨m1, tau1, hm1, htau1, hM1, hT1⟩, hF1w⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
      hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, hright'⟩ :=
      hright
    refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
        hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, ?_⟩⟩
    rcases hright' with hu1z | hcomp
    · obtain ⟨hu1z, t1, u2, w2, b51, ht1, hu2, hw2, hb51, hp5_3, hq7_5,
        hq5d, hTform, hVform⟩ := hu1z
      have hMsubst :
          localClearedSecondDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 ^ 5 * s0) lambda =
            localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
              (q.coeff 8) lambda := by
        simp only [ht0, hv0, hs0]
      have hXsubst :
          localClearedSeventhDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (p.coeff 4) (p.coeff 3) (p.coeff 2)
              (p.coeff 1) (h0 ^ 5 * s0) (h0 ^ 3 * w0)
              (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
              lambda =
            localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
              (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0, hb62]
      have hMparen :
          secondJetParen810 h0 t0 v0 s0 lambda =
            Polynomial.C alpha * h0 ^ 3 :=
        secondJetParen810_eq_of_power h0 t0 v0 s0 lambda alpha hh0
          (hMsubst.trans hMrel)
      have hXparen :
          seventhJetParen810 h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (h0 ^ 2 * b62) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) lambda =
            Polynomial.C etaX * h0 ^ 10 :=
        seventhJetParen810_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (h0 ^ 2 * b62)
          (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda etaX hh0
          (hXsubst.trans hXrel)
      have hu0' : u0 = h0 ^ 2 * u2 := by
        rw [hu1, hu2]
        ring
      have hw0' : w0 = h0 ^ 2 * w2 := by
        rw [hw1, hw2]
        ring
      have hMleft :
          secondJetParen810 h0 t0 v0 s0 lambda =
            h0 * secondJetParen810_leftCofactor h0 t0 v1 s1
              lambda := by
        simpa [hv1, hs1] using
          secondJetParen810_left_mul_h h0 t0 v1 s1 lambda
      have hMcof :
          secondJetParen810_leftCofactor h0 t0 v1 s1 lambda =
            Polynomial.C alpha * h0 ^ 2 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C alpha * h0 ^ 3 =
            h0 * (Polynomial.C alpha * h0 ^ 2) := by ring
        rw [← hMleft, hMparen, hscale]
      have hM1poly :
          (32 : k[X]) * s1 - (40 : k[X]) * v1 =
            (32 : k[X]) * s1 - (40 : k[X]) * v1 -
              (5 : k[X]) * t0 ^ 2 + (5 : k[X]) * t0 ^ 2 := by
        ring
      have hMeval0 :
          ((32 : k[X]) * s1 - (40 : k[X]) * v1).eval a = 0 := by
        have : (32 : k) * s1.eval a - (40 : k) * v1.eval a = 0 := by
          linear_combination (8 : k) * hs1rel
        simpa using this
      obtain ⟨sigma0, hsigma0⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((32 : k[X]) * s1 - (40 : k[X]) * v1) a hh0degree hroot
          hMeval0
      have hMcof' :
          (32 : k[X]) * s1 - (40 : k[X]) * v1 -
              (5 : k[X]) * t0 ^ 2 +
            (9 : k[X]) * Polynomial.C lambda * t0 * h0 =
            Polynomial.C alpha * h0 ^ 2 := by
        simpa [secondJetParen810_leftCofactor] using hMcof
      have hsigma_eval :
          sigma0.eval a = 0 := by
        have hrew :
            (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                (5 : k[X]) * t0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t0 * h0 =
              h0 *
                (sigma0 +
                  h0 *
                    (-(5 : k[X]) * t1 ^ 2 +
                      (9 : k[X]) * Polynomial.C lambda * t1)) := by
          rw [hsigma0, ht1]
          ring
        have hpoly :
            h0 *
                (sigma0 +
                  h0 *
                    (-(5 : k[X]) * t1 ^ 2 +
                      (9 : k[X]) * Polynomial.C lambda * t1)) =
              Polynomial.C alpha * h0 ^ 2 := by
          rw [← hrew, hMcof']
        have hred :
            sigma0 +
                h0 *
                  (-(5 : k[X]) * t1 ^ 2 +
                    (9 : k[X]) * Polynomial.C lambda * t1) =
              Polynomial.C alpha * h0 := by
          apply mul_left_cancel₀ hh0
          have hscale : Polynomial.C alpha * h0 ^ 2 =
              h0 * (Polynomial.C alpha * h0) := by ring
          rw [hpoly, hscale]
        have := congrArg (fun r : k[X] => Polynomial.eval a r) hred
        simpa [hroot] using this
      obtain ⟨sigma, hsigma⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 sigma0 a hh0degree
          hroot hsigma_eval
      have hsigmapoly :
          (32 : k[X]) * s1 - (40 : k[X]) * v1 = h0 ^ 2 * sigma := by
        rw [hsigma0, hsigma]
        ring
      have hsigmadvd :
          h0 ^ 2 ∣ ((32 : k[X]) * s1 - (40 : k[X]) * v1) :=
        ⟨sigma, by rw [hsigmapoly]⟩
      have hXleft :
          seventhJetParen810 h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (h0 ^ 2 * b62)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda =
            h0 ^ 4 *
              twelfthFace_zeroU1_Xcof810 h0 t1 v1 s1 w2 u2
                (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) b62
                b51 (q.coeff 4) (q.coeff 3) lambda := by
        simpa [ht1, hv1, hs1, hw0', hu0', hb51] using
          twelfthFace_seventh_zeroU1_mul_h h0 t1 v1 s1 w2 u2
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) b62 b51
            (q.coeff 4) (q.coeff 3) lambda
      have hXcof :
          twelfthFace_zeroU1_Xcof810 h0 t1 v1 s1 w2 u2 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) b62 b51
              (q.coeff 4) (q.coeff 3) lambda =
            Polynomial.C etaX * h0 ^ 6 := by
        apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
        have hscale : Polynomial.C etaX * h0 ^ 10 =
            h0 ^ 4 * (Polynomial.C etaX * h0 ^ 6) := by ring
        rw [← hXleft, hXparen, hscale]
      have hXeval :
          -(6488064 : k) * (p.coeff 4).eval a * lambda *
                v1.eval a +
              (23068672 : k) * (p.coeff 4).eval a * s1.eval a *
                t1.eval a -
              (36044800 : k) * (p.coeff 4).eval a * t1.eval a *
                v1.eval a +
              (28835840 : k) * (p.coeff 4).eval a * u2.eval a -
              (14680064 : k) * (p.coeff 4).eval a * w2.eval a -
              (10485760 : k) * b51.eval a * v1.eval a +
              (17301504 : k) * b62.eval a * t1.eval a *
                v1.eval a -
              (12582912 : k) * b62.eval a * u2.eval a +
              (2568192 : k) * lambda * (v1.eval a) ^ 3 -
              (27394048 : k) * s1.eval a * t1.eval a *
                (v1.eval a) ^ 2 +
              (23068672 : k) * s1.eval a * u2.eval a *
                v1.eval a +
              (25681920 : k) * t1.eval a * (v1.eval a) ^ 3 -
              (34242560 : k) * u2.eval a * (v1.eval a) ^ 2 +
              (10092544 : k) * (v1.eval a) ^ 2 * w2.eval a =
            0 := by
        have hleft :=
          eval_twelfthFace_zeroU1_Xcof810 h0 t1 v1 s1 w2 u2
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) b62 b51
            (q.coeff 4) (q.coeff 3) lambda a hroot
        have hzero :
            Polynomial.eval a
                (twelfthFace_zeroU1_Xcof810 h0 t1 v1 s1 w2 u2
                  (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
                  b62 b51 (q.coeff 4) (q.coeff 3) lambda) =
              0 := by
          rw [hXcof]
          simp [hroot]
        rw [← hleft]
        exact hzero
      have hM1 :
          (32 : k) * s1.eval a - (40 : k) * v1.eval a = 0 := by
        linear_combination (8 : k) * hs1rel
      have hW0 :
          (16 : k) * b62.eval a * v1.eval a -
            (5 : k) * (v1.eval a) ^ 3 = 0 := by
        simpa [hu1z] using hWspec
      have hXred :=
        twelfthFace_zeroU1_X_nextOrder810 (v1.eval a) (s1.eval a)
          (t1.eval a) (u2.eval a) (w2.eval a) ((p.coeff 4).eval a)
          (b62.eval a) (b51.eval a) lambda hM1 ha4 hTform hVform
          hXeval
      have hprod :=
        twelfthFace_zeroU1_seventh_product810 (v1.eval a) (t1.eval a)
          (u2.eval a) (b62.eval a) lambda hW0 hXred
      refine Or.inl ⟨hu1z, t1, u2, w2, b51, sigma, ht1, hu2, hw2, hb51,
        hsigmapoly, hp5_3, hq7_5, hq5d, hsigmadvd, hTform, hVform,
        hprod⟩
    · obtain ⟨hB, ha4c, hu1c⟩ := hcomp
      obtain ⟨t1, ht1⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 t0 a hh0degree
          hroot ht0z
      have hweval :
          ((4 : k[X]) * w1 - (5 : k[X]) * u1).eval a = 0 := by
        have : (4 : k) * w1.eval a - (5 : k) * u1.eval a = 0 := by
          linear_combination hw1rel
        simpa using this
      obtain ⟨omega, homega⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((4 : k[X]) * w1 - (5 : k[X]) * u1) a hh0degree hroot
          hweval
      have hMeval0 :
          ((32 : k[X]) * s1 - (40 : k[X]) * v1).eval a = 0 := by
        have : (32 : k) * s1.eval a - (40 : k) * v1.eval a = 0 := by
          linear_combination (8 : k) * hs1rel
        simpa using this
      obtain ⟨sigma0, hsigma0⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((32 : k[X]) * s1 - (40 : k[X]) * v1) a hh0degree hroot
          hMeval0
      have hMsubst :
          localClearedSecondDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 ^ 5 * s0) lambda =
            localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
              (q.coeff 8) lambda := by
        simp only [ht0, hv0, hs0]
      have hTsubst :
          localClearedThirdDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (h0 ^ 5 * s0) (h0 ^ 3 * w0) lambda =
            localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0]
      have hMparen :
          secondJetParen810 h0 t0 v0 s0 lambda =
            Polynomial.C alpha * h0 ^ 3 :=
        secondJetParen810_eq_of_power h0 t0 v0 s0 lambda alpha hh0
          (hMsubst.trans hMrel)
      have hTparen :
          thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
            Polynomial.C gamma * h0 ^ 4 :=
        thirdJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 lambda
          gamma hh0 (hTsubst.trans hTrel)
      have hMleft :
          secondJetParen810 h0 t0 v0 s0 lambda =
            h0 * secondJetParen810_leftCofactor h0 t0 v1 s1
              lambda := by
        simpa [hv1, hs1] using
          secondJetParen810_left_mul_h h0 t0 v1 s1 lambda
      have hTleft :
          thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
            h0 * thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
              lambda := by
        simpa [hv1, hs1, hw1, hu1] using
          thirdJetParen810_left_mul_h h0 t0 v1 s1 w1 u1 lambda
      have hMcof :
          secondJetParen810_leftCofactor h0 t0 v1 s1 lambda =
            Polynomial.C alpha * h0 ^ 2 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C alpha * h0 ^ 3 =
            h0 * (Polynomial.C alpha * h0 ^ 2) := by ring
        rw [← hMleft, hMparen, hscale]
      have hTcof0 :
          thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda =
            Polynomial.C gamma * h0 ^ 3 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C gamma * h0 ^ 4 =
            h0 * (Polynomial.C gamma * h0 ^ 3) := by ring
        rw [← hTleft, hTparen, hscale]
      have hsigma_eval :
          sigma0.eval a = 0 := by
        have hMcof' :
            (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                (5 : k[X]) * t0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t0 * h0 =
              Polynomial.C alpha * h0 ^ 2 := by
          simpa [secondJetParen810_leftCofactor] using hMcof
        have hrew :
            (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                (5 : k[X]) * t0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t0 * h0 =
              h0 *
                (sigma0 +
                  h0 *
                    (-(5 : k[X]) * t1 ^ 2 +
                      (9 : k[X]) * Polynomial.C lambda * t1)) := by
          rw [hsigma0, ht1]
          ring
        have hpoly :
            h0 *
                (sigma0 +
                  h0 *
                    (-(5 : k[X]) * t1 ^ 2 +
                      (9 : k[X]) * Polynomial.C lambda * t1)) =
              Polynomial.C alpha * h0 ^ 2 := by
          rw [← hrew, hMcof']
        have hred :
            sigma0 +
                h0 *
                  (-(5 : k[X]) * t1 ^ 2 +
                    (9 : k[X]) * Polynomial.C lambda * t1) =
              Polynomial.C alpha * h0 := by
          apply mul_left_cancel₀ hh0
          have hscale : Polynomial.C alpha * h0 ^ 2 =
              h0 * (Polynomial.C alpha * h0) := by ring
          rw [hpoly, hscale]
        have := congrArg (fun r : k[X] => Polynomial.eval a r) hred
        simpa [hroot] using this
      obtain ⟨sigma, hsigma⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 sigma0 a
          hh0degree hroot hsigma_eval
      have hsigmapoly :
          (32 : k[X]) * s1 - (40 : k[X]) * v1 = h0 ^ 2 * sigma := by
        rw [hsigma0, hsigma]
        ring
      have hsigmadvd :
          h0 ^ 2 ∣ ((32 : k[X]) * s1 - (40 : k[X]) * v1) :=
        ⟨sigma, by rw [hsigmapoly]⟩
      have hTthird :
          thirdJetParen810_leftCofactor h0 (h0 * t1) v1 s1 w1 u1
              lambda =
            twelfthFace_comp_thirdCof810 h0 t1 v1 s1 w1 u1
              lambda :=
        twelfthFace_comp_third_mul_h h0 t1 v1 s1 w1 u1 lambda
      have homegaX :
          (4 : k[X]) * w1 - (5 : k[X]) * u1 = h0 * omega := homega
      have hTfact :=
        twelfthFace_comp_thirdCof_omega h0 t1 v1 s1 w1 u1 omega
          lambda homegaX
      have hTcof :
          (128 : k[X]) * omega - (512 : k[X]) * s1 * t1 +
              (480 : k[X]) * t1 * v1 +
            (144 : k[X]) * Polynomial.C lambda * v1 +
            ((100 : k[X]) * t1 ^ 3 -
                (135 : k[X]) * Polynomial.C lambda * t1 ^ 2) *
              h0 ^ 2 =
            Polynomial.C gamma * h0 ^ 2 := by
        have hleft :
            twelfthFace_comp_thirdCof810 h0 t1 v1 s1 w1 u1 lambda =
              Polynomial.C gamma * h0 ^ 3 := by
          rw [← hTthird, ← ht1]
          exact hTcof0
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C gamma * h0 ^ 3 =
            h0 * (Polynomial.C gamma * h0 ^ 2) := by ring
        rw [← hTfact, hleft, hscale]
      have hTeval :
          (128 : k) * omega.eval a - (512 : k) * s1.eval a *
                t1.eval a +
              (480 : k) * t1.eval a * v1.eval a +
            (144 : k) * lambda * v1.eval a = 0 := by
        have hleft :=
          eval_twelfthFace_comp_Tcof810 h0 t1 v1 s1 omega lambda a
            hroot
        have hzero :
            Polynomial.eval a
                ((128 : k[X]) * omega - (512 : k[X]) * s1 * t1 +
                  (480 : k[X]) * t1 * v1 +
                  (144 : k[X]) * Polynomial.C lambda * v1 +
                  ((100 : k[X]) * t1 ^ 3 -
                      (135 : k[X]) * Polynomial.C lambda *
                        t1 ^ 2) *
                    h0 ^ 2) =
              0 := by
          rw [hTcof]
          simp [hroot]
        rw [← hleft]
        exact hzero
      have hM4 :
          (4 : k) * s1.eval a - (5 : k) * v1.eval a = 0 := by
        linear_combination hs1rel
      have hTform :=
        twelfthFace_comp_T_nextOrder810 (v1.eval a) (s1.eval a)
          (t1.eval a) (omega.eval a) lambda hM4 hTeval
      exact Or.inr ⟨hB, ha4c, hu1c, t1, omega, sigma, ht1, homega,
        hsigmapoly, hsigmadvd, hTform⟩

/-- Source-facing twelfth-face packet of a normalized scale-two `(8,10)`
nonzero face: the eleventh-face split together with the refinement of
the left component and both right-alternative siblings. -/
theorem normalized810ScaleTwo_nonzeroFace_twelfthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K)
      (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : K) * s1.eval a - (40 : K) * v1.eval a =
              (5 : K) * (t0.eval a) ^ 2 ∧
            (128 : K) * w1.eval a - (160 : K) * u1.eval a -
                (40 : K) * t0.eval a * v1.eval a +
              (5 : K) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : K[X]),
              (32 : K[X]) * s1 - (40 : K[X]) * v1 -
                    (5 : K[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : K[X]) * w1 - (160 : K[X]) * u1 -
                    (40 : K[X]) * t0 * v1 + (5 : K[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : K) * lambda * t0.eval a = 0 ∧
                (4 : K) * tau1.eval a +
                    (9 : K) * lambda * (t0.eval a) ^ 2 +
                  (144 : K) * lambda * v1.eval a = 0) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                  (u1.eval a) →
              (128 : K) * w1.eval a -
                  (5 : K) * t0.eval a *
                    ((24 : K) * v1.eval a -
                      (5 : K) * (t0.eval a) ^ 2) =
                0)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : K) * s1.eval a = (5 : K) * v1.eval a ∧
            (4 : K) * w1.eval a = (5 : K) * u1.eval a ∧
            (40 : K) * (p.coeff 4).eval a - (32 : K) * b62.eval a +
              (5 : K) * (v1.eval a) ^ 2 = 0 ∧
            (16 : K) * (q.coeff 5).eval a =
              (5 : K) * u1.eval a * v1.eval a ∧
            (16 : K) * b62.eval a * v1.eval a +
                (10 : K) * (u1.eval a) ^ 2 -
              (5 : K) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 sigma : K[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    (32 : K) * w2.eval a - (40 : K) * u2.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (2560 : K) * b51.eval a +
                        (576 : K) * lambda * b62.eval a -
                        (640 : K) * t1.eval a * b62.eval a -
                        (45 : K) * lambda * (v1.eval a) ^ 2 +
                        (400 : K) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : K) * u2.eval a * v1.eval a = 0 ∧
                    (v1.eval a) ^ 3 *
                        ((3 : K) * lambda * v1.eval a +
                          (160 : K) * t1.eval a * v1.eval a -
                          (320 : K) * u2.eval a) =
                      0) ∨
              ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a = 0 ∧
                (8 : K) * (p.coeff 4).eval a -
                    (3 : K) * (v1.eval a) ^ 2 = 0 ∧
                (2 : K) * (u1.eval a) ^ 2 +
                  (v1.eval a) ^ 3 = 0 ∧
                ∃ (t1 omega sigma : K[X]),
                  t0 = h0 * t1 ∧
                    (4 : K[X]) * w1 - (5 : K[X]) * u1 =
                      h0 * omega ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    h0 ^ 2 ∣ ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    (8 : K) * omega.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0)))) := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨t0', v0', u0', s0', w0', v1', s1', u1', w1', b62', ht0', hv0',
    hu0', hs0', hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6',
    hsplit'⟩ :=
    nonzeroFace810_linearRoot_twelfthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroTwelfthFace810

#print axioms twelfthCoefficientJacobianRow_810
#print axioms twelfthFace_left_alternative810
#print axioms twelfthFace_leftF1_w1_810
#print axioms twelfthFace_leftF1_G_810
#print axioms twelfthFace_left_T_nextOrder810
#print axioms twelfthFace_zeroU1_X_nextOrder810
#print axioms twelfthFace_zeroU1_seventh_product810
#print axioms twelfthFace_comp_T_nextOrder810
#print axioms twelfthFace_comp_third_mul_h
#print axioms twelfthFace_seventh_zeroU1_mul_h
#print axioms nonzeroFace810_linearRoot_twelfthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_twelfthInitialPacket

end Max11DegreeRoutes
