import Grok810ScaleTwoTwelfthFaceScratch

/-! # Scale-two thirteenth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the twelfth-face packet supplies the degree-`5`
Jacobian row (without clearing the corresponding first integral) and
the live split of the eleventh-face jet.  On the left the seventh-load
alternative `F₁ ∨ F₂` survives, together with the next-order second
and third defects `m₁(a) + 9 λ t₀(a) = 0` and
`4 τ₁(a) + 9 λ t₀(a)² + 144 λ v₁(a) = 0`.  On the right, the `u₁ = 0`
sibling carries `h² ∣ (4 s₁ - 5 v₁)` and
`v₁³ (3 λ v₁ + 160 t₁ v₁ - 320 u₂) = 0`, while the complementary
factor carries `8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`, `2 u₁² + v₁³ = 0`,
and `8 ω(a) = v₁(a) (10 t₁(a) - 9 λ)`.

The next unused Keller coefficient is the degree-`4` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`5 S G' + 4 T F' + 3 U E' + 2 V D' + W C'
- D S' - 2 C T' - 3 B U' - 4 A V' - 5 G W' = 0`.
The degree-`5` first integral remains uncleared: clearing it against
the remaining decic coordinate produces a defect larger than the
remaining exact jet.  This file isolates the degree-`4` Jacobian
identity and the strongest exact source-facing refinement of every
live twelfth-face branch.

Both left factors survive.  On `F₁` the fifth and sixth loads
specialise to `1024 b₅ - 256 b₆₂ t₀ - 11 t₀⁵ + 40 t₀³ v₁ = 0` and
`(3 t₀² - 8 v₁) (1024 b₆₂ + 25 t₀⁴ - 320 v₁²) = 0`.  The next-order
fourth and fifth left combinations
`7 t₀³ - 48 t₀ v₁ - 384 u₁` and
`16384 b₆₂ + 175 t₀⁴ - 1120 t₀² v₁ - 17920 t₀ u₁ - 1280 v₁²`
are recorded as scalar identities.  On the `u₁ = 0` sibling the
fourth load upgrades to `h² ∣ (40 a₄ - 32 b₆₂ + 5 v₁²)`.  On the
complementary factor the fifth load upgrades to
`h ∣ (16 b₅ - 5 u₁ v₁)`.  No individual vanishing of
`v₁, a₄, t₀, t₁, p₃, q₄` is claimed, and the aligned face `N = 0`
remains open.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The thirteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the twelfth face
start at degree `4`. -/
theorem thirteenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Scalar algebra of the twelfth-face branches -/

section ThirteenthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Next-order fourth-load combination on the left ninth-face jet. -/
def thirteenthFace_leftGnext810 (t0 v1 u1 : F) : F :=
  (7 : F) * t0 ^ 3 - (48 : F) * t0 * v1 - (384 : F) * u1

/-- Next-order fifth-load combination on the left ninth-face jet. -/
def thirteenthFace_leftVnext810 (t0 v1 u1 b62 : F) : F :=
  (16384 : F) * b62 + (175 : F) * t0 ^ 4 - (1120 : F) * t0 ^ 2 * v1 -
    (17920 : F) * t0 * u1 - (1280 : F) * v1 ^ 2

/-- On the first left factor, the fifth-defect reduction solves `b₅`. -/
theorem thirteenthFace_leftF1_b5_810 (t0 v1 u1 a4 b62 b5 : F)
    (hF1 : twelfthFace_leftF1_810 t0 v1 u1)
    (hG : tenthFace_Gred810 t0 v1 u1 a4 b62)
    (hV : tenthFace_Vred810 t0 v1 u1 a4 b62 b5) :
    (1024 : F) * b5 - (256 : F) * b62 * t0 - (11 : F) * t0 ^ 5 +
        (40 : F) * t0 ^ 3 * v1 =
      0 := by
  unfold twelfthFace_leftF1_810 tenthFace_Gred810 tenthFace_Vred810 at *
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hid :
      (128 : F) *
          ((1024 : F) * b5 - (256 : F) * b62 * t0 -
            (11 : F) * t0 ^ 5 + (40 : F) * t0 ^ 3 * v1) =
        (81920 : F) * a4 * t0 + (131072 : F) * b5 -
            (98304 : F) * b62 * t0 + (2912 : F) * t0 ^ 5 -
            (20480 : F) * t0 ^ 3 * v1 + (46080 : F) * t0 ^ 2 * u1 +
            (30720 : F) * t0 * v1 ^ 2 - (40960 : F) * u1 * v1 -
          (32 : F) * t0 *
            ((2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
              (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
              (320 : F) * v1 ^ 2) -
          ((3200 : F) * t0 ^ 2 - (5120 : F) * v1) *
            (t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) := by
    ring
  have hcomb :
      (128 : F) *
          ((1024 : F) * b5 - (256 : F) * b62 * t0 -
            (11 : F) * t0 ^ 5 + (40 : F) * t0 ^ 3 * v1) =
        0 := by
    rw [hid]
    linear_combination hV - (32 : F) * t0 * hG -
      ((3200 : F) * t0 ^ 2 - (5120 : F) * v1) * hF1
  exact (mul_eq_zero.mp hcomb).resolve_left h128

/-- On the first left factor, the sixth load forces the product
`(3 t₀² - 8 v₁) (1024 b₆₂ + 25 t₀⁴ - 320 v₁²) = 0`. -/
theorem thirteenthFace_leftF1_sixth_product810 (t0 v1 u1 a4 b62 b5 : F)
    (hF1 : twelfthFace_leftF1_810 t0 v1 u1)
    (hG : tenthFace_Gred810 t0 v1 u1 a4 b62)
    (hV : tenthFace_Vred810 t0 v1 u1 a4 b62 b5)
    (hW : tenthFace_Wred810 t0 v1 u1 a4 b62 b5) :
    ((3 : F) * t0 ^ 2 - (8 : F) * v1) *
        ((1024 : F) * b62 + (25 : F) * t0 ^ 4 -
          (320 : F) * v1 ^ 2) =
      0 := by
  unfold twelfthFace_leftF1_810 tenthFace_Gred810 tenthFace_Wred810 at *
  have hGspec := twelfthFace_leftF1_G_810 t0 v1 u1 a4 b62 hF1 hG
  have hB5 :=
    thirteenthFace_leftF1_b5_810 t0 v1 u1 a4 b62 b5 hF1 hG hV
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hid :
      (4 : F) *
          (((3 : F) * t0 ^ 2 - (8 : F) * v1) *
            ((1024 : F) * b62 + (25 : F) * t0 ^ 4 -
              (320 : F) * v1 ^ 2)) =
        -(51200 : F) * a4 * t0 ^ 2 + (81920 : F) * a4 * v1 -
            (81920 : F) * b5 * t0 + (73728 : F) * b62 * t0 ^ 2 -
            (98304 : F) * b62 * v1 - (2800 : F) * t0 ^ 6 +
            (22080 : F) * t0 ^ 4 * v1 - (41600 : F) * t0 ^ 3 * u1 -
            (46080 : F) * t0 ^ 2 * v1 ^ 2 +
            (87040 : F) * t0 * u1 * v1 - (20480 : F) * u1 ^ 2 +
            (20480 : F) * v1 ^ 3 +
          ((20 : F) * t0 ^ 2 - (32 : F) * v1) *
            ((2560 : F) * a4 - (2048 : F) * b62 - (45 : F) * t0 ^ 4 +
              (80 : F) * t0 ^ 2 * v1 + (320 : F) * v1 ^ 2) +
          (80 : F) * t0 *
            ((1024 : F) * b5 - (256 : F) * b62 * t0 -
              (11 : F) * t0 ^ 5 + (40 : F) * t0 ^ 3 * v1) +
          (80 : F) * (t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) *
            ((61 : F) * t0 ^ 3 - (120 : F) * t0 * v1 +
              (32 : F) * u1) := by
    ring
  have hcomb :
      (4 : F) *
          (((3 : F) * t0 ^ 2 - (8 : F) * v1) *
            ((1024 : F) * b62 + (25 : F) * t0 ^ 4 -
              (320 : F) * v1 ^ 2)) =
        0 := by
    rw [hid]
    linear_combination hW +
      ((20 : F) * t0 ^ 2 - (32 : F) * v1) * hGspec +
      (80 : F) * t0 * hB5 +
      (80 : F) * hF1 *
        ((61 : F) * t0 ^ 3 - (120 : F) * t0 * v1 + (32 : F) * u1)
  exact (mul_eq_zero.mp hcomb).resolve_left h4

/-- Combining the next-order second, third, and fourth defects on the
left. -/
theorem thirteenthFace_left_G_nextOrder810 (t0 v1 u1 m1 tau1 g1 : F)
    (lambda : F)
    (hM : m1 + (9 : F) * lambda * t0 = 0)
    (hT : (4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
      (144 : F) * lambda * v1 =
      0)
    (hG : (2 : F) * g1 -
          ((112 : F) * t0 ^ 2 - (128 : F) * v1) * m1 +
        (28 : F) * t0 * tau1 -
      ((924 : F) * lambda * t0 ^ 3 - (2016 : F) * lambda * t0 * v1 +
        (1152 : F) * lambda * u1) =
      0) :
    (2 : F) * g1 + (3 : F) * lambda *
        thirteenthFace_leftGnext810 t0 v1 u1 =
      0 := by
  unfold thirteenthFace_leftGnext810
  have hid :
      (2 : F) * g1 + (3 : F) * lambda *
            ((7 : F) * t0 ^ 3 - (48 : F) * t0 * v1 -
              (384 : F) * u1) =
        (2 : F) * g1 -
            ((112 : F) * t0 ^ 2 - (128 : F) * v1) * m1 +
          (28 : F) * t0 * tau1 -
          ((924 : F) * lambda * t0 ^ 3 -
            (2016 : F) * lambda * t0 * v1 +
            (1152 : F) * lambda * u1) +
        ((112 : F) * t0 ^ 2 - (128 : F) * v1) *
          (m1 + (9 : F) * lambda * t0) -
        (7 : F) * t0 *
          ((4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
            (144 : F) * lambda * v1) := by
    ring
  rw [hid]
  linear_combination hG +
    ((112 : F) * t0 ^ 2 - (128 : F) * v1) * hM - (7 : F) * t0 * hT

/-- The complementary fifth load at the next order of
`16 b₅ - 5 u₁ v₁ = β h` is `32 β + 63 λ v₁² = 0`. -/
theorem thirteenthFace_comp_V_nextOrder810 (v1 u1 a4 b62 b5 t1 omega
    beta : F) (lambda : F)
    (hA : (8 : F) * a4 - (3 : F) * v1 ^ 2 = 0)
    (hB : (5 : F) * v1 ^ 2 - (8 : F) * b62 = 0)
    (hT : (8 : F) * omega - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 =
      0)
    (hV : (32 : F) * beta + (144 : F) * a4 * lambda +
        (320 : F) * a4 * t1 - (384 : F) * b62 * t1 -
        (117 : F) * lambda * v1 ^ 2 - (112 : F) * omega * v1 +
      (260 : F) * t1 * v1 ^ 2 =
      0) :
    (32 : F) * beta + (63 : F) * lambda * v1 ^ 2 = 0 := by
  have hid :
      (32 : F) * beta + (63 : F) * lambda * v1 ^ 2 =
        (32 : F) * beta + (144 : F) * a4 * lambda +
            (320 : F) * a4 * t1 - (384 : F) * b62 * t1 -
            (117 : F) * lambda * v1 ^ 2 -
            (112 : F) * omega * v1 + (260 : F) * t1 * v1 ^ 2 -
          (18 : F) * lambda * ((8 : F) * a4 - (3 : F) * v1 ^ 2) -
          (40 : F) * t1 * ((8 : F) * a4 - (3 : F) * v1 ^ 2) -
          (48 : F) * t1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62) +
          (14 : F) * v1 *
            ((8 : F) * omega - (10 : F) * t1 * v1 +
              (9 : F) * lambda * v1) := by
    ring
  rw [hid]
  linear_combination hV - (18 : F) * lambda * hA -
    (40 : F) * t1 * hA - (48 : F) * t1 * hB + (14 : F) * v1 * hT

/-! ## Extra-`h` substitutions of the sixth-jet fourth and fifth
parentheticals -/

/-- Cofactor of `h²` in the sixth-jet fourth defect after the extra
`u₁ = 0` vanishing `t₀ = h t₁`, `u₁ = h u₂`, `w₁ = h w₂`. -/
def thirteenthFace_zeroU1_Gcof810 (h t1 v1 s1 w2 u2 a4 b62 : F[X])
    (lambda : F) : F[X] :=
  -(2560 : F[X]) * a4 + (2048 : F[X]) * b62 - (2048 : F[X]) * s1 * v1 +
    (2240 : F[X]) * v1 ^ 2 +
    (-(1008 : F[X]) * Polynomial.C lambda * t1 * v1 +
        (576 : F[X]) * Polynomial.C lambda * u2 +
      (1792 : F[X]) * s1 * t1 ^ 2 - (1120 : F[X]) * t1 ^ 2 * v1 +
        (1600 : F[X]) * t1 * u2 - (1792 : F[X]) * t1 * w2) *
      h ^ 2 +
    ((462 : F[X]) * Polynomial.C lambda * t1 ^ 3 -
        (385 : F[X]) * t1 ^ 4) *
      h ^ 4

set_option maxHeartbeats 8000000 in
theorem thirteenthFace_fourth_zeroU1_mul_h
    (h t1 v1 s1 w2 u2 a4 b62 : F[X]) (lambda : F) :
    fourthJetParen810_sixth h (h * t1) (h * v1) (h * s1) (h ^ 2 * w2)
        (h ^ 2 * u2) a4 (h ^ 2 * b62) lambda =
      h ^ 2 *
        thirteenthFace_zeroU1_Gcof810 h t1 v1 s1 w2 u2 a4 b62
          lambda := by
  simp only [fourthJetParen810_sixth, thirteenthFace_zeroU1_Gcof810]
  ring

theorem thirteenthFace_zeroU1_Gcof_sigma
    (h t1 v1 s1 w2 u2 a4 b62 sigma : F[X]) (lambda : F)
    (hsigma : (32 : F[X]) * s1 - (40 : F[X]) * v1 =
      h ^ 2 * sigma) :
    thirteenthFace_zeroU1_Gcof810 h t1 v1 s1 w2 u2 a4 b62 lambda =
      -(64 : F[X]) *
          ((40 : F[X]) * a4 - (32 : F[X]) * b62 +
            (5 : F[X]) * v1 ^ 2) +
        h ^ 2 *
          (-(64 : F[X]) * sigma * v1 -
            (1008 : F[X]) * Polynomial.C lambda * t1 * v1 +
            (576 : F[X]) * Polynomial.C lambda * u2 +
            (1792 : F[X]) * s1 * t1 ^ 2 -
            (1120 : F[X]) * t1 ^ 2 * v1 + (1600 : F[X]) * t1 * u2 -
            (1792 : F[X]) * t1 * w2 +
            ((462 : F[X]) * Polynomial.C lambda * t1 ^ 3 -
                (385 : F[X]) * t1 ^ 4) *
              h ^ 2) := by
  simp only [thirteenthFace_zeroU1_Gcof810]
  have hid :
      -(2560 : F[X]) * a4 + (2048 : F[X]) * b62 -
            (2048 : F[X]) * s1 * v1 + (2240 : F[X]) * v1 ^ 2 =
        -(64 : F[X]) *
            ((40 : F[X]) * a4 - (32 : F[X]) * b62 +
              (5 : F[X]) * v1 ^ 2) -
          (64 : F[X]) * v1 *
            ((32 : F[X]) * s1 - (40 : F[X]) * v1) := by
    ring
  rw [hid, hsigma]
  ring

/-- Cofactor of `h²` in the sixth-jet fifth defect after the extra
right vanishing `t₀ = h t₁`. -/
def thirteenthFace_comp_Vcof810
    (h t1 v1 s1 w1 u1 a4 a3 b62 b5 : F[X]) (lambda : F) : F[X] :=
  -(4096 : F[X]) *
      (-(32 : F[X]) * b5 + (32 : F[X]) * s1 * u1 -
        (65 : F[X]) * u1 * v1 + (28 : F[X]) * v1 * w1) +
    ((36864 : F[X]) * a4 * Polynomial.C lambda +
        (81920 : F[X]) * a4 * t1 - (98304 : F[X]) * b62 * t1 -
      (29952 : F[X]) * Polynomial.C lambda * v1 ^ 2 +
        (212992 : F[X]) * s1 * t1 * v1 -
      (199680 : F[X]) * t1 * v1 ^ 2) *
      h +
    (-(163840 : F[X]) * a3 - (59904 : F[X]) * Polynomial.C lambda * t1 *
          u1 -
      (49920 : F[X]) * t1 ^ 2 * u1 + (93184 : F[X]) * t1 ^ 2 * w1) *
      h ^ 2 +
    ((78624 : F[X]) * Polynomial.C lambda * t1 ^ 2 * v1 -
        (93184 : F[X]) * s1 * t1 ^ 3 +
      (29120 : F[X]) * t1 ^ 3 * v1) *
      h ^ 3 +
    (-(23751 : F[X]) * Polynomial.C lambda * t1 ^ 4 +
        (21112 : F[X]) * t1 ^ 5) *
      h ^ 5

set_option maxHeartbeats 8000000 in
theorem thirteenthFace_fifth_comp_mul_h
    (h t1 v1 s1 w1 u1 a4 a3 b62 b5 : F[X]) (lambda : F) :
    fifthJetParen810_sixth h (h * t1) (h * v1) (h * s1) (h * w1)
        (h * u1) a4 a3 (h ^ 2 * b62) b5 lambda =
      h ^ 2 *
        thirteenthFace_comp_Vcof810 h t1 v1 s1 w1 u1 a4 a3 b62 b5
          lambda := by
  simp only [fifthJetParen810_sixth, thirteenthFace_comp_Vcof810]
  ring

theorem thirteenthFace_comp_V_s1_810 (v1 s1 a4 b62 t1 omega beta : F)
    (lambda : F)
    (hM : (4 : F) * s1 = (5 : F) * v1)
    (hV : (8192 : F) * beta - (28672 : F) * omega * v1 +
        (36864 : F) * a4 * lambda + (81920 : F) * a4 * t1 -
        (98304 : F) * b62 * t1 - (29952 : F) * lambda * v1 ^ 2 +
        (212992 : F) * s1 * t1 * v1 - (199680 : F) * t1 * v1 ^ 2 =
      0) :
    (32 : F) * beta + (144 : F) * a4 * lambda +
        (320 : F) * a4 * t1 - (384 : F) * b62 * t1 -
        (117 : F) * lambda * v1 ^ 2 - (112 : F) * omega * v1 +
      (260 : F) * t1 * v1 ^ 2 =
      0 := by
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hMrel : (32 : F) * s1 - (40 : F) * v1 = 0 := by
    linear_combination (8 : F) * hM
  have hid :
      (256 : F) *
          ((32 : F) * beta + (144 : F) * a4 * lambda +
            (320 : F) * a4 * t1 - (384 : F) * b62 * t1 -
            (117 : F) * lambda * v1 ^ 2 - (112 : F) * omega * v1 +
            (260 : F) * t1 * v1 ^ 2) =
        (8192 : F) * beta - (28672 : F) * omega * v1 +
            (36864 : F) * a4 * lambda + (81920 : F) * a4 * t1 -
            (98304 : F) * b62 * t1 - (29952 : F) * lambda * v1 ^ 2 +
            (212992 : F) * s1 * t1 * v1 -
            (199680 : F) * t1 * v1 ^ 2 -
          (6656 : F) * t1 * v1 *
            ((32 : F) * s1 - (40 : F) * v1) := by
    ring
  have hcomb :
      (256 : F) *
          ((32 : F) * beta + (144 : F) * a4 * lambda +
            (320 : F) * a4 * t1 - (384 : F) * b62 * t1 -
            (117 : F) * lambda * v1 ^ 2 - (112 : F) * omega * v1 +
            (260 : F) * t1 * v1 ^ 2) =
        0 := by
    rw [hid]
    linear_combination hV - (6656 : F) * t1 * v1 * hMrel
  exact (mul_eq_zero.mp hcomb).resolve_left h256

/-- The next-order fifth cofactor on the left reduces to `Vnext`. -/
theorem thirteenthFace_left_c1V_reduces810
    (t0 v1 u1 a4 b62 m1 tau1 : F) (lambda : F)
    (hM : m1 + (9 : F) * lambda * t0 = 0)
    (hT : (4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
      (144 : F) * lambda * v1 =
      0)
    (hG : (2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
        (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
      (320 : F) * v1 ^ 2 =
      0)
    (c1V : F)
    (hc1 : c1V =
      (36864 : F) * a4 * lambda - (23751 : F) * lambda * t0 ^ 4 +
        (78624 : F) * lambda * t0 ^ 2 * v1 -
        (59904 : F) * lambda * t0 * u1 -
        (29952 : F) * lambda * v1 ^ 2 - (2912 : F) * m1 * t0 ^ 3 +
        (6656 : F) * m1 * t0 * v1 - (4096 : F) * m1 * u1 +
        (728 : F) * t0 ^ 2 * tau1 - (896 : F) * tau1 * v1) :
    (5 : F) * c1V = (9 : F) * lambda *
      thirteenthFace_leftVnext810 t0 v1 u1 b62 := by
  unfold thirteenthFace_leftVnext810
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hid :
      (4 : F) *
          ((5 : F) *
                ((36864 : F) * a4 * lambda -
                  (23751 : F) * lambda * t0 ^ 4 +
                  (78624 : F) * lambda * t0 ^ 2 * v1 -
                  (59904 : F) * lambda * t0 * u1 -
                  (29952 : F) * lambda * v1 ^ 2 -
                  (2912 : F) * m1 * t0 ^ 3 +
                  (6656 : F) * m1 * t0 * v1 -
                  (4096 : F) * m1 * u1 +
                  (728 : F) * t0 ^ 2 * tau1 -
                  (896 : F) * tau1 * v1) -
              (9 : F) * lambda *
                ((16384 : F) * b62 + (175 : F) * t0 ^ 4 -
                  (1120 : F) * t0 ^ 2 * v1 -
                  (17920 : F) * t0 * u1 - (1280 : F) * v1 ^ 2)) =
        ((-58240 : F) * t0 ^ 3 + (133120 : F) * t0 * v1 -
            (81920 : F) * u1) *
            (m1 + (9 : F) * lambda * t0) +
          ((3640 : F) * t0 ^ 2 - (4480 : F) * v1) *
            ((4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
              (144 : F) * lambda * v1) +
          (288 : F) * lambda *
            ((2560 : F) * a4 - (2048 : F) * b62 +
              (35 : F) * t0 ^ 4 - (240 : F) * t0 ^ 2 * v1 +
              (640 : F) * t0 * u1 + (320 : F) * v1 ^ 2) := by
    ring
  have hcomb :
      (4 : F) *
          ((5 : F) * c1V - (9 : F) * lambda *
            ((16384 : F) * b62 + (175 : F) * t0 ^ 4 -
              (1120 : F) * t0 ^ 2 * v1 - (17920 : F) * t0 * u1 -
              (1280 : F) * v1 ^ 2)) =
        0 := by
    rw [hc1, hid, hM, hT, hG]
    ring
  have hzero := (mul_eq_zero.mp hcomb).resolve_left h4
  linear_combination hzero

end ThirteenthFaceScalars810

/-! ## Source-facing thirteenth-face packet -/

section NonzeroThirteenthFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local thirteenth-face packet: the twelfth-face split together
with the source-facing refinement of every live branch. -/
theorem nonzeroFace810_linearRoot_thirteenthInitialPacket
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
                  0 ∧
                (1024 : k) * (q.coeff 5).eval a -
                    (256 : k) * b62.eval a * t0.eval a -
                    (11 : k) * (t0.eval a) ^ 5 +
                  (40 : k) * (t0.eval a) ^ 3 * v1.eval a =
                  0 ∧
                ((3 : k) * (t0.eval a) ^ 2 - (8 : k) * v1.eval a) *
                    ((1024 : k) * b62.eval a +
                      (25 : k) * (t0.eval a) ^ 4 -
                      (320 : k) * (v1.eval a) ^ 2) =
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
                ∃ (t1 u2 w2 b51 sigma rho : k[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : k[X]) * (p.coeff 4) -
                          (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2) ∧
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
                ∃ (t1 omega sigma beta : k[X]),
                  t0 = h0 * t1 ∧
                    (4 : k[X]) * w1 - (5 : k[X]) * u1 =
                      h0 * omega ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (16 : k[X]) * (q.coeff 5) -
                        (5 : k[X]) * u1 * v1 =
                      h0 * beta ∧
                    h0 ^ 2 ∣ ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ∣
                      ((16 : k[X]) * (q.coeff 5) -
                        (5 : k[X]) * u1 * v1) ∧
                    (8 : k) * omega.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0)))) := by
  obtain ⟨delta, hGrel⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_twelfthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred, hWred,
      hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt, ⟨m1, tau1, hm1, htau1, hM1,
        hT1⟩, hF1w⟩ := hleft
    have hF1all :
        twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
              (u1.eval a) →
          (128 : k) * w1.eval a -
                (5 : k) * t0.eval a *
                  ((24 : k) * v1.eval a -
                    (5 : k) * (t0.eval a) ^ 2) =
              0 ∧
            (1024 : k) * (q.coeff 5).eval a -
                (256 : k) * b62.eval a * t0.eval a -
                (11 : k) * (t0.eval a) ^ 5 +
              (40 : k) * (t0.eval a) ^ 3 * v1.eval a =
              0 ∧
            ((3 : k) * (t0.eval a) ^ 2 - (8 : k) * v1.eval a) *
                ((1024 : k) * b62.eval a +
                  (25 : k) * (t0.eval a) ^ 4 -
                  (320 : k) * (v1.eval a) ^ 2) =
              0 := fun hF1 =>
      ⟨hF1w hF1,
        thirteenthFace_leftF1_b5_810 (t0.eval a) (v1.eval a)
          (u1.eval a) ((p.coeff 4).eval a) (b62.eval a)
          ((q.coeff 5).eval a) hF1 hGred hVred,
        thirteenthFace_leftF1_sixth_product810 (t0.eval a)
          (v1.eval a) (u1.eval a) ((p.coeff 4).eval a) (b62.eval a)
          ((q.coeff 5).eval a) hF1 hGred hVred hWred⟩
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred,
        hWred, hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt,
        ⟨m1, tau1, hm1, htau1, hM1, hT1⟩, hF1all⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
      hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, hright'⟩ :=
      hright
    refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
        hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, ?_⟩⟩
    rcases hright' with hu1z | hcomp
    · obtain ⟨hu1z, t1, u2, w2, b51, sigma, ht1, hu2, hw2, hb51,
        hsigmapoly, hp5_3, hq7_5, hq5d, hsigmadvd, hTform, hVform,
        hprod⟩ := hu1z
      have hGcomb_eval :
          ((40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
              (5 : k[X]) * v1 ^ 2).eval a =
            0 := by
        simpa using ha4
      obtain ⟨gamma, hgamma⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
            (5 : k[X]) * v1 ^ 2)
          a hh0degree hroot hGcomb_eval
      have hGsubst :
          localClearedFourthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (p.coeff 4) (h0 ^ 5 * s0) (h0 ^ 3 * w0)
              (h0 ^ 2 * b62) lambda =
            localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
              (q.coeff 6) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0, hb62]
      have hGparen :
          fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (h0 ^ 2 * b62) lambda =
            Polynomial.C delta * h0 ^ 6 :=
        fourthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0
          (p.coeff 4) (h0 ^ 2 * b62) lambda delta hh0
          (hGsubst.trans hGrel)
      have hu0' : u0 = h0 ^ 2 * u2 := by
        rw [hu1, hu2]
        ring
      have hw0' : w0 = h0 ^ 2 * w2 := by
        rw [hw1, hw2]
        ring
      have hGleft :
          fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (h0 ^ 2 * b62) lambda =
            h0 ^ 2 *
              thirteenthFace_zeroU1_Gcof810 h0 t1 v1 s1 w2 u2
                (p.coeff 4) b62 lambda := by
        simpa [ht1, hv1, hs1, hw0', hu0'] using
          thirteenthFace_fourth_zeroU1_mul_h h0 t1 v1 s1 w2 u2
            (p.coeff 4) b62 lambda
      have hGcof :
          thirteenthFace_zeroU1_Gcof810 h0 t1 v1 s1 w2 u2 (p.coeff 4)
              b62 lambda =
            Polynomial.C delta * h0 ^ 4 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
        have hscale : Polynomial.C delta * h0 ^ 6 =
            h0 ^ 2 * (Polynomial.C delta * h0 ^ 4) := by ring
        rw [← hGleft, hGparen, hscale]
      have hGfact :=
        thirteenthFace_zeroU1_Gcof_sigma h0 t1 v1 s1 w2 u2
          (p.coeff 4) b62 sigma lambda hsigmapoly
      have hgamma_eval : gamma.eval a = 0 := by
        have hrew :
            thirteenthFace_zeroU1_Gcof810 h0 t1 v1 s1 w2 u2
                (p.coeff 4) b62 lambda =
              -(64 : k[X]) * (h0 * gamma) +
                h0 ^ 2 *
                  (-(64 : k[X]) * sigma * v1 -
                    (1008 : k[X]) * Polynomial.C lambda * t1 * v1 +
                    (576 : k[X]) * Polynomial.C lambda * u2 +
                    (1792 : k[X]) * s1 * t1 ^ 2 -
                    (1120 : k[X]) * t1 ^ 2 * v1 +
                    (1600 : k[X]) * t1 * u2 -
                    (1792 : k[X]) * t1 * w2 +
                    ((462 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
                        (385 : k[X]) * t1 ^ 4) *
                      h0 ^ 2) := by
          rw [hGfact, hgamma]
        have hpoly :
            -(64 : k[X]) * (h0 * gamma) +
                h0 ^ 2 *
                  (-(64 : k[X]) * sigma * v1 -
                    (1008 : k[X]) * Polynomial.C lambda * t1 * v1 +
                    (576 : k[X]) * Polynomial.C lambda * u2 +
                    (1792 : k[X]) * s1 * t1 ^ 2 -
                    (1120 : k[X]) * t1 ^ 2 * v1 +
                    (1600 : k[X]) * t1 * u2 -
                    (1792 : k[X]) * t1 * w2 +
                    ((462 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
                        (385 : k[X]) * t1 ^ 4) *
                      h0 ^ 2) =
              Polynomial.C delta * h0 ^ 4 := by
          rw [← hrew, hGcof]
        have hfactor :
            h0 *
                (-(64 : k[X]) * gamma +
                  h0 *
                    (-(64 : k[X]) * sigma * v1 -
                      (1008 : k[X]) * Polynomial.C lambda * t1 *
                        v1 +
                      (576 : k[X]) * Polynomial.C lambda * u2 +
                      (1792 : k[X]) * s1 * t1 ^ 2 -
                      (1120 : k[X]) * t1 ^ 2 * v1 +
                      (1600 : k[X]) * t1 * u2 -
                      (1792 : k[X]) * t1 * w2 +
                      ((462 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
                          (385 : k[X]) * t1 ^ 4) *
                        h0 ^ 2)) =
              Polynomial.C delta * h0 ^ 4 := by
          convert hpoly using 1
          ring
        have hred :
            -(64 : k[X]) * gamma +
                h0 *
                  (-(64 : k[X]) * sigma * v1 -
                    (1008 : k[X]) * Polynomial.C lambda * t1 * v1 +
                    (576 : k[X]) * Polynomial.C lambda * u2 +
                    (1792 : k[X]) * s1 * t1 ^ 2 -
                    (1120 : k[X]) * t1 ^ 2 * v1 +
                    (1600 : k[X]) * t1 * u2 -
                    (1792 : k[X]) * t1 * w2 +
                    ((462 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
                        (385 : k[X]) * t1 ^ 4) *
                      h0 ^ 2) =
              Polynomial.C delta * h0 ^ 3 := by
          apply mul_left_cancel₀ hh0
          have hscale : Polynomial.C delta * h0 ^ 4 =
              h0 * (Polynomial.C delta * h0 ^ 3) := by ring
          rw [hfactor, hscale]
        have := congrArg (fun r : k[X] => Polynomial.eval a r) hred
        have h64 : (64 : k) ≠ 0 := by norm_num
        have hgeval : -(64 : k) * gamma.eval a = 0 := by
          simpa [hroot] using this
        have : (64 : k) * gamma.eval a = 0 := by
          linear_combination -hgeval
        exact (mul_eq_zero.mp this).resolve_left h64
      obtain ⟨rho, hrho⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 gamma a
          hh0degree hroot hgamma_eval
      have hrhopoly :
          (40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
              (5 : k[X]) * v1 ^ 2 =
            h0 ^ 2 * rho := by
        rw [hgamma, hrho]
        ring
      have hrhovd :
          h0 ^ 2 ∣
            ((40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
              (5 : k[X]) * v1 ^ 2) :=
        ⟨rho, by rw [hrhopoly]⟩
      refine Or.inl ⟨hu1z, t1, u2, w2, b51, sigma, rho, ht1, hu2, hw2,
        hb51, hsigmapoly, hrhopoly, hp5_3, hq7_5, hq5d, hsigmadvd,
        hrhovd, hTform, hVform, hprod⟩
    · obtain ⟨hB, ha4c, hu1c, t1, omega, sigma, ht1, homega, hsigmapoly,
        hsigmadvd, hTform⟩ := hcomp
      have hbeta_eval :
          ((16 : k[X]) * (q.coeff 5) - (5 : k[X]) * u1 * v1).eval a =
            0 := by
        have : (16 : k) * (q.coeff 5).eval a -
            (5 : k) * u1.eval a * v1.eval a = 0 := by
          linear_combination hb5
        simpa using this
      obtain ⟨beta, hbeta⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((16 : k[X]) * (q.coeff 5) - (5 : k[X]) * u1 * v1) a
          hh0degree hroot hbeta_eval
      have hbetadvd :
          h0 ∣
            ((16 : k[X]) * (q.coeff 5) - (5 : k[X]) * u1 * v1) :=
        ⟨beta, by rw [hbeta]⟩
      exact Or.inr ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1, homega,
        hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform⟩

/-- Source-facing thirteenth-face packet of a normalized scale-two `(8,10)`
nonzero face: the twelfth-face split together with the next-order
fourth/fifth refinements of every live branch. -/
theorem normalized810ScaleTwo_nonzeroFace_thirteenthInitialPacket
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
                  0 ∧
                (1024 : K) * (q.coeff 5).eval a -
                    (256 : K) * b62.eval a * t0.eval a -
                    (11 : K) * (t0.eval a) ^ 5 +
                  (40 : K) * (t0.eval a) ^ 3 * v1.eval a =
                  0 ∧
                ((3 : K) * (t0.eval a) ^ 2 - (8 : K) * v1.eval a) *
                    ((1024 : K) * b62.eval a +
                      (25 : K) * (t0.eval a) ^ 4 -
                      (320 : K) * (v1.eval a) ^ 2) =
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
                ∃ (t1 u2 w2 b51 sigma rho : K[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : K[X]) * (p.coeff 4) -
                          (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : K[X]) * (p.coeff 4) -
                          (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2) ∧
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
                ∃ (t1 omega sigma beta : K[X]),
                  t0 = h0 * t1 ∧
                    (4 : K[X]) * w1 - (5 : K[X]) * u1 =
                      h0 * omega ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (16 : K[X]) * (q.coeff 5) -
                        (5 : K[X]) * u1 * v1 =
                      h0 * beta ∧
                    h0 ^ 2 ∣ ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ∣
                      ((16 : K[X]) * (q.coeff 5) -
                        (5 : K[X]) * u1 * v1) ∧
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
    nonzeroFace810_linearRoot_thirteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroThirteenthFace810

#print axioms thirteenthCoefficientJacobianRow_810
#print axioms thirteenthFace_leftF1_b5_810
#print axioms thirteenthFace_leftF1_sixth_product810
#print axioms thirteenthFace_left_G_nextOrder810
#print axioms thirteenthFace_left_c1V_reduces810
#print axioms thirteenthFace_comp_V_nextOrder810
#print axioms thirteenthFace_fourth_zeroU1_mul_h
#print axioms thirteenthFace_fifth_comp_mul_h
#print axioms nonzeroFace810_linearRoot_thirteenthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_thirteenthInitialPacket

end Max11DegreeRoutes



