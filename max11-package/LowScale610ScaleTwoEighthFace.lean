import LowScale610ScaleTwoSeventhFace

/-! # Scale-two eighth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the seventh face supplies the degree-`8` integral
and the jet `h⁴ ∣ p₅`, `h² ∣ p₄`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`,
`h⁸ ∣ q₉`.  The next Keller coefficient is the degree-`7` Jacobian
row.

Evaluating the second through seventh defects together at the root of
`h` on that jet forces the one-parameter identities
`3 (p₄/h²)(a) = w²`, `9 (q₈/h⁶)(a) = 10 w²`, `27 p₃(a) = w³`,
`27 (q₇/h⁴)(a) = 10 w³`, `81 (q₆/h²)(a) = 5 w⁴`, and
`243 q₅(a) = w⁵` with `w = (p₅/h⁴)(a)`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The eighth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  It is the source of the first mixed sextic/decic
`z⁰`/`z²` defect after the degree-`8` integral. -/
theorem eighthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 6).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 7).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 7) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (7 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 7 :
      Finset (ℕ × ℕ)) =
      ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1),
        (7, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8]
  linear_combination hcoeff

/-! ## One-parameter root identities -/

section EighthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The second and third defects on the seventh-face jet reduce to a
linear relation among `u`, `p₃`, `a₄s`, and `w`. -/
theorem eighthFace_T1_610 (w a4s s u p3 : F)
    (hM : (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
        (520 : F) * w ^ 3 - (1080 : F) * p3 = 0) :
    (81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
      (90 : F) * w * a4s = 0 := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hid :
      (8 : F) * ((81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
          (90 : F) * w * a4s) =
        (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
          (520 : F) * w ^ 3 - (1080 : F) * p3 +
        (48 : F) * w *
          ((18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2) := by
    ring
  have hcomb :
      (8 : F) * ((81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
          (90 : F) * w * a4s) = 0 := by
    rw [hid]
    linear_combination hT + (48 : F) * w * hM
  exact (mul_eq_zero.mp hcomb).resolve_left h8

/-- The second through fourth defects on the seventh-face jet reduce to
a linear relation among `b₆s`, `p₃`, `a₄s`, and `w`. -/
theorem eighthFace_U2_610 (w a4s s u p3 b6s : F)
    (hM : (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
        (520 : F) * w ^ 3 - (1080 : F) * p3 = 0)
    (hU : (432 : F) * b6s + (720 : F) * a4s ^ 2 - (576 : F) * a4s * s -
        (504 : F) * w * u + (360 : F) * w * p3 - (360 : F) * w ^ 4 +
        (576 : F) * s * w ^ 2 = 0) :
    -(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s - (135 : F) * a4s ^ 2 -
      (270 : F) * w * p3 + (243 : F) * b6s = 0 := by
  have hT1 := eighthFace_T1_610 w a4s s u p3 hM hT
  have h144 : (144 : F) ≠ 0 := by norm_num
  have hid :
      (144 : F) * (-(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s -
          (135 : F) * a4s ^ 2 - (270 : F) * w * p3 + (243 : F) * b6s) =
        (81 : F) * ((432 : F) * b6s + (720 : F) * a4s ^ 2 -
            (576 : F) * a4s * s - (504 : F) * w * u +
            (360 : F) * w * p3 - (360 : F) * w ^ 4 +
            (576 : F) * s * w ^ 2 -
          (32 : F) * (w ^ 2 - a4s) *
            ((18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2)) +
        (504 : F) * w * ((81 : F) * u - (135 : F) * p3 +
          (5 : F) * w ^ 3 - (90 : F) * w * a4s) := by
    ring
  have hcomb :
      (144 : F) * (-(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s -
          (135 : F) * a4s ^ 2 - (270 : F) * w * p3 +
          (243 : F) * b6s) = 0 := by
    rw [hid]
    linear_combination (81 : F) * hU + (504 : F) * w * hT1 -
      (81 : F) * (32 : F) * (w ^ 2 - a4s) * hM
  exact (mul_eq_zero.mp hcomb).resolve_left h144

/-- The second through fifth defects on the seventh-face jet reduce to
a linear relation among `q₅`, `p₃`, `a₄s`, and `w`. -/
theorem eighthFace_V3_610 (w a4s s u p3 b6s q5 : F)
    (hM : (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
        (520 : F) * w ^ 3 - (1080 : F) * p3 = 0)
    (hU : (432 : F) * b6s + (720 : F) * a4s ^ 2 - (576 : F) * a4s * s -
        (504 : F) * w * u + (360 : F) * w * p3 - (360 : F) * w ^ 4 +
        (576 : F) * s * w ^ 2 = 0)
    (hV : (285120 : F) * a4s * p3 + (23760 : F) * w ^ 2 * p3 -
        (124416 : F) * s * p3 - (190080 : F) * w * a4s ^ 2 -
        (89760 : F) * w ^ 3 * a4s + (228096 : F) * w * a4s * s -
        (108864 : F) * a4s * u + (68816 : F) * w ^ 5 -
        (107712 : F) * w ^ 3 * s + (99792 : F) * w ^ 2 * u -
        (93312 : F) * w * b6s + (93312 : F) * q5 = 0) :
    (7 : F) * w ^ 5 - (60 : F) * w ^ 3 * a4s + (135 : F) * w * a4s ^ 2 +
      (135 : F) * w ^ 2 * p3 - (810 : F) * a4s * p3 +
      (729 : F) * q5 = 0 := by
  have hT1 := eighthFace_T1_610 w a4s s u p3 hM hT
  have hU2 := eighthFace_U2_610 w a4s s u p3 b6s hM hT hU
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hid :
      (128 : F) * ((7 : F) * w ^ 5 - (60 : F) * w ^ 3 * a4s +
          (135 : F) * w * a4s ^ 2 + (135 : F) * w ^ 2 * p3 -
          (810 : F) * a4s * p3 + (729 : F) * q5) =
        (285120 : F) * a4s * p3 + (23760 : F) * w ^ 2 * p3 -
          (124416 : F) * s * p3 - (190080 : F) * w * a4s ^ 2 -
          (89760 : F) * w ^ 3 * a4s + (228096 : F) * w * a4s * s -
          (108864 : F) * a4s * u + (68816 : F) * w ^ 5 -
          (107712 : F) * w ^ 3 * s + (99792 : F) * w ^ 2 * u -
          (93312 : F) * w * b6s + (93312 : F) * q5 +
        ((6912 : F) * p3 - (12672 : F) * w * a4s + (5984 : F) * w ^ 3) *
          ((18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2) +
        ((168 : F) * a4s - (154 : F) * w ^ 2) *
          (8 : F) * ((81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
            (90 : F) * w * a4s) +
        (384 : F) * w * (-(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s -
          (135 : F) * a4s ^ 2 - (270 : F) * w * p3 + (243 : F) * b6s) := by
    ring
  have hcomb :
      (128 : F) * ((7 : F) * w ^ 5 - (60 : F) * w ^ 3 * a4s +
          (135 : F) * w * a4s ^ 2 + (135 : F) * w ^ 2 * p3 -
          (810 : F) * a4s * p3 + (729 : F) * q5) = 0 := by
    rw [hid]
    linear_combination hV +
      ((6912 : F) * p3 - (12672 : F) * w * a4s + (5984 : F) * w ^ 3) *
        hM +
      ((168 : F) * a4s - (154 : F) * w ^ 2) * (8 : F) * hT1 +
      (384 : F) * w * hU2
  exact (mul_eq_zero.mp hcomb).resolve_left h128

set_option maxHeartbeats 4000000 in
/-- The second through sixth defects on the seventh-face jet reduce to
a quadratic in `p₃` over `a₄s` and `w`. -/
theorem eighthFace_W4_610 (w a4s s u p3 b6s q5 : F)
    (hM : (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
        (520 : F) * w ^ 3 - (1080 : F) * p3 = 0)
    (hU : (432 : F) * b6s + (720 : F) * a4s ^ 2 - (576 : F) * a4s * s -
        (504 : F) * w * u + (360 : F) * w * p3 - (360 : F) * w ^ 4 +
        (576 : F) * s * w ^ 2 = 0)
    (hV : (285120 : F) * a4s * p3 + (23760 : F) * w ^ 2 * p3 -
        (124416 : F) * s * p3 - (190080 : F) * w * a4s ^ 2 -
        (89760 : F) * w ^ 3 * a4s + (228096 : F) * w * a4s * s -
        (108864 : F) * a4s * u + (68816 : F) * w ^ 5 -
        (107712 : F) * w ^ 3 * s + (99792 : F) * w ^ 2 * u -
        (93312 : F) * w * b6s + (93312 : F) * q5 = 0)
    (hW : (583200 : F) * p3 ^ 2 - (1360800 : F) * w * a4s * p3 -
        (432000 : F) * w ^ 3 * p3 + (933120 : F) * w * s * p3 -
        (489888 : F) * u * p3 - (518400 : F) * a4s ^ 3 +
        (518400 : F) * w ^ 2 * a4s ^ 2 + (466560 : F) * a4s ^ 2 * s +
        (633600 : F) * w ^ 4 * a4s - (1244160 : F) * w ^ 2 * a4s * s +
        (816480 : F) * w * a4s * u - (419904 : F) * a4s * b6s -
        (246400 : F) * w ^ 6 + (380160 : F) * w ^ 4 * s -
        (362880 : F) * w ^ 3 * u + (349920 : F) * w ^ 2 * b6s -
        (349920 : F) * w * q5 = 0) :
    (7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s + (162 : F) * w ^ 2 * a4s ^ 2 +
      (108 : F) * w ^ 3 * p3 - (81 : F) * a4s ^ 3 -
      (486 : F) * w * a4s * p3 + (729 : F) * p3 ^ 2 = 0 := by
  have hT1 := eighthFace_T1_610 w a4s s u p3 hM hT
  have hU2 := eighthFace_U2_610 w a4s s u p3 b6s hM hT hU
  have hV3 := eighthFace_V3_610 w a4s s u p3 b6s q5 hM hT hU hV
  have h320 : (320 : F) ≠ 0 := by norm_num
  have hid :
      -(320 : F) * ((7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
          (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
          (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
          (729 : F) * p3 ^ 2) =
        (583200 : F) * p3 ^ 2 - (1360800 : F) * w * a4s * p3 -
          (432000 : F) * w ^ 3 * p3 + (933120 : F) * w * s * p3 -
          (489888 : F) * u * p3 - (518400 : F) * a4s ^ 3 +
          (518400 : F) * w ^ 2 * a4s ^ 2 + (466560 : F) * a4s ^ 2 * s +
          (633600 : F) * w ^ 4 * a4s - (1244160 : F) * w ^ 2 * a4s * s +
          (816480 : F) * w * a4s * u - (419904 : F) * a4s * b6s -
          (246400 : F) * w ^ 6 + (380160 : F) * w ^ 4 * s -
          (362880 : F) * w ^ 3 * u + (349920 : F) * w ^ 2 * b6s -
          (349920 : F) * w * q5 -
        ((51840 : F) * w * p3 + (25920 : F) * a4s ^ 2 -
            (69120 : F) * w ^ 2 * a4s + (21120 : F) * w ^ 4) *
          ((18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2) -
        ((-6048 : F) * p3 + (10080 : F) * w * a4s - (4480 : F) * w ^ 3) *
          ((81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
            (90 : F) * w * a4s) -
        ((-1728 : F) * a4s + (1440 : F) * w ^ 2) *
          (-(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s -
            (135 : F) * a4s ^ 2 - (270 : F) * w * p3 +
            (243 : F) * b6s) -
        (-(480 : F) * w) *
          ((7 : F) * w ^ 5 - (60 : F) * w ^ 3 * a4s +
            (135 : F) * w * a4s ^ 2 + (135 : F) * w ^ 2 * p3 -
            (810 : F) * a4s * p3 + (729 : F) * q5) := by
    ring
  have hcomb :
      -(320 : F) * ((7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
          (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
          (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
          (729 : F) * p3 ^ 2) = 0 := by
    rw [hid]
    linear_combination hW -
      ((51840 : F) * w * p3 + (25920 : F) * a4s ^ 2 -
          (69120 : F) * w ^ 2 * a4s + (21120 : F) * w ^ 4) * hM -
      ((-6048 : F) * p3 + (10080 : F) * w * a4s - (4480 : F) * w ^ 3) *
        hT1 -
      ((-1728 : F) * a4s + (1440 : F) * w ^ 2) * hU2 -
      (-(480 : F) * w) * hV3
  have : ((7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
      (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
      (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
      (729 : F) * p3 ^ 2) = 0 := by
    have : (320 : F) * ((7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
        (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
        (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
        (729 : F) * p3 ^ 2) = 0 := by
      linear_combination -hcomb
    exact (mul_eq_zero.mp this).resolve_left h320
  exact this

set_option maxHeartbeats 4000000 in
/-- The second through seventh defects on the seventh-face jet reduce to
a second quadratic in `p₃` over `a₄s` and `w`. -/
theorem eighthFace_X4_610 (w a4s s u p3 b6s q5 : F)
    (hM : (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
        (520 : F) * w ^ 3 - (1080 : F) * p3 = 0)
    (hU : (432 : F) * b6s + (720 : F) * a4s ^ 2 - (576 : F) * a4s * s -
        (504 : F) * w * u + (360 : F) * w * p3 - (360 : F) * w ^ 4 +
        (576 : F) * s * w ^ 2 = 0)
    (hV : (285120 : F) * a4s * p3 + (23760 : F) * w ^ 2 * p3 -
        (124416 : F) * s * p3 - (190080 : F) * w * a4s ^ 2 -
        (89760 : F) * w ^ 3 * a4s + (228096 : F) * w * a4s * s -
        (108864 : F) * a4s * u + (68816 : F) * w ^ 5 -
        (107712 : F) * w ^ 3 * s + (99792 : F) * w ^ 2 * u -
        (93312 : F) * w * b6s + (93312 : F) * q5 = 0)
    (hX : -(3840 : F) * w * p3 ^ 2 - (9600 : F) * a4s ^ 2 * p3 +
        (4800 : F) * w ^ 2 * a4s * p3 + (6144 : F) * a4s * s * p3 +
        (4200 : F) * w ^ 4 * p3 - (7680 : F) * w ^ 2 * s * p3 +
        (5376 : F) * w * u * p3 - (3072 : F) * b6s * p3 +
        (6400 : F) * w * a4s ^ 3 - (7680 : F) * w * a4s ^ 2 * s +
        (2688 : F) * a4s ^ 2 * u - (5040 : F) * w ^ 5 * a4s +
        (8960 : F) * w ^ 3 * a4s * s - (6720 : F) * w ^ 2 * a4s * u +
        (4608 : F) * w * a4s * b6s - (2560 : F) * a4s * q5 +
        (1320 : F) * w ^ 7 - (2016 : F) * w ^ 5 * s +
        (1960 : F) * w ^ 4 * u - (1920 : F) * w ^ 3 * b6s +
        (1920 : F) * w ^ 2 * q5 = 0) :
    (3 : F) * w ^ 7 - (28 : F) * w ^ 5 * a4s + (78 : F) * w ^ 3 * a4s ^ 2 +
      (45 : F) * w ^ 4 * p3 - (54 : F) * w * a4s ^ 3 -
      (216 : F) * w ^ 2 * a4s * p3 + (81 : F) * a4s ^ 2 * p3 +
      (243 : F) * w * p3 ^ 2 = 0 := by
  have hT1 := eighthFace_T1_610 w a4s s u p3 hM hT
  have hU2 := eighthFace_U2_610 w a4s s u p3 b6s hM hT hU
  have hV3 := eighthFace_V3_610 w a4s s u p3 b6s q5 hM hT hU hV
  have h10240 : (10240 : F) ≠ 0 := by norm_num
  have hid :
      (10240 : F) * ((3 : F) * w ^ 7 - (28 : F) * w ^ 5 * a4s +
          (78 : F) * w ^ 3 * a4s ^ 2 + (45 : F) * w ^ 4 * p3 -
          (54 : F) * w * a4s ^ 3 - (216 : F) * w ^ 2 * a4s * p3 +
          (81 : F) * a4s ^ 2 * p3 + (243 : F) * w * p3 ^ 2) =
        (1458 : F) * (-(3840 : F) * w * p3 ^ 2 - (9600 : F) * a4s ^ 2 * p3 +
          (4800 : F) * w ^ 2 * a4s * p3 + (6144 : F) * a4s * s * p3 +
          (4200 : F) * w ^ 4 * p3 - (7680 : F) * w ^ 2 * s * p3 +
          (5376 : F) * w * u * p3 - (3072 : F) * b6s * p3 +
          (6400 : F) * w * a4s ^ 3 - (7680 : F) * w * a4s ^ 2 * s +
          (2688 : F) * a4s ^ 2 * u - (5040 : F) * w ^ 5 * a4s +
          (8960 : F) * w ^ 3 * a4s * s - (6720 : F) * w ^ 2 * a4s * u +
          (4608 : F) * w * a4s * b6s - (2560 : F) * a4s * q5 +
          (1320 : F) * w ^ 7 - (2016 : F) * w ^ 5 * s +
          (1960 : F) * w ^ 4 * u - (1920 : F) * w ^ 3 * b6s +
          (1920 : F) * w ^ 2 * q5) -
        (81 : F) * ((6144 : F) * a4s * p3 - (7680 : F) * w ^ 2 * p3 -
            (7680 : F) * w * a4s ^ 2 + (8960 : F) * w ^ 3 * a4s -
            (2016 : F) * w ^ 5) *
          ((18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2) -
        (18 : F) * ((5376 : F) * w * p3 + (2688 : F) * a4s ^ 2 -
            (6720 : F) * w ^ 2 * a4s + (1960 : F) * w ^ 4) *
          ((81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
            (90 : F) * w * a4s) -
        (6 : F) * (-(3072 : F) * p3 + (4608 : F) * w * a4s -
            (1920 : F) * w ^ 3) *
          (-(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s -
            (135 : F) * a4s ^ 2 - (270 : F) * w * p3 +
            (243 : F) * b6s) -
        (2 : F) * (-(2560 : F) * a4s + (1920 : F) * w ^ 2) *
          ((7 : F) * w ^ 5 - (60 : F) * w ^ 3 * a4s +
            (135 : F) * w * a4s ^ 2 + (135 : F) * w ^ 2 * p3 -
            (810 : F) * a4s * p3 + (729 : F) * q5) := by
    ring
  have hcomb :
      (10240 : F) * ((3 : F) * w ^ 7 - (28 : F) * w ^ 5 * a4s +
          (78 : F) * w ^ 3 * a4s ^ 2 + (45 : F) * w ^ 4 * p3 -
          (54 : F) * w * a4s ^ 3 - (216 : F) * w ^ 2 * a4s * p3 +
          (81 : F) * a4s ^ 2 * p3 + (243 : F) * w * p3 ^ 2) = 0 := by
    rw [hid]
    linear_combination (1458 : F) * hX -
      (81 : F) * ((6144 : F) * a4s * p3 - (7680 : F) * w ^ 2 * p3 -
          (7680 : F) * w * a4s ^ 2 + (8960 : F) * w ^ 3 * a4s -
          (2016 : F) * w ^ 5) * hM -
      (18 : F) * ((5376 : F) * w * p3 + (2688 : F) * a4s ^ 2 -
          (6720 : F) * w ^ 2 * a4s + (1960 : F) * w ^ 4) * hT1 -
      (6 : F) * (-(3072 : F) * p3 + (4608 : F) * w * a4s -
          (1920 : F) * w ^ 3) * hU2 -
      (2 : F) * (-(2560 : F) * a4s + (1920 : F) * w ^ 2) * hV3
  exact (mul_eq_zero.mp hcomb).resolve_left h10240

/-- The sixth-face/seventh-face jet reduces the second through seventh
defects at the root of `h` to the one-parameter identities
`3 a₄s = w²`, `9 s = 10 w²`, `27 p₃ = w³`, `27 u = 10 w³`,
`81 b₆s = 5 w⁴`, and `243 q₅ = w⁵`. -/
theorem eighthFace_rootPowerIdentities610 (w a4s s u p3 b6s q5 : F)
    (hM : (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u + (720 : F) * a4s * w - (864 : F) * s * w +
        (520 : F) * w ^ 3 - (1080 : F) * p3 = 0)
    (hU : (432 : F) * b6s + (720 : F) * a4s ^ 2 - (576 : F) * a4s * s -
        (504 : F) * w * u + (360 : F) * w * p3 - (360 : F) * w ^ 4 +
        (576 : F) * s * w ^ 2 = 0)
    (hV : (285120 : F) * a4s * p3 + (23760 : F) * w ^ 2 * p3 -
        (124416 : F) * s * p3 - (190080 : F) * w * a4s ^ 2 -
        (89760 : F) * w ^ 3 * a4s + (228096 : F) * w * a4s * s -
        (108864 : F) * a4s * u + (68816 : F) * w ^ 5 -
        (107712 : F) * w ^ 3 * s + (99792 : F) * w ^ 2 * u -
        (93312 : F) * w * b6s + (93312 : F) * q5 = 0)
    (hW : (583200 : F) * p3 ^ 2 - (1360800 : F) * w * a4s * p3 -
        (432000 : F) * w ^ 3 * p3 + (933120 : F) * w * s * p3 -
        (489888 : F) * u * p3 - (518400 : F) * a4s ^ 3 +
        (518400 : F) * w ^ 2 * a4s ^ 2 + (466560 : F) * a4s ^ 2 * s +
        (633600 : F) * w ^ 4 * a4s - (1244160 : F) * w ^ 2 * a4s * s +
        (816480 : F) * w * a4s * u - (419904 : F) * a4s * b6s -
        (246400 : F) * w ^ 6 + (380160 : F) * w ^ 4 * s -
        (362880 : F) * w ^ 3 * u + (349920 : F) * w ^ 2 * b6s -
        (349920 : F) * w * q5 = 0)
    (hX : -(3840 : F) * w * p3 ^ 2 - (9600 : F) * a4s ^ 2 * p3 +
        (4800 : F) * w ^ 2 * a4s * p3 + (6144 : F) * a4s * s * p3 +
        (4200 : F) * w ^ 4 * p3 - (7680 : F) * w ^ 2 * s * p3 +
        (5376 : F) * w * u * p3 - (3072 : F) * b6s * p3 +
        (6400 : F) * w * a4s ^ 3 - (7680 : F) * w * a4s ^ 2 * s +
        (2688 : F) * a4s ^ 2 * u - (5040 : F) * w ^ 5 * a4s +
        (8960 : F) * w ^ 3 * a4s * s - (6720 : F) * w ^ 2 * a4s * u +
        (4608 : F) * w * a4s * b6s - (2560 : F) * a4s * q5 +
        (1320 : F) * w ^ 7 - (2016 : F) * w ^ 5 * s +
        (1960 : F) * w ^ 4 * u - (1920 : F) * w ^ 3 * b6s +
        (1920 : F) * w ^ 2 * q5 = 0) :
    (3 : F) * a4s = w ^ 2 ∧ (9 : F) * s = (10 : F) * w ^ 2 ∧
      (27 : F) * p3 = w ^ 3 ∧ (27 : F) * u = (10 : F) * w ^ 3 ∧
      (81 : F) * b6s = (5 : F) * w ^ 4 ∧ (243 : F) * q5 = w ^ 5 := by
  have hT1 := eighthFace_T1_610 w a4s s u p3 hM hT
  have hU2 := eighthFace_U2_610 w a4s s u p3 b6s hM hT hU
  have hV3 := eighthFace_V3_610 w a4s s u p3 b6s q5 hM hT hU hV
  have hW4 := eighthFace_W4_610 w a4s s u p3 b6s q5 hM hT hU hV hW
  have hX4 := eighthFace_X4_610 w a4s s u p3 b6s q5 hM hT hU hV hX
  have hW4form :
      (7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
          (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
          (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
          (729 : F) * p3 ^ 2 =
        ((27 : F) * p3 - ((9 : F) * w * a4s - (2 : F) * w ^ 3)) ^ 2 +
          (3 : F) * (w ^ 2 - (3 : F) * a4s) ^ 3 := by
    ring
  have hlin :
      (729 : F) * ((3 : F) * w ^ 7 - (28 : F) * w ^ 5 * a4s +
          (78 : F) * w ^ 3 * a4s ^ 2 + (45 : F) * w ^ 4 * p3 -
          (54 : F) * w * a4s ^ 3 - (216 : F) * w ^ 2 * a4s * p3 +
          (81 : F) * a4s ^ 2 * p3 + (243 : F) * w * p3 ^ 2) -
        (243 : F) * w * ((7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
          (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
          (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
          (729 : F) * p3 ^ 2) =
        (w ^ 2 - (3 : F) * a4s) ^ 2 * (243 : F) *
          ((27 : F) * p3 - ((9 : F) * w * a4s - (2 : F) * w ^ 3)) := by
    ring
  have hlin0 :
      (w ^ 2 - (3 : F) * a4s) ^ 2 *
          ((27 : F) * p3 - ((9 : F) * w * a4s - (2 : F) * w ^ 3)) = 0 := by
    have h243 : (243 : F) ≠ 0 := by norm_num
    have : (w ^ 2 - (3 : F) * a4s) ^ 2 * (243 : F) *
        ((27 : F) * p3 - ((9 : F) * w * a4s - (2 : F) * w ^ 3)) = 0 := by
      rw [← hlin]
      linear_combination (729 : F) * hX4 - (243 : F) * w * hW4
    have : (w ^ 2 - (3 : F) * a4s) ^ 2 *
        ((27 : F) * p3 - ((9 : F) * w * a4s - (2 : F) * w ^ 3)) * (243 : F) =
        0 := by
      convert this using 1
      ring
    exact (mul_eq_zero.mp this).resolve_right h243
  have hA : w ^ 2 - (3 : F) * a4s = 0 := by
    rcases mul_eq_zero.mp hlin0 with hsq | hQ
    · exact eq_zero_of_pow_eq_zero hsq
    · have : (3 : F) * (w ^ 2 - (3 : F) * a4s) ^ 3 = 0 := by
        have hW0 :
            ((27 : F) * p3 - ((9 : F) * w * a4s - (2 : F) * w ^ 3)) ^ 2 +
              (3 : F) * (w ^ 2 - (3 : F) * a4s) ^ 3 = 0 := by
          rw [← hW4form]
          exact hW4
        simpa [hQ] using hW0
      have h3 : (3 : F) ≠ 0 := by norm_num
      have hcub : (w ^ 2 - (3 : F) * a4s) ^ 3 = 0 :=
        (mul_eq_zero.mp this).resolve_left h3
      exact eq_zero_of_pow_eq_zero hcub
  have ha4 : (3 : F) * a4s = w ^ 2 := by
    linear_combination -hA
  have hs : (9 : F) * s = (10 : F) * w ^ 2 := by
    have h2 : (2 : F) ≠ 0 := by norm_num
    have hid :
        (2 : F) * ((9 : F) * s - (10 : F) * w ^ 2) =
          (18 : F) * s - (30 : F) * a4s - (10 : F) * w ^ 2 +
            (10 : F) * ((3 : F) * a4s - w ^ 2) := by
      ring
    have : (2 : F) * ((9 : F) * s - (10 : F) * w ^ 2) = 0 := by
      rw [hid, hM]
      have : (3 : F) * a4s - w ^ 2 = 0 := by linear_combination ha4
      simpa [this]
    have : (9 : F) * s - (10 : F) * w ^ 2 = 0 :=
      (mul_eq_zero.mp this).resolve_left h2
    linear_combination this
  have hp3 : (27 : F) * p3 = w ^ 3 := by
    have hid :
        (7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
            (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
            (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
            (729 : F) * p3 ^ 2 -
          ((27 : F) * p3 - w ^ 3) ^ 2 =
          ((3 : F) * a4s - w ^ 2) *
            (-(162 : F) * w * p3 - (27 : F) * a4s ^ 2 +
              (45 : F) * w ^ 2 * a4s - (6 : F) * w ^ 4) := by
      ring
    have : ((27 : F) * p3 - w ^ 3) ^ 2 = 0 := by
      have : (3 : F) * a4s - w ^ 2 = 0 := by linear_combination ha4
      have hW' :
          ((27 : F) * p3 - w ^ 3) ^ 2 =
            (7 : F) * w ^ 6 - (63 : F) * w ^ 4 * a4s +
              (162 : F) * w ^ 2 * a4s ^ 2 + (108 : F) * w ^ 3 * p3 -
              (81 : F) * a4s ^ 3 - (486 : F) * w * a4s * p3 +
              (729 : F) * p3 ^ 2 -
            ((3 : F) * a4s - w ^ 2) *
              (-(162 : F) * w * p3 - (27 : F) * a4s ^ 2 +
                (45 : F) * w ^ 2 * a4s - (6 : F) * w ^ 4) := by
        linear_combination -hid
      simpa [this, hW4] using hW'
    have : (27 : F) * p3 - w ^ 3 = 0 := eq_zero_of_pow_eq_zero this
    linear_combination this
  have hu : (27 : F) * u = (10 : F) * w ^ 3 := by
    have hid :
        (3 : F) * ((27 : F) * u - (10 : F) * w ^ 3) =
          (81 : F) * u - (135 : F) * p3 + (5 : F) * w ^ 3 -
            (90 : F) * w * a4s +
          (5 : F) * ((27 : F) * p3 - w ^ 3) +
            (30 : F) * w * ((3 : F) * a4s - w ^ 2) := by
      ring
    have : (3 : F) * ((27 : F) * u - (10 : F) * w ^ 3) = 0 := by
      have hp0 : (27 : F) * p3 - w ^ 3 = 0 := by linear_combination hp3
      have ha0 : (3 : F) * a4s - w ^ 2 = 0 := by linear_combination ha4
      rw [hid, hT1, hp0, ha0]
      simp
    have h3 : (3 : F) ≠ 0 := by norm_num
    have : (27 : F) * u - (10 : F) * w ^ 3 = 0 :=
      (mul_eq_zero.mp this).resolve_left h3
    linear_combination this
  have hb6 : (81 : F) * b6s = (5 : F) * w ^ 4 := by
    have hid :
        (3 : F) * ((81 : F) * b6s - (5 : F) * w ^ 4) =
          -(5 : F) * w ^ 4 + (45 : F) * w ^ 2 * a4s - (135 : F) * a4s ^ 2 -
            (270 : F) * w * p3 + (243 : F) * b6s +
          (45 : F) * a4s * ((3 : F) * a4s - w ^ 2) +
            (10 : F) * w * ((27 : F) * p3 - w ^ 3) := by
      ring
    have : (3 : F) * ((81 : F) * b6s - (5 : F) * w ^ 4) = 0 := by
      have hp0 : (27 : F) * p3 - w ^ 3 = 0 := by linear_combination hp3
      have ha0 : (3 : F) * a4s - w ^ 2 = 0 := by linear_combination ha4
      rw [hid, hU2, hp0, ha0]
      simp
    have h3 : (3 : F) ≠ 0 := by norm_num
    have : (81 : F) * b6s - (5 : F) * w ^ 4 = 0 :=
      (mul_eq_zero.mp this).resolve_left h3
    linear_combination this
  have hq5 : (243 : F) * q5 = w ^ 5 := by
    have hid :
        (3 : F) * ((243 : F) * q5 - w ^ 5) =
          (7 : F) * w ^ 5 - (60 : F) * w ^ 3 * a4s +
            (135 : F) * w * a4s ^ 2 + (135 : F) * w ^ 2 * p3 -
            (810 : F) * a4s * p3 + (729 : F) * q5 -
          ((5 : F) * w ^ 2 - (30 : F) * a4s) *
            ((27 : F) * p3 - w ^ 3) -
          (15 : F) * w * (w ^ 2 - (3 : F) * a4s) ^ 2 := by
      ring
    have : (3 : F) * ((243 : F) * q5 - w ^ 5) = 0 := by
      have hp0 : (27 : F) * p3 - w ^ 3 = 0 := by linear_combination hp3
      have ha0 : w ^ 2 - (3 : F) * a4s = 0 := hA
      rw [hid, hV3, hp0, ha0]
      simp
    have h3 : (3 : F) ≠ 0 := by norm_num
    have : (243 : F) * q5 - w ^ 5 = 0 :=
      (mul_eq_zero.mp this).resolve_left h3
    linear_combination this
  exact ⟨ha4, hs, hp3, hu, hb6, hq5⟩

end EighthFaceScalars610

/-! ## Source-facing eighth-face packet -/

section NonzeroEighthFace610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000 in
/-- Finite local power jet: the seventh-face divisibilities together with
the one-parameter identities at the root of `h`. -/
theorem nonzeroFace610_linearRoot_eighthPowerJet
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ (w a4s s u b6s : k[X]),
      p.coeff 5 = h0 ^ 4 * w ∧ p.coeff 4 = h0 ^ 2 * a4s ∧
        q.coeff 8 = h0 ^ 6 * s ∧ q.coeff 7 = h0 ^ 4 * u ∧
        q.coeff 6 = h0 ^ 2 * b6s ∧
        (3 : k) * a4s.eval a = (w.eval a) ^ 2 ∧
        (9 : k) * s.eval a = (10 : k) * (w.eval a) ^ 2 ∧
        (27 : k) * (p.coeff 3).eval a = (w.eval a) ^ 3 ∧
        (27 : k) * u.eval a = (10 : k) * (w.eval a) ^ 3 ∧
        (81 : k) * b6s.eval a = (5 : k) * (w.eval a) ^ 4 ∧
        (243 : k) * (q.coeff 5).eval a = (w.eval a) ^ 5 := by
  obtain ⟨alpha, hMrel⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨gamma, hTrel⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨delta, hUrel⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace610_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace610_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨eta, hXrel⟩ :=
    nonzeroFace610_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨hp5pow, hp4div, hq8pow, hq7pow, hq6div, _hq9pow⟩ :=
    nonzeroFace610_linearRoot_seventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot
  obtain ⟨w, hw⟩ := hp5pow
  obtain ⟨a4s, ha4s⟩ := hp4div
  obtain ⟨s, hs⟩ := hq8pow
  obtain ⟨u, hu⟩ := hq7pow
  obtain ⟨b6s, hb6s⟩ := hq6div
  have hM0 :
      (18 : k[X]) * s - (30 : k[X]) * a4s - (10 : k[X]) * w ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * w * h0 =
        Polynomial.C alpha * h0 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 8 hh0)
    calc
      h0 ^ 8 *
            ((18 : k[X]) * s - (30 : k[X]) * a4s - (10 : k[X]) * w ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * w * h0) =
          localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect610, hw, ha4s, hs]
        ring
      _ = Polynomial.C alpha * h0 ^ 10 := hMrel
      _ = h0 ^ 8 * (Polynomial.C alpha * h0 ^ 2) := by ring
  have hT0 :
      (648 : k[X]) * u + (720 : k[X]) * a4s * w - (864 : k[X]) * s * w +
          (520 : k[X]) * w ^ 3 - (1080 : k[X]) * p.coeff 3 +
        ((324 : k[X]) * Polynomial.C lambda * a4s -
            (351 : k[X]) * Polynomial.C lambda * w ^ 2) * h0 =
        Polynomial.C gamma * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
    calc
      h0 ^ 12 *
            ((648 : k[X]) * u + (720 : k[X]) * a4s * w -
                (864 : k[X]) * s * w + (520 : k[X]) * w ^ 3 -
              (1080 : k[X]) * p.coeff 3 +
              ((324 : k[X]) * Polynomial.C lambda * a4s -
                  (351 : k[X]) * Polynomial.C lambda * w ^ 2) * h0) =
          localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect610, hw, ha4s, hs, hu]
        ring
      _ = Polynomial.C gamma * h0 ^ 15 := hTrel
      _ = h0 ^ 12 * (Polynomial.C gamma * h0 ^ 3) := by ring
  have hU0 :
      (432 : k[X]) * b6s + (720 : k[X]) * a4s ^ 2 -
          (576 : k[X]) * a4s * s - (504 : k[X]) * w * u +
        (360 : k[X]) * w * p.coeff 3 - (360 : k[X]) * w ^ 4 +
          (576 : k[X]) * s * w ^ 2 +
        ((216 : k[X]) * Polynomial.C lambda * w ^ 3 -
            (432 : k[X]) * Polynomial.C lambda * w * a4s +
            (216 : k[X]) * Polynomial.C lambda * p.coeff 3) * h0 -
          (720 : k[X]) * p.coeff 2 * h0 ^ 2 =
        Polynomial.C delta * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 16 hh0)
    calc
      h0 ^ 16 *
            ((432 : k[X]) * b6s + (720 : k[X]) * a4s ^ 2 -
                (576 : k[X]) * a4s * s - (504 : k[X]) * w * u +
              (360 : k[X]) * w * p.coeff 3 - (360 : k[X]) * w ^ 4 +
                (576 : k[X]) * s * w ^ 2 +
              ((216 : k[X]) * Polynomial.C lambda * w ^ 3 -
                  (432 : k[X]) * Polynomial.C lambda * w * a4s +
                  (216 : k[X]) * Polynomial.C lambda * p.coeff 3) *
                h0 - (720 : k[X]) * p.coeff 2 * h0 ^ 2) =
          localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect610, hw, ha4s, hs, hu, hb6s]
        ring
      _ = Polynomial.C delta * h0 ^ 20 := hUrel
      _ = h0 ^ 16 * (Polynomial.C delta * h0 ^ 4) := by ring
  have hV0 :
      (285120 : k[X]) * a4s * p.coeff 3 + (23760 : k[X]) * w ^ 2 *
            p.coeff 3 - (124416 : k[X]) * s * p.coeff 3 -
          (190080 : k[X]) * w * a4s ^ 2 - (89760 : k[X]) * w ^ 3 * a4s +
        (228096 : k[X]) * w * a4s * s - (108864 : k[X]) * a4s * u +
          (68816 : k[X]) * w ^ 5 - (107712 : k[X]) * w ^ 3 * s +
        (99792 : k[X]) * w ^ 2 * u - (93312 : k[X]) * w * b6s +
          (93312 : k[X]) * q.coeff 5 +
        ((-85536 : k[X]) * Polynomial.C lambda * p.coeff 3 * w -
            (42768 : k[X]) * Polynomial.C lambda * a4s ^ 2 +
            (121176 : k[X]) * Polynomial.C lambda * a4s * w ^ 2 -
            (38709 : k[X]) * Polynomial.C lambda * w ^ 4) * h0 +
          (51840 : k[X]) * w * p.coeff 2 * h0 ^ 2 +
            (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 3 -
              (155520 : k[X]) * p.coeff 1 * h0 ^ 4 =
        Polynomial.C eps * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 20 hh0)
    calc
      h0 ^ 20 *
            ((285120 : k[X]) * a4s * p.coeff 3 +
                (23760 : k[X]) * w ^ 2 * p.coeff 3 -
              (124416 : k[X]) * s * p.coeff 3 -
                (190080 : k[X]) * w * a4s ^ 2 -
              (89760 : k[X]) * w ^ 3 * a4s +
                (228096 : k[X]) * w * a4s * s -
              (108864 : k[X]) * a4s * u + (68816 : k[X]) * w ^ 5 -
                (107712 : k[X]) * w ^ 3 * s +
              (99792 : k[X]) * w ^ 2 * u - (93312 : k[X]) * w * b6s +
                (93312 : k[X]) * q.coeff 5 +
              ((-85536 : k[X]) * Polynomial.C lambda * p.coeff 3 * w -
                  (42768 : k[X]) * Polynomial.C lambda * a4s ^ 2 +
                  (121176 : k[X]) * Polynomial.C lambda * a4s * w ^ 2 -
                  (38709 : k[X]) * Polynomial.C lambda * w ^ 4) * h0 +
                (51840 : k[X]) * w * p.coeff 2 * h0 ^ 2 +
                  (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                      h0 ^ 3 -
                    (155520 : k[X]) * p.coeff 1 * h0 ^ 4) =
          localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda := by
        simp only [localClearedFifthDefect610, hw, ha4s, hs, hu, hb6s]
        ring
      _ = Polynomial.C eps * h0 ^ 25 := hVrel
      _ = h0 ^ 20 * (Polynomial.C eps * h0 ^ 5) := by ring
  have hW0 :
      (583200 : k[X]) * p.coeff 3 ^ 2 - (1360800 : k[X]) * w * a4s *
            p.coeff 3 - (432000 : k[X]) * w ^ 3 * p.coeff 3 +
        (933120 : k[X]) * w * s * p.coeff 3 - (489888 : k[X]) * u *
            p.coeff 3 - (518400 : k[X]) * a4s ^ 3 +
        (518400 : k[X]) * w ^ 2 * a4s ^ 2 + (466560 : k[X]) * a4s ^ 2 *
            s + (633600 : k[X]) * w ^ 4 * a4s -
        (1244160 : k[X]) * w ^ 2 * a4s * s + (816480 : k[X]) * w *
            a4s * u - (419904 : k[X]) * a4s * b6s -
        (246400 : k[X]) * w ^ 6 + (380160 : k[X]) * w ^ 4 * s -
        (362880 : k[X]) * w ^ 3 * u + (349920 : k[X]) * w ^ 2 * b6s -
        (349920 : k[X]) * w * q.coeff 5 +
        ((-349920 : k[X]) * Polynomial.C lambda * a4s * p.coeff 3 +
            (466560 : k[X]) * Polynomial.C lambda * w ^ 2 * p.coeff 3 +
            (466560 : k[X]) * Polynomial.C lambda * w * a4s ^ 2 -
            (570240 : k[X]) * Polynomial.C lambda * w ^ 3 * a4s +
            (133056 : k[X]) * Polynomial.C lambda * w ^ 5) * h0 +
          ((1166400 : k[X]) * a4s * p.coeff 2 +
              (194400 : k[X]) * w ^ 2 * p.coeff 2 -
            (559872 : k[X]) * s * p.coeff 2 +
              (419904 : k[X]) * q.coeff 4) * h0 ^ 2 +
            (-(349920 : k[X]) * Polynomial.C lambda * p.coeff 2 * w) *
                h0 ^ 3 + (116640 : k[X]) * p.coeff 1 * w * h0 ^ 4 +
              (209952 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                  h0 ^ 5 - (699840 : k[X]) * p.coeff 0 * h0 ^ 6 =
        Polynomial.C zeta * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 24 hh0)
    calc
      h0 ^ 24 *
            ((583200 : k[X]) * p.coeff 3 ^ 2 -
                (1360800 : k[X]) * w * a4s * p.coeff 3 -
              (432000 : k[X]) * w ^ 3 * p.coeff 3 +
                (933120 : k[X]) * w * s * p.coeff 3 -
              (489888 : k[X]) * u * p.coeff 3 -
                (518400 : k[X]) * a4s ^ 3 +
              (518400 : k[X]) * w ^ 2 * a4s ^ 2 +
                (466560 : k[X]) * a4s ^ 2 * s +
              (633600 : k[X]) * w ^ 4 * a4s -
                (1244160 : k[X]) * w ^ 2 * a4s * s +
              (816480 : k[X]) * w * a4s * u -
                (419904 : k[X]) * a4s * b6s -
              (246400 : k[X]) * w ^ 6 + (380160 : k[X]) * w ^ 4 * s -
                (362880 : k[X]) * w ^ 3 * u +
              (349920 : k[X]) * w ^ 2 * b6s -
                (349920 : k[X]) * w * q.coeff 5 +
              ((-349920 : k[X]) * Polynomial.C lambda * a4s *
                    p.coeff 3 +
                  (466560 : k[X]) * Polynomial.C lambda * w ^ 2 *
                    p.coeff 3 +
                  (466560 : k[X]) * Polynomial.C lambda * w * a4s ^ 2 -
                  (570240 : k[X]) * Polynomial.C lambda * w ^ 3 * a4s +
                  (133056 : k[X]) * Polynomial.C lambda * w ^ 5) * h0 +
                ((1166400 : k[X]) * a4s * p.coeff 2 +
                    (194400 : k[X]) * w ^ 2 * p.coeff 2 -
                  (559872 : k[X]) * s * p.coeff 2 +
                    (419904 : k[X]) * q.coeff 4) * h0 ^ 2 +
                  (-(349920 : k[X]) * Polynomial.C lambda *
                        p.coeff 2 * w) * h0 ^ 3 +
                    (116640 : k[X]) * p.coeff 1 * w * h0 ^ 4 +
                      (209952 : k[X]) * Polynomial.C lambda *
                          p.coeff 1 * h0 ^ 5 -
                        (699840 : k[X]) * p.coeff 0 * h0 ^ 6) =
          localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda := by
        simp only [localClearedSixthDefect610, hw, ha4s, hs, hu, hb6s]
        ring
      _ = Polynomial.C zeta * h0 ^ 30 := hWrel
      _ = h0 ^ 24 * (Polynomial.C zeta * h0 ^ 6) := by ring
  have hX0 :
      -(3840 : k[X]) * w * p.coeff 3 ^ 2 - (9600 : k[X]) * a4s ^ 2 *
            p.coeff 3 + (4800 : k[X]) * w ^ 2 * a4s * p.coeff 3 +
        (6144 : k[X]) * a4s * s * p.coeff 3 + (4200 : k[X]) * w ^ 4 *
            p.coeff 3 - (7680 : k[X]) * w ^ 2 * s * p.coeff 3 +
        (5376 : k[X]) * w * u * p.coeff 3 - (3072 : k[X]) * b6s *
            p.coeff 3 + (6400 : k[X]) * w * a4s ^ 3 -
        (7680 : k[X]) * w * a4s ^ 2 * s + (2688 : k[X]) * a4s ^ 2 * u -
        (5040 : k[X]) * w ^ 5 * a4s + (8960 : k[X]) * w ^ 3 * a4s * s -
        (6720 : k[X]) * w ^ 2 * a4s * u + (4608 : k[X]) * w * a4s *
            b6s - (2560 : k[X]) * a4s * q.coeff 5 +
        (1320 : k[X]) * w ^ 7 - (2016 : k[X]) * w ^ 5 * s +
        (1960 : k[X]) * w ^ 4 * u - (1920 : k[X]) * w ^ 3 * b6s +
        (1920 : k[X]) * w ^ 2 * q.coeff 5 +
        ((-1152 : k[X]) * Polynomial.C lambda * p.coeff 3 ^ 2 +
            (5760 : k[X]) * Polynomial.C lambda * w * a4s * p.coeff 3 -
            (3360 : k[X]) * Polynomial.C lambda * w ^ 3 * p.coeff 3 +
            (960 : k[X]) * Polynomial.C lambda * a4s ^ 3 -
            (5040 : k[X]) * Polynomial.C lambda * w ^ 2 * a4s ^ 2 +
            (3780 : k[X]) * Polynomial.C lambda * w ^ 4 * a4s -
            (693 : k[X]) * Polynomial.C lambda * w ^ 6) * h0 +
          ((7680 : k[X]) * p.coeff 3 * p.coeff 2 -
              (7680 : k[X]) * w * a4s * p.coeff 2 -
            (3200 : k[X]) * w ^ 3 * p.coeff 2 +
              (6144 : k[X]) * w * s * p.coeff 2 -
            (3584 : k[X]) * u * p.coeff 2 -
              (2048 : k[X]) * w * q.coeff 4) * h0 ^ 2 +
            ((-(2304 : k[X]) * Polynomial.C lambda * p.coeff 2 * a4s +
                (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                  w ^ 2) * h0 ^ 3 +
              ((7680 : k[X]) * p.coeff 1 * a4s +
                  (1920 : k[X]) * p.coeff 1 * w ^ 2 -
                (4096 : k[X]) * p.coeff 1 * s +
                  (3072 : k[X]) * q.coeff 3) * h0 ^ 4 +
                (-(2304 : k[X]) * Polynomial.C lambda * p.coeff 1 * w) *
                    h0 ^ 5 +
                  (1536 : k[X]) * Polynomial.C lambda * p.coeff 0 *
                      h0 ^ 7) =
        Polynomial.C eta * h0 ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 28 hh0)
    calc
      h0 ^ 28 *
            (-(3840 : k[X]) * w * p.coeff 3 ^ 2 -
                (9600 : k[X]) * a4s ^ 2 * p.coeff 3 +
              (4800 : k[X]) * w ^ 2 * a4s * p.coeff 3 +
                (6144 : k[X]) * a4s * s * p.coeff 3 +
              (4200 : k[X]) * w ^ 4 * p.coeff 3 -
                (7680 : k[X]) * w ^ 2 * s * p.coeff 3 +
              (5376 : k[X]) * w * u * p.coeff 3 -
                (3072 : k[X]) * b6s * p.coeff 3 +
              (6400 : k[X]) * w * a4s ^ 3 -
                (7680 : k[X]) * w * a4s ^ 2 * s +
              (2688 : k[X]) * a4s ^ 2 * u -
                (5040 : k[X]) * w ^ 5 * a4s +
              (8960 : k[X]) * w ^ 3 * a4s * s -
                (6720 : k[X]) * w ^ 2 * a4s * u +
              (4608 : k[X]) * w * a4s * b6s -
                (2560 : k[X]) * a4s * q.coeff 5 +
              (1320 : k[X]) * w ^ 7 - (2016 : k[X]) * w ^ 5 * s +
                (1960 : k[X]) * w ^ 4 * u -
              (1920 : k[X]) * w ^ 3 * b6s +
                (1920 : k[X]) * w ^ 2 * q.coeff 5 +
              ((-1152 : k[X]) * Polynomial.C lambda * p.coeff 3 ^ 2 +
                  (5760 : k[X]) * Polynomial.C lambda * w * a4s *
                    p.coeff 3 -
                  (3360 : k[X]) * Polynomial.C lambda * w ^ 3 *
                    p.coeff 3 +
                  (960 : k[X]) * Polynomial.C lambda * a4s ^ 3 -
                  (5040 : k[X]) * Polynomial.C lambda * w ^ 2 *
                    a4s ^ 2 +
                  (3780 : k[X]) * Polynomial.C lambda * w ^ 4 * a4s -
                  (693 : k[X]) * Polynomial.C lambda * w ^ 6) * h0 +
                ((7680 : k[X]) * p.coeff 3 * p.coeff 2 -
                    (7680 : k[X]) * w * a4s * p.coeff 2 -
                  (3200 : k[X]) * w ^ 3 * p.coeff 2 +
                    (6144 : k[X]) * w * s * p.coeff 2 -
                  (3584 : k[X]) * u * p.coeff 2 -
                    (2048 : k[X]) * w * q.coeff 4) * h0 ^ 2 +
                  ((-(2304 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                        a4s +
                      (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                        w ^ 2) * h0 ^ 3 +
                    ((7680 : k[X]) * p.coeff 1 * a4s +
                        (1920 : k[X]) * p.coeff 1 * w ^ 2 -
                      (4096 : k[X]) * p.coeff 1 * s +
                        (3072 : k[X]) * q.coeff 3) * h0 ^ 4 +
                      (-(2304 : k[X]) * Polynomial.C lambda *
                            p.coeff 1 * w) * h0 ^ 5 +
                        (1536 : k[X]) * Polynomial.C lambda *
                            p.coeff 0 * h0 ^ 7)) =
          localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda := by
        simp only [localClearedSeventhDefect610, hw, ha4s, hs, hu, hb6s]
        ring
      _ = Polynomial.C eta * h0 ^ 35 := hXrel
      _ = h0 ^ 28 * (Polynomial.C eta * h0 ^ 7) := by ring
  have hMroot : (18 : k) * s.eval a - (30 : k) * a4s.eval a -
      (10 : k) * (w.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (648 : k) * u.eval a + (720 : k) * a4s.eval a * w.eval a -
      (864 : k) * s.eval a * w.eval a + (520 : k) * (w.eval a) ^ 3 -
      (1080 : k) * (p.coeff 3).eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (432 : k) * b6s.eval a + (720 : k) * (a4s.eval a) ^ 2 -
      (576 : k) * a4s.eval a * s.eval a - (504 : k) * w.eval a * u.eval a +
      (360 : k) * w.eval a * (p.coeff 3).eval a -
      (360 : k) * (w.eval a) ^ 4 + (576 : k) * s.eval a *
        (w.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    simpa [hroot] using heval
  have hVroot : (285120 : k) * a4s.eval a * (p.coeff 3).eval a +
      (23760 : k) * (w.eval a) ^ 2 * (p.coeff 3).eval a -
      (124416 : k) * s.eval a * (p.coeff 3).eval a -
      (190080 : k) * w.eval a * (a4s.eval a) ^ 2 -
      (89760 : k) * (w.eval a) ^ 3 * a4s.eval a +
      (228096 : k) * w.eval a * a4s.eval a * s.eval a -
      (108864 : k) * a4s.eval a * u.eval a +
      (68816 : k) * (w.eval a) ^ 5 -
      (107712 : k) * (w.eval a) ^ 3 * s.eval a +
      (99792 : k) * (w.eval a) ^ 2 * u.eval a -
      (93312 : k) * w.eval a * b6s.eval a +
      (93312 : k) * (q.coeff 5).eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hV0
    simpa [hroot] using heval
  have hWroot : (583200 : k) * ((p.coeff 3).eval a) ^ 2 -
      (1360800 : k) * w.eval a * a4s.eval a * (p.coeff 3).eval a -
      (432000 : k) * (w.eval a) ^ 3 * (p.coeff 3).eval a +
      (933120 : k) * w.eval a * s.eval a * (p.coeff 3).eval a -
      (489888 : k) * u.eval a * (p.coeff 3).eval a -
      (518400 : k) * (a4s.eval a) ^ 3 +
      (518400 : k) * (w.eval a) ^ 2 * (a4s.eval a) ^ 2 +
      (466560 : k) * (a4s.eval a) ^ 2 * s.eval a +
      (633600 : k) * (w.eval a) ^ 4 * a4s.eval a -
      (1244160 : k) * (w.eval a) ^ 2 * a4s.eval a * s.eval a +
      (816480 : k) * w.eval a * a4s.eval a * u.eval a -
      (419904 : k) * a4s.eval a * b6s.eval a -
      (246400 : k) * (w.eval a) ^ 6 +
      (380160 : k) * (w.eval a) ^ 4 * s.eval a -
      (362880 : k) * (w.eval a) ^ 3 * u.eval a +
      (349920 : k) * (w.eval a) ^ 2 * b6s.eval a -
      (349920 : k) * w.eval a * (q.coeff 5).eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hW0
    simpa [hroot] using heval
  have hXroot : -(3840 : k) * w.eval a * ((p.coeff 3).eval a) ^ 2 -
      (9600 : k) * (a4s.eval a) ^ 2 * (p.coeff 3).eval a +
      (4800 : k) * (w.eval a) ^ 2 * a4s.eval a * (p.coeff 3).eval a +
      (6144 : k) * a4s.eval a * s.eval a * (p.coeff 3).eval a +
      (4200 : k) * (w.eval a) ^ 4 * (p.coeff 3).eval a -
      (7680 : k) * (w.eval a) ^ 2 * s.eval a * (p.coeff 3).eval a +
      (5376 : k) * w.eval a * u.eval a * (p.coeff 3).eval a -
      (3072 : k) * b6s.eval a * (p.coeff 3).eval a +
      (6400 : k) * w.eval a * (a4s.eval a) ^ 3 -
      (7680 : k) * w.eval a * (a4s.eval a) ^ 2 * s.eval a +
      (2688 : k) * (a4s.eval a) ^ 2 * u.eval a -
      (5040 : k) * (w.eval a) ^ 5 * a4s.eval a +
      (8960 : k) * (w.eval a) ^ 3 * a4s.eval a * s.eval a -
      (6720 : k) * (w.eval a) ^ 2 * a4s.eval a * u.eval a +
      (4608 : k) * w.eval a * a4s.eval a * b6s.eval a -
      (2560 : k) * a4s.eval a * (q.coeff 5).eval a +
      (1320 : k) * (w.eval a) ^ 7 -
      (2016 : k) * (w.eval a) ^ 5 * s.eval a +
      (1960 : k) * (w.eval a) ^ 4 * u.eval a -
      (1920 : k) * (w.eval a) ^ 3 * b6s.eval a +
      (1920 : k) * (w.eval a) ^ 2 * (q.coeff 5).eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hX0
    simpa [hroot] using heval
  obtain ⟨ha4, hs', hp3, hu', hb6, hq5⟩ :=
    eighthFace_rootPowerIdentities610 (w.eval a) (a4s.eval a) (s.eval a)
      (u.eval a) ((p.coeff 3).eval a) (b6s.eval a) ((q.coeff 5).eval a)
      hMroot hTroot hUroot hVroot hWroot hXroot
  exact ⟨w, a4s, s, u, b6s, hw, ha4s, hs, hu, hb6s, ha4, hs', hp3, hu',
    hb6, hq5⟩

/-- Source-facing eighth-face power jet of a normalized scale-two
`(6,10)` nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_eighthPowerJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K) (w a4s s u b6s : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 4 * w ∧ p.coeff 4 = h0 ^ 2 * a4s ∧
        q.coeff 8 = h0 ^ 6 * s ∧ q.coeff 7 = h0 ^ 4 * u ∧
        q.coeff 6 = h0 ^ 2 * b6s ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        (3 : K) * a4s.eval a = (w.eval a) ^ 2 ∧
        (9 : K) * s.eval a = (10 : K) * (w.eval a) ^ 2 ∧
        (27 : K) * (p.coeff 3).eval a = (w.eval a) ^ 3 ∧
        (27 : K) * u.eval a = (10 : K) * (w.eval a) ^ 3 ∧
        (81 : K) * b6s.eval a = (5 : K) * (w.eval a) ^ 4 ∧
        (243 : K) * (q.coeff 5).eval a = (w.eval a) ^ 5 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hp4, hq8,
    hq7, hq6, hq9, hN⟩ :=
    normalized610ScaleTwo_nonzeroFace_seventhInitialPacket hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨w, a4s, s, u, b6s, hw, ha4s, hs, hu, hb6s, ha4, hs', hp3, hu',
    hb6, hq5⟩ :=
    nonzeroFace610_linearRoot_eighthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, w, a4s, s, u, b6s, hh0, hlambda, hh0degree, hH,
    hroot, hw, ha4s, hs, hu, hb6s, hq9, ha4, hs', hp3, hu', hb6, hq5, hN'⟩

end NonzeroEighthFace610

#print axioms eighthCoefficientJacobianRow_610
#print axioms eighthFace_T1_610
#print axioms eighthFace_U2_610
#print axioms eighthFace_V3_610
#print axioms eighthFace_W4_610
#print axioms eighthFace_X4_610
#print axioms eighthFace_rootPowerIdentities610
#print axioms nonzeroFace610_linearRoot_eighthPowerJet
#print axioms normalized610ScaleTwo_nonzeroFace_eighthPowerJet

end Max11DegreeRoutes
