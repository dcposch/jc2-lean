import LowScale610ScaleTwoNinthFace

/-! # Scale-two tenth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the ninth-face packet supplies the degree-`6`
Jacobian row and the collapsed jet `h⁵ ∣ p₅`, `h³ ∣ p₄`, `h ∣ p₃`,
`h⁷ ∣ q₈`, `h⁵ ∣ q₇`, `h⁴ ∣ q₆`, `h² ∣ q₅`, `h⁸ ∣ q₉` together with
`S₁(a) = 5 A₁(a)`, `5 P₃₁(a) = 3 U₁(a)`, and `B₆₁(a) = Q₅₁(a) = 0`.

The next unused Keller coefficient is the degree-`5` Jacobian row.  After
the same sextic depression that kills `z⁵`, that row is
`6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A' - E R' - 2 D S' - 3 C T'
- 4 B U' - 5 A V' - 7 W' = 0`.  Clearing the corresponding first integral
against the remaining decic coordinate produces a defect larger than the
remaining exact jet, so this file isolates that Jacobian identity and the
strongest exact next-order refinement of the collapsed ninth-face jet.

Evaluating the second through seventh defects at the next order on the
collapsed jet forces
`3 (q₈/h⁷)(a) = 5 (p₄/h³)(a)`, `3 (q₇/h⁵)(a) = 5 (p₃/h)(a)`,
`9 (q₅/h²)(a) = 10 (p₄/h³)(a)(p₃/h)(a)`, `9 q₄(a) = 5 (p₃/h)(a)²`,
and the source-facing load
`10 a₄₁² - 18 b₆₂ - 9 λ p₃₁ + 30 p₂ + 20 p₃₁ w₁ = 0` at the root of
`h`, together with the alternative
`p₃₁ (240 p₂ - 40 a₄₁² - 27 λ p₃₁ - 40 p₃₁ w₁) = 0`.  No further
individual vanishing of `p₂, p₁, p₀, q₄, q₃` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the ninth face start
at degree `5`. -/
theorem tenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
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
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

/-! ## Order-one scalar algebra on the collapsed ninth-face jet -/

section TenthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The second defect at the next order on the collapsed jet is
`3 s₁ = 5 a₄₁`. -/
theorem tenthFace_M_nextOrder610 (a41 s1 : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0) :
    (3 : F) * s1 = (5 : F) * a41 := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have hid : (6 : F) * ((3 : F) * s1 - (5 : F) * a41) =
      (18 : F) * s1 - (30 : F) * a41 := by ring
  have : (6 : F) * ((3 : F) * s1 - (5 : F) * a41) = 0 := by
    rw [hid, hM]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h6)

/-- The third defect at the next order on the collapsed jet is
`3 u₁ = 5 p₃₁`. -/
theorem tenthFace_T_nextOrder610 (p31 u1 : F)
    (hT : (648 : F) * u1 - (1080 : F) * p31 = 0) :
    (3 : F) * u1 = (5 : F) * p31 := by
  have h216 : (216 : F) ≠ 0 := by norm_num
  have hid : (216 : F) * ((3 : F) * u1 - (5 : F) * p31) =
      (648 : F) * u1 - (1080 : F) * p31 := by ring
  have : (216 : F) * ((3 : F) * u1 - (5 : F) * p31) = 0 := by
    rw [hid, hT]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h216)

/-- The second, third, and fifth defects at the next order force
`9 q₅₂ = 10 a₄₁ p₃₁`. -/
theorem tenthFace_V_nextOrder610 (a41 s1 p31 u1 q52 : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (648 : F) * u1 - (1080 : F) * p31 = 0)
    (hV : (285120 : F) * a41 * p31 - (108864 : F) * a41 * u1 -
        (124416 : F) * p31 * s1 + (93312 : F) * q52 = 0) :
    (9 : F) * q52 = (10 : F) * a41 * p31 := by
  have h10368 : (10368 : F) ≠ 0 := by norm_num
  have hid :
      (10368 : F) * ((9 : F) * q52 - (10 : F) * a41 * p31) =
        (285120 : F) * a41 * p31 - (108864 : F) * a41 * u1 -
          (124416 : F) * p31 * s1 + (93312 : F) * q52 +
        (6912 : F) * p31 *
          ((18 : F) * s1 - (30 : F) * a41) +
        (168 : F) * a41 *
          ((648 : F) * u1 - (1080 : F) * p31) := by
    ring
  have hcomb :
      (10368 : F) * ((9 : F) * q52 - (10 : F) * a41 * p31) = 0 := by
    rw [hid]
    linear_combination hV + (6912 : F) * p31 * hM +
      (168 : F) * a41 * hT
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomb).resolve_left h10368)

/-- The second, third, and sixth defects at the next order force
`9 q₄ = 5 p₃₁²`. -/
theorem tenthFace_W_nextOrder610 (p31 u1 q4 : F)
    (hT : (648 : F) * u1 - (1080 : F) * p31 = 0)
    (hW : (583200 : F) * p31 ^ 2 - (489888 : F) * p31 * u1 +
        (419904 : F) * q4 = 0) :
    (9 : F) * q4 = (5 : F) * p31 ^ 2 := by
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have hid :
      (46656 : F) * ((9 : F) * q4 - (5 : F) * p31 ^ 2) =
        (583200 : F) * p31 ^ 2 - (489888 : F) * p31 * u1 +
          (419904 : F) * q4 +
        (756 : F) * p31 *
          ((648 : F) * u1 - (1080 : F) * p31) := by
    ring
  have hcomb :
      (46656 : F) * ((9 : F) * q4 - (5 : F) * p31 ^ 2) = 0 := by
    rw [hid]
    linear_combination hW + (756 : F) * p31 * hT
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomb).resolve_left h46656)

/-- The second through fourth defects at the next order force the
source-facing load among `a₄₁`, `b₆₂`, `p₂`, `p₃₁`, `w₁`, and `λ`. -/
theorem tenthFace_U_nextOrder610 (w1 a41 s1 p31 u1 b62 p2 lambda : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (648 : F) * u1 - (1080 : F) * p31 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 + (216 : F) * lambda * p31 - (720 : F) * p2 +
        (360 : F) * p31 * w1 - (504 : F) * u1 * w1 = 0) :
    (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lambda * p31 +
      (30 : F) * p2 + (20 : F) * p31 * w1 = 0 := by
  have h216 : (216 : F) ≠ 0 := by norm_num
  have hid :
      -(216 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 -
          (9 : F) * lambda * p31 + (30 : F) * p2 +
          (20 : F) * p31 * w1) =
        (9 : F) *
            ((720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
              (432 : F) * b62 + (216 : F) * lambda * p31 -
              (720 : F) * p2 + (360 : F) * p31 * w1 -
              (504 : F) * u1 * w1 +
            (32 : F) * a41 *
              ((18 : F) * s1 - (30 : F) * a41)) +
          (7 : F) * w1 *
            ((648 : F) * u1 - (1080 : F) * p31) := by
    ring
  have hcomb :
      -(216 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 -
          (9 : F) * lambda * p31 + (30 : F) * p2 +
          (20 : F) * p31 * w1) = 0 := by
    rw [hid]
    linear_combination (9 : F) * hU + (9 : F) * (32 : F) * a41 * hM +
      (7 : F) * w1 * hT
  have : (216 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 -
      (9 : F) * lambda * p31 + (30 : F) * p2 +
      (20 : F) * p31 * w1) = 0 := by
    linear_combination -hcomb
  exact (mul_eq_zero.mp this).resolve_left h216

set_option maxHeartbeats 4000000 in
/-- After the second through sixth identities, the seventh defect forces
the alternative `p₃₁ (240 p₂ - 40 a₄₁² - 27 λ p₃₁ - 40 p₃₁ w₁) = 0`. -/
theorem tenthFace_X_nextOrder610 (w1 a41 s1 p31 u1 b62 q52 p2 q4
    lambda : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (648 : F) * u1 - (1080 : F) * p31 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 + (216 : F) * lambda * p31 - (720 : F) * p2 +
        (360 : F) * p31 * w1 - (504 : F) * u1 * w1 = 0)
    (hV : (285120 : F) * a41 * p31 - (108864 : F) * a41 * u1 -
        (124416 : F) * p31 * s1 + (93312 : F) * q52 = 0)
    (hW : (583200 : F) * p31 ^ 2 - (489888 : F) * p31 * u1 +
        (419904 : F) * q4 = 0)
    (hX : -(9600 : F) * a41 ^ 2 * p31 + (2688 : F) * a41 ^ 2 * u1 +
        (6144 : F) * a41 * p31 * s1 - (2560 : F) * a41 * q52 -
        (3072 : F) * b62 * p31 - (1152 : F) * lambda * p31 ^ 2 +
        (7680 : F) * p2 * p31 - (3584 : F) * p2 * u1 -
        (3840 : F) * p31 ^ 2 * w1 + (5376 : F) * p31 * u1 * w1 -
        (2048 : F) * q4 * w1 = 0) :
    p31 * ((240 : F) * p2 - (40 : F) * a41 ^ 2 -
      (27 : F) * lambda * p31 - (40 : F) * p31 * w1) = 0 := by
  have hs := tenthFace_M_nextOrder610 a41 s1 hM
  have hu := tenthFace_T_nextOrder610 p31 u1 hT
  have hq5 := tenthFace_V_nextOrder610 a41 s1 p31 u1 q52 hM hT hV
  have hq4 := tenthFace_W_nextOrder610 p31 u1 q4 hT hW
  have hUform :=
    tenthFace_U_nextOrder610 w1 a41 s1 p31 u1 b62 p2 lambda hM hT hU
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have hs1 : s1 = (5 / 3 : F) * a41 := by
    have hid : (3 : F) * (s1 - (5 / 3 : F) * a41) =
        (3 : F) * s1 - (5 : F) * a41 := by ring
    have : (3 : F) * (s1 - (5 / 3 : F) * a41) = 0 := by
      rw [hid]
      linear_combination hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)
  have hu1 : u1 = (5 / 3 : F) * p31 := by
    have hid : (3 : F) * (u1 - (5 / 3 : F) * p31) =
        (3 : F) * u1 - (5 : F) * p31 := by ring
    have : (3 : F) * (u1 - (5 / 3 : F) * p31) = 0 := by
      rw [hid]
      linear_combination hu
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)
  have hq52 : q52 = (10 / 9 : F) * a41 * p31 := by
    have hid : (9 : F) * (q52 - (10 / 9 : F) * a41 * p31) =
        (9 : F) * q52 - (10 : F) * a41 * p31 := by ring
    have : (9 : F) * (q52 - (10 / 9 : F) * a41 * p31) = 0 := by
      rw [hid]
      linear_combination hq5
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h9)
  have hq4' : q4 = (5 / 9 : F) * p31 ^ 2 := by
    have hid : (9 : F) * (q4 - (5 / 9 : F) * p31 ^ 2) =
        (9 : F) * q4 - (5 : F) * p31 ^ 2 := by ring
    have : (9 : F) * (q4 - (5 / 9 : F) * p31 ^ 2) = 0 := by
      rw [hid]
      linear_combination hq4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h9)
  have hX2 :
      -(9600 : F) * a41 ^ 2 * p31 + (2688 : F) * a41 ^ 2 * u1 +
          (6144 : F) * a41 * p31 * s1 - (2560 : F) * a41 * q52 -
          (3072 : F) * b62 * p31 - (1152 : F) * lambda * p31 ^ 2 +
          (7680 : F) * p2 * p31 - (3584 : F) * p2 * u1 -
          (3840 : F) * p31 ^ 2 * w1 + (5376 : F) * p31 * u1 * w1 -
          (2048 : F) * q4 * w1 =
        (128 / 9 : F) * p31 *
          ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
            (81 : F) * lambda * p31 + (120 : F) * p2 +
            (280 : F) * p31 * w1) := by
    simp only [hs1, hu1, hq52, hq4']
    ring
  have hXform :
      p31 * ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
        (81 : F) * lambda * p31 + (120 : F) * p2 +
        (280 : F) * p31 * w1) = 0 := by
    have h128 : (128 : F) ≠ 0 := by norm_num
    have : (128 / 9 : F) * p31 *
          ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
            (81 : F) * lambda * p31 + (120 : F) * p2 +
            (280 : F) * p31 * w1) = 0 := by
      rw [← hX2, hX]
    have hid :
        (128 : F) * (p31 *
            ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
              (81 : F) * lambda * p31 + (120 : F) * p2 +
              (280 : F) * p31 * w1)) =
          (9 : F) * ((128 / 9 : F) * p31 *
            ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
              (81 : F) * lambda * p31 + (120 : F) * p2 +
              (280 : F) * p31 * w1)) := by
      ring
    have hscale :
        (128 : F) * (p31 *
            ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
              (81 : F) * lambda * p31 + (120 : F) * p2 +
              (280 : F) * p31 * w1)) = 0 := by
      rw [hid]
      linear_combination (9 : F) * this
    exact (mul_eq_zero.mp hscale).resolve_left h128
  have hid :
      p31 * ((240 : F) * p2 - (40 : F) * a41 ^ 2 -
          (27 : F) * lambda * p31 - (40 : F) * p31 * w1) =
        (12 : F) * p31 *
            ((10 : F) * a41 ^ 2 - (18 : F) * b62 -
              (9 : F) * lambda * p31 + (30 : F) * p2 +
              (20 : F) * p31 * w1) -
          (p31 * ((160 : F) * a41 ^ 2 - (216 : F) * b62 -
            (81 : F) * lambda * p31 + (120 : F) * p2 +
            (280 : F) * p31 * w1)) := by
    ring
  rw [hid, hUform, hXform]
  ring

/-- Combined next-order identities of the collapsed ninth-face jet. -/
theorem tenthFace_collapsedNextOrder610 (w1 a41 s1 p31 u1 b62 q52 p2 q4
    lambda : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (648 : F) * u1 - (1080 : F) * p31 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 + (216 : F) * lambda * p31 - (720 : F) * p2 +
        (360 : F) * p31 * w1 - (504 : F) * u1 * w1 = 0)
    (hV : (285120 : F) * a41 * p31 - (108864 : F) * a41 * u1 -
        (124416 : F) * p31 * s1 + (93312 : F) * q52 = 0)
    (hW : (583200 : F) * p31 ^ 2 - (489888 : F) * p31 * u1 +
        (419904 : F) * q4 = 0)
    (hX : -(9600 : F) * a41 ^ 2 * p31 + (2688 : F) * a41 ^ 2 * u1 +
        (6144 : F) * a41 * p31 * s1 - (2560 : F) * a41 * q52 -
        (3072 : F) * b62 * p31 - (1152 : F) * lambda * p31 ^ 2 +
        (7680 : F) * p2 * p31 - (3584 : F) * p2 * u1 -
        (3840 : F) * p31 ^ 2 * w1 + (5376 : F) * p31 * u1 * w1 -
        (2048 : F) * q4 * w1 = 0) :
    (3 : F) * s1 = (5 : F) * a41 ∧ (3 : F) * u1 = (5 : F) * p31 ∧
      (9 : F) * q52 = (10 : F) * a41 * p31 ∧
      (9 : F) * q4 = (5 : F) * p31 ^ 2 ∧
      (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lambda * p31 +
        (30 : F) * p2 + (20 : F) * p31 * w1 = 0 ∧
      p31 * ((240 : F) * p2 - (40 : F) * a41 ^ 2 -
        (27 : F) * lambda * p31 - (40 : F) * p31 * w1) = 0 :=
  ⟨tenthFace_M_nextOrder610 a41 s1 hM,
    tenthFace_T_nextOrder610 p31 u1 hT,
    tenthFace_V_nextOrder610 a41 s1 p31 u1 q52 hM hT hV,
    tenthFace_W_nextOrder610 p31 u1 q4 hT hW,
    tenthFace_U_nextOrder610 w1 a41 s1 p31 u1 b62 p2 lambda hM hT hU,
    tenthFace_X_nextOrder610 w1 a41 s1 p31 u1 b62 q52 p2 q4 lambda
      hM hT hU hV hW hX⟩

/-! ## Collapsed substitutions of the cleared defects -/

theorem tenthFace_clearedM_collapsed610 (h w1 a41 s1 : F[X])
    (lambda : F) :
    localClearedSecondDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 7 * s1) lambda =
      h ^ 9 * ((18 : F[X]) * s1 - (30 : F[X]) * a41 +
        (9 : F[X]) * Polynomial.C lambda * w1 * h -
        (10 : F[X]) * h * w1 ^ 2) := by
  simp only [localClearedSecondDefect610]
  ring

theorem tenthFace_clearedT_collapsed610 (h w1 a41 s1 u1 p31 : F[X])
    (lambda : F) :
    localClearedThirdDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        (h ^ 7 * s1) (h ^ 5 * u1) lambda =
      h ^ 13 * ((648 : F[X]) * u1 - (1080 : F[X]) * p31 +
        (324 : F[X]) * a41 * h * Polynomial.C lambda +
        (720 : F[X]) * a41 * h * w1 -
        (864 : F[X]) * h * s1 * w1 -
        (351 : F[X]) * Polynomial.C lambda * h ^ 2 * w1 ^ 2 +
        (520 : F[X]) * h ^ 2 * w1 ^ 3) := by
  simp only [localClearedThirdDefect610]
  ring

set_option maxHeartbeats 4000000 in
theorem tenthFace_clearedU_collapsed610 (h w1 a41 s1 u1 p31 b62 p2 :
    F[X]) (lambda : F) :
    localClearedFourthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) lambda =
      h ^ 18 * ((720 : F[X]) * a41 ^ 2 - (576 : F[X]) * a41 * s1 +
        (432 : F[X]) * b62 + (216 : F[X]) * Polynomial.C lambda * p31 -
        (720 : F[X]) * p2 + (360 : F[X]) * p31 * w1 -
        (504 : F[X]) * u1 * w1 -
        (432 : F[X]) * a41 * h * Polynomial.C lambda * w1 +
        (576 : F[X]) * h * s1 * w1 ^ 2 +
        (216 : F[X]) * h ^ 2 * Polynomial.C lambda * w1 ^ 3 -
        (360 : F[X]) * h ^ 2 * w1 ^ 4) := by
  simp only [localClearedFourthDefect610]
  ring

set_option maxHeartbeats 8000000 in
theorem tenthFace_clearedV_collapsed610 (h w1 a41 s1 u1 p31 b62 q52 p2
    p1 : F[X]) (lambda : F) :
    localClearedFifthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        lambda =
      h ^ 22 * ((285120 : F[X]) * a41 * p31 -
        (108864 : F[X]) * a41 * u1 - (124416 : F[X]) * p31 * s1 +
        (93312 : F[X]) * q52 -
        (42768 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda -
        (190080 : F[X]) * a41 ^ 2 * h * w1 +
        (228096 : F[X]) * a41 * h * s1 * w1 -
        (93312 : F[X]) * b62 * h * w1 +
        (121176 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 2 -
        (89760 : F[X]) * a41 * h ^ 2 * w1 ^ 3 -
        (155520 : F[X]) * h ^ 2 * p1 -
        (107712 : F[X]) * h ^ 2 * s1 * w1 ^ 3 +
        (46656 : F[X]) * h * Polynomial.C lambda * p2 -
        (85536 : F[X]) * h * Polynomial.C lambda * p31 * w1 +
        (51840 : F[X]) * h * p2 * w1 +
        (23760 : F[X]) * h * p31 * w1 ^ 2 +
        (99792 : F[X]) * h * u1 * w1 ^ 2 -
        (38709 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 4 +
        (68816 : F[X]) * h ^ 3 * w1 ^ 5) := by
  simp only [localClearedFifthDefect610]
  ring

set_option maxHeartbeats 12000000 in
theorem tenthFace_clearedW_collapsed610 (h w1 a41 s1 u1 p31 b62 q52 p2
    p1 p0 q4 : F[X]) (lambda : F) :
    localClearedSixthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        q4 lambda =
      h ^ 26 * ((583200 : F[X]) * p31 ^ 2 -
        (489888 : F[X]) * p31 * u1 + (419904 : F[X]) * q4 -
        (518400 : F[X]) * a41 ^ 3 * h +
        (466560 : F[X]) * a41 ^ 2 * h * s1 -
        (419904 : F[X]) * a41 * b62 * h -
        (349920 : F[X]) * a41 * h * Polynomial.C lambda * p31 +
        (1166400 : F[X]) * a41 * h * p2 -
        (1360800 : F[X]) * a41 * h * p31 * w1 +
        (816480 : F[X]) * a41 * h * u1 * w1 -
        (559872 : F[X]) * h * p2 * s1 +
        (933120 : F[X]) * h * p31 * s1 * w1 -
        (349920 : F[X]) * h * q52 * w1 +
        (466560 : F[X]) * a41 ^ 2 * h ^ 2 * Polynomial.C lambda * w1 +
        (518400 : F[X]) * a41 ^ 2 * h ^ 2 * w1 ^ 2 -
        (1244160 : F[X]) * a41 * h ^ 2 * s1 * w1 ^ 2 +
        (349920 : F[X]) * b62 * h ^ 2 * w1 ^ 2 -
        (349920 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 * w1 +
        (466560 : F[X]) * h ^ 2 * Polynomial.C lambda * p31 * w1 ^ 2 +
        (194400 : F[X]) * h ^ 2 * p2 * w1 ^ 2 -
        (432000 : F[X]) * h ^ 2 * p31 * w1 ^ 3 -
        (362880 : F[X]) * h ^ 2 * u1 * w1 ^ 3 -
        (570240 : F[X]) * a41 * h ^ 3 * Polynomial.C lambda * w1 ^ 3 +
        (633600 : F[X]) * a41 * h ^ 3 * w1 ^ 4 +
        (209952 : F[X]) * h ^ 3 * Polynomial.C lambda * p1 +
        (116640 : F[X]) * h ^ 3 * p1 * w1 +
        (380160 : F[X]) * h ^ 3 * s1 * w1 ^ 4 +
        (133056 : F[X]) * h ^ 4 * Polynomial.C lambda * w1 ^ 5 -
        (699840 : F[X]) * h ^ 4 * p0 -
        (246400 : F[X]) * h ^ 4 * w1 ^ 6) := by
  simp only [localClearedSixthDefect610]
  ring

set_option maxHeartbeats 16000000 in
theorem tenthFace_clearedX_collapsed610 (h w1 a41 s1 u1 p31 b62 q52 p2
    p1 p0 q4 q3 : F[X]) (lambda : F) :
    localClearedSeventhDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        q4 q3 lambda =
      h ^ 31 * (-(9600 : F[X]) * a41 ^ 2 * p31 +
        (2688 : F[X]) * a41 ^ 2 * u1 +
        (6144 : F[X]) * a41 * p31 * s1 - (2560 : F[X]) * a41 * q52 -
        (3072 : F[X]) * b62 * p31 -
        (1152 : F[X]) * Polynomial.C lambda * p31 ^ 2 +
        (7680 : F[X]) * p2 * p31 - (3584 : F[X]) * p2 * u1 -
        (3840 : F[X]) * p31 ^ 2 * w1 +
        (5376 : F[X]) * p31 * u1 * w1 - (2048 : F[X]) * q4 * w1 +
        (960 : F[X]) * a41 ^ 3 * h * Polynomial.C lambda +
        (6400 : F[X]) * a41 ^ 3 * h * w1 -
        (7680 : F[X]) * a41 ^ 2 * h * s1 * w1 +
        (4608 : F[X]) * a41 * b62 * h * w1 -
        (2304 : F[X]) * a41 * h * Polynomial.C lambda * p2 +
        (5760 : F[X]) * a41 * h * Polynomial.C lambda * p31 * w1 -
        (7680 : F[X]) * a41 * h * p2 * w1 +
        (4800 : F[X]) * a41 * h * p31 * w1 ^ 2 -
        (6720 : F[X]) * a41 * h * u1 * w1 ^ 2 +
        (6144 : F[X]) * h * p2 * s1 * w1 -
        (7680 : F[X]) * h * p31 * s1 * w1 ^ 2 +
        (3072 : F[X]) * h * q3 +
        (1920 : F[X]) * h * q52 * w1 ^ 2 -
        (5040 : F[X]) * a41 ^ 2 * h ^ 2 * Polynomial.C lambda * w1 ^ 2 +
        (7680 : F[X]) * a41 * h ^ 2 * p1 +
        (8960 : F[X]) * a41 * h ^ 2 * s1 * w1 ^ 3 -
        (1920 : F[X]) * b62 * h ^ 2 * w1 ^ 3 +
        (2880 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 * w1 ^ 2 -
        (3360 : F[X]) * h ^ 2 * Polynomial.C lambda * p31 * w1 ^ 3 -
        (4096 : F[X]) * h ^ 2 * p1 * s1 -
        (3200 : F[X]) * h ^ 2 * p2 * w1 ^ 3 +
        (4200 : F[X]) * h ^ 2 * p31 * w1 ^ 4 +
        (1960 : F[X]) * h ^ 2 * u1 * w1 ^ 4 +
        (3780 : F[X]) * a41 * h ^ 3 * Polynomial.C lambda * w1 ^ 4 -
        (5040 : F[X]) * a41 * h ^ 3 * w1 ^ 5 -
        (2304 : F[X]) * h ^ 3 * Polynomial.C lambda * p1 * w1 +
        (1920 : F[X]) * h ^ 3 * p1 * w1 ^ 2 -
        (2016 : F[X]) * h ^ 3 * s1 * w1 ^ 5 +
        (1536 : F[X]) * h ^ 4 * Polynomial.C lambda * p0 -
        (693 : F[X]) * h ^ 4 * Polynomial.C lambda * w1 ^ 6 +
        (1320 : F[X]) * h ^ 4 * w1 ^ 7) := by
  simp only [localClearedSeventhDefect610]
  ring

theorem eval_tenthFace_M_cofactor610 (h w1 a41 s1 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((18 : F[X]) * s1 - (30 : F[X]) * a41 +
          (9 : F[X]) * Polynomial.C lambda * w1 * h -
          (10 : F[X]) * h * w1 ^ 2) =
      (18 : F) * Polynomial.eval root s1 -
        (30 : F) * Polynomial.eval root a41 := by
  simp [hroot]

theorem eval_tenthFace_T_cofactor610 (h w1 a41 s1 u1 p31 : F[X])
    (lambda : F) (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((648 : F[X]) * u1 - (1080 : F[X]) * p31 +
          (324 : F[X]) * a41 * h * Polynomial.C lambda +
          (720 : F[X]) * a41 * h * w1 -
          (864 : F[X]) * h * s1 * w1 -
          (351 : F[X]) * Polynomial.C lambda * h ^ 2 * w1 ^ 2 +
          (520 : F[X]) * h ^ 2 * w1 ^ 3) =
      (648 : F) * Polynomial.eval root u1 -
        (1080 : F) * Polynomial.eval root p31 := by
  simp [hroot]

theorem eval_tenthFace_U_cofactor610 (h w1 a41 s1 u1 p31 b62 p2 : F[X])
    (lambda : F) (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((720 : F[X]) * a41 ^ 2 - (576 : F[X]) * a41 * s1 +
          (432 : F[X]) * b62 + (216 : F[X]) * Polynomial.C lambda * p31 -
          (720 : F[X]) * p2 + (360 : F[X]) * p31 * w1 -
          (504 : F[X]) * u1 * w1 -
          (432 : F[X]) * a41 * h * Polynomial.C lambda * w1 +
          (576 : F[X]) * h * s1 * w1 ^ 2 +
          (216 : F[X]) * h ^ 2 * Polynomial.C lambda * w1 ^ 3 -
          (360 : F[X]) * h ^ 2 * w1 ^ 4) =
      (720 : F) * (Polynomial.eval root a41) ^ 2 -
        (576 : F) * Polynomial.eval root a41 * Polynomial.eval root s1 +
        (432 : F) * Polynomial.eval root b62 +
        (216 : F) * lambda * Polynomial.eval root p31 -
        (720 : F) * Polynomial.eval root p2 +
        (360 : F) * Polynomial.eval root p31 * Polynomial.eval root w1 -
        (504 : F) * Polynomial.eval root u1 *
          Polynomial.eval root w1 := by
  simp [hroot]

theorem eval_tenthFace_V_cofactor610 (h w1 a41 s1 u1 p31 b62 q52 p2 p1 :
    F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((285120 : F[X]) * a41 * p31 -
          (108864 : F[X]) * a41 * u1 - (124416 : F[X]) * p31 * s1 +
          (93312 : F[X]) * q52 -
          (42768 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda -
          (190080 : F[X]) * a41 ^ 2 * h * w1 +
          (228096 : F[X]) * a41 * h * s1 * w1 -
          (93312 : F[X]) * b62 * h * w1 +
          (121176 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 2 -
          (89760 : F[X]) * a41 * h ^ 2 * w1 ^ 3 -
          (155520 : F[X]) * h ^ 2 * p1 -
          (107712 : F[X]) * h ^ 2 * s1 * w1 ^ 3 +
          (46656 : F[X]) * h * Polynomial.C lambda * p2 -
          (85536 : F[X]) * h * Polynomial.C lambda * p31 * w1 +
          (51840 : F[X]) * h * p2 * w1 +
          (23760 : F[X]) * h * p31 * w1 ^ 2 +
          (99792 : F[X]) * h * u1 * w1 ^ 2 -
          (38709 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 4 +
          (68816 : F[X]) * h ^ 3 * w1 ^ 5) =
      (285120 : F) * Polynomial.eval root a41 *
          Polynomial.eval root p31 -
        (108864 : F) * Polynomial.eval root a41 *
          Polynomial.eval root u1 -
        (124416 : F) * Polynomial.eval root p31 *
          Polynomial.eval root s1 +
        (93312 : F) * Polynomial.eval root q52 := by
  simp [hroot]

theorem eval_tenthFace_W_cofactor610 (h w1 a41 s1 u1 p31 b62 q52 p2 p1
    p0 q4 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((583200 : F[X]) * p31 ^ 2 -
          (489888 : F[X]) * p31 * u1 + (419904 : F[X]) * q4 -
          (518400 : F[X]) * a41 ^ 3 * h +
          (466560 : F[X]) * a41 ^ 2 * h * s1 -
          (419904 : F[X]) * a41 * b62 * h -
          (349920 : F[X]) * a41 * h * Polynomial.C lambda * p31 +
          (1166400 : F[X]) * a41 * h * p2 -
          (1360800 : F[X]) * a41 * h * p31 * w1 +
          (816480 : F[X]) * a41 * h * u1 * w1 -
          (559872 : F[X]) * h * p2 * s1 +
          (933120 : F[X]) * h * p31 * s1 * w1 -
          (349920 : F[X]) * h * q52 * w1 +
          (466560 : F[X]) * a41 ^ 2 * h ^ 2 * Polynomial.C lambda * w1 +
          (518400 : F[X]) * a41 ^ 2 * h ^ 2 * w1 ^ 2 -
          (1244160 : F[X]) * a41 * h ^ 2 * s1 * w1 ^ 2 +
          (349920 : F[X]) * b62 * h ^ 2 * w1 ^ 2 -
          (349920 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 * w1 +
          (466560 : F[X]) * h ^ 2 * Polynomial.C lambda * p31 * w1 ^ 2 +
          (194400 : F[X]) * h ^ 2 * p2 * w1 ^ 2 -
          (432000 : F[X]) * h ^ 2 * p31 * w1 ^ 3 -
          (362880 : F[X]) * h ^ 2 * u1 * w1 ^ 3 -
          (570240 : F[X]) * a41 * h ^ 3 * Polynomial.C lambda * w1 ^ 3 +
          (633600 : F[X]) * a41 * h ^ 3 * w1 ^ 4 +
          (209952 : F[X]) * h ^ 3 * Polynomial.C lambda * p1 +
          (116640 : F[X]) * h ^ 3 * p1 * w1 +
          (380160 : F[X]) * h ^ 3 * s1 * w1 ^ 4 +
          (133056 : F[X]) * h ^ 4 * Polynomial.C lambda * w1 ^ 5 -
          (699840 : F[X]) * h ^ 4 * p0 -
          (246400 : F[X]) * h ^ 4 * w1 ^ 6) =
      (583200 : F) * (Polynomial.eval root p31) ^ 2 -
        (489888 : F) * Polynomial.eval root p31 *
          Polynomial.eval root u1 +
        (419904 : F) * Polynomial.eval root q4 := by
  simp [hroot]

theorem eval_tenthFace_X_cofactor610 (h w1 a41 s1 u1 p31 b62 q52 p2 p1
    p0 q4 q3 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (-(9600 : F[X]) * a41 ^ 2 * p31 +
          (2688 : F[X]) * a41 ^ 2 * u1 +
          (6144 : F[X]) * a41 * p31 * s1 - (2560 : F[X]) * a41 * q52 -
          (3072 : F[X]) * b62 * p31 -
          (1152 : F[X]) * Polynomial.C lambda * p31 ^ 2 +
          (7680 : F[X]) * p2 * p31 - (3584 : F[X]) * p2 * u1 -
          (3840 : F[X]) * p31 ^ 2 * w1 +
          (5376 : F[X]) * p31 * u1 * w1 - (2048 : F[X]) * q4 * w1 +
          (960 : F[X]) * a41 ^ 3 * h * Polynomial.C lambda +
          (6400 : F[X]) * a41 ^ 3 * h * w1 -
          (7680 : F[X]) * a41 ^ 2 * h * s1 * w1 +
          (4608 : F[X]) * a41 * b62 * h * w1 -
          (2304 : F[X]) * a41 * h * Polynomial.C lambda * p2 +
          (5760 : F[X]) * a41 * h * Polynomial.C lambda * p31 * w1 -
          (7680 : F[X]) * a41 * h * p2 * w1 +
          (4800 : F[X]) * a41 * h * p31 * w1 ^ 2 -
          (6720 : F[X]) * a41 * h * u1 * w1 ^ 2 +
          (6144 : F[X]) * h * p2 * s1 * w1 -
          (7680 : F[X]) * h * p31 * s1 * w1 ^ 2 +
          (3072 : F[X]) * h * q3 +
          (1920 : F[X]) * h * q52 * w1 ^ 2 -
          (5040 : F[X]) * a41 ^ 2 * h ^ 2 * Polynomial.C lambda *
            w1 ^ 2 +
          (7680 : F[X]) * a41 * h ^ 2 * p1 +
          (8960 : F[X]) * a41 * h ^ 2 * s1 * w1 ^ 3 -
          (1920 : F[X]) * b62 * h ^ 2 * w1 ^ 3 +
          (2880 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 * w1 ^ 2 -
          (3360 : F[X]) * h ^ 2 * Polynomial.C lambda * p31 * w1 ^ 3 -
          (4096 : F[X]) * h ^ 2 * p1 * s1 -
          (3200 : F[X]) * h ^ 2 * p2 * w1 ^ 3 +
          (4200 : F[X]) * h ^ 2 * p31 * w1 ^ 4 +
          (1960 : F[X]) * h ^ 2 * u1 * w1 ^ 4 +
          (3780 : F[X]) * a41 * h ^ 3 * Polynomial.C lambda * w1 ^ 4 -
          (5040 : F[X]) * a41 * h ^ 3 * w1 ^ 5 -
          (2304 : F[X]) * h ^ 3 * Polynomial.C lambda * p1 * w1 +
          (1920 : F[X]) * h ^ 3 * p1 * w1 ^ 2 -
          (2016 : F[X]) * h ^ 3 * s1 * w1 ^ 5 +
          (1536 : F[X]) * h ^ 4 * Polynomial.C lambda * p0 -
          (693 : F[X]) * h ^ 4 * Polynomial.C lambda * w1 ^ 6 +
          (1320 : F[X]) * h ^ 4 * w1 ^ 7) =
      -(9600 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root p31 +
        (2688 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root u1 +
        (6144 : F) * Polynomial.eval root a41 *
          Polynomial.eval root p31 * Polynomial.eval root s1 -
        (2560 : F) * Polynomial.eval root a41 *
          Polynomial.eval root q52 -
        (3072 : F) * Polynomial.eval root b62 *
          Polynomial.eval root p31 -
        (1152 : F) * lambda * (Polynomial.eval root p31) ^ 2 +
        (7680 : F) * Polynomial.eval root p2 *
          Polynomial.eval root p31 -
        (3584 : F) * Polynomial.eval root p2 *
          Polynomial.eval root u1 -
        (3840 : F) * (Polynomial.eval root p31) ^ 2 *
          Polynomial.eval root w1 +
        (5376 : F) * Polynomial.eval root p31 *
          Polynomial.eval root u1 * Polynomial.eval root w1 -
        (2048 : F) * Polynomial.eval root q4 *
          Polynomial.eval root w1 := by
  simp [hroot]

end TenthFaceScalars610

/-! ## Source-facing tenth-face packet -/

section NonzeroTenthFace610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
/-- Finite local tenth-face packet: the collapsed ninth-face jet together
with the next-order identities of the second through seventh defects. -/
theorem nonzeroFace610_linearRoot_tenthPowerJet
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (3 : k) * u1.eval a = (5 : k) * p31.eval a ∧
        (9 : k) * q52.eval a =
          (10 : k) * a41.eval a * p31.eval a ∧
        (9 : k) * (q.coeff 4).eval a = (5 : k) * (p31.eval a) ^ 2 ∧
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a -
            (9 : k) * lambda * p31.eval a +
          (30 : k) * (p.coeff 2).eval a +
            (20 : k) * p31.eval a * w1.eval a = 0 ∧
        p31.eval a *
            ((240 : k) * (p.coeff 2).eval a -
              (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
              (40 : k) * p31.eval a * w1.eval a) = 0 := by
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
  obtain ⟨w, a4s, s, u, b6s, A1, S1, P31, U1, B61, Q51, hw, ha4s, hs, hu,
    hb6s, hA1, hS1, hP31, hU1, hB61, hQ51, hlamw, hMeval, hTeval, hUeval,
    hVeval, hWeval⟩ :=
    nonzeroFace610_linearRoot_ninthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot
  have hwz : w.eval a = 0 := by
    have : (w.eval a) ^ 5 = 0 :=
      (mul_eq_zero.mp hlamw).resolve_left hlambda
    exact eq_zero_of_pow_eq_zero this
  have ha4z : a4s.eval a = 0 := by
    have : ((3 : k[X]) * a4s - w ^ 2).eval a = 0 := by
      rw [hA1]
      simp [hroot]
    simpa [hwz, map_sub, map_mul, map_pow] using this
  have hsz : s.eval a = 0 := by
    have : ((9 : k[X]) * s - (10 : k[X]) * w ^ 2).eval a = 0 := by
      rw [hS1]
      simp [hroot]
    simpa [hwz, map_sub, map_mul, map_pow] using this
  have hp3z : (p.coeff 3).eval a = 0 := by
    have : ((27 : k[X]) * p.coeff 3 - w ^ 3).eval a = 0 := by
      rw [hP31]
      simp [hroot]
    simpa [hwz, map_sub, map_mul, map_pow] using this
  have huz : u.eval a = 0 := by
    have : ((27 : k[X]) * u - (10 : k[X]) * w ^ 3).eval a = 0 := by
      rw [hU1]
      simp [hroot]
    simpa [hwz, map_sub, map_mul, map_pow] using this
  have hb6z : b6s.eval a = 0 := by
    have : ((81 : k[X]) * b6s - (5 : k[X]) * w ^ 4).eval a = 0 := by
      rw [hB61]
      simp [hroot]
    simpa [hwz, map_sub, map_mul, map_pow] using this
  have hq5z : (q.coeff 5).eval a = 0 := by
    have : ((243 : k[X]) * q.coeff 5 - w ^ 5).eval a = 0 := by
      rw [hQ51]
      simp [hroot]
    simpa [hwz, map_sub, map_mul, map_pow] using this
  have hM0 : (2 : k) * S1.eval a - (10 : k) * A1.eval a = 0 := by
    simpa [hwz] using hMeval
  have hT0 : -(40 : k) * P31.eval a + (24 : k) * U1.eval a = 0 := by
    simpa [hwz] using hTeval
  have hU0 : (16 : k) * B61.eval a = 0 := by
    simpa [hwz] using hUeval
  have hV0 : (384 : k) * Q51.eval a = 0 := by
    simpa [hwz] using hVeval
  obtain ⟨_hSrel, _hPrel, hBrel, hQrel⟩ :=
    ninthFace_zeroW_nextOrder610 (A1.eval a) (S1.eval a) (P31.eval a)
      (U1.eval a) (B61.eval a) (Q51.eval a) hM0 hT0 hU0 hV0
  obtain ⟨w1, hw1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 w a hh0degree hroot hwz
  obtain ⟨a41, ha41⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 a4s a hh0degree hroot
      ha4z
  obtain ⟨s1, hs1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hsz
  obtain ⟨p31, hp31⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 3) a hh0degree
      hroot hp3z
  obtain ⟨u1, hu1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u a hh0degree hroot huz
  obtain ⟨b61', hb61'⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 b6s a hh0degree hroot
      hb6z
  have hcancelB :
      (81 : k[X]) * b61' - (5 : k[X]) * h0 ^ 3 * w1 ^ 4 = B61 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * ((81 : k[X]) * b61' - (5 : k[X]) * h0 ^ 3 * w1 ^ 4) =
          (81 : k[X]) * (h0 * b61') - (5 : k[X]) * (h0 * w1) ^ 4 := by
        ring
      _ = (81 : k[X]) * b6s - (5 : k[X]) * w ^ 4 := by
        rw [← hb61', ← hw1]
      _ = h0 * B61 := hB61
  have hb61z' : b61'.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hcancelB
    have h81 : (81 : k) ≠ 0 := by norm_num
    have : (81 : k) * b61'.eval a = 0 := by
      simpa [hroot, hBrel, map_sub, map_mul, map_pow] using heval
    exact (mul_eq_zero.mp this).resolve_left h81
  obtain ⟨b62, hb62⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 b61' a hh0degree hroot
      hb61z'
  obtain ⟨q51', hq51'⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 5) a hh0degree
      hroot hq5z
  have hcancelQ :
      (243 : k[X]) * q51' - h0 ^ 4 * w1 ^ 5 = Q51 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * ((243 : k[X]) * q51' - h0 ^ 4 * w1 ^ 5) =
          (243 : k[X]) * (h0 * q51') - (h0 * w1) ^ 5 := by
        ring
      _ = (243 : k[X]) * q.coeff 5 - w ^ 5 := by
        rw [← hq51', ← hw1]
      _ = h0 * Q51 := hQ51
  have hq51z : q51'.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hcancelQ
    have h243 : (243 : k) ≠ 0 := by norm_num
    have : (243 : k) * q51'.eval a = 0 := by
      simpa [hroot, hQrel, map_sub, map_mul, map_pow] using heval
    exact (mul_eq_zero.mp this).resolve_left h243
  obtain ⟨q52, hq52⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 q51' a hh0degree hroot
      hq51z
  have hp5 : p.coeff 5 = h0 ^ 5 * w1 := by
    rw [hw, hw1]
    ring
  have hp4 : p.coeff 4 = h0 ^ 3 * a41 := by
    rw [ha4s, ha41]
    ring
  have hp3 : p.coeff 3 = h0 * p31 := hp31
  have hq8 : q.coeff 8 = h0 ^ 7 * s1 := by
    rw [hs, hs1]
    ring
  have hq7 : q.coeff 7 = h0 ^ 5 * u1 := by
    rw [hu, hu1]
    ring
  have hq6 : q.coeff 6 = h0 ^ 4 * b62 := by
    rw [hb6s, hb61', hb62]
    ring
  have hq5 : q.coeff 5 = h0 ^ 2 * q52 := by
    rw [hq51', hq52]
    ring
  have hMclr :
      localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
          (q.coeff 8) lambda =
        h0 ^ 9 * ((18 : k[X]) * s1 - (30 : k[X]) * a41 +
          (9 : k[X]) * Polynomial.C lambda * w1 * h0 -
          (10 : k[X]) * h0 * w1 ^ 2) := by
    simpa [hp5, hp4, hq8] using
      tenthFace_clearedM_collapsed610 h0 w1 a41 s1 lambda
  have hTclr :
      localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda =
        h0 ^ 13 * ((648 : k[X]) * u1 - (1080 : k[X]) * p31 +
          (324 : k[X]) * a41 * h0 * Polynomial.C lambda +
          (720 : k[X]) * a41 * h0 * w1 -
          (864 : k[X]) * h0 * s1 * w1 -
          (351 : k[X]) * Polynomial.C lambda * h0 ^ 2 * w1 ^ 2 +
          (520 : k[X]) * h0 ^ 2 * w1 ^ 3) := by
    simpa [hp5, hp4, hp3, hq8, hq7] using
      tenthFace_clearedT_collapsed610 h0 w1 a41 s1 u1 p31 lambda
  have hUclr :
      localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) lambda =
        h0 ^ 18 * ((720 : k[X]) * a41 ^ 2 - (576 : k[X]) * a41 * s1 +
          (432 : k[X]) * b62 +
          (216 : k[X]) * Polynomial.C lambda * p31 -
          (720 : k[X]) * p.coeff 2 + (360 : k[X]) * p31 * w1 -
          (504 : k[X]) * u1 * w1 -
          (432 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 +
          (576 : k[X]) * h0 * s1 * w1 ^ 2 +
          (216 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 3 -
          (360 : k[X]) * h0 ^ 2 * w1 ^ 4) := by
    simpa [hp5, hp4, hp3, hq8, hq7, hq6] using
      tenthFace_clearedU_collapsed610 h0 w1 a41 s1 u1 p31 b62
        (p.coeff 2) lambda
  have hVclr :
      localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) lambda =
        h0 ^ 22 * ((285120 : k[X]) * a41 * p31 -
          (108864 : k[X]) * a41 * u1 - (124416 : k[X]) * p31 * s1 +
          (93312 : k[X]) * q52 -
          (42768 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda -
          (190080 : k[X]) * a41 ^ 2 * h0 * w1 +
          (228096 : k[X]) * a41 * h0 * s1 * w1 -
          (93312 : k[X]) * b62 * h0 * w1 +
          (121176 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
            w1 ^ 2 -
          (89760 : k[X]) * a41 * h0 ^ 2 * w1 ^ 3 -
          (155520 : k[X]) * h0 ^ 2 * p.coeff 1 -
          (107712 : k[X]) * h0 ^ 2 * s1 * w1 ^ 3 +
          (46656 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 -
          (85536 : k[X]) * h0 * Polynomial.C lambda * p31 * w1 +
          (51840 : k[X]) * h0 * p.coeff 2 * w1 +
          (23760 : k[X]) * h0 * p31 * w1 ^ 2 +
          (99792 : k[X]) * h0 * u1 * w1 ^ 2 -
          (38709 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 4 +
          (68816 : k[X]) * h0 ^ 3 * w1 ^ 5) := by
    simpa [hp5, hp4, hp3, hq8, hq7, hq6, hq5] using
      tenthFace_clearedV_collapsed610 h0 w1 a41 s1 u1 p31 b62 q52
        (p.coeff 2) (p.coeff 1) lambda
  have hWclr :
      localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        h0 ^ 26 * ((583200 : k[X]) * p31 ^ 2 -
          (489888 : k[X]) * p31 * u1 + (419904 : k[X]) * q.coeff 4 -
          (518400 : k[X]) * a41 ^ 3 * h0 +
          (466560 : k[X]) * a41 ^ 2 * h0 * s1 -
          (419904 : k[X]) * a41 * b62 * h0 -
          (349920 : k[X]) * a41 * h0 * Polynomial.C lambda * p31 +
          (1166400 : k[X]) * a41 * h0 * p.coeff 2 -
          (1360800 : k[X]) * a41 * h0 * p31 * w1 +
          (816480 : k[X]) * a41 * h0 * u1 * w1 -
          (559872 : k[X]) * h0 * p.coeff 2 * s1 +
          (933120 : k[X]) * h0 * p31 * s1 * w1 -
          (349920 : k[X]) * h0 * q52 * w1 +
          (466560 : k[X]) * a41 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
            w1 +
          (518400 : k[X]) * a41 ^ 2 * h0 ^ 2 * w1 ^ 2 -
          (1244160 : k[X]) * a41 * h0 ^ 2 * s1 * w1 ^ 2 +
          (349920 : k[X]) * b62 * h0 ^ 2 * w1 ^ 2 -
          (349920 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 2 *
            w1 +
          (466560 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p31 *
            w1 ^ 2 +
          (194400 : k[X]) * h0 ^ 2 * p.coeff 2 * w1 ^ 2 -
          (432000 : k[X]) * h0 ^ 2 * p31 * w1 ^ 3 -
          (362880 : k[X]) * h0 ^ 2 * u1 * w1 ^ 3 -
          (570240 : k[X]) * a41 * h0 ^ 3 * Polynomial.C lambda *
            w1 ^ 3 +
          (633600 : k[X]) * a41 * h0 ^ 3 * w1 ^ 4 +
          (209952 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 1 +
          (116640 : k[X]) * h0 ^ 3 * p.coeff 1 * w1 +
          (380160 : k[X]) * h0 ^ 3 * s1 * w1 ^ 4 +
          (133056 : k[X]) * h0 ^ 4 * Polynomial.C lambda * w1 ^ 5 -
          (699840 : k[X]) * h0 ^ 4 * p.coeff 0 -
          (246400 : k[X]) * h0 ^ 4 * w1 ^ 6) := by
    simpa [hp5, hp4, hp3, hq8, hq7, hq6, hq5] using
      tenthFace_clearedW_collapsed610 h0 w1 a41 s1 u1 p31 b62 q52
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) lambda
  have hXclr :
      localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) lambda =
        h0 ^ 31 * (-(9600 : k[X]) * a41 ^ 2 * p31 +
          (2688 : k[X]) * a41 ^ 2 * u1 +
          (6144 : k[X]) * a41 * p31 * s1 - (2560 : k[X]) * a41 * q52 -
          (3072 : k[X]) * b62 * p31 -
          (1152 : k[X]) * Polynomial.C lambda * p31 ^ 2 +
          (7680 : k[X]) * p.coeff 2 * p31 -
          (3584 : k[X]) * p.coeff 2 * u1 -
          (3840 : k[X]) * p31 ^ 2 * w1 +
          (5376 : k[X]) * p31 * u1 * w1 -
          (2048 : k[X]) * q.coeff 4 * w1 +
          (960 : k[X]) * a41 ^ 3 * h0 * Polynomial.C lambda +
          (6400 : k[X]) * a41 ^ 3 * h0 * w1 -
          (7680 : k[X]) * a41 ^ 2 * h0 * s1 * w1 +
          (4608 : k[X]) * a41 * b62 * h0 * w1 -
          (2304 : k[X]) * a41 * h0 * Polynomial.C lambda * p.coeff 2 +
          (5760 : k[X]) * a41 * h0 * Polynomial.C lambda * p31 * w1 -
          (7680 : k[X]) * a41 * h0 * p.coeff 2 * w1 +
          (4800 : k[X]) * a41 * h0 * p31 * w1 ^ 2 -
          (6720 : k[X]) * a41 * h0 * u1 * w1 ^ 2 +
          (6144 : k[X]) * h0 * p.coeff 2 * s1 * w1 -
          (7680 : k[X]) * h0 * p31 * s1 * w1 ^ 2 +
          (3072 : k[X]) * h0 * q.coeff 3 +
          (1920 : k[X]) * h0 * q52 * w1 ^ 2 -
          (5040 : k[X]) * a41 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
            w1 ^ 2 +
          (7680 : k[X]) * a41 * h0 ^ 2 * p.coeff 1 +
          (8960 : k[X]) * a41 * h0 ^ 2 * s1 * w1 ^ 3 -
          (1920 : k[X]) * b62 * h0 ^ 2 * w1 ^ 3 +
          (2880 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 2 *
            w1 ^ 2 -
          (3360 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p31 * w1 ^ 3 -
          (4096 : k[X]) * h0 ^ 2 * p.coeff 1 * s1 -
          (3200 : k[X]) * h0 ^ 2 * p.coeff 2 * w1 ^ 3 +
          (4200 : k[X]) * h0 ^ 2 * p31 * w1 ^ 4 +
          (1960 : k[X]) * h0 ^ 2 * u1 * w1 ^ 4 +
          (3780 : k[X]) * a41 * h0 ^ 3 * Polynomial.C lambda * w1 ^ 4 -
          (5040 : k[X]) * a41 * h0 ^ 3 * w1 ^ 5 -
          (2304 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 1 *
            w1 +
          (1920 : k[X]) * h0 ^ 3 * p.coeff 1 * w1 ^ 2 -
          (2016 : k[X]) * h0 ^ 3 * s1 * w1 ^ 5 +
          (1536 : k[X]) * h0 ^ 4 * Polynomial.C lambda * p.coeff 0 -
          (693 : k[X]) * h0 ^ 4 * Polynomial.C lambda * w1 ^ 6 +
          (1320 : k[X]) * h0 ^ 4 * w1 ^ 7) := by
    simpa [hp5, hp4, hp3, hq8, hq7, hq6, hq5] using
      tenthFace_clearedX_collapsed610 h0 w1 a41 s1 u1 p31 b62 q52
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) (q.coeff 3)
        lambda
  have hMcof :
      (18 : k[X]) * s1 - (30 : k[X]) * a41 +
          (9 : k[X]) * Polynomial.C lambda * w1 * h0 -
          (10 : k[X]) * h0 * w1 ^ 2 =
        Polynomial.C alpha * h0 := by
    apply mul_left_cancel₀ (pow_ne_zero 9 hh0)
    rw [← hMclr, hMrel]
    ring
  have hTcof :
      (648 : k[X]) * u1 - (1080 : k[X]) * p31 +
          (324 : k[X]) * a41 * h0 * Polynomial.C lambda +
          (720 : k[X]) * a41 * h0 * w1 -
          (864 : k[X]) * h0 * s1 * w1 -
          (351 : k[X]) * Polynomial.C lambda * h0 ^ 2 * w1 ^ 2 +
          (520 : k[X]) * h0 ^ 2 * w1 ^ 3 =
        Polynomial.C gamma * h0 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 13 hh0)
    rw [← hTclr, hTrel]
    ring
  have hUcof :
      (720 : k[X]) * a41 ^ 2 - (576 : k[X]) * a41 * s1 +
          (432 : k[X]) * b62 +
          (216 : k[X]) * Polynomial.C lambda * p31 -
          (720 : k[X]) * p.coeff 2 + (360 : k[X]) * p31 * w1 -
          (504 : k[X]) * u1 * w1 -
          (432 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 +
          (576 : k[X]) * h0 * s1 * w1 ^ 2 +
          (216 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 3 -
          (360 : k[X]) * h0 ^ 2 * w1 ^ 4 =
        Polynomial.C delta * h0 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 18 hh0)
    rw [← hUclr, hUrel]
    ring
  have hVcof :
      (285120 : k[X]) * a41 * p31 -
          (108864 : k[X]) * a41 * u1 - (124416 : k[X]) * p31 * s1 +
          (93312 : k[X]) * q52 -
          (42768 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda -
          (190080 : k[X]) * a41 ^ 2 * h0 * w1 +
          (228096 : k[X]) * a41 * h0 * s1 * w1 -
          (93312 : k[X]) * b62 * h0 * w1 +
          (121176 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
            w1 ^ 2 -
          (89760 : k[X]) * a41 * h0 ^ 2 * w1 ^ 3 -
          (155520 : k[X]) * h0 ^ 2 * p.coeff 1 -
          (107712 : k[X]) * h0 ^ 2 * s1 * w1 ^ 3 +
          (46656 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 -
          (85536 : k[X]) * h0 * Polynomial.C lambda * p31 * w1 +
          (51840 : k[X]) * h0 * p.coeff 2 * w1 +
          (23760 : k[X]) * h0 * p31 * w1 ^ 2 +
          (99792 : k[X]) * h0 * u1 * w1 ^ 2 -
          (38709 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 4 +
          (68816 : k[X]) * h0 ^ 3 * w1 ^ 5 =
        Polynomial.C eps * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 22 hh0)
    rw [← hVclr, hVrel]
    ring
  have hWcof :
      (583200 : k[X]) * p31 ^ 2 -
          (489888 : k[X]) * p31 * u1 + (419904 : k[X]) * q.coeff 4 -
          (518400 : k[X]) * a41 ^ 3 * h0 +
          (466560 : k[X]) * a41 ^ 2 * h0 * s1 -
          (419904 : k[X]) * a41 * b62 * h0 -
          (349920 : k[X]) * a41 * h0 * Polynomial.C lambda * p31 +
          (1166400 : k[X]) * a41 * h0 * p.coeff 2 -
          (1360800 : k[X]) * a41 * h0 * p31 * w1 +
          (816480 : k[X]) * a41 * h0 * u1 * w1 -
          (559872 : k[X]) * h0 * p.coeff 2 * s1 +
          (933120 : k[X]) * h0 * p31 * s1 * w1 -
          (349920 : k[X]) * h0 * q52 * w1 +
          (466560 : k[X]) * a41 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
            w1 +
          (518400 : k[X]) * a41 ^ 2 * h0 ^ 2 * w1 ^ 2 -
          (1244160 : k[X]) * a41 * h0 ^ 2 * s1 * w1 ^ 2 +
          (349920 : k[X]) * b62 * h0 ^ 2 * w1 ^ 2 -
          (349920 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 2 *
            w1 +
          (466560 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p31 *
            w1 ^ 2 +
          (194400 : k[X]) * h0 ^ 2 * p.coeff 2 * w1 ^ 2 -
          (432000 : k[X]) * h0 ^ 2 * p31 * w1 ^ 3 -
          (362880 : k[X]) * h0 ^ 2 * u1 * w1 ^ 3 -
          (570240 : k[X]) * a41 * h0 ^ 3 * Polynomial.C lambda *
            w1 ^ 3 +
          (633600 : k[X]) * a41 * h0 ^ 3 * w1 ^ 4 +
          (209952 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 1 +
          (116640 : k[X]) * h0 ^ 3 * p.coeff 1 * w1 +
          (380160 : k[X]) * h0 ^ 3 * s1 * w1 ^ 4 +
          (133056 : k[X]) * h0 ^ 4 * Polynomial.C lambda * w1 ^ 5 -
          (699840 : k[X]) * h0 ^ 4 * p.coeff 0 -
          (246400 : k[X]) * h0 ^ 4 * w1 ^ 6 =
        Polynomial.C zeta * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 26 hh0)
    rw [← hWclr, hWrel]
    ring
  have hXcof :
      -(9600 : k[X]) * a41 ^ 2 * p31 +
          (2688 : k[X]) * a41 ^ 2 * u1 +
          (6144 : k[X]) * a41 * p31 * s1 - (2560 : k[X]) * a41 * q52 -
          (3072 : k[X]) * b62 * p31 -
          (1152 : k[X]) * Polynomial.C lambda * p31 ^ 2 +
          (7680 : k[X]) * p.coeff 2 * p31 -
          (3584 : k[X]) * p.coeff 2 * u1 -
          (3840 : k[X]) * p31 ^ 2 * w1 +
          (5376 : k[X]) * p31 * u1 * w1 -
          (2048 : k[X]) * q.coeff 4 * w1 +
          (960 : k[X]) * a41 ^ 3 * h0 * Polynomial.C lambda +
          (6400 : k[X]) * a41 ^ 3 * h0 * w1 -
          (7680 : k[X]) * a41 ^ 2 * h0 * s1 * w1 +
          (4608 : k[X]) * a41 * b62 * h0 * w1 -
          (2304 : k[X]) * a41 * h0 * Polynomial.C lambda * p.coeff 2 +
          (5760 : k[X]) * a41 * h0 * Polynomial.C lambda * p31 * w1 -
          (7680 : k[X]) * a41 * h0 * p.coeff 2 * w1 +
          (4800 : k[X]) * a41 * h0 * p31 * w1 ^ 2 -
          (6720 : k[X]) * a41 * h0 * u1 * w1 ^ 2 +
          (6144 : k[X]) * h0 * p.coeff 2 * s1 * w1 -
          (7680 : k[X]) * h0 * p31 * s1 * w1 ^ 2 +
          (3072 : k[X]) * h0 * q.coeff 3 +
          (1920 : k[X]) * h0 * q52 * w1 ^ 2 -
          (5040 : k[X]) * a41 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
            w1 ^ 2 +
          (7680 : k[X]) * a41 * h0 ^ 2 * p.coeff 1 +
          (8960 : k[X]) * a41 * h0 ^ 2 * s1 * w1 ^ 3 -
          (1920 : k[X]) * b62 * h0 ^ 2 * w1 ^ 3 +
          (2880 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 2 *
            w1 ^ 2 -
          (3360 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p31 * w1 ^ 3 -
          (4096 : k[X]) * h0 ^ 2 * p.coeff 1 * s1 -
          (3200 : k[X]) * h0 ^ 2 * p.coeff 2 * w1 ^ 3 +
          (4200 : k[X]) * h0 ^ 2 * p31 * w1 ^ 4 +
          (1960 : k[X]) * h0 ^ 2 * u1 * w1 ^ 4 +
          (3780 : k[X]) * a41 * h0 ^ 3 * Polynomial.C lambda * w1 ^ 4 -
          (5040 : k[X]) * a41 * h0 ^ 3 * w1 ^ 5 -
          (2304 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 1 *
            w1 +
          (1920 : k[X]) * h0 ^ 3 * p.coeff 1 * w1 ^ 2 -
          (2016 : k[X]) * h0 ^ 3 * s1 * w1 ^ 5 +
          (1536 : k[X]) * h0 ^ 4 * Polynomial.C lambda * p.coeff 0 -
          (693 : k[X]) * h0 ^ 4 * Polynomial.C lambda * w1 ^ 6 +
          (1320 : k[X]) * h0 ^ 4 * w1 ^ 7 =
        Polynomial.C eta * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 31 hh0)
    rw [← hXclr, hXrel]
    ring
  have hMeval' :
      (18 : k) * s1.eval a - (30 : k) * a41.eval a = 0 := by
    have hleft :=
      eval_tenthFace_M_cofactor610 h0 w1 a41 s1 lambda a hroot
    have hzero :
        Polynomial.eval a
            ((18 : k[X]) * s1 - (30 : k[X]) * a41 +
              (9 : k[X]) * Polynomial.C lambda * w1 * h0 -
              (10 : k[X]) * h0 * w1 ^ 2) = 0 := by
      rw [hMcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hTeval' :
      (648 : k) * u1.eval a - (1080 : k) * p31.eval a = 0 := by
    have hleft :=
      eval_tenthFace_T_cofactor610 h0 w1 a41 s1 u1 p31 lambda a hroot
    have hzero :
        Polynomial.eval a
            ((648 : k[X]) * u1 - (1080 : k[X]) * p31 +
              (324 : k[X]) * a41 * h0 * Polynomial.C lambda +
              (720 : k[X]) * a41 * h0 * w1 -
              (864 : k[X]) * h0 * s1 * w1 -
              (351 : k[X]) * Polynomial.C lambda * h0 ^ 2 * w1 ^ 2 +
              (520 : k[X]) * h0 ^ 2 * w1 ^ 3) = 0 := by
      rw [hTcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hUeval' :
      (720 : k) * (a41.eval a) ^ 2 -
        (576 : k) * a41.eval a * s1.eval a +
        (432 : k) * b62.eval a + (216 : k) * lambda * p31.eval a -
        (720 : k) * (p.coeff 2).eval a +
        (360 : k) * p31.eval a * w1.eval a -
        (504 : k) * u1.eval a * w1.eval a = 0 := by
    have hleft :=
      eval_tenthFace_U_cofactor610 h0 w1 a41 s1 u1 p31 b62 (p.coeff 2)
        lambda a hroot
    have hzero :
        Polynomial.eval a
            ((720 : k[X]) * a41 ^ 2 - (576 : k[X]) * a41 * s1 +
              (432 : k[X]) * b62 +
              (216 : k[X]) * Polynomial.C lambda * p31 -
              (720 : k[X]) * p.coeff 2 + (360 : k[X]) * p31 * w1 -
              (504 : k[X]) * u1 * w1 -
              (432 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 +
              (576 : k[X]) * h0 * s1 * w1 ^ 2 +
              (216 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 3 -
              (360 : k[X]) * h0 ^ 2 * w1 ^ 4) = 0 := by
      rw [hUcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hVeval' :
      (285120 : k) * a41.eval a * p31.eval a -
        (108864 : k) * a41.eval a * u1.eval a -
        (124416 : k) * p31.eval a * s1.eval a +
        (93312 : k) * q52.eval a = 0 := by
    have hleft :=
      eval_tenthFace_V_cofactor610 h0 w1 a41 s1 u1 p31 b62 q52
        (p.coeff 2) (p.coeff 1) lambda a hroot
    have hzero :
        Polynomial.eval a
            ((285120 : k[X]) * a41 * p31 -
              (108864 : k[X]) * a41 * u1 -
              (124416 : k[X]) * p31 * s1 + (93312 : k[X]) * q52 -
              (42768 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda -
              (190080 : k[X]) * a41 ^ 2 * h0 * w1 +
              (228096 : k[X]) * a41 * h0 * s1 * w1 -
              (93312 : k[X]) * b62 * h0 * w1 +
              (121176 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
                w1 ^ 2 -
              (89760 : k[X]) * a41 * h0 ^ 2 * w1 ^ 3 -
              (155520 : k[X]) * h0 ^ 2 * p.coeff 1 -
              (107712 : k[X]) * h0 ^ 2 * s1 * w1 ^ 3 +
              (46656 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 -
              (85536 : k[X]) * h0 * Polynomial.C lambda * p31 * w1 +
              (51840 : k[X]) * h0 * p.coeff 2 * w1 +
              (23760 : k[X]) * h0 * p31 * w1 ^ 2 +
              (99792 : k[X]) * h0 * u1 * w1 ^ 2 -
              (38709 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 4 +
              (68816 : k[X]) * h0 ^ 3 * w1 ^ 5) = 0 := by
      rw [hVcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hWeval' :
      (583200 : k) * (p31.eval a) ^ 2 -
        (489888 : k) * p31.eval a * u1.eval a +
        (419904 : k) * (q.coeff 4).eval a = 0 := by
    have hleft :=
      eval_tenthFace_W_cofactor610 h0 w1 a41 s1 u1 p31 b62 q52
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) lambda a hroot
    have hzero :
        Polynomial.eval a
            ((583200 : k[X]) * p31 ^ 2 -
              (489888 : k[X]) * p31 * u1 +
              (419904 : k[X]) * q.coeff 4 -
              (518400 : k[X]) * a41 ^ 3 * h0 +
              (466560 : k[X]) * a41 ^ 2 * h0 * s1 -
              (419904 : k[X]) * a41 * b62 * h0 -
              (349920 : k[X]) * a41 * h0 * Polynomial.C lambda * p31 +
              (1166400 : k[X]) * a41 * h0 * p.coeff 2 -
              (1360800 : k[X]) * a41 * h0 * p31 * w1 +
              (816480 : k[X]) * a41 * h0 * u1 * w1 -
              (559872 : k[X]) * h0 * p.coeff 2 * s1 +
              (933120 : k[X]) * h0 * p31 * s1 * w1 -
              (349920 : k[X]) * h0 * q52 * w1 +
              (466560 : k[X]) * a41 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
                w1 +
              (518400 : k[X]) * a41 ^ 2 * h0 ^ 2 * w1 ^ 2 -
              (1244160 : k[X]) * a41 * h0 ^ 2 * s1 * w1 ^ 2 +
              (349920 : k[X]) * b62 * h0 ^ 2 * w1 ^ 2 -
              (349920 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                p.coeff 2 * w1 +
              (466560 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p31 *
                w1 ^ 2 +
              (194400 : k[X]) * h0 ^ 2 * p.coeff 2 * w1 ^ 2 -
              (432000 : k[X]) * h0 ^ 2 * p31 * w1 ^ 3 -
              (362880 : k[X]) * h0 ^ 2 * u1 * w1 ^ 3 -
              (570240 : k[X]) * a41 * h0 ^ 3 * Polynomial.C lambda *
                w1 ^ 3 +
              (633600 : k[X]) * a41 * h0 ^ 3 * w1 ^ 4 +
              (209952 : k[X]) * h0 ^ 3 * Polynomial.C lambda *
                p.coeff 1 +
              (116640 : k[X]) * h0 ^ 3 * p.coeff 1 * w1 +
              (380160 : k[X]) * h0 ^ 3 * s1 * w1 ^ 4 +
              (133056 : k[X]) * h0 ^ 4 * Polynomial.C lambda * w1 ^ 5 -
              (699840 : k[X]) * h0 ^ 4 * p.coeff 0 -
              (246400 : k[X]) * h0 ^ 4 * w1 ^ 6) = 0 := by
      rw [hWcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hXeval' :
      -(9600 : k) * (a41.eval a) ^ 2 * p31.eval a +
        (2688 : k) * (a41.eval a) ^ 2 * u1.eval a +
        (6144 : k) * a41.eval a * p31.eval a * s1.eval a -
        (2560 : k) * a41.eval a * q52.eval a -
        (3072 : k) * b62.eval a * p31.eval a -
        (1152 : k) * lambda * (p31.eval a) ^ 2 +
        (7680 : k) * (p.coeff 2).eval a * p31.eval a -
        (3584 : k) * (p.coeff 2).eval a * u1.eval a -
        (3840 : k) * (p31.eval a) ^ 2 * w1.eval a +
        (5376 : k) * p31.eval a * u1.eval a * w1.eval a -
        (2048 : k) * (q.coeff 4).eval a * w1.eval a = 0 := by
    have hleft :=
      eval_tenthFace_X_cofactor610 h0 w1 a41 s1 u1 p31 b62 q52
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) (q.coeff 3)
        lambda a hroot
    have hzero :
        Polynomial.eval a
            (-(9600 : k[X]) * a41 ^ 2 * p31 +
              (2688 : k[X]) * a41 ^ 2 * u1 +
              (6144 : k[X]) * a41 * p31 * s1 -
              (2560 : k[X]) * a41 * q52 -
              (3072 : k[X]) * b62 * p31 -
              (1152 : k[X]) * Polynomial.C lambda * p31 ^ 2 +
              (7680 : k[X]) * p.coeff 2 * p31 -
              (3584 : k[X]) * p.coeff 2 * u1 -
              (3840 : k[X]) * p31 ^ 2 * w1 +
              (5376 : k[X]) * p31 * u1 * w1 -
              (2048 : k[X]) * q.coeff 4 * w1 +
              (960 : k[X]) * a41 ^ 3 * h0 * Polynomial.C lambda +
              (6400 : k[X]) * a41 ^ 3 * h0 * w1 -
              (7680 : k[X]) * a41 ^ 2 * h0 * s1 * w1 +
              (4608 : k[X]) * a41 * b62 * h0 * w1 -
              (2304 : k[X]) * a41 * h0 * Polynomial.C lambda *
                p.coeff 2 +
              (5760 : k[X]) * a41 * h0 * Polynomial.C lambda * p31 *
                w1 -
              (7680 : k[X]) * a41 * h0 * p.coeff 2 * w1 +
              (4800 : k[X]) * a41 * h0 * p31 * w1 ^ 2 -
              (6720 : k[X]) * a41 * h0 * u1 * w1 ^ 2 +
              (6144 : k[X]) * h0 * p.coeff 2 * s1 * w1 -
              (7680 : k[X]) * h0 * p31 * s1 * w1 ^ 2 +
              (3072 : k[X]) * h0 * q.coeff 3 +
              (1920 : k[X]) * h0 * q52 * w1 ^ 2 -
              (5040 : k[X]) * a41 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
                w1 ^ 2 +
              (7680 : k[X]) * a41 * h0 ^ 2 * p.coeff 1 +
              (8960 : k[X]) * a41 * h0 ^ 2 * s1 * w1 ^ 3 -
              (1920 : k[X]) * b62 * h0 ^ 2 * w1 ^ 3 +
              (2880 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 2 *
                w1 ^ 2 -
              (3360 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p31 *
                w1 ^ 3 -
              (4096 : k[X]) * h0 ^ 2 * p.coeff 1 * s1 -
              (3200 : k[X]) * h0 ^ 2 * p.coeff 2 * w1 ^ 3 +
              (4200 : k[X]) * h0 ^ 2 * p31 * w1 ^ 4 +
              (1960 : k[X]) * h0 ^ 2 * u1 * w1 ^ 4 +
              (3780 : k[X]) * a41 * h0 ^ 3 * Polynomial.C lambda *
                w1 ^ 4 -
              (5040 : k[X]) * a41 * h0 ^ 3 * w1 ^ 5 -
              (2304 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 1 *
                w1 +
              (1920 : k[X]) * h0 ^ 3 * p.coeff 1 * w1 ^ 2 -
              (2016 : k[X]) * h0 ^ 3 * s1 * w1 ^ 5 +
              (1536 : k[X]) * h0 ^ 4 * Polynomial.C lambda * p.coeff 0 -
              (693 : k[X]) * h0 ^ 4 * Polynomial.C lambda * w1 ^ 6 +
              (1320 : k[X]) * h0 ^ 4 * w1 ^ 7) = 0 := by
      rw [hXcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  obtain ⟨hMs, hTu, hVq, hWq, hUload, hXalt⟩ :=
    tenthFace_collapsedNextOrder610 (w1.eval a) (a41.eval a) (s1.eval a)
      (p31.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
      ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda
      hMeval' hTeval' hUeval' hVeval' hWeval' hXeval'
  exact ⟨w1, a41, s1, u1, p31, b62, q52, hp5, hp4, hp3, hq8, hq7, hq6,
    hq5, hMs, hTu, hVq, hWq, hUload, hXalt⟩

set_option maxHeartbeats 8000000 in
/-- Source-facing tenth-face power jet of a normalized scale-two
`(6,10)` nonzero face: the collapsed ninth-face jet is refined at the
next order. -/
theorem normalized610ScaleTwo_nonzeroFace_tenthPowerJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K) (w1 a41 s1 u1 p31 b62 q52 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        (3 : K) * s1.eval a = (5 : K) * a41.eval a ∧
        (3 : K) * u1.eval a = (5 : K) * p31.eval a ∧
        (9 : K) * q52.eval a =
          (10 : K) * a41.eval a * p31.eval a ∧
        (9 : K) * (q.coeff 4).eval a = (5 : K) * (p31.eval a) ^ 2 ∧
        (10 : K) * (a41.eval a) ^ 2 - (18 : K) * b62.eval a -
            (9 : K) * lambda * p31.eval a +
          (30 : K) * (p.coeff 2).eval a +
            (20 : K) * p31.eval a * w1.eval a = 0 ∧
        p31.eval a *
            ((240 : K) * (p.coeff 2).eval a -
              (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
              (40 : K) * p31.eval a * w1.eval a) = 0 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, w, a4s, s, u, b6s, A1, S1, P31, U1, B61, Q51,
    hh0, hlambda, hh0degree, hH, hroot, hw, ha4s, hs, hu, hb6s, hq9,
    hA1, hS1, hP31, hU1, hB61, hQ51, hwz, ha4z, hsz, hp3z, huz, hb6z,
    hq5z, hSrel, hPrel, hBrel, hQrel, hp5_5, hp4_3, hp3_1, hq8_7, hq7_5,
    hq6_4, hq5_2, hN'⟩ :=
    normalized610ScaleTwo_nonzeroFace_ninthPowerJet hsource hnonzero
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
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, hwN, ha4sN, hp3N, hsN, huN,
    hb6sN, hq5N, hMs, hTu, hVq, hWq, hUload, hXalt⟩ :=
    nonzeroFace610_linearRoot_tenthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  exact ⟨h0, lambda, a, w1, a41, s1, u1, p31, b62, q52, hh0, hlambda,
    hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN, huN, hb6sN, hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs, hTu, hVq, hWq, hUload, hXalt, hN'⟩

end NonzeroTenthFace610

#print axioms tenthCoefficientJacobianRow_610
#print axioms tenthFace_M_nextOrder610
#print axioms tenthFace_T_nextOrder610
#print axioms tenthFace_V_nextOrder610
#print axioms tenthFace_W_nextOrder610
#print axioms tenthFace_U_nextOrder610
#print axioms tenthFace_X_nextOrder610
#print axioms tenthFace_collapsedNextOrder610
#print axioms tenthFace_clearedM_collapsed610
#print axioms tenthFace_clearedT_collapsed610
#print axioms tenthFace_clearedU_collapsed610
#print axioms tenthFace_clearedV_collapsed610
#print axioms tenthFace_clearedW_collapsed610
#print axioms tenthFace_clearedX_collapsed610
#print axioms nonzeroFace610_linearRoot_tenthPowerJet
#print axioms normalized610ScaleTwo_nonzeroFace_tenthPowerJet

end Max11DegreeRoutes
