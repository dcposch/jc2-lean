import LowScale610ScaleTwoEleventhFace

/-! # Scale-two twelfth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the eleventh-face packet supplies the degree-`4`
Jacobian row and the refined tenth-face alternative: either
`p₃₁(a) = 0` with the upgraded jet `h² ∣ p₃`, `h⁶ ∣ q₇`, `h³ ∣ q₅`,
`h ∣ q₄` and the laws `18 u₂ - 30 p₃₂ = a₄₁ (20 w₁ - 9 λ)`,
`81 q₄₁ = 5 a₄₁ (18 p₂ - a₄₁²)`, and
`216 q₅₃ + 27 λ a₄₁² + 40 a₄₁² w₁ - 240 a₄₁ p₃₂ + 108 λ p₂
- 240 p₂ w₁ = 0`, or the complementary factor solving `p₂` and `b₆₂`.

The next unused Keller coefficient is the degree-`3` Jacobian row.
After the same sextic depression that kills `z⁵`, that row is
`4 T E' + 3 U D' + 2 V C' + W B' - E T' - 2 D U' - 3 C V' - 4 B W'
- 5 A X' - 9 Y' = 0`.  Clearing the corresponding first integral
against the remaining decic coordinates produces a defect larger than
the remaining exact jet, so this file isolates that Jacobian identity
and the strongest exact source-facing refinement of both live
eleventh-face alternatives.

On `p₃₁(a) = 0` the upgraded jet pushes the cleared seventh defect to
`h³²` while its first integral is a scalar times `h³⁵`, so the next
leftover order is exact and forces
`3888 q₃(a) = 81 λ a₄₁³ + 320 a₄₁³ w₁ - 720 a₄₁² p₃₂ - 972 λ a₄₁ p₂
- 1440 a₄₁ p₂ w₁ + 4320 p₂ p₃₂` at the root of `h`.  On the
complementary factor the already-vanishing sixth-defect combination
`583200 p₃₁² - 489888 p₃₁ u₁ + 419904 q₄ = h ω` gains one power of `h`,
and the next order of the cleared sixth defect forces
`ω(a) = 648 a₄₁ (80 a₄₁² + 297 λ p₃₁ - 960 p₃₁ w₁)`.

Neither alternative is closed further: the aligned face `N = 0` and the
`p₃₁ ≠ 0` sibling remain open, the ground constants of the sixth- and
seventh-defect first integrals are preserved and not cleared to zero,
the degree-`5`, degree-`4`, and degree-`3` first integrals stay
uncleared, and no individual vanishing of `p₂, p₁, p₀, q₃` (nor of
`w₁, a₄₁, p₃₂, ω`) is claimed.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The twelfth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the eleventh face
start at degree `3`. -/
theorem twelfthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 3) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (3 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC2, hC3, hC4]
  linear_combination hcoeff

/-! ## Scalar algebra of the eleventh-face alternatives -/

section TwelfthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ = 0` sibling, the seventh defect at the next leftover
order solves `q₃(a)` exactly. -/
theorem twelfthFace_zeroP31_X_nextOrder610 (w1 a41 s1 p32 u2 b62 q53 p2
    q41 q3 : F) (lambda : F)
    (hM : (3 : F) * s1 = (5 : F) * a41)
    (hT : (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
      (9 : F) * lambda * a41 = 0)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0)
    (hW : (81 : F) * q41 - (90 : F) * a41 * p2 +
      (5 : F) * a41 ^ 3 = 0)
    (hV : (216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
        (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
        (108 : F) * lambda * p2 - (240 : F) * p2 * w1 = 0)
    (hX : (960 : F) * a41 ^ 3 * lambda + (6400 : F) * a41 ^ 3 * w1 -
        (9600 : F) * a41 ^ 2 * p32 - (7680 : F) * a41 ^ 2 * s1 * w1 +
        (2688 : F) * a41 ^ 2 * u2 + (4608 : F) * a41 * b62 * w1 -
        (2304 : F) * a41 * lambda * p2 - (7680 : F) * a41 * p2 * w1 +
        (6144 : F) * a41 * p32 * s1 - (2560 : F) * a41 * q53 -
        (3072 : F) * b62 * p32 + (7680 : F) * p2 * p32 +
        (6144 : F) * p2 * s1 * w1 - (3584 : F) * p2 * u2 +
        (3072 : F) * q3 - (2048 : F) * q41 * w1 = 0) :
    (3888 : F) * q3 - (81 : F) * lambda * a41 ^ 3 -
        (320 : F) * a41 ^ 3 * w1 + (720 : F) * a41 ^ 2 * p32 +
        (972 : F) * lambda * a41 * p2 + (1440 : F) * a41 * p2 * w1 -
      (4320 : F) * p2 * p32 = 0 := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have hs1 : s1 = (5 / 3 : F) * a41 := by
    have hid : (3 : F) * (s1 - (5 / 3 : F) * a41) =
        (3 : F) * s1 - (5 : F) * a41 := by ring
    have hz : (3 : F) * (s1 - (5 / 3 : F) * a41) = 0 := by
      rw [hid]
      linear_combination hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h3)
  have hu2 : u2 = ((30 : F) * p32 + (20 : F) * a41 * w1 -
      (9 : F) * lambda * a41) / (18 : F) := by
    have hid : (18 : F) * (u2 - ((30 : F) * p32 + (20 : F) * a41 * w1 -
          (9 : F) * lambda * a41) / (18 : F)) =
        (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
          (9 : F) * lambda * a41 := by
      ring
    have hz : (18 : F) * (u2 - ((30 : F) * p32 +
          (20 : F) * a41 * w1 - (9 : F) * lambda * a41) / (18 : F)) =
        0 := by
      rw [hid]
      linear_combination hT
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h18)
  have hb62 : b62 = (5 / 9 : F) * a41 ^ 2 + (5 / 3 : F) * p2 := by
    have hid : (18 : F) * (b62 - ((5 / 9 : F) * a41 ^ 2 +
          (5 / 3 : F) * p2)) =
        -((10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2) := by
      ring
    have hz : (18 : F) * (b62 - ((5 / 9 : F) * a41 ^ 2 +
          (5 / 3 : F) * p2)) = 0 := by
      rw [hid]
      linear_combination -hU
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h18)
  have hq41 : q41 = ((90 : F) * a41 * p2 - (5 : F) * a41 ^ 3) /
      (81 : F) := by
    have hid : (81 : F) * (q41 - ((90 : F) * a41 * p2 -
          (5 : F) * a41 ^ 3) / (81 : F)) =
        (81 : F) * q41 - (90 : F) * a41 * p2 + (5 : F) * a41 ^ 3 := by
      ring
    have hz : (81 : F) * (q41 - ((90 : F) * a41 * p2 -
          (5 : F) * a41 ^ 3) / (81 : F)) = 0 := by
      rw [hid]
      linear_combination hW
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h81)
  have hq53 : q53 = -(((27 : F) * lambda * a41 ^ 2 +
      (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
      (108 : F) * lambda * p2 - (240 : F) * p2 * w1) / (216 : F)) := by
    have hid : (216 : F) * (q53 - -(((27 : F) * lambda * a41 ^ 2 +
          (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
          (108 : F) * lambda * p2 - (240 : F) * p2 * w1) /
          (216 : F))) =
        (216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
          (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
          (108 : F) * lambda * p2 - (240 : F) * p2 * w1 := by
      ring
    have hz : (216 : F) * (q53 - -(((27 : F) * lambda * a41 ^ 2 +
          (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
          (108 : F) * lambda * p2 - (240 : F) * p2 * w1) /
          (216 : F))) = 0 := by
      rw [hid]
      linear_combination hV
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h216)
  have hX2 : (81 : F) * ((960 : F) * a41 ^ 3 * lambda +
        (6400 : F) * a41 ^ 3 * w1 - (9600 : F) * a41 ^ 2 * p32 -
        (7680 : F) * a41 ^ 2 * s1 * w1 + (2688 : F) * a41 ^ 2 * u2 +
        (4608 : F) * a41 * b62 * w1 - (2304 : F) * a41 * lambda * p2 -
        (7680 : F) * a41 * p2 * w1 + (6144 : F) * a41 * p32 * s1 -
        (2560 : F) * a41 * q53 - (3072 : F) * b62 * p32 +
        (7680 : F) * p2 * p32 + (6144 : F) * p2 * s1 * w1 -
        (3584 : F) * p2 * u2 + (3072 : F) * q3 -
        (2048 : F) * q41 * w1) =
      (64 : F) * ((3888 : F) * q3 - (81 : F) * lambda * a41 ^ 3 -
        (320 : F) * a41 ^ 3 * w1 + (720 : F) * a41 ^ 2 * p32 +
        (972 : F) * lambda * a41 * p2 + (1440 : F) * a41 * p2 * w1 -
        (4320 : F) * p2 * p32) := by
    simp only [hs1, hu2, hb62, hq41, hq53]
    ring
  have hcomb : (64 : F) * ((3888 : F) * q3 -
      (81 : F) * lambda * a41 ^ 3 - (320 : F) * a41 ^ 3 * w1 +
      (720 : F) * a41 ^ 2 * p32 + (972 : F) * lambda * a41 * p2 +
      (1440 : F) * a41 * p2 * w1 - (4320 : F) * p2 * p32) = 0 := by
    rw [← hX2, hX, mul_zero]
  exact (mul_eq_zero.mp hcomb).resolve_left h64

set_option maxHeartbeats 4000000 in
/-- On the complementary factor, the sixth defect at the next order of
the already-vanishing combination solves its cofactor `ω(a)` exactly. -/
theorem twelfthFace_tp2_W_nextOrder610 (w1 a41 s1 u1 p31 b62 q52 p2
    omega : F) (lambda : F)
    (hM : (3 : F) * s1 = (5 : F) * a41)
    (hT : (3 : F) * u1 = (5 : F) * p31)
    (hV : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hXc : (240 : F) * p2 - (40 : F) * a41 ^ 2 -
        (27 : F) * lambda * p31 - (40 : F) * p31 * w1 = 0)
    (hB : (144 : F) * b62 - (120 : F) * a41 ^ 2 +
        (45 : F) * lambda * p31 - (200 : F) * p31 * w1 = 0)
    (hW : omega + (-(518400 : F) * a41 ^ 3 +
        (466560 : F) * a41 ^ 2 * s1 - (419904 : F) * a41 * b62 -
        (349920 : F) * a41 * lambda * p31 + (1166400 : F) * a41 * p2 -
        (1360800 : F) * a41 * p31 * w1 +
        (816480 : F) * a41 * u1 * w1 - (559872 : F) * p2 * s1 +
        (933120 : F) * p31 * s1 * w1 - (349920 : F) * q52 * w1) =
      0) :
    omega = (648 : F) * a41 * ((80 : F) * a41 ^ 2 +
      (297 : F) * lambda * p31 - (960 : F) * p31 * w1) := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h240 : (240 : F) ≠ 0 := by norm_num
  have hs1 : s1 = (5 / 3 : F) * a41 := by
    have hid : (3 : F) * (s1 - (5 / 3 : F) * a41) =
        (3 : F) * s1 - (5 : F) * a41 := by ring
    have hz : (3 : F) * (s1 - (5 / 3 : F) * a41) = 0 := by
      rw [hid]
      linear_combination hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h3)
  have hu1 : u1 = (5 / 3 : F) * p31 := by
    have hid : (3 : F) * (u1 - (5 / 3 : F) * p31) =
        (3 : F) * u1 - (5 : F) * p31 := by ring
    have hz : (3 : F) * (u1 - (5 / 3 : F) * p31) = 0 := by
      rw [hid]
      linear_combination hT
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h3)
  have hq52 : q52 = (10 / 9 : F) * a41 * p31 := by
    have hid : (9 : F) * (q52 - (10 / 9 : F) * a41 * p31) =
        (9 : F) * q52 - (10 : F) * a41 * p31 := by ring
    have hz : (9 : F) * (q52 - (10 / 9 : F) * a41 * p31) = 0 := by
      rw [hid]
      linear_combination hV
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h9)
  have hb62 : b62 = ((120 : F) * a41 ^ 2 - (45 : F) * lambda * p31 +
      (200 : F) * p31 * w1) / (144 : F) := by
    have hid : (144 : F) * (b62 - ((120 : F) * a41 ^ 2 -
          (45 : F) * lambda * p31 + (200 : F) * p31 * w1) /
          (144 : F)) =
        (144 : F) * b62 - (120 : F) * a41 ^ 2 +
          (45 : F) * lambda * p31 - (200 : F) * p31 * w1 := by
      ring
    have hz : (144 : F) * (b62 - ((120 : F) * a41 ^ 2 -
          (45 : F) * lambda * p31 + (200 : F) * p31 * w1) /
          (144 : F)) = 0 := by
      rw [hid]
      linear_combination hB
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h144)
  have hp2 : p2 = ((40 : F) * a41 ^ 2 + (27 : F) * lambda * p31 +
      (40 : F) * p31 * w1) / (240 : F) := by
    have hid : (240 : F) * (p2 - ((40 : F) * a41 ^ 2 +
          (27 : F) * lambda * p31 + (40 : F) * p31 * w1) /
          (240 : F)) =
        (240 : F) * p2 - (40 : F) * a41 ^ 2 -
          (27 : F) * lambda * p31 - (40 : F) * p31 * w1 := by
      ring
    have hz : (240 : F) * (p2 - ((40 : F) * a41 ^ 2 +
          (27 : F) * lambda * p31 + (40 : F) * p31 * w1) /
          (240 : F)) = 0 := by
      rw [hid]
      linear_combination hXc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h240)
  have hW2 : omega + (-(518400 : F) * a41 ^ 3 +
        (466560 : F) * a41 ^ 2 * s1 - (419904 : F) * a41 * b62 -
        (349920 : F) * a41 * lambda * p31 + (1166400 : F) * a41 * p2 -
        (1360800 : F) * a41 * p31 * w1 +
        (816480 : F) * a41 * u1 * w1 - (559872 : F) * p2 * s1 +
        (933120 : F) * p31 * s1 * w1 - (349920 : F) * q52 * w1) =
      omega - (648 : F) * a41 * ((80 : F) * a41 ^ 2 +
        (297 : F) * lambda * p31 - (960 : F) * p31 * w1) := by
    simp only [hs1, hu1, hq52, hb62, hp2]
    ring
  have hz : omega - (648 : F) * a41 * ((80 : F) * a41 ^ 2 +
      (297 : F) * lambda * p31 - (960 : F) * p31 * w1) = 0 := by
    rw [← hW2]
    exact hW
  linear_combination hz

/-! ## Cleared-defect substitutions on the refined alternatives -/

set_option maxHeartbeats 24000000 in
/-- The cleared seventh defect on the upgraded `p₃₁ = 0` jet gains one
more power of `h` than the tenth-face collapse. -/
theorem twelfthFace_clearedX_zeroP31610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 p0 q41 q3 : F[X]) (lambda : F) :
    localClearedSeventhDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 lambda =
      h ^ 32 * ((960 : F[X]) * a41 ^ 3 * Polynomial.C lambda +
        (6400 : F[X]) * a41 ^ 3 * w1 - (9600 : F[X]) * a41 ^ 2 * p32 -
        (7680 : F[X]) * a41 ^ 2 * s1 * w1 +
        (2688 : F[X]) * a41 ^ 2 * u2 +
        (4608 : F[X]) * a41 * b62 * w1 -
        (2304 : F[X]) * a41 * Polynomial.C lambda * p2 -
        (7680 : F[X]) * a41 * p2 * w1 +
        (6144 : F[X]) * a41 * p32 * s1 - (2560 : F[X]) * a41 * q53 -
        (3072 : F[X]) * b62 * p32 + (7680 : F[X]) * p2 * p32 +
        (6144 : F[X]) * p2 * s1 * w1 - (3584 : F[X]) * p2 * u2 +
        (3072 : F[X]) * q3 - (2048 : F[X]) * q41 * w1 -
        (5040 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 ^ 2 +
        (5760 : F[X]) * a41 * h * Polynomial.C lambda * p32 * w1 +
        (7680 : F[X]) * a41 * h * p1 +
        (4800 : F[X]) * a41 * h * p32 * w1 ^ 2 +
        (8960 : F[X]) * a41 * h * s1 * w1 ^ 3 -
        (6720 : F[X]) * a41 * h * u2 * w1 ^ 2 -
        (1920 : F[X]) * b62 * h * w1 ^ 3 +
        (2880 : F[X]) * h * Polynomial.C lambda * p2 * w1 ^ 2 -
        (1152 : F[X]) * h * Polynomial.C lambda * p32 ^ 2 -
        (4096 : F[X]) * h * p1 * s1 -
        (3200 : F[X]) * h * p2 * w1 ^ 3 -
        (3840 : F[X]) * h * p32 ^ 2 * w1 -
        (7680 : F[X]) * h * p32 * s1 * w1 ^ 2 +
        (5376 : F[X]) * h * p32 * u2 * w1 +
        (1920 : F[X]) * h * q53 * w1 ^ 2 +
        (3780 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 4 -
        (5040 : F[X]) * a41 * h ^ 2 * w1 ^ 5 -
        (2304 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 * w1 -
        (3360 : F[X]) * h ^ 2 * Polynomial.C lambda * p32 * w1 ^ 3 +
        (1920 : F[X]) * h ^ 2 * p1 * w1 ^ 2 +
        (4200 : F[X]) * h ^ 2 * p32 * w1 ^ 4 -
        (2016 : F[X]) * h ^ 2 * s1 * w1 ^ 5 +
        (1960 : F[X]) * h ^ 2 * u2 * w1 ^ 4 +
        (1536 : F[X]) * h ^ 3 * Polynomial.C lambda * p0 -
        (693 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 6 +
        (1320 : F[X]) * h ^ 3 * w1 ^ 7) := by
  simp only [localClearedSeventhDefect610]
  ring

theorem eval_twelfthFace_X_cofactor610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 p0 q41 q3 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((960 : F[X]) * a41 ^ 3 * Polynomial.C lambda +
          (6400 : F[X]) * a41 ^ 3 * w1 -
          (9600 : F[X]) * a41 ^ 2 * p32 -
          (7680 : F[X]) * a41 ^ 2 * s1 * w1 +
          (2688 : F[X]) * a41 ^ 2 * u2 +
          (4608 : F[X]) * a41 * b62 * w1 -
          (2304 : F[X]) * a41 * Polynomial.C lambda * p2 -
          (7680 : F[X]) * a41 * p2 * w1 +
          (6144 : F[X]) * a41 * p32 * s1 - (2560 : F[X]) * a41 * q53 -
          (3072 : F[X]) * b62 * p32 + (7680 : F[X]) * p2 * p32 +
          (6144 : F[X]) * p2 * s1 * w1 - (3584 : F[X]) * p2 * u2 +
          (3072 : F[X]) * q3 - (2048 : F[X]) * q41 * w1 -
          (5040 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 ^ 2 +
          (5760 : F[X]) * a41 * h * Polynomial.C lambda * p32 * w1 +
          (7680 : F[X]) * a41 * h * p1 +
          (4800 : F[X]) * a41 * h * p32 * w1 ^ 2 +
          (8960 : F[X]) * a41 * h * s1 * w1 ^ 3 -
          (6720 : F[X]) * a41 * h * u2 * w1 ^ 2 -
          (1920 : F[X]) * b62 * h * w1 ^ 3 +
          (2880 : F[X]) * h * Polynomial.C lambda * p2 * w1 ^ 2 -
          (1152 : F[X]) * h * Polynomial.C lambda * p32 ^ 2 -
          (4096 : F[X]) * h * p1 * s1 -
          (3200 : F[X]) * h * p2 * w1 ^ 3 -
          (3840 : F[X]) * h * p32 ^ 2 * w1 -
          (7680 : F[X]) * h * p32 * s1 * w1 ^ 2 +
          (5376 : F[X]) * h * p32 * u2 * w1 +
          (1920 : F[X]) * h * q53 * w1 ^ 2 +
          (3780 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 4 -
          (5040 : F[X]) * a41 * h ^ 2 * w1 ^ 5 -
          (2304 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 * w1 -
          (3360 : F[X]) * h ^ 2 * Polynomial.C lambda * p32 * w1 ^ 3 +
          (1920 : F[X]) * h ^ 2 * p1 * w1 ^ 2 +
          (4200 : F[X]) * h ^ 2 * p32 * w1 ^ 4 -
          (2016 : F[X]) * h ^ 2 * s1 * w1 ^ 5 +
          (1960 : F[X]) * h ^ 2 * u2 * w1 ^ 4 +
          (1536 : F[X]) * h ^ 3 * Polynomial.C lambda * p0 -
          (693 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 6 +
          (1320 : F[X]) * h ^ 3 * w1 ^ 7) =
      (960 : F) * (Polynomial.eval root a41) ^ 3 * lambda +
        (6400 : F) * (Polynomial.eval root a41) ^ 3 *
          Polynomial.eval root w1 -
        (9600 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root p32 -
        (7680 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root s1 * Polynomial.eval root w1 +
        (2688 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root u2 +
        (4608 : F) * Polynomial.eval root a41 *
          Polynomial.eval root b62 * Polynomial.eval root w1 -
        (2304 : F) * Polynomial.eval root a41 * lambda *
          Polynomial.eval root p2 -
        (7680 : F) * Polynomial.eval root a41 *
          Polynomial.eval root p2 * Polynomial.eval root w1 +
        (6144 : F) * Polynomial.eval root a41 *
          Polynomial.eval root p32 * Polynomial.eval root s1 -
        (2560 : F) * Polynomial.eval root a41 *
          Polynomial.eval root q53 -
        (3072 : F) * Polynomial.eval root b62 *
          Polynomial.eval root p32 +
        (7680 : F) * Polynomial.eval root p2 *
          Polynomial.eval root p32 +
        (6144 : F) * Polynomial.eval root p2 *
          Polynomial.eval root s1 * Polynomial.eval root w1 -
        (3584 : F) * Polynomial.eval root p2 *
          Polynomial.eval root u2 +
        (3072 : F) * Polynomial.eval root q3 -
        (2048 : F) * Polynomial.eval root q41 *
          Polynomial.eval root w1 := by
  simp [hroot]

set_option maxHeartbeats 12000000 in
/-- The tenth-face collapse of the cleared sixth defect, grouped around
the already-vanishing combination. -/
theorem twelfthFace_comp_clearedW_grouped610 (h w1 a41 s1 u1 p31 b62
    q52 p2 p1 p0 q4 : F[X]) (lambda : F) :
    localClearedSixthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        q4 lambda =
      h ^ 26 * ((583200 : F[X]) * p31 ^ 2 -
        (489888 : F[X]) * p31 * u1 + (419904 : F[X]) * q4 +
        h * (-(518400 : F[X]) * a41 ^ 3 +
          (466560 : F[X]) * a41 ^ 2 * s1 -
          (419904 : F[X]) * a41 * b62 -
          (349920 : F[X]) * a41 * Polynomial.C lambda * p31 +
          (1166400 : F[X]) * a41 * p2 -
          (1360800 : F[X]) * a41 * p31 * w1 +
          (816480 : F[X]) * a41 * u1 * w1 -
          (559872 : F[X]) * p2 * s1 +
          (933120 : F[X]) * p31 * s1 * w1 -
          (349920 : F[X]) * q52 * w1 +
          (466560 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 +
          (518400 : F[X]) * a41 ^ 2 * h * w1 ^ 2 -
          (1244160 : F[X]) * a41 * h * s1 * w1 ^ 2 +
          (349920 : F[X]) * b62 * h * w1 ^ 2 -
          (349920 : F[X]) * h * Polynomial.C lambda * p2 * w1 +
          (466560 : F[X]) * h * Polynomial.C lambda * p31 * w1 ^ 2 +
          (194400 : F[X]) * h * p2 * w1 ^ 2 -
          (432000 : F[X]) * h * p31 * w1 ^ 3 -
          (362880 : F[X]) * h * u1 * w1 ^ 3 -
          (570240 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda *
            w1 ^ 3 +
          (633600 : F[X]) * a41 * h ^ 2 * w1 ^ 4 +
          (209952 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 +
          (116640 : F[X]) * h ^ 2 * p1 * w1 +
          (380160 : F[X]) * h ^ 2 * s1 * w1 ^ 4 +
          (133056 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 5 -
          (699840 : F[X]) * h ^ 3 * p0 -
          (246400 : F[X]) * h ^ 3 * w1 ^ 6)) := by
  simp only [localClearedSixthDefect610]
  ring

/-- Peeling the extra factor of `h` from the vanishing combination
pushes the cleared sixth defect to `h²⁷`. -/
theorem twelfthFace_comp_sixthDefect_omega610 (h w1 a41 s1 u1 p31 b62
    q52 p2 p1 p0 q4 omega : F[X]) (lambda : F)
    (homega : (583200 : F[X]) * p31 ^ 2 - (489888 : F[X]) * p31 * u1 +
      (419904 : F[X]) * q4 = h * omega) :
    localClearedSixthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        q4 lambda =
      h ^ 27 * (omega + (-(518400 : F[X]) * a41 ^ 3 +
        (466560 : F[X]) * a41 ^ 2 * s1 -
        (419904 : F[X]) * a41 * b62 -
        (349920 : F[X]) * a41 * Polynomial.C lambda * p31 +
        (1166400 : F[X]) * a41 * p2 -
        (1360800 : F[X]) * a41 * p31 * w1 +
        (816480 : F[X]) * a41 * u1 * w1 -
        (559872 : F[X]) * p2 * s1 +
        (933120 : F[X]) * p31 * s1 * w1 -
        (349920 : F[X]) * q52 * w1 +
        (466560 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 +
        (518400 : F[X]) * a41 ^ 2 * h * w1 ^ 2 -
        (1244160 : F[X]) * a41 * h * s1 * w1 ^ 2 +
        (349920 : F[X]) * b62 * h * w1 ^ 2 -
        (349920 : F[X]) * h * Polynomial.C lambda * p2 * w1 +
        (466560 : F[X]) * h * Polynomial.C lambda * p31 * w1 ^ 2 +
        (194400 : F[X]) * h * p2 * w1 ^ 2 -
        (432000 : F[X]) * h * p31 * w1 ^ 3 -
        (362880 : F[X]) * h * u1 * w1 ^ 3 -
        (570240 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 3 +
        (633600 : F[X]) * a41 * h ^ 2 * w1 ^ 4 +
        (209952 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 +
        (116640 : F[X]) * h ^ 2 * p1 * w1 +
        (380160 : F[X]) * h ^ 2 * s1 * w1 ^ 4 +
        (133056 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 5 -
        (699840 : F[X]) * h ^ 3 * p0 -
        (246400 : F[X]) * h ^ 3 * w1 ^ 6)) := by
  rw [twelfthFace_comp_clearedW_grouped610, homega]
  ring

theorem eval_twelfthFace_comp_W_cofactor610 (h w1 a41 s1 u1 p31 b62
    q52 p2 p1 p0 omega : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (omega + (-(518400 : F[X]) * a41 ^ 3 +
          (466560 : F[X]) * a41 ^ 2 * s1 -
          (419904 : F[X]) * a41 * b62 -
          (349920 : F[X]) * a41 * Polynomial.C lambda * p31 +
          (1166400 : F[X]) * a41 * p2 -
          (1360800 : F[X]) * a41 * p31 * w1 +
          (816480 : F[X]) * a41 * u1 * w1 -
          (559872 : F[X]) * p2 * s1 +
          (933120 : F[X]) * p31 * s1 * w1 -
          (349920 : F[X]) * q52 * w1 +
          (466560 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 +
          (518400 : F[X]) * a41 ^ 2 * h * w1 ^ 2 -
          (1244160 : F[X]) * a41 * h * s1 * w1 ^ 2 +
          (349920 : F[X]) * b62 * h * w1 ^ 2 -
          (349920 : F[X]) * h * Polynomial.C lambda * p2 * w1 +
          (466560 : F[X]) * h * Polynomial.C lambda * p31 * w1 ^ 2 +
          (194400 : F[X]) * h * p2 * w1 ^ 2 -
          (432000 : F[X]) * h * p31 * w1 ^ 3 -
          (362880 : F[X]) * h * u1 * w1 ^ 3 -
          (570240 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda *
            w1 ^ 3 +
          (633600 : F[X]) * a41 * h ^ 2 * w1 ^ 4 +
          (209952 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 +
          (116640 : F[X]) * h ^ 2 * p1 * w1 +
          (380160 : F[X]) * h ^ 2 * s1 * w1 ^ 4 +
          (133056 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 5 -
          (699840 : F[X]) * h ^ 3 * p0 -
          (246400 : F[X]) * h ^ 3 * w1 ^ 6)) =
      Polynomial.eval root omega +
        (-(518400 : F) * (Polynomial.eval root a41) ^ 3 +
          (466560 : F) * (Polynomial.eval root a41) ^ 2 *
            Polynomial.eval root s1 -
          (419904 : F) * Polynomial.eval root a41 *
            Polynomial.eval root b62 -
          (349920 : F) * Polynomial.eval root a41 * lambda *
            Polynomial.eval root p31 +
          (1166400 : F) * Polynomial.eval root a41 *
            Polynomial.eval root p2 -
          (1360800 : F) * Polynomial.eval root a41 *
            Polynomial.eval root p31 * Polynomial.eval root w1 +
          (816480 : F) * Polynomial.eval root a41 *
            Polynomial.eval root u1 * Polynomial.eval root w1 -
          (559872 : F) * Polynomial.eval root p2 *
            Polynomial.eval root s1 +
          (933120 : F) * Polynomial.eval root p31 *
            Polynomial.eval root s1 * Polynomial.eval root w1 -
          (349920 : F) * Polynomial.eval root q52 *
            Polynomial.eval root w1) := by
  simp [hroot]

end TwelfthFaceScalars610

/-! ## Source-facing twelfth-face packet -/

section NonzeroTwelfthFace610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
/-- Finite local twelfth-face packet: both eleventh-face alternatives
are refined.  On `p₃₁(a) = 0` the seventh defect at the next order
solves `q₃(a)` exactly; on the complementary factor the sixth defect at
the next order solves the cofactor of the already-vanishing combination
exactly. -/
theorem nonzeroFace610_linearRoot_twelfthPowerJet
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
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : k[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : k) * u2.eval a - (30 : k) * p32.eval a -
                    (20 : k) * a41.eval a * w1.eval a +
                  (9 : k) * lambda * a41.eval a = 0 ∧
                (81 : k) * q41.eval a -
                    (90 : k) * a41.eval a * (p.coeff 2).eval a +
                  (5 : k) * (a41.eval a) ^ 3 = 0 ∧
                (216 : k) * q53.eval a +
                    (27 : k) * lambda * (a41.eval a) ^ 2 +
                  (40 : k) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : k) * a41.eval a * p32.eval a +
                  (108 : k) * lambda * (p.coeff 2).eval a -
                    (240 : k) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : k) * (q.coeff 3).eval a -
                    (81 : k) * lambda * (a41.eval a) ^ 3 -
                  (320 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : k) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : k) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : k) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : k) * (p.coeff 2).eval a * p32.eval a =
                    0) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ∃ omega : k[X],
              (583200 : k[X]) * p31 ^ 2 -
                  (489888 : k[X]) * p31 * u1 +
                (419904 : k[X]) * q.coeff 4 = h0 * omega ∧
              omega.eval a =
                (648 : k) * a41.eval a *
                  ((80 : k) * (a41.eval a) ^ 2 +
                      (297 : k) * lambda * p31.eval a -
                    (960 : k) * p31.eval a * w1.eval a))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, halt⟩ :=
    nonzeroFace610_linearRoot_eleventhPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, ?_⟩
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      hTform, hWform, hVform⟩⟩ | ⟨htp, hb62form⟩
  · -- `p₃₁(a) = 0`: seventh defect at the next order.
    obtain ⟨eta, hXrel⟩ :=
      nonzeroFace610_seventhDefectPowerRelation p q H h0 j lambda
        hp hq hh0 hH hp6 hq10 hN hD
    have hXclr :
        localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda =
          h0 ^ 32 * ((960 : k[X]) * a41 ^ 3 * Polynomial.C lambda +
            (6400 : k[X]) * a41 ^ 3 * w1 -
            (9600 : k[X]) * a41 ^ 2 * p32 -
            (7680 : k[X]) * a41 ^ 2 * s1 * w1 +
            (2688 : k[X]) * a41 ^ 2 * u2 +
            (4608 : k[X]) * a41 * b62 * w1 -
            (2304 : k[X]) * a41 * Polynomial.C lambda * p.coeff 2 -
            (7680 : k[X]) * a41 * p.coeff 2 * w1 +
            (6144 : k[X]) * a41 * p32 * s1 -
            (2560 : k[X]) * a41 * q53 -
            (3072 : k[X]) * b62 * p32 +
            (7680 : k[X]) * p.coeff 2 * p32 +
            (6144 : k[X]) * p.coeff 2 * s1 * w1 -
            (3584 : k[X]) * p.coeff 2 * u2 +
            (3072 : k[X]) * q.coeff 3 - (2048 : k[X]) * q41 * w1 -
            (5040 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
              w1 ^ 2 +
            (5760 : k[X]) * a41 * h0 * Polynomial.C lambda * p32 *
              w1 +
            (7680 : k[X]) * a41 * h0 * p.coeff 1 +
            (4800 : k[X]) * a41 * h0 * p32 * w1 ^ 2 +
            (8960 : k[X]) * a41 * h0 * s1 * w1 ^ 3 -
            (6720 : k[X]) * a41 * h0 * u2 * w1 ^ 2 -
            (1920 : k[X]) * b62 * h0 * w1 ^ 3 +
            (2880 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
              w1 ^ 2 -
            (1152 : k[X]) * h0 * Polynomial.C lambda * p32 ^ 2 -
            (4096 : k[X]) * h0 * p.coeff 1 * s1 -
            (3200 : k[X]) * h0 * p.coeff 2 * w1 ^ 3 -
            (3840 : k[X]) * h0 * p32 ^ 2 * w1 -
            (7680 : k[X]) * h0 * p32 * s1 * w1 ^ 2 +
            (5376 : k[X]) * h0 * p32 * u2 * w1 +
            (1920 : k[X]) * h0 * q53 * w1 ^ 2 +
            (3780 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
              w1 ^ 4 -
            (5040 : k[X]) * a41 * h0 ^ 2 * w1 ^ 5 -
            (2304 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
              p.coeff 1 * w1 -
            (3360 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p32 *
              w1 ^ 3 +
            (1920 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 ^ 2 +
            (4200 : k[X]) * h0 ^ 2 * p32 * w1 ^ 4 -
            (2016 : k[X]) * h0 ^ 2 * s1 * w1 ^ 5 +
            (1960 : k[X]) * h0 ^ 2 * u2 * w1 ^ 4 +
            (1536 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 0 -
            (693 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 6 +
            (1320 : k[X]) * h0 ^ 3 * w1 ^ 7) := by
      simpa [hw, ha4s, hp3u, hs, hq7u, hb6s, hq5u, hq4u] using
        twelfthFace_clearedX_zeroP31610 h0 w1 a41 s1 u2 p32 b62 q53
          (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3) lambda
    have hXcof :
        (960 : k[X]) * a41 ^ 3 * Polynomial.C lambda +
            (6400 : k[X]) * a41 ^ 3 * w1 -
            (9600 : k[X]) * a41 ^ 2 * p32 -
            (7680 : k[X]) * a41 ^ 2 * s1 * w1 +
            (2688 : k[X]) * a41 ^ 2 * u2 +
            (4608 : k[X]) * a41 * b62 * w1 -
            (2304 : k[X]) * a41 * Polynomial.C lambda * p.coeff 2 -
            (7680 : k[X]) * a41 * p.coeff 2 * w1 +
            (6144 : k[X]) * a41 * p32 * s1 -
            (2560 : k[X]) * a41 * q53 -
            (3072 : k[X]) * b62 * p32 +
            (7680 : k[X]) * p.coeff 2 * p32 +
            (6144 : k[X]) * p.coeff 2 * s1 * w1 -
            (3584 : k[X]) * p.coeff 2 * u2 +
            (3072 : k[X]) * q.coeff 3 - (2048 : k[X]) * q41 * w1 -
            (5040 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
              w1 ^ 2 +
            (5760 : k[X]) * a41 * h0 * Polynomial.C lambda * p32 *
              w1 +
            (7680 : k[X]) * a41 * h0 * p.coeff 1 +
            (4800 : k[X]) * a41 * h0 * p32 * w1 ^ 2 +
            (8960 : k[X]) * a41 * h0 * s1 * w1 ^ 3 -
            (6720 : k[X]) * a41 * h0 * u2 * w1 ^ 2 -
            (1920 : k[X]) * b62 * h0 * w1 ^ 3 +
            (2880 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
              w1 ^ 2 -
            (1152 : k[X]) * h0 * Polynomial.C lambda * p32 ^ 2 -
            (4096 : k[X]) * h0 * p.coeff 1 * s1 -
            (3200 : k[X]) * h0 * p.coeff 2 * w1 ^ 3 -
            (3840 : k[X]) * h0 * p32 ^ 2 * w1 -
            (7680 : k[X]) * h0 * p32 * s1 * w1 ^ 2 +
            (5376 : k[X]) * h0 * p32 * u2 * w1 +
            (1920 : k[X]) * h0 * q53 * w1 ^ 2 +
            (3780 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
              w1 ^ 4 -
            (5040 : k[X]) * a41 * h0 ^ 2 * w1 ^ 5 -
            (2304 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
              p.coeff 1 * w1 -
            (3360 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p32 *
              w1 ^ 3 +
            (1920 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 ^ 2 +
            (4200 : k[X]) * h0 ^ 2 * p32 * w1 ^ 4 -
            (2016 : k[X]) * h0 ^ 2 * s1 * w1 ^ 5 +
            (1960 : k[X]) * h0 ^ 2 * u2 * w1 ^ 4 +
            (1536 : k[X]) * h0 ^ 3 * Polynomial.C lambda * p.coeff 0 -
            (693 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 6 +
            (1320 : k[X]) * h0 ^ 3 * w1 ^ 7 =
          Polynomial.C eta * h0 ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 32 hh0)
      rw [← hXclr, hXrel]
      ring
    have hzero :
        Polynomial.eval a
            ((960 : k[X]) * a41 ^ 3 * Polynomial.C lambda +
              (6400 : k[X]) * a41 ^ 3 * w1 -
              (9600 : k[X]) * a41 ^ 2 * p32 -
              (7680 : k[X]) * a41 ^ 2 * s1 * w1 +
              (2688 : k[X]) * a41 ^ 2 * u2 +
              (4608 : k[X]) * a41 * b62 * w1 -
              (2304 : k[X]) * a41 * Polynomial.C lambda * p.coeff 2 -
              (7680 : k[X]) * a41 * p.coeff 2 * w1 +
              (6144 : k[X]) * a41 * p32 * s1 -
              (2560 : k[X]) * a41 * q53 -
              (3072 : k[X]) * b62 * p32 +
              (7680 : k[X]) * p.coeff 2 * p32 +
              (6144 : k[X]) * p.coeff 2 * s1 * w1 -
              (3584 : k[X]) * p.coeff 2 * u2 +
              (3072 : k[X]) * q.coeff 3 - (2048 : k[X]) * q41 * w1 -
              (5040 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
                w1 ^ 2 +
              (5760 : k[X]) * a41 * h0 * Polynomial.C lambda * p32 *
                w1 +
              (7680 : k[X]) * a41 * h0 * p.coeff 1 +
              (4800 : k[X]) * a41 * h0 * p32 * w1 ^ 2 +
              (8960 : k[X]) * a41 * h0 * s1 * w1 ^ 3 -
              (6720 : k[X]) * a41 * h0 * u2 * w1 ^ 2 -
              (1920 : k[X]) * b62 * h0 * w1 ^ 3 +
              (2880 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
                w1 ^ 2 -
              (1152 : k[X]) * h0 * Polynomial.C lambda * p32 ^ 2 -
              (4096 : k[X]) * h0 * p.coeff 1 * s1 -
              (3200 : k[X]) * h0 * p.coeff 2 * w1 ^ 3 -
              (3840 : k[X]) * h0 * p32 ^ 2 * w1 -
              (7680 : k[X]) * h0 * p32 * s1 * w1 ^ 2 +
              (5376 : k[X]) * h0 * p32 * u2 * w1 +
              (1920 : k[X]) * h0 * q53 * w1 ^ 2 +
              (3780 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
                w1 ^ 4 -
              (5040 : k[X]) * a41 * h0 ^ 2 * w1 ^ 5 -
              (2304 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                p.coeff 1 * w1 -
              (3360 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p32 *
                w1 ^ 3 +
              (1920 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 ^ 2 +
              (4200 : k[X]) * h0 ^ 2 * p32 * w1 ^ 4 -
              (2016 : k[X]) * h0 ^ 2 * s1 * w1 ^ 5 +
              (1960 : k[X]) * h0 ^ 2 * u2 * w1 ^ 4 +
              (1536 : k[X]) * h0 ^ 3 * Polynomial.C lambda *
                p.coeff 0 -
              (693 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 6 +
              (1320 : k[X]) * h0 ^ 3 * w1 ^ 7) = 0 := by
      rw [hXcof]
      simp [hroot]
    have hXeval :=
      (eval_twelfthFace_X_cofactor610 h0 w1 a41 s1 u2 p32 b62 q53
        (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3) lambda a
        hroot).symm.trans hzero
    have hUred :
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
          (30 : k) * (p.coeff 2).eval a = 0 :=
      eleventhFace_zeroP31_load610 (w1.eval a) (a41.eval a)
        (p31.eval a) (b62.eval a) ((p.coeff 2).eval a) lambda hp31z
        hUload
    have hQ3form :=
      twelfthFace_zeroP31_X_nextOrder610 (w1.eval a) (a41.eval a)
        (s1.eval a) (p32.eval a) (u2.eval a) (b62.eval a)
        (q53.eval a) ((p.coeff 2).eval a) (q41.eval a)
        ((q.coeff 3).eval a) lambda hMs hTform hUred hWform hVform
        hXeval
    exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      hTform, hWform, hVform, hQ3form⟩⟩
  · -- Complementary factor: sixth defect at the next order.
    obtain ⟨zeta, hWrel⟩ :=
      nonzeroFace610_sixthDefectPowerRelation p q H h0 j lambda
        hp hq hh0 hH hp6 hq10 hN hD
    have hW0z : ((583200 : k[X]) * p31 ^ 2 -
        (489888 : k[X]) * p31 * u1 +
        (419904 : k[X]) * q.coeff 4).eval a = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
      linear_combination (-163296 : k) * p31.eval a * hTu +
        (46656 : k) * hWq
    obtain ⟨omega, homega⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        ((583200 : k[X]) * p31 ^ 2 - (489888 : k[X]) * p31 * u1 +
          (419904 : k[X]) * q.coeff 4) a hh0degree hroot hW0z
    have hWclr :
        localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda =
          h0 ^ 27 * (omega + (-(518400 : k[X]) * a41 ^ 3 +
            (466560 : k[X]) * a41 ^ 2 * s1 -
            (419904 : k[X]) * a41 * b62 -
            (349920 : k[X]) * a41 * Polynomial.C lambda * p31 +
            (1166400 : k[X]) * a41 * p.coeff 2 -
            (1360800 : k[X]) * a41 * p31 * w1 +
            (816480 : k[X]) * a41 * u1 * w1 -
            (559872 : k[X]) * p.coeff 2 * s1 +
            (933120 : k[X]) * p31 * s1 * w1 -
            (349920 : k[X]) * q52 * w1 +
            (466560 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
              w1 +
            (518400 : k[X]) * a41 ^ 2 * h0 * w1 ^ 2 -
            (1244160 : k[X]) * a41 * h0 * s1 * w1 ^ 2 +
            (349920 : k[X]) * b62 * h0 * w1 ^ 2 -
            (349920 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
              w1 +
            (466560 : k[X]) * h0 * Polynomial.C lambda * p31 *
              w1 ^ 2 +
            (194400 : k[X]) * h0 * p.coeff 2 * w1 ^ 2 -
            (432000 : k[X]) * h0 * p31 * w1 ^ 3 -
            (362880 : k[X]) * h0 * u1 * w1 ^ 3 -
            (570240 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
              w1 ^ 3 +
            (633600 : k[X]) * a41 * h0 ^ 2 * w1 ^ 4 +
            (209952 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
              p.coeff 1 +
            (116640 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 +
            (380160 : k[X]) * h0 ^ 2 * s1 * w1 ^ 4 +
            (133056 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 ^ 3 * p.coeff 0 -
            (246400 : k[X]) * h0 ^ 3 * w1 ^ 6)) := by
      simpa [hw, ha4s, hp3, hs, hu, hb6s, hq5] using
        twelfthFace_comp_sixthDefect_omega610 h0 w1 a41 s1 u1 p31 b62
          q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) omega
          lambda homega
    have hWcof :
        omega + (-(518400 : k[X]) * a41 ^ 3 +
            (466560 : k[X]) * a41 ^ 2 * s1 -
            (419904 : k[X]) * a41 * b62 -
            (349920 : k[X]) * a41 * Polynomial.C lambda * p31 +
            (1166400 : k[X]) * a41 * p.coeff 2 -
            (1360800 : k[X]) * a41 * p31 * w1 +
            (816480 : k[X]) * a41 * u1 * w1 -
            (559872 : k[X]) * p.coeff 2 * s1 +
            (933120 : k[X]) * p31 * s1 * w1 -
            (349920 : k[X]) * q52 * w1 +
            (466560 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
              w1 +
            (518400 : k[X]) * a41 ^ 2 * h0 * w1 ^ 2 -
            (1244160 : k[X]) * a41 * h0 * s1 * w1 ^ 2 +
            (349920 : k[X]) * b62 * h0 * w1 ^ 2 -
            (349920 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
              w1 +
            (466560 : k[X]) * h0 * Polynomial.C lambda * p31 *
              w1 ^ 2 +
            (194400 : k[X]) * h0 * p.coeff 2 * w1 ^ 2 -
            (432000 : k[X]) * h0 * p31 * w1 ^ 3 -
            (362880 : k[X]) * h0 * u1 * w1 ^ 3 -
            (570240 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
              w1 ^ 3 +
            (633600 : k[X]) * a41 * h0 ^ 2 * w1 ^ 4 +
            (209952 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
              p.coeff 1 +
            (116640 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 +
            (380160 : k[X]) * h0 ^ 2 * s1 * w1 ^ 4 +
            (133056 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 ^ 3 * p.coeff 0 -
            (246400 : k[X]) * h0 ^ 3 * w1 ^ 6) =
          Polynomial.C zeta * h0 ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 27 hh0)
      rw [← hWclr, hWrel]
      ring
    have hzero :
        Polynomial.eval a
            (omega + (-(518400 : k[X]) * a41 ^ 3 +
              (466560 : k[X]) * a41 ^ 2 * s1 -
              (419904 : k[X]) * a41 * b62 -
              (349920 : k[X]) * a41 * Polynomial.C lambda * p31 +
              (1166400 : k[X]) * a41 * p.coeff 2 -
              (1360800 : k[X]) * a41 * p31 * w1 +
              (816480 : k[X]) * a41 * u1 * w1 -
              (559872 : k[X]) * p.coeff 2 * s1 +
              (933120 : k[X]) * p31 * s1 * w1 -
              (349920 : k[X]) * q52 * w1 +
              (466560 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
                w1 +
              (518400 : k[X]) * a41 ^ 2 * h0 * w1 ^ 2 -
              (1244160 : k[X]) * a41 * h0 * s1 * w1 ^ 2 +
              (349920 : k[X]) * b62 * h0 * w1 ^ 2 -
              (349920 : k[X]) * h0 * Polynomial.C lambda *
                p.coeff 2 * w1 +
              (466560 : k[X]) * h0 * Polynomial.C lambda * p31 *
                w1 ^ 2 +
              (194400 : k[X]) * h0 * p.coeff 2 * w1 ^ 2 -
              (432000 : k[X]) * h0 * p31 * w1 ^ 3 -
              (362880 : k[X]) * h0 * u1 * w1 ^ 3 -
              (570240 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
                w1 ^ 3 +
              (633600 : k[X]) * a41 * h0 ^ 2 * w1 ^ 4 +
              (209952 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                p.coeff 1 +
              (116640 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 +
              (380160 : k[X]) * h0 ^ 2 * s1 * w1 ^ 4 +
              (133056 : k[X]) * h0 ^ 3 * Polynomial.C lambda *
                w1 ^ 5 -
              (699840 : k[X]) * h0 ^ 3 * p.coeff 0 -
              (246400 : k[X]) * h0 ^ 3 * w1 ^ 6)) = 0 := by
      rw [hWcof]
      simp [hroot]
    have hWeval :=
      (eval_twelfthFace_comp_W_cofactor610 h0 w1 a41 s1 u1 p31 b62
        q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) omega lambda a
        hroot).symm.trans hzero
    have homegaval :=
      twelfthFace_tp2_W_nextOrder610 (w1.eval a) (a41.eval a)
        (s1.eval a) (u1.eval a) (p31.eval a) (b62.eval a)
        (q52.eval a) ((p.coeff 2).eval a) (omega.eval a) lambda hMs
        hTu hVq htp hb62form hWeval
    exact Or.inr ⟨htp, hb62form, omega, homega, homegaval⟩

set_option maxHeartbeats 8000000 in
/-- Source-facing twelfth-face power jet of a normalized scale-two
`(6,10)` nonzero face: both eleventh-face alternatives are refined. -/
theorem normalized610ScaleTwo_nonzeroFace_twelfthPowerJet
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
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : K[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                h0 ^ 2 ∣ p.coeff 3 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
                h0 ^ 3 ∣ q.coeff 5 ∧ h0 ∣ q.coeff 4 ∧
                (18 : K) * u2.eval a - (30 : K) * p32.eval a -
                    (20 : K) * a41.eval a * w1.eval a +
                  (9 : K) * lambda * a41.eval a = 0 ∧
                (81 : K) * q41.eval a -
                    (90 : K) * a41.eval a * (p.coeff 2).eval a +
                  (5 : K) * (a41.eval a) ^ 3 = 0 ∧
                (216 : K) * q53.eval a +
                    (27 : K) * lambda * (a41.eval a) ^ 2 +
                  (40 : K) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : K) * a41.eval a * p32.eval a +
                  (108 : K) * lambda * (p.coeff 2).eval a -
                    (240 : K) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : K) * (q.coeff 3).eval a -
                    (81 : K) * lambda * (a41.eval a) ^ 3 -
                  (320 : K) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : K) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : K) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : K) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : K) * (p.coeff 2).eval a * p32.eval a =
                    0) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            ∃ omega : K[X],
              (583200 : K[X]) * p31 ^ 2 -
                  (489888 : K[X]) * p31 * u1 +
                (419904 : K[X]) * q.coeff 4 = h0 * omega ∧
              omega.eval a =
                (648 : K) * a41.eval a *
                  ((80 : K) * (a41.eval a) ^ 2 +
                      (297 : K) * lambda * p31.eval a -
                    (960 : K) * p31.eval a * w1.eval a))) ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, w1, a41, s1, u1, p31, b62, q52, hh0, hlambda,
    hh0degree, hH, hroot, hw, ha4s, hp3, hs, hu, hb6s, hq5, hq9, hp5d,
    hp4d, hp3d, hq8d, hq7d, hq6d, hq5d, hMs, hTu, hVq, hWq, hUload,
    hXalt, hN'⟩ :=
    normalized610ScaleTwo_nonzeroFace_tenthPowerJet hsource hnonzero
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
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', hwN, ha4sN, hp3N, hsN,
    huN, hb6sN, hq5N, hMs', hTu', hVq', hWq', hUload', halt⟩ :=
    nonzeroFace610_linearRoot_twelfthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  refine ⟨h0, lambda, a, w1', a41', s1', u1', p31', b62', q52', hh0,
    hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN, huN, hb6sN,
    hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', ?_, hN'⟩
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      hTform, hWform, hVform, hQ3form⟩⟩ |
      ⟨htp, hb62form, omega, homega, homegaval⟩
  · exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      (by rw [hp3u]; exact dvd_mul_right _ _),
      (by rw [hq7u]; exact dvd_mul_right _ _),
      (by rw [hq5u]; exact dvd_mul_right _ _),
      (by rw [hq4u]; exact dvd_mul_right _ _),
      hTform, hWform, hVform, hQ3form⟩⟩
  · exact Or.inr ⟨htp, hb62form, omega, homega, homegaval⟩

end NonzeroTwelfthFace610

#print axioms twelfthCoefficientJacobianRow_610
#print axioms twelfthFace_zeroP31_X_nextOrder610
#print axioms twelfthFace_tp2_W_nextOrder610
#print axioms twelfthFace_clearedX_zeroP31610
#print axioms eval_twelfthFace_X_cofactor610
#print axioms twelfthFace_comp_clearedW_grouped610
#print axioms twelfthFace_comp_sixthDefect_omega610
#print axioms eval_twelfthFace_comp_W_cofactor610
#print axioms nonzeroFace610_linearRoot_twelfthPowerJet
#print axioms normalized610ScaleTwo_nonzeroFace_twelfthPowerJet

end Max11DegreeRoutes
