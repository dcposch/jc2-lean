import LowScale610ScaleTwoTenthFace

/-! # Scale-two eleventh face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the tenth-face packet supplies the degree-`5`
Jacobian row and the collapsed jet `h⁵ ∣ p₅`, `h³ ∣ p₄`, `h ∣ p₃`,
`h⁷ ∣ q₈`, `h⁵ ∣ q₇`, `h⁴ ∣ q₆`, `h² ∣ q₅`, `h⁸ ∣ q₉` together with
`3 s₁(a) = 5 a₄₁(a)`, `3 u₁(a) = 5 p₃₁(a)`, `9 q₅₂(a) = 10 a₄₁(a) p₃₁(a)`,
`9 q₄(a) = 5 p₃₁(a)²`, the source-facing load
`10 a₄₁² - 18 b₆₂ - 9 λ p₃₁ + 30 p₂ + 20 p₃₁ w₁ = 0`, and the
alternative `p₃₁ (240 p₂ - 40 a₄₁² - 27 λ p₃₁ - 40 p₃₁ w₁) = 0`.

The next unused Keller coefficient is the degree-`4` Jacobian row.  After
the same sextic depression that kills `z⁵`, that row is
`5 S E' + 4 T D' + 3 U C' + 2 V B' + W A' - E S' - 2 D T' - 3 C U'
- 4 B V' - 5 A W' - 8 X' = 0`.  Clearing the corresponding first integral
against the remaining decic coordinate produces a defect larger than the
remaining exact jet, so this file isolates that Jacobian identity and the
strongest exact source-facing refinement of the tenth-face alternative.

The alternative splits the nonzero face.  On `p₃₁(a) = 0` the tenth-face
laws upgrade the jet to `h² ∣ p₃`, `h⁶ ∣ q₇`, `h³ ∣ q₅`, `h ∣ q₄`, and
the third, fifth, and sixth defects at the next order force
`18 u₂ - 30 p₃₂ = a₄₁ (20 w₁ - 9 λ)`,
`81 q₄₁ = 5 a₄₁ (18 p₂ - a₄₁²)`, and
`216 q₅₃ + 27 λ a₄₁² + 40 a₄₁² w₁ - 240 a₄₁ p₃₂ + 108 λ p₂ - 240 p₂ w₁ = 0`
at the root of `h`.  On the complementary factor the same alternative
solves `p₂` and `b₆₂` exactly.  Neither factor is closed further: the
`p₃₁ ≠ 0` sibling and the aligned face `N = 0` remain open, and no
individual vanishing of `p₂, p₁, p₀, q₃` (nor of `w₁, a₄₁`) is claimed.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The eleventh row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the tenth face start
at degree `4`. -/
theorem eleventhCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
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
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  rw [hC2, hC3, hC4, hC5]
  linear_combination hcoeff

/-! ## Scalar algebra of the tenth-face alternative -/

section EleventhFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- On `p₃₁ = 0` the tenth-face load reduces to a relation among
`a₄₁`, `b₆₂`, and `p₂`. -/
theorem eleventhFace_zeroP31_load610 (w1 a41 p31 b62 p2 : F) (lambda : F)
    (hp31 : p31 = 0)
    (hL : (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lambda * p31 +
        (30 : F) * p2 + (20 : F) * p31 * w1 = 0) :
    (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0 := by
  simpa [hp31] using hL

/-- The third defect at the next order on the `p₃₁ = 0` jet is
`18 u₂ - 30 p₃₂ = a₄₁ (20 w₁ - 9 λ)`. -/
theorem eleventhFace_zeroP31_T_nextOrder610 (w1 a41 s1 p32 u2 : F)
    (lambda : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (324 : F) * a41 * lambda + (720 : F) * a41 * w1 -
        (1080 : F) * p32 - (864 : F) * s1 * w1 + (648 : F) * u2 = 0) :
    (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
      (9 : F) * lambda * a41 = 0 := by
  have h36 : (36 : F) ≠ 0 := by norm_num
  have hid :
      (36 : F) * ((18 : F) * u2 - (30 : F) * p32 -
          (20 : F) * a41 * w1 + (9 : F) * lambda * a41) =
        (324 : F) * a41 * lambda + (720 : F) * a41 * w1 -
          (1080 : F) * p32 - (864 : F) * s1 * w1 + (648 : F) * u2 +
        (48 : F) * w1 * ((18 : F) * s1 - (30 : F) * a41) := by
    ring
  have hcomb :
      (36 : F) * ((18 : F) * u2 - (30 : F) * p32 -
          (20 : F) * a41 * w1 + (9 : F) * lambda * a41) = 0 := by
    rw [hid]
    linear_combination hT + (48 : F) * w1 * hM
  exact (mul_eq_zero.mp hcomb).resolve_left h36

/-- The fourth defect at the next order on the `p₃₁ = 0` jet recovers
the reduced load. -/
theorem eleventhFace_zeroP31_U_nextOrder610 (a41 s1 b62 p2 : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 - (720 : F) * p2 = 0) :
    (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0 := by
  have h24 : (24 : F) ≠ 0 := by norm_num
  have hid :
      -(24 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 +
          (30 : F) * p2) =
        (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
          (432 : F) * b62 - (720 : F) * p2 +
        (32 : F) * a41 * ((18 : F) * s1 - (30 : F) * a41) := by
    ring
  have hcomb :
      -(24 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 +
          (30 : F) * p2) = 0 := by
    rw [hid]
    linear_combination hU + (32 : F) * a41 * hM
  have : (24 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 +
      (30 : F) * p2) = 0 := by
    linear_combination -hcomb
  exact (mul_eq_zero.mp this).resolve_left h24

set_option maxHeartbeats 4000000 in
/-- The sixth defect at the next order on the `p₃₁ = 0` jet is
`81 q₄₁ = 5 a₄₁ (18 p₂ - a₄₁²)`. -/
theorem eleventhFace_zeroP31_W_nextOrder610 (a41 s1 b62 p2 q41 : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 - (720 : F) * p2 = 0)
    (hW : -(518400 : F) * a41 ^ 3 + (466560 : F) * a41 ^ 2 * s1 -
        (419904 : F) * a41 * b62 + (1166400 : F) * a41 * p2 -
        (559872 : F) * p2 * s1 + (419904 : F) * q41 = 0) :
    (81 : F) * q41 - (90 : F) * a41 * p2 + (5 : F) * a41 ^ 3 = 0 := by
  have hs := tenthFace_M_nextOrder610 a41 s1 hM
  have hL :=
    eleventhFace_zeroP31_U_nextOrder610 a41 s1 b62 p2 hM hU
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h5184 : (5184 : F) ≠ 0 := by norm_num
  have hs1 : s1 = (5 / 3 : F) * a41 := by
    have hid : (3 : F) * (s1 - (5 / 3 : F) * a41) =
        (3 : F) * s1 - (5 : F) * a41 := by ring
    have : (3 : F) * (s1 - (5 / 3 : F) * a41) = 0 := by
      rw [hid]
      linear_combination hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)
  have hb62 : b62 = (5 / 9 : F) * a41 ^ 2 + (5 / 3 : F) * p2 := by
    have hid : (18 : F) * (b62 - ((5 / 9 : F) * a41 ^ 2 +
            (5 / 3 : F) * p2)) =
        -((10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2) := by
      ring
    have : (18 : F) * (b62 - ((5 / 9 : F) * a41 ^ 2 +
            (5 / 3 : F) * p2)) = 0 := by
      rw [hid]
      linear_combination -hL
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h18)
  have hW2 :
      -(518400 : F) * a41 ^ 3 + (466560 : F) * a41 ^ 2 * s1 -
          (419904 : F) * a41 * b62 + (1166400 : F) * a41 * p2 -
          (559872 : F) * p2 * s1 + (419904 : F) * q41 =
        (5184 : F) * ((81 : F) * q41 - (90 : F) * a41 * p2 +
          (5 : F) * a41 ^ 3) := by
    simp only [hs1, hb62]
    ring
  have : (5184 : F) * ((81 : F) * q41 - (90 : F) * a41 * p2 +
      (5 : F) * a41 ^ 3) = 0 := by
    rw [← hW2, hW]
  exact (mul_eq_zero.mp this).resolve_left h5184

set_option maxHeartbeats 4000000 in
/-- The fifth defect at the next order on the `p₃₁ = 0` jet, after the
third-defect law, determines `(q₅ / h³)(a)`. -/
theorem eleventhFace_zeroP31_V_nextOrder610 (w1 a41 s1 p32 u2 b62 q53 p2 :
    F) (lambda : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (324 : F) * a41 * lambda + (720 : F) * a41 * w1 -
        (1080 : F) * p32 - (864 : F) * s1 * w1 + (648 : F) * u2 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 - (720 : F) * p2 = 0)
    (hV : -(42768 : F) * a41 ^ 2 * lambda - (190080 : F) * a41 ^ 2 * w1 +
        (285120 : F) * a41 * p32 + (228096 : F) * a41 * s1 * w1 -
        (108864 : F) * a41 * u2 - (93312 : F) * b62 * w1 +
        (46656 : F) * lambda * p2 + (51840 : F) * p2 * w1 -
        (124416 : F) * p32 * s1 + (93312 : F) * q53 = 0) :
    (216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
      (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
      (108 : F) * lambda * p2 - (240 : F) * p2 * w1 = 0 := by
  have hs := tenthFace_M_nextOrder610 a41 s1 hM
  have hTu :=
    eleventhFace_zeroP31_T_nextOrder610 w1 a41 s1 p32 u2 lambda hM hT
  have hL :=
    eleventhFace_zeroP31_U_nextOrder610 a41 s1 b62 p2 hM hU
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have hs1 : s1 = (5 / 3 : F) * a41 := by
    have hid : (3 : F) * (s1 - (5 / 3 : F) * a41) =
        (3 : F) * s1 - (5 : F) * a41 := by ring
    have : (3 : F) * (s1 - (5 / 3 : F) * a41) = 0 := by
      rw [hid]
      linear_combination hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)
  have hu2 : u2 = ((30 : F) * p32 + (20 : F) * a41 * w1 -
        (9 : F) * lambda * a41) / (18 : F) := by
    have hid : (18 : F) * (u2 - ((30 : F) * p32 + (20 : F) * a41 * w1 -
            (9 : F) * lambda * a41) / (18 : F)) =
        (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
          (9 : F) * lambda * a41 := by
      ring
    have : (18 : F) * (u2 - ((30 : F) * p32 + (20 : F) * a41 * w1 -
            (9 : F) * lambda * a41) / (18 : F)) = 0 := by
      rw [hid]
      linear_combination hTu
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h18)
  have hb62 : b62 = (5 / 9 : F) * a41 ^ 2 + (5 / 3 : F) * p2 := by
    have hid : (18 : F) * (b62 - ((5 / 9 : F) * a41 ^ 2 +
            (5 / 3 : F) * p2)) =
        -((10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2) := by
      ring
    have : (18 : F) * (b62 - ((5 / 9 : F) * a41 ^ 2 +
            (5 / 3 : F) * p2)) = 0 := by
      rw [hid]
      linear_combination -hL
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h18)
  have hV2 :
      -(42768 : F) * a41 ^ 2 * lambda - (190080 : F) * a41 ^ 2 * w1 +
          (285120 : F) * a41 * p32 + (228096 : F) * a41 * s1 * w1 -
          (108864 : F) * a41 * u2 - (93312 : F) * b62 * w1 +
          (46656 : F) * lambda * p2 + (51840 : F) * p2 * w1 -
          (124416 : F) * p32 * s1 + (93312 : F) * q53 =
        (432 : F) * ((216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
            (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
            (108 : F) * lambda * p2 - (240 : F) * p2 * w1) := by
    simp only [hs1, hu2, hb62]
    ring
  have :
      (432 : F) * ((216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
          (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
          (108 : F) * lambda * p2 - (240 : F) * p2 * w1) = 0 := by
    rw [← hV2, hV]
  exact (mul_eq_zero.mp this).resolve_left h432

/-- Combined next-order identities of the `p₃₁ = 0` jet. -/
theorem eleventhFace_zeroP31_nextOrder610 (w1 a41 s1 p32 u2 b62 q53 p2
    q41 : F) (lambda : F)
    (hM : (18 : F) * s1 - (30 : F) * a41 = 0)
    (hT : (324 : F) * a41 * lambda + (720 : F) * a41 * w1 -
        (1080 : F) * p32 - (864 : F) * s1 * w1 + (648 : F) * u2 = 0)
    (hU : (720 : F) * a41 ^ 2 - (576 : F) * a41 * s1 +
        (432 : F) * b62 - (720 : F) * p2 = 0)
    (hV : -(42768 : F) * a41 ^ 2 * lambda - (190080 : F) * a41 ^ 2 * w1 +
        (285120 : F) * a41 * p32 + (228096 : F) * a41 * s1 * w1 -
        (108864 : F) * a41 * u2 - (93312 : F) * b62 * w1 +
        (46656 : F) * lambda * p2 + (51840 : F) * p2 * w1 -
        (124416 : F) * p32 * s1 + (93312 : F) * q53 = 0)
    (hW : -(518400 : F) * a41 ^ 3 + (466560 : F) * a41 ^ 2 * s1 -
        (419904 : F) * a41 * b62 + (1166400 : F) * a41 * p2 -
        (559872 : F) * p2 * s1 + (419904 : F) * q41 = 0) :
    (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
        (9 : F) * lambda * a41 = 0 ∧
      (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0 ∧
      (81 : F) * q41 - (90 : F) * a41 * p2 + (5 : F) * a41 ^ 3 = 0 ∧
      (216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
        (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
        (108 : F) * lambda * p2 - (240 : F) * p2 * w1 = 0 :=
  ⟨eleventhFace_zeroP31_T_nextOrder610 w1 a41 s1 p32 u2 lambda hM hT,
    eleventhFace_zeroP31_U_nextOrder610 a41 s1 b62 p2 hM hU,
    eleventhFace_zeroP31_W_nextOrder610 a41 s1 b62 p2 q41 hM hU hW,
    eleventhFace_zeroP31_V_nextOrder610 w1 a41 s1 p32 u2 b62 q53 p2
      lambda hM hT hU hV⟩

/-- On the complementary factor of the tenth-face alternative, `p₂` is
exact. -/
theorem eleventhFace_tp2_p2_610 (a41 p31 w1 p2 : F) (lambda : F)
    (hp31 : p31 ≠ 0)
    (hX : p31 * ((240 : F) * p2 - (40 : F) * a41 ^ 2 -
        (27 : F) * lambda * p31 - (40 : F) * p31 * w1) = 0) :
    (240 : F) * p2 - (40 : F) * a41 ^ 2 - (27 : F) * lambda * p31 -
      (40 : F) * p31 * w1 = 0 :=
  (mul_eq_zero.mp hX).resolve_left hp31

/-- The tenth-face load together with the complementary factor solves
`b₆₂`. -/
theorem eleventhFace_tp2_b62_610 (w1 a41 p31 b62 p2 : F) (lambda : F)
    (hL : (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lambda * p31 +
        (30 : F) * p2 + (20 : F) * p31 * w1 = 0)
    (hX : (240 : F) * p2 - (40 : F) * a41 ^ 2 -
        (27 : F) * lambda * p31 - (40 : F) * p31 * w1 = 0) :
    (144 : F) * b62 - (120 : F) * a41 ^ 2 + (45 : F) * lambda * p31 -
      (200 : F) * p31 * w1 = 0 := by
  have hid :
      -((144 : F) * b62 - (120 : F) * a41 ^ 2 +
            (45 : F) * lambda * p31 - (200 : F) * p31 * w1) =
        (8 : F) * ((10 : F) * a41 ^ 2 - (18 : F) * b62 -
            (9 : F) * lambda * p31 + (30 : F) * p2 +
            (20 : F) * p31 * w1) -
          ((240 : F) * p2 - (40 : F) * a41 ^ 2 -
            (27 : F) * lambda * p31 - (40 : F) * p31 * w1) := by
    ring
  have hcomb :
      -((144 : F) * b62 - (120 : F) * a41 ^ 2 +
            (45 : F) * lambda * p31 - (200 : F) * p31 * w1) = 0 := by
    rw [hid]
    linear_combination (8 : F) * hL - hX
  linear_combination -hcomb

/-! ## Extra-`h` substitutions of the cleared defects on `p₃₁ = 0` -/

theorem eleventhFace_clearedT_zeroP31610 (h w1 a41 s1 u2 p32 : F[X])
    (lambda : F) :
    localClearedThirdDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) (h ^ 7 * s1) (h ^ 6 * u2) lambda =
      h ^ 14 * ((648 : F[X]) * u2 - (1080 : F[X]) * p32 +
        (324 : F[X]) * a41 * Polynomial.C lambda +
        (720 : F[X]) * a41 * w1 - (864 : F[X]) * s1 * w1 -
        (351 : F[X]) * Polynomial.C lambda * h * w1 ^ 2 +
        (520 : F[X]) * h * w1 ^ 3) := by
  simp only [localClearedThirdDefect610]
  ring

set_option maxHeartbeats 4000000 in
theorem eleventhFace_clearedU_zeroP31610 (h w1 a41 s1 u2 p32 b62 p2 :
    F[X]) (lambda : F) :
    localClearedFourthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        lambda =
      h ^ 18 * ((720 : F[X]) * a41 ^ 2 - (576 : F[X]) * a41 * s1 +
        (432 : F[X]) * b62 - (720 : F[X]) * p2 -
        (432 : F[X]) * a41 * h * Polynomial.C lambda * w1 +
        (216 : F[X]) * h * Polynomial.C lambda * p32 +
        (360 : F[X]) * h * p32 * w1 + (576 : F[X]) * h * s1 * w1 ^ 2 -
        (504 : F[X]) * h * u2 * w1 +
        (216 : F[X]) * h ^ 2 * Polynomial.C lambda * w1 ^ 3 -
        (360 : F[X]) * h ^ 2 * w1 ^ 4) := by
  simp only [localClearedFourthDefect610]
  ring

set_option maxHeartbeats 8000000 in
theorem eleventhFace_clearedV_zeroP31610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 : F[X]) (lambda : F) :
    localClearedFifthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) lambda =
      h ^ 23 * (-(42768 : F[X]) * a41 ^ 2 * Polynomial.C lambda -
        (190080 : F[X]) * a41 ^ 2 * w1 + (285120 : F[X]) * a41 * p32 +
        (228096 : F[X]) * a41 * s1 * w1 - (108864 : F[X]) * a41 * u2 -
        (93312 : F[X]) * b62 * w1 +
        (46656 : F[X]) * Polynomial.C lambda * p2 +
        (51840 : F[X]) * p2 * w1 - (124416 : F[X]) * p32 * s1 +
        (93312 : F[X]) * q53 +
        (121176 : F[X]) * a41 * h * Polynomial.C lambda * w1 ^ 2 -
        (89760 : F[X]) * a41 * h * w1 ^ 3 -
        (85536 : F[X]) * h * Polynomial.C lambda * p32 * w1 -
        (155520 : F[X]) * h * p1 + (23760 : F[X]) * h * p32 * w1 ^ 2 -
        (107712 : F[X]) * h * s1 * w1 ^ 3 +
        (99792 : F[X]) * h * u2 * w1 ^ 2 -
        (38709 : F[X]) * h ^ 2 * Polynomial.C lambda * w1 ^ 4 +
        (68816 : F[X]) * h ^ 2 * w1 ^ 5) := by
  simp only [localClearedFifthDefect610]
  ring

set_option maxHeartbeats 12000000 in
theorem eleventhFace_clearedW_zeroP31610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 p0 q41 : F[X]) (lambda : F) :
    localClearedSixthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) lambda =
      h ^ 27 * (-(518400 : F[X]) * a41 ^ 3 +
        (466560 : F[X]) * a41 ^ 2 * s1 - (419904 : F[X]) * a41 * b62 +
        (1166400 : F[X]) * a41 * p2 - (559872 : F[X]) * p2 * s1 +
        (419904 : F[X]) * q41 +
        (466560 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 +
        (518400 : F[X]) * a41 ^ 2 * h * w1 ^ 2 -
        (349920 : F[X]) * a41 * h * Polynomial.C lambda * p32 -
        (1360800 : F[X]) * a41 * h * p32 * w1 -
        (1244160 : F[X]) * a41 * h * s1 * w1 ^ 2 +
        (816480 : F[X]) * a41 * h * u2 * w1 +
        (349920 : F[X]) * b62 * h * w1 ^ 2 -
        (349920 : F[X]) * h * Polynomial.C lambda * p2 * w1 +
        (194400 : F[X]) * h * p2 * w1 ^ 2 +
        (583200 : F[X]) * h * p32 ^ 2 +
        (933120 : F[X]) * h * p32 * s1 * w1 -
        (489888 : F[X]) * h * p32 * u2 - (349920 : F[X]) * h * q53 * w1 -
        (570240 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 3 +
        (633600 : F[X]) * a41 * h ^ 2 * w1 ^ 4 +
        (209952 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 +
        (466560 : F[X]) * h ^ 2 * Polynomial.C lambda * p32 * w1 ^ 2 +
        (116640 : F[X]) * h ^ 2 * p1 * w1 -
        (432000 : F[X]) * h ^ 2 * p32 * w1 ^ 3 +
        (380160 : F[X]) * h ^ 2 * s1 * w1 ^ 4 -
        (362880 : F[X]) * h ^ 2 * u2 * w1 ^ 3 +
        (133056 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 5 -
        (699840 : F[X]) * h ^ 3 * p0 -
        (246400 : F[X]) * h ^ 3 * w1 ^ 6) := by
  simp only [localClearedSixthDefect610]
  ring

theorem eval_eleventhFace_T_cofactor610 (h w1 a41 s1 u2 p32 : F[X])
    (lambda : F) (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((648 : F[X]) * u2 - (1080 : F[X]) * p32 +
          (324 : F[X]) * a41 * Polynomial.C lambda +
          (720 : F[X]) * a41 * w1 - (864 : F[X]) * s1 * w1 -
          (351 : F[X]) * Polynomial.C lambda * h * w1 ^ 2 +
          (520 : F[X]) * h * w1 ^ 3) =
      (648 : F) * Polynomial.eval root u2 -
        (1080 : F) * Polynomial.eval root p32 +
        (324 : F) * Polynomial.eval root a41 * lambda +
        (720 : F) * Polynomial.eval root a41 * Polynomial.eval root w1 -
        (864 : F) * Polynomial.eval root s1 *
          Polynomial.eval root w1 := by
  simp [hroot]

theorem eval_eleventhFace_U_cofactor610 (h w1 a41 s1 u2 p32 b62 p2 :
    F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((720 : F[X]) * a41 ^ 2 - (576 : F[X]) * a41 * s1 +
          (432 : F[X]) * b62 - (720 : F[X]) * p2 -
          (432 : F[X]) * a41 * h * Polynomial.C lambda * w1 +
          (216 : F[X]) * h * Polynomial.C lambda * p32 +
          (360 : F[X]) * h * p32 * w1 +
          (576 : F[X]) * h * s1 * w1 ^ 2 -
          (504 : F[X]) * h * u2 * w1 +
          (216 : F[X]) * h ^ 2 * Polynomial.C lambda * w1 ^ 3 -
          (360 : F[X]) * h ^ 2 * w1 ^ 4) =
      (720 : F) * (Polynomial.eval root a41) ^ 2 -
        (576 : F) * Polynomial.eval root a41 * Polynomial.eval root s1 +
        (432 : F) * Polynomial.eval root b62 -
        (720 : F) * Polynomial.eval root p2 := by
  simp [hroot]

theorem eval_eleventhFace_V_cofactor610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (-(42768 : F[X]) * a41 ^ 2 * Polynomial.C lambda -
          (190080 : F[X]) * a41 ^ 2 * w1 +
          (285120 : F[X]) * a41 * p32 +
          (228096 : F[X]) * a41 * s1 * w1 -
          (108864 : F[X]) * a41 * u2 - (93312 : F[X]) * b62 * w1 +
          (46656 : F[X]) * Polynomial.C lambda * p2 +
          (51840 : F[X]) * p2 * w1 - (124416 : F[X]) * p32 * s1 +
          (93312 : F[X]) * q53 +
          (121176 : F[X]) * a41 * h * Polynomial.C lambda * w1 ^ 2 -
          (89760 : F[X]) * a41 * h * w1 ^ 3 -
          (85536 : F[X]) * h * Polynomial.C lambda * p32 * w1 -
          (155520 : F[X]) * h * p1 +
          (23760 : F[X]) * h * p32 * w1 ^ 2 -
          (107712 : F[X]) * h * s1 * w1 ^ 3 +
          (99792 : F[X]) * h * u2 * w1 ^ 2 -
          (38709 : F[X]) * h ^ 2 * Polynomial.C lambda * w1 ^ 4 +
          (68816 : F[X]) * h ^ 2 * w1 ^ 5) =
      -(42768 : F) * (Polynomial.eval root a41) ^ 2 * lambda -
        (190080 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root w1 +
        (285120 : F) * Polynomial.eval root a41 *
          Polynomial.eval root p32 +
        (228096 : F) * Polynomial.eval root a41 *
          Polynomial.eval root s1 * Polynomial.eval root w1 -
        (108864 : F) * Polynomial.eval root a41 *
          Polynomial.eval root u2 -
        (93312 : F) * Polynomial.eval root b62 *
          Polynomial.eval root w1 +
        (46656 : F) * lambda * Polynomial.eval root p2 +
        (51840 : F) * Polynomial.eval root p2 *
          Polynomial.eval root w1 -
        (124416 : F) * Polynomial.eval root p32 *
          Polynomial.eval root s1 +
        (93312 : F) * Polynomial.eval root q53 := by
  simp [hroot]

theorem eval_eleventhFace_W_cofactor610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 p0 q41 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (-(518400 : F[X]) * a41 ^ 3 + (466560 : F[X]) * a41 ^ 2 * s1 -
          (419904 : F[X]) * a41 * b62 + (1166400 : F[X]) * a41 * p2 -
          (559872 : F[X]) * p2 * s1 + (419904 : F[X]) * q41 +
          (466560 : F[X]) * a41 ^ 2 * h * Polynomial.C lambda * w1 +
          (518400 : F[X]) * a41 ^ 2 * h * w1 ^ 2 -
          (349920 : F[X]) * a41 * h * Polynomial.C lambda * p32 -
          (1360800 : F[X]) * a41 * h * p32 * w1 -
          (1244160 : F[X]) * a41 * h * s1 * w1 ^ 2 +
          (816480 : F[X]) * a41 * h * u2 * w1 +
          (349920 : F[X]) * b62 * h * w1 ^ 2 -
          (349920 : F[X]) * h * Polynomial.C lambda * p2 * w1 +
          (194400 : F[X]) * h * p2 * w1 ^ 2 +
          (583200 : F[X]) * h * p32 ^ 2 +
          (933120 : F[X]) * h * p32 * s1 * w1 -
          (489888 : F[X]) * h * p32 * u2 -
          (349920 : F[X]) * h * q53 * w1 -
          (570240 : F[X]) * a41 * h ^ 2 * Polynomial.C lambda * w1 ^ 3 +
          (633600 : F[X]) * a41 * h ^ 2 * w1 ^ 4 +
          (209952 : F[X]) * h ^ 2 * Polynomial.C lambda * p1 +
          (466560 : F[X]) * h ^ 2 * Polynomial.C lambda * p32 * w1 ^ 2 +
          (116640 : F[X]) * h ^ 2 * p1 * w1 -
          (432000 : F[X]) * h ^ 2 * p32 * w1 ^ 3 +
          (380160 : F[X]) * h ^ 2 * s1 * w1 ^ 4 -
          (362880 : F[X]) * h ^ 2 * u2 * w1 ^ 3 +
          (133056 : F[X]) * h ^ 3 * Polynomial.C lambda * w1 ^ 5 -
          (699840 : F[X]) * h ^ 3 * p0 -
          (246400 : F[X]) * h ^ 3 * w1 ^ 6) =
      -(518400 : F) * (Polynomial.eval root a41) ^ 3 +
        (466560 : F) * (Polynomial.eval root a41) ^ 2 *
          Polynomial.eval root s1 -
        (419904 : F) * Polynomial.eval root a41 *
          Polynomial.eval root b62 +
        (1166400 : F) * Polynomial.eval root a41 *
          Polynomial.eval root p2 -
        (559872 : F) * Polynomial.eval root p2 *
          Polynomial.eval root s1 +
        (419904 : F) * Polynomial.eval root q41 := by
  simp [hroot]

end EleventhFaceScalars610

/-! ## Source-facing eleventh-face packet -/

section NonzeroEleventhFace610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
/-- Finite local eleventh-face packet: the tenth-face alternative is
refined.  Either `p₃₁(a) = 0` and the jet upgrades by one more power of
`h`, or the complementary factor solves `p₂` and `b₆₂`. -/
theorem nonzeroFace610_linearRoot_eleventhPowerJet
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
                    (240 : k) * (p.coeff 2).eval a * w1.eval a = 0) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0)) := by
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
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, hXalt⟩ :=
    nonzeroFace610_linearRoot_tenthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, ?_⟩
  have h18 : (18 : k) ≠ 0 := by norm_num
  have h9 : (9 : k) ≠ 0 := by norm_num
  have h3 : (3 : k) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hXalt with hp31z | htp
  · have hu1z : u1.eval a = 0 := by
      have : (3 : k) * u1.eval a = 0 := by
        rw [hTu, hp31z]
        ring
      exact (mul_eq_zero.mp this).resolve_left h3
    have hq52z : q52.eval a = 0 := by
      have : (9 : k) * q52.eval a = 0 := by
        rw [hVq, hp31z]
        ring
      exact (mul_eq_zero.mp this).resolve_left h9
    have hq4z : (q.coeff 4).eval a = 0 := by
      have : (9 : k) * (q.coeff 4).eval a = 0 := by
        rw [hWq, hp31z]
        ring
      exact (mul_eq_zero.mp this).resolve_left h9
    obtain ⟨p32, hp32⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 p31 a hh0degree hroot
        hp31z
    obtain ⟨u2, hu2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 u1 a hh0degree hroot
        hu1z
    obtain ⟨q53, hq53⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 q52 a hh0degree hroot
        hq52z
    obtain ⟨q41, hq41⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 4) a
        hh0degree hroot hq4z
    have hp3' : p.coeff 3 = h0 ^ 2 * p32 := by
      rw [hp3, hp32]
      ring
    have hq7' : q.coeff 7 = h0 ^ 6 * u2 := by
      rw [hu, hu2]
      ring
    have hq5' : q.coeff 5 = h0 ^ 3 * q53 := by
      rw [hq5, hq53]
      ring
    have hq4' : q.coeff 4 = h0 * q41 := hq41
    have hM0 : (18 : k) * s1.eval a - (30 : k) * a41.eval a = 0 := by
      linear_combination (6 : k) * hMs
    have hTclr :
        localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda =
          h0 ^ 14 * ((648 : k[X]) * u2 - (1080 : k[X]) * p32 +
            (324 : k[X]) * a41 * Polynomial.C lambda +
            (720 : k[X]) * a41 * w1 - (864 : k[X]) * s1 * w1 -
            (351 : k[X]) * Polynomial.C lambda * h0 * w1 ^ 2 +
            (520 : k[X]) * h0 * w1 ^ 3) := by
      simpa [hw, ha4s, hp3', hs, hq7'] using
        eleventhFace_clearedT_zeroP31610 h0 w1 a41 s1 u2 p32 lambda
    have hUclr :
        localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda =
          h0 ^ 18 * ((720 : k[X]) * a41 ^ 2 - (576 : k[X]) * a41 * s1 +
            (432 : k[X]) * b62 - (720 : k[X]) * p.coeff 2 -
            (432 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 +
            (216 : k[X]) * h0 * Polynomial.C lambda * p32 +
            (360 : k[X]) * h0 * p32 * w1 +
            (576 : k[X]) * h0 * s1 * w1 ^ 2 -
            (504 : k[X]) * h0 * u2 * w1 +
            (216 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 3 -
            (360 : k[X]) * h0 ^ 2 * w1 ^ 4) := by
      simpa [hw, ha4s, hp3', hs, hq7', hb6s] using
        eleventhFace_clearedU_zeroP31610 h0 w1 a41 s1 u2 p32 b62
          (p.coeff 2) lambda
    have hVclr :
        localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda =
          h0 ^ 23 * (-(42768 : k[X]) * a41 ^ 2 * Polynomial.C lambda -
            (190080 : k[X]) * a41 ^ 2 * w1 +
            (285120 : k[X]) * a41 * p32 +
            (228096 : k[X]) * a41 * s1 * w1 -
            (108864 : k[X]) * a41 * u2 - (93312 : k[X]) * b62 * w1 +
            (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 +
            (51840 : k[X]) * p.coeff 2 * w1 -
            (124416 : k[X]) * p32 * s1 + (93312 : k[X]) * q53 +
            (121176 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 ^ 2 -
            (89760 : k[X]) * a41 * h0 * w1 ^ 3 -
            (85536 : k[X]) * h0 * Polynomial.C lambda * p32 * w1 -
            (155520 : k[X]) * h0 * p.coeff 1 +
            (23760 : k[X]) * h0 * p32 * w1 ^ 2 -
            (107712 : k[X]) * h0 * s1 * w1 ^ 3 +
            (99792 : k[X]) * h0 * u2 * w1 ^ 2 -
            (38709 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 4 +
            (68816 : k[X]) * h0 ^ 2 * w1 ^ 5) := by
      simpa [hw, ha4s, hp3', hs, hq7', hb6s, hq5'] using
        eleventhFace_clearedV_zeroP31610 h0 w1 a41 s1 u2 p32 b62 q53
          (p.coeff 2) (p.coeff 1) lambda
    have hWclr :
        localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda =
          h0 ^ 27 * (-(518400 : k[X]) * a41 ^ 3 +
            (466560 : k[X]) * a41 ^ 2 * s1 -
            (419904 : k[X]) * a41 * b62 +
            (1166400 : k[X]) * a41 * p.coeff 2 -
            (559872 : k[X]) * p.coeff 2 * s1 +
            (419904 : k[X]) * q41 +
            (466560 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda * w1 +
            (518400 : k[X]) * a41 ^ 2 * h0 * w1 ^ 2 -
            (349920 : k[X]) * a41 * h0 * Polynomial.C lambda * p32 -
            (1360800 : k[X]) * a41 * h0 * p32 * w1 -
            (1244160 : k[X]) * a41 * h0 * s1 * w1 ^ 2 +
            (816480 : k[X]) * a41 * h0 * u2 * w1 +
            (349920 : k[X]) * b62 * h0 * w1 ^ 2 -
            (349920 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
              w1 +
            (194400 : k[X]) * h0 * p.coeff 2 * w1 ^ 2 +
            (583200 : k[X]) * h0 * p32 ^ 2 +
            (933120 : k[X]) * h0 * p32 * s1 * w1 -
            (489888 : k[X]) * h0 * p32 * u2 -
            (349920 : k[X]) * h0 * q53 * w1 -
            (570240 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
              w1 ^ 3 +
            (633600 : k[X]) * a41 * h0 ^ 2 * w1 ^ 4 +
            (209952 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 1 +
            (466560 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p32 *
              w1 ^ 2 +
            (116640 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 -
            (432000 : k[X]) * h0 ^ 2 * p32 * w1 ^ 3 +
            (380160 : k[X]) * h0 ^ 2 * s1 * w1 ^ 4 -
            (362880 : k[X]) * h0 ^ 2 * u2 * w1 ^ 3 +
            (133056 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 ^ 3 * p.coeff 0 -
            (246400 : k[X]) * h0 ^ 3 * w1 ^ 6) := by
      simpa [hw, ha4s, hp3', hs, hq7', hb6s, hq5', hq4'] using
        eleventhFace_clearedW_zeroP31610 h0 w1 a41 s1 u2 p32 b62 q53
          (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 lambda
    have hTcof :
        (648 : k[X]) * u2 - (1080 : k[X]) * p32 +
            (324 : k[X]) * a41 * Polynomial.C lambda +
            (720 : k[X]) * a41 * w1 - (864 : k[X]) * s1 * w1 -
            (351 : k[X]) * Polynomial.C lambda * h0 * w1 ^ 2 +
            (520 : k[X]) * h0 * w1 ^ 3 =
          Polynomial.C gamma * h0 := by
      apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
      rw [← hTclr, hTrel]
      ring
    have hUcof :
        (720 : k[X]) * a41 ^ 2 - (576 : k[X]) * a41 * s1 +
            (432 : k[X]) * b62 - (720 : k[X]) * p.coeff 2 -
            (432 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 +
            (216 : k[X]) * h0 * Polynomial.C lambda * p32 +
            (360 : k[X]) * h0 * p32 * w1 +
            (576 : k[X]) * h0 * s1 * w1 ^ 2 -
            (504 : k[X]) * h0 * u2 * w1 +
            (216 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 3 -
            (360 : k[X]) * h0 ^ 2 * w1 ^ 4 =
          Polynomial.C delta * h0 ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 18 hh0)
      rw [← hUclr, hUrel]
      ring
    have hVcof :
        -(42768 : k[X]) * a41 ^ 2 * Polynomial.C lambda -
            (190080 : k[X]) * a41 ^ 2 * w1 +
            (285120 : k[X]) * a41 * p32 +
            (228096 : k[X]) * a41 * s1 * w1 -
            (108864 : k[X]) * a41 * u2 - (93312 : k[X]) * b62 * w1 +
            (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 +
            (51840 : k[X]) * p.coeff 2 * w1 -
            (124416 : k[X]) * p32 * s1 + (93312 : k[X]) * q53 +
            (121176 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 ^ 2 -
            (89760 : k[X]) * a41 * h0 * w1 ^ 3 -
            (85536 : k[X]) * h0 * Polynomial.C lambda * p32 * w1 -
            (155520 : k[X]) * h0 * p.coeff 1 +
            (23760 : k[X]) * h0 * p32 * w1 ^ 2 -
            (107712 : k[X]) * h0 * s1 * w1 ^ 3 +
            (99792 : k[X]) * h0 * u2 * w1 ^ 2 -
            (38709 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 4 +
            (68816 : k[X]) * h0 ^ 2 * w1 ^ 5 =
          Polynomial.C eps * h0 ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 23 hh0)
      rw [← hVclr, hVrel]
      ring
    have hWcof :
        -(518400 : k[X]) * a41 ^ 3 + (466560 : k[X]) * a41 ^ 2 * s1 -
            (419904 : k[X]) * a41 * b62 +
            (1166400 : k[X]) * a41 * p.coeff 2 -
            (559872 : k[X]) * p.coeff 2 * s1 + (419904 : k[X]) * q41 +
            (466560 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda * w1 +
            (518400 : k[X]) * a41 ^ 2 * h0 * w1 ^ 2 -
            (349920 : k[X]) * a41 * h0 * Polynomial.C lambda * p32 -
            (1360800 : k[X]) * a41 * h0 * p32 * w1 -
            (1244160 : k[X]) * a41 * h0 * s1 * w1 ^ 2 +
            (816480 : k[X]) * a41 * h0 * u2 * w1 +
            (349920 : k[X]) * b62 * h0 * w1 ^ 2 -
            (349920 : k[X]) * h0 * Polynomial.C lambda * p.coeff 2 *
              w1 +
            (194400 : k[X]) * h0 * p.coeff 2 * w1 ^ 2 +
            (583200 : k[X]) * h0 * p32 ^ 2 +
            (933120 : k[X]) * h0 * p32 * s1 * w1 -
            (489888 : k[X]) * h0 * p32 * u2 -
            (349920 : k[X]) * h0 * q53 * w1 -
            (570240 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
              w1 ^ 3 +
            (633600 : k[X]) * a41 * h0 ^ 2 * w1 ^ 4 +
            (209952 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 1 +
            (466560 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p32 *
              w1 ^ 2 +
            (116640 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 -
            (432000 : k[X]) * h0 ^ 2 * p32 * w1 ^ 3 +
            (380160 : k[X]) * h0 ^ 2 * s1 * w1 ^ 4 -
            (362880 : k[X]) * h0 ^ 2 * u2 * w1 ^ 3 +
            (133056 : k[X]) * h0 ^ 3 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 ^ 3 * p.coeff 0 -
            (246400 : k[X]) * h0 ^ 3 * w1 ^ 6 =
          Polynomial.C zeta * h0 ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 27 hh0)
      rw [← hWclr, hWrel]
      ring
    have hTeval' :
        (324 : k) * a41.eval a * lambda +
          (720 : k) * a41.eval a * w1.eval a - (1080 : k) * p32.eval a -
          (864 : k) * s1.eval a * w1.eval a +
          (648 : k) * u2.eval a = 0 := by
      have hleft :=
        eval_eleventhFace_T_cofactor610 h0 w1 a41 s1 u2 p32 lambda a
          hroot
      have hzero :
          Polynomial.eval a
              ((648 : k[X]) * u2 - (1080 : k[X]) * p32 +
                (324 : k[X]) * a41 * Polynomial.C lambda +
                (720 : k[X]) * a41 * w1 - (864 : k[X]) * s1 * w1 -
                (351 : k[X]) * Polynomial.C lambda * h0 * w1 ^ 2 +
                (520 : k[X]) * h0 * w1 ^ 3) = 0 := by
        rw [hTcof]
        simp [hroot]
      have hfield := hleft.symm.trans hzero
      linear_combination hfield
    have hUeval' :
        (720 : k) * (a41.eval a) ^ 2 -
          (576 : k) * a41.eval a * s1.eval a +
          (432 : k) * b62.eval a - (720 : k) * (p.coeff 2).eval a =
          0 := by
      have hleft :=
        eval_eleventhFace_U_cofactor610 h0 w1 a41 s1 u2 p32 b62
          (p.coeff 2) lambda a hroot
      have hzero :
          Polynomial.eval a
              ((720 : k[X]) * a41 ^ 2 - (576 : k[X]) * a41 * s1 +
                (432 : k[X]) * b62 - (720 : k[X]) * p.coeff 2 -
                (432 : k[X]) * a41 * h0 * Polynomial.C lambda * w1 +
                (216 : k[X]) * h0 * Polynomial.C lambda * p32 +
                (360 : k[X]) * h0 * p32 * w1 +
                (576 : k[X]) * h0 * s1 * w1 ^ 2 -
                (504 : k[X]) * h0 * u2 * w1 +
                (216 : k[X]) * h0 ^ 2 * Polynomial.C lambda * w1 ^ 3 -
                (360 : k[X]) * h0 ^ 2 * w1 ^ 4) = 0 := by
        rw [hUcof]
        simp [hroot]
      exact hleft.symm.trans hzero
    have hVeval' :
        -(42768 : k) * (a41.eval a) ^ 2 * lambda -
          (190080 : k) * (a41.eval a) ^ 2 * w1.eval a +
          (285120 : k) * a41.eval a * p32.eval a +
          (228096 : k) * a41.eval a * s1.eval a * w1.eval a -
          (108864 : k) * a41.eval a * u2.eval a -
          (93312 : k) * b62.eval a * w1.eval a +
          (46656 : k) * lambda * (p.coeff 2).eval a +
          (51840 : k) * (p.coeff 2).eval a * w1.eval a -
          (124416 : k) * p32.eval a * s1.eval a +
          (93312 : k) * q53.eval a = 0 := by
      have hleft :=
        eval_eleventhFace_V_cofactor610 h0 w1 a41 s1 u2 p32 b62 q53
          (p.coeff 2) (p.coeff 1) lambda a hroot
      have hzero :
          Polynomial.eval a
              (-(42768 : k[X]) * a41 ^ 2 * Polynomial.C lambda -
                (190080 : k[X]) * a41 ^ 2 * w1 +
                (285120 : k[X]) * a41 * p32 +
                (228096 : k[X]) * a41 * s1 * w1 -
                (108864 : k[X]) * a41 * u2 -
                (93312 : k[X]) * b62 * w1 +
                (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 +
                (51840 : k[X]) * p.coeff 2 * w1 -
                (124416 : k[X]) * p32 * s1 + (93312 : k[X]) * q53 +
                (121176 : k[X]) * a41 * h0 * Polynomial.C lambda *
                  w1 ^ 2 -
                (89760 : k[X]) * a41 * h0 * w1 ^ 3 -
                (85536 : k[X]) * h0 * Polynomial.C lambda * p32 * w1 -
                (155520 : k[X]) * h0 * p.coeff 1 +
                (23760 : k[X]) * h0 * p32 * w1 ^ 2 -
                (107712 : k[X]) * h0 * s1 * w1 ^ 3 +
                (99792 : k[X]) * h0 * u2 * w1 ^ 2 -
                (38709 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                  w1 ^ 4 +
                (68816 : k[X]) * h0 ^ 2 * w1 ^ 5) = 0 := by
        rw [hVcof]
        simp [hroot]
      exact hleft.symm.trans hzero
    have hWeval' :
        -(518400 : k) * (a41.eval a) ^ 3 +
          (466560 : k) * (a41.eval a) ^ 2 * s1.eval a -
          (419904 : k) * a41.eval a * b62.eval a +
          (1166400 : k) * a41.eval a * (p.coeff 2).eval a -
          (559872 : k) * (p.coeff 2).eval a * s1.eval a +
          (419904 : k) * q41.eval a = 0 := by
      have hleft :=
        eval_eleventhFace_W_cofactor610 h0 w1 a41 s1 u2 p32 b62 q53
          (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 lambda a hroot
      have hzero :
          Polynomial.eval a
              (-(518400 : k[X]) * a41 ^ 3 +
                (466560 : k[X]) * a41 ^ 2 * s1 -
                (419904 : k[X]) * a41 * b62 +
                (1166400 : k[X]) * a41 * p.coeff 2 -
                (559872 : k[X]) * p.coeff 2 * s1 +
                (419904 : k[X]) * q41 +
                (466560 : k[X]) * a41 ^ 2 * h0 * Polynomial.C lambda *
                  w1 +
                (518400 : k[X]) * a41 ^ 2 * h0 * w1 ^ 2 -
                (349920 : k[X]) * a41 * h0 * Polynomial.C lambda *
                  p32 -
                (1360800 : k[X]) * a41 * h0 * p32 * w1 -
                (1244160 : k[X]) * a41 * h0 * s1 * w1 ^ 2 +
                (816480 : k[X]) * a41 * h0 * u2 * w1 +
                (349920 : k[X]) * b62 * h0 * w1 ^ 2 -
                (349920 : k[X]) * h0 * Polynomial.C lambda *
                  p.coeff 2 * w1 +
                (194400 : k[X]) * h0 * p.coeff 2 * w1 ^ 2 +
                (583200 : k[X]) * h0 * p32 ^ 2 +
                (933120 : k[X]) * h0 * p32 * s1 * w1 -
                (489888 : k[X]) * h0 * p32 * u2 -
                (349920 : k[X]) * h0 * q53 * w1 -
                (570240 : k[X]) * a41 * h0 ^ 2 * Polynomial.C lambda *
                  w1 ^ 3 +
                (633600 : k[X]) * a41 * h0 ^ 2 * w1 ^ 4 +
                (209952 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                  p.coeff 1 +
                (466560 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p32 *
                  w1 ^ 2 +
                (116640 : k[X]) * h0 ^ 2 * p.coeff 1 * w1 -
                (432000 : k[X]) * h0 ^ 2 * p32 * w1 ^ 3 +
                (380160 : k[X]) * h0 ^ 2 * s1 * w1 ^ 4 -
                (362880 : k[X]) * h0 ^ 2 * u2 * w1 ^ 3 +
                (133056 : k[X]) * h0 ^ 3 * Polynomial.C lambda *
                  w1 ^ 5 -
                (699840 : k[X]) * h0 ^ 3 * p.coeff 0 -
                (246400 : k[X]) * h0 ^ 3 * w1 ^ 6) = 0 := by
        rw [hWcof]
        simp [hroot]
      exact hleft.symm.trans hzero
    obtain ⟨hTform, hLform, hWform, hVform⟩ :=
      eleventhFace_zeroP31_nextOrder610 (w1.eval a) (a41.eval a)
        (s1.eval a) (p32.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
        ((p.coeff 2).eval a) (q41.eval a) lambda
        hM0 hTeval' hUeval' hVeval' hWeval'
    refine Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, hp3', hq7', hq5', hq4',
      hTform, hWform, hVform⟩⟩
  · have hb62form :=
      eleventhFace_tp2_b62_610 (w1.eval a) (a41.eval a) (p31.eval a)
        (b62.eval a) ((p.coeff 2).eval a) lambda hUload htp
    exact Or.inr ⟨htp, hb62form⟩

set_option maxHeartbeats 8000000 in
/-- Source-facing eleventh-face power jet of a normalized scale-two
`(6,10)` nonzero face: the tenth-face alternative is refined. -/
theorem normalized610ScaleTwo_nonzeroFace_eleventhPowerJet
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
                    (240 : K) * (p.coeff 2).eval a * w1.eval a = 0) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0)) ∧
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
    nonzeroFace610_linearRoot_eleventhPowerJet p q H h0 j lambda a
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
      hTform, hWform, hVform⟩⟩ | hcomp
  · exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      (by rw [hp3u]; exact dvd_mul_right _ _),
      (by rw [hq7u]; exact dvd_mul_right _ _),
      (by rw [hq5u]; exact dvd_mul_right _ _),
      (by rw [hq4u]; exact dvd_mul_right _ _),
      hTform, hWform, hVform⟩⟩
  · exact Or.inr hcomp

end NonzeroEleventhFace610

#print axioms eleventhCoefficientJacobianRow_610
#print axioms eleventhFace_zeroP31_load610
#print axioms eleventhFace_zeroP31_T_nextOrder610
#print axioms eleventhFace_zeroP31_U_nextOrder610
#print axioms eleventhFace_zeroP31_W_nextOrder610
#print axioms eleventhFace_zeroP31_V_nextOrder610
#print axioms eleventhFace_zeroP31_nextOrder610
#print axioms eleventhFace_tp2_p2_610
#print axioms eleventhFace_tp2_b62_610
#print axioms eleventhFace_clearedT_zeroP31610
#print axioms eleventhFace_clearedU_zeroP31610
#print axioms eleventhFace_clearedV_zeroP31610
#print axioms eleventhFace_clearedW_zeroP31610
#print axioms nonzeroFace610_linearRoot_eleventhPowerJet
#print axioms normalized610ScaleTwo_nonzeroFace_eleventhPowerJet

end Max11DegreeRoutes
