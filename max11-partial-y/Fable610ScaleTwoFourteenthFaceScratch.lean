import Fable610ScaleTwoThirteenthFaceScratch

/-! # Scale-two fourteenth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the thirteenth-face packet supplies the degree-`2`
Jacobian row and the refined twelfth-face alternatives: either
`p₃₁(a) = 0` with the peeled seventh-defect cofactor `Ξ = h χ` and the
law `9 χ(a) = 17280 λ a₄₁² w₁² - 54400 a₄₁² w₁³
- 27648 λ a₄₁ p₃₂ w₁ - 7680 a₄₁ p₁ + 99840 a₄₁ p₃₂ w₁²
- 17280 λ p₂ w₁² + 10368 λ p₃₂² + 38400 p₂ w₁³ - 46080 p₃₂² w₁`, or
the complementary factor with the peeled sixth-defect head `h ψ` and
the law `ψ(a) = 162 w₁ (7600 a₄₁² w₁ - 2520 λ a₄₁² + 243 λ² p₃₁
- 1980 λ p₃₁ w₁ + 3200 p₃₁ w₁²)`.

The next unused Keller coefficient is the degree-`1` Jacobian row.
After the same sextic depression that kills `z⁵`, that row is
`2 V E' + W D' - D W' - 2 C X' = 0`.  Clearing the corresponding first
integral against the remaining decic coordinates produces a defect
larger than the remaining exact jet, so this file isolates that
Jacobian identity and the strongest exact source-facing refinement of
both live thirteenth-face alternatives.

On `p₃₁(a) = 0` the thirteenth-face law makes the `h³³` head
`χ + ⋯` of the cleared seventh defect vanish at the root of `h`, so it
is a polynomial multiple `h χ₂`; the cleared seventh defect collapses
to `h³⁴ (χ₂ + ⋯)` while its first integral is a scalar times `h³⁵`, so
the last leftover order before the ground constant is exact and forces
`9 χ₂(a) = 16 w₁ (1296 λ p₁ - 1080 p₁ w₁ + 1890 λ p₃₂ w₁²
- 1575 λ a₄₁ w₁³ - 4200 p₃₂ w₁³ + 3500 a₄₁ w₁⁴)` at the root of `h`.
On the complementary factor the thirteenth-face law makes the `h²⁸`
head `ψ + ⋯` of the cleared sixth defect vanish at the root of `h`, so
it is a polynomial multiple `h ψ₂`; the cleared sixth defect collapses
to `h²⁹ (ψ₂ + ⋯)` while its first integral is a scalar times `h³⁰`, so
the last leftover order before the ground constant is exact and forces
`ψ₂(a) = 288 (1980 λ a₄₁ w₁³ - 4400 a₄₁ w₁⁴ - 729 λ p₁ - 405 p₁ w₁)`
at the root of `h`.

Neither alternative is closed further: the aligned face `N = 0` and the
`p₃₁ ≠ 0` sibling remain open, the ground constants `η` and `ζ` of the
seventh- and sixth-defect first integrals are preserved and not cleared
to zero (their orders `h³⁵` and `h³⁰` are now the only leftover orders
of the two cleared defects), the degree-`5`, degree-`4`, degree-`3`,
degree-`2`, and degree-`1` first integrals stay uncleared, and no
individual vanishing of `p₂, p₁, p₀, q₃` (nor of
`w₁, a₄₁, p₃₂, ω, χ, ψ, χ₂, ψ₂`) is claimed.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fourteenth row below the leading weighted-Wronskian row for
outer degrees `(6,10)`.  Unused Jacobian coefficients of the thirteenth
face start at degree `1`. -/
theorem fourteenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 1).derivative * q.coeff 1 +
        (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
      ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
        p.coeff 1 * (q.coeff 1).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 1) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (1 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 1 :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC2]
  linear_combination hcoeff

/-! ## Scalar algebra of the thirteenth-face alternatives -/

section FourteenthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ = 0` sibling, the thirteenth-face law makes the `h³³`
head of the cleared seventh defect vanish at the root. -/
theorem fourteenthFace_zeroP31_chiCombo_vanish610 (w1 a41 s1 p32 u2 b62
    q53 p2 p1 chi : F) (lambda : F)
    (hM : (3 : F) * s1 = (5 : F) * a41)
    (hT : (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
      (9 : F) * lambda * a41 = 0)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0)
    (hV : (216 : F) * q53 + (27 : F) * lambda * a41 ^ 2 +
        (40 : F) * a41 ^ 2 * w1 - (240 : F) * a41 * p32 +
        (108 : F) * lambda * p2 - (240 : F) * p2 * w1 = 0)
    (hChi : (9 : F) * chi = (17280 : F) * lambda * a41 ^ 2 * w1 ^ 2 -
        (54400 : F) * a41 ^ 2 * w1 ^ 3 -
        (27648 : F) * lambda * a41 * p32 * w1 -
        (7680 : F) * a41 * p1 +
        (99840 : F) * a41 * p32 * w1 ^ 2 -
        (17280 : F) * lambda * p2 * w1 ^ 2 +
        (10368 : F) * lambda * p32 ^ 2 +
        (38400 : F) * p2 * w1 ^ 3 -
      (46080 : F) * p32 ^ 2 * w1) :
    chi + (-(5040 : F) * a41 ^ 2 * lambda * w1 ^ 2 +
        (5760 : F) * a41 * lambda * p32 * w1 +
        (7680 : F) * a41 * p1 +
        (4800 : F) * a41 * p32 * w1 ^ 2 +
        (8960 : F) * a41 * s1 * w1 ^ 3 -
        (6720 : F) * a41 * u2 * w1 ^ 2 -
        (1920 : F) * b62 * w1 ^ 3 +
        (2880 : F) * lambda * p2 * w1 ^ 2 -
        (1152 : F) * lambda * p32 ^ 2 -
        (4096 : F) * p1 * s1 -
        (3200 : F) * p2 * w1 ^ 3 -
        (3840 : F) * p32 ^ 2 * w1 -
        (7680 : F) * p32 * s1 * w1 ^ 2 +
        (5376 : F) * p32 * u2 * w1 +
        (1920 : F) * q53 * w1 ^ 2) = 0 := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
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
  have hid : (9 : F) * (chi + (-(5040 : F) * a41 ^ 2 * lambda * w1 ^ 2 +
        (5760 : F) * a41 * lambda * p32 * w1 +
        (7680 : F) * a41 * p1 +
        (4800 : F) * a41 * p32 * w1 ^ 2 +
        (8960 : F) * a41 * s1 * w1 ^ 3 -
        (6720 : F) * a41 * u2 * w1 ^ 2 -
        (1920 : F) * b62 * w1 ^ 3 +
        (2880 : F) * lambda * p2 * w1 ^ 2 -
        (1152 : F) * lambda * p32 ^ 2 -
        (4096 : F) * p1 * s1 -
        (3200 : F) * p2 * w1 ^ 3 -
        (3840 : F) * p32 ^ 2 * w1 -
        (7680 : F) * p32 * s1 * w1 ^ 2 +
        (5376 : F) * p32 * u2 * w1 +
        (1920 : F) * q53 * w1 ^ 2)) =
      (9 : F) * chi - ((17280 : F) * lambda * a41 ^ 2 * w1 ^ 2 -
        (54400 : F) * a41 ^ 2 * w1 ^ 3 -
        (27648 : F) * lambda * a41 * p32 * w1 -
        (7680 : F) * a41 * p1 +
        (99840 : F) * a41 * p32 * w1 ^ 2 -
        (17280 : F) * lambda * p2 * w1 ^ 2 +
        (10368 : F) * lambda * p32 ^ 2 +
        (38400 : F) * p2 * w1 ^ 3 -
        (46080 : F) * p32 ^ 2 * w1) := by
    simp only [hs1, hu2, hb62, hq53]
    ring
  have hz : (9 : F) * (chi + (-(5040 : F) * a41 ^ 2 * lambda * w1 ^ 2 +
        (5760 : F) * a41 * lambda * p32 * w1 +
        (7680 : F) * a41 * p1 +
        (4800 : F) * a41 * p32 * w1 ^ 2 +
        (8960 : F) * a41 * s1 * w1 ^ 3 -
        (6720 : F) * a41 * u2 * w1 ^ 2 -
        (1920 : F) * b62 * w1 ^ 3 +
        (2880 : F) * lambda * p2 * w1 ^ 2 -
        (1152 : F) * lambda * p32 ^ 2 -
        (4096 : F) * p1 * s1 -
        (3200 : F) * p2 * w1 ^ 3 -
        (3840 : F) * p32 ^ 2 * w1 -
        (7680 : F) * p32 * s1 * w1 ^ 2 +
        (5376 : F) * p32 * u2 * w1 +
        (1920 : F) * q53 * w1 ^ 2)) = 0 := by
    rw [hid]
    linear_combination hChi
  exact (mul_eq_zero.mp hz).resolve_left h9

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ = 0` sibling, the seventh defect at the last leftover
order before the ground constant solves the peeled cofactor `χ₂(a)`
exactly. -/
theorem fourteenthFace_zeroP31_chi2_nextOrder610 (w1 a41 s1 p32 u2 p1
    chi2 : F) (lambda : F)
    (hM : (3 : F) * s1 = (5 : F) * a41)
    (hT : (18 : F) * u2 - (30 : F) * p32 - (20 : F) * a41 * w1 +
      (9 : F) * lambda * a41 = 0)
    (hChi2 : chi2 + ((3780 : F) * a41 * lambda * w1 ^ 4 -
        (5040 : F) * a41 * w1 ^ 5 -
        (2304 : F) * lambda * p1 * w1 -
        (3360 : F) * lambda * p32 * w1 ^ 3 +
        (1920 : F) * p1 * w1 ^ 2 +
        (4200 : F) * p32 * w1 ^ 4 -
        (2016 : F) * s1 * w1 ^ 5 +
        (1960 : F) * u2 * w1 ^ 4) = 0) :
    (9 : F) * chi2 = (16 : F) * w1 *
      ((1296 : F) * lambda * p1 - (1080 : F) * p1 * w1 +
        (1890 : F) * lambda * p32 * w1 ^ 2 -
        (1575 : F) * lambda * a41 * w1 ^ 3 -
        (4200 : F) * p32 * w1 ^ 3 +
      (3500 : F) * a41 * w1 ^ 4) := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
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
  have hid : (9 : F) * (chi2 + ((3780 : F) * a41 * lambda * w1 ^ 4 -
        (5040 : F) * a41 * w1 ^ 5 -
        (2304 : F) * lambda * p1 * w1 -
        (3360 : F) * lambda * p32 * w1 ^ 3 +
        (1920 : F) * p1 * w1 ^ 2 +
        (4200 : F) * p32 * w1 ^ 4 -
        (2016 : F) * s1 * w1 ^ 5 +
        (1960 : F) * u2 * w1 ^ 4)) =
      (9 : F) * chi2 - (16 : F) * w1 *
        ((1296 : F) * lambda * p1 - (1080 : F) * p1 * w1 +
          (1890 : F) * lambda * p32 * w1 ^ 2 -
          (1575 : F) * lambda * a41 * w1 ^ 3 -
          (4200 : F) * p32 * w1 ^ 3 +
          (3500 : F) * a41 * w1 ^ 4) := by
    simp only [hs1, hu2]
    ring
  have hz : (9 : F) * chi2 - (16 : F) * w1 *
      ((1296 : F) * lambda * p1 - (1080 : F) * p1 * w1 +
        (1890 : F) * lambda * p32 * w1 ^ 2 -
        (1575 : F) * lambda * a41 * w1 ^ 3 -
        (4200 : F) * p32 * w1 ^ 3 +
        (3500 : F) * a41 * w1 ^ 4) = 0 := by
    rw [← hid, hChi2, mul_zero]
  linear_combination hz

set_option maxHeartbeats 4000000 in
/-- On the complementary factor, the thirteenth-face law makes the
`h²⁸` head of the cleared sixth defect vanish at the root. -/
theorem fourteenthFace_tp2_psiCombo_vanish610 (w1 a41 s1 u1 p31 b62 p2
    psi : F) (lambda : F)
    (hM : (3 : F) * s1 = (5 : F) * a41)
    (hT : (3 : F) * u1 = (5 : F) * p31)
    (hXc : (240 : F) * p2 - (40 : F) * a41 ^ 2 -
        (27 : F) * lambda * p31 - (40 : F) * p31 * w1 = 0)
    (hB : (144 : F) * b62 - (120 : F) * a41 ^ 2 +
        (45 : F) * lambda * p31 - (200 : F) * p31 * w1 = 0)
    (hPsi : psi = (162 : F) * w1 * ((7600 : F) * a41 ^ 2 * w1 -
        (2520 : F) * lambda * a41 ^ 2 + (243 : F) * lambda ^ 2 * p31 -
        (1980 : F) * lambda * p31 * w1 +
      (3200 : F) * p31 * w1 ^ 2)) :
    psi + ((466560 : F) * a41 ^ 2 * lambda * w1 +
        (518400 : F) * a41 ^ 2 * w1 ^ 2 -
        (1244160 : F) * a41 * s1 * w1 ^ 2 +
        (349920 : F) * b62 * w1 ^ 2 -
        (349920 : F) * lambda * p2 * w1 +
        (466560 : F) * lambda * p31 * w1 ^ 2 +
        (194400 : F) * p2 * w1 ^ 2 -
        (432000 : F) * p31 * w1 ^ 3 -
        (362880 : F) * u1 * w1 ^ 3) = 0 := by
  have h3 : (3 : F) ≠ 0 := by norm_num
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
  have hid : psi + ((466560 : F) * a41 ^ 2 * lambda * w1 +
        (518400 : F) * a41 ^ 2 * w1 ^ 2 -
        (1244160 : F) * a41 * s1 * w1 ^ 2 +
        (349920 : F) * b62 * w1 ^ 2 -
        (349920 : F) * lambda * p2 * w1 +
        (466560 : F) * lambda * p31 * w1 ^ 2 +
        (194400 : F) * p2 * w1 ^ 2 -
        (432000 : F) * p31 * w1 ^ 3 -
        (362880 : F) * u1 * w1 ^ 3) =
      psi - (162 : F) * w1 * ((7600 : F) * a41 ^ 2 * w1 -
        (2520 : F) * lambda * a41 ^ 2 + (243 : F) * lambda ^ 2 * p31 -
        (1980 : F) * lambda * p31 * w1 +
        (3200 : F) * p31 * w1 ^ 2) := by
    simp only [hs1, hu1, hb62, hp2]
    ring
  rw [hid]
  linear_combination hPsi

set_option maxHeartbeats 4000000 in
/-- On the complementary factor, the sixth defect at the last leftover
order before the ground constant solves the peeled cofactor `ψ₂(a)`
exactly. -/
theorem fourteenthFace_tp2_psi2_nextOrder610 (w1 a41 s1 p1 psi2 : F)
    (lambda : F)
    (hM : (3 : F) * s1 = (5 : F) * a41)
    (hPsi2 : psi2 + (-(570240 : F) * a41 * lambda * w1 ^ 3 +
        (633600 : F) * a41 * w1 ^ 4 +
        (209952 : F) * lambda * p1 +
        (116640 : F) * p1 * w1 +
        (380160 : F) * s1 * w1 ^ 4) = 0) :
    psi2 = (288 : F) * ((1980 : F) * lambda * a41 * w1 ^ 3 -
        (4400 : F) * a41 * w1 ^ 4 - (729 : F) * lambda * p1 -
      (405 : F) * p1 * w1) := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  have hs1 : s1 = (5 / 3 : F) * a41 := by
    have hid : (3 : F) * (s1 - (5 / 3 : F) * a41) =
        (3 : F) * s1 - (5 : F) * a41 := by ring
    have hz : (3 : F) * (s1 - (5 / 3 : F) * a41) = 0 := by
      rw [hid]
      linear_combination hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h3)
  have hid : psi2 + (-(570240 : F) * a41 * lambda * w1 ^ 3 +
        (633600 : F) * a41 * w1 ^ 4 +
        (209952 : F) * lambda * p1 +
        (116640 : F) * p1 * w1 +
        (380160 : F) * s1 * w1 ^ 4) =
      psi2 - (288 : F) * ((1980 : F) * lambda * a41 * w1 ^ 3 -
        (4400 : F) * a41 * w1 ^ 4 - (729 : F) * lambda * p1 -
        (405 : F) * p1 * w1) := by
    simp only [hs1]
    ring
  have hz : psi2 - (288 : F) * ((1980 : F) * lambda * a41 * w1 ^ 3 -
      (4400 : F) * a41 * w1 ^ 4 - (729 : F) * lambda * p1 -
      (405 : F) * p1 * w1) = 0 := by
    rw [← hid]
    exact hPsi2
  linear_combination hz

end FourteenthFaceScalars610

/-! ## Cleared-defect substitutions on the refined alternatives -/

section FourteenthFaceCleared610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 24000000 in
/-- Peeling the extra factor of `h` from the vanishing thirteenth-face
head pushes the cleared seventh defect on the `p₃₁ = 0` jet to
`h³⁴`. -/
theorem fourteenthFace_clearedX_chi2_610 (h w1 a41 s1 u2 p32 b62 q53 p2
    p1 p0 q41 q3 chi chi2 : F[X]) (lambda : F)
    (hchi : (960 : F[X]) * a41 ^ 3 * Polynomial.C lambda +
        (6400 : F[X]) * a41 ^ 3 * w1 - (9600 : F[X]) * a41 ^ 2 * p32 -
        (7680 : F[X]) * a41 ^ 2 * s1 * w1 +
        (2688 : F[X]) * a41 ^ 2 * u2 +
        (4608 : F[X]) * a41 * b62 * w1 -
        (2304 : F[X]) * a41 * Polynomial.C lambda * p2 -
        (7680 : F[X]) * a41 * p2 * w1 +
        (6144 : F[X]) * a41 * p32 * s1 - (2560 : F[X]) * a41 * q53 -
        (3072 : F[X]) * b62 * p32 + (7680 : F[X]) * p2 * p32 +
        (6144 : F[X]) * p2 * s1 * w1 - (3584 : F[X]) * p2 * u2 +
        (3072 : F[X]) * q3 - (2048 : F[X]) * q41 * w1 = h * chi)
    (hchi2 : chi + (-(5040 : F[X]) * a41 ^ 2 * Polynomial.C lambda *
        w1 ^ 2 +
        (5760 : F[X]) * a41 * Polynomial.C lambda * p32 * w1 +
        (7680 : F[X]) * a41 * p1 +
        (4800 : F[X]) * a41 * p32 * w1 ^ 2 +
        (8960 : F[X]) * a41 * s1 * w1 ^ 3 -
        (6720 : F[X]) * a41 * u2 * w1 ^ 2 -
        (1920 : F[X]) * b62 * w1 ^ 3 +
        (2880 : F[X]) * Polynomial.C lambda * p2 * w1 ^ 2 -
        (1152 : F[X]) * Polynomial.C lambda * p32 ^ 2 -
        (4096 : F[X]) * p1 * s1 -
        (3200 : F[X]) * p2 * w1 ^ 3 -
        (3840 : F[X]) * p32 ^ 2 * w1 -
        (7680 : F[X]) * p32 * s1 * w1 ^ 2 +
        (5376 : F[X]) * p32 * u2 * w1 +
        (1920 : F[X]) * q53 * w1 ^ 2) = h * chi2) :
    localClearedSeventhDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 lambda =
      h ^ 34 * (chi2 +
        ((3780 : F[X]) * a41 * Polynomial.C lambda * w1 ^ 4 -
        (5040 : F[X]) * a41 * w1 ^ 5 -
        (2304 : F[X]) * Polynomial.C lambda * p1 * w1 -
        (3360 : F[X]) * Polynomial.C lambda * p32 * w1 ^ 3 +
        (1920 : F[X]) * p1 * w1 ^ 2 +
        (4200 : F[X]) * p32 * w1 ^ 4 -
        (2016 : F[X]) * s1 * w1 ^ 5 +
        (1960 : F[X]) * u2 * w1 ^ 4 +
        (1536 : F[X]) * h * Polynomial.C lambda * p0 -
        (693 : F[X]) * h * Polynomial.C lambda * w1 ^ 6 +
        (1320 : F[X]) * h * w1 ^ 7)) := by
  rw [thirteenthFace_clearedX_chi610 h w1 a41 s1 u2 p32 b62 q53 p2 p1
    p0 q41 q3 chi lambda hchi]
  linear_combination h ^ 33 * hchi2

theorem eval_fourteenthFace_X_chi2Cofactor610 (h w1 a41 s1 u2 p32 p1
    p0 chi2 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root (chi2 +
        ((3780 : F[X]) * a41 * Polynomial.C lambda * w1 ^ 4 -
        (5040 : F[X]) * a41 * w1 ^ 5 -
        (2304 : F[X]) * Polynomial.C lambda * p1 * w1 -
        (3360 : F[X]) * Polynomial.C lambda * p32 * w1 ^ 3 +
        (1920 : F[X]) * p1 * w1 ^ 2 +
        (4200 : F[X]) * p32 * w1 ^ 4 -
        (2016 : F[X]) * s1 * w1 ^ 5 +
        (1960 : F[X]) * u2 * w1 ^ 4 +
        (1536 : F[X]) * h * Polynomial.C lambda * p0 -
        (693 : F[X]) * h * Polynomial.C lambda * w1 ^ 6 +
        (1320 : F[X]) * h * w1 ^ 7)) =
      Polynomial.eval root chi2 +
        ((3780 : F) * Polynomial.eval root a41 * lambda *
          (Polynomial.eval root w1) ^ 4 -
        (5040 : F) * Polynomial.eval root a41 *
          (Polynomial.eval root w1) ^ 5 -
        (2304 : F) * lambda * Polynomial.eval root p1 *
          Polynomial.eval root w1 -
        (3360 : F) * lambda * Polynomial.eval root p32 *
          (Polynomial.eval root w1) ^ 3 +
        (1920 : F) * Polynomial.eval root p1 *
          (Polynomial.eval root w1) ^ 2 +
        (4200 : F) * Polynomial.eval root p32 *
          (Polynomial.eval root w1) ^ 4 -
        (2016 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root w1) ^ 5 +
        (1960 : F) * Polynomial.eval root u2 *
          (Polynomial.eval root w1) ^ 4) := by
  simp [hroot]

set_option maxHeartbeats 12000000 in
/-- Peeling the extra factor of `h` from the vanishing thirteenth-face
head pushes the cleared sixth defect on the complementary factor to
`h²⁹`. -/
theorem fourteenthFace_comp_sixthDefect_psi2_610 (h w1 a41 s1 u1 p31
    b62 q52 p2 p1 p0 q4 omega psi psi2 : F[X]) (lambda : F)
    (homega : (583200 : F[X]) * p31 ^ 2 - (489888 : F[X]) * p31 * u1 +
      (419904 : F[X]) * q4 = h * omega)
    (hpsi : omega + (-(518400 : F[X]) * a41 ^ 3 +
        (466560 : F[X]) * a41 ^ 2 * s1 -
        (419904 : F[X]) * a41 * b62 -
        (349920 : F[X]) * a41 * Polynomial.C lambda * p31 +
        (1166400 : F[X]) * a41 * p2 -
        (1360800 : F[X]) * a41 * p31 * w1 +
        (816480 : F[X]) * a41 * u1 * w1 -
        (559872 : F[X]) * p2 * s1 +
        (933120 : F[X]) * p31 * s1 * w1 -
        (349920 : F[X]) * q52 * w1) = h * psi)
    (hpsi2 : psi + ((466560 : F[X]) * a41 ^ 2 * Polynomial.C lambda *
        w1 +
        (518400 : F[X]) * a41 ^ 2 * w1 ^ 2 -
        (1244160 : F[X]) * a41 * s1 * w1 ^ 2 +
        (349920 : F[X]) * b62 * w1 ^ 2 -
        (349920 : F[X]) * Polynomial.C lambda * p2 * w1 +
        (466560 : F[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
        (194400 : F[X]) * p2 * w1 ^ 2 -
        (432000 : F[X]) * p31 * w1 ^ 3 -
        (362880 : F[X]) * u1 * w1 ^ 3) = h * psi2) :
    localClearedSixthDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        q4 lambda =
      h ^ 29 * (psi2 +
        (-(570240 : F[X]) * a41 * Polynomial.C lambda * w1 ^ 3 +
        (633600 : F[X]) * a41 * w1 ^ 4 +
        (209952 : F[X]) * Polynomial.C lambda * p1 +
        (116640 : F[X]) * p1 * w1 +
        (380160 : F[X]) * s1 * w1 ^ 4 +
        (133056 : F[X]) * h * Polynomial.C lambda * w1 ^ 5 -
        (699840 : F[X]) * h * p0 -
        (246400 : F[X]) * h * w1 ^ 6)) := by
  rw [thirteenthFace_comp_sixthDefect_psi610 h w1 a41 s1 u1 p31 b62 q52
    p2 p1 p0 q4 omega psi lambda homega hpsi]
  linear_combination h ^ 28 * hpsi2

theorem eval_fourteenthFace_comp_psi2Cofactor610 (h w1 a41 s1 p1 p0
    psi2 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root (psi2 +
        (-(570240 : F[X]) * a41 * Polynomial.C lambda * w1 ^ 3 +
        (633600 : F[X]) * a41 * w1 ^ 4 +
        (209952 : F[X]) * Polynomial.C lambda * p1 +
        (116640 : F[X]) * p1 * w1 +
        (380160 : F[X]) * s1 * w1 ^ 4 +
        (133056 : F[X]) * h * Polynomial.C lambda * w1 ^ 5 -
        (699840 : F[X]) * h * p0 -
        (246400 : F[X]) * h * w1 ^ 6)) =
      Polynomial.eval root psi2 +
        (-(570240 : F) * Polynomial.eval root a41 * lambda *
          (Polynomial.eval root w1) ^ 3 +
        (633600 : F) * Polynomial.eval root a41 *
          (Polynomial.eval root w1) ^ 4 +
        (209952 : F) * lambda * Polynomial.eval root p1 +
        (116640 : F) * Polynomial.eval root p1 *
          Polynomial.eval root w1 +
        (380160 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root w1) ^ 4) := by
  simp [hroot]

end FourteenthFaceCleared610

/-! ## Source-facing fourteenth-face packet -/

section NonzeroFourteenthFace610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
/-- Finite local fourteenth-face packet: both thirteenth-face
alternatives are refined at the last leftover order before the ground
constants.  On `p₃₁(a) = 0` the vanishing `h³³` head of the cleared
seventh defect peels one factor of `h` and the `h³⁴` order solves
`χ₂(a)` exactly; on the complementary factor the vanishing `h²⁸` head
of the cleared sixth defect peels one factor of `h` and the `h²⁹`
order solves `ψ₂(a)` exactly. -/
theorem nonzeroFace610_linearRoot_fourteenthPowerJet
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
            ∃ (p32 u2 q53 q41 chi chi2 : k[X]),
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
                    0 ∧
                (960 : k[X]) * a41 ^ 3 * Polynomial.C lambda +
                    (6400 : k[X]) * a41 ^ 3 * w1 -
                    (9600 : k[X]) * a41 ^ 2 * p32 -
                    (7680 : k[X]) * a41 ^ 2 * s1 * w1 +
                    (2688 : k[X]) * a41 ^ 2 * u2 +
                    (4608 : k[X]) * a41 * b62 * w1 -
                    (2304 : k[X]) * a41 * Polynomial.C lambda *
                      p.coeff 2 -
                    (7680 : k[X]) * a41 * p.coeff 2 * w1 +
                    (6144 : k[X]) * a41 * p32 * s1 -
                    (2560 : k[X]) * a41 * q53 -
                    (3072 : k[X]) * b62 * p32 +
                    (7680 : k[X]) * p.coeff 2 * p32 +
                    (6144 : k[X]) * p.coeff 2 * s1 * w1 -
                    (3584 : k[X]) * p.coeff 2 * u2 +
                    (3072 : k[X]) * q.coeff 3 -
                    (2048 : k[X]) * q41 * w1 = h0 * chi ∧
                (9 : k) * chi.eval a =
                  (17280 : k) * lambda * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 2 -
                    (54400 : k) * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 3 -
                    (27648 : k) * lambda * a41.eval a * p32.eval a *
                      w1.eval a -
                    (7680 : k) * a41.eval a * (p.coeff 1).eval a +
                    (99840 : k) * a41.eval a * p32.eval a *
                      (w1.eval a) ^ 2 -
                    (17280 : k) * lambda * (p.coeff 2).eval a *
                      (w1.eval a) ^ 2 +
                    (10368 : k) * lambda * (p32.eval a) ^ 2 +
                    (38400 : k) * (p.coeff 2).eval a *
                      (w1.eval a) ^ 3 -
                    (46080 : k) * (p32.eval a) ^ 2 * w1.eval a ∧
                chi + (-(5040 : k[X]) * a41 ^ 2 * Polynomial.C lambda *
                    w1 ^ 2 +
                  (5760 : k[X]) * a41 * Polynomial.C lambda * p32 *
                    w1 +
                  (7680 : k[X]) * a41 * p.coeff 1 +
                  (4800 : k[X]) * a41 * p32 * w1 ^ 2 +
                  (8960 : k[X]) * a41 * s1 * w1 ^ 3 -
                  (6720 : k[X]) * a41 * u2 * w1 ^ 2 -
                  (1920 : k[X]) * b62 * w1 ^ 3 +
                  (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                    w1 ^ 2 -
                  (1152 : k[X]) * Polynomial.C lambda * p32 ^ 2 -
                  (4096 : k[X]) * p.coeff 1 * s1 -
                  (3200 : k[X]) * p.coeff 2 * w1 ^ 3 -
                  (3840 : k[X]) * p32 ^ 2 * w1 -
                  (7680 : k[X]) * p32 * s1 * w1 ^ 2 +
                  (5376 : k[X]) * p32 * u2 * w1 +
                  (1920 : k[X]) * q53 * w1 ^ 2) = h0 * chi2 ∧
                (9 : k) * chi2.eval a =
                  (16 : k) * w1.eval a *
                    ((1296 : k) * lambda * (p.coeff 1).eval a -
                      (1080 : k) * (p.coeff 1).eval a * w1.eval a +
                      (1890 : k) * lambda * p32.eval a *
                        (w1.eval a) ^ 2 -
                      (1575 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4200 : k) * p32.eval a * (w1.eval a) ^ 3 +
                    (3500 : k) * a41.eval a * (w1.eval a) ^ 4)) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ∃ (omega psi psi2 : k[X]),
              (583200 : k[X]) * p31 ^ 2 -
                  (489888 : k[X]) * p31 * u1 +
                (419904 : k[X]) * q.coeff 4 = h0 * omega ∧
              omega.eval a =
                (648 : k) * a41.eval a *
                  ((80 : k) * (a41.eval a) ^ 2 +
                      (297 : k) * lambda * p31.eval a -
                    (960 : k) * p31.eval a * w1.eval a) ∧
              omega + (-(518400 : k[X]) * a41 ^ 3 +
                  (466560 : k[X]) * a41 ^ 2 * s1 -
                  (419904 : k[X]) * a41 * b62 -
                  (349920 : k[X]) * a41 * Polynomial.C lambda * p31 +
                  (1166400 : k[X]) * a41 * p.coeff 2 -
                  (1360800 : k[X]) * a41 * p31 * w1 +
                  (816480 : k[X]) * a41 * u1 * w1 -
                  (559872 : k[X]) * p.coeff 2 * s1 +
                  (933120 : k[X]) * p31 * s1 * w1 -
                  (349920 : k[X]) * q52 * w1) = h0 * psi ∧
              psi.eval a =
                (162 : k) * w1.eval a *
                  ((7600 : k) * (a41.eval a) ^ 2 * w1.eval a -
                      (2520 : k) * lambda * (a41.eval a) ^ 2 +
                      (243 : k) * lambda ^ 2 * p31.eval a -
                      (1980 : k) * lambda * p31.eval a * w1.eval a +
                    (3200 : k) * p31.eval a *
                      (w1.eval a) ^ 2) ∧
              psi + ((466560 : k[X]) * a41 ^ 2 * Polynomial.C lambda *
                  w1 +
                (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
                (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
                (349920 : k[X]) * b62 * w1 ^ 2 -
                (349920 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                  w1 +
                (466560 : k[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
                (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
                (432000 : k[X]) * p31 * w1 ^ 3 -
                (362880 : k[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
              psi2.eval a =
                (288 : k) * ((1980 : k) * lambda * a41.eval a *
                    (w1.eval a) ^ 3 -
                  (4400 : k) * a41.eval a * (w1.eval a) ^ 4 -
                  (729 : k) * lambda * (p.coeff 1).eval a -
                  (405 : k) * (p.coeff 1).eval a * w1.eval a))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, halt⟩ :=
    nonzeroFace610_linearRoot_thirteenthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, ?_⟩
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, chi, hp3u, hq7u, hq5u,
      hq4u, hTform, hWform, hVform, hQ3form, hchieq, hchival⟩⟩ |
      ⟨htp, hb62form, omega, psi, homega, homegaval, hpsieq, hpsival⟩
  · -- `p₃₁(a) = 0`: peel the vanishing `h³³` head of the seventh
    -- defect and solve the `h³⁴` order.
    have hUred :
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
          (30 : k) * (p.coeff 2).eval a = 0 :=
      eleventhFace_zeroP31_load610 (w1.eval a) (a41.eval a)
        (p31.eval a) (b62.eval a) ((p.coeff 2).eval a) lambda hp31z
        hUload
    have hcv :=
      fourteenthFace_zeroP31_chiCombo_vanish610 (w1.eval a)
        (a41.eval a) (s1.eval a) (p32.eval a) (u2.eval a)
        (b62.eval a) (q53.eval a) ((p.coeff 2).eval a)
        ((p.coeff 1).eval a) (chi.eval a) lambda hMs hTform hUred
        hVform hchival
    have hcombz :
        (chi + (-(5040 : k[X]) * a41 ^ 2 * Polynomial.C lambda *
            w1 ^ 2 +
          (5760 : k[X]) * a41 * Polynomial.C lambda * p32 * w1 +
          (7680 : k[X]) * a41 * p.coeff 1 +
          (4800 : k[X]) * a41 * p32 * w1 ^ 2 +
          (8960 : k[X]) * a41 * s1 * w1 ^ 3 -
          (6720 : k[X]) * a41 * u2 * w1 ^ 2 -
          (1920 : k[X]) * b62 * w1 ^ 3 +
          (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 * w1 ^ 2 -
          (1152 : k[X]) * Polynomial.C lambda * p32 ^ 2 -
          (4096 : k[X]) * p.coeff 1 * s1 -
          (3200 : k[X]) * p.coeff 2 * w1 ^ 3 -
          (3840 : k[X]) * p32 ^ 2 * w1 -
          (7680 : k[X]) * p32 * s1 * w1 ^ 2 +
          (5376 : k[X]) * p32 * u2 * w1 +
          (1920 : k[X]) * q53 * w1 ^ 2)).eval a = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
        Polynomial.eval_ofNat, Polynomial.eval_C]
      linear_combination hcv
    obtain ⟨chi2, hchi2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        (chi + (-(5040 : k[X]) * a41 ^ 2 * Polynomial.C lambda *
            w1 ^ 2 +
          (5760 : k[X]) * a41 * Polynomial.C lambda * p32 * w1 +
          (7680 : k[X]) * a41 * p.coeff 1 +
          (4800 : k[X]) * a41 * p32 * w1 ^ 2 +
          (8960 : k[X]) * a41 * s1 * w1 ^ 3 -
          (6720 : k[X]) * a41 * u2 * w1 ^ 2 -
          (1920 : k[X]) * b62 * w1 ^ 3 +
          (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 * w1 ^ 2 -
          (1152 : k[X]) * Polynomial.C lambda * p32 ^ 2 -
          (4096 : k[X]) * p.coeff 1 * s1 -
          (3200 : k[X]) * p.coeff 2 * w1 ^ 3 -
          (3840 : k[X]) * p32 ^ 2 * w1 -
          (7680 : k[X]) * p32 * s1 * w1 ^ 2 +
          (5376 : k[X]) * p32 * u2 * w1 +
          (1920 : k[X]) * q53 * w1 ^ 2)) a hh0degree hroot hcombz
    obtain ⟨eta, hXrel⟩ :=
      nonzeroFace610_seventhDefectPowerRelation p q H h0 j lambda
        hp hq hh0 hH hp6 hq10 hN hD
    have hXclr :
        localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda =
          h0 ^ 34 * (chi2 +
            ((3780 : k[X]) * a41 * Polynomial.C lambda * w1 ^ 4 -
            (5040 : k[X]) * a41 * w1 ^ 5 -
            (2304 : k[X]) * Polynomial.C lambda * p.coeff 1 * w1 -
            (3360 : k[X]) * Polynomial.C lambda * p32 * w1 ^ 3 +
            (1920 : k[X]) * p.coeff 1 * w1 ^ 2 +
            (4200 : k[X]) * p32 * w1 ^ 4 -
            (2016 : k[X]) * s1 * w1 ^ 5 +
            (1960 : k[X]) * u2 * w1 ^ 4 +
            (1536 : k[X]) * h0 * Polynomial.C lambda * p.coeff 0 -
            (693 : k[X]) * h0 * Polynomial.C lambda * w1 ^ 6 +
            (1320 : k[X]) * h0 * w1 ^ 7)) := by
      simpa [hw, ha4s, hp3u, hs, hq7u, hb6s, hq5u, hq4u] using
        fourteenthFace_clearedX_chi2_610 h0 w1 a41 s1 u2 p32 b62 q53
          (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3) chi chi2
          lambda hchieq hchi2
    have hXcof :
        chi2 + ((3780 : k[X]) * a41 * Polynomial.C lambda * w1 ^ 4 -
            (5040 : k[X]) * a41 * w1 ^ 5 -
            (2304 : k[X]) * Polynomial.C lambda * p.coeff 1 * w1 -
            (3360 : k[X]) * Polynomial.C lambda * p32 * w1 ^ 3 +
            (1920 : k[X]) * p.coeff 1 * w1 ^ 2 +
            (4200 : k[X]) * p32 * w1 ^ 4 -
            (2016 : k[X]) * s1 * w1 ^ 5 +
            (1960 : k[X]) * u2 * w1 ^ 4 +
            (1536 : k[X]) * h0 * Polynomial.C lambda * p.coeff 0 -
            (693 : k[X]) * h0 * Polynomial.C lambda * w1 ^ 6 +
            (1320 : k[X]) * h0 * w1 ^ 7) =
          Polynomial.C eta * h0 := by
      apply mul_left_cancel₀ (pow_ne_zero 34 hh0)
      rw [← hXclr, hXrel]
      ring
    have hzero :
        Polynomial.eval a
            (chi2 + ((3780 : k[X]) * a41 * Polynomial.C lambda *
              w1 ^ 4 -
            (5040 : k[X]) * a41 * w1 ^ 5 -
            (2304 : k[X]) * Polynomial.C lambda * p.coeff 1 * w1 -
            (3360 : k[X]) * Polynomial.C lambda * p32 * w1 ^ 3 +
            (1920 : k[X]) * p.coeff 1 * w1 ^ 2 +
            (4200 : k[X]) * p32 * w1 ^ 4 -
            (2016 : k[X]) * s1 * w1 ^ 5 +
            (1960 : k[X]) * u2 * w1 ^ 4 +
            (1536 : k[X]) * h0 * Polynomial.C lambda * p.coeff 0 -
            (693 : k[X]) * h0 * Polynomial.C lambda * w1 ^ 6 +
            (1320 : k[X]) * h0 * w1 ^ 7)) = 0 := by
      rw [hXcof]
      simp [hroot]
    have hXeval :=
      (eval_fourteenthFace_X_chi2Cofactor610 h0 w1 a41 s1 u2 p32
        (p.coeff 1) (p.coeff 0) chi2 lambda a hroot).symm.trans hzero
    have hChi2form :=
      fourteenthFace_zeroP31_chi2_nextOrder610 (w1.eval a)
        (a41.eval a) (s1.eval a) (p32.eval a) (u2.eval a)
        ((p.coeff 1).eval a) (chi2.eval a) lambda hMs hTform hXeval
    exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u, hTform, hWform, hVform, hQ3form, hchieq, hchival,
      hchi2, hChi2form⟩⟩
  · -- Complementary factor: peel the vanishing `h²⁸` head of the
    -- sixth defect and solve the `h²⁹` order.
    have hpv :=
      fourteenthFace_tp2_psiCombo_vanish610 (w1.eval a) (a41.eval a)
        (s1.eval a) (u1.eval a) (p31.eval a) (b62.eval a)
        ((p.coeff 2).eval a) (psi.eval a) lambda hMs hTu htp hb62form
        hpsival
    have hpz :
        (psi + ((466560 : k[X]) * a41 ^ 2 * Polynomial.C lambda * w1 +
          (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
          (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
          (349920 : k[X]) * b62 * w1 ^ 2 -
          (349920 : k[X]) * Polynomial.C lambda * p.coeff 2 * w1 +
          (466560 : k[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
          (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
          (432000 : k[X]) * p31 * w1 ^ 3 -
          (362880 : k[X]) * u1 * w1 ^ 3)).eval a = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
        Polynomial.eval_ofNat, Polynomial.eval_C]
      linear_combination hpv
    obtain ⟨psi2, hpsi2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        (psi + ((466560 : k[X]) * a41 ^ 2 * Polynomial.C lambda * w1 +
          (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
          (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
          (349920 : k[X]) * b62 * w1 ^ 2 -
          (349920 : k[X]) * Polynomial.C lambda * p.coeff 2 * w1 +
          (466560 : k[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
          (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
          (432000 : k[X]) * p31 * w1 ^ 3 -
          (362880 : k[X]) * u1 * w1 ^ 3)) a hh0degree hroot hpz
    obtain ⟨zeta, hWrel⟩ :=
      nonzeroFace610_sixthDefectPowerRelation p q H h0 j lambda
        hp hq hh0 hH hp6 hq10 hN hD
    have hWclr :
        localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda =
          h0 ^ 29 * (psi2 +
            (-(570240 : k[X]) * a41 * Polynomial.C lambda * w1 ^ 3 +
            (633600 : k[X]) * a41 * w1 ^ 4 +
            (209952 : k[X]) * Polynomial.C lambda * p.coeff 1 +
            (116640 : k[X]) * p.coeff 1 * w1 +
            (380160 : k[X]) * s1 * w1 ^ 4 +
            (133056 : k[X]) * h0 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 * p.coeff 0 -
            (246400 : k[X]) * h0 * w1 ^ 6)) := by
      simpa [hw, ha4s, hp3, hs, hu, hb6s, hq5] using
        fourteenthFace_comp_sixthDefect_psi2_610 h0 w1 a41 s1 u1 p31
          b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
          omega psi psi2 lambda homega hpsieq hpsi2
    have hWcof :
        psi2 + (-(570240 : k[X]) * a41 * Polynomial.C lambda * w1 ^ 3 +
            (633600 : k[X]) * a41 * w1 ^ 4 +
            (209952 : k[X]) * Polynomial.C lambda * p.coeff 1 +
            (116640 : k[X]) * p.coeff 1 * w1 +
            (380160 : k[X]) * s1 * w1 ^ 4 +
            (133056 : k[X]) * h0 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 * p.coeff 0 -
            (246400 : k[X]) * h0 * w1 ^ 6) =
          Polynomial.C zeta * h0 := by
      apply mul_left_cancel₀ (pow_ne_zero 29 hh0)
      rw [← hWclr, hWrel]
      ring
    have hzero :
        Polynomial.eval a
            (psi2 + (-(570240 : k[X]) * a41 * Polynomial.C lambda *
              w1 ^ 3 +
            (633600 : k[X]) * a41 * w1 ^ 4 +
            (209952 : k[X]) * Polynomial.C lambda * p.coeff 1 +
            (116640 : k[X]) * p.coeff 1 * w1 +
            (380160 : k[X]) * s1 * w1 ^ 4 +
            (133056 : k[X]) * h0 * Polynomial.C lambda * w1 ^ 5 -
            (699840 : k[X]) * h0 * p.coeff 0 -
            (246400 : k[X]) * h0 * w1 ^ 6)) = 0 := by
      rw [hWcof]
      simp [hroot]
    have hWeval :=
      (eval_fourteenthFace_comp_psi2Cofactor610 h0 w1 a41 s1
        (p.coeff 1) (p.coeff 0) psi2 lambda a hroot).symm.trans hzero
    have hpsi2val :=
      fourteenthFace_tp2_psi2_nextOrder610 (w1.eval a) (a41.eval a)
        (s1.eval a) ((p.coeff 1).eval a) (psi2.eval a) lambda hMs
        hWeval
    exact Or.inr ⟨htp, hb62form, omega, psi, psi2, homega, homegaval,
      hpsieq, hpsival, hpsi2, hpsi2val⟩

set_option maxHeartbeats 8000000 in
/-- Source-facing fourteenth-face power jet of a normalized scale-two
`(6,10)` nonzero face: both thirteenth-face alternatives are refined at
the last leftover order before the ground constants. -/
theorem normalized610ScaleTwo_nonzeroFace_fourteenthPowerJet
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
            ∃ (p32 u2 q53 q41 chi chi2 : K[X]),
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
                    0 ∧
                (960 : K[X]) * a41 ^ 3 * Polynomial.C lambda +
                    (6400 : K[X]) * a41 ^ 3 * w1 -
                    (9600 : K[X]) * a41 ^ 2 * p32 -
                    (7680 : K[X]) * a41 ^ 2 * s1 * w1 +
                    (2688 : K[X]) * a41 ^ 2 * u2 +
                    (4608 : K[X]) * a41 * b62 * w1 -
                    (2304 : K[X]) * a41 * Polynomial.C lambda *
                      p.coeff 2 -
                    (7680 : K[X]) * a41 * p.coeff 2 * w1 +
                    (6144 : K[X]) * a41 * p32 * s1 -
                    (2560 : K[X]) * a41 * q53 -
                    (3072 : K[X]) * b62 * p32 +
                    (7680 : K[X]) * p.coeff 2 * p32 +
                    (6144 : K[X]) * p.coeff 2 * s1 * w1 -
                    (3584 : K[X]) * p.coeff 2 * u2 +
                    (3072 : K[X]) * q.coeff 3 -
                    (2048 : K[X]) * q41 * w1 = h0 * chi ∧
                (9 : K) * chi.eval a =
                  (17280 : K) * lambda * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 2 -
                    (54400 : K) * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 3 -
                    (27648 : K) * lambda * a41.eval a * p32.eval a *
                      w1.eval a -
                    (7680 : K) * a41.eval a * (p.coeff 1).eval a +
                    (99840 : K) * a41.eval a * p32.eval a *
                      (w1.eval a) ^ 2 -
                    (17280 : K) * lambda * (p.coeff 2).eval a *
                      (w1.eval a) ^ 2 +
                    (10368 : K) * lambda * (p32.eval a) ^ 2 +
                    (38400 : K) * (p.coeff 2).eval a *
                      (w1.eval a) ^ 3 -
                    (46080 : K) * (p32.eval a) ^ 2 * w1.eval a ∧
                chi + (-(5040 : K[X]) * a41 ^ 2 * Polynomial.C lambda *
                    w1 ^ 2 +
                  (5760 : K[X]) * a41 * Polynomial.C lambda * p32 *
                    w1 +
                  (7680 : K[X]) * a41 * p.coeff 1 +
                  (4800 : K[X]) * a41 * p32 * w1 ^ 2 +
                  (8960 : K[X]) * a41 * s1 * w1 ^ 3 -
                  (6720 : K[X]) * a41 * u2 * w1 ^ 2 -
                  (1920 : K[X]) * b62 * w1 ^ 3 +
                  (2880 : K[X]) * Polynomial.C lambda * p.coeff 2 *
                    w1 ^ 2 -
                  (1152 : K[X]) * Polynomial.C lambda * p32 ^ 2 -
                  (4096 : K[X]) * p.coeff 1 * s1 -
                  (3200 : K[X]) * p.coeff 2 * w1 ^ 3 -
                  (3840 : K[X]) * p32 ^ 2 * w1 -
                  (7680 : K[X]) * p32 * s1 * w1 ^ 2 +
                  (5376 : K[X]) * p32 * u2 * w1 +
                  (1920 : K[X]) * q53 * w1 ^ 2) = h0 * chi2 ∧
                (9 : K) * chi2.eval a =
                  (16 : K) * w1.eval a *
                    ((1296 : K) * lambda * (p.coeff 1).eval a -
                      (1080 : K) * (p.coeff 1).eval a * w1.eval a +
                      (1890 : K) * lambda * p32.eval a *
                        (w1.eval a) ^ 2 -
                      (1575 : K) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4200 : K) * p32.eval a * (w1.eval a) ^ 3 +
                    (3500 : K) * a41.eval a * (w1.eval a) ^ 4)) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            ∃ (omega psi psi2 : K[X]),
              (583200 : K[X]) * p31 ^ 2 -
                  (489888 : K[X]) * p31 * u1 +
                (419904 : K[X]) * q.coeff 4 = h0 * omega ∧
              omega.eval a =
                (648 : K) * a41.eval a *
                  ((80 : K) * (a41.eval a) ^ 2 +
                      (297 : K) * lambda * p31.eval a -
                    (960 : K) * p31.eval a * w1.eval a) ∧
              omega + (-(518400 : K[X]) * a41 ^ 3 +
                  (466560 : K[X]) * a41 ^ 2 * s1 -
                  (419904 : K[X]) * a41 * b62 -
                  (349920 : K[X]) * a41 * Polynomial.C lambda * p31 +
                  (1166400 : K[X]) * a41 * p.coeff 2 -
                  (1360800 : K[X]) * a41 * p31 * w1 +
                  (816480 : K[X]) * a41 * u1 * w1 -
                  (559872 : K[X]) * p.coeff 2 * s1 +
                  (933120 : K[X]) * p31 * s1 * w1 -
                  (349920 : K[X]) * q52 * w1) = h0 * psi ∧
              psi.eval a =
                (162 : K) * w1.eval a *
                  ((7600 : K) * (a41.eval a) ^ 2 * w1.eval a -
                      (2520 : K) * lambda * (a41.eval a) ^ 2 +
                      (243 : K) * lambda ^ 2 * p31.eval a -
                      (1980 : K) * lambda * p31.eval a * w1.eval a +
                    (3200 : K) * p31.eval a *
                      (w1.eval a) ^ 2) ∧
              psi + ((466560 : K[X]) * a41 ^ 2 * Polynomial.C lambda *
                  w1 +
                (518400 : K[X]) * a41 ^ 2 * w1 ^ 2 -
                (1244160 : K[X]) * a41 * s1 * w1 ^ 2 +
                (349920 : K[X]) * b62 * w1 ^ 2 -
                (349920 : K[X]) * Polynomial.C lambda * p.coeff 2 *
                  w1 +
                (466560 : K[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
                (194400 : K[X]) * p.coeff 2 * w1 ^ 2 -
                (432000 : K[X]) * p31 * w1 ^ 3 -
                (362880 : K[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
              psi2.eval a =
                (288 : K) * ((1980 : K) * lambda * a41.eval a *
                    (w1.eval a) ^ 3 -
                  (4400 : K) * a41.eval a * (w1.eval a) ^ 4 -
                  (729 : K) * lambda * (p.coeff 1).eval a -
                  (405 : K) * (p.coeff 1).eval a * w1.eval a))) ∧
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
    nonzeroFace610_linearRoot_fourteenthPowerJet p q H h0 j lambda a
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
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u, hTform, hWform, hVform, hQ3form, hchieq, hchival,
      hchi2eq, hchi2val⟩⟩ |
      ⟨htp, hb62form, omega, psi, psi2, homega, homegaval, hpsieq,
        hpsival, hpsi2eq, hpsi2val⟩
  · exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u,
      (by rw [hp3u]; exact dvd_mul_right _ _),
      (by rw [hq7u]; exact dvd_mul_right _ _),
      (by rw [hq5u]; exact dvd_mul_right _ _),
      (by rw [hq4u]; exact dvd_mul_right _ _),
      hTform, hWform, hVform, hQ3form, hchieq, hchival, hchi2eq,
      hchi2val⟩⟩
  · exact Or.inr ⟨htp, hb62form, omega, psi, psi2, homega, homegaval,
      hpsieq, hpsival, hpsi2eq, hpsi2val⟩

end NonzeroFourteenthFace610

#print axioms fourteenthCoefficientJacobianRow_610
#print axioms fourteenthFace_zeroP31_chiCombo_vanish610
#print axioms fourteenthFace_zeroP31_chi2_nextOrder610
#print axioms fourteenthFace_tp2_psiCombo_vanish610
#print axioms fourteenthFace_tp2_psi2_nextOrder610
#print axioms fourteenthFace_clearedX_chi2_610
#print axioms eval_fourteenthFace_X_chi2Cofactor610
#print axioms fourteenthFace_comp_sixthDefect_psi2_610
#print axioms eval_fourteenthFace_comp_psi2Cofactor610
#print axioms nonzeroFace610_linearRoot_fourteenthPowerJet
#print axioms normalized610ScaleTwo_nonzeroFace_fourteenthPowerJet

end Max11DegreeRoutes
