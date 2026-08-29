import LowScale610ScaleTwoEighthFace

/-! # Scale-two ninth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the eighth-face packet supplies the degree-`7`
Jacobian row and the one-parameter root jet `h⁴ ∣ p₅`, `h² ∣ p₄`,
`h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`, `h⁸ ∣ q₉` together with
`3 (p₄/h²)(a) = w²`, `9 (q₈/h⁶)(a) = 10 w²`, `27 p₃(a) = w³`,
`27 (q₇/h⁴)(a) = 10 w³`, `81 (q₆/h²)(a) = 5 w⁴`, and
`243 q₅(a) = w⁵` on `w = (p₅/h⁴)(a)`.

The next unused Keller coefficient is the degree-`6` Jacobian row.  After
the same sextic depression that kills `z⁵`, that row is
`7 Q E' + 6 R D' + 5 S C' + 4 T B' + 3 U A' - D R' - 2 C S' - 3 B T'
- 4 A U' - 6 W' = 0`.  Clearing the corresponding first integral against
the `z¹` decic coordinate produces a defect of weight forty-five, larger
than the remaining exact jet, so this file isolates that Jacobian
identity and the strongest exact refinement of the eighth-face jet.

Evaluating the second through sixth defects at the next order on the
eighth-face power jet forces the compatibility `λ w⁵ = 0`.  On the
nonzero face this collapses `w(a) = 0`, upgrades the jet to
`h⁵ ∣ p₅`, `h³ ∣ p₄`, `h ∣ p₃`, `h⁷ ∣ q₈`, `h⁵ ∣ q₇`, `h⁴ ∣ q₆`,
`h² ∣ q₅`, and `h⁸ ∣ q₉`, and yields the next-order identities
`S₁(a) = 5 A₁(a)` and `5 P₃₁(a) = 3 U₁(a)` together with
`B₆₁(a) = Q₅₁(a) = 0`.  No further individual vanishing of
`p₂, p₁, p₀, q₄, q₃` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The ninth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the eighth face start
at degree `6`. -/
theorem ninthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 1 * Polynomial.C (1 : K)) +
        (p.coeff 5).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 1).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 2).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 6).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC2, hC3, hC4, hC5, hC6, hC7]
  linear_combination hcoeff

/-! ## Order-one scalar algebra on the eighth-face power jet -/

section NinthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The second through sixth defects at the next order on the eighth-face
power jet are compatible only if `λ w⁵ = 0`. -/
theorem ninthFace_lambda_w5_610 (w A1 S1 P31 U1 B61 Q51 lambda : F)
    (hM : (2 : F) * S1 - (10 : F) * A1 + (9 : F) * lambda * w = 0)
    (hT : (240 : F) * A1 * w - (40 : F) * P31 - (96 : F) * S1 * w +
        (24 : F) * U1 - (243 : F) * lambda * w ^ 2 = 0)
    (hU : -(160 : F) * A1 * w ^ 2 + (16 : F) * B61 +
        (40 : F) * P31 * w + (128 : F) * S1 * w ^ 2 -
        (56 : F) * U1 * w + (240 : F) * lambda * w ^ 3 = 0)
    (hV : (2400 : F) * A1 * w ^ 3 - (1152 : F) * B61 * w -
        (720 : F) * P31 * w ^ 2 + (384 : F) * Q51 -
        (4032 : F) * S1 * w ^ 3 + (2352 : F) * U1 * w ^ 2 -
        (6237 : F) * lambda * w ^ 4 = 0)
    (hW : -(1440 : F) * A1 * w ^ 4 + (2592 : F) * B61 * w ^ 2 +
        (480 : F) * P31 * w ^ 3 - (1440 : F) * Q51 * w +
        (5760 : F) * S1 * w ^ 4 - (4032 : F) * U1 * w ^ 3 +
        (7776 : F) * lambda * w ^ 5 = 0) :
    lambda * w ^ 5 = 0 := by
  have h567 : (567 : F) ≠ 0 := by norm_num
  have hid :
      (1152 : F) * w ^ 4 *
            ((2 : F) * S1 - (10 : F) * A1 + (9 : F) * lambda * w) +
          (210 : F) * w ^ 3 *
            ((240 : F) * A1 * w - (40 : F) * P31 - (96 : F) * S1 * w +
              (24 : F) * U1 - (243 : F) * lambda * w ^ 2) +
          (432 : F) * w ^ 2 *
            (-(160 : F) * A1 * w ^ 2 + (16 : F) * B61 +
              (40 : F) * P31 * w + (128 : F) * S1 * w ^ 2 -
              (56 : F) * U1 * w + (240 : F) * lambda * w ^ 3) +
          (15 : F) * w *
            ((2400 : F) * A1 * w ^ 3 - (1152 : F) * B61 * w -
              (720 : F) * P31 * w ^ 2 + (384 : F) * Q51 -
              (4032 : F) * S1 * w ^ 3 + (2352 : F) * U1 * w ^ 2 -
              (6237 : F) * lambda * w ^ 4) +
          (4 : F) *
            (-(1440 : F) * A1 * w ^ 4 + (2592 : F) * B61 * w ^ 2 +
              (480 : F) * P31 * w ^ 3 - (1440 : F) * Q51 * w +
              (5760 : F) * S1 * w ^ 4 - (4032 : F) * U1 * w ^ 3 +
              (7776 : F) * lambda * w ^ 5) =
        (567 : F) * (lambda * w ^ 5) := by
    ring
  have hcomb : (567 : F) * (lambda * w ^ 5) = 0 := by
    rw [← hid]
    linear_combination (1152 : F) * w ^ 4 * hM +
      (210 : F) * w ^ 3 * hT + (432 : F) * w ^ 2 * hU +
      (15 : F) * w * hV + (4 : F) * hW
  exact (mul_eq_zero.mp hcomb).resolve_left h567

/-- After the collapse `w(a) = 0`, the same next-order coefficients force
`S₁ = 5 A₁`, `5 P₃₁ = 3 U₁`, and `B₆₁ = Q₅₁ = 0`. -/
theorem ninthFace_zeroW_nextOrder610 (A1 S1 P31 U1 B61 Q51 : F)
    (hM : (2 : F) * S1 - (10 : F) * A1 = 0)
    (hT : -(40 : F) * P31 + (24 : F) * U1 = 0)
    (hU : (16 : F) * B61 = 0)
    (hV : (384 : F) * Q51 = 0) :
    S1 = (5 : F) * A1 ∧ (5 : F) * P31 = (3 : F) * U1 ∧
      B61 = 0 ∧ Q51 = 0 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h384 : (384 : F) ≠ 0 := by norm_num
  have hs : S1 = (5 : F) * A1 := by
    have hid : (2 : F) * (S1 - (5 : F) * A1) =
        (2 : F) * S1 - (10 : F) * A1 := by ring
    have : (2 : F) * (S1 - (5 : F) * A1) = 0 := by
      rw [hid, hM]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  have hp : (5 : F) * P31 = (3 : F) * U1 := by
    have hid : (8 : F) * ((5 : F) * P31 - (3 : F) * U1) =
        (40 : F) * P31 - (24 : F) * U1 := by ring
    have : (8 : F) * ((5 : F) * P31 - (3 : F) * U1) = 0 := by
      rw [hid]
      linear_combination -hT
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h8)
  have hb : B61 = 0 :=
    (mul_eq_zero.mp hU).resolve_left h16
  have hq : Q51 = 0 :=
    (mul_eq_zero.mp hV).resolve_left h384
  exact ⟨hs, hp, hb, hq⟩

/-! ## Integer jet parentheticals of the second through sixth defects -/

theorem ninthFace_M_mul_h610 (h w a4s s A1 S1 : F[X]) (lambda : F)
    (hA : (3 : F[X]) * a4s - w ^ 2 = h * A1)
    (hS : (9 : F[X]) * s - (10 : F[X]) * w ^ 2 = h * S1) :
    (18 : F[X]) * s - (30 : F[X]) * a4s - (10 : F[X]) * w ^ 2 +
        (9 : F[X]) * Polynomial.C lambda * w * h =
      h * ((2 : F[X]) * S1 - (10 : F[X]) * A1 +
        (9 : F[X]) * Polynomial.C lambda * w) := by
  have hid :
      (18 : F[X]) * s - (30 : F[X]) * a4s - (10 : F[X]) * w ^ 2 +
          (9 : F[X]) * Polynomial.C lambda * w * h =
        -(10 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) +
          (2 : F[X]) * ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) +
          (9 : F[X]) * Polynomial.C lambda * w * h := by
    ring
  rw [hid, hA, hS]
  ring

theorem ninthFace_T_mul_h610 (h w a4s s u p3 A1 S1 P31 U1 : F[X])
    (lambda : F) (hA : (3 : F[X]) * a4s - w ^ 2 = h * A1)
    (hS : (9 : F[X]) * s - (10 : F[X]) * w ^ 2 = h * S1)
    (hP : (27 : F[X]) * p3 - w ^ 3 = h * P31)
    (hU : (27 : F[X]) * u - (10 : F[X]) * w ^ 3 = h * U1) :
    (648 : F[X]) * u + (720 : F[X]) * a4s * w - (864 : F[X]) * s * w +
        (520 : F[X]) * w ^ 3 - (1080 : F[X]) * p3 +
        ((324 : F[X]) * Polynomial.C lambda * a4s -
            (351 : F[X]) * Polynomial.C lambda * w ^ 2) * h =
      h * ((108 : F[X]) * A1 * h * Polynomial.C lambda +
          (240 : F[X]) * A1 * w - (40 : F[X]) * P31 -
          (96 : F[X]) * S1 * w + (24 : F[X]) * U1 -
          (243 : F[X]) * Polynomial.C lambda * w ^ 2) := by
  have hid :
      (648 : F[X]) * u + (720 : F[X]) * a4s * w - (864 : F[X]) * s * w +
          (520 : F[X]) * w ^ 3 - (1080 : F[X]) * p3 +
          ((324 : F[X]) * Polynomial.C lambda * a4s -
              (351 : F[X]) * Polynomial.C lambda * w ^ 2) * h =
        (108 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * h *
            Polynomial.C lambda +
          (240 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * w -
          (40 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) -
          (96 : F[X]) * ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) * w +
          (24 : F[X]) * ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) -
          (243 : F[X]) * h * Polynomial.C lambda * w ^ 2 := by
    ring
  rw [hid, hA, hS, hP, hU]
  ring

set_option maxHeartbeats 8000000 in
theorem ninthFace_U_mul_h610 (h w a4s s u p3 b6s p2 A1 S1 P31 U1 B61 :
    F[X]) (lambda : F) (hA : (3 : F[X]) * a4s - w ^ 2 = h * A1)
    (hS : (9 : F[X]) * s - (10 : F[X]) * w ^ 2 = h * S1)
    (hP : (27 : F[X]) * p3 - w ^ 3 = h * P31)
    (hU : (27 : F[X]) * u - (10 : F[X]) * w ^ 3 = h * U1)
    (hB : (81 : F[X]) * b6s - (5 : F[X]) * w ^ 4 = h * B61) :
    (3 : F[X]) *
        ((432 : F[X]) * b6s + (720 : F[X]) * a4s ^ 2 -
            (576 : F[X]) * a4s * s - (504 : F[X]) * w * u +
            (360 : F[X]) * w * p3 - (360 : F[X]) * w ^ 4 +
            (576 : F[X]) * s * w ^ 2 +
            ((216 : F[X]) * Polynomial.C lambda * w ^ 3 -
                (432 : F[X]) * Polynomial.C lambda * w * a4s +
                (216 : F[X]) * Polynomial.C lambda * p3) * h -
            (720 : F[X]) * p2 * h ^ 2) =
      h * ((240 : F[X]) * A1 ^ 2 * h - (64 : F[X]) * A1 * S1 * h -
          (432 : F[X]) * A1 * h * Polynomial.C lambda * w -
          (160 : F[X]) * A1 * w ^ 2 + (16 : F[X]) * B61 +
          (24 : F[X]) * P31 * h * Polynomial.C lambda +
          (40 : F[X]) * P31 * w + (128 : F[X]) * S1 * w ^ 2 -
          (56 : F[X]) * U1 * w - (2160 : F[X]) * h * p2 +
          (240 : F[X]) * Polynomial.C lambda * w ^ 3) := by
  have hid :
      (3 : F[X]) *
          ((432 : F[X]) * b6s + (720 : F[X]) * a4s ^ 2 -
              (576 : F[X]) * a4s * s - (504 : F[X]) * w * u +
              (360 : F[X]) * w * p3 - (360 : F[X]) * w ^ 4 +
              (576 : F[X]) * s * w ^ 2 +
              ((216 : F[X]) * Polynomial.C lambda * w ^ 3 -
                  (432 : F[X]) * Polynomial.C lambda * w * a4s +
                  (216 : F[X]) * Polynomial.C lambda * p3) * h -
              (720 : F[X]) * p2 * h ^ 2) =
        (240 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 2 -
          (64 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) -
          (432 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * h *
            Polynomial.C lambda * w -
          (160 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * w ^ 2 +
          (16 : F[X]) * ((81 : F[X]) * b6s - (5 : F[X]) * w ^ 4) +
          (24 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) * h *
            Polynomial.C lambda +
          (40 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) * w +
          (128 : F[X]) * ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) *
            w ^ 2 -
          (56 : F[X]) * ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) * w -
          (2160 : F[X]) * h ^ 2 * p2 +
          (240 : F[X]) * h * Polynomial.C lambda * w ^ 3 := by
    ring
  rw [hid, hA, hS, hP, hU, hB]
  ring

set_option maxHeartbeats 12000000 in
theorem ninthFace_V_mul_h610 (h w a4s s u p3 b6s q5 p2 p1 A1 S1 P31 U1
    B61 Q51 : F[X]) (lambda : F)
    (hA : (3 : F[X]) * a4s - w ^ 2 = h * A1)
    (hS : (9 : F[X]) * s - (10 : F[X]) * w ^ 2 = h * S1)
    (hP : (27 : F[X]) * p3 - w ^ 3 = h * P31)
    (hU : (27 : F[X]) * u - (10 : F[X]) * w ^ 3 = h * U1)
    (hB : (81 : F[X]) * b6s - (5 : F[X]) * w ^ 4 = h * B61)
    (hQ : (243 : F[X]) * q5 - w ^ 5 = h * Q51) :
    (285120 : F[X]) * a4s * p3 + (23760 : F[X]) * w ^ 2 * p3 -
        (124416 : F[X]) * s * p3 - (190080 : F[X]) * w * a4s ^ 2 -
        (89760 : F[X]) * w ^ 3 * a4s + (228096 : F[X]) * w * a4s * s -
        (108864 : F[X]) * a4s * u + (68816 : F[X]) * w ^ 5 -
        (107712 : F[X]) * w ^ 3 * s + (99792 : F[X]) * w ^ 2 * u -
        (93312 : F[X]) * w * b6s + (93312 : F[X]) * q5 +
        ((-85536 : F[X]) * Polynomial.C lambda * p3 * w -
            (42768 : F[X]) * Polynomial.C lambda * a4s ^ 2 +
            (121176 : F[X]) * Polynomial.C lambda * a4s * w ^ 2 -
            (38709 : F[X]) * Polynomial.C lambda * w ^ 4) * h +
          (51840 : F[X]) * w * p2 * h ^ 2 +
            (46656 : F[X]) * Polynomial.C lambda * p2 * h ^ 3 -
              (155520 : F[X]) * p1 * h ^ 4 =
      h * (-(4752 : F[X]) * A1 ^ 2 * h ^ 2 * Polynomial.C lambda -
          (21120 : F[X]) * A1 ^ 2 * h * w +
          (3520 : F[X]) * A1 * P31 * h +
          (8448 : F[X]) * A1 * S1 * h * w -
          (1344 : F[X]) * A1 * U1 * h +
          (30888 : F[X]) * A1 * h * Polynomial.C lambda * w ^ 2 +
          (2400 : F[X]) * A1 * w ^ 3 - (1152 : F[X]) * B61 * w -
          (512 : F[X]) * P31 * S1 * h -
          (3168 : F[X]) * P31 * h * Polynomial.C lambda * w -
          (720 : F[X]) * P31 * w ^ 2 + (384 : F[X]) * Q51 -
          (4032 : F[X]) * S1 * w ^ 3 + (2352 : F[X]) * U1 * w ^ 2 -
          (155520 : F[X]) * h ^ 3 * p1 +
          (46656 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 +
          (51840 : F[X]) * h * p2 * w -
          (6237 : F[X]) * Polynomial.C lambda * w ^ 4) := by
  have hid :
      (285120 : F[X]) * a4s * p3 + (23760 : F[X]) * w ^ 2 * p3 -
          (124416 : F[X]) * s * p3 - (190080 : F[X]) * w * a4s ^ 2 -
          (89760 : F[X]) * w ^ 3 * a4s +
          (228096 : F[X]) * w * a4s * s - (108864 : F[X]) * a4s * u +
          (68816 : F[X]) * w ^ 5 - (107712 : F[X]) * w ^ 3 * s +
          (99792 : F[X]) * w ^ 2 * u - (93312 : F[X]) * w * b6s +
          (93312 : F[X]) * q5 +
          ((-85536 : F[X]) * Polynomial.C lambda * p3 * w -
              (42768 : F[X]) * Polynomial.C lambda * a4s ^ 2 +
              (121176 : F[X]) * Polynomial.C lambda * a4s * w ^ 2 -
              (38709 : F[X]) * Polynomial.C lambda * w ^ 4) * h +
            (51840 : F[X]) * w * p2 * h ^ 2 +
              (46656 : F[X]) * Polynomial.C lambda * p2 * h ^ 3 -
                (155520 : F[X]) * p1 * h ^ 4 =
        -(4752 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 2 * h *
            Polynomial.C lambda -
          (21120 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 2 * w +
          (3520 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((27 : F[X]) * p3 - w ^ 3) +
          (8448 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) * w -
          (1344 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) +
          (30888 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * h *
            Polynomial.C lambda * w ^ 2 +
          (2400 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * w ^ 3 -
          (1152 : F[X]) * ((81 : F[X]) * b6s - (5 : F[X]) * w ^ 4) *
            w -
          (512 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) *
            ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) -
          (3168 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) * h *
            Polynomial.C lambda * w -
          (720 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) * w ^ 2 +
          (384 : F[X]) * ((243 : F[X]) * q5 - w ^ 5) -
          (4032 : F[X]) * ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) *
            w ^ 3 +
          (2352 : F[X]) * ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) *
            w ^ 2 -
          (155520 : F[X]) * h ^ 4 * p1 +
          (46656 : F[X]) * h ^ 3 * Polynomial.C lambda * p2 +
          (51840 : F[X]) * h ^ 2 * p2 * w -
          (6237 : F[X]) * h * Polynomial.C lambda * w ^ 4 := by
    ring
  rw [hid, hA, hS, hP, hU, hB, hQ]
  ring

set_option maxHeartbeats 16000000 in
theorem ninthFace_W_mul_h610 (h w a4s s u p3 b6s q5 p2 p1 p0 q4 A1 S1
    P31 U1 B61 Q51 : F[X]) (lambda : F)
    (hA : (3 : F[X]) * a4s - w ^ 2 = h * A1)
    (hS : (9 : F[X]) * s - (10 : F[X]) * w ^ 2 = h * S1)
    (hP : (27 : F[X]) * p3 - w ^ 3 = h * P31)
    (hU : (27 : F[X]) * u - (10 : F[X]) * w ^ 3 = h * U1)
    (hB : (81 : F[X]) * b6s - (5 : F[X]) * w ^ 4 = h * B61)
    (hQ : (243 : F[X]) * q5 - w ^ 5 = h * Q51) :
    (583200 : F[X]) * p3 ^ 2 - (1360800 : F[X]) * w * a4s * p3 -
        (432000 : F[X]) * w ^ 3 * p3 + (933120 : F[X]) * w * s * p3 -
        (489888 : F[X]) * u * p3 - (518400 : F[X]) * a4s ^ 3 +
        (518400 : F[X]) * w ^ 2 * a4s ^ 2 +
        (466560 : F[X]) * a4s ^ 2 * s +
        (633600 : F[X]) * w ^ 4 * a4s -
        (1244160 : F[X]) * w ^ 2 * a4s * s +
        (816480 : F[X]) * w * a4s * u - (419904 : F[X]) * a4s * b6s -
        (246400 : F[X]) * w ^ 6 + (380160 : F[X]) * w ^ 4 * s -
        (362880 : F[X]) * w ^ 3 * u + (349920 : F[X]) * w ^ 2 * b6s -
        (349920 : F[X]) * w * q5 +
        ((-349920 : F[X]) * Polynomial.C lambda * a4s * p3 +
            (466560 : F[X]) * Polynomial.C lambda * w ^ 2 * p3 +
            (466560 : F[X]) * Polynomial.C lambda * w * a4s ^ 2 -
            (570240 : F[X]) * Polynomial.C lambda * w ^ 3 * a4s +
            (133056 : F[X]) * Polynomial.C lambda * w ^ 5) * h +
          ((1166400 : F[X]) * a4s * p2 +
              (194400 : F[X]) * w ^ 2 * p2 -
            (559872 : F[X]) * s * p2 +
              (419904 : F[X]) * q4) * h ^ 2 +
            (-(349920 : F[X]) * Polynomial.C lambda * p2 * w) * h ^ 3 +
              (116640 : F[X]) * p1 * w * h ^ 4 +
                (209952 : F[X]) * Polynomial.C lambda * p1 * h ^ 5 -
                  (699840 : F[X]) * p0 * h ^ 6 =
      h * (-(19200 : F[X]) * A1 ^ 3 * h ^ 2 +
          (5760 : F[X]) * A1 ^ 2 * S1 * h ^ 2 +
          (51840 : F[X]) * A1 ^ 2 * h ^ 2 * Polynomial.C lambda * w +
          (57600 : F[X]) * A1 ^ 2 * h * w ^ 2 -
          (1728 : F[X]) * A1 * B61 * h -
          (4320 : F[X]) * A1 * P31 * h ^ 2 * Polynomial.C lambda -
          (16800 : F[X]) * A1 * P31 * h * w -
          (34560 : F[X]) * A1 * S1 * h * w ^ 2 +
          (10080 : F[X]) * A1 * U1 * h * w +
          (388800 : F[X]) * A1 * h ^ 2 * p2 -
          (90720 : F[X]) * A1 * h * Polynomial.C lambda * w ^ 3 -
          (1440 : F[X]) * A1 * w ^ 4 + (2592 : F[X]) * B61 * w ^ 2 +
          (800 : F[X]) * P31 ^ 2 * h +
          (3840 : F[X]) * P31 * S1 * h * w -
          (672 : F[X]) * P31 * U1 * h +
          (12960 : F[X]) * P31 * h * Polynomial.C lambda * w ^ 2 +
          (480 : F[X]) * P31 * w ^ 3 - (1440 : F[X]) * Q51 * w -
          (62208 : F[X]) * S1 * h ^ 2 * p2 +
          (5760 : F[X]) * S1 * w ^ 4 - (4032 : F[X]) * U1 * w ^ 3 -
          (699840 : F[X]) * h ^ 5 * p0 +
          (209952 : F[X]) * h ^ 4 * Polynomial.C lambda * p1 +
          (116640 : F[X]) * h ^ 3 * p1 * w -
          (349920 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 * w -
          (38880 : F[X]) * h * p2 * w ^ 2 +
          (419904 : F[X]) * h * q4 +
          (7776 : F[X]) * Polynomial.C lambda * w ^ 5) := by
  have hid :
      (583200 : F[X]) * p3 ^ 2 - (1360800 : F[X]) * w * a4s * p3 -
          (432000 : F[X]) * w ^ 3 * p3 +
          (933120 : F[X]) * w * s * p3 - (489888 : F[X]) * u * p3 -
          (518400 : F[X]) * a4s ^ 3 +
          (518400 : F[X]) * w ^ 2 * a4s ^ 2 +
          (466560 : F[X]) * a4s ^ 2 * s +
          (633600 : F[X]) * w ^ 4 * a4s -
          (1244160 : F[X]) * w ^ 2 * a4s * s +
          (816480 : F[X]) * w * a4s * u -
          (419904 : F[X]) * a4s * b6s - (246400 : F[X]) * w ^ 6 +
          (380160 : F[X]) * w ^ 4 * s - (362880 : F[X]) * w ^ 3 * u +
          (349920 : F[X]) * w ^ 2 * b6s - (349920 : F[X]) * w * q5 +
          ((-349920 : F[X]) * Polynomial.C lambda * a4s * p3 +
              (466560 : F[X]) * Polynomial.C lambda * w ^ 2 * p3 +
              (466560 : F[X]) * Polynomial.C lambda * w * a4s ^ 2 -
              (570240 : F[X]) * Polynomial.C lambda * w ^ 3 * a4s +
              (133056 : F[X]) * Polynomial.C lambda * w ^ 5) * h +
            ((1166400 : F[X]) * a4s * p2 +
                (194400 : F[X]) * w ^ 2 * p2 -
              (559872 : F[X]) * s * p2 +
                (419904 : F[X]) * q4) * h ^ 2 +
              (-(349920 : F[X]) * Polynomial.C lambda * p2 * w) *
                  h ^ 3 +
                (116640 : F[X]) * p1 * w * h ^ 4 +
                  (209952 : F[X]) * Polynomial.C lambda * p1 * h ^ 5 -
                    (699840 : F[X]) * p0 * h ^ 6 =
        -(19200 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 3 +
          (5760 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 2 *
            ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) +
          (51840 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 2 * h *
            Polynomial.C lambda * w +
          (57600 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) ^ 2 * w ^ 2 -
          (1728 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((81 : F[X]) * b6s - (5 : F[X]) * w ^ 4) -
          (4320 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((27 : F[X]) * p3 - w ^ 3) * h * Polynomial.C lambda -
          (16800 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((27 : F[X]) * p3 - w ^ 3) * w -
          (34560 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) * w ^ 2 +
          (10080 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) *
            ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) * w +
          (388800 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * h ^ 2 * p2 -
          (90720 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * h *
            Polynomial.C lambda * w ^ 3 -
          (1440 : F[X]) * ((3 : F[X]) * a4s - w ^ 2) * w ^ 4 +
          (2592 : F[X]) * ((81 : F[X]) * b6s - (5 : F[X]) * w ^ 4) *
            w ^ 2 +
          (800 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) ^ 2 +
          (3840 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) *
            ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) * w -
          (672 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) *
            ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) +
          (12960 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) * h *
            Polynomial.C lambda * w ^ 2 +
          (480 : F[X]) * ((27 : F[X]) * p3 - w ^ 3) * w ^ 3 -
          (1440 : F[X]) * ((243 : F[X]) * q5 - w ^ 5) * w -
          (62208 : F[X]) * ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) *
            h ^ 2 * p2 +
          (5760 : F[X]) * ((9 : F[X]) * s - (10 : F[X]) * w ^ 2) *
            w ^ 4 -
          (4032 : F[X]) * ((27 : F[X]) * u - (10 : F[X]) * w ^ 3) *
            w ^ 3 -
          (699840 : F[X]) * h ^ 6 * p0 +
          (209952 : F[X]) * h ^ 5 * Polynomial.C lambda * p1 +
          (116640 : F[X]) * h ^ 4 * p1 * w -
          (349920 : F[X]) * h ^ 3 * Polynomial.C lambda * p2 * w -
          (38880 : F[X]) * h ^ 2 * p2 * w ^ 2 +
          (419904 : F[X]) * h ^ 2 * q4 +
          (7776 : F[X]) * h * Polynomial.C lambda * w ^ 5 := by
    ring
  rw [hid, hA, hS, hP, hU, hB, hQ]
  ring

theorem eval_ninthFace_M_cofactor610 (h w A1 S1 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((2 : F[X]) * S1 - (10 : F[X]) * A1 +
          (9 : F[X]) * Polynomial.C lambda * w) =
      (2 : F) * Polynomial.eval root S1 -
        (10 : F) * Polynomial.eval root A1 +
        (9 : F) * lambda * Polynomial.eval root w := by
  simp [hroot]

theorem eval_ninthFace_T_cofactor610 (h w A1 S1 P31 U1 : F[X])
    (lambda : F) (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((108 : F[X]) * A1 * h * Polynomial.C lambda +
          (240 : F[X]) * A1 * w - (40 : F[X]) * P31 -
          (96 : F[X]) * S1 * w + (24 : F[X]) * U1 -
          (243 : F[X]) * Polynomial.C lambda * w ^ 2) =
      (240 : F) * Polynomial.eval root A1 * Polynomial.eval root w -
        (40 : F) * Polynomial.eval root P31 -
        (96 : F) * Polynomial.eval root S1 * Polynomial.eval root w +
        (24 : F) * Polynomial.eval root U1 -
        (243 : F) * lambda * (Polynomial.eval root w) ^ 2 := by
  simp [hroot]

theorem eval_ninthFace_U_cofactor610 (h w A1 S1 P31 U1 B61 p2 : F[X])
    (lambda : F) (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((240 : F[X]) * A1 ^ 2 * h - (64 : F[X]) * A1 * S1 * h -
          (432 : F[X]) * A1 * h * Polynomial.C lambda * w -
          (160 : F[X]) * A1 * w ^ 2 + (16 : F[X]) * B61 +
          (24 : F[X]) * P31 * h * Polynomial.C lambda +
          (40 : F[X]) * P31 * w + (128 : F[X]) * S1 * w ^ 2 -
          (56 : F[X]) * U1 * w - (2160 : F[X]) * h * p2 +
          (240 : F[X]) * Polynomial.C lambda * w ^ 3) =
      -(160 : F) * Polynomial.eval root A1 *
          (Polynomial.eval root w) ^ 2 +
        (16 : F) * Polynomial.eval root B61 +
        (40 : F) * Polynomial.eval root P31 * Polynomial.eval root w +
        (128 : F) * Polynomial.eval root S1 *
          (Polynomial.eval root w) ^ 2 -
        (56 : F) * Polynomial.eval root U1 * Polynomial.eval root w +
        (240 : F) * lambda * (Polynomial.eval root w) ^ 3 := by
  simp [hroot]

theorem eval_ninthFace_V_cofactor610 (h w A1 S1 P31 U1 B61 Q51 p2 p1 :
    F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (-(4752 : F[X]) * A1 ^ 2 * h ^ 2 * Polynomial.C lambda -
          (21120 : F[X]) * A1 ^ 2 * h * w +
          (3520 : F[X]) * A1 * P31 * h +
          (8448 : F[X]) * A1 * S1 * h * w -
          (1344 : F[X]) * A1 * U1 * h +
          (30888 : F[X]) * A1 * h * Polynomial.C lambda * w ^ 2 +
          (2400 : F[X]) * A1 * w ^ 3 - (1152 : F[X]) * B61 * w -
          (512 : F[X]) * P31 * S1 * h -
          (3168 : F[X]) * P31 * h * Polynomial.C lambda * w -
          (720 : F[X]) * P31 * w ^ 2 + (384 : F[X]) * Q51 -
          (4032 : F[X]) * S1 * w ^ 3 + (2352 : F[X]) * U1 * w ^ 2 -
          (155520 : F[X]) * h ^ 3 * p1 +
          (46656 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 +
          (51840 : F[X]) * h * p2 * w -
          (6237 : F[X]) * Polynomial.C lambda * w ^ 4) =
      (2400 : F) * Polynomial.eval root A1 *
          (Polynomial.eval root w) ^ 3 -
        (1152 : F) * Polynomial.eval root B61 *
          Polynomial.eval root w -
        (720 : F) * Polynomial.eval root P31 *
          (Polynomial.eval root w) ^ 2 +
        (384 : F) * Polynomial.eval root Q51 -
        (4032 : F) * Polynomial.eval root S1 *
          (Polynomial.eval root w) ^ 3 +
        (2352 : F) * Polynomial.eval root U1 *
          (Polynomial.eval root w) ^ 2 -
        (6237 : F) * lambda * (Polynomial.eval root w) ^ 4 := by
  simp [hroot]

theorem eval_ninthFace_W_cofactor610 (h w A1 S1 P31 U1 B61 Q51 p2 p1 p0
    q4 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (-(19200 : F[X]) * A1 ^ 3 * h ^ 2 +
          (5760 : F[X]) * A1 ^ 2 * S1 * h ^ 2 +
          (51840 : F[X]) * A1 ^ 2 * h ^ 2 * Polynomial.C lambda * w +
          (57600 : F[X]) * A1 ^ 2 * h * w ^ 2 -
          (1728 : F[X]) * A1 * B61 * h -
          (4320 : F[X]) * A1 * P31 * h ^ 2 * Polynomial.C lambda -
          (16800 : F[X]) * A1 * P31 * h * w -
          (34560 : F[X]) * A1 * S1 * h * w ^ 2 +
          (10080 : F[X]) * A1 * U1 * h * w +
          (388800 : F[X]) * A1 * h ^ 2 * p2 -
          (90720 : F[X]) * A1 * h * Polynomial.C lambda * w ^ 3 -
          (1440 : F[X]) * A1 * w ^ 4 + (2592 : F[X]) * B61 * w ^ 2 +
          (800 : F[X]) * P31 ^ 2 * h +
          (3840 : F[X]) * P31 * S1 * h * w -
          (672 : F[X]) * P31 * U1 * h +
          (12960 : F[X]) * P31 * h * Polynomial.C lambda * w ^ 2 +
          (480 : F[X]) * P31 * w ^ 3 - (1440 : F[X]) * Q51 * w -
          (62208 : F[X]) * S1 * h ^ 2 * p2 +
          (5760 : F[X]) * S1 * w ^ 4 - (4032 : F[X]) * U1 * w ^ 3 -
          (699840 : F[X]) * h ^ 5 * p0 +
          (209952 : F[X]) * h ^ 4 * Polynomial.C lambda * p1 +
          (116640 : F[X]) * h ^ 3 * p1 * w -
          (349920 : F[X]) * h ^ 2 * Polynomial.C lambda * p2 * w -
          (38880 : F[X]) * h * p2 * w ^ 2 +
          (419904 : F[X]) * h * q4 +
          (7776 : F[X]) * Polynomial.C lambda * w ^ 5) =
      -(1440 : F) * Polynomial.eval root A1 *
          (Polynomial.eval root w) ^ 4 +
        (2592 : F) * Polynomial.eval root B61 *
          (Polynomial.eval root w) ^ 2 +
        (480 : F) * Polynomial.eval root P31 *
          (Polynomial.eval root w) ^ 3 -
        (1440 : F) * Polynomial.eval root Q51 *
          Polynomial.eval root w +
        (5760 : F) * Polynomial.eval root S1 *
          (Polynomial.eval root w) ^ 4 -
        (4032 : F) * Polynomial.eval root U1 *
          (Polynomial.eval root w) ^ 3 +
        (7776 : F) * lambda * (Polynomial.eval root w) ^ 5 := by
  simp [hroot]

end NinthFaceScalars610

/-! ## Source-facing ninth-face packet -/

section NonzeroNinthFace610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000 in
/-- Finite local ninth-face packet: the eighth-face power jet together
with the next-order compatibility `λ w⁵ = 0`. -/
theorem nonzeroFace610_linearRoot_ninthPowerJet
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
    ∃ (w a4s s u b6s A1 S1 P31 U1 B61 Q51 : k[X]),
      p.coeff 5 = h0 ^ 4 * w ∧ p.coeff 4 = h0 ^ 2 * a4s ∧
        q.coeff 8 = h0 ^ 6 * s ∧ q.coeff 7 = h0 ^ 4 * u ∧
        q.coeff 6 = h0 ^ 2 * b6s ∧
        (3 : k[X]) * a4s - w ^ 2 = h0 * A1 ∧
        (9 : k[X]) * s - (10 : k[X]) * w ^ 2 = h0 * S1 ∧
        (27 : k[X]) * p.coeff 3 - w ^ 3 = h0 * P31 ∧
        (27 : k[X]) * u - (10 : k[X]) * w ^ 3 = h0 * U1 ∧
        (81 : k[X]) * b6s - (5 : k[X]) * w ^ 4 = h0 * B61 ∧
        (243 : k[X]) * q.coeff 5 - w ^ 5 = h0 * Q51 ∧
        lambda * (w.eval a) ^ 5 = 0 ∧
        (2 : k) * S1.eval a - (10 : k) * A1.eval a +
          (9 : k) * lambda * w.eval a = 0 ∧
        (240 : k) * A1.eval a * w.eval a - (40 : k) * P31.eval a -
          (96 : k) * S1.eval a * w.eval a + (24 : k) * U1.eval a -
          (243 : k) * lambda * (w.eval a) ^ 2 = 0 ∧
        -(160 : k) * A1.eval a * (w.eval a) ^ 2 +
          (16 : k) * B61.eval a + (40 : k) * P31.eval a * w.eval a +
          (128 : k) * S1.eval a * (w.eval a) ^ 2 -
          (56 : k) * U1.eval a * w.eval a +
          (240 : k) * lambda * (w.eval a) ^ 3 = 0 ∧
        (2400 : k) * A1.eval a * (w.eval a) ^ 3 -
          (1152 : k) * B61.eval a * w.eval a -
          (720 : k) * P31.eval a * (w.eval a) ^ 2 +
          (384 : k) * Q51.eval a -
          (4032 : k) * S1.eval a * (w.eval a) ^ 3 +
          (2352 : k) * U1.eval a * (w.eval a) ^ 2 -
          (6237 : k) * lambda * (w.eval a) ^ 4 = 0 ∧
        -(1440 : k) * A1.eval a * (w.eval a) ^ 4 +
          (2592 : k) * B61.eval a * (w.eval a) ^ 2 +
          (480 : k) * P31.eval a * (w.eval a) ^ 3 -
          (1440 : k) * Q51.eval a * w.eval a +
          (5760 : k) * S1.eval a * (w.eval a) ^ 4 -
          (4032 : k) * U1.eval a * (w.eval a) ^ 3 +
          (7776 : k) * lambda * (w.eval a) ^ 5 = 0 := by
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
  obtain ⟨w, a4s, s, u, b6s, hw, ha4s, hs, hu, hb6s, ha4, hs', hp3, hu',
    hb6, hq5⟩ :=
    nonzeroFace610_linearRoot_eighthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot
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
  have hA0 : ((3 : k[X]) * a4s - w ^ 2).eval a = 0 := by
    simp [map_sub, map_mul, map_pow]
    linear_combination ha4
  have hS0 : ((9 : k[X]) * s - (10 : k[X]) * w ^ 2).eval a = 0 := by
    simp [map_sub, map_mul, map_pow]
    linear_combination hs'
  have hP0 : ((27 : k[X]) * p.coeff 3 - w ^ 3).eval a = 0 := by
    simp [map_sub, map_mul, map_pow]
    linear_combination hp3
  have hU0' : ((27 : k[X]) * u - (10 : k[X]) * w ^ 3).eval a = 0 := by
    simp [map_sub, map_mul, map_pow]
    linear_combination hu'
  have hB0 : ((81 : k[X]) * b6s - (5 : k[X]) * w ^ 4).eval a = 0 := by
    simp [map_sub, map_mul, map_pow]
    linear_combination hb6
  have hQ0 : ((243 : k[X]) * q.coeff 5 - w ^ 5).eval a = 0 := by
    simp [map_sub, map_mul, map_pow]
    linear_combination hq5
  obtain ⟨A1, hA1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      ((3 : k[X]) * a4s - w ^ 2) a hh0degree hroot hA0
  obtain ⟨S1, hS1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      ((9 : k[X]) * s - (10 : k[X]) * w ^ 2) a hh0degree hroot hS0
  obtain ⟨P31, hP31⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      ((27 : k[X]) * p.coeff 3 - w ^ 3) a hh0degree hroot hP0
  obtain ⟨U1, hU1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      ((27 : k[X]) * u - (10 : k[X]) * w ^ 3) a hh0degree hroot hU0'
  obtain ⟨B61, hB61⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      ((81 : k[X]) * b6s - (5 : k[X]) * w ^ 4) a hh0degree hroot hB0
  obtain ⟨Q51, hQ51⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      ((243 : k[X]) * q.coeff 5 - w ^ 5) a hh0degree hroot hQ0
  have hMmul :=
    ninthFace_M_mul_h610 h0 w a4s s A1 S1 lambda hA1 hS1
  have hTmul :=
    ninthFace_T_mul_h610 h0 w a4s s u (p.coeff 3) A1 S1 P31 U1 lambda
      hA1 hS1 hP31 hU1
  have hUmul :=
    ninthFace_U_mul_h610 h0 w a4s s u (p.coeff 3) b6s (p.coeff 2) A1 S1
      P31 U1 B61 lambda hA1 hS1 hP31 hU1 hB61
  have hVmul :=
    ninthFace_V_mul_h610 h0 w a4s s u (p.coeff 3) b6s (q.coeff 5)
      (p.coeff 2) (p.coeff 1) A1 S1 P31 U1 B61 Q51 lambda hA1 hS1 hP31
      hU1 hB61 hQ51
  have hWmul :=
    ninthFace_W_mul_h610 h0 w a4s s u (p.coeff 3) b6s (q.coeff 5)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) A1 S1 P31 U1 B61
      Q51 lambda hA1 hS1 hP31 hU1 hB61 hQ51
  have hMcof :
      (2 : k[X]) * S1 - (10 : k[X]) * A1 +
          (9 : k[X]) * Polynomial.C lambda * w =
        Polynomial.C alpha * h0 := by
    apply mul_left_cancel₀ hh0
    rw [← hMmul, hM0]
    ring
  have hTcof :
      (108 : k[X]) * A1 * h0 * Polynomial.C lambda +
          (240 : k[X]) * A1 * w - (40 : k[X]) * P31 -
          (96 : k[X]) * S1 * w + (24 : k[X]) * U1 -
          (243 : k[X]) * Polynomial.C lambda * w ^ 2 =
        Polynomial.C gamma * h0 ^ 2 := by
    apply mul_left_cancel₀ hh0
    rw [← hTmul, hT0]
    ring
  have hUcof :
      (240 : k[X]) * A1 ^ 2 * h0 - (64 : k[X]) * A1 * S1 * h0 -
          (432 : k[X]) * A1 * h0 * Polynomial.C lambda * w -
          (160 : k[X]) * A1 * w ^ 2 + (16 : k[X]) * B61 +
          (24 : k[X]) * P31 * h0 * Polynomial.C lambda +
          (40 : k[X]) * P31 * w + (128 : k[X]) * S1 * w ^ 2 -
          (56 : k[X]) * U1 * w - (2160 : k[X]) * h0 * p.coeff 2 +
          (240 : k[X]) * Polynomial.C lambda * w ^ 3 =
        (3 : k[X]) * Polynomial.C delta * h0 ^ 3 := by
    apply mul_left_cancel₀ hh0
    have h3U :
        (3 : k[X]) *
            ((432 : k[X]) * b6s + (720 : k[X]) * a4s ^ 2 -
                (576 : k[X]) * a4s * s - (504 : k[X]) * w * u +
              (360 : k[X]) * w * p.coeff 3 - (360 : k[X]) * w ^ 4 +
                (576 : k[X]) * s * w ^ 2 +
              ((216 : k[X]) * Polynomial.C lambda * w ^ 3 -
                  (432 : k[X]) * Polynomial.C lambda * w * a4s +
                  (216 : k[X]) * Polynomial.C lambda * p.coeff 3) *
                h0 - (720 : k[X]) * p.coeff 2 * h0 ^ 2) =
          (3 : k[X]) * Polynomial.C delta * h0 ^ 4 := by
      rw [hU0]
      ring
    rw [← hUmul, h3U]
    ring
  have hVcof :
      -(4752 : k[X]) * A1 ^ 2 * h0 ^ 2 * Polynomial.C lambda -
          (21120 : k[X]) * A1 ^ 2 * h0 * w +
          (3520 : k[X]) * A1 * P31 * h0 +
          (8448 : k[X]) * A1 * S1 * h0 * w -
          (1344 : k[X]) * A1 * U1 * h0 +
          (30888 : k[X]) * A1 * h0 * Polynomial.C lambda * w ^ 2 +
          (2400 : k[X]) * A1 * w ^ 3 - (1152 : k[X]) * B61 * w -
          (512 : k[X]) * P31 * S1 * h0 -
          (3168 : k[X]) * P31 * h0 * Polynomial.C lambda * w -
          (720 : k[X]) * P31 * w ^ 2 + (384 : k[X]) * Q51 -
          (4032 : k[X]) * S1 * w ^ 3 + (2352 : k[X]) * U1 * w ^ 2 -
          (155520 : k[X]) * h0 ^ 3 * p.coeff 1 +
          (46656 : k[X]) * h0 ^ 2 * Polynomial.C lambda * p.coeff 2 +
          (51840 : k[X]) * h0 * p.coeff 2 * w -
          (6237 : k[X]) * Polynomial.C lambda * w ^ 4 =
        Polynomial.C eps * h0 ^ 4 := by
    apply mul_left_cancel₀ hh0
    rw [← hVmul, hV0]
    ring
  have hWcof :
      -(19200 : k[X]) * A1 ^ 3 * h0 ^ 2 +
          (5760 : k[X]) * A1 ^ 2 * S1 * h0 ^ 2 +
          (51840 : k[X]) * A1 ^ 2 * h0 ^ 2 * Polynomial.C lambda * w +
          (57600 : k[X]) * A1 ^ 2 * h0 * w ^ 2 -
          (1728 : k[X]) * A1 * B61 * h0 -
          (4320 : k[X]) * A1 * P31 * h0 ^ 2 * Polynomial.C lambda -
          (16800 : k[X]) * A1 * P31 * h0 * w -
          (34560 : k[X]) * A1 * S1 * h0 * w ^ 2 +
          (10080 : k[X]) * A1 * U1 * h0 * w +
          (388800 : k[X]) * A1 * h0 ^ 2 * p.coeff 2 -
          (90720 : k[X]) * A1 * h0 * Polynomial.C lambda * w ^ 3 -
          (1440 : k[X]) * A1 * w ^ 4 + (2592 : k[X]) * B61 * w ^ 2 +
          (800 : k[X]) * P31 ^ 2 * h0 +
          (3840 : k[X]) * P31 * S1 * h0 * w -
          (672 : k[X]) * P31 * U1 * h0 +
          (12960 : k[X]) * P31 * h0 * Polynomial.C lambda * w ^ 2 +
          (480 : k[X]) * P31 * w ^ 3 - (1440 : k[X]) * Q51 * w -
          (62208 : k[X]) * S1 * h0 ^ 2 * p.coeff 2 +
          (5760 : k[X]) * S1 * w ^ 4 - (4032 : k[X]) * U1 * w ^ 3 -
          (699840 : k[X]) * h0 ^ 5 * p.coeff 0 +
          (209952 : k[X]) * h0 ^ 4 * Polynomial.C lambda * p.coeff 1 +
          (116640 : k[X]) * h0 ^ 3 * p.coeff 1 * w -
          (349920 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
            p.coeff 2 * w -
          (38880 : k[X]) * h0 * p.coeff 2 * w ^ 2 +
          (419904 : k[X]) * h0 * q.coeff 4 +
          (7776 : k[X]) * Polynomial.C lambda * w ^ 5 =
        Polynomial.C zeta * h0 ^ 5 := by
    apply mul_left_cancel₀ hh0
    rw [← hWmul, hW0]
    ring
  have hMeval :
      (2 : k) * S1.eval a - (10 : k) * A1.eval a +
        (9 : k) * lambda * w.eval a = 0 := by
    have hleft :=
      eval_ninthFace_M_cofactor610 h0 w A1 S1 lambda a hroot
    have hzero :
        Polynomial.eval a
            ((2 : k[X]) * S1 - (10 : k[X]) * A1 +
              (9 : k[X]) * Polynomial.C lambda * w) = 0 := by
      rw [hMcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hTeval :
      (240 : k) * A1.eval a * w.eval a - (40 : k) * P31.eval a -
        (96 : k) * S1.eval a * w.eval a + (24 : k) * U1.eval a -
        (243 : k) * lambda * (w.eval a) ^ 2 = 0 := by
    have hleft :=
      eval_ninthFace_T_cofactor610 h0 w A1 S1 P31 U1 lambda a hroot
    have hzero :
        Polynomial.eval a
            ((108 : k[X]) * A1 * h0 * Polynomial.C lambda +
              (240 : k[X]) * A1 * w - (40 : k[X]) * P31 -
              (96 : k[X]) * S1 * w + (24 : k[X]) * U1 -
              (243 : k[X]) * Polynomial.C lambda * w ^ 2) = 0 := by
      rw [hTcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hUeval :
      -(160 : k) * A1.eval a * (w.eval a) ^ 2 + (16 : k) * B61.eval a +
        (40 : k) * P31.eval a * w.eval a +
        (128 : k) * S1.eval a * (w.eval a) ^ 2 -
        (56 : k) * U1.eval a * w.eval a +
        (240 : k) * lambda * (w.eval a) ^ 3 = 0 := by
    have hleft :=
      eval_ninthFace_U_cofactor610 h0 w A1 S1 P31 U1 B61 (p.coeff 2)
        lambda a hroot
    have hzero :
        Polynomial.eval a
            ((240 : k[X]) * A1 ^ 2 * h0 - (64 : k[X]) * A1 * S1 * h0 -
              (432 : k[X]) * A1 * h0 * Polynomial.C lambda * w -
              (160 : k[X]) * A1 * w ^ 2 + (16 : k[X]) * B61 +
              (24 : k[X]) * P31 * h0 * Polynomial.C lambda +
              (40 : k[X]) * P31 * w + (128 : k[X]) * S1 * w ^ 2 -
              (56 : k[X]) * U1 * w - (2160 : k[X]) * h0 * p.coeff 2 +
              (240 : k[X]) * Polynomial.C lambda * w ^ 3) = 0 := by
      rw [hUcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hVeval :
      (2400 : k) * A1.eval a * (w.eval a) ^ 3 -
        (1152 : k) * B61.eval a * w.eval a -
        (720 : k) * P31.eval a * (w.eval a) ^ 2 +
        (384 : k) * Q51.eval a -
        (4032 : k) * S1.eval a * (w.eval a) ^ 3 +
        (2352 : k) * U1.eval a * (w.eval a) ^ 2 -
        (6237 : k) * lambda * (w.eval a) ^ 4 = 0 := by
    have hleft :=
      eval_ninthFace_V_cofactor610 h0 w A1 S1 P31 U1 B61 Q51
        (p.coeff 2) (p.coeff 1) lambda a hroot
    have hzero :
        Polynomial.eval a
            (-(4752 : k[X]) * A1 ^ 2 * h0 ^ 2 * Polynomial.C lambda -
              (21120 : k[X]) * A1 ^ 2 * h0 * w +
              (3520 : k[X]) * A1 * P31 * h0 +
              (8448 : k[X]) * A1 * S1 * h0 * w -
              (1344 : k[X]) * A1 * U1 * h0 +
              (30888 : k[X]) * A1 * h0 * Polynomial.C lambda * w ^ 2 +
              (2400 : k[X]) * A1 * w ^ 3 - (1152 : k[X]) * B61 * w -
              (512 : k[X]) * P31 * S1 * h0 -
              (3168 : k[X]) * P31 * h0 * Polynomial.C lambda * w -
              (720 : k[X]) * P31 * w ^ 2 + (384 : k[X]) * Q51 -
              (4032 : k[X]) * S1 * w ^ 3 +
              (2352 : k[X]) * U1 * w ^ 2 -
              (155520 : k[X]) * h0 ^ 3 * p.coeff 1 +
              (46656 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                p.coeff 2 +
              (51840 : k[X]) * h0 * p.coeff 2 * w -
              (6237 : k[X]) * Polynomial.C lambda * w ^ 4) = 0 := by
      rw [hVcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hWeval :
      -(1440 : k) * A1.eval a * (w.eval a) ^ 4 +
        (2592 : k) * B61.eval a * (w.eval a) ^ 2 +
        (480 : k) * P31.eval a * (w.eval a) ^ 3 -
        (1440 : k) * Q51.eval a * w.eval a +
        (5760 : k) * S1.eval a * (w.eval a) ^ 4 -
        (4032 : k) * U1.eval a * (w.eval a) ^ 3 +
        (7776 : k) * lambda * (w.eval a) ^ 5 = 0 := by
    have hleft :=
      eval_ninthFace_W_cofactor610 h0 w A1 S1 P31 U1 B61 Q51
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4) lambda a hroot
    have hzero :
        Polynomial.eval a
            (-(19200 : k[X]) * A1 ^ 3 * h0 ^ 2 +
              (5760 : k[X]) * A1 ^ 2 * S1 * h0 ^ 2 +
              (51840 : k[X]) * A1 ^ 2 * h0 ^ 2 * Polynomial.C lambda *
                w +
              (57600 : k[X]) * A1 ^ 2 * h0 * w ^ 2 -
              (1728 : k[X]) * A1 * B61 * h0 -
              (4320 : k[X]) * A1 * P31 * h0 ^ 2 * Polynomial.C lambda -
              (16800 : k[X]) * A1 * P31 * h0 * w -
              (34560 : k[X]) * A1 * S1 * h0 * w ^ 2 +
              (10080 : k[X]) * A1 * U1 * h0 * w +
              (388800 : k[X]) * A1 * h0 ^ 2 * p.coeff 2 -
              (90720 : k[X]) * A1 * h0 * Polynomial.C lambda * w ^ 3 -
              (1440 : k[X]) * A1 * w ^ 4 +
              (2592 : k[X]) * B61 * w ^ 2 +
              (800 : k[X]) * P31 ^ 2 * h0 +
              (3840 : k[X]) * P31 * S1 * h0 * w -
              (672 : k[X]) * P31 * U1 * h0 +
              (12960 : k[X]) * P31 * h0 * Polynomial.C lambda * w ^ 2 +
              (480 : k[X]) * P31 * w ^ 3 - (1440 : k[X]) * Q51 * w -
              (62208 : k[X]) * S1 * h0 ^ 2 * p.coeff 2 +
              (5760 : k[X]) * S1 * w ^ 4 -
              (4032 : k[X]) * U1 * w ^ 3 -
              (699840 : k[X]) * h0 ^ 5 * p.coeff 0 +
              (209952 : k[X]) * h0 ^ 4 * Polynomial.C lambda *
                p.coeff 1 +
              (116640 : k[X]) * h0 ^ 3 * p.coeff 1 * w -
              (349920 : k[X]) * h0 ^ 2 * Polynomial.C lambda *
                p.coeff 2 * w -
              (38880 : k[X]) * h0 * p.coeff 2 * w ^ 2 +
              (419904 : k[X]) * h0 * q.coeff 4 +
              (7776 : k[X]) * Polynomial.C lambda * w ^ 5) = 0 := by
      rw [hWcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hlamw :=
    ninthFace_lambda_w5_610 (w.eval a) (A1.eval a) (S1.eval a)
      (P31.eval a) (U1.eval a) (B61.eval a) (Q51.eval a) lambda
      hMeval hTeval hUeval hVeval hWeval
  exact ⟨w, a4s, s, u, b6s, A1, S1, P31, U1, B61, Q51, hw, ha4s, hs, hu,
    hb6s, hA1, hS1, hP31, hU1, hB61, hQ51, hlamw, hMeval, hTeval, hUeval,
    hVeval, hWeval⟩

set_option maxHeartbeats 8000000 in
/-- Source-facing ninth-face power jet of a normalized scale-two
`(6,10)` nonzero face: the eighth-face one-parameter jet collapses at
the root of `h`. -/
theorem normalized610ScaleTwo_nonzeroFace_ninthPowerJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K) (w a4s s u b6s A1 S1 P31 U1 B61 Q51 :
        K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 4 * w ∧ p.coeff 4 = h0 ^ 2 * a4s ∧
        q.coeff 8 = h0 ^ 6 * s ∧ q.coeff 7 = h0 ^ 4 * u ∧
        q.coeff 6 = h0 ^ 2 * b6s ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        (3 : K[X]) * a4s - w ^ 2 = h0 * A1 ∧
        (9 : K[X]) * s - (10 : K[X]) * w ^ 2 = h0 * S1 ∧
        (27 : K[X]) * p.coeff 3 - w ^ 3 = h0 * P31 ∧
        (27 : K[X]) * u - (10 : K[X]) * w ^ 3 = h0 * U1 ∧
        (81 : K[X]) * b6s - (5 : K[X]) * w ^ 4 = h0 * B61 ∧
        (243 : K[X]) * q.coeff 5 - w ^ 5 = h0 * Q51 ∧
        w.eval a = 0 ∧ a4s.eval a = 0 ∧ s.eval a = 0 ∧
        (p.coeff 3).eval a = 0 ∧ u.eval a = 0 ∧ b6s.eval a = 0 ∧
        (q.coeff 5).eval a = 0 ∧
        S1.eval a = (5 : K) * A1.eval a ∧
        (5 : K) * P31.eval a = (3 : K) * U1.eval a ∧
        B61.eval a = 0 ∧ Q51.eval a = 0 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, w, a4s, s, u, b6s, hh0, hlambda, hh0degree, hH,
    hroot, hw, ha4s, hs, hu, hb6s, hq9, ha4, hs', hp3, hu', hb6, hq5,
    hN'⟩ :=
    normalized610ScaleTwo_nonzeroFace_eighthPowerJet hsource hnonzero
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
  obtain ⟨w', a4s', s', u', b6s', A1, S1, P31, U1, B61, Q51, hwN, ha4sN,
    hsN, huN, hb6sN, hA1, hS1, hP31, hU1, hB61, hQ51, hlamw, hMeval,
    hTeval, hUeval, hVeval, hWeval⟩ :=
    nonzeroFace610_linearRoot_ninthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  have hw_eq : w' = w := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
    calc
      h0 ^ 4 * w' = p.coeff 5 := by rw [hwN]
      _ = h0 ^ 4 * w := hw
  have ha4s_eq : a4s' = a4s := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 * a4s' = p.coeff 4 := by rw [ha4sN]
      _ = h0 ^ 2 * a4s := ha4s
  have hs_eq : s' = s := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
    calc
      h0 ^ 6 * s' = q.coeff 8 := by rw [hsN]
      _ = h0 ^ 6 * s := hs
  have hu_eq : u' = u := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
    calc
      h0 ^ 4 * u' = q.coeff 7 := by rw [huN]
      _ = h0 ^ 4 * u := hu
  have hb6s_eq : b6s' = b6s := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 * b6s' = q.coeff 6 := by rw [hb6sN]
      _ = h0 ^ 2 * b6s := hb6s
  have hwz : w.eval a = 0 := by
    have : (w'.eval a) ^ 5 = 0 :=
      (mul_eq_zero.mp hlamw).resolve_left hlambda
    have : w'.eval a = 0 := eq_zero_of_pow_eq_zero this
    simpa [hw_eq] using this
  have ha4z : a4s.eval a = 0 := by
    have : (3 : K) * a4s.eval a = (w.eval a) ^ 2 := ha4
    simpa [hwz] using this
  have hsz : s.eval a = 0 := by
    have : (9 : K) * s.eval a = (10 : K) * (w.eval a) ^ 2 := hs'
    simpa [hwz] using this
  have hp3z : (p.coeff 3).eval a = 0 := by
    have : (27 : K) * (p.coeff 3).eval a = (w.eval a) ^ 3 := hp3
    simpa [hwz] using this
  have huz : u.eval a = 0 := by
    have : (27 : K) * u.eval a = (10 : K) * (w.eval a) ^ 3 := hu'
    simpa [hwz] using this
  have hb6z : b6s.eval a = 0 := by
    have : (81 : K) * b6s.eval a = (5 : K) * (w.eval a) ^ 4 := hb6
    simpa [hwz] using this
  have hq5z : (q.coeff 5).eval a = 0 := by
    have : (243 : K) * (q.coeff 5).eval a = (w.eval a) ^ 5 := hq5
    simpa [hwz] using this
  have hw'z : w'.eval a = 0 := by simpa [hw_eq] using hwz
  have hM0 : (2 : K) * S1.eval a - (10 : K) * A1.eval a = 0 := by
    simpa [hw'z] using hMeval
  have hT0 : -(40 : K) * P31.eval a + (24 : K) * U1.eval a = 0 := by
    simpa [hw'z] using hTeval
  have hU0 : (16 : K) * B61.eval a = 0 := by
    simpa [hw'z] using hUeval
  have hV0 : (384 : K) * Q51.eval a = 0 := by
    simpa [hw'z] using hVeval
  obtain ⟨hSrel, hPrel, hBrel, hQrel⟩ :=
    ninthFace_zeroW_nextOrder610 (A1.eval a) (S1.eval a) (P31.eval a)
      (U1.eval a) (B61.eval a) (Q51.eval a) hM0 hT0 hU0 hV0
  have hp5_5 : h0 ^ 5 ∣ p.coeff 5 := by
    obtain ⟨w1, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w a hh0degree hroot hwz
    refine ⟨w1, ?_⟩
    rw [hw, hw1]
    ring
  have hp4_3 : h0 ^ 3 ∣ p.coeff 4 := by
    obtain ⟨a41, ha41⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 a4s a hh0degree hroot
        ha4z
    refine ⟨a41, ?_⟩
    rw [ha4s, ha41]
    ring
  have hp3_1 : h0 ∣ p.coeff 3 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 3) a hh0degree
      hroot hp3z
  have hq8_7 : h0 ^ 7 ∣ q.coeff 8 := by
    obtain ⟨s1, hs1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hsz
    refine ⟨s1, ?_⟩
    rw [hs, hs1]
    ring
  have hq7_5 : h0 ^ 5 ∣ q.coeff 7 := by
    obtain ⟨u1, hu1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 u a hh0degree hroot huz
    refine ⟨u1, ?_⟩
    rw [hu, hu1]
    ring
  have hq6_4 : h0 ^ 4 ∣ q.coeff 6 := by
    obtain ⟨b61', hb61'⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b6s a hh0degree hroot
        hb6z
    obtain ⟨w1, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w a hh0degree hroot hwz
    have hB : (81 : K[X]) * b6s - (5 : K[X]) * w ^ 4 = h0 * B61 := by
      simpa [hb6s_eq, hw_eq] using hB61
    have hcancel :
        (81 : K[X]) * b61' - (5 : K[X]) * h0 ^ 3 * w1 ^ 4 = B61 := by
      apply mul_left_cancel₀ hh0
      calc
        h0 * ((81 : K[X]) * b61' - (5 : K[X]) * h0 ^ 3 * w1 ^ 4) =
            (81 : K[X]) * (h0 * b61') - (5 : K[X]) * (h0 * w1) ^ 4 := by
          ring
        _ = (81 : K[X]) * b6s - (5 : K[X]) * w ^ 4 := by
          rw [← hb61', ← hw1]
        _ = h0 * B61 := hB
    have hb61z' : b61'.eval a = 0 := by
      have heval := congrArg (fun r : K[X] => r.eval a) hcancel
      have h81 : (81 : K) ≠ 0 := by norm_num
      have : (81 : K) * b61'.eval a = 0 := by
        simpa [hroot, hBrel, map_sub, map_mul, map_pow] using heval
      exact (mul_eq_zero.mp this).resolve_left h81
    obtain ⟨b62, hb62⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b61' a hh0degree hroot
        hb61z'
    refine ⟨b62, ?_⟩
    rw [hb6s, hb61', hb62]
    ring
  have hq5_2 : h0 ^ 2 ∣ q.coeff 5 := by
    obtain ⟨q51', hq51'⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 5) a
        hh0degree hroot hq5z
    obtain ⟨w1, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w a hh0degree hroot hwz
    have hQ : (243 : K[X]) * q.coeff 5 - w ^ 5 = h0 * Q51 := by
      simpa [hw_eq] using hQ51
    have hcancel :
        (243 : K[X]) * q51' - h0 ^ 4 * w1 ^ 5 = Q51 := by
      apply mul_left_cancel₀ hh0
      calc
        h0 * ((243 : K[X]) * q51' - h0 ^ 4 * w1 ^ 5) =
            (243 : K[X]) * (h0 * q51') - (h0 * w1) ^ 5 := by
          ring
        _ = (243 : K[X]) * q.coeff 5 - w ^ 5 := by
          rw [← hq51', ← hw1]
        _ = h0 * Q51 := hQ
    have hq51z : q51'.eval a = 0 := by
      have heval := congrArg (fun r : K[X] => r.eval a) hcancel
      have h243 : (243 : K) ≠ 0 := by norm_num
      have : (243 : K) * q51'.eval a = 0 := by
        simpa [hroot, hQrel, map_sub, map_mul, map_pow] using heval
      exact (mul_eq_zero.mp this).resolve_left h243
    obtain ⟨q52, hq52⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 q51' a hh0degree hroot
        hq51z
    refine ⟨q52, ?_⟩
    rw [hq51', hq52]
    ring
  exact ⟨h0, lambda, a, w, a4s, s, u, b6s, A1, S1, P31, U1, B61, Q51,
    hh0, hlambda, hh0degree, hH, hroot, hw, ha4s, hs, hu, hb6s, hq9,
    (by simpa [ha4s_eq, hw_eq] using hA1),
    (by simpa [hs_eq, hw_eq] using hS1),
    (by simpa [hw_eq] using hP31),
    (by simpa [hu_eq, hw_eq] using hU1),
    (by simpa [hb6s_eq, hw_eq] using hB61),
    (by simpa [hw_eq] using hQ51),
    hwz, ha4z, hsz, hp3z, huz, hb6z, hq5z, hSrel, hPrel, hBrel, hQrel,
    hp5_5, hp4_3, hp3_1, hq8_7, hq7_5, hq6_4, hq5_2, hN'⟩

end NonzeroNinthFace610

#print axioms ninthCoefficientJacobianRow_610
#print axioms ninthFace_lambda_w5_610
#print axioms ninthFace_zeroW_nextOrder610
#print axioms ninthFace_M_mul_h610
#print axioms ninthFace_T_mul_h610
#print axioms ninthFace_U_mul_h610
#print axioms ninthFace_V_mul_h610
#print axioms ninthFace_W_mul_h610
#print axioms nonzeroFace610_linearRoot_ninthPowerJet
#print axioms normalized610ScaleTwo_nonzeroFace_ninthPowerJet

end Max11DegreeRoutes
