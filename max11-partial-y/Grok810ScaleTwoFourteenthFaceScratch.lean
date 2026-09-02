import Grok810ScaleTwoThirteenthFaceScratch

/-! # Scale-two fourteenth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the thirteenth-face packet supplies the degree-`4`
Jacobian row (without clearing the corresponding first integral) and
the live split of the twelfth-face jet.  On the left the seventh-load
alternative `F₁ ∨ F₂` survives, together with the unsplit `F₁` product
`(3 t₀² - 8 v₁) (1024 b₆₂ + 25 t₀⁴ - 320 v₁²) = 0`.  On the right, the
`u₁ = 0` sibling carries `h² ∣ (4 s₁ - 5 v₁)` and
`h² ∣ (40 a₄ - 32 b₆₂ + 5 v₁²)` together with
`v₁³ (3 λ v₁ + 160 t₁ v₁ - 320 u₂) = 0`, while the complementary
factor carries `8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`, `2 u₁² + v₁³ = 0`,
`8 ω(a) = v₁(a) (10 t₁(a) - 9 λ)`, and `h ∣ (16 b₅ - 5 u₁ v₁)`.

The next unused Keller coefficient is the degree-`3` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`4 T G' + 3 U F' + 2 V E' + W D'
- C T' - 2 B U' - 3 A V' - 4 G W' = 0`.
The degree-`5` first integral remains uncleared: clearing it against
the remaining decic coordinate produces a defect larger than the
remaining exact jet.  This file isolates the degree-`3` Jacobian
identity and the strongest exact source-facing refinement of every
live thirteenth-face branch.

Both left factors survive.  On `F₁` the seventh load is a multiple of
the unsplit sixth product,
`Xred + 384 t₀ (3 t₀² - 8 v₁) (1024 b₆₂ + 25 t₀⁴ - 320 v₁²) = 0`.
The next-order sixth left combination
`-77 t₀⁵ + 640 t₀³ v₁ + 960 t₀² u₁ - 1280 t₀ v₁² - 5120 u₁ v₁`
is recorded as a scalar identity.  On the `u₁ = 0` sibling the sixth
load upgrades to `h² ∣ (16 b₆₂ v₁ - 5 v₁³)`.  On the complementary
factor the sixth leftover is the unsplit product
`u₁ v₁ (8 t₁ - 3 λ) = 0`, recorded as a scalar identity.  No individual vanishing of
`v₁, u₁, a₄, t₀, t₁, p₃, q₄` is claimed, and the aligned face `N = 0`
remains open.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fourteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the thirteenth face
start at degree `3`. -/
theorem fourteenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
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
      ({(0, 3), (1, 2), (2, 1),
        (3, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Scalar algebra of the thirteenth-face branches -/

section FourteenthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Next-order sixth-load combination on the left ninth-face jet. -/
def fourteenthFace_leftWnext810 (t0 v1 u1 : F) : F :=
  -(77 : F) * t0 ^ 5 + (640 : F) * t0 ^ 3 * v1 +
    (960 : F) * t0 ^ 2 * u1 - (1280 : F) * t0 * v1 ^ 2 -
    (5120 : F) * u1 * v1

/-- On the first left factor, the seventh-defect reduction is a multiple
of the unsplit sixth product. -/
theorem fourteenthFace_leftF1_X_product810 (t0 v1 u1 a4 b62 b5 : F)
    (hF1 : twelfthFace_leftF1_810 t0 v1 u1)
    (hG : tenthFace_Gred810 t0 v1 u1 a4 b62)
    (hV : tenthFace_Vred810 t0 v1 u1 a4 b62 b5) :
    (4177920 : F) * a4 * t0 ^ 3 - (11796480 : F) * a4 * t0 * v1 +
          (10485760 : F) * a4 * u1 + (7208960 : F) * b5 * t0 ^ 2 -
          (10485760 : F) * b5 * v1 - (6848512 : F) * b62 * t0 ^ 3 +
          (17301504 : F) * b62 * t0 * v1 -
          (12582912 : F) * b62 * u1 + (300960 : F) * t0 ^ 7 -
          (2675200 : F) * t0 ^ 5 * v1 +
          (4561920 : F) * t0 ^ 4 * u1 +
          (7096320 : F) * t0 ^ 3 * v1 ^ 2 -
          (15769600 : F) * t0 ^ 2 * u1 * v1 +
          (7208960 : F) * t0 * u1 ^ 2 - (5406720 : F) * t0 * v1 ^ 3 +
          (7208960 : F) * u1 * v1 ^ 2 +
        (384 : F) * t0 *
          ((3 : F) * t0 ^ 2 - (8 : F) * v1) *
            ((1024 : F) * b62 + (25 : F) * t0 ^ 4 -
              (320 : F) * v1 ^ 2) =
      0 := by
  unfold twelfthFace_leftF1_810 tenthFace_Gred810 at *
  have hGspec := twelfthFace_leftF1_G_810 t0 v1 u1 a4 b62 hF1 hG
  have hB5 :=
    thirteenthFace_leftF1_b5_810 t0 v1 u1 a4 b62 b5 hF1 hG hV
  have hid :
      (4177920 : F) * a4 * t0 ^ 3 - (11796480 : F) * a4 * t0 * v1 +
            (10485760 : F) * a4 * u1 + (7208960 : F) * b5 * t0 ^ 2 -
            (10485760 : F) * b5 * v1 - (6848512 : F) * b62 * t0 ^ 3 +
            (17301504 : F) * b62 * t0 * v1 -
            (12582912 : F) * b62 * u1 + (300960 : F) * t0 ^ 7 -
            (2675200 : F) * t0 ^ 5 * v1 +
            (4561920 : F) * t0 ^ 4 * u1 +
            (7096320 : F) * t0 ^ 3 * v1 ^ 2 -
            (15769600 : F) * t0 ^ 2 * u1 * v1 +
            (7208960 : F) * t0 * u1 ^ 2 -
            (5406720 : F) * t0 * v1 ^ 3 +
            (7208960 : F) * u1 * v1 ^ 2 +
          (384 : F) * t0 *
            ((3 : F) * t0 ^ 2 - (8 : F) * v1) *
              ((1024 : F) * b62 + (25 : F) * t0 ^ 4 -
                (320 : F) * v1 ^ 2) =
        ((1632 : F) * t0 ^ 3 - (4608 : F) * t0 * v1 +
              (4096 : F) * u1) *
            ((2560 : F) * a4 - (2048 : F) * b62 - (45 : F) * t0 ^ 4 +
              (80 : F) * t0 ^ 2 * v1 + (320 : F) * v1 ^ 2) +
          ((7040 : F) * t0 ^ 2 - (10240 : F) * v1) *
            ((1024 : F) * b5 - (256 : F) * b62 * t0 -
              (11 : F) * t0 ^ 5 + (40 : F) * t0 ^ 3 * v1) +
          (128 : F) * (t0 ^ 3 - (4 : F) * t0 * v1 + (8 : F) * u1) *
            (-(4096 : F) * b62 + (3755 : F) * t0 ^ 4 -
              (12200 : F) * t0 ^ 2 * v1 + (7040 : F) * t0 * u1 +
              (5760 : F) * v1 ^ 2) := by
    ring
  rw [hid]
  linear_combination ((1632 : F) * t0 ^ 3 - (4608 : F) * t0 * v1 +
        (4096 : F) * u1) *
      hGspec +
    ((7040 : F) * t0 ^ 2 - (10240 : F) * v1) * hB5 +
    (128 : F) * hF1 *
      (-(4096 : F) * b62 + (3755 : F) * t0 ^ 4 -
        (12200 : F) * t0 ^ 2 * v1 + (7040 : F) * t0 * u1 +
        (5760 : F) * v1 ^ 2)

/-- Combining the next-order second, third, fourth, and fifth defects
on the left reduces the sixth leftover to `Wnext`. -/
theorem fourteenthFace_left_c1W_reduces810
    (t0 v1 u1 a4 b62 m1 tau1 : F) (lambda : F)
    (hM : m1 + (9 : F) * lambda * t0 = 0)
    (hT : (4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
      (144 : F) * lambda * v1 =
      0)
    (hG : (2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
        (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
      (320 : F) * v1 ^ 2 =
      0)
    (hVnext : (16384 : F) * b62 + (175 : F) * t0 ^ 4 -
        (1120 : F) * t0 ^ 2 * v1 - (17920 : F) * t0 * u1 -
      (1280 : F) * v1 ^ 2 =
      0)
    (c1W : F)
    (hc1 : c1W =
      -(55296 : F) * a4 * lambda * t0 - (4096 : F) * a4 * m1 +
        (18144 : F) * lambda * t0 ^ 5 -
        (80640 : F) * lambda * t0 ^ 3 * v1 +
        (69120 : F) * lambda * t0 ^ 2 * u1 +
        (69120 : F) * lambda * t0 * v1 ^ 2 -
        (55296 : F) * lambda * u1 * v1 +
        (2240 : F) * m1 * t0 ^ 4 - (7680 : F) * m1 * t0 ^ 2 * v1 +
        (6144 : F) * m1 * t0 * u1 + (3072 : F) * m1 * v1 ^ 2 -
        (560 : F) * t0 ^ 3 * tau1 + (1344 : F) * t0 * tau1 * v1 -
        (896 : F) * tau1 * u1) :
    (2 : F) * c1W = (9 : F) * lambda *
      fourteenthFace_leftWnext810 t0 v1 u1 := by
  have hid :
      (20 : F) *
            (-(55296 : F) * a4 * lambda * t0 - (4096 : F) * a4 * m1 +
              (18144 : F) * lambda * t0 ^ 5 -
              (80640 : F) * lambda * t0 ^ 3 * v1 +
              (69120 : F) * lambda * t0 ^ 2 * u1 +
              (69120 : F) * lambda * t0 * v1 ^ 2 -
              (55296 : F) * lambda * u1 * v1 +
              (2240 : F) * m1 * t0 ^ 4 -
              (7680 : F) * m1 * t0 ^ 2 * v1 +
              (6144 : F) * m1 * t0 * u1 + (3072 : F) * m1 * v1 ^ 2 -
              (560 : F) * t0 ^ 3 * tau1 +
              (1344 : F) * t0 * tau1 * v1 - (896 : F) * tau1 * u1) -
          (90 : F) * lambda *
            fourteenthFace_leftWnext810 t0 v1 u1 =
        (20 : F) * (m1 + (9 : F) * lambda * t0) *
            (-(4096 : F) * a4 + (2240 : F) * t0 ^ 4 -
              (7680 : F) * t0 ^ 2 * v1 + (6144 : F) * t0 * u1 +
              (3072 : F) * v1 ^ 2) +
          (5 : F) *
            ((4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
              (144 : F) * lambda * v1) *
            (-(560 : F) * t0 ^ 3 + (1344 : F) * t0 * v1 -
              (896 : F) * u1) -
          (144 : F) * t0 * lambda *
            ((2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
              (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
              (320 : F) * v1 ^ 2) -
          (18 : F) * t0 * lambda *
            ((16384 : F) * b62 + (175 : F) * t0 ^ 4 -
              (1120 : F) * t0 ^ 2 * v1 - (17920 : F) * t0 * u1 -
              (1280 : F) * v1 ^ 2) := by
    unfold fourteenthFace_leftWnext810
    ring
  have hcomb :
      (20 : F) * c1W - (90 : F) * lambda *
          fourteenthFace_leftWnext810 t0 v1 u1 =
        0 := by
    rw [hc1, hid, hM, hT, hG, hVnext]
    ring
  have h10 : (10 : F) ≠ 0 := by norm_num
  have hscale :
      (10 : F) *
          ((2 : F) * c1W - (9 : F) * lambda *
            fourteenthFace_leftWnext810 t0 v1 u1) =
        (20 : F) * c1W - (90 : F) * lambda *
          fourteenthFace_leftWnext810 t0 v1 u1 := by
    ring
  have hzero :
      (10 : F) *
          ((2 : F) * c1W - (9 : F) * lambda *
            fourteenthFace_leftWnext810 t0 v1 u1) =
        0 := by
    rw [hscale, hcomb]
  have hsub :
      (2 : F) * c1W - (9 : F) * lambda *
          fourteenthFace_leftWnext810 t0 v1 u1 =
        0 :=
    (mul_eq_zero.mp hzero).resolve_left h10
  linear_combination hsub

/-- The complementary sixth leftover at the next order of
`4 w₁ - 5 u₁ = ω h` is the unsplit product `u₁ v₁ (8 t₁ - 3 λ)`. -/
theorem fourteenthFace_comp_W_nextOrder810 (v1 u1 t1 omega : F)
    (lambda : F)
    (hT : (8 : F) * omega - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 =
      0)
    (hW : (1024 : F) * u1 *
        (-(54 : F) * lambda * v1 - (28 : F) * omega +
          (95 : F) * t1 * v1) =
      0) :
    u1 * v1 * ((8 : F) * t1 - (3 : F) * lambda) = 0 := by
  have h7680 : (7680 : F) ≠ 0 := by norm_num
  have hid :
      (1024 : F) * u1 *
            (-(54 : F) * lambda * v1 - (28 : F) * omega +
              (95 : F) * t1 * v1) +
          (3584 : F) * u1 *
            ((8 : F) * omega - (10 : F) * t1 * v1 +
              (9 : F) * lambda * v1) =
        (7680 : F) *
          (u1 * v1 * ((8 : F) * t1 - (3 : F) * lambda)) := by
    ring
  have hcomb :
      (7680 : F) *
          (u1 * v1 * ((8 : F) * t1 - (3 : F) * lambda)) =
        0 := by
    rw [← hid]
    linear_combination hW + (3584 : F) * u1 * hT
  exact (mul_eq_zero.mp hcomb).resolve_left h7680

/-! ## Extra-`h` substitutions of the sixth-jet sixth parenthetical -/

/-- Cofactor of `h³` in the sixth-jet sixth defect after the extra
`u₁ = 0` vanishing `t₀ = h t₁`, `u₁ = h u₂`, `w₁ = h w₂`,
`b₅ = h b₅₁`. -/
def fourteenthFace_zeroU1_Wcof810
    (h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51 b4 : F[X]) (lambda : F) :
    F[X] :=
  -(131072 : F[X]) * a4 * s1 + (245760 : F[X]) * a4 * v1 -
      (98304 : F[X]) * b62 * v1 + (98304 : F[X]) * s1 * v1 ^ 2 -
    (102400 : F[X]) * v1 ^ 3 +
    (-(55296 : F[X]) * a4 * Polynomial.C lambda * t1 -
          (30720 : F[X]) * a4 * t1 ^ 2 + (131072 : F[X]) * b4 -
        (81920 : F[X]) * b51 * t1 + (73728 : F[X]) * b62 * t1 ^ 2 +
        (69120 : F[X]) * Polynomial.C lambda * t1 * v1 ^ 2 -
          (55296 : F[X]) * Polynomial.C lambda * u2 * v1 -
        (245760 : F[X]) * s1 * t1 ^ 2 * v1 +
          (196608 : F[X]) * s1 * t1 * u2 +
        (192000 : F[X]) * t1 ^ 2 * v1 ^ 2 -
          (337920 : F[X]) * t1 * u2 * v1 +
        (172032 : F[X]) * t1 * v1 * w2 + (122880 : F[X]) * u2 ^ 2 -
          (114688 : F[X]) * u2 * w2) *
      h ^ 2 +
    ((36864 : F[X]) * a3 * Polynomial.C lambda +
        (61440 : F[X]) * a3 * t1) *
      h ^ 3 +
    (-(163840 : F[X]) * a2 -
          (80640 : F[X]) * Polynomial.C lambda * t1 ^ 3 * v1 +
        (69120 : F[X]) * Polynomial.C lambda * t1 ^ 2 * u2 +
          (71680 : F[X]) * s1 * t1 ^ 4 +
        (12800 : F[X]) * t1 ^ 3 * u2 - (71680 : F[X]) * t1 ^ 3 * w2) *
      h ^ 4 +
    ((18144 : F[X]) * Polynomial.C lambda * t1 ^ 5 -
        (16800 : F[X]) * t1 ^ 6) *
      h ^ 6

set_option maxHeartbeats 8000000 in
theorem fourteenthFace_sixth_zeroU1_mul_h
    (h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51 b4 : F[X]) (lambda : F) :
    sixthJetParen810_sixth h (h * t1) (h * v1) (h * s1) (h ^ 2 * w2)
        (h ^ 2 * u2) a4 a3 a2 (h ^ 2 * b62) (h * b51) b4 lambda =
      h ^ 3 *
        fourteenthFace_zeroU1_Wcof810 h t1 v1 s1 w2 u2 a4 a3 a2 b62
          b51 b4 lambda := by
  simp only [sixthJetParen810_sixth, fourteenthFace_zeroU1_Wcof810]
  ring

/-- Cofactor of `h²` in `fourteenthFace_zeroU1_Wcof810` after the constant
`a₄, s₁, b₆₂, v₁` face. -/
def fourteenthFace_zeroU1_Wcof_rest810
    (h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51 b4 : F[X]) (lambda : F) :
    F[X] :=
  -(55296 : F[X]) * a4 * Polynomial.C lambda * t1 -
      (30720 : F[X]) * a4 * t1 ^ 2 + (131072 : F[X]) * b4 -
    (81920 : F[X]) * b51 * t1 + (73728 : F[X]) * b62 * t1 ^ 2 +
    (69120 : F[X]) * Polynomial.C lambda * t1 * v1 ^ 2 -
      (55296 : F[X]) * Polynomial.C lambda * u2 * v1 -
    (245760 : F[X]) * s1 * t1 ^ 2 * v1 +
      (196608 : F[X]) * s1 * t1 * u2 +
    (192000 : F[X]) * t1 ^ 2 * v1 ^ 2 - (337920 : F[X]) * t1 * u2 * v1 +
    (172032 : F[X]) * t1 * v1 * w2 + (122880 : F[X]) * u2 ^ 2 -
      (114688 : F[X]) * u2 * w2 +
    ((36864 : F[X]) * a3 * Polynomial.C lambda +
        (61440 : F[X]) * a3 * t1) *
      h +
    (-(163840 : F[X]) * a2 -
          (80640 : F[X]) * Polynomial.C lambda * t1 ^ 3 * v1 +
        (69120 : F[X]) * Polynomial.C lambda * t1 ^ 2 * u2 +
          (71680 : F[X]) * s1 * t1 ^ 4 +
        (12800 : F[X]) * t1 ^ 3 * u2 - (71680 : F[X]) * t1 ^ 3 * w2) *
      h ^ 2 +
    ((18144 : F[X]) * Polynomial.C lambda * t1 ^ 5 -
        (16800 : F[X]) * t1 ^ 6) *
      h ^ 4

theorem fourteenthFace_zeroU1_Wcof_split
    (h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51 b4 : F[X]) (lambda : F) :
    fourteenthFace_zeroU1_Wcof810 h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51 b4
        lambda =
      -(131072 : F[X]) * a4 * s1 + (245760 : F[X]) * a4 * v1 -
          (98304 : F[X]) * b62 * v1 + (98304 : F[X]) * s1 * v1 ^ 2 -
        (102400 : F[X]) * v1 ^ 3 +
        h ^ 2 *
          fourteenthFace_zeroU1_Wcof_rest810 h t1 v1 s1 w2 u2 a4 a3 a2
            b62 b51 b4 lambda := by
  simp only [fourteenthFace_zeroU1_Wcof810,
    fourteenthFace_zeroU1_Wcof_rest810]
  ring

theorem fourteenthFace_zeroU1_Wcof_sigma
    (h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51 b4 sigma rho : F[X])
    (lambda : F)
    (hsigma : (32 : F[X]) * s1 - (40 : F[X]) * v1 =
      h ^ 2 * sigma)
    (hrho : (40 : F[X]) * a4 - (32 : F[X]) * b62 +
        (5 : F[X]) * v1 ^ 2 =
      h ^ 2 * rho) :
    (5 : F[X]) *
          fourteenthFace_zeroU1_Wcof810 h t1 v1 s1 w2 u2 a4 a3 a2 b62
            b51 b4 lambda +
        (10240 : F[X]) *
          ((16 : F[X]) * b62 * v1 - (5 : F[X]) * v1 ^ 3) =
      h ^ 2 *
        ((10240 : F[X]) * rho * v1 - (16384 : F[X]) * sigma * b62 +
          (17920 : F[X]) * sigma * v1 ^ 2 -
          (512 : F[X]) * rho * sigma * h ^ 2 +
          (5 : F[X]) *
            fourteenthFace_zeroU1_Wcof_rest810 h t1 v1 s1 w2 u2 a4 a3
              a2 b62 b51 b4 lambda) := by
  have hsplit :=
    fourteenthFace_zeroU1_Wcof_split h t1 v1 s1 w2 u2 a4 a3 a2 b62 b51
      b4 lambda
  have hid :
      (5 : F[X]) *
            (-(131072 : F[X]) * a4 * s1 + (245760 : F[X]) * a4 * v1 -
              (98304 : F[X]) * b62 * v1 +
              (98304 : F[X]) * s1 * v1 ^ 2 -
              (102400 : F[X]) * v1 ^ 3) +
          (10240 : F[X]) *
            ((16 : F[X]) * b62 * v1 - (5 : F[X]) * v1 ^ 3) =
        -(512 : F[X]) *
            ((40 : F[X]) * a4 - (32 : F[X]) * b62 +
              (5 : F[X]) * v1 ^ 2) *
            ((32 : F[X]) * s1 - (40 : F[X]) * v1) +
          (10240 : F[X]) * v1 *
            ((40 : F[X]) * a4 - (32 : F[X]) * b62 +
              (5 : F[X]) * v1 ^ 2) -
          (16384 : F[X]) * b62 *
            ((32 : F[X]) * s1 - (40 : F[X]) * v1) +
          (17920 : F[X]) * v1 ^ 2 *
            ((32 : F[X]) * s1 - (40 : F[X]) * v1) := by
    ring
  have hleft :
      (5 : F[X]) *
            ( -(131072 : F[X]) * a4 * s1 + (245760 : F[X]) * a4 * v1 -
                (98304 : F[X]) * b62 * v1 +
                (98304 : F[X]) * s1 * v1 ^ 2 -
                (102400 : F[X]) * v1 ^ 3 +
              h ^ 2 *
                fourteenthFace_zeroU1_Wcof_rest810 h t1 v1 s1 w2 u2 a4
                  a3 a2 b62 b51 b4 lambda) +
          (10240 : F[X]) *
            ((16 : F[X]) * b62 * v1 - (5 : F[X]) * v1 ^ 3) =
        (5 : F[X]) *
              (-(131072 : F[X]) * a4 * s1 +
                (245760 : F[X]) * a4 * v1 -
                (98304 : F[X]) * b62 * v1 +
                (98304 : F[X]) * s1 * v1 ^ 2 -
                (102400 : F[X]) * v1 ^ 3) +
            (10240 : F[X]) *
              ((16 : F[X]) * b62 * v1 - (5 : F[X]) * v1 ^ 3) +
          (5 : F[X]) * h ^ 2 *
            fourteenthFace_zeroU1_Wcof_rest810 h t1 v1 s1 w2 u2 a4 a3
              a2 b62 b51 b4 lambda := by
    ring
  rw [hsplit, hleft, hid, hsigma, hrho]
  ring

end FourteenthFaceScalars810

/-! ## Source-facing fourteenth-face packet -/

section NonzeroFourteenthFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local fourteenth-face packet: the thirteenth-face split together
with the source-facing refinement of every live branch. -/
theorem nonzeroFace810_linearRoot_fourteenthInitialPacket
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
                  0 ∧
                (4177920 : k) * (p.coeff 4).eval a *
                        (t0.eval a) ^ 3 -
                      (11796480 : k) * (p.coeff 4).eval a *
                        t0.eval a * v1.eval a +
                      (10485760 : k) * (p.coeff 4).eval a *
                        u1.eval a +
                      (7208960 : k) * (q.coeff 5).eval a *
                        (t0.eval a) ^ 2 -
                      (10485760 : k) * (q.coeff 5).eval a *
                        v1.eval a -
                      (6848512 : k) * b62.eval a *
                        (t0.eval a) ^ 3 +
                      (17301504 : k) * b62.eval a * t0.eval a *
                        v1.eval a -
                      (12582912 : k) * b62.eval a * u1.eval a +
                      (300960 : k) * (t0.eval a) ^ 7 -
                      (2675200 : k) * (t0.eval a) ^ 5 * v1.eval a +
                      (4561920 : k) * (t0.eval a) ^ 4 * u1.eval a +
                      (7096320 : k) * (t0.eval a) ^ 3 *
                        (v1.eval a) ^ 2 -
                      (15769600 : k) * (t0.eval a) ^ 2 *
                        u1.eval a * v1.eval a +
                      (7208960 : k) * t0.eval a *
                        (u1.eval a) ^ 2 -
                      (5406720 : k) * t0.eval a *
                        (v1.eval a) ^ 3 +
                      (7208960 : k) * u1.eval a *
                        (v1.eval a) ^ 2 +
                    (384 : k) * t0.eval a *
                      ((3 : k) * (t0.eval a) ^ 2 -
                        (8 : k) * v1.eval a) *
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
                ∃ (t1 u2 w2 b51 sigma rho pi : k[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    (16 : k[X]) * b62 * v1 -
                        (5 : k[X]) * v1 ^ 3 =
                      h0 ^ 2 * pi ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : k[X]) * (p.coeff 4) -
                          (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2) ∧
                    h0 ^ 2 ∣
                      ((16 : k[X]) * b62 * v1 -
                        (5 : k[X]) * v1 ^ 3) ∧
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
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_thirteenthInitialPacket p q H h0 j lambda a
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
              0 ∧
            (4177920 : k) * (p.coeff 4).eval a * (t0.eval a) ^ 3 -
                  (11796480 : k) * (p.coeff 4).eval a * t0.eval a *
                    v1.eval a +
                  (10485760 : k) * (p.coeff 4).eval a * u1.eval a +
                  (7208960 : k) * (q.coeff 5).eval a *
                    (t0.eval a) ^ 2 -
                  (10485760 : k) * (q.coeff 5).eval a * v1.eval a -
                  (6848512 : k) * b62.eval a * (t0.eval a) ^ 3 +
                  (17301504 : k) * b62.eval a * t0.eval a *
                    v1.eval a -
                  (12582912 : k) * b62.eval a * u1.eval a +
                  (300960 : k) * (t0.eval a) ^ 7 -
                  (2675200 : k) * (t0.eval a) ^ 5 * v1.eval a +
                  (4561920 : k) * (t0.eval a) ^ 4 * u1.eval a +
                  (7096320 : k) * (t0.eval a) ^ 3 *
                    (v1.eval a) ^ 2 -
                  (15769600 : k) * (t0.eval a) ^ 2 * u1.eval a *
                    v1.eval a +
                  (7208960 : k) * t0.eval a * (u1.eval a) ^ 2 -
                  (5406720 : k) * t0.eval a * (v1.eval a) ^ 3 +
                  (7208960 : k) * u1.eval a * (v1.eval a) ^ 2 +
                (384 : k) * t0.eval a *
                  ((3 : k) * (t0.eval a) ^ 2 -
                    (8 : k) * v1.eval a) *
                  ((1024 : k) * b62.eval a +
                    (25 : k) * (t0.eval a) ^ 4 -
                    (320 : k) * (v1.eval a) ^ 2) =
              0 := fun hF1 =>
      have h13 := hF1w hF1
      ⟨h13.1, h13.2.1, h13.2.2,
        fourteenthFace_leftF1_X_product810 (t0.eval a) (v1.eval a)
          (u1.eval a) ((p.coeff 4).eval a) (b62.eval a)
          ((q.coeff 5).eval a) hF1 hGred hVred⟩
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
    · obtain ⟨hu1z, t1, u2, w2, b51, sigma, rho, ht1, hu2, hw2, hb51,
        hsigmapoly, hrhopoly, hp5_3, hq7_5, hq5d, hsigmadvd, hrhovd,
        hTform, hVform, hprod⟩ := hu1z
      have hWsubst :
          localClearedSixthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (p.coeff 4) (p.coeff 3) (p.coeff 2)
              (h0 ^ 5 * s0) (h0 ^ 3 * w0) (h0 ^ 2 * b62)
              (q.coeff 5) (q.coeff 4) lambda =
            localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0, hb62]
      have hWparen :
          sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (h0 ^ 2 * b62) (q.coeff 5)
              (q.coeff 4) lambda =
            Polynomial.C zeta * h0 ^ 9 :=
        sixthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (h0 ^ 2 * b62)
          (q.coeff 5) (q.coeff 4) lambda zeta hh0
          (hWsubst.trans hWrel)
      have hu0' : u0 = h0 ^ 2 * u2 := by
        rw [hu1, hu2]
        ring
      have hw0' : w0 = h0 ^ 2 * w2 := by
        rw [hw1, hw2]
        ring
      have hWleft :
          sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (h0 ^ 2 * b62) (q.coeff 5)
              (q.coeff 4) lambda =
            h0 ^ 3 *
              fourteenthFace_zeroU1_Wcof810 h0 t1 v1 s1 w2 u2
                (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
                (q.coeff 4) lambda := by
        simpa [ht1, hv1, hs1, hw0', hu0', hb51] using
          fourteenthFace_sixth_zeroU1_mul_h h0 t1 v1 s1 w2 u2
            (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
            (q.coeff 4) lambda
      have hWcof :
          fourteenthFace_zeroU1_Wcof810 h0 t1 v1 s1 w2 u2
              (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
              (q.coeff 4) lambda =
            Polynomial.C zeta * h0 ^ 6 := by
        apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
        have hscale : Polynomial.C zeta * h0 ^ 9 =
            h0 ^ 3 * (Polynomial.C zeta * h0 ^ 6) := by ring
        rw [← hWleft, hWparen, hscale]
      have hWfact :=
        fourteenthFace_zeroU1_Wcof_sigma h0 t1 v1 s1 w2 u2
          (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51 (q.coeff 4)
          sigma rho lambda hsigmapoly hrhopoly
      have h10240 : (10240 : k) ≠ 0 := by norm_num
      have hCne : Polynomial.C (10240 : k) ≠ 0 :=
        mt Polynomial.C_eq_zero.mp h10240
      have h5Wcof :
          (5 : k[X]) *
              fourteenthFace_zeroU1_Wcof810 h0 t1 v1 s1 w2 u2
                (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
                (q.coeff 4) lambda =
            (5 : k[X]) * (Polynomial.C zeta * h0 ^ 6) := by
        rw [hWcof]
      have hWright_pow :
          (10240 : k[X]) *
              ((16 : k[X]) * b62 * v1 - (5 : k[X]) * v1 ^ 3) =
            h0 ^ 2 *
              ((10240 : k[X]) * rho * v1 -
                (16384 : k[X]) * sigma * b62 +
                (17920 : k[X]) * sigma * v1 ^ 2 -
                (512 : k[X]) * rho * sigma * h0 ^ 2 +
                (5 : k[X]) *
                  fourteenthFace_zeroU1_Wcof_rest810 h0 t1 v1 s1 w2
                    u2 (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
                    (q.coeff 4) lambda -
                (5 : k[X]) * Polynomial.C zeta * h0 ^ 4) := by
        linear_combination hWfact - h5Wcof
      have hpipoly :
          (16 : k[X]) * b62 * v1 - (5 : k[X]) * v1 ^ 3 =
            h0 ^ 2 *
              (Polynomial.C (10240 : k)⁻¹ *
                ((10240 : k[X]) * rho * v1 -
                  (16384 : k[X]) * sigma * b62 +
                  (17920 : k[X]) * sigma * v1 ^ 2 -
                  (512 : k[X]) * rho * sigma * h0 ^ 2 +
                  (5 : k[X]) *
                    fourteenthFace_zeroU1_Wcof_rest810 h0 t1 v1 s1 w2
                      u2 (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
                      (q.coeff 4) lambda -
                  (5 : k[X]) * Polynomial.C zeta * h0 ^ 4)) := by
        have hC10240 : (10240 : k[X]) = Polynomial.C (10240 : k) :=
          (Polynomial.C_eq_natCast 10240).symm
        have hunit :
            Polynomial.C (10240 : k) * Polynomial.C (10240 : k)⁻¹ =
              1 := by
          rw [← map_mul, mul_inv_cancel₀ h10240, map_one]
        have hWright_pow' :
            Polynomial.C (10240 : k) *
                ((16 : k[X]) * b62 * v1 - (5 : k[X]) * v1 ^ 3) =
              h0 ^ 2 *
                ((10240 : k[X]) * rho * v1 -
                  (16384 : k[X]) * sigma * b62 +
                  (17920 : k[X]) * sigma * v1 ^ 2 -
                  (512 : k[X]) * rho * sigma * h0 ^ 2 +
                  (5 : k[X]) *
                    fourteenthFace_zeroU1_Wcof_rest810 h0 t1 v1 s1 w2
                      u2 (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
                      (q.coeff 4) lambda -
                  (5 : k[X]) * Polynomial.C zeta * h0 ^ 4) := by
          rw [← hC10240]
          exact hWright_pow
        apply mul_left_cancel₀ hCne
        rw [hWright_pow']
        conv_rhs =>
          rw [mul_left_comm (Polynomial.C (10240 : k)) (h0 ^ 2)]
          arg 2
          rw [← mul_assoc, hunit, one_mul]
      have hpivd :
          h0 ^ 2 ∣
            ((16 : k[X]) * b62 * v1 - (5 : k[X]) * v1 ^ 3) :=
        ⟨_, hpipoly⟩
      refine Or.inl ⟨hu1z, t1, u2, w2, b51, sigma, rho,
        Polynomial.C (10240 : k)⁻¹ *
          ((10240 : k[X]) * rho * v1 -
            (16384 : k[X]) * sigma * b62 +
            (17920 : k[X]) * sigma * v1 ^ 2 -
            (512 : k[X]) * rho * sigma * h0 ^ 2 +
            (5 : k[X]) *
              fourteenthFace_zeroU1_Wcof_rest810 h0 t1 v1 s1 w2 u2
                (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 b51
                (q.coeff 4) lambda -
            (5 : k[X]) * Polynomial.C zeta * h0 ^ 4), ht1, hu2, hw2,
        hb51, hsigmapoly, hrhopoly, hpipoly, hp5_3, hq7_5, hq5d,
        hsigmadvd, hrhovd, hpivd, hTform, hVform, hprod⟩
    · obtain ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1, homega,
        hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform⟩ := hcomp
      exact Or.inr ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1, homega,
        hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform⟩

/-- Source-facing fourteenth-face packet of a normalized scale-two `(8,10)`
nonzero face: the thirteenth-face split together with the next-order
sixth refinements of every live branch. -/
theorem normalized810ScaleTwo_nonzeroFace_fourteenthInitialPacket
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
                  0 ∧
                (4177920 : K) * (p.coeff 4).eval a *
                        (t0.eval a) ^ 3 -
                      (11796480 : K) * (p.coeff 4).eval a *
                        t0.eval a * v1.eval a +
                      (10485760 : K) * (p.coeff 4).eval a *
                        u1.eval a +
                      (7208960 : K) * (q.coeff 5).eval a *
                        (t0.eval a) ^ 2 -
                      (10485760 : K) * (q.coeff 5).eval a *
                        v1.eval a -
                      (6848512 : K) * b62.eval a *
                        (t0.eval a) ^ 3 +
                      (17301504 : K) * b62.eval a * t0.eval a *
                        v1.eval a -
                      (12582912 : K) * b62.eval a * u1.eval a +
                      (300960 : K) * (t0.eval a) ^ 7 -
                      (2675200 : K) * (t0.eval a) ^ 5 * v1.eval a +
                      (4561920 : K) * (t0.eval a) ^ 4 * u1.eval a +
                      (7096320 : K) * (t0.eval a) ^ 3 *
                        (v1.eval a) ^ 2 -
                      (15769600 : K) * (t0.eval a) ^ 2 *
                        u1.eval a * v1.eval a +
                      (7208960 : K) * t0.eval a *
                        (u1.eval a) ^ 2 -
                      (5406720 : K) * t0.eval a *
                        (v1.eval a) ^ 3 +
                      (7208960 : K) * u1.eval a *
                        (v1.eval a) ^ 2 +
                    (384 : K) * t0.eval a *
                      ((3 : K) * (t0.eval a) ^ 2 -
                        (8 : K) * v1.eval a) *
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
                ∃ (t1 u2 w2 b51 sigma rho pi : K[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : K[X]) * (p.coeff 4) -
                          (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    (16 : K[X]) * b62 * v1 -
                        (5 : K[X]) * v1 ^ 3 =
                      h0 ^ 2 * pi ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : K[X]) * (p.coeff 4) -
                          (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2) ∧
                    h0 ^ 2 ∣
                      ((16 : K[X]) * b62 * v1 -
                        (5 : K[X]) * v1 ^ 3) ∧
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
    nonzeroFace810_linearRoot_fourteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroFourteenthFace810

#print axioms fourteenthCoefficientJacobianRow_810
#print axioms fourteenthFace_leftF1_X_product810
#print axioms fourteenthFace_left_c1W_reduces810
#print axioms fourteenthFace_comp_W_nextOrder810
#print axioms fourteenthFace_sixth_zeroU1_mul_h
#print axioms fourteenthFace_zeroU1_Wcof_sigma
#print axioms nonzeroFace810_linearRoot_fourteenthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_fourteenthInitialPacket

end Max11DegreeRoutes
