import LowScale810ScaleTwoNinthFace

/-! # Scale-two tenth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the ninth-face packet supplies the degree-`8`
Jacobian row and the collapsed two-component jet `v₀ = h v₁`,
`s₀ = h s₁`, `u₀ = h u₁`, `w₀ = h w₁` together with `h⁸ ∣ q₉`,
`h² ∣ q₆`, the left identities `32 s₁ - 40 v₁ = 5 t₀²` and
`128 w₁ - 160 u₁ - 40 t₀ v₁ + 5 t₀³ = 0`, and the right identities
`t₀ = 0`, `4 s₁ = 5 v₁`, and `4 w₁ = 5 u₁`.

The next unused Keller coefficient is the degree-`7` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`8 P G' + 7 Q F' + 6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A'
- G P' - 2 F Q' - 3 E R' - 4 D S' - 5 C T' - 6 B U' - 7 A V' - 8 X'
= 0`.  Clearing the corresponding first integral against the remaining
decic coordinate produces a defect larger than the remaining exact jet,
so this file isolates that Jacobian identity and the strongest exact
next-order refinement of the collapsed ninth-face jet.

Evaluating the fourth through seventh defects on that packet upgrades
the jet by the source-facing loads among `a₄ = p₄(a)`, `b₅ = q₅(a)`,
and `b₆₂ = (q₆/h²)(a)`.  On both components
`2560 a₄ - 2048 b₆₂ + 35 t₀⁴ - 240 t₀² v₁ + 640 t₀ u₁ + 320 v₁² = 0`
together with the next fifth-, sixth-, and seventh-defect cofactors; on
the right these specialise to `40 a₄ - 32 b₆₂ + 5 v₁² = 0`,
`16 b₅ = 5 u₁ v₁`, `16 b₆₂ v₁ + 10 u₁² - 5 v₁³ = 0`, and the
alternative `u₁ (5 v₁² - 8 b₆₂) = 0`.  No further individual vanishing
of `p₄, p₃, p₂, p₁, q₅, q₄, q₃` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the ninth face start
at degree `7`. -/
theorem tenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 7).derivative * q.coeff 1 +
        (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 0).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 1).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 6).derivative +
        p.coeff 1 * (q.coeff 7).derivative) =
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
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
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
  rw [hC8, hC7, hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Ninth-jet parentheticals of the fourth through seventh defects -/

section TenthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Cofactor of `h²` in the sixth-jet fourth defect after the ninth-packet
vanishing `v₀ = h v₁`, `s₀ = h s₁`, `u₀ = h u₁`, `w₀ = h w₁`,
`b₆ = h² b₆₂`. -/
def fourthJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 b62 : F[X]) (lambda : F) : F[X] :=
  -(2560 : F[X]) * a4 + (2048 : F[X]) * b62 +
    (1792 : F[X]) * s1 * t0 ^ 2 - (2048 : F[X]) * s1 * v1 -
    (385 : F[X]) * t0 ^ 4 - (1120 : F[X]) * t0 ^ 2 * v1 +
    (1600 : F[X]) * t0 * u1 - (1792 : F[X]) * t0 * w1 +
    (2240 : F[X]) * v1 ^ 2 +
    ((462 : F[X]) * Polynomial.C lambda * t0 ^ 3 -
        (1008 : F[X]) * Polynomial.C lambda * t0 * v1 +
      (576 : F[X]) * Polynomial.C lambda * u1) * h

/-- Cofactor of `h²` in the sixth-jet fifth defect after the ninth-packet
vanishing. -/
def fifthJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 a3 b62 b5 : F[X]) (lambda : F) : F[X] :=
  (81920 : F[X]) * a4 * t0 + (131072 : F[X]) * b5 -
    (98304 : F[X]) * b62 * t0 - (93184 : F[X]) * s1 * t0 ^ 3 +
    (212992 : F[X]) * s1 * t0 * v1 - (131072 : F[X]) * s1 * u1 +
    (21112 : F[X]) * t0 ^ 5 + (29120 : F[X]) * t0 ^ 3 * v1 -
    (49920 : F[X]) * t0 ^ 2 * u1 + (93184 : F[X]) * t0 ^ 2 * w1 -
    (199680 : F[X]) * t0 * v1 ^ 2 + (266240 : F[X]) * u1 * v1 -
    (114688 : F[X]) * v1 * w1 +
    ((36864 : F[X]) * a4 * Polynomial.C lambda -
        (23751 : F[X]) * Polynomial.C lambda * t0 ^ 4 +
      (78624 : F[X]) * Polynomial.C lambda * t0 ^ 2 * v1 -
        (59904 : F[X]) * Polynomial.C lambda * t0 * u1 -
      (29952 : F[X]) * Polynomial.C lambda * v1 ^ 2) * h +
    (-(163840 : F[X]) * a3) * h ^ 2

/-- Cofactor of `h³` in the sixth-jet sixth defect after the ninth-packet
vanishing. -/
def sixthJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 a3 a2 b62 b5 b4 : F[X]) (lambda : F) : F[X] :=
  -(131072 : F[X]) * a4 * s1 - (30720 : F[X]) * a4 * t0 ^ 2 +
    (245760 : F[X]) * a4 * v1 - (81920 : F[X]) * b5 * t0 +
    (73728 : F[X]) * b62 * t0 ^ 2 - (98304 : F[X]) * b62 * v1 +
    (71680 : F[X]) * s1 * t0 ^ 4 - (245760 : F[X]) * s1 * t0 ^ 2 * v1 +
    (196608 : F[X]) * s1 * t0 * u1 + (98304 : F[X]) * s1 * v1 ^ 2 -
    (16800 : F[X]) * t0 ^ 6 + (12800 : F[X]) * t0 ^ 3 * u1 -
    (71680 : F[X]) * t0 ^ 3 * w1 + (192000 : F[X]) * t0 ^ 2 * v1 ^ 2 -
    (337920 : F[X]) * t0 * u1 * v1 + (172032 : F[X]) * t0 * v1 * w1 +
    (122880 : F[X]) * u1 ^ 2 - (114688 : F[X]) * u1 * w1 -
    (102400 : F[X]) * v1 ^ 3 +
    (-(55296 : F[X]) * a4 * Polynomial.C lambda * t0 +
        (18144 : F[X]) * Polynomial.C lambda * t0 ^ 5 -
      (80640 : F[X]) * Polynomial.C lambda * t0 ^ 3 * v1 +
        (69120 : F[X]) * Polynomial.C lambda * t0 ^ 2 * u1 +
      (69120 : F[X]) * Polynomial.C lambda * t0 * v1 ^ 2 -
        (55296 : F[X]) * Polynomial.C lambda * u1 * v1) * h +
    ((61440 : F[X]) * a3 * t0 + (131072 : F[X]) * b4) * h ^ 2 +
    ((36864 : F[X]) * a3 * Polynomial.C lambda) * h ^ 3 +
    (-(163840 : F[X]) * a2) * h ^ 4

/-- Cofactor of `h³` in the sixth-jet seventh defect after the ninth-packet
vanishing. -/
def seventhJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 a3 a2 a1 b62 b5 b4 b3 : F[X])
    (lambda : F) : F[X] :=
  (23068672 : F[X]) * a4 * s1 * t0 - (36044800 : F[X]) * a4 * t0 * v1 +
    (28835840 : F[X]) * a4 * u1 - (14680064 : F[X]) * a4 * w1 +
    (7208960 : F[X]) * b5 * t0 ^ 2 - (10485760 : F[X]) * b5 * v1 -
    (6848512 : F[X]) * b62 * t0 ^ 3 +
    (17301504 : F[X]) * b62 * t0 * v1 -
    (12582912 : F[X]) * b62 * u1 - (6741504 : F[X]) * s1 * t0 ^ 5 +
    (30818304 : F[X]) * s1 * t0 ^ 3 * v1 -
    (27394048 : F[X]) * s1 * t0 ^ 2 * u1 -
    (27394048 : F[X]) * s1 * t0 * v1 ^ 2 +
    (23068672 : F[X]) * s1 * u1 * v1 + (1617660 : F[X]) * t0 ^ 7 -
    (2106720 : F[X]) * t0 ^ 5 * v1 + (1203840 : F[X]) * t0 ^ 4 * u1 +
    (6741504 : F[X]) * t0 ^ 4 * w1 - (19261440 : F[X]) * t0 ^ 3 * v1 ^ 2 +
    (38522880 : F[X]) * t0 ^ 2 * u1 * v1 -
    (23969792 : F[X]) * t0 ^ 2 * v1 * w1 -
    (18022400 : F[X]) * t0 * u1 ^ 2 +
    (20185088 : F[X]) * t0 * u1 * w1 +
    (25681920 : F[X]) * t0 * v1 ^ 3 -
    (34242560 : F[X]) * u1 * v1 ^ 2 +
    (10092544 : F[X]) * v1 ^ 2 * w1 +
    ((7704576 : F[X]) * a4 * Polynomial.C lambda * t0 ^ 2 -
        (6488064 : F[X]) * a4 * Polynomial.C lambda * v1 -
      (1698543 : F[X]) * Polynomial.C lambda * t0 ^ 6 +
        (9480240 : F[X]) * Polynomial.C lambda * t0 ^ 4 * v1 -
      (8667648 : F[X]) * Polynomial.C lambda * t0 ^ 3 * u1 -
        (13001472 : F[X]) * Polynomial.C lambda * t0 ^ 2 * v1 ^ 2 +
      (15409152 : F[X]) * Polynomial.C lambda * t0 * u1 * v1 -
        (3244032 : F[X]) * Polynomial.C lambda * u1 ^ 2 +
      (2568192 : F[X]) * Polynomial.C lambda * v1 ^ 3) * h +
    (-(16777216 : F[X]) * a3 * s1 - (1802240 : F[X]) * a3 * t0 ^ 2 +
        (28835840 : F[X]) * a3 * v1 -
      (8388608 : F[X]) * b4 * t0) * h ^ 2 +
    (-(6488064 : F[X]) * a3 * Polynomial.C lambda * t0) * h ^ 3 +
    ((5242880 : F[X]) * a2 * t0 + (16777216 : F[X]) * b3) * h ^ 4 +
    ((4718592 : F[X]) * a2 * Polynomial.C lambda) * h ^ 5 +
    (-(20971520 : F[X]) * a1) * h ^ 6

set_option maxHeartbeats 4000000 in
theorem fourthJetParen810_ninth_mul_h
    (h t0 v1 s1 w1 u1 a4 b62 : F[X]) (lambda : F) :
    fourthJetParen810_sixth h t0 (h * v1) (h * s1) (h * w1) (h * u1) a4
        (h ^ 2 * b62) lambda =
      h ^ 2 * fourthJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 b62
        lambda := by
  simp only [fourthJetParen810_sixth, fourthJetParen810_ninthCofactor]
  ring

set_option maxHeartbeats 8000000 in
theorem fifthJetParen810_ninth_mul_h
    (h t0 v1 s1 w1 u1 a4 a3 b62 b5 : F[X]) (lambda : F) :
    fifthJetParen810_sixth h t0 (h * v1) (h * s1) (h * w1) (h * u1) a4 a3
        (h ^ 2 * b62) b5 lambda =
      h ^ 2 * fifthJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 a3 b62
        b5 lambda := by
  simp only [fifthJetParen810_sixth, fifthJetParen810_ninthCofactor]
  ring

set_option maxHeartbeats 8000000 in
theorem sixthJetParen810_ninth_mul_h
    (h t0 v1 s1 w1 u1 a4 a3 a2 b62 b5 b4 : F[X]) (lambda : F) :
    sixthJetParen810_sixth h t0 (h * v1) (h * s1) (h * w1) (h * u1) a4 a3
        a2 (h ^ 2 * b62) b5 b4 lambda =
      h ^ 3 * sixthJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 a3 a2
        b62 b5 b4 lambda := by
  simp only [sixthJetParen810_sixth, sixthJetParen810_ninthCofactor]
  ring

set_option maxHeartbeats 16000000 in
theorem seventhJetParen810_ninth_mul_h
    (h t0 v1 s1 w1 u1 a4 a3 a2 a1 b62 b5 b4 b3 : F[X]) (lambda : F) :
    seventhJetParen810 h t0 (h * v1) (h * s1) (h * w1) (h * u1) a4 a3 a2
        a1 (h ^ 2 * b62) b5 b4 b3 lambda =
      h ^ 3 * seventhJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 a3 a2
        a1 b62 b5 b4 b3 lambda := by
  simp only [seventhJetParen810, seventhJetParen810_ninthCofactor]
  ring

theorem eval_fourthJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 b62 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (fourthJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 b62
          lambda) =
      -(2560 : F) * Polynomial.eval root a4 +
        (2048 : F) * Polynomial.eval root b62 +
        (1792 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 2 -
        (2048 : F) * Polynomial.eval root s1 *
          Polynomial.eval root v1 -
        (385 : F) * (Polynomial.eval root t0) ^ 4 -
        (1120 : F) * (Polynomial.eval root t0) ^ 2 *
          Polynomial.eval root v1 +
        (1600 : F) * Polynomial.eval root t0 *
          Polynomial.eval root u1 -
        (1792 : F) * Polynomial.eval root t0 *
          Polynomial.eval root w1 +
        (2240 : F) * (Polynomial.eval root v1) ^ 2 := by
  simp [fourthJetParen810_ninthCofactor, hroot]

theorem eval_fifthJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 a3 b62 b5 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (fifthJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 a3 b62 b5
          lambda) =
      (81920 : F) * Polynomial.eval root a4 * Polynomial.eval root t0 +
        (131072 : F) * Polynomial.eval root b5 -
        (98304 : F) * Polynomial.eval root b62 *
          Polynomial.eval root t0 -
        (93184 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 3 +
        (212992 : F) * Polynomial.eval root s1 *
          Polynomial.eval root t0 * Polynomial.eval root v1 -
        (131072 : F) * Polynomial.eval root s1 *
          Polynomial.eval root u1 +
        (21112 : F) * (Polynomial.eval root t0) ^ 5 +
        (29120 : F) * (Polynomial.eval root t0) ^ 3 *
          Polynomial.eval root v1 -
        (49920 : F) * (Polynomial.eval root t0) ^ 2 *
          Polynomial.eval root u1 +
        (93184 : F) * (Polynomial.eval root t0) ^ 2 *
          Polynomial.eval root w1 -
        (199680 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root v1) ^ 2 +
        (266240 : F) * Polynomial.eval root u1 *
          Polynomial.eval root v1 -
        (114688 : F) * Polynomial.eval root v1 *
          Polynomial.eval root w1 := by
  simp [fifthJetParen810_ninthCofactor, hroot]

theorem eval_sixthJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 a3 a2 b62 b5 b4 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (sixthJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 a3 a2 b62
          b5 b4 lambda) =
      -(131072 : F) * Polynomial.eval root a4 *
          Polynomial.eval root s1 -
        (30720 : F) * Polynomial.eval root a4 *
          (Polynomial.eval root t0) ^ 2 +
        (245760 : F) * Polynomial.eval root a4 *
          Polynomial.eval root v1 -
        (81920 : F) * Polynomial.eval root b5 *
          Polynomial.eval root t0 +
        (73728 : F) * Polynomial.eval root b62 *
          (Polynomial.eval root t0) ^ 2 -
        (98304 : F) * Polynomial.eval root b62 *
          Polynomial.eval root v1 +
        (71680 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 4 -
        (245760 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 2 * Polynomial.eval root v1 +
        (196608 : F) * Polynomial.eval root s1 *
          Polynomial.eval root t0 * Polynomial.eval root u1 +
        (98304 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root v1) ^ 2 -
        (16800 : F) * (Polynomial.eval root t0) ^ 6 +
        (12800 : F) * (Polynomial.eval root t0) ^ 3 *
          Polynomial.eval root u1 -
        (71680 : F) * (Polynomial.eval root t0) ^ 3 *
          Polynomial.eval root w1 +
        (192000 : F) * (Polynomial.eval root t0) ^ 2 *
          (Polynomial.eval root v1) ^ 2 -
        (337920 : F) * Polynomial.eval root t0 *
          Polynomial.eval root u1 * Polynomial.eval root v1 +
        (172032 : F) * Polynomial.eval root t0 *
          Polynomial.eval root v1 * Polynomial.eval root w1 +
        (122880 : F) * (Polynomial.eval root u1) ^ 2 -
        (114688 : F) * Polynomial.eval root u1 *
          Polynomial.eval root w1 -
        (102400 : F) * (Polynomial.eval root v1) ^ 3 := by
  simp [sixthJetParen810_ninthCofactor, hroot]

theorem eval_seventhJetParen810_ninthCofactor
    (h t0 v1 s1 w1 u1 a4 a3 a2 a1 b62 b5 b4 b3 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (seventhJetParen810_ninthCofactor h t0 v1 s1 w1 u1 a4 a3 a2 a1
          b62 b5 b4 b3 lambda) =
      (23068672 : F) * Polynomial.eval root a4 *
          Polynomial.eval root s1 * Polynomial.eval root t0 -
        (36044800 : F) * Polynomial.eval root a4 *
          Polynomial.eval root t0 * Polynomial.eval root v1 +
        (28835840 : F) * Polynomial.eval root a4 *
          Polynomial.eval root u1 -
        (14680064 : F) * Polynomial.eval root a4 *
          Polynomial.eval root w1 +
        (7208960 : F) * Polynomial.eval root b5 *
          (Polynomial.eval root t0) ^ 2 -
        (10485760 : F) * Polynomial.eval root b5 *
          Polynomial.eval root v1 -
        (6848512 : F) * Polynomial.eval root b62 *
          (Polynomial.eval root t0) ^ 3 +
        (17301504 : F) * Polynomial.eval root b62 *
          Polynomial.eval root t0 * Polynomial.eval root v1 -
        (12582912 : F) * Polynomial.eval root b62 *
          Polynomial.eval root u1 -
        (6741504 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 5 +
        (30818304 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 3 * Polynomial.eval root v1 -
        (27394048 : F) * Polynomial.eval root s1 *
          (Polynomial.eval root t0) ^ 2 * Polynomial.eval root u1 -
        (27394048 : F) * Polynomial.eval root s1 *
          Polynomial.eval root t0 * (Polynomial.eval root v1) ^ 2 +
        (23068672 : F) * Polynomial.eval root s1 *
          Polynomial.eval root u1 * Polynomial.eval root v1 +
        (1617660 : F) * (Polynomial.eval root t0) ^ 7 -
        (2106720 : F) * (Polynomial.eval root t0) ^ 5 *
          Polynomial.eval root v1 +
        (1203840 : F) * (Polynomial.eval root t0) ^ 4 *
          Polynomial.eval root u1 +
        (6741504 : F) * (Polynomial.eval root t0) ^ 4 *
          Polynomial.eval root w1 -
        (19261440 : F) * (Polynomial.eval root t0) ^ 3 *
          (Polynomial.eval root v1) ^ 2 +
        (38522880 : F) * (Polynomial.eval root t0) ^ 2 *
          Polynomial.eval root u1 * Polynomial.eval root v1 -
        (23969792 : F) * (Polynomial.eval root t0) ^ 2 *
          Polynomial.eval root v1 * Polynomial.eval root w1 -
        (18022400 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root u1) ^ 2 +
        (20185088 : F) * Polynomial.eval root t0 *
          Polynomial.eval root u1 * Polynomial.eval root w1 +
        (25681920 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root v1) ^ 3 -
        (34242560 : F) * Polynomial.eval root u1 *
          (Polynomial.eval root v1) ^ 2 +
        (10092544 : F) * (Polynomial.eval root v1) ^ 2 *
          Polynomial.eval root w1 := by
  simp [seventhJetParen810_ninthCofactor, hroot]

/-- Reduced fourth-defect identity on the ninth-face jet. -/
def tenthFace_Gred810 (t0 v1 u1 a4 b62 : F) : Prop :=
  (2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
    (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
    (320 : F) * v1 ^ 2 = 0

/-- Reduced fifth-defect identity on the ninth-face jet. -/
def tenthFace_Vred810 (t0 v1 u1 a4 b62 b5 : F) : Prop :=
  (81920 : F) * a4 * t0 + (131072 : F) * b5 -
    (98304 : F) * b62 * t0 + (2912 : F) * t0 ^ 5 -
    (20480 : F) * t0 ^ 3 * v1 + (46080 : F) * t0 ^ 2 * u1 +
    (30720 : F) * t0 * v1 ^ 2 - (40960 : F) * u1 * v1 = 0

/-- Reduced sixth-defect identity on the ninth-face jet. -/
def tenthFace_Wred810 (t0 v1 u1 a4 b62 b5 : F) : Prop :=
  -(51200 : F) * a4 * t0 ^ 2 + (81920 : F) * a4 * v1 -
    (81920 : F) * b5 * t0 + (73728 : F) * b62 * t0 ^ 2 -
    (98304 : F) * b62 * v1 - (2800 : F) * t0 ^ 6 +
    (22080 : F) * t0 ^ 4 * v1 - (41600 : F) * t0 ^ 3 * u1 -
    (46080 : F) * t0 ^ 2 * v1 ^ 2 + (87040 : F) * t0 * u1 * v1 -
    (20480 : F) * u1 ^ 2 + (20480 : F) * v1 ^ 3 = 0

/-- Reduced seventh-defect identity on the ninth-face jet. -/
def tenthFace_Xred810 (t0 v1 u1 a4 b62 b5 : F) : Prop :=
  (4177920 : F) * a4 * t0 ^ 3 - (11796480 : F) * a4 * t0 * v1 +
    (10485760 : F) * a4 * u1 + (7208960 : F) * b5 * t0 ^ 2 -
    (10485760 : F) * b5 * v1 - (6848512 : F) * b62 * t0 ^ 3 +
    (17301504 : F) * b62 * t0 * v1 - (12582912 : F) * b62 * u1 +
    (300960 : F) * t0 ^ 7 - (2675200 : F) * t0 ^ 5 * v1 +
    (4561920 : F) * t0 ^ 4 * u1 + (7096320 : F) * t0 ^ 3 * v1 ^ 2 -
    (15769600 : F) * t0 ^ 2 * u1 * v1 +
    (7208960 : F) * t0 * u1 ^ 2 - (5406720 : F) * t0 * v1 ^ 3 +
    (7208960 : F) * u1 * v1 ^ 2 = 0

/-- The ninth-face third-defect reduction reconstructs the unreduced
third cofactor. -/
theorem tenthFace_thirdUnreduced_810 (t0 v1 s1 u1 w1 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2 = 0)
    (hTred : (128 : F) * w1 - (160 : F) * u1 - (40 : F) * t0 * v1 +
      (5 : F) * t0 ^ 3 = 0) :
    -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 - (640 : F) * u1 +
      (512 : F) * w1 + (100 : F) * t0 ^ 3 = 0 := by
  have hid :
      -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 - (640 : F) * u1 +
          (512 : F) * w1 + (100 : F) * t0 ^ 3 -
        (4 : F) * ((128 : F) * w1 - (160 : F) * u1 -
          (40 : F) * t0 * v1 + (5 : F) * t0 ^ 3) +
        (16 : F) * t0 *
          ((32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2) = 0 := by
    ring
  linear_combination hid + (4 : F) * hTred - (16 : F) * t0 * hM

/-- The next fourth-defect coefficient on the ninth-face jet. -/
theorem tenthFace_G_nextOrder810 (t0 v1 s1 u1 w1 a4 b62 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2 = 0)
    (hT : -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 - (640 : F) * u1 +
      (512 : F) * w1 + (100 : F) * t0 ^ 3 = 0)
    (hG : -(2560 : F) * a4 + (2048 : F) * b62 +
      (1792 : F) * s1 * t0 ^ 2 - (2048 : F) * s1 * v1 -
      (385 : F) * t0 ^ 4 - (1120 : F) * t0 ^ 2 * v1 +
      (1600 : F) * t0 * u1 - (1792 : F) * t0 * w1 +
      (2240 : F) * v1 ^ 2 = 0) :
    tenthFace_Gred810 t0 v1 u1 a4 b62 := by
  unfold tenthFace_Gred810
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hid :
      (2 : F) * ((2560 : F) * a4 - (2048 : F) * b62 +
          (35 : F) * t0 ^ 4 - (240 : F) * t0 ^ 2 * v1 +
          (640 : F) * t0 * u1 + (320 : F) * v1 ^ 2) =
        -((2 : F) * (-(2560 : F) * a4 + (2048 : F) * b62 +
            (1792 : F) * s1 * t0 ^ 2 - (2048 : F) * s1 * v1 -
            (385 : F) * t0 ^ 4 - (1120 : F) * t0 ^ 2 * v1 +
            (1600 : F) * t0 * u1 - (1792 : F) * t0 * w1 +
            (2240 : F) * v1 ^ 2) +
          (128 : F) * v1 *
            ((32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2) +
          (7 : F) * t0 *
            (-(512 : F) * s1 * t0 + (480 : F) * t0 * v1 -
              (640 : F) * u1 + (512 : F) * w1 +
              (100 : F) * t0 ^ 3)) := by
    ring
  have hcomb :
      (2 : F) * ((2560 : F) * a4 - (2048 : F) * b62 +
          (35 : F) * t0 ^ 4 - (240 : F) * t0 ^ 2 * v1 +
          (640 : F) * t0 * u1 + (320 : F) * v1 ^ 2) = 0 := by
    rw [hid]
    linear_combination -(2 : F) * hG - (128 : F) * v1 * hM -
      (7 : F) * t0 * hT
  exact (mul_eq_zero.mp hcomb).resolve_left h2

set_option maxHeartbeats 4000000 in
/-- The next fifth-defect coefficient on the ninth-face jet. -/
theorem tenthFace_V_nextOrder810 (t0 v1 s1 u1 w1 a4 b62 b5 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2 = 0)
    (hT : -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 - (640 : F) * u1 +
      (512 : F) * w1 + (100 : F) * t0 ^ 3 = 0)
    (hV : (81920 : F) * a4 * t0 + (131072 : F) * b5 -
      (98304 : F) * b62 * t0 - (93184 : F) * s1 * t0 ^ 3 +
      (212992 : F) * s1 * t0 * v1 - (131072 : F) * s1 * u1 +
      (21112 : F) * t0 ^ 5 + (29120 : F) * t0 ^ 3 * v1 -
      (49920 : F) * t0 ^ 2 * u1 + (93184 : F) * t0 ^ 2 * w1 -
      (199680 : F) * t0 * v1 ^ 2 + (266240 : F) * u1 * v1 -
      (114688 : F) * v1 * w1 = 0) :
    tenthFace_Vred810 t0 v1 u1 a4 b62 b5 := by
  unfold tenthFace_Vred810
  have hid :
      (81920 : F) * a4 * t0 + (131072 : F) * b5 -
          (98304 : F) * b62 * t0 + (2912 : F) * t0 ^ 5 -
          (20480 : F) * t0 ^ 3 * v1 + (46080 : F) * t0 ^ 2 * u1 +
          (30720 : F) * t0 * v1 ^ 2 - (40960 : F) * u1 * v1 =
        (81920 : F) * a4 * t0 + (131072 : F) * b5 -
            (98304 : F) * b62 * t0 - (93184 : F) * s1 * t0 ^ 3 +
            (212992 : F) * s1 * t0 * v1 - (131072 : F) * s1 * u1 +
            (21112 : F) * t0 ^ 5 + (29120 : F) * t0 ^ 3 * v1 -
            (49920 : F) * t0 ^ 2 * u1 + (93184 : F) * t0 ^ 2 * w1 -
            (199680 : F) * t0 * v1 ^ 2 + (266240 : F) * u1 * v1 -
            (114688 : F) * v1 * w1 +
          (-(3072 : F) * t0 * v1 + (4096 : F) * u1) *
            ((32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2) +
          (-(182 : F) * t0 ^ 2 + (224 : F) * v1) *
            (-(512 : F) * s1 * t0 + (480 : F) * t0 * v1 -
              (640 : F) * u1 + (512 : F) * w1 +
              (100 : F) * t0 ^ 3) := by
    ring
  rw [hid]
  linear_combination hV +
    (-(3072 : F) * t0 * v1 + (4096 : F) * u1) * hM +
    (-(182 : F) * t0 ^ 2 + (224 : F) * v1) * hT

set_option maxHeartbeats 4000000 in
/-- The next sixth-defect coefficient on the ninth-face jet. -/
theorem tenthFace_W_nextOrder810 (t0 v1 s1 u1 w1 a4 b62 b5 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2 = 0)
    (hT : -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 - (640 : F) * u1 +
      (512 : F) * w1 + (100 : F) * t0 ^ 3 = 0)
    (hW : -(131072 : F) * a4 * s1 - (30720 : F) * a4 * t0 ^ 2 +
      (245760 : F) * a4 * v1 - (81920 : F) * b5 * t0 +
      (73728 : F) * b62 * t0 ^ 2 - (98304 : F) * b62 * v1 +
      (71680 : F) * s1 * t0 ^ 4 - (245760 : F) * s1 * t0 ^ 2 * v1 +
      (196608 : F) * s1 * t0 * u1 + (98304 : F) * s1 * v1 ^ 2 -
      (16800 : F) * t0 ^ 6 + (12800 : F) * t0 ^ 3 * u1 -
      (71680 : F) * t0 ^ 3 * w1 + (192000 : F) * t0 ^ 2 * v1 ^ 2 -
      (337920 : F) * t0 * u1 * v1 + (172032 : F) * t0 * v1 * w1 +
      (122880 : F) * u1 ^ 2 - (114688 : F) * u1 * w1 -
      (102400 : F) * v1 ^ 3 = 0) :
    tenthFace_Wred810 t0 v1 u1 a4 b62 b5 := by
  unfold tenthFace_Wred810
  have hid :
      -(51200 : F) * a4 * t0 ^ 2 + (81920 : F) * a4 * v1 -
          (81920 : F) * b5 * t0 + (73728 : F) * b62 * t0 ^ 2 -
          (98304 : F) * b62 * v1 - (2800 : F) * t0 ^ 6 +
          (22080 : F) * t0 ^ 4 * v1 - (41600 : F) * t0 ^ 3 * u1 -
          (46080 : F) * t0 ^ 2 * v1 ^ 2 + (87040 : F) * t0 * u1 * v1 -
          (20480 : F) * u1 ^ 2 + (20480 : F) * v1 ^ 3 =
        -(131072 : F) * a4 * s1 - (30720 : F) * a4 * t0 ^ 2 +
            (245760 : F) * a4 * v1 - (81920 : F) * b5 * t0 +
            (73728 : F) * b62 * t0 ^ 2 - (98304 : F) * b62 * v1 +
            (71680 : F) * s1 * t0 ^ 4 -
            (245760 : F) * s1 * t0 ^ 2 * v1 +
            (196608 : F) * s1 * t0 * u1 + (98304 : F) * s1 * v1 ^ 2 -
            (16800 : F) * t0 ^ 6 + (12800 : F) * t0 ^ 3 * u1 -
            (71680 : F) * t0 ^ 3 * w1 +
            (192000 : F) * t0 ^ 2 * v1 ^ 2 -
            (337920 : F) * t0 * u1 * v1 +
            (172032 : F) * t0 * v1 * w1 + (122880 : F) * u1 ^ 2 -
            (114688 : F) * u1 * w1 - (102400 : F) * v1 ^ 3 +
          ((4096 : F) * a4 + (2304 : F) * t0 ^ 2 * v1 -
              (2560 : F) * t0 * u1 - (3072 : F) * v1 ^ 2) *
            ((32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2) +
          ((140 : F) * t0 ^ 3 - (336 : F) * t0 * v1 +
              (224 : F) * u1) *
            (-(512 : F) * s1 * t0 + (480 : F) * t0 * v1 -
              (640 : F) * u1 + (512 : F) * w1 +
              (100 : F) * t0 ^ 3) := by
    ring
  rw [hid]
  linear_combination hW +
    ((4096 : F) * a4 + (2304 : F) * t0 ^ 2 * v1 -
        (2560 : F) * t0 * u1 - (3072 : F) * v1 ^ 2) * hM +
    ((140 : F) * t0 ^ 3 - (336 : F) * t0 * v1 + (224 : F) * u1) * hT

set_option maxHeartbeats 8000000 in
/-- The next seventh-defect coefficient on the ninth-face jet. -/
theorem tenthFace_X_nextOrder810 (t0 v1 s1 u1 w1 a4 b62 b5 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2 = 0)
    (hT : -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 - (640 : F) * u1 +
      (512 : F) * w1 + (100 : F) * t0 ^ 3 = 0)
    (hX : (23068672 : F) * a4 * s1 * t0 -
      (36044800 : F) * a4 * t0 * v1 + (28835840 : F) * a4 * u1 -
      (14680064 : F) * a4 * w1 + (7208960 : F) * b5 * t0 ^ 2 -
      (10485760 : F) * b5 * v1 - (6848512 : F) * b62 * t0 ^ 3 +
      (17301504 : F) * b62 * t0 * v1 - (12582912 : F) * b62 * u1 -
      (6741504 : F) * s1 * t0 ^ 5 +
      (30818304 : F) * s1 * t0 ^ 3 * v1 -
      (27394048 : F) * s1 * t0 ^ 2 * u1 -
      (27394048 : F) * s1 * t0 * v1 ^ 2 +
      (23068672 : F) * s1 * u1 * v1 + (1617660 : F) * t0 ^ 7 -
      (2106720 : F) * t0 ^ 5 * v1 + (1203840 : F) * t0 ^ 4 * u1 +
      (6741504 : F) * t0 ^ 4 * w1 - (19261440 : F) * t0 ^ 3 * v1 ^ 2 +
      (38522880 : F) * t0 ^ 2 * u1 * v1 -
      (23969792 : F) * t0 ^ 2 * v1 * w1 -
      (18022400 : F) * t0 * u1 ^ 2 + (20185088 : F) * t0 * u1 * w1 +
      (25681920 : F) * t0 * v1 ^ 3 - (34242560 : F) * u1 * v1 ^ 2 +
      (10092544 : F) * v1 ^ 2 * w1 = 0) :
    tenthFace_Xred810 t0 v1 u1 a4 b62 b5 := by
  unfold tenthFace_Xred810
  have hid :
      (4177920 : F) * a4 * t0 ^ 3 - (11796480 : F) * a4 * t0 * v1 +
          (10485760 : F) * a4 * u1 + (7208960 : F) * b5 * t0 ^ 2 -
          (10485760 : F) * b5 * v1 - (6848512 : F) * b62 * t0 ^ 3 +
          (17301504 : F) * b62 * t0 * v1 - (12582912 : F) * b62 * u1 +
          (300960 : F) * t0 ^ 7 - (2675200 : F) * t0 ^ 5 * v1 +
          (4561920 : F) * t0 ^ 4 * u1 +
          (7096320 : F) * t0 ^ 3 * v1 ^ 2 -
          (15769600 : F) * t0 ^ 2 * u1 * v1 +
          (7208960 : F) * t0 * u1 ^ 2 - (5406720 : F) * t0 * v1 ^ 3 +
          (7208960 : F) * u1 * v1 ^ 2 =
        (23068672 : F) * a4 * s1 * t0 -
            (36044800 : F) * a4 * t0 * v1 +
            (28835840 : F) * a4 * u1 - (14680064 : F) * a4 * w1 +
            (7208960 : F) * b5 * t0 ^ 2 - (10485760 : F) * b5 * v1 -
            (6848512 : F) * b62 * t0 ^ 3 +
            (17301504 : F) * b62 * t0 * v1 -
            (12582912 : F) * b62 * u1 - (6741504 : F) * s1 * t0 ^ 5 +
            (30818304 : F) * s1 * t0 ^ 3 * v1 -
            (27394048 : F) * s1 * t0 ^ 2 * u1 -
            (27394048 : F) * s1 * t0 * v1 ^ 2 +
            (23068672 : F) * s1 * u1 * v1 + (1617660 : F) * t0 ^ 7 -
            (2106720 : F) * t0 ^ 5 * v1 +
            (1203840 : F) * t0 ^ 4 * u1 +
            (6741504 : F) * t0 ^ 4 * w1 -
            (19261440 : F) * t0 ^ 3 * v1 ^ 2 +
            (38522880 : F) * t0 ^ 2 * u1 * v1 -
            (23969792 : F) * t0 ^ 2 * v1 * w1 -
            (18022400 : F) * t0 * u1 ^ 2 +
            (20185088 : F) * t0 * u1 * w1 +
            (25681920 : F) * t0 * v1 ^ 3 -
            (34242560 : F) * u1 * v1 ^ 2 +
            (10092544 : F) * v1 ^ 2 * w1 +
          (-(262144 : F) * a4 * t0 - (214016 : F) * t0 ^ 3 * v1 +
              (225280 : F) * t0 ^ 2 * u1 +
              (540672 : F) * t0 * v1 ^ 2 -
              (720896 : F) * u1 * v1) *
            ((32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2) +
          ((28672 : F) * a4 - (13167 : F) * t0 ^ 4 +
              (46816 : F) * t0 ^ 2 * v1 - (39424 : F) * t0 * u1 -
              (19712 : F) * v1 ^ 2) *
            (-(512 : F) * s1 * t0 + (480 : F) * t0 * v1 -
              (640 : F) * u1 + (512 : F) * w1 +
              (100 : F) * t0 ^ 3) := by
    ring
  rw [hid]
  linear_combination hX +
    (-(262144 : F) * a4 * t0 - (214016 : F) * t0 ^ 3 * v1 +
        (225280 : F) * t0 ^ 2 * u1 + (540672 : F) * t0 * v1 ^ 2 -
        (720896 : F) * u1 * v1) * hM +
    ((28672 : F) * a4 - (13167 : F) * t0 ^ 4 +
        (46816 : F) * t0 ^ 2 * v1 - (39424 : F) * t0 * u1 -
        (19712 : F) * v1 ^ 2) * hT

/-- On the `t₀ = 0` ninth-packet component, the next fourth defect is
`40 a₄ - 32 b₆₂ + 5 v₁² = 0`. -/
theorem tenthFace_right_a4_810 (v1 a4 b62 : F)
    (hG : (2560 : F) * a4 - (2048 : F) * b62 + (320 : F) * v1 ^ 2 =
      0) :
    (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0 := by
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hid :
      (64 : F) * ((40 : F) * a4 - (32 : F) * b62 +
          (5 : F) * v1 ^ 2) =
        (2560 : F) * a4 - (2048 : F) * b62 + (320 : F) * v1 ^ 2 := by
    ring
  have : (64 : F) * ((40 : F) * a4 - (32 : F) * b62 +
      (5 : F) * v1 ^ 2) = 0 := by
    rw [hid, hG]
  exact (mul_eq_zero.mp this).resolve_left h64

/-- On the `t₀ = 0` ninth-packet component, the next fifth defect is
`16 b₅ = 5 u₁ v₁`. -/
theorem tenthFace_right_b5_810 (v1 u1 b5 : F)
    (hV : (131072 : F) * b5 - (40960 : F) * u1 * v1 = 0) :
    (16 : F) * b5 = (5 : F) * u1 * v1 := by
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have hid :
      (8192 : F) * ((16 : F) * b5 - (5 : F) * u1 * v1) =
        (131072 : F) * b5 - (40960 : F) * u1 * v1 := by
    ring
  have : (8192 : F) * ((16 : F) * b5 - (5 : F) * u1 * v1) = 0 := by
    rw [hid, hV]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h8192)

/-- On the `t₀ = 0` ninth-packet component, the next fourth and sixth
defects force `16 b₆₂ v₁ + 10 u₁² - 5 v₁³ = 0`. -/
theorem tenthFace_right_sixth_810 (v1 u1 a4 b62 : F)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hW : (81920 : F) * a4 * v1 - (98304 : F) * b62 * v1 -
      (20480 : F) * u1 ^ 2 + (20480 : F) * v1 ^ 3 = 0) :
    (16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 - (5 : F) * v1 ^ 3 =
      0 := by
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hid :
      -(2048 : F) * ((16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 -
          (5 : F) * v1 ^ 3) =
        (81920 : F) * a4 * v1 - (98304 : F) * b62 * v1 -
            (20480 : F) * u1 ^ 2 + (20480 : F) * v1 ^ 3 -
          (2048 : F) * v1 *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) := by
    ring
  have hcomb :
      -(2048 : F) * ((16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 -
          (5 : F) * v1 ^ 3) = 0 := by
    rw [hid]
    linear_combination hW - (2048 : F) * v1 * hG
  have : (2048 : F) * ((16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 -
      (5 : F) * v1 ^ 3) = 0 := by
    linear_combination -hcomb
  exact (mul_eq_zero.mp this).resolve_left h2048

/-- On the `t₀ = 0` ninth-packet component, the next fourth, fifth, and
seventh defects force the alternative `u₁ (5 v₁² - 8 b₆₂) = 0`. -/
theorem tenthFace_right_seventh_810 (v1 u1 a4 b62 b5 : F)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hV : (16 : F) * b5 = (5 : F) * u1 * v1)
    (hX : (10485760 : F) * a4 * u1 - (10485760 : F) * b5 * v1 -
      (12582912 : F) * b62 * u1 + (7208960 : F) * u1 * v1 ^ 2 = 0) :
    u1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62) = 0 := by
  have h524288 : (524288 : F) ≠ 0 := by norm_num
  have hVrel : (16 : F) * b5 - (5 : F) * u1 * v1 = 0 := by
    linear_combination hV
  have hid :
      (524288 : F) * (u1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62)) =
        (10485760 : F) * a4 * u1 - (10485760 : F) * b5 * v1 -
            (12582912 : F) * b62 * u1 +
            (7208960 : F) * u1 * v1 ^ 2 -
          (262144 : F) * u1 *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) +
          (655360 : F) * v1 *
            ((16 : F) * b5 - (5 : F) * u1 * v1) := by
    ring
  have hcomb :
      (524288 : F) * (u1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62)) =
        0 := by
    rw [hid]
    linear_combination hX - (262144 : F) * u1 * hG +
      (655360 : F) * v1 * hVrel
  exact (mul_eq_zero.mp hcomb).resolve_left h524288

end TenthFaceScalars810

/-! ## Source-facing tenth-face packet -/

section NonzeroTenthFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local tenth-face packet: the ninth-face split together with
the fourth- through seventh-defect refinements of both components. -/
theorem nonzeroFace810_linearRoot_tenthInitialPacket
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
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7) ∨
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
            h0 ^ 6 ∣ q.coeff 8)) := by
  obtain ⟨delta, hGrel⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eta, hXrel⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, ht0, hv0, hu0, hs0, hw0,
    hv1, hs1, hu1, hw1, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_ninthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨b62, hb62⟩ := hq6_2
  have hGsubst :
      localClearedFourthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (h0 ^ 5 * s0) (h0 ^ 3 * w0)
          (h0 ^ 2 * b62) lambda =
        localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0, hb62]
  have hVsubst :
      localClearedFifthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (p.coeff 3) (h0 ^ 5 * s0) (h0 ^ 3 * w0)
          (h0 ^ 2 * b62) (q.coeff 5) lambda =
        localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0, hb62]
  have hWsubst :
      localClearedSixthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (p.coeff 3) (p.coeff 2) (h0 ^ 5 * s0)
          (h0 ^ 3 * w0) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
          lambda =
        localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0, hb62]
  have hXsubst :
      localClearedSeventhDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (h0 ^ 5 * s0) (h0 ^ 3 * w0) (h0 ^ 2 * b62) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda =
        localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0, hb62]
  have hGparen :
      fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
          (h0 ^ 2 * b62) lambda =
        Polynomial.C delta * h0 ^ 6 :=
    fourthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (h0 ^ 2 * b62) lambda delta hh0 (hGsubst.trans hGrel)
  have hVparen :
      fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (h0 ^ 2 * b62) (q.coeff 5) lambda =
        Polynomial.C eps * h0 ^ 7 :=
    fifthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda eps hh0
      (hVsubst.trans hVrel)
  have hWparen :
      sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 9 :=
    sixthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (p.coeff 2) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      lambda zeta hh0 (hWsubst.trans hWrel)
  have hXparen :
      seventhJetParen810 h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (h0 ^ 2 * b62) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda =
        Polynomial.C eta * h0 ^ 10 :=
    seventhJetParen810_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (p.coeff 2) (p.coeff 1) (h0 ^ 2 * b62) (q.coeff 5)
      (q.coeff 4) (q.coeff 3) lambda eta hh0 (hXsubst.trans hXrel)
  have hGleft :
      fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
          (h0 ^ 2 * b62) lambda =
        h0 ^ 2 * fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
          (p.coeff 4) b62 lambda := by
    simpa [hv1, hs1, hw1, hu1] using
      fourthJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4) b62
        lambda
  have hVleft :
      fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (h0 ^ 2 * b62) (q.coeff 5) lambda =
        h0 ^ 2 * fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
          (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda := by
    simpa [hv1, hs1, hw1, hu1] using
      fifthJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4)
        (p.coeff 3) b62 (q.coeff 5) lambda
  have hWleft :
      sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) lambda =
        h0 ^ 3 * sixthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
          (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 (q.coeff 5)
          (q.coeff 4) lambda := by
    simpa [hv1, hs1, hw1, hu1] using
      sixthJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4)
        (p.coeff 3) (p.coeff 2) b62 (q.coeff 5) (q.coeff 4) lambda
  have hXleft :
      seventhJetParen810 h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (h0 ^ 2 * b62) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda =
        h0 ^ 3 * seventhJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda := by
    simpa [hv1, hs1, hw1, hu1] using
      seventhJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4)
        (p.coeff 3) (p.coeff 2) (p.coeff 1) b62 (q.coeff 5)
        (q.coeff 4) (q.coeff 3) lambda
  have hGcof :
      fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4) b62
          lambda =
        Polynomial.C delta * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    have hscale : Polynomial.C delta * h0 ^ 6 =
        h0 ^ 2 * (Polynomial.C delta * h0 ^ 4) := by ring
    rw [← hGleft, hGparen, hscale]
  have hVcof :
      fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4)
          (p.coeff 3) b62 (q.coeff 5) lambda =
        Polynomial.C eps * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    have hscale : Polynomial.C eps * h0 ^ 7 =
        h0 ^ 2 * (Polynomial.C eps * h0 ^ 5) := by ring
    rw [← hVleft, hVparen, hscale]
  have hWcof :
      sixthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) b62 (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    have hscale : Polynomial.C zeta * h0 ^ 9 =
        h0 ^ 3 * (Polynomial.C zeta * h0 ^ 6) := by ring
    rw [← hWleft, hWparen, hscale]
  have hXcof :
      seventhJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda =
        Polynomial.C eta * h0 ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    have hscale : Polynomial.C eta * h0 ^ 10 =
        h0 ^ 3 * (Polynomial.C eta * h0 ^ 7) := by ring
    rw [← hXleft, hXparen, hscale]
  have hG1 :
      -(2560 : k) * (p.coeff 4).eval a + (2048 : k) * b62.eval a +
          (1792 : k) * s1.eval a * (t0.eval a) ^ 2 -
          (2048 : k) * s1.eval a * v1.eval a -
          (385 : k) * (t0.eval a) ^ 4 -
          (1120 : k) * (t0.eval a) ^ 2 * v1.eval a +
          (1600 : k) * t0.eval a * u1.eval a -
          (1792 : k) * t0.eval a * w1.eval a +
          (2240 : k) * (v1.eval a) ^ 2 = 0 := by
    have hleft :=
      eval_fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
        (p.coeff 4) b62 lambda a hroot
    have hzero :
        Polynomial.eval a
            (fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) b62 lambda) = 0 := by
      rw [hGcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hV1 :
      (81920 : k) * (p.coeff 4).eval a * t0.eval a +
          (131072 : k) * (q.coeff 5).eval a -
          (98304 : k) * b62.eval a * t0.eval a -
          (93184 : k) * s1.eval a * (t0.eval a) ^ 3 +
          (212992 : k) * s1.eval a * t0.eval a * v1.eval a -
          (131072 : k) * s1.eval a * u1.eval a +
          (21112 : k) * (t0.eval a) ^ 5 +
          (29120 : k) * (t0.eval a) ^ 3 * v1.eval a -
          (49920 : k) * (t0.eval a) ^ 2 * u1.eval a +
          (93184 : k) * (t0.eval a) ^ 2 * w1.eval a -
          (199680 : k) * t0.eval a * (v1.eval a) ^ 2 +
          (266240 : k) * u1.eval a * v1.eval a -
          (114688 : k) * v1.eval a * w1.eval a = 0 := by
    have hleft :=
      eval_fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4)
        (p.coeff 3) b62 (q.coeff 5) lambda a hroot
    have hzero :
        Polynomial.eval a
            (fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda) = 0 := by
      rw [hVcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hW1 :
      -(131072 : k) * (p.coeff 4).eval a * s1.eval a -
          (30720 : k) * (p.coeff 4).eval a * (t0.eval a) ^ 2 +
          (245760 : k) * (p.coeff 4).eval a * v1.eval a -
          (81920 : k) * (q.coeff 5).eval a * t0.eval a +
          (73728 : k) * b62.eval a * (t0.eval a) ^ 2 -
          (98304 : k) * b62.eval a * v1.eval a +
          (71680 : k) * s1.eval a * (t0.eval a) ^ 4 -
          (245760 : k) * s1.eval a * (t0.eval a) ^ 2 * v1.eval a +
          (196608 : k) * s1.eval a * t0.eval a * u1.eval a +
          (98304 : k) * s1.eval a * (v1.eval a) ^ 2 -
          (16800 : k) * (t0.eval a) ^ 6 +
          (12800 : k) * (t0.eval a) ^ 3 * u1.eval a -
          (71680 : k) * (t0.eval a) ^ 3 * w1.eval a +
          (192000 : k) * (t0.eval a) ^ 2 * (v1.eval a) ^ 2 -
          (337920 : k) * t0.eval a * u1.eval a * v1.eval a +
          (172032 : k) * t0.eval a * v1.eval a * w1.eval a +
          (122880 : k) * (u1.eval a) ^ 2 -
          (114688 : k) * u1.eval a * w1.eval a -
          (102400 : k) * (v1.eval a) ^ 3 = 0 := by
    have hleft :=
      eval_sixthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4)
        (p.coeff 3) (p.coeff 2) b62 (q.coeff 5) (q.coeff 4) lambda a
        hroot
    have hzero :
        Polynomial.eval a
            (sixthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) (p.coeff 3) (p.coeff 2) b62 (q.coeff 5)
              (q.coeff 4) lambda) = 0 := by
      rw [hWcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  have hX1 :
      (23068672 : k) * (p.coeff 4).eval a * s1.eval a * t0.eval a -
          (36044800 : k) * (p.coeff 4).eval a * t0.eval a *
            v1.eval a +
          (28835840 : k) * (p.coeff 4).eval a * u1.eval a -
          (14680064 : k) * (p.coeff 4).eval a * w1.eval a +
          (7208960 : k) * (q.coeff 5).eval a * (t0.eval a) ^ 2 -
          (10485760 : k) * (q.coeff 5).eval a * v1.eval a -
          (6848512 : k) * b62.eval a * (t0.eval a) ^ 3 +
          (17301504 : k) * b62.eval a * t0.eval a * v1.eval a -
          (12582912 : k) * b62.eval a * u1.eval a -
          (6741504 : k) * s1.eval a * (t0.eval a) ^ 5 +
          (30818304 : k) * s1.eval a * (t0.eval a) ^ 3 * v1.eval a -
          (27394048 : k) * s1.eval a * (t0.eval a) ^ 2 * u1.eval a -
          (27394048 : k) * s1.eval a * t0.eval a * (v1.eval a) ^ 2 +
          (23068672 : k) * s1.eval a * u1.eval a * v1.eval a +
          (1617660 : k) * (t0.eval a) ^ 7 -
          (2106720 : k) * (t0.eval a) ^ 5 * v1.eval a +
          (1203840 : k) * (t0.eval a) ^ 4 * u1.eval a +
          (6741504 : k) * (t0.eval a) ^ 4 * w1.eval a -
          (19261440 : k) * (t0.eval a) ^ 3 * (v1.eval a) ^ 2 +
          (38522880 : k) * (t0.eval a) ^ 2 * u1.eval a * v1.eval a -
          (23969792 : k) * (t0.eval a) ^ 2 * v1.eval a * w1.eval a -
          (18022400 : k) * t0.eval a * (u1.eval a) ^ 2 +
          (20185088 : k) * t0.eval a * u1.eval a * w1.eval a +
          (25681920 : k) * t0.eval a * (v1.eval a) ^ 3 -
          (34242560 : k) * u1.eval a * (v1.eval a) ^ 2 +
          (10092544 : k) * (v1.eval a) ^ 2 * w1.eval a = 0 := by
    have hleft :=
      eval_seventhJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
        (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) b62
        (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda a hroot
    have hzero :
        Polynomial.eval a
            (seventhJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda) = 0 := by
      rw [hXcof]
      simp [hroot]
    rw [← hleft]
    exact hzero
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM1eq, hTred, hp6_4, hq8_6,
      hp5_2, hq7_4⟩ := hleft
    have hM1 :
        (32 : k) * s1.eval a - (40 : k) * v1.eval a -
          (5 : k) * (t0.eval a) ^ 2 = 0 := by
      linear_combination hM1eq
    have hT1 :=
      tenthFace_thirdUnreduced_810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) hM1 hTred
    have hGred :=
      tenthFace_G_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a) hM1
        hT1 hG1
    have hVred :=
      tenthFace_V_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hM1 hT1 hV1
    have hWred :=
      tenthFace_W_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hM1 hT1 hW1
    have hXred :=
      tenthFace_X_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hM1 hT1 hX1
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, ⟨b62, hb62⟩,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM1eq, hTred, hGred, hVred,
        hWred, hXred, hp6_4, hq8_6, hp5_2, hq7_4⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, hp7_7,
      hp5_2, hq7_4, hp6_4, hq8_6⟩ := hright
    have hM1 :
        (32 : k) * s1.eval a - (40 : k) * v1.eval a -
          (5 : k) * (t0.eval a) ^ 2 = 0 := by
      have : (32 : k) * s1.eval a - (40 : k) * v1.eval a = 0 := by
        linear_combination (8 : k) * hs1rel
      simpa [ht0z] using this
    have hT1 :
        -(512 : k) * s1.eval a * t0.eval a +
            (480 : k) * t0.eval a * v1.eval a -
            (640 : k) * u1.eval a + (512 : k) * w1.eval a +
            (100 : k) * (t0.eval a) ^ 3 = 0 := by
      have : -(640 : k) * u1.eval a + (512 : k) * w1.eval a = 0 := by
        linear_combination (128 : k) * hw1rel
      simpa [ht0z] using this
    have hGred :=
      tenthFace_G_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a) hM1
        hT1 hG1
    have hVred :=
      tenthFace_V_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hM1 hT1 hV1
    have hWred :=
      tenthFace_W_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hM1 hT1 hW1
    have hXred :=
      tenthFace_X_nextOrder810 (t0.eval a) (v1.eval a) (s1.eval a)
        (u1.eval a) (w1.eval a) ((p.coeff 4).eval a) (b62.eval a)
        ((q.coeff 5).eval a) hM1 hT1 hX1
    have hG0 :
        (2560 : k) * (p.coeff 4).eval a - (2048 : k) * b62.eval a +
          (320 : k) * (v1.eval a) ^ 2 = 0 := by
      simpa [ht0z, tenthFace_Gred810] using hGred
    have hV0 :
        (131072 : k) * (q.coeff 5).eval a -
          (40960 : k) * u1.eval a * v1.eval a = 0 := by
      simpa [ht0z, tenthFace_Vred810] using hVred
    have hW0 :
        (81920 : k) * (p.coeff 4).eval a * v1.eval a -
            (98304 : k) * b62.eval a * v1.eval a -
          (20480 : k) * (u1.eval a) ^ 2 +
          (20480 : k) * (v1.eval a) ^ 3 = 0 := by
      simpa [ht0z, tenthFace_Wred810] using hWred
    have hX0 :
        (10485760 : k) * (p.coeff 4).eval a * u1.eval a -
            (10485760 : k) * (q.coeff 5).eval a * v1.eval a -
          (12582912 : k) * b62.eval a * u1.eval a +
          (7208960 : k) * u1.eval a * (v1.eval a) ^ 2 = 0 := by
      simpa [ht0z, tenthFace_Xred810] using hXred
    have ha4 :=
      tenthFace_right_a4_810 (v1.eval a) ((p.coeff 4).eval a)
        (b62.eval a) hG0
    have hb5 :=
      tenthFace_right_b5_810 (v1.eval a) (u1.eval a)
        ((q.coeff 5).eval a) hV0
    have hWspec :=
      tenthFace_right_sixth_810 (v1.eval a) (u1.eval a)
        ((p.coeff 4).eval a) (b62.eval a) ha4 hW0
    have hXspec :=
      tenthFace_right_seventh_810 (v1.eval a) (u1.eval a)
        ((p.coeff 4).eval a) (b62.eval a) ((q.coeff 5).eval a) ha4 hb5
        hX0
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, ⟨b62, hb62⟩,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
        hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6⟩⟩

/-- Source-facing tenth-face packet of a normalized scale-two `(8,10)`
nonzero face: the ninth-face split together with the fourth- through
seventh-defect refinements of both components. -/
theorem normalized810ScaleTwo_nonzeroFace_tenthInitialPacket
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
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7) ∨
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
            h0 ^ 6 ∣ q.coeff 8)) := by
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
    nonzeroFace810_linearRoot_tenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroTenthFace810

#print axioms tenthCoefficientJacobianRow_810
#print axioms tenthFace_G_nextOrder810
#print axioms tenthFace_V_nextOrder810
#print axioms tenthFace_W_nextOrder810
#print axioms tenthFace_X_nextOrder810
#print axioms tenthFace_right_a4_810
#print axioms tenthFace_right_b5_810
#print axioms tenthFace_right_sixth_810
#print axioms tenthFace_right_seventh_810
#print axioms nonzeroFace810_linearRoot_tenthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_tenthInitialPacket

end Max11DegreeRoutes
