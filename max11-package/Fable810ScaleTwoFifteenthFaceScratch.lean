import Grok810ScaleTwoFourteenthFaceScratch

/-! # Scale-two fifteenth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the fourteenth-face packet supplies the degree-`3`
Jacobian row (without clearing the corresponding first integral) and
the live split of the thirteenth-face jet.  On the left the seventh-load
alternative `F₁ ∨ F₂` survives, together with the unsplit `F₁` sixth
product and its seventh-load multiple.  On the right, the `u₁ = 0`
sibling carries the `h²` divisibilities of `4 s₁ - 5 v₁`,
`40 a₄ - 32 b₆₂ + 5 v₁²`, and `16 b₆₂ v₁ - 5 v₁³`, while the
complementary factor carries `8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`,
`2 u₁² + v₁³ = 0`, and the unsplit product
`u₁ v₁ (8 t₁ - 3 λ) = 0` recorded as a scalar identity.

The next unused Keller coefficient is the degree-`2` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`3 U G' + 2 V F' + W E' - B U' - 2 A V' - 3 G W' = 0`.
The degree-`5` first integral remains uncleared: clearing it against
the remaining decic coordinate produces a defect larger than the
remaining exact jet.  This file isolates the degree-`2` Jacobian
identity and the strongest exact source-facing refinement of every
live fourteenth-face branch.

Both left factors survive.  On the left the fourth-defect next order
is cleared into the packet: the reduced fourth combination is `h g₁`
with `2 g₁(a) + 3 λ (7 t₀³ - 48 t₀ v₁ - 384 u₁) = 0`.  The next-order
seventh-load combination
`7707 t₀⁶ - 65136 t₀⁴ v₁ - 66048 t₀³ u₁ + 137472 t₀² v₁²
+ 294912 t₀ u₁ v₁ - 540672 u₁² - 20480 v₁³`
is recorded as a scalar identity `c₁X = 6 λ Xnext`.  On the `u₁ = 0`
sibling the fourth-defect next order ties the `h²` quotients:
`8 ρ(a) + 8 σ(a) v₁ + 63 λ t₁ v₁ - 72 λ u₂ - 70 t₁² v₁ + 80 t₁ u₂ = 0`.
On the complementary factor the fifth-defect next order lands
`32 β(a) + 63 λ v₁² = 0` in the packet.  No individual vanishing of
`v₁, u₁, a₄, t₀, t₁, p₃, q₄` is claimed, and the aligned face `N = 0`
remains open.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fifteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the fourteenth face
start at degree `2`. -/
theorem fifteenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : K)) -
      ((p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 2) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (2 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1),
        (2, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC3, hC2]
  linear_combination hcoeff

/-! ## Scalar algebra of the fourteenth-face branches -/

section FifteenthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Next-order seventh-load combination on the left ninth-face jet. -/
def fifteenthFace_leftXnext810 (t0 v1 u1 : F) : F :=
  (7707 : F) * t0 ^ 6 - (65136 : F) * t0 ^ 4 * v1 -
    (66048 : F) * t0 ^ 3 * u1 + (137472 : F) * t0 ^ 2 * v1 ^ 2 +
    (294912 : F) * t0 * u1 * v1 - (540672 : F) * u1 ^ 2 -
    (20480 : F) * v1 ^ 3

set_option maxHeartbeats 8000000 in
/-- Combining the next-order second, third, fourth, and fifth defects
on the left reduces the seventh leftover to `Xnext`. -/
theorem fifteenthFace_left_c1X_reduces810
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
    (c1X : F)
    (hc1 : c1X =
      (720896 : F) * a4 * m1 * t0 - (210672 : F) * m1 * t0 ^ 5 +
        (963072 : F) * m1 * t0 ^ 3 * v1 -
        (856064 : F) * m1 * t0 ^ 2 * u1 -
        (856064 : F) * m1 * t0 * v1 ^ 2 +
        (720896 : F) * m1 * u1 * v1 - (114688 : F) * a4 * tau1 +
        (52668 : F) * t0 ^ 4 * tau1 -
        (187264 : F) * t0 ^ 2 * tau1 * v1 +
        (157696 : F) * t0 * tau1 * u1 + (78848 : F) * tau1 * v1 ^ 2 +
        (7704576 : F) * a4 * lambda * t0 ^ 2 -
        (6488064 : F) * a4 * lambda * v1 -
        (1698543 : F) * lambda * t0 ^ 6 +
        (9480240 : F) * lambda * t0 ^ 4 * v1 -
        (8667648 : F) * lambda * t0 ^ 3 * u1 -
        (13001472 : F) * lambda * t0 ^ 2 * v1 ^ 2 +
        (15409152 : F) * lambda * t0 * u1 * v1 -
        (3244032 : F) * lambda * u1 ^ 2 +
        (2568192 : F) * lambda * v1 ^ 3) :
    c1X = (6 : F) * lambda *
      fifteenthFace_leftXnext810 t0 v1 u1 := by
  have hid :
      (5 : F) *
            ((720896 : F) * a4 * m1 * t0 - (210672 : F) * m1 * t0 ^ 5 +
              (963072 : F) * m1 * t0 ^ 3 * v1 -
              (856064 : F) * m1 * t0 ^ 2 * u1 -
              (856064 : F) * m1 * t0 * v1 ^ 2 +
              (720896 : F) * m1 * u1 * v1 - (114688 : F) * a4 * tau1 +
              (52668 : F) * t0 ^ 4 * tau1 -
              (187264 : F) * t0 ^ 2 * tau1 * v1 +
              (157696 : F) * t0 * tau1 * u1 +
              (78848 : F) * tau1 * v1 ^ 2 +
              (7704576 : F) * a4 * lambda * t0 ^ 2 -
              (6488064 : F) * a4 * lambda * v1 -
              (1698543 : F) * lambda * t0 ^ 6 +
              (9480240 : F) * lambda * t0 ^ 4 * v1 -
              (8667648 : F) * lambda * t0 ^ 3 * u1 -
              (13001472 : F) * lambda * t0 ^ 2 * v1 ^ 2 +
              (15409152 : F) * lambda * t0 * u1 * v1 -
              (3244032 : F) * lambda * u1 ^ 2 +
              (2568192 : F) * lambda * v1 ^ 3) -
          (30 : F) * lambda *
            fifteenthFace_leftXnext810 t0 v1 u1 =
        ((3604480 : F) * a4 * t0 - (1053360 : F) * t0 ^ 5 +
              (4815360 : F) * t0 ^ 3 * v1 -
              (4280320 : F) * t0 ^ 2 * u1 -
              (4280320 : F) * t0 * v1 ^ 2 +
              (3604480 : F) * u1 * v1) *
            (m1 + (9 : F) * lambda * t0) +
          (-(143360 : F) * a4 + (65835 : F) * t0 ^ 4 -
              (234080 : F) * t0 ^ 2 * v1 + (197120 : F) * t0 * u1 +
              (98560 : F) * v1 ^ 2) *
            ((4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
              (144 : F) * lambda * v1) +
          ((2880 : F) * lambda * t0 ^ 2 -
              (4608 : F) * lambda * v1) *
            ((2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
              (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
              (320 : F) * v1 ^ 2) +
          ((360 : F) * lambda * t0 ^ 2 - (576 : F) * lambda * v1) *
            ((16384 : F) * b62 + (175 : F) * t0 ^ 4 -
              (1120 : F) * t0 ^ 2 * v1 - (17920 : F) * t0 * u1 -
              (1280 : F) * v1 ^ 2) := by
    unfold fifteenthFace_leftXnext810
    ring
  have hcomb :
      (5 : F) * c1X - (30 : F) * lambda *
          fifteenthFace_leftXnext810 t0 v1 u1 =
        0 := by
    rw [hc1, hid, hM, hT, hG, hVnext]
    ring
  have h5 : (5 : F) ≠ 0 := by norm_num
  have hscale :
      (5 : F) *
          (c1X - (6 : F) * lambda *
            fifteenthFace_leftXnext810 t0 v1 u1) =
        (5 : F) * c1X - (30 : F) * lambda *
          fifteenthFace_leftXnext810 t0 v1 u1 := by
    ring
  have hzero :
      (5 : F) *
          (c1X - (6 : F) * lambda *
            fifteenthFace_leftXnext810 t0 v1 u1) =
        0 := by
    rw [hscale, hcomb]
  have hsub :
      c1X - (6 : F) * lambda *
          fifteenthFace_leftXnext810 t0 v1 u1 =
        0 :=
    (mul_eq_zero.mp hzero).resolve_left h5
  linear_combination hsub

/-- On the `u₁ = 0` sibling, the fourth-defect next order at the root
ties the `h²` quotients `ρ` and `σ`. -/
theorem fifteenthFace_zeroU1_G_nextOrder810
    (v1 s1 t1 u2 w2 sigma rho : F) (lambda : F)
    (hs1 : (4 : F) * s1 = (5 : F) * v1)
    (hT : (32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 =
      0)
    (hQ : -(64 : F) * rho - (64 : F) * sigma * v1 -
        (1008 : F) * lambda * t1 * v1 + (576 : F) * lambda * u2 +
        (1792 : F) * s1 * t1 ^ 2 - (1120 : F) * t1 ^ 2 * v1 +
        (1600 : F) * t1 * u2 - (1792 : F) * t1 * w2 =
      0) :
    (8 : F) * rho + (8 : F) * sigma * v1 +
        (63 : F) * lambda * t1 * v1 - (72 : F) * lambda * u2 -
        (70 : F) * t1 ^ 2 * v1 + (80 : F) * t1 * u2 =
      0 := by
  have h8 : (-8 : F) ≠ 0 := by norm_num
  have hs1' : (4 : F) * s1 - (5 : F) * v1 = 0 := by
    linear_combination hs1
  have hid :
      (-8 : F) *
          ((8 : F) * rho + (8 : F) * sigma * v1 +
            (63 : F) * lambda * t1 * v1 - (72 : F) * lambda * u2 -
            (70 : F) * t1 ^ 2 * v1 + (80 : F) * t1 * u2) =
        (-(64 : F) * rho - (64 : F) * sigma * v1 -
            (1008 : F) * lambda * t1 * v1 + (576 : F) * lambda * u2 +
            (1792 : F) * s1 * t1 ^ 2 - (1120 : F) * t1 ^ 2 * v1 +
            (1600 : F) * t1 * u2 - (1792 : F) * t1 * w2) -
          (448 : F) * t1 ^ 2 * ((4 : F) * s1 - (5 : F) * v1) +
          (56 : F) * t1 *
            ((32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
              (9 : F) * lambda * v1) := by
    ring
  have hcomb :
      (-8 : F) *
          ((8 : F) * rho + (8 : F) * sigma * v1 +
            (63 : F) * lambda * t1 * v1 - (72 : F) * lambda * u2 -
            (70 : F) * t1 ^ 2 * v1 + (80 : F) * t1 * u2) =
        0 := by
    rw [hid]
    linear_combination hQ - (448 : F) * t1 ^ 2 * hs1' +
      (56 : F) * t1 * hT
  exact (mul_eq_zero.mp hcomb).resolve_left h8

/-! ## Extra-`h` factor of the complementary fifth cofactor -/

/-- Quotient of `h` in the complementary fifth cofactor after the
`σ`, `ω`, `β` substitutions. -/
def fifteenthFace_comp_Vquot810
    (h t1 v1 s1 w1 u1 sigma omega beta a4 a3 b62 : F[X])
    (lambda : F) : F[X] :=
  (8192 : F[X]) * beta - (28672 : F[X]) * v1 * omega -
    (4096 : F[X]) * sigma * u1 * h +
    (36864 : F[X]) * a4 * Polynomial.C lambda +
    (81920 : F[X]) * a4 * t1 - (98304 : F[X]) * b62 * t1 -
    (29952 : F[X]) * Polynomial.C lambda * v1 ^ 2 +
    (212992 : F[X]) * s1 * t1 * v1 - (199680 : F[X]) * t1 * v1 ^ 2 +
    (-(163840 : F[X]) * a3 -
        (59904 : F[X]) * Polynomial.C lambda * t1 * u1 -
      (49920 : F[X]) * t1 ^ 2 * u1 + (93184 : F[X]) * t1 ^ 2 * w1) *
      h +
    ((78624 : F[X]) * Polynomial.C lambda * t1 ^ 2 * v1 -
        (93184 : F[X]) * s1 * t1 ^ 3 +
      (29120 : F[X]) * t1 ^ 3 * v1) *
      h ^ 2 +
    (-(23751 : F[X]) * Polynomial.C lambda * t1 ^ 4 +
        (21112 : F[X]) * t1 ^ 5) *
      h ^ 4

set_option maxHeartbeats 8000000 in
theorem fifteenthFace_comp_Vcof_factor810
    (h t1 v1 s1 w1 u1 a4 a3 b62 b5 sigma omega beta : F[X])
    (lambda : F)
    (hsigma : (32 : F[X]) * s1 - (40 : F[X]) * v1 = h ^ 2 * sigma)
    (homega : (4 : F[X]) * w1 - (5 : F[X]) * u1 = h * omega)
    (hbeta : (16 : F[X]) * b5 - (5 : F[X]) * u1 * v1 = h * beta) :
    thirteenthFace_comp_Vcof810 h t1 v1 s1 w1 u1 a4 a3 b62 b5 lambda =
      h * fifteenthFace_comp_Vquot810 h t1 v1 s1 w1 u1 sigma omega beta
        a4 a3 b62 lambda := by
  have hid :
      thirteenthFace_comp_Vcof810 h t1 v1 s1 w1 u1 a4 a3 b62 b5
          lambda =
        -(4096 : F[X]) *
            (-(2 : F[X]) *
                ((16 : F[X]) * b5 - (5 : F[X]) * u1 * v1) +
              u1 * ((32 : F[X]) * s1 - (40 : F[X]) * v1) +
              (7 : F[X]) * v1 *
                ((4 : F[X]) * w1 - (5 : F[X]) * u1)) +
          ((36864 : F[X]) * a4 * Polynomial.C lambda +
              (81920 : F[X]) * a4 * t1 - (98304 : F[X]) * b62 * t1 -
              (29952 : F[X]) * Polynomial.C lambda * v1 ^ 2 +
              (212992 : F[X]) * s1 * t1 * v1 -
              (199680 : F[X]) * t1 * v1 ^ 2) *
            h +
          (-(163840 : F[X]) * a3 -
              (59904 : F[X]) * Polynomial.C lambda * t1 * u1 -
              (49920 : F[X]) * t1 ^ 2 * u1 +
              (93184 : F[X]) * t1 ^ 2 * w1) *
            h ^ 2 +
          ((78624 : F[X]) * Polynomial.C lambda * t1 ^ 2 * v1 -
              (93184 : F[X]) * s1 * t1 ^ 3 +
              (29120 : F[X]) * t1 ^ 3 * v1) *
            h ^ 3 +
          (-(23751 : F[X]) * Polynomial.C lambda * t1 ^ 4 +
              (21112 : F[X]) * t1 ^ 5) *
            h ^ 5 := by
    simp only [thirteenthFace_comp_Vcof810]
    ring
  rw [hid, hsigma, homega, hbeta]
  simp only [fifteenthFace_comp_Vquot810]
  ring

end FifteenthFaceScalars810

/-! ## Source-facing fifteenth-face packet -/

section NonzeroFifteenthFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local fifteenth-face packet: the fourteenth-face split together
with the source-facing refinement of every live branch. -/
theorem nonzeroFace810_linearRoot_fifteenthInitialPacket
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
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
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
                      0 ∧
                    (8 : k) * rho.eval a +
                        (8 : k) * sigma.eval a * v1.eval a +
                        (63 : k) * lambda * t1.eval a * v1.eval a -
                        (72 : k) * lambda * u2.eval a -
                        (70 : k) * (t1.eval a) ^ 2 * v1.eval a +
                      (80 : k) * t1.eval a * u2.eval a = 0) ∨
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
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (32 : k) * beta.eval a +
                      (63 : k) * lambda * (v1.eval a) ^ 2 =
                      0)))) := by
  obtain ⟨delta, hGrel⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_fourteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred, hWred,
      hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt, ⟨m1, tau1, hm1, htau1, hM1,
        hT1⟩, hF1w⟩ := hleft
    have hGredEval :
        ((2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
            (35 : k[X]) * t0 ^ 4 - (240 : k[X]) * t0 ^ 2 * v1 +
            (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2).eval a =
          0 := by
      have hG' := hGred
      simp only [tenthFace_Gred810] at hG'
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
      linear_combination hG'
    obtain ⟨g1, hg1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        ((2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
          (35 : k[X]) * t0 ^ 4 - (240 : k[X]) * t0 ^ 2 * v1 +
          (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2)
        a hh0degree hroot hGredEval
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
    have hGninth :
        fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
            (h0 ^ 2 * b62) lambda =
          h0 ^ 2 *
            fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) b62 lambda := by
      simpa [hv1, hs1, hu1, hw1] using
        fourthJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4)
          b62 lambda
    have hNinthPow :
        fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
            (p.coeff 4) b62 lambda =
          Polynomial.C delta * h0 ^ 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
      have hscale : Polynomial.C delta * h0 ^ 6 =
          h0 ^ 2 * (Polynomial.C delta * h0 ^ 4) := by ring
      rw [← hGninth, hGparen, hscale]
    have hid0 :
        fourthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) b62 lambda +
            ((2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
              (35 : k[X]) * t0 ^ 4 - (240 : k[X]) * t0 ^ 2 * v1 +
              (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2) =
          ((56 : k[X]) * t0 ^ 2 - (64 : k[X]) * v1) *
              ((32 : k[X]) * s1 - (40 : k[X]) * v1 -
                (5 : k[X]) * t0 ^ 2) -
            (14 : k[X]) * t0 *
              ((128 : k[X]) * w1 - (160 : k[X]) * u1 -
                (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3) +
            h0 *
              ((462 : k[X]) * Polynomial.C lambda * t0 ^ 3 -
                (1008 : k[X]) * Polynomial.C lambda * t0 * v1 +
                (576 : k[X]) * Polynomial.C lambda * u1) := by
      simp only [fourthJetParen810_ninthCofactor]
      ring
    rw [hm1, htau1, hg1] at hid0
    have hquotPow :
        ((56 : k[X]) * t0 ^ 2 - (64 : k[X]) * v1) * m1 -
            (14 : k[X]) * t0 * tau1 +
            ((462 : k[X]) * Polynomial.C lambda * t0 ^ 3 -
              (1008 : k[X]) * Polynomial.C lambda * t0 * v1 +
              (576 : k[X]) * Polynomial.C lambda * u1) - g1 =
          Polynomial.C delta * h0 ^ 3 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C delta * h0 ^ 4 =
          h0 * (Polynomial.C delta * h0 ^ 3) := by ring
      rw [← hscale, ← hNinthPow]
      linear_combination -hid0
    have hqe := congrArg (fun r : k[X] => Polynomial.eval a r) hquotPow
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C, hroot] at hqe
    have hGform :
        (2 : k) * g1.eval a -
            ((112 : k) * (t0.eval a) ^ 2 -
              (128 : k) * v1.eval a) * m1.eval a +
            (28 : k) * t0.eval a * tau1.eval a -
          ((924 : k) * lambda * (t0.eval a) ^ 3 -
            (2016 : k) * lambda * t0.eval a * v1.eval a +
            (1152 : k) * lambda * u1.eval a) = 0 := by
      linear_combination (-2 : k) * hqe
    have hg1next :
        (2 : k) * g1.eval a +
            (3 : k) * lambda *
              ((7 : k) * (t0.eval a) ^ 3 -
                (48 : k) * t0.eval a * v1.eval a -
                (384 : k) * u1.eval a) = 0 := by
      have hred := thirteenthFace_left_G_nextOrder810 (t0.eval a)
        (v1.eval a) (u1.eval a) (m1.eval a) (tau1.eval a)
        (g1.eval a) lambda hM1 hT1 hGform
      simp only [thirteenthFace_leftGnext810] at hred
      linear_combination hred
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred,
        hWred, hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt,
        ⟨m1, tau1, hm1, htau1, hM1, hT1⟩, ⟨g1, hg1, hg1next⟩, hF1w⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
      hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, hright'⟩ :=
      hright
    refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
        hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, ?_⟩⟩
    rcases hright' with hu1z | hcomp
    · obtain ⟨hu1z, t1, u2, w2, b51, sigma, rho, pi, ht1, hu2, hw2,
        hb51, hsigmapoly, hrhopoly, hpipoly, hp5_3, hq7_5, hq5d,
        hsigmadvd, hrhovd, hpivd, hTform, hVform, hprod⟩ := hu1z
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
      have hGrew :
          thirteenthFace_zeroU1_Gcof810 h0 t1 v1 s1 w2 u2 (p.coeff 4)
              b62 lambda =
            h0 ^ 2 *
              (-(64 : k[X]) * rho +
                (-(64 : k[X]) * sigma * v1 -
                  (1008 : k[X]) * Polynomial.C lambda * t1 * v1 +
                  (576 : k[X]) * Polynomial.C lambda * u2 +
                  (1792 : k[X]) * s1 * t1 ^ 2 -
                  (1120 : k[X]) * t1 ^ 2 * v1 +
                  (1600 : k[X]) * t1 * u2 -
                  (1792 : k[X]) * t1 * w2 +
                  ((462 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
                      (385 : k[X]) * t1 ^ 4) *
                    h0 ^ 2)) := by
        rw [hGfact, hrhopoly]
        ring
      have hquotPow :
          -(64 : k[X]) * rho +
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
            Polynomial.C delta * h0 ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
        have hscale : Polynomial.C delta * h0 ^ 4 =
            h0 ^ 2 * (Polynomial.C delta * h0 ^ 2) := by ring
        rw [← hGrew, hGcof, hscale]
      have hqe := congrArg (fun r : k[X] => Polynomial.eval a r)
        hquotPow
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_pow,
        Polynomial.eval_ofNat, Polynomial.eval_C, hroot] at hqe
      have hGnextRel :
          (8 : k) * rho.eval a +
              (8 : k) * sigma.eval a * v1.eval a +
              (63 : k) * lambda * t1.eval a * v1.eval a -
              (72 : k) * lambda * u2.eval a -
              (70 : k) * (t1.eval a) ^ 2 * v1.eval a +
            (80 : k) * t1.eval a * u2.eval a = 0 :=
        fifteenthFace_zeroU1_G_nextOrder810 (v1.eval a) (s1.eval a)
          (t1.eval a) (u2.eval a) (w2.eval a) (sigma.eval a)
          (rho.eval a) lambda hs1rel hTform
          (by linear_combination hqe)
      exact Or.inl ⟨hu1z, t1, u2, w2, b51, sigma, rho, pi, ht1, hu2,
        hw2, hb51, hsigmapoly, hrhopoly, hpipoly, hp5_3, hq7_5, hq5d,
        hsigmadvd, hrhovd, hpivd, hTform, hVform, hprod, hGnextRel⟩
    · obtain ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1, homega,
        hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform⟩ := hcomp
      have hVsubst :
          localClearedFifthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (p.coeff 4) (p.coeff 3) (h0 ^ 5 * s0)
              (h0 ^ 3 * w0) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0, hb62]
      have hVparen :
          fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            Polynomial.C eps * h0 ^ 7 :=
        fifthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0
          (p.coeff 4) (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda
          eps hh0 (hVsubst.trans hVrel)
      have hVleft :
          fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            h0 ^ 2 *
              thirteenthFace_comp_Vcof810 h0 t1 v1 s1 w1 u1
                (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda := by
        simpa [ht1, hv1, hs1, hw1, hu1] using
          thirteenthFace_fifth_comp_mul_h h0 t1 v1 s1 w1 u1
            (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda
      have hVcof :
          thirteenthFace_comp_Vcof810 h0 t1 v1 s1 w1 u1 (p.coeff 4)
              (p.coeff 3) b62 (q.coeff 5) lambda =
            Polynomial.C eps * h0 ^ 5 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
        have hscale : Polynomial.C eps * h0 ^ 7 =
            h0 ^ 2 * (Polynomial.C eps * h0 ^ 5) := by ring
        rw [← hVleft, hVparen, hscale]
      have hVfact :=
        fifteenthFace_comp_Vcof_factor810 h0 t1 v1 s1 w1 u1
          (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) sigma omega beta
          lambda hsigmapoly homega hbeta
      have hQpow :
          fifteenthFace_comp_Vquot810 h0 t1 v1 s1 w1 u1 sigma omega
              beta (p.coeff 4) (p.coeff 3) b62 lambda =
            Polynomial.C eps * h0 ^ 4 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C eps * h0 ^ 5 =
            h0 * (Polynomial.C eps * h0 ^ 4) := by ring
        rw [← hVfact, hVcof, hscale]
      have hqe := congrArg (fun r : k[X] => Polynomial.eval a r) hQpow
      simp only [fifteenthFace_comp_Vquot810, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
        Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_C,
        hroot] at hqe
      have hVs1form :
          (8192 : k) * beta.eval a -
              (28672 : k) * omega.eval a * v1.eval a +
              (36864 : k) * (p.coeff 4).eval a * lambda +
              (81920 : k) * (p.coeff 4).eval a * t1.eval a -
              (98304 : k) * b62.eval a * t1.eval a -
              (29952 : k) * lambda * (v1.eval a) ^ 2 +
              (212992 : k) * s1.eval a * t1.eval a * v1.eval a -
            (199680 : k) * t1.eval a * (v1.eval a) ^ 2 = 0 := by
        linear_combination hqe
      have hVstd :=
        thirteenthFace_comp_V_s1_810 (v1.eval a) (s1.eval a)
          ((p.coeff 4).eval a) (b62.eval a) (t1.eval a)
          (omega.eval a) (beta.eval a) lambda hs1rel hVs1form
      have hVnextRel :
          (32 : k) * beta.eval a +
              (63 : k) * lambda * (v1.eval a) ^ 2 = 0 :=
        thirteenthFace_comp_V_nextOrder810 (v1.eval a) (u1.eval a)
          ((p.coeff 4).eval a) (b62.eval a) ((q.coeff 5).eval a)
          (t1.eval a) (omega.eval a) (beta.eval a) lambda ha4c hB
          hTform hVstd
      exact Or.inr ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1,
        homega, hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform,
        hVnextRel⟩

/-- Source-facing fifteenth-face packet of a normalized scale-two `(8,10)`
nonzero face: the fourteenth-face split together with the next-order
fourth/fifth/seventh refinements of every live branch. -/
theorem normalized810ScaleTwo_nonzeroFace_fifteenthInitialPacket
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
            (∃ g1 : K[X],
              (2560 : K[X]) * (p.coeff 4) - (2048 : K[X]) * b62 +
                    (35 : K[X]) * t0 ^ 4 -
                    (240 : K[X]) * t0 ^ 2 * v1 +
                    (640 : K[X]) * t0 * u1 + (320 : K[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : K) * g1.eval a +
                    (3 : K) * lambda *
                      ((7 : K) * (t0.eval a) ^ 3 -
                        (48 : K) * t0.eval a * v1.eval a -
                        (384 : K) * u1.eval a) = 0) ∧
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
                      0 ∧
                    (8 : K) * rho.eval a +
                        (8 : K) * sigma.eval a * v1.eval a +
                        (63 : K) * lambda * t1.eval a * v1.eval a -
                        (72 : K) * lambda * u2.eval a -
                        (70 : K) * (t1.eval a) ^ 2 * v1.eval a +
                      (80 : K) * t1.eval a * u2.eval a = 0) ∨
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
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (32 : K) * beta.eval a +
                      (63 : K) * lambda * (v1.eval a) ^ 2 =
                      0)))) := by
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
    nonzeroFace810_linearRoot_fifteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroFifteenthFace810

#print axioms fifteenthCoefficientJacobianRow_810
#print axioms fifteenthFace_left_c1X_reduces810
#print axioms fifteenthFace_zeroU1_G_nextOrder810
#print axioms fifteenthFace_comp_Vcof_factor810
#print axioms nonzeroFace810_linearRoot_fifteenthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_fifteenthInitialPacket

end Max11DegreeRoutes
