import Fable810ScaleTwoFifteenthFaceScratch

/-! # Scale-two sixteenth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the fifteenth-face packet supplies the degree-`2`
Jacobian row (without clearing the corresponding first integral) and
the live split of the fourteenth-face jet.  On the left the seventh-load
alternative `F₁ ∨ F₂` survives, together with the unsplit `F₁` sixth
product, its seventh-load multiple, and the fourth-defect witness `g₁`
with `2 g₁(a) + 3 λ (7 t₀³ - 48 t₀ v₁ - 384 u₁) = 0`.  On the right,
the `u₁ = 0` sibling carries the `h²` quotients `σ`, `ρ`, `π` and the
fourth-defect tie `8 ρ(a) + 8 σ(a) v₁ + 63 λ t₁ v₁ - 72 λ u₂
- 70 t₁² v₁ + 80 t₁ u₂ = 0`, while the complementary factor carries
`8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`, `2 u₁² + v₁³ = 0`, the unsplit
product `u₁ v₁ (8 t₁ - 3 λ) = 0`, and the fifth-defect law
`32 β(a) + 63 λ v₁² = 0`.

The next unused Keller coefficient is the degree-`1` Jacobian row.
After the same octic depression that kills `z⁷`, that row is
`2 V G' + W F' - A V' - 2 G W' = 0`.
The degree-`5` first integral remains uncleared: clearing it against
the remaining decic coordinate produces a defect larger than the
remaining exact jet.  This file isolates the degree-`1` Jacobian
identity and the strongest exact source-facing refinement of every
live fifteenth-face branch.

Both left factors survive.  On the left the fifth-defect next order is
cleared into the packet: the reduced fifth combination is `h k₁` with
`k₁(a) + 9 λ (4096 a₄ + 91 t₀⁴ - 608 t₀² v₁ - 2560 t₀ u₁ + 256 v₁²)
= 0`.  On the `u₁ = 0` sibling the fifth-defect next order peels the
`h` head of the ninth cofactor: the head is `h k_z` with
`k_z(a) = 163840 p₃(a)`, tying the sibling to the octic coefficient
`p₃`.  On the complementary factor the fourth-defect next order lands
the `h` quotient `ρ_c` of `40 a₄ - 32 b₆₂ + 5 v₁²` in the packet with
`ρ_c(a) + 10 t₁(a) u₁(a) - 9 λ u₁(a) = 0`.  The terminal degree-`0`
row `W G' - G W'` carries the Keller constant and ends the coefficient
tower.  No individual vanishing of `v₁, u₁, a₄, t₀, t₁, p₃, q₄` is
claimed, and the aligned face `N = 0` remains open.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The sixteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the fifteenth face
start at degree `1`. -/
theorem sixteenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
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

/-! ## Scalar algebra of the fifteenth-face branches -/

section SixteenthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- On the left ninth-face jet, the peeled fifth-defect quotient obeys
an exact next-order law once the `m₁`/`τ₁` next orders are known. -/
theorem sixteenthFace_left_V_nextOrder810
    (t0 v1 u1 a4 m1 tau1 k1 : F) (lambda : F)
    (hM : m1 + (9 : F) * lambda * t0 = 0)
    (hT : (4 : F) * tau1 + (9 : F) * lambda * t0 ^ 2 +
      (144 : F) * lambda * v1 = 0)
    (hform : k1 +
        (-(2912 : F) * t0 ^ 3 + (6656 : F) * t0 * v1 -
            (4096 : F) * u1) * m1 +
        ((728 : F) * t0 ^ 2 - (896 : F) * v1) * tau1 +
        (36864 : F) * lambda * a4 - (23751 : F) * lambda * t0 ^ 4 +
        (78624 : F) * lambda * t0 ^ 2 * v1 -
        (59904 : F) * lambda * t0 * u1 -
        (29952 : F) * lambda * v1 ^ 2 = 0) :
    k1 + (9 : F) * lambda *
        ((4096 : F) * a4 + (91 : F) * t0 ^ 4 -
          (608 : F) * t0 ^ 2 * v1 - (2560 : F) * t0 * u1 +
          (256 : F) * v1 ^ 2) =
      0 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hcomb :
      (4 : F) *
          (k1 + (9 : F) * lambda *
            ((4096 : F) * a4 + (91 : F) * t0 ^ 4 -
              (608 : F) * t0 ^ 2 * v1 - (2560 : F) * t0 * u1 +
              (256 : F) * v1 ^ 2)) =
        0 := by
    linear_combination (4 : F) * hform -
      (4 : F) *
        (-(2912 : F) * t0 ^ 3 + (6656 : F) * t0 * v1 -
          (4096 : F) * u1) * hM -
      ((728 : F) * t0 ^ 2 - (896 : F) * v1) * hT
  exact (mul_eq_zero.mp hcomb).resolve_left h4

/-- On the `u₁ = 0` sibling, the `h` head of the fifth-defect ninth
cofactor vanishes at the root. -/
theorem sixteenthFace_zeroU1_Vhead_eval810
    (v1 s1 t1 u2 w2 b51 a4 b62 : F) (lambda : F)
    (hs1 : (4 : F) * s1 = (5 : F) * v1)
    (ha4 : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hT : (32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 = 0)
    (hV : (2560 : F) * b51 + (576 : F) * lambda * b62 -
        (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
        (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1 = 0) :
    (81920 : F) * a4 * t1 + (131072 : F) * b51 -
        (98304 : F) * b62 * t1 + (212992 : F) * s1 * t1 * v1 -
        (131072 : F) * s1 * u2 - (199680 : F) * t1 * v1 ^ 2 +
        (266240 : F) * u2 * v1 - (114688 : F) * v1 * w2 +
        (36864 : F) * lambda * a4 - (29952 : F) * lambda * v1 ^ 2 =
      0 := by
  have h5 : (5 : F) ≠ 0 := by norm_num
  have hcomb :
      (5 : F) *
          ((81920 : F) * a4 * t1 + (131072 : F) * b51 -
            (98304 : F) * b62 * t1 + (212992 : F) * s1 * t1 * v1 -
            (131072 : F) * s1 * u2 - (199680 : F) * t1 * v1 ^ 2 +
            (266240 : F) * u2 * v1 - (114688 : F) * v1 * w2 +
            (36864 : F) * lambda * a4 -
            (29952 : F) * lambda * v1 ^ 2) =
        0 := by
    linear_combination ((10240 : F) * t1 + (4608 : F) * lambda) * ha4 +
      ((266240 : F) * t1 * v1 - (163840 : F) * u2) * hs1 -
      (17920 : F) * v1 * hT + (256 : F) * hV
  exact (mul_eq_zero.mp hcomb).resolve_left h5

/-- On the complementary factor, the peeled fourth-defect quotient obeys
an exact next-order law once `4 w₁ = 5 u₁` is known. -/
theorem sixteenthFace_comp_G_nextOrder810
    (u1 w1 t1 rhoc : F) (lambda : F)
    (hw : (4 : F) * w1 = (5 : F) * u1)
    (hform : -(64 : F) * rhoc + (1600 : F) * t1 * u1 -
        (1792 : F) * t1 * w1 + (576 : F) * lambda * u1 = 0) :
    rhoc + (10 : F) * t1 * u1 - (9 : F) * lambda * u1 = 0 := by
  have h64 : (-64 : F) ≠ 0 := by norm_num
  have hcomb :
      (-64 : F) *
          (rhoc + (10 : F) * t1 * u1 - (9 : F) * lambda * u1) =
        0 := by
    linear_combination hform + (448 : F) * t1 * hw
  exact (mul_eq_zero.mp hcomb).resolve_left h64

set_option maxHeartbeats 8000000 in
/-- Extra `h` factor of the fifth-defect ninth cofactor on the
`u₁ = 0` sibling after `t₀ = h t₁`, `u₁ = h u₂`, `w₁ = h w₂`,
`b₅ = h b₅₁`. -/
theorem sixteenthFace_fifth_zeroU1_mul_h
    (h t1 v1 s1 w2 u2 a4 a3 b62 b51 : F[X]) (lambda : F) :
    fifthJetParen810_ninthCofactor h (h * t1) v1 s1 (h * w2) (h * u2)
        a4 a3 b62 (h * b51) lambda =
      h * ((81920 : F[X]) * a4 * t1 + (131072 : F[X]) * b51 -
          (98304 : F[X]) * b62 * t1 + (212992 : F[X]) * s1 * t1 * v1 -
          (131072 : F[X]) * s1 * u2 - (199680 : F[X]) * t1 * v1 ^ 2 +
          (266240 : F[X]) * u2 * v1 - (114688 : F[X]) * v1 * w2 +
          (36864 : F[X]) * Polynomial.C lambda * a4 -
          (29952 : F[X]) * Polynomial.C lambda * v1 ^ 2 +
          h * (-(163840 : F[X]) * a3) +
          h ^ 2 *
            (-(93184 : F[X]) * s1 * t1 ^ 3 +
              (29120 : F[X]) * t1 ^ 3 * v1 -
              (49920 : F[X]) * t1 ^ 2 * u2 +
              (93184 : F[X]) * t1 ^ 2 * w2 +
              (78624 : F[X]) * Polynomial.C lambda * t1 ^ 2 * v1 -
              (59904 : F[X]) * Polynomial.C lambda * t1 * u2) +
          h ^ 4 *
            ((21112 : F[X]) * t1 ^ 5 -
              (23751 : F[X]) * Polynomial.C lambda * t1 ^ 4)) := by
  simp only [fifthJetParen810_ninthCofactor]
  ring

set_option maxHeartbeats 8000000 in
/-- Split of the fourth-defect ninth cofactor on the complementary
factor after `t₀ = h t₁`. -/
theorem sixteenthFace_fourth_comp_mul_h
    (h t1 v1 s1 w1 u1 a4 b62 : F[X]) (lambda : F) :
    fourthJetParen810_ninthCofactor h (h * t1) v1 s1 w1 u1 a4 b62
        lambda =
      -(64 : F[X]) *
          ((40 : F[X]) * a4 - (32 : F[X]) * b62 +
            (5 : F[X]) * v1 ^ 2) -
        (64 : F[X]) * v1 * ((32 : F[X]) * s1 - (40 : F[X]) * v1) +
        h * ((1600 : F[X]) * t1 * u1 - (1792 : F[X]) * t1 * w1 +
          (576 : F[X]) * Polynomial.C lambda * u1) +
        h ^ 2 *
          ((1792 : F[X]) * s1 * t1 ^ 2 - (1120 : F[X]) * t1 ^ 2 * v1 -
            (1008 : F[X]) * Polynomial.C lambda * t1 * v1) +
        h ^ 4 *
          (-(385 : F[X]) * t1 ^ 4 +
            (462 : F[X]) * Polynomial.C lambda * t1 ^ 3) := by
  simp only [fourthJetParen810_ninthCofactor]
  ring

end SixteenthFaceScalars810

/-! ## Source-facing sixteenth-face packet -/

section NonzeroSixteenthFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local sixteenth-face packet: the fifteenth-face split together
with the source-facing refinement of every live branch. -/
theorem nonzeroFace810_linearRoot_sixteenthInitialPacket
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
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1 ∧
                k1.eval a + (9 : k) * lambda *
                    ((4096 : k) * (p.coeff 4).eval a +
                      (91 : k) * (t0.eval a) ^ 4 -
                      (608 : k) * (t0.eval a) ^ 2 * v1.eval a -
                      (2560 : k) * t0.eval a * u1.eval a +
                      (256 : k) * (v1.eval a) ^ 2) = 0) ∧
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
                      (80 : k) * t1.eval a * u2.eval a = 0 ∧
                    ∃ kz : k[X],
                      (81920 : k[X]) * (p.coeff 4) * t1 +
                            (131072 : k[X]) * b51 -
                            (98304 : k[X]) * b62 * t1 +
                            (212992 : k[X]) * s1 * t1 * v1 -
                            (131072 : k[X]) * s1 * u2 -
                            (199680 : k[X]) * t1 * v1 ^ 2 +
                            (266240 : k[X]) * u2 * v1 -
                            (114688 : k[X]) * v1 * w2 +
                            (36864 : k[X]) * Polynomial.C lambda *
                              (p.coeff 4) -
                            (29952 : k[X]) * Polynomial.C lambda *
                              v1 ^ 2 =
                          h0 * kz ∧
                        kz.eval a =
                          (163840 : k) * (p.coeff 3).eval a) ∨
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
                      0 ∧
                    ∃ rhoc : k[X],
                      (40 : k[X]) * (p.coeff 4) -
                            (32 : k[X]) * b62 +
                          (5 : k[X]) * v1 ^ 2 =
                        h0 * rhoc ∧
                      rhoc.eval a +
                          (10 : k) * t1.eval a * u1.eval a -
                        (9 : k) * lambda * u1.eval a = 0)))) := by
  obtain ⟨delta, hGrel⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_fifteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred, hWred,
      hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt, ⟨m1, tau1, hm1, htau1, hM1,
        hT1⟩, ⟨g1, hg1, hg1next⟩, hF1w⟩ := hleft
    have hVredEval :
        ((81920 : k[X]) * (p.coeff 4) * t0 +
            (131072 : k[X]) * (q.coeff 5) -
            (98304 : k[X]) * b62 * t0 + (2912 : k[X]) * t0 ^ 5 -
            (20480 : k[X]) * t0 ^ 3 * v1 +
            (46080 : k[X]) * t0 ^ 2 * u1 +
            (30720 : k[X]) * t0 * v1 ^ 2 -
          (40960 : k[X]) * u1 * v1).eval a =
          0 := by
      have hV' := hVred
      simp only [tenthFace_Vred810] at hV'
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
      linear_combination hV'
    obtain ⟨k1, hk1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0
        ((81920 : k[X]) * (p.coeff 4) * t0 +
          (131072 : k[X]) * (q.coeff 5) -
          (98304 : k[X]) * b62 * t0 + (2912 : k[X]) * t0 ^ 5 -
          (20480 : k[X]) * t0 ^ 3 * v1 +
          (46080 : k[X]) * t0 ^ 2 * u1 +
          (30720 : k[X]) * t0 * v1 ^ 2 - (40960 : k[X]) * u1 * v1)
        a hh0degree hroot hVredEval
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
    have hVninth :
        fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
            (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda =
          h0 ^ 2 *
            fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda := by
      simpa [hv1, hs1, hu1, hw1] using
        fifthJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4)
          (p.coeff 3) b62 (q.coeff 5) lambda
    have hNinthPow :
        fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
            (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda =
          Polynomial.C eps * h0 ^ 5 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
      have hscale : Polynomial.C eps * h0 ^ 7 =
          h0 ^ 2 * (Polynomial.C eps * h0 ^ 5) := by ring
      rw [← hVninth, hVparen, hscale]
    have hid0 :
        fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4)
            (p.coeff 3) b62 (q.coeff 5) lambda =
          ((81920 : k[X]) * (p.coeff 4) * t0 +
              (131072 : k[X]) * (q.coeff 5) -
              (98304 : k[X]) * b62 * t0 + (2912 : k[X]) * t0 ^ 5 -
              (20480 : k[X]) * t0 ^ 3 * v1 +
              (46080 : k[X]) * t0 ^ 2 * u1 +
              (30720 : k[X]) * t0 * v1 ^ 2 -
              (40960 : k[X]) * u1 * v1) +
            (-(2912 : k[X]) * t0 ^ 3 + (6656 : k[X]) * t0 * v1 -
                (4096 : k[X]) * u1) *
              ((32 : k[X]) * s1 - (40 : k[X]) * v1 -
                (5 : k[X]) * t0 ^ 2) +
            ((728 : k[X]) * t0 ^ 2 - (896 : k[X]) * v1) *
              ((128 : k[X]) * w1 - (160 : k[X]) * u1 -
                (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3) +
            h0 *
              ((36864 : k[X]) * Polynomial.C lambda * (p.coeff 4) -
                (23751 : k[X]) * Polynomial.C lambda * t0 ^ 4 +
                (78624 : k[X]) * Polynomial.C lambda * t0 ^ 2 * v1 -
                (59904 : k[X]) * Polynomial.C lambda * t0 * u1 -
                (29952 : k[X]) * Polynomial.C lambda * v1 ^ 2) +
            h0 ^ 2 * (-(163840 : k[X]) * (p.coeff 3)) := by
      simp only [fifthJetParen810_ninthCofactor]
      ring
    rw [hk1, hm1, htau1] at hid0
    have hquotPow :
        k1 +
            (-(2912 : k[X]) * t0 ^ 3 + (6656 : k[X]) * t0 * v1 -
              (4096 : k[X]) * u1) * m1 +
            ((728 : k[X]) * t0 ^ 2 - (896 : k[X]) * v1) * tau1 +
            ((36864 : k[X]) * Polynomial.C lambda * (p.coeff 4) -
              (23751 : k[X]) * Polynomial.C lambda * t0 ^ 4 +
              (78624 : k[X]) * Polynomial.C lambda * t0 ^ 2 * v1 -
              (59904 : k[X]) * Polynomial.C lambda * t0 * u1 -
              (29952 : k[X]) * Polynomial.C lambda * v1 ^ 2) +
            h0 * (-(163840 : k[X]) * (p.coeff 3)) =
          Polynomial.C eps * h0 ^ 4 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C eps * h0 ^ 5 =
          h0 * (Polynomial.C eps * h0 ^ 4) := by ring
      rw [← hscale, ← hNinthPow]
      linear_combination -hid0
    have hqe := congrArg (fun r : k[X] => Polynomial.eval a r) hquotPow
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_C, hroot] at hqe
    have hk1next :
        k1.eval a + (9 : k) * lambda *
            ((4096 : k) * (p.coeff 4).eval a +
              (91 : k) * (t0.eval a) ^ 4 -
              (608 : k) * (t0.eval a) ^ 2 * v1.eval a -
              (2560 : k) * t0.eval a * u1.eval a +
              (256 : k) * (v1.eval a) ^ 2) = 0 :=
      sixteenthFace_left_V_nextOrder810 (t0.eval a) (v1.eval a)
        (u1.eval a) ((p.coeff 4).eval a) (m1.eval a) (tau1.eval a)
        (k1.eval a) lambda hM1 hT1 (by linear_combination hqe)
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM, hTred, hGred, hVred,
        hWred, hXred, hp6_4, hq8_6, hp5_2, hq7_4, halt,
        ⟨m1, tau1, hm1, htau1, hM1, hT1⟩, ⟨g1, hg1, hg1next⟩,
        ⟨k1, hk1, hk1next⟩, hF1w⟩⟩
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
        hsigmadvd, hrhovd, hpivd, hTform, hVform, hprod, hGnextRel⟩ :=
        hu1z
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
      have hVninth :
          fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            h0 ^ 2 *
              fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
                (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda := by
        simpa [hv1, hs1, hu1, hw1] using
          fifthJetParen810_ninth_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4)
            (p.coeff 3) b62 (q.coeff 5) lambda
      have hNinthPow :
          fifthJetParen810_ninthCofactor h0 t0 v1 s1 w1 u1
              (p.coeff 4) (p.coeff 3) b62 (q.coeff 5) lambda =
            Polynomial.C eps * h0 ^ 5 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
        have hscale : Polynomial.C eps * h0 ^ 7 =
            h0 ^ 2 * (Polynomial.C eps * h0 ^ 5) := by ring
        rw [← hVninth, hVparen, hscale]
      rw [ht1, hu2, hw2, hb51] at hNinthPow
      have hbScalar :=
        sixteenthFace_zeroU1_Vhead_eval810 (v1.eval a) (s1.eval a)
          (t1.eval a) (u2.eval a) (w2.eval a) (b51.eval a)
          ((p.coeff 4).eval a) (b62.eval a) lambda hs1rel ha4 hTform
          hVform
      have hbEval :
          ((81920 : k[X]) * (p.coeff 4) * t1 +
              (131072 : k[X]) * b51 -
              (98304 : k[X]) * b62 * t1 +
              (212992 : k[X]) * s1 * t1 * v1 -
              (131072 : k[X]) * s1 * u2 -
              (199680 : k[X]) * t1 * v1 ^ 2 +
              (266240 : k[X]) * u2 * v1 -
              (114688 : k[X]) * v1 * w2 +
              (36864 : k[X]) * Polynomial.C lambda * (p.coeff 4) -
            (29952 : k[X]) * Polynomial.C lambda * v1 ^ 2).eval a =
          0 := by
        simp only [Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_ofNat, Polynomial.eval_C]
        linear_combination hbScalar
      obtain ⟨kz, hkz⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((81920 : k[X]) * (p.coeff 4) * t1 +
            (131072 : k[X]) * b51 -
            (98304 : k[X]) * b62 * t1 +
            (212992 : k[X]) * s1 * t1 * v1 -
            (131072 : k[X]) * s1 * u2 -
            (199680 : k[X]) * t1 * v1 ^ 2 +
            (266240 : k[X]) * u2 * v1 -
            (114688 : k[X]) * v1 * w2 +
            (36864 : k[X]) * Polynomial.C lambda * (p.coeff 4) -
            (29952 : k[X]) * Polynomial.C lambda * v1 ^ 2)
          a hh0degree hroot hbEval
      have hzfact :=
        sixteenthFace_fifth_zeroU1_mul_h h0 t1 v1 s1 w2 u2
          (p.coeff 4) (p.coeff 3) b62 b51 lambda
      rw [hkz] at hzfact
      have hquotPow :
          kz - (163840 : k[X]) * (p.coeff 3) +
              h0 *
                (-(93184 : k[X]) * s1 * t1 ^ 3 +
                  (29120 : k[X]) * t1 ^ 3 * v1 -
                  (49920 : k[X]) * t1 ^ 2 * u2 +
                  (93184 : k[X]) * t1 ^ 2 * w2 +
                  (78624 : k[X]) * Polynomial.C lambda * t1 ^ 2 * v1 -
                  (59904 : k[X]) * Polynomial.C lambda * t1 * u2) +
              h0 ^ 3 *
                ((21112 : k[X]) * t1 ^ 5 -
                  (23751 : k[X]) * Polynomial.C lambda * t1 ^ 4) =
            Polynomial.C eps * h0 ^ 3 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
        have hscale : Polynomial.C eps * h0 ^ 5 =
            h0 ^ 2 * (Polynomial.C eps * h0 ^ 3) := by ring
        rw [← hscale, ← hNinthPow]
        linear_combination -hzfact
      have hqe := congrArg (fun r : k[X] => Polynomial.eval a r)
        hquotPow
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_pow,
        Polynomial.eval_ofNat, Polynomial.eval_C, hroot] at hqe
      have hkzLaw : kz.eval a = (163840 : k) * (p.coeff 3).eval a := by
        linear_combination hqe
      exact Or.inl ⟨hu1z, t1, u2, w2, b51, sigma, rho, pi, ht1, hu2,
        hw2, hb51, hsigmapoly, hrhopoly, hpipoly, hp5_3, hq7_5, hq5d,
        hsigmadvd, hrhovd, hpivd, hTform, hVform, hprod, hGnextRel,
        ⟨kz, hkz, hkzLaw⟩⟩
    · obtain ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1, homega,
        hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform, hVnextRel⟩ :=
        hcomp
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
      rw [ht1] at hNinthPow
      have haEval :
          ((40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
            (5 : k[X]) * v1 ^ 2).eval a = 0 := by
        simp only [Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_ofNat]
        linear_combination ha4
      obtain ⟨rhoc, hrhoc⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0
          ((40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
            (5 : k[X]) * v1 ^ 2)
          a hh0degree hroot haEval
      have hcfact :=
        sixteenthFace_fourth_comp_mul_h h0 t1 v1 s1 w1 u1 (p.coeff 4)
          b62 lambda
      rw [hrhoc, hsigmapoly] at hcfact
      have hquotPow :
          -(64 : k[X]) * rhoc +
              ((1600 : k[X]) * t1 * u1 - (1792 : k[X]) * t1 * w1 +
                (576 : k[X]) * Polynomial.C lambda * u1) +
              h0 *
                ((1792 : k[X]) * s1 * t1 ^ 2 -
                  (1120 : k[X]) * t1 ^ 2 * v1 -
                  (1008 : k[X]) * Polynomial.C lambda * t1 * v1) +
              h0 * (-(64 : k[X]) * sigma * v1) +
              h0 ^ 3 *
                (-(385 : k[X]) * t1 ^ 4 +
                  (462 : k[X]) * Polynomial.C lambda * t1 ^ 3) =
            Polynomial.C delta * h0 ^ 3 := by
        apply mul_left_cancel₀ hh0
        have hscale : Polynomial.C delta * h0 ^ 4 =
            h0 * (Polynomial.C delta * h0 ^ 3) := by ring
        rw [← hscale, ← hNinthPow]
        linear_combination -hcfact
      have hqe := congrArg (fun r : k[X] => Polynomial.eval a r)
        hquotPow
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_pow,
        Polynomial.eval_ofNat, Polynomial.eval_C, hroot] at hqe
      have hrhocLaw :
          rhoc.eval a + (10 : k) * t1.eval a * u1.eval a -
            (9 : k) * lambda * u1.eval a = 0 :=
        sixteenthFace_comp_G_nextOrder810 (u1.eval a) (w1.eval a)
          (t1.eval a) (rhoc.eval a) lambda hw1rel
          (by linear_combination hqe)
      exact Or.inr ⟨hB, ha4c, hu1c, t1, omega, sigma, beta, ht1,
        homega, hsigmapoly, hbeta, hsigmadvd, hbetadvd, hTform,
        hVnextRel, ⟨rhoc, hrhoc, hrhocLaw⟩⟩

/-- Source-facing sixteenth-face packet of a normalized scale-two `(8,10)`
nonzero face: the fifteenth-face split together with the next-order
fourth/fifth refinements of every live branch. -/
theorem normalized810ScaleTwo_nonzeroFace_sixteenthInitialPacket
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
            (∃ k1 : K[X],
              (81920 : K[X]) * (p.coeff 4) * t0 +
                    (131072 : K[X]) * (q.coeff 5) -
                    (98304 : K[X]) * b62 * t0 +
                    (2912 : K[X]) * t0 ^ 5 -
                    (20480 : K[X]) * t0 ^ 3 * v1 +
                    (46080 : K[X]) * t0 ^ 2 * u1 +
                    (30720 : K[X]) * t0 * v1 ^ 2 -
                    (40960 : K[X]) * u1 * v1 =
                  h0 * k1 ∧
                k1.eval a + (9 : K) * lambda *
                    ((4096 : K) * (p.coeff 4).eval a +
                      (91 : K) * (t0.eval a) ^ 4 -
                      (608 : K) * (t0.eval a) ^ 2 * v1.eval a -
                      (2560 : K) * t0.eval a * u1.eval a +
                      (256 : K) * (v1.eval a) ^ 2) = 0) ∧
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
                    (40 : K[X]) * (p.coeff 4) - (32 : K[X]) * b62 +
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
                      (80 : K) * t1.eval a * u2.eval a = 0 ∧
                    ∃ kz : K[X],
                      (81920 : K[X]) * (p.coeff 4) * t1 +
                            (131072 : K[X]) * b51 -
                            (98304 : K[X]) * b62 * t1 +
                            (212992 : K[X]) * s1 * t1 * v1 -
                            (131072 : K[X]) * s1 * u2 -
                            (199680 : K[X]) * t1 * v1 ^ 2 +
                            (266240 : K[X]) * u2 * v1 -
                            (114688 : K[X]) * v1 * w2 +
                            (36864 : K[X]) * Polynomial.C lambda *
                              (p.coeff 4) -
                            (29952 : K[X]) * Polynomial.C lambda *
                              v1 ^ 2 =
                          h0 * kz ∧
                        kz.eval a =
                          (163840 : K) * (p.coeff 3).eval a) ∨
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
                      0 ∧
                    ∃ rhoc : K[X],
                      (40 : K[X]) * (p.coeff 4) -
                            (32 : K[X]) * b62 +
                          (5 : K[X]) * v1 ^ 2 =
                        h0 * rhoc ∧
                      rhoc.eval a +
                          (10 : K) * t1.eval a * u1.eval a -
                        (9 : K) * lambda * u1.eval a = 0)))) := by
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
    nonzeroFace810_linearRoot_sixteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroSixteenthFace810

#print axioms sixteenthCoefficientJacobianRow_810
#print axioms sixteenthFace_left_V_nextOrder810
#print axioms sixteenthFace_zeroU1_Vhead_eval810
#print axioms sixteenthFace_comp_G_nextOrder810
#print axioms sixteenthFace_fifth_zeroU1_mul_h
#print axioms sixteenthFace_fourth_comp_mul_h
#print axioms nonzeroFace810_linearRoot_sixteenthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_sixteenthInitialPacket

end Max11DegreeRoutes
