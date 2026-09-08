import LowScale810ScaleTwoEighthFace

/-! # Scale-two ninth face for normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the eighth-face packet supplies the degree-`9`
integral and the collapsed two-component jet `v₀ = s₀ = b₆ = u₀ = w₀ = 0`
at the root of `h`, with the left alternative still allowing `t₀ ≠ 0`
and the right alternative already forcing `t₀ = 0` as well.

The next unused Keller coefficient is the degree-`8` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`9 L G' + 8 P F' + 7 Q E' + 6 R D' + 5 S C' + 4 T B' + 3 U A'
- F P' - 2 E Q' - 3 D R' - 4 C S' - 5 B T' - 6 A U' - 8 W' = 0`.
Clearing the corresponding first integral against the `z¹` decic
coordinate produces a defect larger than the remaining exact jet, so
this file isolates that Jacobian identity and the strongest exact
refinement of the collapsed eighth packet.

Evaluating the second, third, and fourth defects on that packet upgrades
`h ∣ q₆` to `h² ∣ q₆` on both components, and forces the next-order
identities `32 s₁ - 40 v₁ = 5 t₀²` together with
`128 w₁ - 160 u₁ - 40 t₀ v₁ + 5 t₀³ = 0` on the left, and
`4 s₁ = 5 v₁` together with `4 w₁ = 5 u₁` on the right.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The ninth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the eighth face start
at degree `8`. -/
theorem ninthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * q.coeff 1 +
        (p.coeff 7).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 6).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 1).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 2).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 7).derivative +
        p.coeff 1 * (q.coeff 8).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1), (8, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
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
  rw [hC9, hC8, hC7, hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Eighth-jet parentheticals of the second through fourth defects -/

section NinthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- Cofactor of `h` in the sixth-jet second defect after the eighth-packet
vanishing `v₀ = h v₁`, `s₀ = h s₁`. -/
def secondJetParen810_leftCofactor
    (h t0 v1 s1 : F[X]) (lambda : F) : F[X] :=
  (32 : F[X]) * s1 - (40 : F[X]) * v1 - (5 : F[X]) * t0 ^ 2 +
    (9 : F[X]) * Polynomial.C lambda * t0 * h

/-- Cofactor of `h` in the sixth-jet third defect after the eighth-packet
vanishing `v₀ = h v₁`, `s₀ = h s₁`, `u₀ = h u₁`, `w₀ = h w₁`. -/
def thirdJetParen810_leftCofactor
    (h t0 v1 s1 w1 u1 : F[X]) (lambda : F) : F[X] :=
  -(512 : F[X]) * s1 * t0 + (480 : F[X]) * t0 * v1 -
    (640 : F[X]) * u1 + (512 : F[X]) * w1 + (100 : F[X]) * t0 ^ 3 +
    ((144 : F[X]) * Polynomial.C lambda * v1 -
        (135 : F[X]) * Polynomial.C lambda * t0 ^ 2) * h

/-- Cofactor of `h` in the sixth-jet fourth defect after the eighth-packet
vanishing `v₀ = h v₁`, `s₀ = h s₁`, `u₀ = h u₁`, `w₀ = h w₁`,
`b₆ = h b₆₁`. -/
def fourthJetParen810_leftCofactor
    (h t0 v1 s1 w1 u1 a4 b61 : F[X]) (lambda : F) : F[X] :=
  (2048 : F[X]) * b61 +
    ((1792 : F[X]) * s1 * t0 ^ 2 - (2048 : F[X]) * s1 * v1 -
        (385 : F[X]) * t0 ^ 4 - (1120 : F[X]) * t0 ^ 2 * v1 +
      (1600 : F[X]) * t0 * u1 - (1792 : F[X]) * t0 * w1 +
        (2240 : F[X]) * v1 ^ 2 - (2560 : F[X]) * a4) * h +
    ((462 : F[X]) * Polynomial.C lambda * t0 ^ 3 -
        (1008 : F[X]) * Polynomial.C lambda * t0 * v1 +
      (576 : F[X]) * Polynomial.C lambda * u1) * h ^ 2

theorem secondJetParen810_left_mul_h
    (h t0 v1 s1 : F[X]) (lambda : F) :
    secondJetParen810 h t0 (h * v1) (h * s1) lambda =
      h * secondJetParen810_leftCofactor h t0 v1 s1 lambda := by
  simp only [secondJetParen810, secondJetParen810_leftCofactor]
  ring

theorem thirdJetParen810_left_mul_h
    (h t0 v1 s1 w1 u1 : F[X]) (lambda : F) :
    thirdJetParen810_sixth h t0 (h * v1) (h * s1) (h * w1) (h * u1)
        lambda =
      h * thirdJetParen810_leftCofactor h t0 v1 s1 w1 u1 lambda := by
  simp only [thirdJetParen810_sixth, thirdJetParen810_leftCofactor]
  ring

set_option maxHeartbeats 4000000 in
theorem fourthJetParen810_left_mul_h
    (h t0 v1 s1 w1 u1 a4 b61 : F[X]) (lambda : F) :
    fourthJetParen810_sixth h t0 (h * v1) (h * s1) (h * w1) (h * u1) a4
        (h * b61) lambda =
      h * fourthJetParen810_leftCofactor h t0 v1 s1 w1 u1 a4 b61
        lambda := by
  simp only [fourthJetParen810_sixth, fourthJetParen810_leftCofactor]
  ring

theorem eval_secondJetParen810_leftCofactor
    (h t0 v1 s1 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (secondJetParen810_leftCofactor h t0 v1 s1 lambda) =
      (32 : F) * Polynomial.eval root s1 -
        (40 : F) * Polynomial.eval root v1 -
        (5 : F) * (Polynomial.eval root t0) ^ 2 := by
  simp [secondJetParen810_leftCofactor, hroot]

theorem eval_thirdJetParen810_leftCofactor
    (h t0 v1 s1 w1 u1 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (thirdJetParen810_leftCofactor h t0 v1 s1 w1 u1 lambda) =
      -(512 : F) * Polynomial.eval root s1 * Polynomial.eval root t0 +
        (480 : F) * Polynomial.eval root t0 * Polynomial.eval root v1 -
        (640 : F) * Polynomial.eval root u1 +
        (512 : F) * Polynomial.eval root w1 +
        (100 : F) * (Polynomial.eval root t0) ^ 3 := by
  simp [thirdJetParen810_leftCofactor, hroot]

theorem eval_fourthJetParen810_leftCofactor
    (h t0 v1 s1 w1 u1 a4 b61 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (fourthJetParen810_leftCofactor h t0 v1 s1 w1 u1 a4 b61
          lambda) =
      (2048 : F) * Polynomial.eval root b61 := by
  simp [fourthJetParen810_leftCofactor, hroot]

/-- The next fourth-defect coefficient on the collapsed eighth packet
forces `b₆₁ = 0`. -/
theorem ninthFace_left_b61_810 (b61 : F)
    (hG : (2048 : F) * b61 = 0) : b61 = 0 := by
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hG).resolve_left h2048

/-- On the `t₀ = 0` eighth-packet component, the next second-defect
coefficient lifts `4 s₀ = 5 v₀` to `4 s₁ = 5 v₁`. -/
theorem ninthFace_right_s1_810 (v1 s1 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 = 0) :
    (4 : F) * s1 = (5 : F) * v1 := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hcomb : (8 : F) * ((4 : F) * s1 - (5 : F) * v1) = 0 := by
    linear_combination hM
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomb).resolve_left h8)

/-- On the `t₀ = 0` eighth-packet component, the next third-defect
coefficient forces `4 w₁ = 5 u₁`. -/
theorem ninthFace_right_w1_810 (u1 w1 : F)
    (hT : -(640 : F) * u1 + (512 : F) * w1 = 0) :
    (4 : F) * w1 = (5 : F) * u1 := by
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hcomb : (128 : F) * ((4 : F) * w1 - (5 : F) * u1) = 0 := by
    linear_combination hT
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomb).resolve_left h128)

/-- On the `v₀ = 0` eighth-packet component, the next second and third
defect coefficients reduce to a linear relation among `w₁`, `u₁`,
`t₀`, and `v₁`. -/
theorem ninthFace_left_third_reduced_810 (t0 v1 s1 u1 w1 : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 - (5 : F) * t0 ^ 2 = 0)
    (hT : -(512 : F) * s1 * t0 + (480 : F) * t0 * v1 -
      (640 : F) * u1 + (512 : F) * w1 + (100 : F) * t0 ^ 3 = 0) :
    (128 : F) * w1 - (160 : F) * u1 - (40 : F) * t0 * v1 +
      (5 : F) * t0 ^ 3 = 0 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hcomb :
      (4 : F) * ((128 : F) * w1 - (160 : F) * u1 -
          (40 : F) * t0 * v1 + (5 : F) * t0 ^ 3) = 0 := by
    linear_combination hT + (16 : F) * t0 * hM
  exact (mul_eq_zero.mp hcomb).resolve_left h4

end NinthFaceScalars810

/-! ## Source-facing ninth-face packet -/

section NonzeroNinthFace810

variable {k : Type*} [Field k] [CharZero k]

/-- Finite local ninth-face packet: the collapsed eighth-face split
together with the second-, third-, and fourth-defect refinements of
both components. -/
theorem nonzeroFace810_linearRoot_ninthInitialPacket
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
    ∃ t0 v0 u0 s0 w0 v1 s1 u1 w1 : k[X],
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 2 ∣ q.coeff 6 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8)) := by
  obtain ⟨alpha, hMrel⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨gamma, hTrel⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨delta, hGrel⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9d, hsplit⟩ :=
    nonzeroFace810_linearRoot_eighthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have hMsubst :
      localClearedSecondDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 ^ 5 * s0) lambda =
        localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
          (q.coeff 8) lambda := by
    simp only [ht0, hv0, hs0]
  have hTsubst :
      localClearedThirdDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (h0 ^ 5 * s0) (h0 ^ 3 * w0) lambda =
        localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0]
  have hGsubst :
      localClearedFourthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (h0 ^ 5 * s0) (h0 ^ 3 * w0)
          (q.coeff 6) lambda =
        localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0]
  have hMparen :
      secondJetParen810 h0 t0 v0 s0 lambda =
        Polynomial.C alpha * h0 ^ 3 :=
    secondJetParen810_eq_of_power h0 t0 v0 s0 lambda alpha hh0
      (hMsubst.trans hMrel)
  have hTparen :
      thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
        Polynomial.C gamma * h0 ^ 4 :=
    thirdJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 lambda gamma hh0
      (hTsubst.trans hTrel)
  have hGparen :
      fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (q.coeff 6)
          lambda =
        Polynomial.C delta * h0 ^ 6 :=
    fourthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (q.coeff 6) lambda delta hh0 (hGsubst.trans hGrel)
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hu0z, hw0z, _hwrel, hp6_4, hq8_6, _hq6div,
      hp5_2, hq7_4⟩ := hleft
    obtain ⟨v1, hv1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 v0 a hh0degree hroot hv0z
    obtain ⟨s1, hs1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s0 a hh0degree hroot hs0z
    obtain ⟨u1, hu1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 u0 a hh0degree hroot hu0z
    obtain ⟨w1, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w0 a hh0degree hroot hw0z
    obtain ⟨b61, hb61⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 6) a hh0degree
        hroot hb6z
    have hMleft :
        secondJetParen810 h0 t0 v0 s0 lambda =
          h0 * secondJetParen810_leftCofactor h0 t0 v1 s1 lambda := by
      simpa [hv1, hs1] using
        secondJetParen810_left_mul_h h0 t0 v1 s1 lambda
    have hTleft :
        thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
          h0 * thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
            lambda := by
      simpa [hv1, hs1, hw1, hu1] using
        thirdJetParen810_left_mul_h h0 t0 v1 s1 w1 u1 lambda
    have hGleft :
        fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
            (q.coeff 6) lambda =
          h0 * fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
            (p.coeff 4) b61 lambda := by
      simpa [hv1, hs1, hw1, hu1, hb61] using
        fourthJetParen810_left_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4) b61
          lambda
    have hMcof :
        secondJetParen810_leftCofactor h0 t0 v1 s1 lambda =
          Polynomial.C alpha * h0 ^ 2 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C alpha * h0 ^ 3 =
          h0 * (Polynomial.C alpha * h0 ^ 2) := by ring
      rw [← hMleft, hMparen, hscale]
    have hTcof :
        thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda =
          Polynomial.C gamma * h0 ^ 3 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C gamma * h0 ^ 4 =
          h0 * (Polynomial.C gamma * h0 ^ 3) := by ring
      rw [← hTleft, hTparen, hscale]
    have hGcof :
        fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4) b61
            lambda =
          Polynomial.C delta * h0 ^ 5 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C delta * h0 ^ 6 =
          h0 * (Polynomial.C delta * h0 ^ 5) := by ring
      rw [← hGleft, hGparen, hscale]
    have hM1 :
        (32 : k) * s1.eval a - (40 : k) * v1.eval a -
            (5 : k) * (t0.eval a) ^ 2 = 0 := by
      have hleft :=
        eval_secondJetParen810_leftCofactor h0 t0 v1 s1 lambda a hroot
      have hzero :
          Polynomial.eval a
              (secondJetParen810_leftCofactor h0 t0 v1 s1 lambda) =
            0 := by
        rw [hMcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    have hT1 :
        -(512 : k) * s1.eval a * t0.eval a +
            (480 : k) * t0.eval a * v1.eval a -
            (640 : k) * u1.eval a + (512 : k) * w1.eval a +
            (100 : k) * (t0.eval a) ^ 3 = 0 := by
      have hleft :=
        eval_thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda a
          hroot
      have hzero :
          Polynomial.eval a
              (thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
                lambda) = 0 := by
        rw [hTcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    have hG1 : (2048 : k) * b61.eval a = 0 := by
      have hleft :=
        eval_fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
          (p.coeff 4) b61 lambda a hroot
      have hzero :
          Polynomial.eval a
              (fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
                (p.coeff 4) b61 lambda) = 0 := by
        rw [hGcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    have hb61z := ninthFace_left_b61_810 (b61.eval a) hG1
    have hM1eq :
        (32 : k) * s1.eval a - (40 : k) * v1.eval a =
          (5 : k) * (t0.eval a) ^ 2 := by
      linear_combination hM1
    have hTred :=
      ninthFace_left_third_reduced_810 (t0.eval a) (v1.eval a)
        (s1.eval a) (u1.eval a) (w1.eval a) hM1 hT1
    have hq6_2 : h0 ^ 2 ∣ q.coeff 6 := by
      have htmp :=
        pow_dvd_mul_of_eval_eq_zero_810 h0 b61 1 a hh0degree hroot hb61z
      simpa [hb61, pow_one] using htmp
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, ht0, hv0, hu0, hs0, hw0,
      hv1, hs1, hu1, hw1, hq9d, hq6_2,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hM1eq, hTred, hp6_4, hq8_6,
        hp5_2, hq7_4⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, _hsrel, _hbrel, hp7_7,
      hp5_2, hq7_4, hp6_4, hq8_6, _hq6div⟩ := hright
    obtain ⟨v1, hv1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 v0 a hh0degree hroot hv0z
    obtain ⟨s1, hs1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s0 a hh0degree hroot hs0z
    obtain ⟨u1, hu1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 u0 a hh0degree hroot hu0z
    obtain ⟨w1, hw1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w0 a hh0degree hroot hw0z
    obtain ⟨b61, hb61⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 6) a hh0degree
        hroot hb6z
    have hMleft :
        secondJetParen810 h0 t0 v0 s0 lambda =
          h0 * secondJetParen810_leftCofactor h0 t0 v1 s1 lambda := by
      simpa [hv1, hs1] using
        secondJetParen810_left_mul_h h0 t0 v1 s1 lambda
    have hTleft :
        thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
          h0 * thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
            lambda := by
      simpa [hv1, hs1, hw1, hu1] using
        thirdJetParen810_left_mul_h h0 t0 v1 s1 w1 u1 lambda
    have hGleft :
        fourthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
            (q.coeff 6) lambda =
          h0 * fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
            (p.coeff 4) b61 lambda := by
      simpa [hv1, hs1, hw1, hu1, hb61] using
        fourthJetParen810_left_mul_h h0 t0 v1 s1 w1 u1 (p.coeff 4) b61
          lambda
    have hMcof :
        secondJetParen810_leftCofactor h0 t0 v1 s1 lambda =
          Polynomial.C alpha * h0 ^ 2 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C alpha * h0 ^ 3 =
          h0 * (Polynomial.C alpha * h0 ^ 2) := by ring
      rw [← hMleft, hMparen, hscale]
    have hTcof :
        thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda =
          Polynomial.C gamma * h0 ^ 3 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C gamma * h0 ^ 4 =
          h0 * (Polynomial.C gamma * h0 ^ 3) := by ring
      rw [← hTleft, hTparen, hscale]
    have hGcof :
        fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 (p.coeff 4) b61
            lambda =
          Polynomial.C delta * h0 ^ 5 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C delta * h0 ^ 6 =
          h0 * (Polynomial.C delta * h0 ^ 5) := by ring
      rw [← hGleft, hGparen, hscale]
    have hM1 :
        (32 : k) * s1.eval a - (40 : k) * v1.eval a -
            (5 : k) * (t0.eval a) ^ 2 = 0 := by
      have hleft :=
        eval_secondJetParen810_leftCofactor h0 t0 v1 s1 lambda a hroot
      have hzero :
          Polynomial.eval a
              (secondJetParen810_leftCofactor h0 t0 v1 s1 lambda) =
            0 := by
        rw [hMcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    have hT1 :
        -(512 : k) * s1.eval a * t0.eval a +
            (480 : k) * t0.eval a * v1.eval a -
            (640 : k) * u1.eval a + (512 : k) * w1.eval a +
            (100 : k) * (t0.eval a) ^ 3 = 0 := by
      have hleft :=
        eval_thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1 lambda a
          hroot
      have hzero :
          Polynomial.eval a
              (thirdJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
                lambda) = 0 := by
        rw [hTcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    have hG1 : (2048 : k) * b61.eval a = 0 := by
      have hleft :=
        eval_fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
          (p.coeff 4) b61 lambda a hroot
      have hzero :
          Polynomial.eval a
              (fourthJetParen810_leftCofactor h0 t0 v1 s1 w1 u1
                (p.coeff 4) b61 lambda) = 0 := by
        rw [hGcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    have hb61z := ninthFace_left_b61_810 (b61.eval a) hG1
    have hM10 : (32 : k) * s1.eval a - (40 : k) * v1.eval a = 0 := by
      simpa [ht0z] using hM1
    have hT10 : -(640 : k) * u1.eval a + (512 : k) * w1.eval a = 0 := by
      simpa [ht0z] using hT1
    have hs1rel := ninthFace_right_s1_810 (v1.eval a) (s1.eval a) hM10
    have hw1rel := ninthFace_right_w1_810 (u1.eval a) (w1.eval a) hT10
    have hq6_2 : h0 ^ 2 ∣ q.coeff 6 := by
      have htmp :=
        pow_dvd_mul_of_eval_eq_zero_810 h0 b61 1 a hh0degree hroot hb61z
      simpa [hb61, pow_one] using htmp
    exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, ht0, hv0, hu0, hs0, hw0,
      hv1, hs1, hu1, hw1, hq9d, hq6_2,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, hp7_7,
        hp5_2, hq7_4, hp6_4, hq8_6⟩⟩

/-- Source-facing ninth-face packet of a normalized scale-two `(8,10)`
nonzero face: the collapsed eighth-face split together with the
second-, third-, and fourth-defect refinements of both components. -/
theorem normalized810ScaleTwo_nonzeroFace_ninthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K) (t0 v0 u0 s0 w0 v1 s1 u1 w1 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 2 ∣ q.coeff 6 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : K) * s1.eval a - (40 : K) * v1.eval a =
              (5 : K) * (t0.eval a) ^ 2 ∧
            (128 : K) * w1.eval a - (160 : K) * u1.eval a -
                (40 : K) * t0.eval a * v1.eval a +
              (5 : K) * (t0.eval a) ^ 3 = 0 ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : K) * s1.eval a = (5 : K) * v1.eval a ∧
            (4 : K) * w1.eval a = (5 : K) * u1.eval a ∧
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
  obtain ⟨t0', v0', u0', s0', w0', v1', s1', u1', w1', ht0', hv0', hu0',
    hs0', hw0', hv1', hs1', hu1', hw1', hq9', hq6', hsplit'⟩ :=
    nonzeroFace810_linearRoot_ninthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0', hw0',
    hv1', hs1', hu1', hw1', hq9', hq6', hN', hsplit'⟩

end NonzeroNinthFace810

#print axioms ninthCoefficientJacobianRow_810
#print axioms ninthFace_left_b61_810
#print axioms ninthFace_right_s1_810
#print axioms ninthFace_right_w1_810
#print axioms ninthFace_left_third_reduced_810
#print axioms nonzeroFace810_linearRoot_ninthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_ninthInitialPacket

end Max11DegreeRoutes
