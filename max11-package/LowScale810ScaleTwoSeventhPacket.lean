import LowScale810ScaleTwoSeventhFace

/-! # Source-facing seventh-face packet for the normalized `(8,10)`
nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the sixth face supplies the jet `h⁶ ∣ p₇`,
`h³ ∣ p₆`, `h ∣ p₅`, `h⁵ ∣ q₈`, `h³ ∣ q₇`, `h⁸ ∣ q₉`, and the
seventh face supplies the degree-`10` integral together with a root-level
scalar split.  This file lifts that split to the normalized source,
preserving both exact alternatives, and records the next unused Jacobian
coefficient (degree `9`).

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The eighth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the seventh face start
at degree `9`. -/
theorem eighthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 7).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 6).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 2).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 3).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 4).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 5).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 8).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 9).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 9) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (9 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 9 :
      Finset (ℕ × ℕ)) =
      ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3),
        (7, 2), (8, 1), (9, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
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
  rw [hC10, hC9, hC8, hC7, hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Sixth-jet parentheticals of the cleared defects -/

section SeventhPacketScalars810

variable {F : Type*} [Field F] [CharZero F]

theorem secondJetParen810_eq_of_power
    (h t0 v0 s0 : F[X]) (lambda alpha : F) (hh : h ≠ 0)
    (hM : localClearedSecondDefect810 h (h ^ 6 * t0) (h ^ 3 * v0)
        (h ^ 5 * s0) lambda =
      Polynomial.C alpha * h ^ 14) :
    secondJetParen810 h t0 v0 s0 lambda =
      Polynomial.C alpha * h ^ 3 := by
  have hfactor := localClearedSecondDefect810_of_sixthJet h t0 v0 s0 lambda
  have hscale : Polynomial.C alpha * h ^ 14 =
      h ^ 11 * (Polynomial.C alpha * h ^ 3) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 11 hh)
  rw [← hfactor, hM, hscale]

theorem thirdJetParen810_sixth_eq_of_power
    (h t0 v0 s0 w0 u0 : F[X]) (lambda gamma : F) (hh : h ≠ 0)
    (hT : localClearedThirdDefect810 h (h ^ 6 * t0) (h ^ 3 * v0)
        (h * u0) (h ^ 5 * s0) (h ^ 3 * w0) lambda =
      Polynomial.C gamma * h ^ 21) :
    thirdJetParen810_sixth h t0 v0 s0 w0 u0 lambda =
      Polynomial.C gamma * h ^ 4 := by
  have hfactor :=
    localClearedThirdDefect810_of_sixthJet h t0 v0 s0 w0 u0 lambda
  have hscale : Polynomial.C gamma * h ^ 21 =
      h ^ 17 * (Polynomial.C gamma * h ^ 4) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 17 hh)
  rw [← hfactor, hT, hscale]

theorem fourthJetParen810_sixth_eq_of_power
    (h t0 v0 s0 w0 u0 a4 b6 : F[X]) (lambda delta : F) (hh : h ≠ 0)
    (hG : localClearedFourthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0)
        (h * u0) a4 (h ^ 5 * s0) (h ^ 3 * w0) b6 lambda =
      Polynomial.C delta * h ^ 28) :
    fourthJetParen810_sixth h t0 v0 s0 w0 u0 a4 b6 lambda =
      Polynomial.C delta * h ^ 6 := by
  have hfactor :=
    localClearedFourthDefect810_of_sixthJet h t0 v0 s0 w0 u0 a4 b6 lambda
  have hscale : Polynomial.C delta * h ^ 28 =
      h ^ 22 * (Polynomial.C delta * h ^ 6) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 22 hh)
  rw [← hfactor, hG, hscale]

theorem fifthJetParen810_sixth_eq_of_power
    (h t0 v0 s0 w0 u0 a4 a3 b6 b5 : F[X]) (lambda eps : F) (hh : h ≠ 0)
    (hV : localClearedFifthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0)
        (h * u0) a4 a3 (h ^ 5 * s0) (h ^ 3 * w0) b6 b5 lambda =
      Polynomial.C eps * h ^ 35) :
    fifthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 b6 b5 lambda =
      Polynomial.C eps * h ^ 7 := by
  have hfactor :=
    localClearedFifthDefect810_of_sixthJet h t0 v0 s0 w0 u0 a4 a3 b6 b5
      lambda
  have hscale : Polynomial.C eps * h ^ 35 =
      h ^ 28 * (Polynomial.C eps * h ^ 7) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 28 hh)
  rw [← hfactor, hV, hscale]

theorem seventhJetParen810_eq_of_power
    (h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3 : F[X])
    (lambda eta : F) (hh : h ≠ 0)
    (hX : localClearedSeventhDefect810 h (h ^ 6 * t0) (h ^ 3 * v0)
        (h * u0) a4 a3 a2 a1 (h ^ 5 * s0) (h ^ 3 * w0) b6 b5 b4 b3
        lambda =
      Polynomial.C eta * h ^ 49) :
    seventhJetParen810 h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3 lambda =
      Polynomial.C eta * h ^ 10 := by
  have hfactor :=
    localClearedSeventhDefect810_of_sixthJet h t0 v0 s0 w0 u0 a4 a3 a2 a1
      b6 b5 b4 b3 lambda
  have hscale : Polynomial.C eta * h ^ 49 =
      h ^ 39 * (Polynomial.C eta * h ^ 10) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 39 hh)
  rw [← hfactor, hX, hscale]

theorem secondJetParen810_eval_of_power
    (h t0 v0 s0 : F[X]) (lambda alpha : F) (root : F)
    (hroot : Polynomial.eval root h = 0)
    (hpow : secondJetParen810 h t0 v0 s0 lambda =
      Polynomial.C alpha * h ^ 3) :
    (32 : F) * Polynomial.eval root s0 -
      (40 : F) * Polynomial.eval root v0 = 0 := by
  have hleft := eval_secondJetParen810 h t0 v0 s0 lambda root hroot
  have hzero :
      Polynomial.eval root (secondJetParen810 h t0 v0 s0 lambda) = 0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

theorem thirdJetParen810_sixth_eval_of_power
    (h t0 v0 s0 w0 u0 : F[X]) (lambda gamma : F) (root : F)
    (hroot : Polynomial.eval root h = 0)
    (hpow : thirdJetParen810_sixth h t0 v0 s0 w0 u0 lambda =
      Polynomial.C gamma * h ^ 4) :
    -(512 : F) * Polynomial.eval root s0 * Polynomial.eval root t0 +
        (480 : F) * Polynomial.eval root t0 * Polynomial.eval root v0 -
        (640 : F) * Polynomial.eval root u0 +
        (512 : F) * Polynomial.eval root w0 = 0 := by
  have hleft :=
    eval_thirdJetParen810_sixth h t0 v0 s0 w0 u0 lambda root hroot
  have hzero :
      Polynomial.eval root
          (thirdJetParen810_sixth h t0 v0 s0 w0 u0 lambda) = 0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

theorem fourthJetParen810_sixth_eval_of_power
    (h t0 v0 s0 w0 u0 a4 b6 : F[X]) (lambda delta : F) (root : F)
    (hroot : Polynomial.eval root h = 0)
    (hpow : fourthJetParen810_sixth h t0 v0 s0 w0 u0 a4 b6 lambda =
      Polynomial.C delta * h ^ 6) :
    (2048 : F) * Polynomial.eval root b6 -
      (2048 : F) * Polynomial.eval root s0 * Polynomial.eval root v0 +
      (2240 : F) * (Polynomial.eval root v0) ^ 2 = 0 := by
  have hleft :=
    eval_fourthJetParen810_sixth h t0 v0 s0 w0 u0 a4 b6 lambda root hroot
  have hzero :
      Polynomial.eval root
          (fourthJetParen810_sixth h t0 v0 s0 w0 u0 a4 b6 lambda) = 0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

theorem fifthJetParen810_sixth_eval_of_power
    (h t0 v0 s0 w0 u0 a4 a3 b6 b5 : F[X]) (lambda eps : F) (root : F)
    (hroot : Polynomial.eval root h = 0)
    (hpow : fifthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 b6 b5 lambda =
      Polynomial.C eps * h ^ 7) :
    -(98304 : F) * Polynomial.eval root b6 * Polynomial.eval root t0 +
        (212992 : F) * Polynomial.eval root s0 * Polynomial.eval root t0 *
          Polynomial.eval root v0 -
        (131072 : F) * Polynomial.eval root s0 * Polynomial.eval root u0 -
        (199680 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root v0) ^ 2 +
        (266240 : F) * Polynomial.eval root u0 * Polynomial.eval root v0 -
        (114688 : F) * Polynomial.eval root v0 *
          Polynomial.eval root w0 = 0 := by
  have hleft :=
    eval_fifthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 b6 b5 lambda root
      hroot
  have hzero :
      Polynomial.eval root
          (fifthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 b6 b5 lambda) =
        0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

theorem seventhJetParen810_eval_of_power
    (h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3 : F[X])
    (lambda eta : F) (root : F) (hroot : Polynomial.eval root h = 0)
    (hpow : seventhJetParen810 h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3
        lambda =
      Polynomial.C eta * h ^ 10) :
    (17301504 : F) * Polynomial.eval root b6 * Polynomial.eval root t0 *
          Polynomial.eval root v0 -
        (12582912 : F) * Polynomial.eval root b6 * Polynomial.eval root u0 -
        (27394048 : F) * Polynomial.eval root s0 * Polynomial.eval root t0 *
          (Polynomial.eval root v0) ^ 2 +
        (23068672 : F) * Polynomial.eval root s0 * Polynomial.eval root u0 *
          Polynomial.eval root v0 +
        (25681920 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root v0) ^ 3 -
        (34242560 : F) * Polynomial.eval root u0 *
          (Polynomial.eval root v0) ^ 2 +
        (10092544 : F) * (Polynomial.eval root v0) ^ 2 *
          Polynomial.eval root w0 = 0 := by
  have hleft :=
    eval_seventhJetParen810 h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3
      lambda root hroot
  have hzero :
      Polynomial.eval root
          (seventhJetParen810 h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3
            lambda) = 0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

set_option linter.unusedSectionVars false in
/-- A further simple-root vanishing upgrades `hⁿ g` to order `n+1`. -/
theorem pow_dvd_mul_of_eval_eq_zero_810
    (h g : F[X]) (n : ℕ) (a : F) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hg : g.eval a = 0) :
    h ^ (n + 1) ∣ h ^ n * g := by
  obtain ⟨g1, hg1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h g a hdegree hroot hg
  refine ⟨g1, ?_⟩
  rw [hg1, pow_succ, mul_assoc]

end SeventhPacketScalars810

/-! ## Source-facing seventh-face packet -/

section NonzeroSeventhPacket810

variable {k : Type*} [Field k] [CharZero k]

/-- Finite local seventh-face packet: the sixth-face jet together with
the exact root-level split of the second through fifth and seventh
defects.  The first alternative is `h⁴ ∣ p₆`, `h⁶ ∣ q₈`, `h ∣ q₆`
and `4 (q₇/h³)(a) = 5 (p₅/h)(a)`.  The second is `h⁷ ∣ p₇`,
`h² ∣ p₅`, `h⁴ ∣ q₇` together with `4 (q₈/h⁵)(a) = 5 (p₆/h³)(a)`
and `32 q₆(a) = 5 (p₆/h³)(a)²`. -/
theorem nonzeroFace810_linearRoot_seventhInitialPacket
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
    ∃ t0 v0 u0 s0 w0 : k[X],
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            (4 : k) * w0.eval a = (5 : k) * u0.eval a ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ∣ q.coeff 6) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (4 : k) * s0.eval a = (5 : k) * v0.eval a ∧
            (32 : k) * (q.coeff 6).eval a = (5 : k) * (v0.eval a) ^ 2 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7)) := by
  obtain ⟨alpha, hMrel⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨gamma, hTrel⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨delta, hGrel⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eta, hXrel⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨hp7d, hp6d, hp5d, hq8d, hq7d, hq9d⟩ :=
    nonzeroFace810_linearRoot_sixthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨t0, ht0⟩ := hp7d
  obtain ⟨v0, hv0⟩ := hp6d
  obtain ⟨u0, hu0⟩ := hp5d
  obtain ⟨s0, hs0⟩ := hq8d
  obtain ⟨w0, hw0⟩ := hq7d
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
  have hVsubst :
      localClearedFifthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (p.coeff 3) (h0 ^ 5 * s0)
          (h0 ^ 3 * w0) (q.coeff 6) (q.coeff 5) lambda =
        localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0]
  have hXsubst :
      localClearedSeventhDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (h0 ^ 5 * s0) (h0 ^ 3 * w0) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda =
        localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda := by
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
  have hVparen :
      fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (q.coeff 6) (q.coeff 5) lambda =
        Polynomial.C eps * h0 ^ 7 :=
    fifthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (q.coeff 6) (q.coeff 5) lambda eps hh0
      (hVsubst.trans hVrel)
  have hXparen :
      seventhJetParen810 h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) lambda =
        Polynomial.C eta * h0 ^ 10 :=
    seventhJetParen810_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 6) (q.coeff 5)
      (q.coeff 4) (q.coeff 3) lambda eta hh0 (hXsubst.trans hXrel)
  have hMroot :=
    secondJetParen810_eval_of_power h0 t0 v0 s0 lambda alpha a hroot
      hMparen
  have hTroot :=
    thirdJetParen810_sixth_eval_of_power h0 t0 v0 s0 w0 u0 lambda gamma a
      hroot hTparen
  have hGroot :=
    fourthJetParen810_sixth_eval_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (q.coeff 6) lambda delta a hroot hGparen
  have hVroot :=
    fifthJetParen810_sixth_eval_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (q.coeff 6) (q.coeff 5) lambda eps a hroot hVparen
  have hXroot :=
    seventhJetParen810_eval_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 6) (q.coeff 5)
      (q.coeff 4) (q.coeff 3) lambda eta a hroot hXparen
  rcases seventhFace_rootScalars_split810 (t0.eval a) (v0.eval a)
      (u0.eval a) (s0.eval a) (w0.eval a) ((q.coeff 6).eval a)
      hMroot hTroot hGroot hVroot hXroot with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hwrel⟩ := hleft
    have hp6_4 : h0 ^ 4 ∣ p.coeff 6 := by
      rw [hv0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 v0 3 a hh0degree hroot hv0z
    have hq8_6 : h0 ^ 6 ∣ q.coeff 8 := by
      rw [hs0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 s0 5 a hh0degree hroot hs0z
    have hq6div : h0 ∣ q.coeff 6 :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 6) a hh0degree
        hroot hb6z
    exact ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9d,
      Or.inl ⟨hv0z, hs0z, hb6z, hwrel, hp6_4, hq8_6, hq6div⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hsrel, hbrel⟩ := hright
    have hp7_7 : h0 ^ 7 ∣ p.coeff 7 := by
      rw [ht0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 t0 6 a hh0degree hroot ht0z
    have hp5_2 : h0 ^ 2 ∣ p.coeff 5 := by
      have htmp :=
        pow_dvd_mul_of_eval_eq_zero_810 h0 u0 1 a hh0degree hroot hu0z
      simpa [hu0, pow_one] using htmp
    have hq7_4 : h0 ^ 4 ∣ q.coeff 7 := by
      rw [hw0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 w0 3 a hh0degree hroot hw0z
    exact ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9d,
      Or.inr ⟨ht0z, hu0z, hw0z, hsrel, hbrel, hp7_7, hp5_2, hq7_4⟩⟩

/-- Source-facing seventh-face packet of a normalized scale-two `(8,10)`
nonzero face: the sixth-face jet, together with the exact two-component
root split of the second through fifth and seventh defects. -/
theorem normalized810ScaleTwo_nonzeroFace_seventhInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K) (t0 v0 u0 s0 w0 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            (4 : K) * w0.eval a = (5 : K) * u0.eval a ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ∣ q.coeff 6) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (4 : K) * s0.eval a = (5 : K) * v0.eval a ∧
            (32 : K) * (q.coeff 6).eval a = (5 : K) * (v0.eval a) ^ 2 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7)) := by
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
  obtain ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9, hsplit⟩ :=
    nonzeroFace810_linearRoot_seventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0, v0, u0, s0, w0, hh0, hlambda, hh0degree, hH,
    hroot, ht0, hv0, hu0, hs0, hw0, hq9, hN', hsplit⟩

end NonzeroSeventhPacket810

#print axioms eighthCoefficientJacobianRow_810
#print axioms secondJetParen810_eq_of_power
#print axioms thirdJetParen810_sixth_eq_of_power
#print axioms fourthJetParen810_sixth_eq_of_power
#print axioms fifthJetParen810_sixth_eq_of_power
#print axioms seventhJetParen810_eq_of_power
#print axioms seventhFace_rootScalars_split810
#print axioms nonzeroFace810_linearRoot_seventhInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_seventhInitialPacket

end Max11DegreeRoutes
