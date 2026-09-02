import Sol68ScaleTwoAlignedNonsquareFixedUnifiedLoadedScratch
import Fable68ScaleTwoAlignedNonsquareMixedSixthScratch
import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroSeventhScratch

/-! # Consuming the first loaded coefficients on the fixed branches -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section FixedUnifiedLoadedConsumerAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A cube-loaded difference whose left summand has a fourth core factor
loads the third derivative of the right product with the opposite sign. -/
theorem cubeLoaded_rightProductThird_68
    (H P D K : k[X]) (j z : k) (hz : H.eval z = 0)
    (hHz : H.derivative.eval z ≠ 0) (hj : j ≠ 0)
    (hP : ∃ U : k[X], P = H ^ 4 * U)
    (hload : terminalFixedCubeLoadedThird68 H (P - D * K) j) :
    (D * K).derivative.derivative.derivative.eval z =
        -(6 * j * H.derivative.eval z ^ 3) ∧
      (D * K).derivative.derivative.derivative.eval z ≠ 0 := by
  obtain ⟨U, rfl⟩ := hP
  have hleft :
      (H ^ 4 * U).derivative.derivative.derivative.eval z = 0 :=
    quarticCore_third_derivative_eval_zero_68 H U z hz
  have h := hload z hz hHz hj
  have heq := h.1
  simp only [derivative_sub, eval_sub, hleft, zero_sub] at heq
  refine ⟨?_, ?_⟩
  · linear_combination -heq
  · exact fun hzero => h.2 (by
      simp only [derivative_sub, eval_sub, hleft, hzero, sub_zero])

/-- At the retained double-zero root the homogeneous second cube coefficient
is exactly the product split `D'' K = 0`. -/
theorem cubeSecond_doubleZero_split_68
    (H B w eDot D K : k[X]) (a : k) (ha : H.eval a = 0)
    (hBa : B.eval a = 0) (hBda : B.derivative.eval a = 0)
    (hBdda : B.derivative.derivative.eval a = 0)
    (hDa : D.eval a = 0) (hDda : D.derivative.eval a = 0)
    (hsecond : terminalFixedCubeLoadedSecondCoefficient68 H
      (B * w * eDot - D * K)) :
    D.derivative.derivative.eval a * K.eval a = 0 ∧
      (D.derivative.derivative.eval a = 0 ∨ K.eval a = 0) := by
  have hzero := hsecond a ha
  simp only [derivative_sub, derivative_add, derivative_mul, eval_sub,
    eval_add, eval_mul, hBa, hBda, hBdda, hDa, hDda, zero_mul,
    mul_zero, zero_add, add_zero, sub_zero, zero_sub, neg_eq_zero] at hzero
  have hprod : D.derivative.derivative.eval a * K.eval a = 0 := hzero
  exact ⟨hprod, mul_eq_zero.mp hprod⟩

/-- The square-loaded `E₂*k₁` child after the retained zeros of `B₃` and
`k₁` have been substituted. -/
theorem squareLoaded_E2_scalar_68
    (H B3 w eDot E2 k1 : k[X]) (j a : k)
    (ha : H.eval a = 0) (hHa : H.derivative.eval a ≠ 0) (hj : j ≠ 0)
    (hB3a : B3.eval a = 0) (hB3da : B3.derivative.eval a = 0)
    (hk1a : k1.eval a = 0)
    (hload : terminalFixedSquareLoadedSecond68 H
      (B3 * w * eDot) (E2 * k1) j) :
    B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
        (2 * E2.derivative.eval a * k1.derivative.eval a +
          E2.eval a * k1.derivative.derivative.eval a) =
          2 * j * H.derivative.eval a ^ 2 ∧
      B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
        (2 * E2.derivative.eval a * k1.derivative.eval a +
          E2.eval a * k1.derivative.derivative.eval a) ≠ 0 := by
  have h := hload a ha hHa hj
  have heq := h.1
  simp only [derivative_sub, derivative_add, derivative_mul, eval_sub,
    eval_add, eval_mul, hB3a, hB3da, hk1a, zero_mul, mul_zero,
    zero_add, add_zero] at heq
  have hscalar :
      B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
          (2 * E2.derivative.eval a * k1.derivative.eval a +
            E2.eval a * k1.derivative.derivative.eval a) =
        2 * j * H.derivative.eval a ^ 2 := by
    linear_combination heq
  refine ⟨hscalar, ?_⟩
  rw [hscalar]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 2 hHa)

/-- The square-loaded `E₁*K` child after the retained quotient zeros. -/
theorem squareLoaded_E1K_scalar_68
    (H B3 w eDot E1 K : k[X]) (j a : k)
    (ha : H.eval a = 0) (hHa : H.derivative.eval a ≠ 0) (hj : j ≠ 0)
    (hB3a : B3.eval a = 0) (hB3da : B3.derivative.eval a = 0)
    (hE1a : E1.eval a = 0)
    (hload : terminalFixedSquareLoadedSecond68 H
      (B3 * w * eDot) (E1 * K) j) :
    B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
        (E1.derivative.derivative.eval a * K.eval a +
          2 * E1.derivative.eval a * K.derivative.eval a) =
          2 * j * H.derivative.eval a ^ 2 ∧
      B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
        (E1.derivative.derivative.eval a * K.eval a +
          2 * E1.derivative.eval a * K.derivative.eval a) ≠ 0 := by
  have h := hload a ha hHa hj
  have heq := h.1
  simp only [derivative_sub, derivative_add, derivative_mul, eval_sub,
    eval_add, eval_mul, hB3a, hB3da, hE1a, zero_mul, mul_zero,
    zero_add, add_zero] at heq
  have hscalar :
      B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
          (E1.derivative.derivative.eval a * K.eval a +
            2 * E1.derivative.eval a * K.derivative.eval a) =
        2 * j * H.derivative.eval a ^ 2 := by
    linear_combination heq
  refine ⟨hscalar, ?_⟩
  rw [hscalar]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 2 hHa)

/-- The simultaneously loaded I4 coefficient after `B₃(a)=B₃'(a)=0`. -/
theorem squareI4_loaded_scalar_68
    (H B3 phi w E2 : k[X]) (a : k) (ha : H.eval a = 0)
    (hB3a : B3.eval a = 0) (hB3da : B3.derivative.eval a = 0)
    (hload : terminalFixedSquareI4Second68 H B3 phi w E2) :
    B3.derivative.derivative.eval a * phi.eval a =
      -12 * H.derivative.eval a ^ 2 * w.eval a * E2.eval a := by
  have h := hload a ha
  simpa only [derivative_mul, derivative_add, eval_add, eval_mul,
    hB3a, hB3da, zero_mul, mul_zero, zero_add, add_zero] using h

end FixedUnifiedLoadedConsumerAlgebra68

section FixedUnifiedLoadedConsumer68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

def terminalFixedUnifiedRLoadedConsumed68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRSecondFollowing68 H S
      r t X0 Yd B D w phi1 k1 ∧
    ∃ phi K : k[X],
      terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 phi K ∧
      terminalFixedCubeLoadedThird68 H
        (B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * K) j ∧
      ∀ z : k, H.eval z = 0 → H.derivative.eval z ≠ 0 → j ≠ 0 →
        (D * K).derivative.derivative.derivative.eval z =
            -(6 * j * H.derivative.eval z ^ 3) ∧
          (D * K).derivative.derivative.derivative.eval z ≠ 0

/-- Same-witness mixed leaf with its actual `r`-root and all branch-usable
loaded consequences.  The transverse child remains in the retained fifth
packet and is not silently strengthened. -/
def terminalFixedUnifiedMixedLoadedConsumed68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedLoaded68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
      phi1.eval a ≠ 0 ∧ B.eval a = 0 ∧ B.derivative.eval a = 0 ∧
      D.eval a = 0 ∧ D.derivative.eval a = 0 ∧
      B.derivative.derivative.eval a = 0 ∧
      (∀ K : k[X], k1 = H * K →
        B * w * eDot - D * K = C j * H ^ 3 →
        D.derivative.derivative.eval a * K.eval a = 0 ∧
          (D.derivative.derivative.eval a = 0 ∨ K.eval a = 0)) ∧
      (∀ B3 E1 E2 : k[X], B = H * B3 → D = H * E1 →
        E1 = H * E2 → B3.eval a = 0 → E1.eval a = 0 →
        E2 * k1 = B3 * w * eDot - C j * H ^ 2 →
        B3.derivative.eval a = 0 ∧
          (B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (2 * E2.derivative.eval a * k1.derivative.eval a +
                E2.eval a * k1.derivative.derivative.eval a) =
                2 * j * H.derivative.eval a ^ 2 ∧
            B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (2 * E2.derivative.eval a * k1.derivative.eval a +
                E2.eval a * k1.derivative.derivative.eval a) ≠ 0) ∧
          B3.derivative.derivative.eval a * phi1.eval a =
            -12 * H.derivative.eval a ^ 2 * w.eval a * E2.eval a) ∧
      ∀ B3 E1 K : k[X], B = H * B3 → D = H * E1 →
        B3.eval a = 0 → E1.eval a = 0 →
        E1 * K = B3 * w * eDot - C j * H ^ 2 →
        B3.derivative.eval a = 0 ∧
          (B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (E1.derivative.derivative.eval a * K.eval a +
                2 * E1.derivative.eval a * K.derivative.eval a) =
                2 * j * H.derivative.eval a ^ 2 ∧
            B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (E1.derivative.derivative.eval a * K.eval a +
                2 * E1.derivative.eval a * K.derivative.eval a) ≠ 0)

def terminalFixedUnifiedLoadedConsumerResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoadedConsumed68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoadedConsumed68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem terminalFixedUnifiedLoadedConsumer_of_loaded68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (hI4 : B * phi1 + C 6 * H * w * D = 0)
    (h : terminalFixedUnifiedLoadedResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedLoadedConsumerResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  have hsimple : ∀ z : k, H.eval z = 0 → H.derivative.eval z ≠ 0 :=
    fun z hz => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hz
  rcases h with hR | hM | hG
  · left
    obtain ⟨hRsecond, phi, K, T, hload⟩ := hR
    have href := hRsecond.1.1
    obtain ⟨s, t1, y1, A1, c2, e3, psi, m, K0,
      _hr, _hrdvd, _ht, _htface, _hp4, _hp3, _hyface,
      _htdvd, _hp4dvd, _hp3dvd, _hA1, _hA, _hc2, _hC,
      _he3, hE, heDot, _hpsi, _hphi2, _hphi2dvd, _hphidvd,
      _hwd, _hwddvd, _hlower, _hquot, _hdpsi, _hfaces,
      _hm, _hDk, _hDkdvd, _hmval, _hDne, _hk1ne, _hk1,
      _T0, _hgeom, _hfinal⟩ := href
    refine ⟨hRsecond, phi, K, T, hload, ?_⟩
    intro z hz hHz hj0
    apply cubeLoaded_rightProductThird_68 H
      (B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) D K j z hz hHz hj0
    · refine ⟨B * w * e3.derivative, ?_⟩
      rw [heDot]
      ring
    · exact hload
  · right
    left
    dsimp only [terminalFixedUnifiedMixedLoadedConsumed68]
    dsimp only [terminalFixedUnifiedMixedLoaded68] at hM
    have hMwhole := hM
    obtain ⟨hMsecond, hCube, hSqE2, hSqE1, hSqI4⟩ := hM
    dsimp only [terminalFixedUnifiedMixedSecondFollowing68] at hMsecond
    obtain ⟨hMfollow, hCubeSecond, _hSqFirstE2, _hSqFirstE1,
      _hSqI4First⟩ := hMsecond
    dsimp only [terminalFixedUnifiedMixedFollowing68] at hMfollow
    obtain ⟨hFifth, _hfirst⟩ := hMfollow
    obtain ⟨a, b, hab, ha, hb, _hra, hphia, _hrb, _hphib,
      hBa, _hk1a, hDa, hBda, hDda, _hfaceI, _hfaceR,
      _hfaceB, _heDot, _htri⟩ := hFifth
    have hBdda := mixedIFourSecondCoefficient_68 H B phi1 w D a ha
      hphia hBa hBda hDa hDda hI4
    refine ⟨hMwhole, a, b, hab, ha, hb, hphia, hBa, hBda, hDa, hDda,
      hBdda, ?_, ?_, ?_⟩
    · intro K hk hrow
      exact cubeSecond_doubleZero_split_68 H B w _ D K a ha
        hBa hBda hBdda hDa hDda (hCubeSecond K hk hrow)
    · intro B3 E1 E2 hB hD hE1 hB3a hE1a hrow
      have hB3da := quotientDerivEvalZero_of_secondDerivativeZero_68
        H B B3 a ha (hsimple a ha) hB hB3a hBdda
      have hload := hSqE2 B3 E2 hrow
      have hI4red : B3 * phi1 + C 6 * H ^ 2 * w * E2 = 0 := by
        have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
        apply mul_left_cancel₀ hH
        rw [hB, hD, hE1] at hI4
        linear_combination hI4
      exact ⟨hB3da,
        squareLoaded_E2_scalar_68 H B3 w _ E2 k1 j a ha
          (hsimple a ha) hj hB3a hB3da _hk1a hload,
        squareI4_loaded_scalar_68 H B3 phi1 w E2 a ha hB3a hB3da
          (hSqI4 B3 E2 hI4red)⟩
    · intro B3 E1 K hB hD hB3a hE1a hrow
      have hB3da := quotientDerivEvalZero_of_secondDerivativeZero_68
        H B B3 a ha (hsimple a ha) hB hB3a hBdda
      exact ⟨hB3da,
        squareLoaded_E1K_scalar_68 H B3 w _ E1 K j a ha
          (hsimple a ha) hj hB3a hB3da hE1a (hSqE1 B3 E1 K hrow)⟩
  · exact Or.inr (Or.inr hG)

theorem NonsquareAlignedSourceCurveData68.fixedUnifiedLoadedConsumerPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      terminalFixedUnifiedLoadedConsumerResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedLoadedPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedLoadedConsumer_of_loaded68 H S hdeg hj
      r t X0 Yd B D w phi1 k1 hI4 hres⟩

end FixedUnifiedLoadedConsumer68

end Max11DegreeRoutes
