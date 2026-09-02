import Sol68ScaleTwoAlignedNonsquareFixedUnifiedLoadedConsumerScratch
import Fable68ScaleTwoAlignedNonsquareMixedSeventhScratch

/-! # Finite child split after the first fixed loaded coefficients -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section FixedUnifiedLoadedNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Exact loaded refinement of the `k₁=H*K` child at the retained
`r`-root. -/
def terminalFixedMixedLoadedCubeChild68
    (B D w eDot k1 : k[X]) (j a b : k) : Prop :=
  k1.eval b = 0 ∧
    ∃ K : k[X], k1 = H * K ∧
      B * w * eDot - D * K = C j * H ^ 3 ∧
      B.derivative.eval b * w.eval b * eDot.eval b +
          B.eval b * w.derivative.eval b * eDot.eval b +
          B.eval b * w.eval b * eDot.derivative.eval b -
        (D.derivative.eval b * K.eval b +
          D.eval b * K.derivative.eval b) = 0 ∧
      D.derivative.derivative.eval a * K.eval a = 0 ∧
      (D.derivative.derivative.eval a = 0 ∨ K.eval a = 0) ∧
      B.derivative.derivative.derivative.eval a * w.eval a *
            eDot.eval a -
          (D.derivative.derivative.derivative.eval a * K.eval a +
            3 * D.derivative.derivative.eval a * K.derivative.eval a) =
        6 * j * H.derivative.eval a ^ 3 ∧
      B.derivative.derivative.derivative.eval a * w.eval a *
            eDot.eval a -
          (D.derivative.derivative.derivative.eval a * K.eval a +
            3 * D.derivative.derivative.eval a * K.derivative.eval a) ≠ 0

/-- Exact loaded refinement of the simultaneous `B=H*B₃`, `D=H*E₁`
child.  The retained lower row first splits `E₁'(a)k₁'(a)=0`; each of
its two quotient children then carries its corresponding nonzero square
coefficient. -/
def terminalFixedMixedLoadedSquareChild68
    (B D w phi1 eDot k1 : k[X]) (j a b : k) : Prop :=
  D.eval b = 0 ∧ B.eval b = 0 ∧
    ∃ B3 E1 : k[X], B = H * B3 ∧ D = H * E1 ∧
      B3 * phi1 + C 6 * H * w * E1 = 0 ∧
      E1 * k1 = H * B3 * w * eDot - C j * H ^ 3 ∧
      B3.eval a = 0 ∧ E1.eval a = 0 ∧
      B3.derivative.eval a = 0 ∧
      E1.derivative.eval a * k1.derivative.eval a = 0 ∧
      (E1.derivative.eval a = 0 ∨ k1.derivative.eval a = 0) ∧
      ((E1.eval b = 0 ∧ ∃ E2 : k[X], E1 = H * E2 ∧
          D = H ^ 2 * E2 ∧
          B3 * phi1 + C 6 * H ^ 2 * w * E2 = 0 ∧
          E2 * k1 = B3 * w * eDot - C j * H ^ 2 ∧
          (B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (2 * E2.derivative.eval a * k1.derivative.eval a +
                E2.eval a * k1.derivative.derivative.eval a) =
                2 * j * H.derivative.eval a ^ 2 ∧
            B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (2 * E2.derivative.eval a * k1.derivative.eval a +
                E2.eval a * k1.derivative.derivative.eval a) ≠ 0) ∧
          B3.derivative.derivative.eval a * phi1.eval a =
            -12 * H.derivative.eval a ^ 2 * w.eval a * E2.eval a) ∨
        (k1.eval b = 0 ∧ ∃ K : k[X], k1 = H * K ∧
          E1 * K = B3 * w * eDot - C j * H ^ 2 ∧
          (B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (E1.derivative.derivative.eval a * K.eval a +
                2 * E1.derivative.eval a * K.derivative.eval a) =
                2 * j * H.derivative.eval a ^ 2 ∧
            B3.derivative.derivative.eval a * w.eval a * eDot.eval a -
              (E1.derivative.derivative.eval a * K.eval a +
                2 * E1.derivative.eval a * K.derivative.eval a) ≠ 0)))

/-- The mixed transverse child is preserved exactly; none of the new loaded
functions applies to its undivided witness shape. -/
def terminalFixedMixedLoadedTransverseChild68
    (B D w phi1 eDot k1 : k[X]) (j b : k) : Prop :=
  D.eval b = 0 ∧ k1.eval b ≠ 0 ∧ B.eval b ≠ 0 ∧
    phi1.derivative.eval b = 0 ∧ w.eval b = 0 ∧
    D.derivative.eval b = 0 ∧
    ∃ E2 : k[X], D = H ^ 2 * E2 ∧
      B * phi1 + C 6 * H ^ 3 * w * E2 = 0 ∧
      B * w * eDot - H * E2 * k1 = C j * H ^ 3 ∧
      B.eval b * w.derivative.eval b * eDot.eval b =
        H.derivative.eval b * E2.eval b * k1.eval b

def terminalFixedUnifiedMixedLoadedNextConsumed68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedLoadedConsumed68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
      r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
      r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
      B.eval a = 0 ∧ k1.eval a = 0 ∧ D.eval a = 0 ∧
      B.derivative.eval a = 0 ∧ D.derivative.eval a = 0 ∧
      B.derivative.derivative.eval a = 0 ∧
      (terminalFixedMixedLoadedCubeChild68 H B D w eDot k1 j a b ∨
        terminalFixedMixedLoadedSquareChild68 H B D w phi1 eDot k1 j a b ∨
        terminalFixedMixedLoadedTransverseChild68 H B D w phi1 eDot k1 j b)

def terminalFixedUnifiedLoadedNextConsumerResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoadedConsumed68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoadedNextConsumed68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem terminalFixedUnifiedLoadedNext_of_consumer68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (hI4 : B * phi1 + C 6 * H * w * D = 0)
    (h : terminalFixedUnifiedLoadedConsumerResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedLoadedNextConsumerResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  have hsimple : ∀ z : k, H.eval z = 0 → H.derivative.eval z ≠ 0 :=
    fun z hz => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hz
  rcases h with hR | hM | hG
  · exact Or.inl hR
  · right
    left
    dsimp only [terminalFixedUnifiedMixedLoadedNextConsumed68]
    have hMwhole := hM
    dsimp only [terminalFixedUnifiedMixedLoadedConsumed68] at hM
    obtain ⟨hLoaded, a0, b0, _hab0, _ha0, _hb0, _hphia0,
      _hBa0, _hBda0, _hDa0, _hDda0, _hBdda0,
      _hCubeSplit0, _hSquareE20, _hSquareE10⟩ := hM
    dsimp only [terminalFixedUnifiedMixedLoaded68] at hLoaded
    obtain ⟨hSecond, hCubeLoaded, hSqE2Loaded, hSqE1Loaded,
      hSqI4Loaded⟩ := hLoaded
    dsimp only [terminalFixedUnifiedMixedSecondFollowing68] at hSecond
    obtain ⟨hFollow, hCubeSecond, _hSqFirstE2, _hSqFirstE1,
      _hSqI4First⟩ := hSecond
    dsimp only [terminalFixedUnifiedMixedFollowing68] at hFollow
    obtain ⟨hFifth, _hFirst⟩ := hFollow
    obtain ⟨a, b, hab, ha, hb, hra, hphia, hrb, hphib,
      hBa, hk1a, hDa, hBda, hDda, _hI4b, _hrowb,
      _hfactorb, _heDotb, htri⟩ := hFifth
    have hBdda := mixedIFourSecondCoefficient_68 H B phi1 w D a ha
      hphia hBa hBda hDa hDda hI4
    refine ⟨hMwhole, a, b, hab, ha, hb, hra, hphia, hrb, hphib,
      hBa, hk1a, hDa, hBda, hDda, hBdda, ?_⟩
    rcases htri with ⟨hk1b, K, hk1, hrow, hfirstb⟩ |
      ⟨hDb, hBb, B3, E1, hB3, hE1, hI4red, hE1row,
        hB3a, hE1a, hsub⟩ |
      ⟨hDb, hk1b, hBb, hphidb, hwb, hDdb, E2,
        hDsq, hI4trans, hrowtrans, htie⟩
    · left
      have hsplit := cubeSecond_doubleZero_split_68 H B w _ D K a ha
        hBa hBda hBdda hDa hDda (hCubeSecond K hk1 hrow)
      have hthird := mixedReducedTerminalThirdCoefficient_68
        H B w _ D K j a ha hBa hBda hBdda hDa hDda hrow
      have hthirdNe :
          B.derivative.derivative.derivative.eval a * w.eval a *
                (terminalEDerivativeNumerator68 H
                  (cubicENumerator68 H (p.coeff 0) (p.coeff 1)
                    (p.coeff 2) (p.coeff 3) t r)).eval a -
              (D.derivative.derivative.derivative.eval a * K.eval a +
                3 * D.derivative.derivative.eval a * K.derivative.eval a) ≠ 0 := by
        rw [hthird]
        exact mul_ne_zero (mul_ne_zero (by norm_num) hj)
          (pow_ne_zero 3 (hsimple a ha))
      exact ⟨hk1b, K, hk1, hrow, hfirstb,
        hsplit.1, hsplit.2, hthird, hthirdNe⟩
    · right
      left
      have hB3da := quotientDerivEvalZero_of_secondDerivativeZero_68
        H B B3 a ha (hsimple a ha) hB3 hB3a hBdda
      have hproduct := mixedEOneRowSecondCoefficient_68 H B3 w _ E1
        k1 j a ha hB3a hB3da hE1a hk1a hE1row
      refine ⟨hDb, hBb, B3, E1, hB3, hE1, hI4red, hE1row,
        hB3a, hE1a, hB3da, hproduct, mul_eq_zero.mp hproduct, ?_⟩
      rcases hsub with ⟨hE1b, E2, hE2, hD2, hI42, hrow2⟩ |
        ⟨hk1b, K, hk1, hrowK⟩
      · left
        have hSq := hSqE2Loaded B3 E2 hrow2
        have hsquare := squareLoaded_E2_scalar_68 H B3 w _ E2 k1 j a
          ha (hsimple a ha) hj hB3a hB3da hk1a hSq
        have hI4square := squareI4_loaded_scalar_68 H B3 phi1 w E2 a
          ha hB3a hB3da (hSqI4Loaded B3 E2 hI42)
        exact ⟨hE1b, E2, hE2, hD2, hI42, hrow2,
          hsquare, hI4square⟩
      · right
        have hSq := hSqE1Loaded B3 E1 K hrowK
        have hsquare := squareLoaded_E1K_scalar_68 H B3 w _ E1 K j a
          ha (hsimple a ha) hj hB3a hB3da hE1a hSq
        exact ⟨hk1b, K, hk1, hrowK, hsquare⟩
    · exact Or.inr (Or.inr ⟨hDb, hk1b, hBb, hphidb, hwb, hDdb,
        E2, hDsq, hI4trans, hrowtrans, htie⟩)
  · exact Or.inr (Or.inr hG)

theorem NonsquareAlignedSourceCurveData68.fixedUnifiedLoadedNextPacket
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
      terminalFixedUnifiedLoadedNextConsumerResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedLoadedConsumerPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedLoadedNext_of_consumer68 H S hdeg hj
      r t X0 Yd B D w phi1 k1 hI4 hres⟩

end FixedUnifiedLoadedNext68

end Max11DegreeRoutes
