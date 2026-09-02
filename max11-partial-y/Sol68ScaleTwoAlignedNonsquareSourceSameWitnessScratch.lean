import Sol68ScaleTwoAlignedNonsquareSourceFinalResidualScratch

/-! # Same-witness source transport for the aligned nonsquare branch

This file exposes the source identities which were previously hidden behind
separate existential packets.  Once the canonical `Phi` quotient exists, the
same `B,D,w,phi,K` witnesses carry the scaled-coordinate identities, divided
I4/loaded row, and the larger lower-zero row.  Root/component selection is
deliberately left separate.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section SameWitnessSourceTransport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- All identities needed by the later root-selection machinery, on one fixed
set of quotient witnesses.  In particular, the lower-zero identity is not a
caller-supplied compatibility assumption. -/
def terminalPhiDivisorSameWitnessSourceTransport68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 phi K : k[X]) : Prop :=
  p.coeff 4 = H * t ∧
    C 3 * t - r ^ 2 = H * X0 ∧
    C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
    terminalScaledW68 H (cubicANumerator68 t r)
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) S.gamma =
        H ^ 2 * w ∧
    terminalScaledPhi68 H (cubicANumerator68 t r) (H * B)
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) S.gamma S.epsilon = H ^ 2 * phi ∧
    terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
      H phi K phi1 k1 ∧
    B * phi + C 6 * w * D = 0 ∧
    B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) - D * K = C j * H ^ 3 ∧
    terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * B)
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * D)
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) S.alpha S.gamma S.epsilon S.eta = 0

/-- Canonical source construction of the same-witness transport packet.
The only remaining global input is the genuine divisibility `H ∣ phi1`;
the `K` quotient and every transport identity are then constructed. -/
theorem NonsquareAlignedSourceCurveData68.terminalPhiDivisorSameWitnessSourceTransport
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X0 Yd phi1 k1 B D w : k[X]),
      p.coeff 4 = H * t ∧
      C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      (H ∣ phi1 → ∃ phi K : k[X],
        terminalPhiDivisorSameWitnessSourceTransport68 H S
          r t X0 Yd B D w phi1 k1 phi K) := by
  obtain ⟨g, r, t, X0, Yd, b1, d1, w1, phiOld, _kOld, B, D, w,
      hg, hgr, hp4, hX, hY, hb1, hd1, hw1, hphiOld, hb, hd, hw,
      _hp2desc, hI4old, _hrowOld, _hroots⟩ :=
    S.terminalAfterLowerOneSourcePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  obtain ⟨g0, r0, t0, X00, Yd0, b10, d10, w10, phi1, k1,
      hg0, hgr0, hp40, hX0, hY0, hb10, hd10, hw10, hphi10,
      hkdef0, hrow0, _hselectors⟩ :=
    S.terminalKOneNextSourcePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgg : g0 = g := by
    apply mul_left_cancel₀ hH
    rw [← hg0, ← hg]
  have hrr : r0 = r := by
    apply mul_left_cancel₀ hH
    rw [← hgr0, ← hgr, hgg]
  have htt : t0 = t := by
    apply mul_left_cancel₀ hH
    rw [← hp40, ← hp4]
  have hXX : X00 = X0 := by
    apply mul_left_cancel₀ hH
    rw [← hX0, ← hX, htt, hrr]
  have hYY : Yd0 = Yd := by
    apply mul_left_cancel₀ hH
    rw [← hY0, ← hY, hrr]
  have hbb : b10 = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hb10, ← hb1, htt, hrr]
  have hdd : d10 = d1 := by
    apply mul_left_cancel₀ hH
    rw [← hd10, ← hd1, htt, hrr]
  have hww : w10 = w1 := by
    apply mul_left_cancel₀ hH
    rw [← hw10, ← hw1, htt, hrr]
  have hpp : phi1 = phiOld := by
    apply mul_left_cancel₀ hH
    rw [← hphi10, ← hphiOld, htt, hrr]
  have hphiSource : cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon = H * phi1 := by
    simpa only [htt, hrr] using hphi10
  have hI4 : B * phi1 + C 6 * H * w * D = 0 := by
    rw [hpp]
    exact hI4old
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let c0 := terminalCShiftNumerator68 H A0 S.alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
    S.epsilon S.eta
  let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
    S.alpha S.gamma S.epsilon S.eta
  let eDot := terminalEDerivativeNumerator68 H E0
  have hkcanonical : k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [A0, C0, E0, c0, V0, R1, htt, hrr, hbb, hdd, hww]
      using hkdef0
  have hrow5 : b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    simpa only [A0, C0, E0, eDot, htt, hrr, hbb, hdd, hww] using hrow0
  have hrow4 : H * B * w * eDot - D * k1 = C j * H ^ 4 := by
    rw [hb, hw, hd] at hrow5
    apply mul_left_cancel₀ hH
    linear_combination hrow5
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w := by
    rw [hW1, hw]
    ring
  have hPhi1 : terminalScaledPhi68 H A0 b1 C0 E0
      S.gamma S.epsilon = H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphiSource, ← hb1]
    simp only [cubicPhiNumerator68]
  have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
    hp hp6 hg hgr hp4 hX hY
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X0 Yd hX hY
  have hbred : terminalGReducedB68 r X0 Yd = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hBred, ← hb1]
  have hdred : terminalGReducedD68 H r X0 Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  refine ⟨r, t, X0, Yd, phi1, k1, B, D, w, hp4, hX, hY, ?_⟩
  intro hphiDvd
  obtain ⟨phi, hphi⟩ := hphiDvd
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hkroot : ∀ a : k, H.eval a = 0 → k1.eval a = 0 := by
    intro a ha
    have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
      phi1 S.gamma S.epsilon a hW1 hPhi1 ha
    have hwroot : w1.eval a = 0 := by
      have he := congrArg (fun P : k[X] => P.eval a) hw
      simpa [ha] using he
    have hphiroot : phi1.eval a = 0 := by
      have he := congrArg (fun P : k[X] => P.eval a) hphi
      simpa [ha] using he
    rw [hkcanonical]
    have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
      phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
    dsimp only [c0, V0, R1] at hk0
    rw [hcoords.1, hwroot, hphiroot] at hk0
    simpa using hk0
  obtain ⟨K, hk⟩ : ∃ K, k1 = H * K :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkroot
  have hI4q : B * phi + C 6 * w * D = 0 := by
    rw [hphi] at hI4
    apply mul_left_cancel₀ hH
    linear_combination hI4
  have hrowq : B * w * eDot - D * K = C j * H ^ 3 := by
    rw [hk] at hrow4
    apply mul_left_cancel₀ hH
    linear_combination hrow4
  have hPhi2 : terminalScaledPhi68 H A0 (H * B) C0 E0
      S.gamma S.epsilon = H ^ 2 * phi := by
    rw [← hb, hPhi1, hphi]
    ring
  have hlowerBD : terminalLowerZeroCleared68 H A0 (H * B) C0 (H * D) E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    rw [← hb, ← hd]
    exact hlower
  refine ⟨phi, K, hp4, hX, hY, ?_, ?_, ⟨hphi, hk⟩,
    hI4q, ?_, ?_⟩
  · simpa only [A0, C0] using hW2
  · simpa only [A0, C0, E0] using hPhi2
  · simpa only [E0, eDot] using hrowq
  · simpa only [A0, C0, E0] using hlowerBD

end SameWitnessSourceTransport68

end Max11DegreeRoutes
