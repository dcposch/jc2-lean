import Sol68ScaleTwoAlignedNonsquareAfterLowerOneCoordinateSplitScratch

/-! # The global `H | phi₁` coordinate branch -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section PhiDivisorLowerZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalLowerZeroSOne68
    (H A B D : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * D + C (4 / 9 : k) * A * B + C alpha * H * B

def terminalLowerZeroUOne68
    (H A B C0 D : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * B * C0 + C (4 / 9 : k) * A * D -
    C (4 / 27 : k) * A ^ 2 * B + C alpha * H * D +
    C (2 / 3 * gamma : k) * H ^ 2 * B

def terminalLowerZeroDDOne68 (H D : k[X]) : k[X] :=
  (C 2 - C 3) * H.derivative * D + C 2 * H * D.derivative

def terminalLowerZeroUDOne68 (H U : k[X]) : k[X] :=
  (C 2 - C 5) * H.derivative * U + C 2 * H * U.derivative

def terminalLowerZeroOne68
    (H A B C0 D E : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let S1 := terminalLowerZeroSOne68 H A B D alpha
  let T0 := terminalLowerOneTNumerator68 H A (H * B) C0 E
    alpha gamma epsilon
  let U1 := terminalLowerZeroUOne68 H A B C0 D alpha gamma
  let V0 := terminalVNumerator68 H A (H * B) C0 (H * D) E
    alpha gamma epsilon eta
  U1 * terminalLowerZeroCDot68 H C0 +
    T0 * terminalLowerZeroDDOne68 H D +
    C 3 * S1 * terminalEDerivativeNumerator68 H E -
    C 3 * B * terminalVDerivativeNumerator68 H V0 -
    C0 * terminalLowerZeroUDOne68 H U1 -
    D * terminalLowerZeroTDot68 H T0

theorem terminalLowerZero_factor_one_68
    (H A b C0 d E B D : k[X]) (alpha gamma epsilon eta : k)
    (hb : b = H * B) (hd : d = H * D) :
    terminalLowerZeroCleared68 H A b C0 d E alpha gamma epsilon eta =
      H * terminalLowerZeroOne68 H A B C0 D E
        alpha gamma epsilon eta := by
  rw [hb, hd]
  have hS : terminalLowerZeroSNumerator68 H A (H * B) (H * D) alpha =
      H * terminalLowerZeroSOne68 H A B D alpha := by
    simp only [terminalLowerZeroSNumerator68, terminalLowerZeroSOne68]
    ring
  have hU : terminalLowerOneUNumerator68 H A (H * B) C0 (H * D)
      alpha gamma = H * terminalLowerZeroUOne68 H A B C0 D alpha gamma := by
    simp only [terminalLowerOneUNumerator68, terminalLowerZeroUOne68]
    ring
  have hDD : terminalLowerOneDTwoDot68 H (H * D) =
      H * terminalLowerZeroDDOne68 H D := by
    simp only [terminalLowerOneDTwoDot68, terminalLowerZeroDDOne68,
      derivative_mul]
    ring
  have hUD : terminalLowerOneUTwoDot68 H
      (terminalLowerOneUNumerator68 H A (H * B) C0 (H * D)
        alpha gamma) = H * terminalLowerZeroUDOne68 H
          (terminalLowerZeroUOne68 H A B C0 D alpha gamma) := by
    rw [hU]
    simp only [terminalLowerOneUTwoDot68, terminalLowerZeroUDOne68,
      derivative_mul]
    ring
  simp only [terminalLowerZeroCleared68, terminalLowerZeroOne68]
  rw [hS, hDD, hUD, hU]
  ring

/-- The root face of the once-cancelled larger lower row is tautological.
Thus this row does not yet force a new coordinate divisor on the `H | phi₁`
branch; one more coefficient is genuinely necessary. -/
theorem terminalLowerZeroOne_eval_root_68
    (H A B C0 D E : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0)
    (hC : C0.eval a = (A.eval a) ^ 2 / 3)
    (hE : E.eval a = (A.eval a) ^ 3 / 27) :
    (terminalLowerZeroOne68 H A B C0 D E
      alpha gamma epsilon eta).eval a = 0 := by
  simp only [terminalLowerZeroOne68, terminalLowerZeroSOne68,
    terminalLowerZeroUOne68, terminalLowerZeroDDOne68,
    terminalLowerZeroUDOne68, terminalLowerZeroCDot68,
    terminalLowerZeroTDot68, terminalLowerOneTNumerator68,
    terminalEDerivativeNumerator68, terminalVDerivativeNumerator68,
    terminalVNumerator68, eval_add, eval_sub, eval_neg, eval_mul, eval_pow,
    eval_C, eval_ofNat, ha, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  rw [hC, hE]
  ring

end PhiDivisorLowerZeroAlgebra68

section PhiDivisorSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- On the global `H | phi₁` branch the canonical transverse quotient also
gains `H`.  Both exact invariant rows divide once more.  The once-cancelled
larger lower row is also exposed source-facing; its root face is tautological,
so a further coefficient is required for a new coordinate divisor. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      (H ∣ phi1 →
        ∃ phi2 k2 : k[X],
          phi1 = H * phi2 ∧ k1 = H * k2 ∧
          b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           terminalLowerZeroOne68 H A0 b2 C0 d2 E0
             S.alpha S.gamma S.epsilon S.eta = 0)) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, hg, hgr, ht, hX, hY, hb1, hd1,
      hw1, hroot, _hdvdW, _hsqW⟩ :=
    S.terminalLowerOneSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  obtain ⟨g0, r0, t0, X0, Yd0, b10, d10, w10, phi1, k1,
      hg0, hgr0, ht0, hX0, hY0, hb10, hd10, hw10, hphi10,
      hkdef0, hrow0, _hselectors0⟩ :=
    S.terminalKOneNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgg : g0 = g := by
    apply mul_left_cancel₀ hH
    rw [← hg0, ← hg]
  have hrr : r0 = r := by
    apply mul_left_cancel₀ hH
    rw [← hgr0, ← hgr, hgg]
  have htt : t0 = t := by
    apply mul_left_cancel₀ hH
    rw [← ht0, ← ht]
  have hXX : X0 = X := by
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
  have hphi : cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon = H * phi1 := by
    simpa only [htt, hrr] using hphi10
  have hkdef :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let c0 := terminalCShiftNumerator68 H A0 S.alpha
      let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
        S.epsilon S.eta
      let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
        S.alpha S.gamma S.epsilon S.eta
      k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [htt, hrr, hbb, hdd, hww] using hkdef0
  have hrow :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let eDot := terminalEDerivativeNumerator68 H E0
      b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    simpa only [htt, hrr, hbb, hdd, hww] using hrow0
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hdvdB : H ∣ b1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).1)
  have hdvdD : H ∣ d1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).2.1)
  have hdvdW : H ∣ w1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).2.2)
  obtain ⟨b2, hb2⟩ := hdvdB
  obtain ⟨d2, hd2⟩ := hdvdD
  obtain ⟨w2, hw2⟩ := hdvdW
  have hI4source := S.terminalI4_cleared_source_identity (H := H)
    hp hp6 hg hgr ht
  rw [hb1, hd1, hw1, hphi] at hI4source
  have hI4 : b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 := by
    have hfac : H ^ 2 * (b1 * phi1 + (6 : k[X]) * w1 * d1) = 0 := by
      linear_combination hI4source
    exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hH)
  have hI4next : b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 := by
    rw [hb2, hw2, hd2] at hI4
    apply mul_left_cancel₀ hH
    linear_combination hI4
  have hrowNext :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let eDot := terminalEDerivativeNumerator68 H E0
      H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    dsimp only at hrow ⊢
    rw [hb2, hw2, hd2] at hrow
    apply mul_left_cancel₀ hH
    linear_combination hrow
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
    ht, hX, hY, ?_⟩
  intro hphiDvd
  obtain ⟨phi2, hphi2⟩ := hphiDvd
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let c0 := terminalCShiftNumerator68 H A0 S.alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
    S.epsilon S.eta
  let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
    S.alpha S.gamma S.epsilon S.eta
  have hW : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi, ← hb1]
    simp only [cubicPhiNumerator68]
  have hkcanonical : k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [A0, C0, E0, c0, V0, R1] using hkdef
  have hkroot : ∀ a : k, H.eval a = 0 → k1.eval a = 0 := by
    intro a ha
    have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
      phi1 S.gamma S.epsilon a hW hPhi ha
    have hw1root : w1.eval a = 0 := by
      have h := congrArg (fun f : k[X] => f.eval a) hw2
      simpa [ha] using h
    rw [hkcanonical]
    have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
      phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
    dsimp only [c0, V0, R1] at hk0
    rw [hcoords.1, hw1root] at hk0
    have hp0 : phi1.eval a = 0 := by
      have he := congrArg (fun P : k[X] => P.eval a) hphi2
      simpa [ha] using he
    rw [hp0] at hk0
    simpa using hk0
  have hkDvd : H ∣ k1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkroot
  obtain ⟨k2, hk2⟩ := hkDvd
  have hI4q : b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 := by
    rw [hphi2] at hI4next
    apply mul_left_cancel₀ hH
    linear_combination hI4next
  have hrow' : H * b2 * w2 *
      terminalEDerivativeNumerator68 H E0 - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0] using hrowNext
  have hrowq : b2 * w2 * terminalEDerivativeNumerator68 H E0 -
      d2 * k2 = C j * H ^ 3 := by
    rw [hk2] at hrow'
    apply mul_left_cancel₀ hH
    linear_combination hrow'
  have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
    hp hp6 hg hgr ht hX hY
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hbred : terminalGReducedB68 r X Yd = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hBred, ← hb1]
  have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  have hfactor := terminalLowerZero_factor_one_68 H A0 b1 C0 d1 E0
    b2 d2 S.alpha S.gamma S.epsilon S.eta hb2 hd2
  have hlower1 : terminalLowerZeroOne68 H A0 b2 C0 d2 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    have hz : H * terminalLowerZeroOne68 H A0 b2 C0 d2 E0
        S.alpha S.gamma S.epsilon S.eta = 0 := by rw [← hfactor, hlower]
    exact (mul_eq_zero.mp hz).resolve_left hH
  exact ⟨phi2, k2, hphi2, hk2, hI4q, hrowq, hlower1⟩

end PhiDivisorSource68

end Max11DegreeRoutes
