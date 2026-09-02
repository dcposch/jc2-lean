import Sol68ScaleTwoAlignedNonsquareTerminalMixedRootsI3SourceScratch

/-! # Exported aligned-nonsquare terminal I3 assembly -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalI3Assembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Constant `I₃` removes the last `r=0,b₁≠0` allocation.  Thus the odd
terminal quotient vanishes at both simple core roots, is divisible by `H`,
and the original cleared odd numerator is divisible by `H²`. -/
theorem NonsquareAlignedSourceCurveData68.terminalGNextI3SourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t X Yd b1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      (∀ a : k, H.eval a = 0 → b1.eval a = 0) ∧
      H ∣ b1 ∧ H ^ 2 ∣ cubicBNumerator68 (p.coeff 3) t r := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, hg, hr, ht, hX, hY,
      hb1, hd1, hw1, hphi1, hkdef, hrowdef, _hbranches⟩ :=
    S.terminalKOneNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  obtain ⟨g0, r0, t0, X0, Yd0, b10, hg0, hr0, ht0, hX0, hY0,
      hb10, hroot0, _hdvd0⟩ :=
    S.terminalGNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgg : g0 = g := by
    apply mul_left_cancel₀ hH
    rw [← hg0, ← hg]
  have hrr : r0 = r := by
    apply mul_left_cancel₀ hH
    rw [← hr0, ← hr, hgg]
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
  have hrootOld : ∀ a : k, H.eval a = 0 →
      r.eval a = 0 ∨ b1.eval a = 0 := by
    intro a ha
    simpa only [hrr, hbb] using hroot0 a ha
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
    simpa only [A0, C0, E0, c0, V0, R1] using hkdef
  have hrow5 : b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    simpa only [A0, C0, E0, eDot] using hrowdef
  have hI4source := S.terminalI4_cleared_source_identity (H := H)
    hp hp6 hg hr ht
  rw [hb1, hd1, hw1, hphi1] at hI4source
  have hI4factor : H ^ 2 * (b1 * phi1 + (6 : k[X]) * w1 * d1) = 0 := by
    linear_combination hI4source
  have hI4 : b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 :=
    (mul_eq_zero.mp hI4factor).resolve_left (pow_ne_zero 2 hH)
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi1
  rcases hfactor with ⟨hbform, hdform, hwform, hphiform⟩
  let AR := terminalGReducedA68 H r X
  let bR := terminalGReducedB68 r X Yd
  let CR := terminalGReducedC68 H r X Yd (p.coeff 2)
  let dR := terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2)
  let ER := terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2)
  let wR := terminalGReducedW68 H r X Yd (p.coeff 2) S.gamma
  let phiR := terminalGReducedPhi68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2) S.gamma S.epsilon
  let eR := terminalGReducedEDot68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2)
  let kR := terminalGReducedKOne68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2) S.alpha S.gamma S.epsilon S.eta
  have hbR : b1 = bR := by
    simpa only [bR, terminalGReducedB68] using hbform
  have hdR : d1 = dR := by
    simpa only [dR, terminalGReducedD68] using hdform
  have hwR : w1 = wR := by
    simpa only [wR, terminalGReducedW68] using hwform
  have hphiR : phi1 = phiR := by
    simpa only [phiR, terminalGReducedPhi68] using hphiform
  obtain ⟨hAR, hBnum, hCR, hDnum, hER⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hA0R : A0 = AR := by simpa only [A0, AR] using hAR
  have hC0R : C0 = CR := by simpa only [C0, CR] using hCR
  have hE0R : E0 = ER := by simpa only [E0, ER] using hER
  have heR : eDot = eR := by
    dsimp only [eDot, eR, terminalGReducedEDot68]
    rw [hE0R]
  have hkR : k1 = kR := by
    rw [hkcanonical]
    dsimp only [kR, terminalGReducedKOne68]
    rw [show terminalGReducedA68 H r X = A0 from hA0R.symm,
      show terminalGReducedB68 r X Yd = b1 from hbR.symm,
      show terminalGReducedC68 H r X Yd (p.coeff 2) = C0 from hC0R.symm,
      show terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) = d1
        from hdR.symm,
      show terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1)
          (p.coeff 2) = E0 from hE0R.symm,
      show terminalGReducedW68 H r X Yd (p.coeff 2) S.gamma = w1
        from hwR.symm,
      show terminalGReducedPhi68 H r X Yd (p.coeff 0) (p.coeff 1)
          (p.coeff 2) S.gamma S.epsilon = phi1 from hphiR.symm]
  have hI4R : bR * phiR + (6 : k[X]) * wR * dR = 0 := by
    simpa only [← hbR, ← hphiR, ← hwR, ← hdR] using hI4
  have hrowR : bR * wR * eR - dR * kR = C j * H ^ 5 := by
    simpa only [← hbR, ← hwR, ← heR, ← hdR, ← hkR] using hrow5
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hroot : ∀ a : k, H.eval a = 0 → b1.eval a = 0 := by
    intro a ha
    rcases hrootOld a ha with hrzero | hbzero
    · by_contra hbne
      have hbRne : bR.eval a ≠ 0 := by simpa only [← hbR] using hbne
      have hrigid := terminalRZero_reduced_nonzeroB_packet_68
        H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
        S.alpha S.gamma S.epsilon S.eta j a ha hrzero (hsimple a ha)
        hbRne hI4R hrowR
      obtain ⟨hu, _hlin, hquad⟩ := hrigid
      have hy : Yd.eval a ≠ 0 := by
        intro hy0
        apply hbRne
        dsimp only [bR, terminalGReducedB68]
        simp only [eval_mul, eval_sub, eval_C, eval_ofNat, hrzero, hy0,
          zero_mul, sub_zero]
        ring
      exact S.terminalRZero_nonzeroB_impossible_I3 (H := H)
        hdeg hp hp6 hg hr ht hX hY a ha hrzero hy hu hquad
    · exact hbzero
  have hdvd : H ∣ b1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hroot
  have hsq : H ^ 2 ∣ cubicBNumerator68 (p.coeff 3) t r :=
    terminalB_sq_dvd_of_all_quotient_roots_68 H
      (cubicBNumerator68 (p.coeff 3) t r) b1 hdeg hsimple hb1 hroot
  exact ⟨g, r, t, X, Yd, b1, hg, hr, ht, hX, hY, hb1, hroot, hdvd, hsq⟩

end TerminalI3Assembly68

end Max11DegreeRoutes
