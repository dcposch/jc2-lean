import Sol68ScaleTwoAlignedNonsquareTerminalDDescentScratch

/-! # The W split after aligned-nonsquare B/D descent -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalWSplitAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- At `B=0`, either old transverse allocation makes `W=0`; only `r=0`
can retain the literal value `W=4p₂/9`. -/
theorem terminalW_split_of_B_zero_and_allocations_68
    (r X Yd p2 w : k)
    (hb : 0 = (1 / 27 : k) * (Yd - 6 * r * X))
    (hw : w = (4 / 9 : k) * p2 - (2 / 243 : k) * r * Yd +
      (8 / 243 : k) * r ^ 2 * X)
    (halloc : r = 0 ∨
      (9 * r ^ 2 * X - 2 * r * Yd + 81 * p2 = 0) ∨
      (3 * r ^ 2 * X - r * Yd + 81 * p2 = 0)) :
    (r = 0 ∧ w = (4 / 9 : k) * p2) ∨ w = 0 := by
  have hb0 : Yd - 6 * r * X = 0 := by
    have hc : (1 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hb.symm).resolve_left hc
  rcases halloc with hr | hF | hG
  · left
    refine ⟨hr, ?_⟩
    rw [hw, hr]
    ring
  · right
    rw [hw]
    linear_combination (4 / 729 : k) * hF +
      (2 / 729 : k) * r * hb0
  · right
    rw [hw]
    linear_combination (4 / 729 : k) * hG +
      (-2 / 729 : k) * r * hb0

end TerminalWSplitAlgebra68

section TerminalRZeroBZeroI3Algebra68

variable {k : Type*} [Field k] [CharZero k]

/-- On the remaining `r=Yd=0` sibling, the first informative constant-I3
coefficient is `X·p₂²`; there is still no fresh lower jet. -/
theorem terminalRZeroYZero_reduced_I3_thirdDerivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0) (hy : Yd.eval a = 0) :
    (((terminalGReducedI3ScaledPolynomial68 H
      (terminalGReducedA68 H r X)
      (H * terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (H * terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      gamma epsilon).derivative).derivative).derivative.eval a =
        -(16 / 9 : k) * (H.derivative.eval a) ^ 3 *
          X.eval a * (p2.eval a) ^ 2 := by
  simp only [terminalGReducedI3ScaledPolynomial68, terminalGReducedA68,
    terminalGReducedB68, terminalGReducedC68, terminalGReducedD68,
    terminalGReducedE68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hr, hy, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

theorem terminalRZeroYZero_I3_split_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon i3 a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0)
    (hI3 : terminalGReducedI3ScaledPolynomial68 H
      (terminalGReducedA68 H r X)
      (H * terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (H * terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      gamma epsilon = C i3 * H ^ 5) :
    p2.eval a = 0 ∨ X.eval a = 0 := by
  have hzero :
      (((terminalGReducedI3ScaledPolynomial68 H
        (terminalGReducedA68 H r X)
        (H * terminalGReducedB68 r X Yd)
        (terminalGReducedC68 H r X Yd p2)
        (H * terminalGReducedD68 H r X Yd p1 p2)
        (terminalGReducedE68 H r X Yd p0 p1 p2)
        gamma epsilon).derivative).derivative).derivative.eval a = 0 := by
    rw [hI3]
    simp only [derivative_add, derivative_mul, derivative_pow, derivative_C,
      derivative_ofNat, C_ofNat_poly, eval_add, eval_mul, eval_pow, eval_C,
      eval_ofNat, eval_zero, ha, zero_mul, mul_zero, zero_add, add_zero,
      zero_pow]
    ring
  rw [terminalRZeroYZero_reduced_I3_thirdDerivative_factor_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr hy] at hzero
  have hc : -(16 / 9 : k) * (H.derivative.eval a) ^ 3 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 3 hh)
  rcases mul_eq_zero.mp hzero with hcx | hu2
  · exact Or.inr ((mul_eq_zero.mp hcx).resolve_left hc)
  · left
    by_contra hu
    exact (pow_ne_zero 2 hu) hu2

end TerminalRZeroBZeroI3Algebra68

section TerminalWSplitSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Finite next packet: every core root either gains `W=0`, or lies on the
sharp residual `r=X=0`.  Consequently both `rW` and `XW` gain a full core
factor globally. -/
theorem NonsquareAlignedSourceCurveData68.terminalWSplitSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t X Yd b1 d1 w1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      (∀ a : k, H.eval a = 0 →
        b1.eval a = 0 ∧ d1.eval a = 0 ∧
          (w1.eval a = 0 ∨ (r.eval a = 0 ∧ X.eval a = 0))) ∧
      H ∣ r * w1 ∧ H ∣ X * w1 := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, hg, hr, ht, hX, hY,
      hb1, hd1, hw1, hphi1, hkdef, hrowdef, hbranches⟩ :=
    S.terminalKOneNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  obtain ⟨g0, r0, t0, X0, Yd0, b10, d10, hg0, hr0, ht0, hX0, hY0,
      hb10, hd10, hrootsBD0, _hdb0, _hdd0, _hsb0, _hsd0⟩ :=
    S.terminalDDescentSourcePacket (H := H) hdeg hp hq hp6 hq8
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
  have hdd : d10 = d1 := by
    apply mul_left_cancel₀ hH
    rw [← hd10, ← hd1, htt, hrr]
  have hrootsBD : ∀ a : k, H.eval a = 0 →
      b1.eval a = 0 ∧ d1.eval a = 0 := by
    intro a ha
    simpa only [hbb, hdd] using hrootsBD0 a ha
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi1
  rcases hfactor with ⟨hbform, _hdform, hwform, _hphiform⟩
  obtain ⟨i3, hI3source⟩ :=
    S.terminalI3_cleared_source_identity (H := H) hp hp6 hg hr ht
  obtain ⟨hAR, hBnum, hCR, hDnum, hER⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  rw [hAR, hBnum, hCR, hDnum, hER] at hI3source
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hrootPacket : ∀ a : k, H.eval a = 0 →
      b1.eval a = 0 ∧ d1.eval a = 0 ∧
        (w1.eval a = 0 ∨ (r.eval a = 0 ∧ X.eval a = 0)) := by
    intro a ha
    have hbd := hrootsBD a ha
    have hba := congrArg (fun f : k[X] => f.eval a) hbform
    have hwa := congrArg (fun f : k[X] => f.eval a) hwform
    simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
      eval_ofNat, ha, zero_mul, zero_add, zero_sub] at hba hwa
    rw [hbd.1] at hba
    have hwa' : w1.eval a = (4 / 9 : k) * (p.coeff 2).eval a -
        (2 / 243 : k) * r.eval a * Yd.eval a +
          (8 / 243 : k) * (r.eval a) ^ 2 * X.eval a := by
      simpa only [add_zero] using hwa
    have halloc : r.eval a = 0 ∨
        (9 * (r.eval a) ^ 2 * X.eval a -
          2 * r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∨
        (3 * (r.eval a) ^ 2 * X.eval a -
          r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) := by
      rcases hbranches a ha with hrzero | hF | hG
      · exact Or.inl hrzero
      · exact Or.inr (Or.inl hF.1)
      · exact Or.inr (Or.inr hG.1)
    have hwSplit := terminalW_split_of_B_zero_and_allocations_68
      (r.eval a) (X.eval a) (Yd.eval a) ((p.coeff 2).eval a)
      (w1.eval a) hba hwa' halloc
    refine ⟨hbd.1, hbd.2, ?_⟩
    rcases hwSplit with ⟨hrzero, hwvalue⟩ | hwzero
    · have hyzero : Yd.eval a = 0 := by
        have hc : (1 / 27 : k) ≠ 0 := by norm_num
        have hbscalar := (mul_eq_zero.mp hba.symm).resolve_left hc
        rw [hrzero] at hbscalar
        simpa using hbscalar
      have hI3split := terminalRZeroYZero_I3_split_68
        H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
        S.gamma S.epsilon i3 a ha hrzero hyzero (hsimple a ha) hI3source
      rcases hI3split with hu0 | hx0
      · left
        rw [hwvalue, hu0]
        ring
      · exact Or.inr ⟨hrzero, hx0⟩
    · exact Or.inl hwzero
  have hdvdRW : H ∣ r * w1 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    rcases (hrootPacket a ha).2.2 with hw0 | hrx
    · simp [eval_mul, hw0]
    · simp [eval_mul, hrx.1]
  have hdvdXW : H ∣ X * w1 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    rcases (hrootPacket a ha).2.2 with hw0 | hrx
    · simp [eval_mul, hw0]
    · simp [eval_mul, hrx.2]
  exact ⟨g, r, t, X, Yd, b1, d1, w1, hg, hr, ht, hX, hY, hb1, hd1,
    hw1, hrootPacket, hdvdRW, hdvdXW⟩

end TerminalWSplitSource68

end Max11DegreeRoutes
