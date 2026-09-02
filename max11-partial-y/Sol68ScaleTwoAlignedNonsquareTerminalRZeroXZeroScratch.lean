import Sol68ScaleTwoAlignedNonsquareTerminalWSplitScratch

/-! # The next invariant coefficient on the terminal `r=X=0` residual -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7000000

section TerminalRZeroXZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The first derivative of constant `I₄` on `r=X=Yd=0` is exactly the
product of `p₂` with the next odd-coordinate jet. -/
theorem terminalRZeroXZero_I4_pTwo_split_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hI4 : terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2 = 0) :
    p2.eval a = 0 ∨
      -r.derivative.eval a * p2.eval a +
        3 * H.derivative.eval a * p1.eval a = 0 := by
  have hzero :
      ((terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2).derivative).eval a = 0 := by
    rw [hI4, derivative_zero, eval_zero]
  have hfactor := terminalRZero_reduced_I4_derivative_factor_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr
  rw [hzero] at hfactor
  have hprod : p2.eval a *
      (-r.derivative.eval a * p2.eval a +
        3 * H.derivative.eval a * p1.eval a) = 0 := by
    dsimp only [terminalRZeroI4Jet68] at hfactor
    rw [hx, hy] at hfactor
    linear_combination (9 / 8 : k) * hfactor.symm
  exact mul_eq_zero.mp hprod

/-- After the nonzero-`p₂` I₄ jet is imposed, the fourth constant-I₃
coefficient is affine in `p₀`.  Thus this coefficient does not itself
force `p₂=0`; it fixes the next free coordinate. -/
theorem terminalRZeroXZero_reduced_I3_fourthDerivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0) :
    (((((terminalGReducedI3ScaledPolynomial68 H
      (terminalGReducedA68 H r X)
      (H * terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (H * terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      gamma epsilon).derivative).derivative).derivative).derivative).eval a =
        (16 / 9 : k) * (H.derivative.eval a) ^ 3 * p2.eval a *
          (27 * H.derivative.eval a * epsilon +
            36 * H.derivative.eval a * p0.eval a -
              4 * X.derivative.eval a * p2.eval a) := by
  simp only [terminalGReducedI3ScaledPolynomial68, terminalGReducedA68,
    terminalGReducedB68, terminalGReducedC68, terminalGReducedD68,
    terminalGReducedE68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hr, hx, hy, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow]
  linear_combination
    (32 / 9 : k) * (H.derivative.eval a) ^ 2 *
      ((-r.derivative.eval a * p2.eval a +
          3 * H.derivative.eval a * p1.eval a) -
        r.derivative.eval a * p2.eval a) * hlin

theorem terminalRZeroXZero_I3_affine_pZero_68
    (H r X Yd p0 p1 p2 : k[X]) (gamma epsilon i3 a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hI3 : terminalGReducedI3ScaledPolynomial68 H
      (terminalGReducedA68 H r X)
      (H * terminalGReducedB68 r X Yd)
      (terminalGReducedC68 H r X Yd p2)
      (H * terminalGReducedD68 H r X Yd p1 p2)
      (terminalGReducedE68 H r X Yd p0 p1 p2)
      gamma epsilon = C i3 * H ^ 5) :
    27 * H.derivative.eval a * epsilon +
        36 * H.derivative.eval a * p0.eval a -
          4 * X.derivative.eval a * p2.eval a = 0 := by
  have hzero :
      (((((terminalGReducedI3ScaledPolynomial68 H
        (terminalGReducedA68 H r X)
        (H * terminalGReducedB68 r X Yd)
        (terminalGReducedC68 H r X Yd p2)
        (H * terminalGReducedD68 H r X Yd p1 p2)
        (terminalGReducedE68 H r X Yd p0 p1 p2)
        gamma epsilon).derivative).derivative).derivative).derivative).eval a =
          0 := by
    rw [hI3]
    simp only [derivative_add, derivative_mul, derivative_pow, derivative_C,
      derivative_ofNat, C_ofNat_poly, eval_add, eval_mul, eval_pow, eval_C,
      eval_ofNat, eval_zero, ha, zero_mul, mul_zero, zero_add, add_zero,
      zero_pow]
    ring
  rw [terminalRZeroXZero_reduced_I3_fourthDerivative_factor_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr hx hy hh hlin] at hzero
  have hc : (16 / 9 : k) * (H.derivative.eval a) ^ 3 * p2.eval a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hh)) hu
  exact (mul_eq_zero.mp hzero).resolve_left hc

end TerminalRZeroXZeroAlgebra68

section TerminalRZeroXZeroSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing refinement of the only residual from `terminalWSplitSourcePacket`.
If `W` is nonzero at a core root, then `r=X=Yd=0`, `p₂` is nonzero, the
next odd jet vanishes, and constant `I₃` fixes `p₀` affinely. -/
theorem NonsquareAlignedSourceCurveData68.terminalRZeroXZeroSourcePacket
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
          (w1.eval a = 0 ∨
            (r.eval a = 0 ∧ X.eval a = 0 ∧ Yd.eval a = 0 ∧
              (p.coeff 2).eval a ≠ 0 ∧
              -r.derivative.eval a * (p.coeff 2).eval a +
                3 * H.derivative.eval a * (p.coeff 1).eval a = 0 ∧
              27 * H.derivative.eval a * S.epsilon +
                36 * H.derivative.eval a * (p.coeff 0).eval a -
                  4 * X.derivative.eval a * (p.coeff 2).eval a = 0))) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, hg, hr, ht, hX, hY, hb1, hd1,
      hw1, hroots, _hdvdRW, _hdvdXW⟩ :=
    S.terminalWSplitSourcePacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
  obtain ⟨g0, r0, t0, b10, d10, w10, phi1, hg0, hr0, ht0, hb10, hd10,
      hw10, hphi1, hI40⟩ :=
    S.terminalI4_quotientPacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
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
  have hbb : b10 = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hb10, ← hb1, htt, hrr]
  have hdd : d10 = d1 := by
    apply mul_left_cancel₀ hH
    rw [← hd10, ← hd1, htt, hrr]
  have hww : w10 = w1 := by
    apply mul_left_cancel₀ hH
    rw [← hw10, ← hw1, htt, hrr]
  have hI4 : b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 := by
    simpa only [hbb, hdd, hww] using hI40
  have hphi : cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon = H * phi1 := by
    simpa only [htt, hrr] using hphi1
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi
  rcases hfactor with ⟨hbform, hdform, hwform, hphiform⟩
  have hI4R : terminalGReducedB68 r X Yd *
        terminalGReducedPhi68 H r X Yd (p.coeff 0) (p.coeff 1)
          (p.coeff 2) S.gamma S.epsilon +
      (6 : k[X]) * terminalGReducedW68 H r X Yd (p.coeff 2) S.gamma *
        terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) = 0 := by
    rw [hbform, hdform, hwform, hphiform] at hI4
    exact hI4
  obtain ⟨i3, hI3source⟩ :=
    S.terminalI3_cleared_source_identity (H := H) hp hp6 hg hr ht
  obtain ⟨hAR, hBnum, hCR, hDnum, hER⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  rw [hAR, hBnum, hCR, hDnum, hER] at hI3source
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  refine ⟨g, r, t, X, Yd, b1, d1, w1, hg, hr, ht, hX, hY, hb1, hd1,
    hw1, ?_⟩
  intro a ha
  have hroot := hroots a ha
  refine ⟨hroot.1, hroot.2.1, ?_⟩
  rcases hroot.2.2 with hwzero | hrx
  · exact Or.inl hwzero
  · rcases eq_or_ne (w1.eval a) 0 with hwzero | hwne
    · exact Or.inl hwzero
    · right
      have hba := congrArg (fun f : k[X] => f.eval a) hbform
      have hwa := congrArg (fun f : k[X] => f.eval a) hwform
      simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
        eval_ofNat, ha, zero_mul, zero_add, zero_sub] at hba hwa
      rw [hroot.1, hrx.1, hrx.2] at hba
      rw [hrx.1, hrx.2] at hwa
      have hyzero : Yd.eval a = 0 := by
        have hc : (1 / 27 : k) ≠ 0 := by norm_num
        simpa using (mul_eq_zero.mp hba.symm).resolve_left hc
      have hwvalue : w1.eval a = (4 / 9 : k) * (p.coeff 2).eval a := by
        simpa using hwa
      have hu : (p.coeff 2).eval a ≠ 0 := by
        intro hu0
        apply hwne
        rw [hwvalue, hu0]
        ring
      have hlinSplit := terminalRZeroXZero_I4_pTwo_split_68
        H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
        S.gamma S.epsilon a ha hrx.1 hrx.2 hyzero hI4R
      have hlin := hlinSplit.resolve_left hu
      have haff := terminalRZeroXZero_I3_affine_pZero_68
        H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
        S.gamma S.epsilon i3 a ha hrx.1 hrx.2 hyzero
        (hsimple a ha) hu hlin hI3source
      exact ⟨hrx.1, hrx.2, hyzero, hu, hlin, haff⟩

end TerminalRZeroXZeroSource68

end Max11DegreeRoutes
