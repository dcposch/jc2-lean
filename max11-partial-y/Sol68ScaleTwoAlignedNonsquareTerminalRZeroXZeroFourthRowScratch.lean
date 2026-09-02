import Sol68ScaleTwoAlignedNonsquareTerminalRZeroXZeroLastRowScratch

/-! # One order beyond the terminal zero-defect last-row packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7000000

section TerminalRZeroXZeroFourthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The cleared `E` derivative starts in order four on the literal
`r=X=Yd=0` root component. -/
theorem terminalRZeroXZero_eDot_lowJets_68
    (H r X Yd p0 p1 p2 : k[X]) (a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0) :
    let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
    eDot.eval a = 0 ∧ eDot.derivative.eval a = 0 ∧
      eDot.derivative.derivative.eval a = 0 ∧
      eDot.derivative.derivative.derivative.eval a = 0 := by
  dsimp only
  simp only [terminalGReducedEDot68, terminalEDerivativeNumerator68,
    terminalGReducedE68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hr, hx, hy, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The next transverse quotient has a nonzero first coefficient precisely
because `p₂` is nonzero. -/
theorem terminalRZeroXZero_kOne_derivative_factor_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0) :
    (terminalGReducedKOne68 H r X Yd p0 p1 p2
      alpha gamma epsilon eta).derivative.eval a =
        -(4 / 9 : k) * (H.derivative.eval a) ^ 2 * (p2.eval a) ^ 2 := by
  simp only [terminalGReducedKOne68, terminalGReducedA68,
    terminalGReducedB68, terminalGReducedC68, terminalGReducedD68,
    terminalGReducedE68, terminalGReducedW68, terminalGReducedPhi68,
    terminalKDotNext68, terminalCShiftNumerator68, terminalVNumerator68,
    terminalKDotLoadQuotient68, derivative_add, derivative_sub,
    derivative_neg, derivative_mul, derivative_pow, derivative_C,
    derivative_ofNat, C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_C, eval_ofNat, eval_zero, ha, hr, hx, hy, zero_mul,
    mul_zero, zero_add, add_zero, zero_pow]
  ring

/-- Sparse fourth-product rule after the zeroes already supplied by the
zero-defect packet. -/
theorem eval_fourthDerivative_triple_sub_product_sparse_68
    (b w e d z : k[X]) (a : k)
    (hb0 : b.eval a = 0)
    (he0 : e.eval a = 0) (he1 : e.derivative.eval a = 0)
    (he2 : e.derivative.derivative.eval a = 0)
    (he3 : e.derivative.derivative.derivative.eval a = 0)
    (hd0 : d.eval a = 0) (hd1 : d.derivative.eval a = 0)
    (hd2 : d.derivative.derivative.eval a = 0)
    (hz0 : z.eval a = 0) :
    (((((b * w * e - d * z).derivative).derivative).derivative).derivative).eval a =
      -4 * d.derivative.derivative.derivative.eval a *
        z.derivative.eval a := by
  simp only [derivative_add, derivative_sub, derivative_mul, eval_add,
    eval_sub, eval_mul, hb0, he0, he1, he2, he3, hd0, hd1, hd2, hz0,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub]
  ring

/-- The previous second-jet scalar is exactly `3H' D''`. -/
theorem terminalRZeroXZero_D_second_zero_68
    (H r X Yd p1 p2 : k[X]) (a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hsecond :
      -H.derivative.eval a * r.derivative.derivative.eval a * p2.eval a +
        H.derivative.derivative.eval a * r.derivative.eval a * p2.eval a -
        2 * H.derivative.eval a * r.derivative.eval a * p2.derivative.eval a +
        6 * (H.derivative.eval a) ^ 2 * p1.derivative.eval a = 0) :
    (terminalGReducedD68 H r X Yd p1 p2).derivative.derivative.eval a = 0 := by
  have hfac : 3 * H.derivative.eval a *
      (terminalGReducedD68 H r X Yd p1 p2).derivative.derivative.eval a =
        -H.derivative.eval a * r.derivative.derivative.eval a * p2.eval a +
          H.derivative.derivative.eval a * r.derivative.eval a * p2.eval a -
          2 * H.derivative.eval a * r.derivative.eval a *
            p2.derivative.eval a +
          6 * (H.derivative.eval a) ^ 2 * p1.derivative.eval a := by
    simp only [terminalGReducedD68, derivative_add, derivative_sub,
      derivative_neg, derivative_mul, derivative_pow, derivative_C,
      derivative_ofNat, C_ofNat_poly, eval_add, eval_sub, eval_neg,
      eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero, ha, hr, hx, hy,
      zero_mul, mul_zero, zero_add, add_zero, zero_pow]
    linear_combination
      (H.derivative.derivative.eval a) * hlin
  rw [hsecond] at hfac
  exact (mul_eq_zero.mp hfac).resolve_left
    (mul_ne_zero (by norm_num) hh)

/-- The fourth derivative of the actual descended row has a nonzero
`p₂²` transverse factor, so the reduced odd coordinate gains one more
local order. -/
theorem terminalRZeroXZero_lastRow_D_third_zero_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta j a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hx : X.eval a = 0) (hy : Yd.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hsecond :
      -H.derivative.eval a * r.derivative.derivative.eval a * p2.eval a +
        H.derivative.derivative.eval a * r.derivative.eval a * p2.eval a -
        2 * H.derivative.eval a * r.derivative.eval a * p2.derivative.eval a +
        6 * (H.derivative.eval a) ^ 2 * p1.derivative.eval a = 0)
    (hrow :
      let b := terminalGReducedB68 r X Yd
      let d := terminalGReducedD68 H r X Yd p1 p2
      let w := terminalGReducedW68 H r X Yd p2 gamma
      let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
      let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
        alpha gamma epsilon eta
      b * w * eDot - d * k1 = C j * H ^ 5) :
    (terminalGReducedD68 H r X Yd p1 p2).derivative.derivative.derivative.eval a =
      0 := by
  let b := terminalGReducedB68 r X Yd
  let d := terminalGReducedD68 H r X Yd p1 p2
  let w := terminalGReducedW68 H r X Yd p2 gamma
  let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
  let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
    alpha gamma epsilon eta
  have hb0 : b.eval a = 0 := by
    dsimp only [b, terminalGReducedB68]
    simp [hr, hx, hy]
  obtain ⟨he0, he1, he2, he3⟩ :=
    terminalRZeroXZero_eDot_lowJets_68 H r X Yd p0 p1 p2 a ha hr hx hy
  obtain ⟨_he0old, _he1old, hd0, hk0⟩ :=
    terminalRZero_reduced_lastRow_rootZeroes_68
      H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr
  have hd1 : d.derivative.eval a = 0 := by
    dsimp only [d, terminalGReducedD68]
    simp only [derivative_add, derivative_sub, derivative_neg,
      derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
      C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow,
      eval_C, eval_ofNat, eval_zero, ha, hr, hx, hy, zero_mul, mul_zero,
      zero_add, add_zero, zero_pow]
    linear_combination (1 / 3 : k) * hlin
  have hd2 : d.derivative.derivative.eval a = 0 := by
    dsimp only [d]
    exact terminalRZeroXZero_D_second_zero_68
      H r X Yd p1 p2 a ha hr hx hy hh hlin hsecond
  have hsourceZero :
      (((((b * w * eDot - d * k1).derivative).derivative).derivative).derivative).eval a =
        0 := by
    dsimp only [b, d, w, eDot, k1] at hrow ⊢
    rw [hrow]
    simp only [derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
      eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
      ha, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
    ring
  have hsparse := eval_fourthDerivative_triple_sub_product_sparse_68
    b w eDot d k1 a hb0 he0 he1 he2 he3 hd0 hd1 hd2 hk0
  rw [hsourceZero] at hsparse
  have hkprime : k1.derivative.eval a =
      -(4 / 9 : k) * (H.derivative.eval a) ^ 2 * (p2.eval a) ^ 2 := by
    dsimp only [k1]
    exact terminalRZeroXZero_kOne_derivative_factor_68
      H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr hx hy
  rw [hkprime] at hsparse
  have hcoeff : (16 / 9 : k) * (H.derivative.eval a) ^ 2 *
      (p2.eval a) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh))
      (pow_ne_zero 2 hu)
  have hprod : (16 / 9 : k) * (H.derivative.eval a) ^ 2 *
      (p2.eval a) ^ 2 * d.derivative.derivative.derivative.eval a = 0 := by
    linear_combination hsparse.symm
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff

end TerminalRZeroXZeroFourthAlgebra68

section TerminalRZeroXZeroFourthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Full source transport of the fourth descended-row coefficient.  On the
only nonzero-`W` residual, the reduced odd `D` coordinate has vanishing
value and first three derivatives. -/
theorem NonsquareAlignedSourceCurveData68.terminalRZeroXZeroFourthRowSourcePacket
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
                  4 * X.derivative.eval a * (p.coeff 2).eval a = 0 ∧
              -H.derivative.eval a * r.derivative.derivative.eval a *
                  (p.coeff 2).eval a +
                H.derivative.derivative.eval a * r.derivative.eval a *
                  (p.coeff 2).eval a -
                2 * H.derivative.eval a * r.derivative.eval a *
                  (p.coeff 2).derivative.eval a +
                6 * (H.derivative.eval a) ^ 2 *
                  (p.coeff 1).derivative.eval a = 0 ∧
              (terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2)).derivative.derivative.derivative.eval a =
                0))) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, hg, hr, ht, hX, hY, hb1, hd1,
      hw1, hroots⟩ :=
    S.terminalRZeroXZeroLastRowSourcePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac
  obtain ⟨g0, r0, t0, X0, Yd0, b10, d10, w10, phi1, k1,
      hg0, hr0, ht0, hX0, hY0, hb10, hd10, hw10, hphi10,
      hkdef0, hrow0, _hbranches0⟩ :=
    S.terminalKOneNextSourcePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac
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
  have hww : w10 = w1 := by
    apply mul_left_cancel₀ hH
    rw [← hw10, ← hw1, htt, hrr]
  have hphi : cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon = H * phi1 := by
    simpa only [htt, hrr] using hphi10
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi
  rcases hfactor with ⟨hbform, hdform, hwform, hphiform⟩
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
    dsimp only [A0, C0, E0, c0, V0, R1]
    simpa only [hbb, hdd, hww, htt, hrr] using hkdef0
  have hrow5 : b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    dsimp only [A0, C0, E0, eDot]
    simpa only [hbb, hdd, hww, htt, hrr] using hrow0
  obtain ⟨hAR, _hBnum, hCR, _hDnum, hER⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
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
  have hrowR : bR * wR * eR - dR * kR = C j * H ^ 5 := by
    simpa only [← hbR, ← hwR, ← heR, ← hdR, ← hkR] using hrow5
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  refine ⟨g, r, t, X, Yd, b1, d1, w1, hg, hr, ht, hX, hY, hb1, hd1,
    hw1, ?_⟩
  intro a ha
  have hpkt := hroots a ha
  refine ⟨hpkt.1, hpkt.2.1, ?_⟩
  rcases hpkt.2.2 with hwzero | hres
  · exact Or.inl hwzero
  · right
    refine ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1,
      hres.2.2.2.2.1, hres.2.2.2.2.2.1, hres.2.2.2.2.2.2, ?_⟩
    exact terminalRZeroXZero_lastRow_D_third_zero_68
      H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
      S.alpha S.gamma S.epsilon S.eta j a ha hres.1 hres.2.1
      hres.2.2.1 (hsimple a ha) hres.2.2.2.1
      hres.2.2.2.2.1 hres.2.2.2.2.2.2 hrowR

end TerminalRZeroXZeroFourthSource68

end Max11DegreeRoutes
