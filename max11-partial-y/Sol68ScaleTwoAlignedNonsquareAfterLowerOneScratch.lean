import Sol68ScaleTwoAlignedNonsquareTerminalLowerOneTransportScratch

/-! # The aligned nonsquare packet after the lower-row transport -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalAfterLowerOneAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Once both the odd `B` quotient and `W` quotient gain a second core
factor, their explicit formulas force the next even-coordinate descent. -/
theorem terminalAfterLowerOne_p2_descent_identity_68
    (H r X Yd p2 b w b2 w2 : k[X]) (gamma : k)
    (hbform : b = terminalGReducedB68 r X Yd)
    (hwform : w = terminalGReducedW68 H r X Yd p2 gamma)
    (hb : b = H * b2) (hw : w = H * w2) :
    (27 : k[X]) * p2 - r ^ 2 * X =
      H * (C (243 / 4 : k) * w2 + C (27 / 2 : k) * r * b2 + X ^ 2 -
        C (243 / 4 : k) * C (2 / 3 * gamma : k)) := by
  have hscale243 : (4 : k[X]) * C (243 / 4 : k) = 243 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have hscale54 : (4 : k[X]) * C (27 / 2 : k) = 54 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have h49 : (243 : k[X]) * C (4 / 9 : k) = 108 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have h2243 : (243 : k[X]) * C (2 / 243 : k) = 2 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have h8243 : (243 : k[X]) * C (8 / 243 : k) = 8 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have h4243 : (243 : k[X]) * C (4 / 243 : k) = 4 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have h127 : (54 : k[X]) * C (1 / 27 : k) = 2 := by
    rw [← C_ofNat_poly, ← C_ofNat_poly, ← map_mul]
    congr 1
    ring
  have hid :
      (4 : k[X]) * ((27 : k[X]) * p2 - r ^ 2 * X) =
        (243 : k[X]) * w + (54 : k[X]) * r * b +
          H * ((4 : k[X]) * X ^ 2 -
            C (2 / 3 * gamma : k) * (243 : k[X])) := by
    rw [hbform, hwform]
    simp only [terminalGReducedB68, terminalGReducedW68]
    linear_combination -p2 * h49 + r * Yd * h2243 - r * Yd * h127 -
      r ^ 2 * X * h8243 + 6 * r ^ 2 * X * h127 + H * X ^ 2 * h4243
  rw [hb, hw] at hid
  apply mul_left_cancel₀ (show (4 : k[X]) ≠ 0 by norm_num)
  calc
    (4 : k[X]) * ((27 : k[X]) * p2 - r ^ 2 * X) =
        (243 : k[X]) * (H * w2) + (54 : k[X]) * r * (H * b2) +
          H * ((4 : k[X]) * X ^ 2 -
            C (2 / 3 * gamma : k) * (243 : k[X])) := hid
    _ = (4 : k[X]) *
        (H * (C (243 / 4 : k) * w2 + C (27 / 2 : k) * r * b2 + X ^ 2 -
          C (243 / 4 : k) * C (2 / 3 * gamma : k))) := by
      rw [show (243 : k[X]) = (4 : k[X]) * C (243 / 4 : k)
          from hscale243.symm]
      rw [show (54 : k[X]) = (4 : k[X]) * C (27 / 2 : k)
          from hscale54.symm]
      ring

end TerminalAfterLowerOneAlgebra68

section TerminalAfterLowerOneSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Full finite packet on the sole sibling left by the lower-row transport.
The old `F/G` selectors have collapsed to the same two coordinate equations;
the genuinely surviving split is `b₂ Φ = 0` and `d₂ k₁ = 0`. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (g r t X Yd b1 d1 w1 phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r S.gamma S.epsilon = H * phi1 ∧
      b1 = H * b2 ∧ d1 = H * d2 ∧ w1 = H * w2 ∧
      (27 : k[X]) * p.coeff 2 - r ^ 2 * X =
        H * (C (243 / 4 : k) * w2 + C (27 / 2 : k) * r * b2 + X ^ 2 -
          C (243 / 4 : k) * C (2 / 3 * S.gamma : k)) ∧
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      ∀ a : k, H.eval a = 0 →
        Yd.eval a = 6 * r.eval a * X.eval a ∧
        27 * (p.coeff 2).eval a = (r.eval a) ^ 2 * X.eval a ∧
        (b2.eval a = 0 ∨ phi1.eval a = 0) ∧
        (d2.eval a = 0 ∨ k1.eval a = 0) := by
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
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
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
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi
  rcases hfactor with ⟨hbform, _hdform, hwform, _hphiform⟩
  have hp2desc := terminalAfterLowerOne_p2_descent_identity_68
    H r X Yd (p.coeff 2) b1 w1 b2 w2 S.gamma
    hbform hwform hb2 hw2
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
  refine ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
    hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
    hp2desc, hI4next, hrowNext, ?_⟩
  intro a ha
  have hbroot := congrArg (fun f : k[X] => f.eval a) hbform
  have hp2root := congrArg (fun f : k[X] => f.eval a) hp2desc
  have hI4root := congrArg (fun f : k[X] => f.eval a) hI4next
  have hrowRoot := congrArg (fun f : k[X] => f.eval a) hrowNext
  simp only [terminalGReducedB68, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_C, eval_ofNat, eval_zero, ha, zero_mul, mul_zero,
    zero_add, add_zero, zero_pow] at hbroot hp2root hI4root hrowRoot
  have hzeroes := hroot a ha
  rw [hzeroes.1] at hbroot
  have hYroot : Yd.eval a = 6 * r.eval a * X.eval a := by
    have hinner : Yd.eval a - 6 * r.eval a * X.eval a = 0 :=
      (mul_eq_zero.mp hbroot.symm).resolve_left (by norm_num)
    exact sub_eq_zero.mp hinner
  have hp2root' : 27 * (p.coeff 2).eval a =
      (r.eval a) ^ 2 * X.eval a := by
    linear_combination hp2root
  have hbSplit : b2.eval a = 0 ∨ phi1.eval a = 0 :=
    mul_eq_zero.mp hI4root
  have hdSplit : d2.eval a = 0 ∨ k1.eval a = 0 := by
    have hz : -(d2.eval a * k1.eval a) = 0 := by
      simpa using hrowRoot
    exact mul_eq_zero.mp (neg_eq_zero.mp hz)
  exact ⟨hYroot, hp2root', hbSplit, hdSplit⟩

end TerminalAfterLowerOneSource68

end Max11DegreeRoutes
