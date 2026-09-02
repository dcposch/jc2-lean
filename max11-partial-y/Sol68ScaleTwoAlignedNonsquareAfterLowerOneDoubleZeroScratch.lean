import Sol68ScaleTwoAlignedNonsquareAfterLowerOneComponentsScratch

/-! # Global descent of the terminal double-zero component -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalDoubleZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A polynomial vanishing to second order at both simple roots of a
quadratic is divisible by the square of that quadratic. -/
theorem sq_dvd_of_eval_derivative_zero_simple_natDegree_two_68
    (H f : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hf : ∀ a : k, H.eval a = 0 →
      f.eval a = 0 ∧ f.derivative.eval a = 0) :
    H ^ 2 ∣ f := by
  have hHf : H ∣ f :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hf a ha).1)
  obtain ⟨f1, hf1⟩ := hHf
  have hf1root : ∀ a : k, H.eval a = 0 → f1.eval a = 0 := by
    intro a ha
    have hder := congrArg (fun P : k[X] => P.derivative.eval a) hf1
    simp only [derivative_mul, eval_add, eval_mul, ha, zero_mul, add_zero]
      at hder
    exact (mul_eq_zero.mp (hder.symm.trans (hf a ha).2)).resolve_left
      (hsimple a ha)
  have hHf1 : H ∣ f1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hf1root
  obtain ⟨f2, hf2⟩ := hHf1
  refine ⟨f2, ?_⟩
  rw [hf1, hf2]
  ring

/-- Cancelling one common core factor from the descended `I4` and terminal
row.  The load is kept abstract so the lemma can be iterated up to the first
nonhomogeneous coefficient. -/
theorem terminalAfterLowerOne_cancel_one_68
    (H b d bq dq phi w eDot kap load : k[X])
    (hH : H ≠ 0) (hb : b = H * bq) (hd : d = H * dq)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0)
    (hrow : H * b * w * eDot - d * kap = H * load) :
    bq * phi + (6 : k[X]) * H * w * dq = 0 ∧
      H * bq * w * eDot - dq * kap = load := by
  rw [hb, hd] at hI4 hrow
  constructor
  · apply mul_left_cancel₀ hH
    linear_combination hI4
  · apply mul_left_cancel₀ hH
    linear_combination hrow

/-- If every core root lies on the simultaneous double-zero component,
the two quotient equations bootstrap to the sharp load wall:
`H⁵ | b₂`, `H⁴ | d₂`, and the next terminal row has nonzero constant
load.  No degree bound on the source coefficients is assumed. -/
theorem terminalAfterLowerOne_doubleZero_global_descent_68
    (H b d phi w eDot kap : k[X]) (j : k)
    (hdeg : H.natDegree = 2) (hH : H ≠ 0)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hphi : ∀ a : k, H.eval a = 0 → phi.eval a ≠ 0)
    (hkap : ∀ a : k, H.eval a = 0 → kap.eval a ≠ 0)
    (hdouble : ∀ a : k, H.eval a = 0 →
      b.eval a = 0 ∧ b.derivative.eval a = 0 ∧
      d.eval a = 0 ∧ d.derivative.eval a = 0)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0)
    (hrow : H * b * w * eDot - d * kap = C j * H ^ 4) :
    ∃ b5 d4 : k[X],
      b = H ^ 5 * b5 ∧ d = H ^ 4 * d4 ∧
      b5 * phi + (6 : k[X]) * w * d4 = 0 ∧
      H ^ 2 * b5 * w * eDot - d4 * kap = C j ∧
      ∀ a : k, H.eval a = 0 → d4.eval a * kap.eval a = -j := by
  have hbSq := sq_dvd_of_eval_derivative_zero_simple_natDegree_two_68
    H b hdeg hsimple (fun a ha => ⟨(hdouble a ha).1, (hdouble a ha).2.1⟩)
  have hdSq := sq_dvd_of_eval_derivative_zero_simple_natDegree_two_68
    H d hdeg hsimple
      (fun a ha => ⟨(hdouble a ha).2.2.1, (hdouble a ha).2.2.2⟩)
  obtain ⟨b0, hb0⟩ := hbSq
  obtain ⟨d0, hd0⟩ := hdSq
  have hbPre : b = H * (H * b0) := by rw [hb0]; ring
  have hdPre : d = H * (H * d0) := by rw [hd0]; ring
  have hrowPre : H * b * w * eDot - d * kap =
      H * (C j * H ^ 3) := by rw [hrow]; ring
  obtain ⟨hI4pre, hrowpre⟩ := terminalAfterLowerOne_cancel_one_68
    H b d (H * b0) (H * d0) phi w eDot kap (C j * H ^ 3)
    hH hbPre hdPre hI4 hrowPre
  have hrowPre2 : H * (H * b0) * w * eDot - (H * d0) * kap =
      H * (C j * H ^ 2) := by
    calc
      H * (H * b0) * w * eDot - (H * d0) * kap = C j * H ^ 3 := hrowpre
      _ = H * (C j * H ^ 2) := by ring
  obtain ⟨hI40, hrow0⟩ := terminalAfterLowerOne_cancel_one_68
    H (H * b0) (H * d0) b0 d0 phi w eDot kap (C j * H ^ 2)
    hH rfl rfl hI4pre hrowPre2
  have hb0root : ∀ a : k, H.eval a = 0 → b0.eval a = 0 := by
    intro a ha
    have h := congrArg (fun P : k[X] => P.eval a) hI40
    simp only [eval_add, eval_mul, eval_C, eval_zero, ha, zero_mul, mul_zero,
      zero_add, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (hphi a ha)
  have hd0root : ∀ a : k, H.eval a = 0 → d0.eval a = 0 := by
    intro a ha
    have h := congrArg (fun P : k[X] => P.eval a) hrow0
    simp only [eval_sub, eval_mul, eval_pow, eval_C, ha, zero_mul, mul_zero,
      zero_pow] at h
    have hz : -(d0.eval a * kap.eval a) = 0 := by simpa using h
    exact (mul_eq_zero.mp (neg_eq_zero.mp hz)).resolve_right (hkap a ha)
  have hb0dvd := dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hb0root
  have hd0dvd := dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hd0root
  obtain ⟨b1, hb1⟩ := hb0dvd
  obtain ⟨d1, hd1⟩ := hd0dvd
  have hrow0' : H * b0 * w * eDot - d0 * kap =
      H * (C j * H) := by rw [hrow0]; ring
  obtain ⟨hI41, hrow1⟩ := terminalAfterLowerOne_cancel_one_68
    H b0 d0 b1 d1 phi w eDot kap (C j * H)
    hH hb1 hd1 hI40 hrow0'
  have hb1root : ∀ a : k, H.eval a = 0 → b1.eval a = 0 := by
    intro a ha
    have h := congrArg (fun P : k[X] => P.eval a) hI41
    simp only [eval_add, eval_mul, eval_C, eval_zero, ha, zero_mul, mul_zero,
      zero_add, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (hphi a ha)
  have hd1root : ∀ a : k, H.eval a = 0 → d1.eval a = 0 := by
    intro a ha
    have h := congrArg (fun P : k[X] => P.eval a) hrow1
    simp only [eval_sub, eval_mul, eval_C, ha, zero_mul, mul_zero] at h
    have hz : -(d1.eval a * kap.eval a) = 0 := by simpa using h
    exact (mul_eq_zero.mp (neg_eq_zero.mp hz)).resolve_right (hkap a ha)
  have hb1dvd := dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hb1root
  have hd1dvd := dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hd1root
  obtain ⟨b2, hb2⟩ := hb1dvd
  obtain ⟨d4, hd4⟩ := hd1dvd
  have hrow1' : H * b1 * w * eDot - d1 * kap = H * C j := by
    rw [hrow1]
    ring
  obtain ⟨hI42, hrow2⟩ := terminalAfterLowerOne_cancel_one_68
    H b1 d1 b2 d4 phi w eDot kap (C j)
    hH hb2 hd4 hI41 hrow1'
  have hb2root : ∀ a : k, H.eval a = 0 → b2.eval a = 0 := by
    intro a ha
    have h := congrArg (fun P : k[X] => P.eval a) hI42
    simp only [eval_add, eval_mul, eval_C, eval_zero, ha, zero_mul, mul_zero,
      zero_add, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (hphi a ha)
  have hb2dvd := dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hb2root
  obtain ⟨b5, hb5⟩ := hb2dvd
  have hI4final : b5 * phi + (6 : k[X]) * w * d4 = 0 := by
    rw [hb5] at hI42
    apply mul_left_cancel₀ hH
    linear_combination hI42
  have hrowFinal : H ^ 2 * b5 * w * eDot - d4 * kap = C j := by
    rw [hb5] at hrow2
    convert hrow2 using 1 <;> ring
  refine ⟨b5, d4, ?_, ?_, hI4final, hrowFinal, ?_⟩
  · rw [hb0, hb1, hb2, hb5]
    ring
  · rw [hd0, hd1, hd4]
    ring
  · intro a ha
    have h := congrArg (fun P : k[X] => P.eval a) hrowFinal
    simp only [eval_sub, eval_mul, eval_pow, eval_C, ha, zero_pow, zero_mul]
      at h
    linear_combination -h

end TerminalDoubleZeroAlgebra68

section TerminalDoubleZeroSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The simultaneous double-zero component reaches its first genuine load
wall.  The `r=0` and `Φ₁=0` root loci remain explicit and untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneDoubleZeroPacket
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
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      (∀ a : k, H.eval a = 0 →
        r.eval a = 0 ∨ phi1.eval a = 0 ∨
          (b2.eval a = 0 ∧ b2.derivative.eval a = 0 ∧
           d2.eval a = 0 ∧ d2.derivative.eval a = 0 ∧
           k1.eval a ≠ 0)) ∧
      ((∀ a : k, H.eval a = 0 →
          r.eval a ≠ 0 ∧ phi1.eval a ≠ 0) →
        ∃ b5 d4 : k[X],
          b2 = H ^ 5 * b5 ∧ d2 = H ^ 4 * d4 ∧
          b5 * phi1 + (6 : k[X]) * w2 * d4 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           H ^ 2 * b5 * w2 * eDot - d4 * k1 = C j) ∧
          ∀ a : k, H.eval a = 0 → d4.eval a * k1.eval a = -j) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
      _hp2desc, hI4, hrow, hroots⟩ :=
    S.terminalAfterLowerOneComponentsPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  refine ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
    hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
    hI4, hrow, ?_, ?_⟩
  · intro a ha
    exact (hroots a ha).2.2.2
  · intro hall
    let A0 := cubicANumerator68 t r
    let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
    let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r
    let eDot := terminalEDerivativeNumerator68 H E0
    have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
    have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
      fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
        NonsquarePolynomial46.not_sq ha
    have hdouble : ∀ a : k, H.eval a = 0 →
        b2.eval a = 0 ∧ b2.derivative.eval a = 0 ∧
        d2.eval a = 0 ∧ d2.derivative.eval a = 0 := by
      intro a ha
      rcases (hroots a ha).2.2.2 with hr0 | hphi0 | hlast
      · exact False.elim ((hall a ha).1 hr0)
      · exact False.elim ((hall a ha).2 hphi0)
      · exact ⟨hlast.1, hlast.2.1, hlast.2.2.1, hlast.2.2.2.1⟩
    have hkap : ∀ a : k, H.eval a = 0 → k1.eval a ≠ 0 := by
      intro a ha
      rcases (hroots a ha).2.2.2 with hr0 | hphi0 | hlast
      · exact False.elim ((hall a ha).1 hr0)
      · exact False.elim ((hall a ha).2 hphi0)
      · exact hlast.2.2.2.2
    have hdesc := terminalAfterLowerOne_doubleZero_global_descent_68
      H b2 d2 phi1 w2 eDot k1 j hdeg hH hsimple
      (fun a ha => (hall a ha).2) hkap hdouble hI4 hrow
    simpa only [A0, C0, E0, eDot] using hdesc

end TerminalDoubleZeroSource68

end Max11DegreeRoutes
