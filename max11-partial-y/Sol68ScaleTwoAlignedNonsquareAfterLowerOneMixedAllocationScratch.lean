import Sol68ScaleTwoAlignedNonsquareAfterLowerOneLoadWallScratch

/-! # The first next faces on the mixed terminal allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalMixedAllocationAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- On the `Φ₁=0` allocation, the first unused derivatives of `I4` and
the terminal row give two exact scalar faces.  Their cheapest consequences
are the displayed finite splits. -/
theorem terminalAfterLowerOne_phiZero_next_faces_68
    (H b phi w d eDot kap : k[X]) (j a : k)
    (ha : H.eval a = 0) (hphi : phi.eval a = 0)
    (hsimple : H.derivative.eval a ≠ 0)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0)
    (hrow : H * b * w * eDot - d * kap = C j * H ^ 4) :
    b.eval a * phi.derivative.eval a +
      6 * H.derivative.eval a * w.eval a * d.eval a = 0 ∧
      H.derivative.eval a * b.eval a * w.eval a * eDot.eval a -
        (d.derivative.eval a * kap.eval a +
          d.eval a * kap.derivative.eval a) = 0 ∧
      (b.eval a = 0 → w.eval a = 0 ∨ d.eval a = 0) ∧
      (d.eval a = 0 → b.eval a = 0 ∨ phi.derivative.eval a = 0) := by
  have hI4der := congrArg (fun P : k[X] => P.derivative) hI4
  have hI4eval := congrArg (fun P : k[X] => P.eval a) hI4der
  simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
    eval_add, eval_mul, eval_C, eval_zero] at hI4eval
  rw [ha, hphi] at hI4eval
  have hI4face : b.eval a * phi.derivative.eval a +
      6 * H.derivative.eval a * w.eval a * d.eval a = 0 := by
    simpa only [eval_ofNat, zero_mul, mul_zero, zero_add, add_zero,
      mul_assoc] using hI4eval
  have hrowder := congrArg (fun P : k[X] => P.derivative) hrow
  have hroweval := congrArg (fun P : k[X] => P.eval a) hrowder
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_C,
    derivative_zero, eval_sub, eval_add, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero] at hroweval
  have hrowface : H.derivative.eval a * b.eval a * w.eval a * eDot.eval a -
      (d.derivative.eval a * kap.eval a +
        d.eval a * kap.derivative.eval a) = 0 := by
    simpa [ha] using hroweval
  refine ⟨hI4face, hrowface, ?_, ?_⟩
  · intro hb
    rw [hb, zero_mul, zero_add] at hI4face
    have hfac : H.derivative.eval a * (w.eval a * d.eval a) = 0 := by
      linear_combination (1 / 6 : k) * hI4face
    exact mul_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hsimple)
  · intro hd
    rw [hd, mul_zero, add_zero] at hI4face
    exact mul_eq_zero.mp hI4face

end TerminalMixedAllocationAlgebra68

section TerminalMixedAllocationSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing refinement of the mixed allocation left beside the pure
load wall.  It globalizes the allocation as two product divisibilities and
records the first exact faces on every `Φ₁=0` root. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedAllocationPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t phi1 k1 b2 d2 w2 : k[X]),
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
      H ∣ r * phi1 * b2 ∧ H ∣ r * phi1 * d2 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       ∀ a : k, H.eval a = 0 → phi1.eval a = 0 →
        b2.eval a * phi1.derivative.eval a +
            6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
          H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
            (d2.derivative.eval a * k1.eval a +
              d2.eval a * k1.derivative.eval a) = 0 ∧
          (b2.eval a = 0 → w2.eval a = 0 ∨ d2.eval a = 0) ∧
          (d2.eval a = 0 →
            b2.eval a = 0 ∨ phi1.derivative.eval a = 0)) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      _hg, _hgr, _ht, _hX, _hY, _hb1, _hd1, _hw1, _hphi,
      _hb2, _hd2, _hw2, hI4, hrow, hroots, _hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0, eDot] using hrow
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hprodB : H ∣ r * phi1 * b2 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    rcases hroots a ha with hr | hphi0 | hlast
    · simp [hr]
    · simp [hphi0]
    · simp [hlast.1]
  have hprodD : H ∣ r * phi1 * d2 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    rcases hroots a ha with hr | hphi0 | hlast
    · simp [hr]
    · simp [hphi0]
    · simp [hlast.2.2.1]
  refine ⟨r, t, phi1, k1, b2, d2, w2, hI4, hrow, hroots,
    hprodB, hprodD, ?_⟩
  dsimp only
  intro a ha hphi0
  exact terminalAfterLowerOne_phiZero_next_faces_68
    H b2 phi1 w2 d2 eDot k1 j a ha hphi0 (hsimple a ha) hI4 hrow'

end TerminalMixedAllocationSource68

end Max11DegreeRoutes
