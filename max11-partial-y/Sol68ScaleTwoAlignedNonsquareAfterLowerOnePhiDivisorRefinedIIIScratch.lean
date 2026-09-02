import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorLowerThirdScratch

/-! # The refined component-III jet packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

section RefinedIIIAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalThirdTripleMiddleDoubleZeroAt68 (b w e : k[X]) (a : k) : k :=
  3 * b.derivative.eval a * w.derivative.derivative.eval a * e.eval a +
    b.eval a * w.derivative.derivative.derivative.eval a * e.eval a +
    3 * b.eval a * w.derivative.derivative.eval a * e.derivative.eval a

theorem terminalThirdTripleMiddleZeroAt68_of_derivative_zero
    (b w e : k[X]) (a : k) (hw1 : w.derivative.eval a = 0) :
    terminalThirdTripleMiddleZeroAt68 b w e a =
      terminalThirdTripleMiddleDoubleZeroAt68 b w e a := by
  simp only [terminalThirdTripleMiddleZeroAt68,
    terminalThirdTripleMiddleDoubleZeroAt68, hw1, mul_zero, zero_mul,
    zero_add, add_zero]

def terminalPhiDivisorRefinedIIIResidual68
    (r b d w phi e k2 : k[X]) (a load : k) : Prop :=
  r.eval a = 0 ∨
    (w.derivative.eval a = 0 ∧ phi.derivative.eval a = 0 ∧
      phi.derivative.derivative.eval a = 0 ∧
      b.eval a * phi.derivative.derivative.derivative.eval a +
        18 * w.derivative.derivative.eval a * d.derivative.eval a = 0 ∧
      terminalThirdTripleMiddleDoubleZeroAt68 b w e a -
        terminalThirdPairLeftZeroAt68 d k2 a = load)

end RefinedIIIAlgebra68

section RefinedIIISource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorRefinedIIIPacket
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
        ∃ phi2 k2 : k[X], phi1 = H * phi2 ∧ k1 = H * k2 ∧
          b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∧
          (let A0 := cubicANumerator68 t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           ∀ a : k, H.eval a = 0 →
             terminalPhiDivisorLowerThirdClassification68 (A0.eval a)
               (H.derivative.eval a) (6 * j * (H.derivative.eval a) ^ 3)
               b2 d2 w2 phi2 eDot k2 a ∧
             (w2.eval a = 0 → phi2.eval a = 0 → d2.eval a = 0 →
               b2.eval a ≠ 0 →
               terminalPhiDivisorRefinedIIIResidual68 r b2 d2 w2 phi2
                 eDot k2 a (6 * j * (H.derivative.eval a) ^ 3)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorLowerThirdPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hclass⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hclass ⊢
  intro a ha
  refine ⟨hclass a ha, ?_⟩
  intro hw hph hd hbne
  have hc := hclass a ha
  dsimp only [terminalPhiDivisorLowerThirdClassification68] at hc
  have hrefined := hc.2.2.2.2 hw hph hd
  rcases hrefined with hb0 | ⟨hphi1, hAorW⟩
  · exact (hbne hb0).elim
  rcases hAorW with hA0 | hw1
  · left
    dsimp only [cubicANumerator68] at hA0
    have hxa := congrArg (fun P : k[X] => P.eval a) hX
    simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, ha,
      zero_mul] at hxa hA0
    have hrsq : (r.eval a) ^ 2 = 0 := by
      linear_combination -12 * hA0 + 4 * hxa
    exact sq_eq_zero_iff.mp hrsq
  · right
    have hjets := hc.2.1
    have hIII := terminalI4JetPacket68_componentIII b2 d2 w2 phi2 a
      hw hph hjets
    have hsecond := hIII.2.1
    have hphi2 : phi2.derivative.derivative.eval a = 0 := by
      simp only [hphi1, hw1, hd, zero_mul, mul_zero, zero_add, add_zero]
        at hsecond
      exact (mul_eq_zero.mp hsecond).resolve_left hbne
    have hthird := hIII.2.2
    have hI4three : b2.eval a * phi2.derivative.derivative.derivative.eval a +
        18 * w2.derivative.derivative.eval a * d2.derivative.eval a = 0 := by
      simp only [hphi1, hphi2, hw1, hd, zero_mul, mul_zero, zero_add,
        add_zero] at hthird
      linear_combination hthird
    have hdiff := congrArg
      (fun P : k[X] => P.derivative.derivative.derivative.eval a) hrow
    simp only [derivative_sub, eval_sub] at hdiff
    let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r
    let eDot := terminalEDerivativeNumerator68 H E0
    have hdiff' : terminalThirdTripleAt68 b2 w2 eDot a -
        terminalThirdPairAt68 d2 k2 a =
          6 * j * (H.derivative.eval a) ^ 3 := by
      dsimp only [eDot, E0]
      rw [terminalThirdTripleAt68_eq b2 w2
          (terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r)) a,
        terminalThirdPairAt68_eq d2 k2 a,
        terminalThirdCoreLoad68_eq H j a ha] at hdiff
      exact hdiff
    have htMid := terminalThirdTripleAt68_of_middle_zero b2 w2 eDot a hw
    have htDouble := terminalThirdTripleMiddleZeroAt68_of_derivative_zero
      b2 w2 eDot a hw1
    have hpLeft := terminalThirdPairAt68_of_left_zero d2 k2 a hd
    have hload : terminalThirdTripleMiddleDoubleZeroAt68 b2 w2 eDot a -
        terminalThirdPairLeftZeroAt68 d2 k2 a =
          6 * j * (H.derivative.eval a) ^ 3 := by
      rw [← htDouble, ← htMid, ← hpLeft]
      exact hdiff'
    exact ⟨hw1, hphi1, hphi2, hI4three, hload⟩

end RefinedIIISource68

end Max11DegreeRoutes
