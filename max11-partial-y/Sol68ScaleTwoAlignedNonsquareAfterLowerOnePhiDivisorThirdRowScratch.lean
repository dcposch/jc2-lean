import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorDegeneracyScratch

/-! # The first loaded terminal coefficient on the global phi divisor -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section PhiDivisorThirdRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalThirdTripleAt68 (b w e : k[X]) (a : k) : k :=
  b.derivative.derivative.derivative.eval a * w.eval a * e.eval a +
    3 * b.derivative.derivative.eval a * w.derivative.eval a * e.eval a +
    3 * b.derivative.derivative.eval a * w.eval a * e.derivative.eval a +
    3 * b.derivative.eval a * w.derivative.derivative.eval a * e.eval a +
    6 * b.derivative.eval a * w.derivative.eval a * e.derivative.eval a +
    3 * b.derivative.eval a * w.eval a * e.derivative.derivative.eval a +
    b.eval a * w.derivative.derivative.derivative.eval a * e.eval a +
    3 * b.eval a * w.derivative.derivative.eval a * e.derivative.eval a +
    3 * b.eval a * w.derivative.eval a * e.derivative.derivative.eval a +
    b.eval a * w.eval a * e.derivative.derivative.derivative.eval a

def terminalThirdPairAt68 (d k2 : k[X]) (a : k) : k :=
  d.derivative.derivative.derivative.eval a * k2.eval a +
    3 * d.derivative.derivative.eval a * k2.derivative.eval a +
    3 * d.derivative.eval a * k2.derivative.derivative.eval a +
    d.eval a * k2.derivative.derivative.derivative.eval a

def terminalThirdTripleLeftZeroAt68 (b w e : k[X]) (a : k) : k :=
  b.derivative.derivative.derivative.eval a * w.eval a * e.eval a +
    3 * b.derivative.derivative.eval a * w.derivative.eval a * e.eval a +
    3 * b.derivative.derivative.eval a * w.eval a * e.derivative.eval a +
    3 * b.derivative.eval a * w.derivative.derivative.eval a * e.eval a +
    6 * b.derivative.eval a * w.derivative.eval a * e.derivative.eval a +
    3 * b.derivative.eval a * w.eval a * e.derivative.derivative.eval a

def terminalThirdTripleMiddleZeroAt68 (b w e : k[X]) (a : k) : k :=
  3 * b.derivative.derivative.eval a * w.derivative.eval a * e.eval a +
    3 * b.derivative.eval a * w.derivative.derivative.eval a * e.eval a +
    6 * b.derivative.eval a * w.derivative.eval a * e.derivative.eval a +
    b.eval a * w.derivative.derivative.derivative.eval a * e.eval a +
    3 * b.eval a * w.derivative.derivative.eval a * e.derivative.eval a +
    3 * b.eval a * w.derivative.eval a * e.derivative.derivative.eval a

def terminalThirdPairLeftZeroAt68 (d k2 : k[X]) (a : k) : k :=
  d.derivative.derivative.derivative.eval a * k2.eval a +
    3 * d.derivative.derivative.eval a * k2.derivative.eval a +
    3 * d.derivative.eval a * k2.derivative.derivative.eval a

def terminalThirdPairRightZeroAt68 (d k2 : k[X]) (a : k) : k :=
  3 * d.derivative.derivative.eval a * k2.derivative.eval a +
    3 * d.derivative.eval a * k2.derivative.derivative.eval a +
    d.eval a * k2.derivative.derivative.derivative.eval a

theorem terminalThirdTripleAt68_eq (b w e : k[X]) (a : k) :
    ((b * w * e).derivative.derivative.derivative).eval a =
      terminalThirdTripleAt68 b w e a := by
  simp only [terminalThirdTripleAt68, derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat]
  ring

theorem terminalThirdPairAt68_eq (d k2 : k[X]) (a : k) :
    ((d * k2).derivative.derivative.derivative).eval a =
      terminalThirdPairAt68 d k2 a := by
  simp only [terminalThirdPairAt68, derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat]
  ring

theorem terminalThirdCoreLoad68_eq (H : k[X]) (j a : k)
    (ha : H.eval a = 0) :
    ((C j * H ^ 3).derivative.derivative.derivative).eval a =
      6 * j * (H.derivative.eval a) ^ 3 := by
  simp only [derivative_mul, derivative_pow, derivative_C, zero_mul,
    zero_add, derivative_add, eval_add, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, zero_pow, mul_zero]
  ring

theorem terminalThirdTripleAt68_of_left_zero (b w e : k[X]) (a : k)
    (hb : b.eval a = 0) :
    terminalThirdTripleAt68 b w e a =
      terminalThirdTripleLeftZeroAt68 b w e a := by
  simp only [terminalThirdTripleAt68, terminalThirdTripleLeftZeroAt68, hb,
    zero_mul, zero_add, add_zero]
  ring

theorem terminalThirdTripleAt68_of_middle_zero (b w e : k[X]) (a : k)
    (hw : w.eval a = 0) :
    terminalThirdTripleAt68 b w e a =
      terminalThirdTripleMiddleZeroAt68 b w e a := by
  simp only [terminalThirdTripleAt68, terminalThirdTripleMiddleZeroAt68, hw,
    zero_mul, mul_zero, zero_add, add_zero]

theorem terminalThirdPairAt68_of_left_zero (d k2 : k[X]) (a : k)
    (hd : d.eval a = 0) :
    terminalThirdPairAt68 d k2 a = terminalThirdPairLeftZeroAt68 d k2 a := by
  simp only [terminalThirdPairAt68, terminalThirdPairLeftZeroAt68, hd,
    zero_mul, add_zero]

theorem terminalThirdPairAt68_of_right_zero (d k2 : k[X]) (a : k)
    (hk : k2.eval a = 0) :
    terminalThirdPairAt68 d k2 a = terminalThirdPairRightZeroAt68 d k2 a := by
  simp only [terminalThirdPairAt68, terminalThirdPairRightZeroAt68, hk,
    mul_zero, zero_add]

def terminalPhiDivisorLoadedDegeneracy68
    (A hprime load : k) (b d w phi e k2 : k[X]) (a : k) : Prop :=
  ((A * b.eval a - 3 * d.eval a = 0) ∧
      (phi.eval a + 2 * A * w.eval a = 0) ∧
      (A = 0 ∨ b.eval a = 0 ∨
        hprime * A ^ 2 * w.eval a + 3 * k2.eval a = 0) ∧
      terminalThirdTripleAt68 b w e a - terminalThirdPairAt68 d k2 a = load) ∨
    ((A * b.eval a - 3 * d.eval a = 0) ∧ b.eval a = 0 ∧ d.eval a = 0 ∧
      terminalThirdTripleLeftZeroAt68 b w e a -
        terminalThirdPairLeftZeroAt68 d k2 a = load) ∨
    ((phi.eval a + 2 * A * w.eval a = 0) ∧ w.eval a = 0 ∧
      phi.eval a = 0 ∧
      ((d.eval a = 0 ∧ terminalThirdTripleMiddleZeroAt68 b w e a -
          terminalThirdPairLeftZeroAt68 d k2 a = load) ∨
       (k2.eval a = 0 ∧ terminalThirdTripleMiddleZeroAt68 b w e a -
          terminalThirdPairRightZeroAt68 d k2 a = load)))

theorem terminalPhiDivisor_loadedDegeneracy_68
    (A hprime load : k) (b d w phi e k2 : k[X]) (a : k)
    (hdeg : terminalPhiDivisorDegeneracy68 A (b.eval a) (d.eval a)
      (w.eval a) (phi.eval a) (e.eval a) (k2.eval a) hprime)
    (hthird : terminalThirdTripleAt68 b w e a -
      terminalThirdPairAt68 d k2 a = load) :
    terminalPhiDivisorLoadedDegeneracy68 A hprime load b d w phi e k2 a := by
  rcases hdeg with hcommon | hrest
  · exact Or.inl ⟨hcommon.1, hcommon.2.1, hcommon.2.2, hthird⟩
  rcases hrest with hleft | hmiddle
  · right; left
    have ht := terminalThirdTripleAt68_of_left_zero b w e a hleft.2.1
    have hp := terminalThirdPairAt68_of_left_zero d k2 a hleft.2.2
    exact ⟨hleft.1, hleft.2.1, hleft.2.2, by rw [← ht, ← hp]; exact hthird⟩
  · right; right
    refine ⟨hmiddle.1, hmiddle.2.1, hmiddle.2.2.1, ?_⟩
    have ht := terminalThirdTripleAt68_of_middle_zero b w e a hmiddle.2.1
    rcases hmiddle.2.2.2 with hd | hk
    · left
      have hp := terminalThirdPairAt68_of_left_zero d k2 a hd
      exact ⟨hd, by rw [← ht, ← hp]; exact hthird⟩
    · right
      have hp := terminalThirdPairAt68_of_right_zero d k2 a hk
      exact ⟨hk, by rw [← ht, ← hp]; exact hthird⟩

end PhiDivisorThirdRowAlgebra68

section PhiDivisorThirdRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorThirdRowPacket
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
             terminalPhiDivisorLoadedDegeneracy68 (A0.eval a)
               (H.derivative.eval a) (6 * j * (H.derivative.eval a) ^ 3)
               b2 d2 w2 phi2 eDot k2 a)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorDegeneracyPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hdegenerate⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hdegenerate ⊢
  intro a ha
  have hdiff := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, eval_sub] at hdiff
  rw [terminalThirdTripleAt68_eq b2 w2
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) a,
    terminalThirdPairAt68_eq d2 k2 a,
    terminalThirdCoreLoad68_eq H j a ha] at hdiff
  exact terminalPhiDivisor_loadedDegeneracy_68
    (Polynomial.eval a (cubicANumerator68 t r)) (H.derivative.eval a)
    (6 * j * (H.derivative.eval a) ^ 3) b2 d2 w2 phi2
    (terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)) k2 a (hdegenerate a ha) hdiff

end PhiDivisorThirdRowSource68

end Max11DegreeRoutes
