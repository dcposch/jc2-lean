import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorThirdRowScratch

/-! # Divided-I4 jets on the global phi divisor -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

section PhiDivisorI4JetsAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalFirstPairAt68 (f g : k[X]) (a : k) : k :=
  f.derivative.eval a * g.eval a + f.eval a * g.derivative.eval a

def terminalSecondPairAt68 (f g : k[X]) (a : k) : k :=
  f.derivative.derivative.eval a * g.eval a +
    2 * f.derivative.eval a * g.derivative.eval a +
    f.eval a * g.derivative.derivative.eval a

def terminalI4JetPacket68 (b d w phi : k[X]) (a : k) : Prop :=
  terminalFirstPairAt68 b phi a + 6 * terminalFirstPairAt68 w d a = 0 ∧
  terminalSecondPairAt68 b phi a + 6 * terminalSecondPairAt68 w d a = 0 ∧
  terminalThirdPairAt68 b phi a + 6 * terminalThirdPairAt68 w d a = 0

def terminalI4JetComponentII68 (b d w phi : k[X]) (a : k) : Prop :=
  b.derivative.eval a * phi.eval a + 6 * w.eval a * d.derivative.eval a = 0 ∧
  b.derivative.derivative.eval a * phi.eval a +
      2 * b.derivative.eval a * phi.derivative.eval a +
      6 * (2 * w.derivative.eval a * d.derivative.eval a +
        w.eval a * d.derivative.derivative.eval a) = 0 ∧
  b.derivative.derivative.derivative.eval a * phi.eval a +
      3 * b.derivative.derivative.eval a * phi.derivative.eval a +
      3 * b.derivative.eval a * phi.derivative.derivative.eval a +
      6 * (3 * w.derivative.derivative.eval a * d.derivative.eval a +
        3 * w.derivative.eval a * d.derivative.derivative.eval a +
        w.eval a * d.derivative.derivative.derivative.eval a) = 0

def terminalI4JetComponentIII68 (b d w phi : k[X]) (a : k) : Prop :=
  b.eval a * phi.derivative.eval a + 6 * w.derivative.eval a * d.eval a = 0 ∧
  2 * b.derivative.eval a * phi.derivative.eval a +
      b.eval a * phi.derivative.derivative.eval a +
      6 * (w.derivative.derivative.eval a * d.eval a +
        2 * w.derivative.eval a * d.derivative.eval a) = 0 ∧
  3 * b.derivative.derivative.eval a * phi.derivative.eval a +
      3 * b.derivative.eval a * phi.derivative.derivative.eval a +
      b.eval a * phi.derivative.derivative.derivative.eval a +
      6 * (w.derivative.derivative.derivative.eval a * d.eval a +
        3 * w.derivative.derivative.eval a * d.derivative.eval a +
        3 * w.derivative.eval a * d.derivative.derivative.eval a) = 0

theorem terminalI4JetPacket68_of_identity
    (b d w phi : k[X]) (a : k)
    (hI4 : b * phi + C 6 * w * d = 0) :
    terminalI4JetPacket68 b d w phi a := by
  have h1 := congrArg (fun P : k[X] => P.derivative.eval a) hI4
  have h2 := congrArg (fun P : k[X] => P.derivative.derivative.eval a) hI4
  have h3 := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hI4
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_zero, eval_add, eval_mul, eval_C, eval_ofNat, eval_zero,
    terminalFirstPairAt68, terminalSecondPairAt68, terminalThirdPairAt68] at h1 h2 h3
  simp only [terminalI4JetPacket68, terminalFirstPairAt68,
    terminalSecondPairAt68, terminalThirdPairAt68]
  constructor
  · ring_nf at h1 ⊢
    exact h1
  constructor
  · ring_nf at h2 ⊢
    exact h2
  · ring_nf at h3 ⊢
    exact h3

theorem terminalI4JetPacket68_componentII
    (b d w phi : k[X]) (a : k)
    (hb : b.eval a = 0) (hd : d.eval a = 0)
    (hjets : terminalI4JetPacket68 b d w phi a) :
    terminalI4JetComponentII68 b d w phi a := by
  simp only [terminalI4JetPacket68, terminalI4JetComponentII68,
    terminalFirstPairAt68, terminalSecondPairAt68, terminalThirdPairAt68,
    hb, hd, zero_mul, mul_zero, zero_add, add_zero] at hjets ⊢
  rcases hjets with ⟨h1, h2, h3⟩
  constructor
  · ring_nf at h1 ⊢; exact h1
  constructor
  · ring_nf at h2 ⊢; exact h2
  · ring_nf at h3 ⊢; exact h3

theorem terminalI4JetPacket68_componentIII
    (b d w phi : k[X]) (a : k)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0)
    (hjets : terminalI4JetPacket68 b d w phi a) :
    terminalI4JetComponentIII68 b d w phi a := by
  simp only [terminalI4JetPacket68, terminalI4JetComponentIII68,
    terminalFirstPairAt68, terminalSecondPairAt68, terminalThirdPairAt68,
    hw, hphi, zero_mul, mul_zero, zero_add, add_zero] at hjets ⊢
  rcases hjets with ⟨h1, h2, h3⟩
  constructor
  · ring_nf at h1 ⊢; exact h1
  constructor
  · ring_nf at h2 ⊢; exact h2
  · ring_nf at h3 ⊢; exact h3

theorem terminalI4Jet_componentIII_leftZero_split
    (b d w phi : k[X]) (a : k)
    (hd : d.eval a = 0)
    (hjets : terminalI4JetComponentIII68 b d w phi a) :
    b.eval a = 0 ∨ phi.derivative.eval a = 0 := by
  have hfirst := hjets.1
  simp only [hd, mul_zero, zero_mul, add_zero] at hfirst
  exact mul_eq_zero.mp hfirst

end PhiDivisorI4JetsAlgebra68

section PhiDivisorI4JetsSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorI4JetsPacket
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
               b2 d2 w2 phi2 eDot k2 a ∧
             terminalI4JetPacket68 b2 d2 w2 phi2 a ∧
             (b2.eval a = 0 → d2.eval a = 0 →
               terminalI4JetComponentII68 b2 d2 w2 phi2 a) ∧
             (w2.eval a = 0 → phi2.eval a = 0 →
               terminalI4JetComponentIII68 b2 d2 w2 phi2 a) ∧
             (w2.eval a = 0 → phi2.eval a = 0 → d2.eval a = 0 →
               b2.eval a = 0 ∨ phi2.derivative.eval a = 0) ∧
             6 * j * (H.derivative.eval a) ^ 3 ≠ 0)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorThirdRowPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hloaded⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hloaded ⊢
  intro a ha
  have hjets := terminalI4JetPacket68_of_identity b2 d2 w2 phi2 a hI4
  refine ⟨hloaded a ha, hjets, ?_, ?_, ?_, ?_⟩
  · intro hb hd
    exact terminalI4JetPacket68_componentII b2 d2 w2 phi2 a hb hd hjets
  · intro hw hph
    exact terminalI4JetPacket68_componentIII b2 d2 w2 phi2 a hw hph hjets
  · intro hw hph hd
    have hIII := terminalI4JetPacket68_componentIII b2 d2 w2 phi2 a hw hph hjets
    exact terminalI4Jet_componentIII_leftZero_split b2 d2 w2 phi2 a hd hIII
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hj)
      (pow_ne_zero 3 (hsimple a ha))

end PhiDivisorI4JetsSource68

end Max11DegreeRoutes
