import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateScratch

/-! # Source assembly of the refined-III conjugate-root packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateGlobalAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The three exact global consequences of the conjugate allocation.

* On the common component, the common `G` face has both core roots and the
  divided I4 identity factors through the complementary `F` face.
* On component II, `D` and the transverse product `b*w` have both roots, so
  one core factor cancels from the loaded row.
* On component III, `w` and `phi` both acquire a core factor, and the `D/K`
  child determines which further quotient appears in the cancelled rows. -/
def terminalRefinedIIIConjugateGlobalSplit68
    (H A b D w phi e K : k[X]) (j : k) : Prop :=
  (∃ G : k[X],
      phi + 2 * A * w = H * G ∧
      H * b * G - 2 * w * (A * b - 3 * D) = 0) ∨
  (∃ D1 BW : k[X],
      D = H * D1 ∧ b * w = H * BW ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      BW * e - D1 * K = C j * H ^ 2) ∨
  ((∃ w1 phi1 D1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ D = H * D1 ∧
      b * phi1 + 6 * H * w1 * D1 = 0 ∧
      b * w1 * e - D1 * K = C j * H ^ 2) ∨
   (∃ w1 phi1 K1 : k[X],
      w = H * w1 ∧ phi = H * phi1 ∧ K = H * K1 ∧
      b * phi1 + 6 * w1 * D = 0 ∧
      b * w1 * e - D * K1 = C j * H ^ 2))

theorem terminalRefinedIII_conjugate_global_split_68
    (H A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hI4 : b * phi + 6 * w * D = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3)
    (hmatch : terminalRefinedIIIConjugateMatching68
      H A b D w phi e K j c) :
    terminalRefinedIIIConjugateGlobalSplit68 H A b D w phi e K j := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  rcases hmatch.2 with hcommon | hrest
  · left
    have hGa : (phi + 2 * A * w).eval a = 0 := by
      simp [eval_add, eval_mul, hphia, hwa]
    have hGc : (phi + 2 * A * w).eval c = 0 := by
      simpa [eval_add, eval_mul] using hcommon.2
    obtain ⟨G, hG⟩ := dvd_of_two_simple_root_evals_68
      H (phi + 2 * A * w) hdeg hsimple a c hac ha hc hGa hGc
    refine ⟨G, hG, ?_⟩
    linear_combination hI4 - b * hG
  rcases hrest with hII | hIII
  · right; left
    obtain ⟨D1, hD1⟩ := hII.2.2
    have hbwa : (b * w).eval a = 0 := by simp [eval_mul, hwa]
    have hbwc : (b * w).eval c = 0 := by simp [eval_mul, hII.1]
    obtain ⟨BW, hBW⟩ := dvd_of_two_simple_root_evals_68
      H (b * w) hdeg hsimple a c hac ha hc hbwa hbwc
    refine ⟨D1, BW, hD1, hBW, ?_, ?_⟩
    · rw [hD1] at hI4
      linear_combination hI4
    · rw [hBW, hD1] at hrow
      apply mul_left_cancel₀ hH
      linear_combination hrow
  · right; right
    obtain ⟨w1, hw1⟩ := hIII.2.2.1
    obtain ⟨phi1, hphi1⟩ := hIII.2.2.2.1
    rcases hIII.2.2.2.2 with hD | hK
    · left
      obtain ⟨D1, hD1⟩ := hD.2
      refine ⟨w1, phi1, D1, hw1, hphi1, hD1, ?_, ?_⟩
      · rw [hw1, hphi1, hD1] at hI4
        apply mul_left_cancel₀ hH
        linear_combination hI4
      · rw [hw1, hD1] at hrow
        apply mul_left_cancel₀ hH
        linear_combination hrow
    · right
      obtain ⟨K1, hK1⟩ := hK.2
      refine ⟨w1, phi1, K1, hw1, hphi1, hK1, ?_, ?_⟩
      · rw [hw1, hphi1] at hI4
        apply mul_left_cancel₀ hH
        linear_combination hI4
      · rw [hw1, hK1] at hrow
        apply mul_left_cancel₀ hH
        linear_combination hrow

end RefinedIIIConjugateGlobalAlgebra68

section RefinedIIIConjugateSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-level assembly: the canonical quotients from the refined-III packet
carry the conjugate-root matching and its first global H-adic descent at every
deep component-III root. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugatePacket
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
           ∀ a : k, H.eval a = 0 → w2.eval a = 0 →
             phi2.eval a = 0 → d2.eval a = 0 → k2.eval a = 0 →
             ∃ c : k, c ≠ a ∧ H.eval c = 0 ∧
               terminalRefinedIIIConjugateMatching68
                 H A0 b2 d2 w2 phi2 eDot k2 j c ∧
               terminalRefinedIIIConjugateGlobalSplit68
                 H A0 b2 d2 w2 phi2 eDot k2 j)) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorRefinedIIIPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  let A0 := cubicANumerator68 t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A0.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b2 d2 w2 phi2 eDot k2 x := fun x hx => (hroots x hx).1
  obtain ⟨c, hca, hc, hmatch⟩ := terminalRefinedIII_conjugate_matching_68
    H A0 b2 d2 w2 phi2 eDot k2 j a hdeg hsimple ha hwa hphia hDa hKa hclass
  refine ⟨c, hca, hc, hmatch, ?_⟩
  exact terminalRefinedIII_conjugate_global_split_68
    H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hwa hphia hDa hKa hI4 hrow hmatch

end RefinedIIIConjugateSource68

end Max11DegreeRoutes
