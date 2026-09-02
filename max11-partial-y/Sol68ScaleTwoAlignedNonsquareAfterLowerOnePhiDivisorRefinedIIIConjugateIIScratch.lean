import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateSourceScratch

/-! # The next lower-third face on the conjugate component II -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateIIAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalRefinedIIIConjugateIINextSplit68
    (A h bp w d1 phi : k) : Prop :=
  ((A * bp - 3 * h * d1 = 0) ∧
      (bp = 0 ∨ phi + 2 * A * w = 0)) ∨
    ((phi + 2 * A * w = 0) ∧
      (w = 0 ∨ A * bp - 3 * h * d1 = 0))

/-- The first divided-I4 jet and the independently transported lower-third
coefficient form a two-by-two determinant.  Its determinant is exactly the
product of the differentiated `F` face and the undifferentiated `G` face. -/
theorem terminalRefinedIII_conjugateII_next_split_68
    (A h bp w d1 phi : k)
    (hI4 : bp * phi + 6 * w * (h * d1) = 0)
    (hlower :
      2 * A * w * (A * bp - 3 * (h * d1)) -
        3 * (h * d1) * (phi + 2 * A * w) = 0) :
    terminalRefinedIIIConjugateIINextSplit68 A h bp w d1 phi := by
  let F := A * bp - 3 * h * d1
  let G := phi + 2 * A * w
  have hcross : bp * G - 2 * w * F = 0 := by
    dsimp only [F, G]
    linear_combination hI4
  have hdet : F * G = 0 := by
    dsimp only [F, G] at hcross ⊢
    linear_combination A * hcross + hlower
  rcases mul_eq_zero.mp hdet with hF | hG
  · left
    refine ⟨hF, ?_⟩
    have hbpG : bp * G = 0 := by rw [hF, mul_zero, sub_zero] at hcross; exact hcross
    rcases mul_eq_zero.mp hbpG with hbp | hG
    · exact Or.inl hbp
    · exact Or.inr hG
  · right
    refine ⟨hG, ?_⟩
    have hwF : w * F = 0 := by
      rw [hG, mul_zero, zero_sub] at hcross
      have htwo : (2 : k) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (by linear_combination -hcross)).resolve_left htwo
    exact mul_eq_zero.mp hwF

end RefinedIIIConjugateIIAlgebra68

section RefinedIIIConjugateIIPolynomial68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Component II at the conjugate root acquires the two global quotients from
the preceding packet.  Its lower-third face then gives the exact finite
derivative split above. -/
theorem terminalRefinedIII_conjugateII_next_68
    (H A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hDa : D.eval a = 0)
    (hI4 : b * phi + 6 * w * D = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3)
    (hmatch : terminalRefinedIIIConjugateMatching68
      H A b D w phi e K j c)
    (hbc : b.eval c = 0) (hDc : D.eval c = 0) :
    ∃ D1 BW : k[X],
      D = H * D1 ∧ b * w = H * BW ∧
      b * phi + 6 * H * w * D1 = 0 ∧
      BW * e - D1 * K = C j * H ^ 2 ∧
      terminalRefinedIIIConjugateIINextSplit68
        (A.eval c) (H.derivative.eval c) (b.derivative.eval c)
        (w.eval c) (D1.eval c) (phi.eval c) := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hdvdD : H ∣ D :=
    dvd_of_two_simple_root_evals_68 H D hdeg hsimple a c hac ha hc hDa hDc
  obtain ⟨D1, hD1⟩ := hdvdD
  have hbwa : (b * w).eval a = 0 := by simp [eval_mul, hwa]
  have hbwc : (b * w).eval c = 0 := by simp [eval_mul, hbc]
  obtain ⟨BW, hBW⟩ := dvd_of_two_simple_root_evals_68
    H (b * w) hdeg hsimple a c hac ha hc hbwa hbwc
  have hI4q : b * phi + 6 * H * w * D1 = 0 := by
    rw [hD1] at hI4
    linear_combination hI4
  have hrowq : BW * e - D1 * K = C j * H ^ 2 := by
    rw [hBW, hD1] at hrow
    apply mul_left_cancel₀ hH
    linear_combination hrow
  have hDderiv : D.derivative.eval c =
      H.derivative.eval c * D1.eval c := by
    have hd := congrArg (fun P : k[X] => P.derivative.eval c) hD1
    simpa [derivative_mul, eval_add, eval_mul, hc] using hd
  have hI4first := terminalI4JetPacket68_componentII b D w phi c hbc hDc
    hmatch.1.2.1
  have hfirst : b.derivative.eval c * phi.eval c +
      6 * w.eval c * (H.derivative.eval c * D1.eval c) = 0 := by
    simpa only [terminalI4JetComponentII68, hDderiv] using hI4first.1
  have hlower := hmatch.1.2.2.1 hbc hDc
  rw [hDderiv] at hlower
  refine ⟨D1, BW, hD1, hBW, hI4q, hrowq, ?_⟩
  exact terminalRefinedIII_conjugateII_next_split_68
    (A.eval c) (H.derivative.eval c) (b.derivative.eval c)
      (w.eval c) (D1.eval c) (phi.eval c) hfirst hlower

end RefinedIIIConjugateIIPolynomial68

section RefinedIIIConjugateIISource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing refinement of the conjugate packet.  Every deep root keeps
the full matching/global packet; if its conjugate lies on component II, the
next lower-third split is attached to the canonical quotients. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateIIPacket
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
                 H A0 b2 d2 w2 phi2 eDot k2 j ∧
               (b2.eval c = 0 → d2.eval c = 0 →
                 ∃ D1 BW : k[X],
                   d2 = H * D1 ∧ b2 * w2 = H * BW ∧
                   b2 * phi2 + 6 * H * w2 * D1 = 0 ∧
                   BW * eDot - D1 * k2 = C j * H ^ 2 ∧
                   terminalRefinedIIIConjugateIINextSplit68
                     (A0.eval c) (H.derivative.eval c)
                     (b2.derivative.eval c) (w2.eval c)
                     (D1.eval c) (phi2.eval c)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorConjugatePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hdeep⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hdeep ⊢
  intro a ha hwa hphia hDa hKa
  obtain ⟨c, hca, hc, hmatch, hglobal⟩ := hdeep a ha hwa hphia hDa hKa
  refine ⟨c, hca, hc, hmatch, hglobal, ?_⟩
  intro hbc hDc
  let A0 := cubicANumerator68 t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  exact terminalRefinedIII_conjugateII_next_68
    H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
      hwa hDa hI4 hrow hmatch hbc hDc

end RefinedIIIConjugateIISource68

end Max11DegreeRoutes
