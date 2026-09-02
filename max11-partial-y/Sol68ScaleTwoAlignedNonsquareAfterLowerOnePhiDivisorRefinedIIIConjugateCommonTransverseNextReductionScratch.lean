import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateStableAssemblyScratch

/-! # Finite reduction of the stable CommonTransverseNext residual

The stable source packet carries more structure than the abstract common
transverse packet: `B` has a double zero at the conjugate root and `D=H*D1`.
Those two facts delete the nominal `B(c) != 0` leaf and turn the conjugate
face of the order-two transverse limb into `D'(c)=D1(c)=0`.  No new Taylor
coefficient is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section CommonTransverseNextReductionAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact residual after adding the stable source shapes to
`CommonTransverseNext`.

* the first limb is the already named component-III `D/K` allocation;
* the `F`-collapse limb becomes either the global selector `H | B` or the
  coordinate kill `r(a)=0`;
* the genuine order-two limb gains `D1(c)=0`, and hence either `H^2 | D` or
  the sharp complementary unit `D'(a) != 0`.

The original packet is retained as the first conjunct, so no derivative or
unit data is discarded. -/
def terminalRefinedIIIConjugateCommonTransverseNextReduction68
    (H t r X0 A B D w phi e K : k[X]) (j a c : k) : Prop :=
  terminalRefinedIIIConjugateCommonTransverseNext68
      H A B D w phi e K j a c ∧
    ((w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
        ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K))) ∨
     (w.eval c ≠ 0 ∧ H ∣ B) ∨
     (w.eval c ≠ 0 ∧ r.eval a = 0) ∨
     (w.eval c ≠ 0 ∧ B.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧
       ∃ D1 : k[X], D = H * D1 ∧ D1.eval c = 0 ∧
         (H ^ 2 ∣ D ∨ D.derivative.eval a ≠ 0)))

/-- At a core root, the stable coordinate identity turns an apex zero into
a coordinate zero. -/
theorem commonTransverse_apex_zero_is_coordinate_zero_68
    (H t r X0 A : k[X]) (a : k)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (ha : H.eval a = 0) (hAa : A.eval a = 0) :
    r.eval a = 0 := by
  have hx := congrArg (fun P : k[X] => P.eval a) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, ha, zero_mul] at hx
  have hAv := congrArg (fun P : k[X] => P.eval a) hA
  dsimp only [cubicANumerator68] at hAv
  simp only [eval_sub, eval_mul, eval_pow, eval_C] at hAv
  have hrsq : r.eval a ^ 2 = 0 := by
    linear_combination (12 : k) * hAv - 12 * hAa + 4 * hx
  exact sq_eq_zero_iff.mp hrsq

/-- Local finite reduction.  Only double-root evaluation, one derivative of
the already retained conjugate face, and simple-root globalization are used. -/
theorem terminalRefinedIII_conjugateCommon_transverseNext_reduction_68
    (H t r X0 A B D w phi e K B2 D1 : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hDshape : D = H * D1)
    (hnext : terminalRefinedIIIConjugateCommonTransverseNext68
      H A B D w phi e K j a c) :
    terminalRefinedIIIConjugateCommonTransverseNextReduction68
      H t r X0 A B D w phi e K j a c := by
  have hbc : B.eval c = 0 := by
    rw [hB]
    simp
  have hbpc : B.derivative.eval c = 0 := by
    have hsquare : ((X - C c) ^ 2).derivative.eval c = 0 := by
      rw [derivative_pow]
      simp
    rw [hB, derivative_mul]
    simp only [eval_add, eval_mul, hsquare, zero_mul, eval_pow, eval_sub,
      eval_X, eval_C, sub_self, zero_pow, mul_zero, add_zero]
    norm_num
  refine ⟨hnext, ?_⟩
  obtain ⟨G, hG, hGrow, hsplit⟩ := hnext
  rcases hsplit with hIII | hF | htrans
  · left
    obtain ⟨hwc, w1, hw, hphi, _hI4, hDK⟩ := hIII
    have hphic : phi.eval c = 0 := by rw [hphi]; simp [hc]
    refine ⟨hwc, hphic, ⟨w1, hw⟩,
      ⟨G - 2 * A * w1, hphi⟩, ?_⟩
    rcases hDK with hD | hK
    · exact Or.inl ⟨hD.1, ⟨hD.2.choose, hD.2.choose_spec.1⟩⟩
    · exact Or.inr ⟨hK.1, ⟨hK.2.choose, hK.2.choose_spec.1⟩⟩
  · right
    obtain ⟨hwc, hFpack, hselector⟩ := hF
    obtain ⟨F1, hF1, hbG, _heval, hallocation⟩ := hFpack
    rcases hallocation with hcomponentII | hKtie
    · rcases hselector with hba | hAa
      · left
        exact ⟨hwc, dvd_of_two_simple_root_evals_68 H B hdeg hsimple
          a c hac ha hc hba hbc⟩
      · right; left
        exact ⟨hwc, commonTransverse_apex_zero_is_coordinate_zero_68
          H t r X0 A a hA hX ha hAa.1⟩
    · exact (hKtie.1 hbc).elim
  · right; right; right
    obtain ⟨hwc, hba, hAa, _hw1a, _hphi1a, _hphi2a, _hGa, _htie,
      _hI4third, _hrowtie, _hloaded, hconjugate, _horders⟩ := htrans
    have hDpc : D.derivative.eval c = 0 := by
      rw [hbc, hbpc] at hconjugate
      simp only [mul_zero, zero_mul, add_zero, zero_add] at hconjugate
      have h6prod : (6 : k) * (w.eval c * D.derivative.eval c) = 0 := by
        linear_combination hconjugate
      have hprod : w.eval c * D.derivative.eval c = 0 :=
        (mul_eq_zero.mp h6prod).resolve_left (by norm_num)
      exact (mul_eq_zero.mp hprod).resolve_left hwc
    have hDshapeC := congrArg (fun P : k[X] => P.derivative.eval c) hDshape
    simp only [derivative_mul, eval_add, eval_mul, hc, zero_mul,
      add_zero] at hDshapeC
    have hD1c : D1.eval c = 0 := by
      have hprod : H.derivative.eval c * D1.eval c = 0 := by
        rw [hDpc] at hDshapeC
        exact hDshapeC.symm
      exact (mul_eq_zero.mp hprod).resolve_left (hsimple c hc)
    refine ⟨hwc, hba, hAa, D1, hDshape, hD1c, ?_⟩
    rcases eq_or_ne (D.derivative.eval a) 0 with hDpa | hDpa
    · left
      have hDshapeA := congrArg (fun P : k[X] => P.derivative.eval a) hDshape
      simp only [derivative_mul, eval_add, eval_mul, ha, zero_mul,
        add_zero] at hDshapeA
      have hD1a : D1.eval a = 0 := by
        have hprod : H.derivative.eval a * D1.eval a = 0 := by
          rw [hDpa] at hDshapeA
          exact hDshapeA.symm
        exact (mul_eq_zero.mp hprod).resolve_left (hsimple a ha)
      obtain ⟨D2, hD2⟩ := dvd_of_two_simple_root_evals_68 H D1
        hdeg hsimple a c hac ha hc hD1a hD1c
      refine ⟨D2, ?_⟩
      rw [hDshape, hD2]
      ring
    · exact Or.inr hDpa

end CommonTransverseNextReductionAlgebra68

section CommonTransverseNextReductionSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing wrapper for the stable CommonTransverseNext limb. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateCommonTransverseNextReduction
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 A B D w phi e K B2 D1 : k[X]) (a c : k)
    (hdeg : H.natDegree = 2)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hA : A = cubicANumerator68 t r)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hDshape : D = H * D1)
    (hnext : terminalRefinedIIIConjugateCommonTransverseNext68
      H A B D w phi e K j a c) :
    terminalRefinedIIIConjugateCommonTransverseNextReduction68
      H t r X0 A B D w phi e K j a c := by
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  exact terminalRefinedIII_conjugateCommon_transverseNext_reduction_68
    H t r X0 A B D w phi e K B2 D1 j a c hdeg hsimple ha hc hac
    hA hX hB hDshape hnext

end CommonTransverseNextReductionSource68

end Max11DegreeRoutes
