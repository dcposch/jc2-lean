import FiniteTargetNormalizedPole

noncomputable section
open Polynomial

/-! # Uniqueness of the Faber normal-form parameters

The Faber basis is monic and strictly degree-filtered.  Consequently its
free coefficients are uniquely determined by the represented nonic.  This
identifies the canonical peeling of the target-normalized source with the
explicit `d = c₃ = 0` witness.
-/

namespace GCD369CubeFaberNormalForm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All free parameters of two normal forms of the same nonic agree. -/
theorem parameters_unique
    {k : Type*} [Field k]
    {a0 a1 a2 a3 a4 : RatFunc k} {q : (RatFunc k)[X]}
    (N M : GCD369CubeFaberNormalForm a0 a1 a2 a3 a4 q) :
    N.d = M.d ∧ N.c7 = M.c7 ∧ N.c6 = M.c6 ∧ N.c5 = M.c5 ∧
      N.c4 = M.c4 ∧ N.c3 = M.c3 ∧ N.c2 = M.c2 ∧
      N.c1 = M.c1 ∧ N.c0 = M.c0 := by
  have hd : N.d = M.d := by
    rw [N.d_eq_coeff_eight, M.d_eq_coeff_eight]
  have hq := N.hq.symm.trans M.hq
  have h7 := congrArg (fun p : (RatFunc k)[X] => p.coeff 7) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h7
  have hc7 : N.c7 = M.c7 := h7
  have h6 := congrArg (fun p : (RatFunc k)[X] => p.coeff 6) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h6
  simp only [hd] at h6
  have hc6 : N.c6 = M.c6 := by linear_combination h6
  have h5 := congrArg (fun p : (RatFunc k)[X] => p.coeff 5) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h5
  simp only [hd, hc7] at h5
  have hc5 : N.c5 = M.c5 := by linear_combination h5
  have h4 := congrArg (fun p : (RatFunc k)[X] => p.coeff 4) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h4
  simp only [hd, hc7, hc6] at h4
  have hc4 : N.c4 = M.c4 := by linear_combination h4
  have h3 := congrArg (fun p : (RatFunc k)[X] => p.coeff 3) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h3
  simp only [hd, hc7, hc6, hc5] at h3
  have hc3 : N.c3 = M.c3 := by linear_combination h3
  have h2 := congrArg (fun p : (RatFunc k)[X] => p.coeff 2) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h2
  simp only [hd, hc7, hc6, hc5, hc4] at h2
  have hc2 : N.c2 = M.c2 := by linear_combination h2
  have h1 := congrArg (fun p : (RatFunc k)[X] => p.coeff 1) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h1
  simp only [hd, hc7, hc6, hc5, hc4, hc3] at h1
  have hc1 : N.c1 = M.c1 := by linear_combination h1
  have h0 := congrArg (fun p : (RatFunc k)[X] => p.coeff 0) hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h0
  simp only [hd, hc7, hc6, hc5, hc4, hc3, hc2] at h0
  have hc0 : N.c0 = M.c0 := by linear_combination h0
  exact ⟨hd, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0⟩

end GCD369CubeFaberNormalForm

namespace GCD369CubePolynomialSource

/-- The canonical Faber peeling of the legally translated source is the
explicit `d = c₃ = 0` normal form.  In particular all canonical base-field
parameters have the advertised target-translation values. -/
theorem targetNormalizedCanonicalParameters
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0) :
    let T := S.targetNormalizedSource
    let P := S.faberConstantParameters
    let Q := T.faberConstantParameters
    Q.d = 0 ∧ Q.c7 = P.c7 ∧ Q.c6 = P.c6 ∧ Q.c5 = P.c5 ∧
      Q.c4 = P.c4 ∧ Q.c3 = 0 ∧ Q.c2 = P.c2 ∧
      Q.c1 = P.c1 - 7 * P.c7 * P.c3 / 9 ∧
      Q.c0 = P.c0 - 2 * P.c6 * P.c3 / 3 := by
  let T := S.targetNormalizedSource
  let P := S.faberConstantParameters
  let Q := T.faberConstantParameters
  let N := S.targetNormalizedFaberNormalForm hd
  obtain ⟨hdN, hc7N, hc6N, hc5N, hc4N, hc3N, hc2N, hc1N, hc0N⟩ :=
    GCD369CubeFaberNormalForm.parameters_unique T.faberNormalForm N
  have hQd : Q.d = 0 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hd, hdN]
    simp [N, targetNormalizedFaberNormalForm]
  have hQc7 : Q.c7 = P.c7 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc7, hc7N]
    simp [N, P, targetNormalizedFaberNormalForm]
  have hQc6 : Q.c6 = P.c6 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc6, hc6N]
    simp [N, P, targetNormalizedFaberNormalForm]
  have hQc5 : Q.c5 = P.c5 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc5, hc5N]
    simp [N, P, targetNormalizedFaberNormalForm]
  have hQc4 : Q.c4 = P.c4 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc4, hc4N]
    simp [N, P, targetNormalizedFaberNormalForm]
  have hQc3 : Q.c3 = 0 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc3, hc3N]
    simp [N, targetNormalizedFaberNormalForm]
  have hQc2 : Q.c2 = P.c2 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc2, hc2N]
    simp [N, P, targetNormalizedFaberNormalForm]
  have hQc1 : Q.c1 = P.c1 - 7 * P.c7 * P.c3 / 9 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc1, hc1N]
    simp [N, P, targetNormalizedFaberNormalForm]
  have hQc0 : Q.c0 = P.c0 - 2 * P.c6 * P.c3 / 3 := by
    apply RatFunc.C_injective
    rw [← RatFunc.algebraMap_eq_C, ← Q.hc0, hc0N]
    simp [N, P, targetNormalizedFaberNormalForm]
  exact ⟨hQd, hQc7, hQc6, hQc5, hQc4, hQc3, hQc2, hQc1, hQc0⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubeFaberNormalForm.parameters_unique
#print axioms
  GCD369CubePolynomialSource.targetNormalizedCanonicalParameters
