import Max11Core

open scoped BigOperators

noncomputable section

namespace Max11ClassicalRoutes

open MvPolynomial

/-- In characteristic zero, a vanishing partial derivative means that the
corresponding variable is absent. -/
theorem not_mem_vars_of_pderiv_eq_zero {K σ : Type*}
    [Field K] [CharZero K] {i : σ} {P : MvPolynomial σ K}
    (hP : pderiv i P = 0) : i ∉ P.vars := by
  intro hi
  rw [mem_vars_iff_mem_support] at hi
  obtain ⟨m, hm, him⟩ := hi
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
  let m' := m - Finsupp.single i 1
  have hadd : m' + Finsupp.single i 1 = m :=
    Finsupp.sub_add_single_one_cancel hmi
  have hcoeff : coeff m P ≠ 0 := mem_support_iff.mp hm
  have hzero := congrArg (coeff m') hP
  rw [coeff_pderiv, coeff_zero, hadd] at hzero
  exact (mul_ne_zero hcoeff (Nat.cast_add_one_ne_zero (R := K) _)).elim hzero

/-- A Keller pair whose first coordinate has partial y-degree zero has
nonzero constant x- and y-derivatives in the two respective coordinates. -/
theorem derivative_constants_of_zero_y_degree {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hdegree : degreeOf 1 P = 0) (hKeller : IsPlaneKellerPair P Q) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      pderiv 0 P = C a ∧ pderiv 1 Q = C b := by
  have hyP : pderiv 1 P = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    rw [mem_vars_iff_degreeOf_ne_zero, hdegree]
    simp
  obtain ⟨j, hj, hjac⟩ := hKeller
  have hprod : pderiv 0 P * pderiv 1 Q = C j := by
    simpa [PlaneJacobian, hyP] using hjac
  have hunit : IsUnit (pderiv 0 P * pderiv 1 Q) := by
    rw [hprod]
    exact (isUnit_iff_ne_zero.mpr hj).map C
  have hxunit : IsUnit (pderiv 0 P) :=
    isUnit_of_mul_isUnit_left hunit
  have hyunit : IsUnit (pderiv 1 Q) :=
    isUnit_of_mul_isUnit_right hunit
  obtain ⟨a, haunit, hxa⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hxunit
  obtain ⟨b, hbunit, hyb⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hyunit
  exact ⟨a, b, isUnit_iff_ne_zero.mp haunit, isUnit_iff_ne_zero.mp hbunit,
    hxa, hyb⟩

/-- The first coordinate of a zero-y-degree Keller pair is affine linear in
the other variable, with nonzero slope. -/
theorem first_coordinate_affine_of_zero_y_degree {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hdegree : degreeOf 1 P = 0) (hKeller : IsPlaneKellerPair P Q) :
    ∃ a c : K, a ≠ 0 ∧ P = C a * X 0 + C c := by
  obtain ⟨a, _b, ha, _hb, hxa, _hyb⟩ :=
    derivative_constants_of_zero_y_degree hdegree hKeller
  have hyP : pderiv 1 P = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    rw [mem_vars_iff_degreeOf_ne_zero, hdegree]
    simp
  let R : MvPolynomial (Fin 2) K := P - C a * X 0
  have hxR : pderiv 0 R = 0 := by
    simp [R, hxa]
  have hyR : pderiv 1 R = 0 := by
    simp [R, hyP]
  have hvars : R.vars = ∅ := by
    ext i
    simp
    fin_cases i
    · exact not_mem_vars_of_pderiv_eq_zero hxR
    · exact not_mem_vars_of_pderiv_eq_zero hyR
  have hR : R = C (R.coeff 0) := vars_eq_empty_iff_eq_C.mp hvars
  refine ⟨a, R.coeff 0, ha, ?_⟩
  calc
    P = R + C a * X 0 := by simp [R]
    _ = C (R.coeff 0) + C a * X 0 :=
      congrArg (fun T => T + C a * X 0) hR
    _ = C a * X 0 + C (R.coeff 0) := add_comm _ _

/-- After subtracting its nonzero linear y-term, the second coordinate is a
polynomial in x alone. -/
theorem second_coordinate_remainder_supported {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hdegree : degreeOf 1 P = 0) (hKeller : IsPlaneKellerPair P Q) :
    ∃ b : K, b ≠ 0 ∧
      Q - C b * X 1 ∈ supported K ({0} : Set (Fin 2)) := by
  obtain ⟨_a, b, _ha, hb, _hxa, hyb⟩ :=
    derivative_constants_of_zero_y_degree hdegree hKeller
  refine ⟨b, hb, ?_⟩
  rw [mem_supported]
  intro i hi
  have hnot : 1 ∉ (Q - C b * X 1).vars := by
    apply not_mem_vars_of_pderiv_eq_zero
    simp [hyb]
  fin_cases i
  · simp
  · exact False.elim (hnot hi)

/-- The zero partial-degree route for bivariate Keller pairs: if the first
coordinate is independent of y, the two coordinates generate the full
polynomial ring. -/
theorem planeKellerGeneration_of_zero_y_degree {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hdegree : degreeOf 1 P = 0) (hKeller : IsPlaneKellerPair P Q) :
    PlanePairGenerates P Q := by
  obtain ⟨a, c, ha, hPshape⟩ :=
    first_coordinate_affine_of_zero_y_degree hdegree hKeller
  obtain ⟨b, hb, hQsupported⟩ :=
    second_coordinate_remainder_supported hdegree hKeller
  let S : Subalgebra K (MvPolynomial (Fin 2) K) :=
    Algebra.adjoin K ({P, Q} : Set (MvPolynomial (Fin 2) K))
  have hPmem : P ∈ S := by
    apply Algebra.subset_adjoin
    simp
  have hQmem : Q ∈ S := by
    apply Algebra.subset_adjoin
    simp
  have hCmem (r : K) : C r ∈ S := by
    rw [← MvPolynomial.algebraMap_eq]
    exact S.algebraMap_mem r
  have hx : X 0 ∈ S := by
    have hmem : C (a⁻¹) * (P - C c) ∈ S :=
      S.mul_mem (hCmem _) (S.sub_mem hPmem (hCmem _))
    have heq : C (a⁻¹) * (P - C c) = X 0 := by
      rw [hPshape]
      simp only [add_sub_cancel_right, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ ha, C_1, one_mul]
    rwa [heq] at hmem
  let R : MvPolynomial (Fin 2) K := Q - C b * X 1
  have hRmem : R ∈ S := by
    have hsupported : R ∈ supported K ({0} : Set (Fin 2)) := by
      simpa [R] using hQsupported
    have hsupp_le : supported K ({0} : Set (Fin 2)) ≤ S := by
      rw [supported_eq_adjoin_X]
      apply Algebra.adjoin_le
      rintro _ ⟨i, hi, rfl⟩
      simp only [Set.mem_singleton_iff] at hi
      subst i
      exact hx
    exact hsupp_le hsupported
  have hy : X 1 ∈ S := by
    have hmem : C (b⁻¹) * (Q - R) ∈ S :=
      S.mul_mem (hCmem _) (S.sub_mem hQmem hRmem)
    have heq : C (b⁻¹) * (Q - R) = X 1 := by
      simp only [R, sub_sub_cancel, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ hb, C_1, one_mul]
    rwa [heq] at hmem
  change S = ⊤
  apply top_unique
  rw [← MvPolynomial.adjoin_range_X]
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hx
  · exact hy

/-- The first standard route required by the max-eleven recursion is now
discharged for actual characteristic-zero bivariate Keller pairs. -/
theorem planeKellerAutomorphicAtDegrees_zero {K : Type*}
    [Field K] [CharZero K] :
    ∀ n, PlaneKellerAutomorphicAtDegrees (K := K) 0 n := by
  intro n P Q hPdegree _hQdegree hKeller
  exact planeKellerGeneration_of_zero_y_degree hPdegree hKeller

/-- Concrete max-eleven composition with the zero-degree route proved
internally; only the gcd, divisibility, equal-degree, and global (6,9) routes
remain as hypotheses. -/
theorem Max11PlaneKellerGenerationWithZeroRoute {K : Type*}
    [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hdiv : ∀ m n, m < n → m ∣ n →
      (∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) m r) →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hequal : ∀ n,
      (∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) r n) →
      PlaneKellerAutomorphicAtDegrees (K := K) n n)
    (h69 : PlaneKellerAutomorphicAtDegrees (K := K) 6 9) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGeneration
    planeKellerAutomorphicAtDegrees_zero hgcd hdiv hequal h69

#print axioms not_mem_vars_of_pderiv_eq_zero
#print axioms derivative_constants_of_zero_y_degree
#print axioms first_coordinate_affine_of_zero_y_degree
#print axioms second_coordinate_remainder_supported
#print axioms planeKellerGeneration_of_zero_y_degree
#print axioms planeKellerAutomorphicAtDegrees_zero
#print axioms Max11PlaneKellerGenerationWithZeroRoute

end Max11ClassicalRoutes
