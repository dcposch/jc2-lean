import LowScale410LWallFanConnector

/-!
# Zero-degree boundary of the `(4,10)`, scale-zero `l ≠ 0` wall

This closes the cases omitted by the positive-degree Newton fan.  A
zero natural degree may mean either a constant polynomial or the zero
polynomial, so nonzeroness is required only for the exposed monomial
actually used in each chamber.
-/

noncomputable section

set_option maxHeartbeats 8000000

open Polynomial

namespace Max11DegreeRoutes

section LWallZeroDegree410

variable {k : Type*} [Field k] [CharZero k]

/-! ## Relaxed exposed-vertex bounds -/

theorem lWallFanRestTwoA5_410_natDegree_lt_of_posA
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanTwoA5Unique410 a b u) :
    (lWallFanRestTwoA5_410 l beta gamma delta zeta eta theta A B U).natDegree <
      5 * a := by
  simp only [lWallFanRestTwoA5_410, lWallLowURestTwo410,
    fanTwoA5Unique410] at *
  compute_degree
  omega

theorem lWallFanRestTwoBU2_410_natDegree_lt_of_posBU
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanTwoBU2Unique410 a b u) :
    (lWallFanRestTwoBU2_410 l beta gamma delta zeta eta theta A B U).natDegree <
      b + 2 * u := by
  simp only [lWallFanRestTwoBU2_410, lWallIntermediateRestTwo410,
    fanTwoBU2Unique410] at *
  compute_degree
  omega

theorem lWallFanRestOneA4B_410_natDegree_lt_of_posA
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneA4BUnique410 a b u) :
    (lWallFanRestOneA4B_410 l beta gamma delta zeta eta theta A B U).natDegree <
      4 * a + b := by
  simp only [lWallFanRestOneA4B_410, lWallLowURestOne410,
    fanOneA4BUnique410] at *
  compute_degree
  omega

theorem lWallFanRestOneB4_410_natDegree_lt_of_posB
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (hb : 0 < b)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneB4Unique410 a b u) :
    (lWallFanRestOneB4_410 l beta gamma delta zeta eta theta A B U).natDegree <
      4 * b := by
  simp only [lWallFanRestOneB4_410, lWallLowURestOne410,
    fanOneB4Unique410] at *
  compute_degree
  omega

theorem lWallFanRestOneU3_410_natDegree_lt_of_posU
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneU3Unique410 a b u) :
    (lWallFanRestOneU3_410 l beta gamma delta zeta eta theta A B U).natDegree <
      3 * u := by
  simp only [lWallFanRestOneU3_410, lWallIntermediateRestOne410,
    fanOneU3Unique410] at *
  compute_degree
  omega

/-! ## Relaxed unique-vertex exclusions -/

theorem fanTwoA5_not_unique_of_posA410
    (l beta gamma delta zeta eta theta k₂ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hl : l ≠ 0) (hAne : A ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂) :
    ¬ fanTwoA5Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantTwoNumerator410_eq_fanA5_add_rest] at hTwo
  apply (smul_add_lower_ne_C410 (63 * l) k₂ (A ^ 5)
    (lWallFanRestTwoA5_410 l beta gamma delta zeta eta theta A B U)
      (5 * a))
  · exact mul_ne_zero (by norm_num) hl
  · exact pow_ne_zero 5 hAne
  · omega
  · rw [natDegree_pow, hA]
  · exact lWallFanRestTwoA5_410_natDegree_lt_of_posA
      l beta gamma delta zeta eta theta A B U a b u ha hA hB hU hunique
  · exact hTwo

theorem fanTwoBU2_not_unique_of_posBU410
    (l beta gamma delta zeta eta theta k₂ : k) (A B U : k[X])
    (a b u : ℕ) (hb : 0 < b) (hu : 0 < u)
    (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂) :
    ¬ fanTwoBU2Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantTwoNumerator410_eq_fanBU2_add_rest] at hTwo
  apply (smul_add_lower_ne_C410 (480 : k) k₂ (B * U ^ 2)
    (lWallFanRestTwoBU2_410 l beta gamma delta zeta eta theta A B U)
      (b + 2 * u))
  · norm_num
  · exact mul_ne_zero hBne (pow_ne_zero 2 hUne)
  · omega
  · rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
  · exact lWallFanRestTwoBU2_410_natDegree_lt_of_posBU
      l beta gamma delta zeta eta theta A B U a b u hb hu hA hB hU hunique
  · exact hTwo

theorem fanOneA4B_not_unique_of_posA410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hl : l ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneA4BUnique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanA4B_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (-(45 * l : k)) k₁ (A ^ 4 * B)
    (lWallFanRestOneA4B_410 l beta gamma delta zeta eta theta A B U)
      (4 * a + b))
  · exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hl)
  · exact mul_ne_zero (pow_ne_zero 4 hAne) hBne
  · omega
  · rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow, hA, hB]
  · exact lWallFanRestOneA4B_410_natDegree_lt_of_posA
      l beta gamma delta zeta eta theta A B U a b u ha hA hB hU hunique
  · exact hOne

theorem fanOneB4_not_unique_of_posB410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (hb : 0 < b) (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneB4Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanB4_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (-(320 : k)) k₁ (B ^ 4)
    (lWallFanRestOneB4_410 l beta gamma delta zeta eta theta A B U)
      (4 * b))
  · norm_num
  · exact pow_ne_zero 4 hBne
  · omega
  · rw [natDegree_pow, hB]
  · exact lWallFanRestOneB4_410_natDegree_lt_of_posB
      l beta gamma delta zeta eta theta A B U a b u hb hA hB hU hunique
  · exact hOne

theorem fanOneU3_not_unique_of_posU410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (hu : 0 < u) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneU3Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanU3_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (-(40 : k)) k₁ (U ^ 3)
    (lWallFanRestOneU3_410 l beta gamma delta zeta eta theta A B U)
      (3 * u))
  · norm_num
  · exact pow_ne_zero 3 hUne
  · omega
  · rw [natDegree_pow, hU]
  · exact lWallFanRestOneU3_410_natDegree_lt_of_posU
      l beta gamma delta zeta eta theta A B U a b u hu hA hB hU hunique
  · exact hOne

/-! ## Exhaustion of the zero-degree boundary -/

theorem lWall410_discriminant_zero_degree_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ terminal : k)
    (A B U : k[X]) (hl : l ≠ 0) (hterminal : terminal ≠ 0)
    (hboundary : A.natDegree = 0 ∨ B.natDegree = 0 ∨ U.natDegree = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁)
    (hTerminal : lWallTerminalNumerator410
      l beta gamma delta zeta eta theta A B U = C terminal) : False := by
  by_cases hA0 : A.natDegree = 0
  · by_cases hB0 : B.natDegree = 0
    · by_cases hU0 : U.natDegree = 0
      · have hdA : derivative A = 0 := derivative_eq_zero.mpr hA0
        have hdB : derivative B = 0 := derivative_eq_zero.mpr hB0
        have hdU : derivative U = 0 := derivative_eq_zero.mpr hU0
        have hzero : lWallTerminalNumerator410
            l beta gamma delta zeta eta theta A B U = 0 := by
          simp [lWallTerminalNumerator410, hdA, hdB, hdU]
        rw [hzero] at hTerminal
        have hcoeff := congrArg (fun P : k[X] => P.coeff 0) hTerminal
        simp only [coeff_zero, coeff_C_zero] at hcoeff
        exact hterminal hcoeff.symm
      · have hUpos : 0 < U.natDegree := by omega
        have hUne : U ≠ 0 := by
          intro hzero
          subst U
          simp at hUpos
        have hunique : fanOneU3Unique410
            A.natDegree B.natDegree U.natDegree := by
          simp only [fanOneU3Unique410]
          omega
        exact (fanOneU3_not_unique_of_posU410
          l beta gamma delta zeta eta theta k₁ A B U
            A.natDegree B.natDegree U.natDegree hUpos hUne
              rfl rfl rfl hOne) hunique
    · have hBpos : 0 < B.natDegree := by omega
      have hBne : B ≠ 0 := by
        intro hzero
        subst B
        simp at hBpos
      by_cases hU0 : U.natDegree = 0
      · have hunique : fanOneB4Unique410
            A.natDegree B.natDegree U.natDegree := by
          simp only [fanOneB4Unique410]
          omega
        exact (fanOneB4_not_unique_of_posB410
          l beta gamma delta zeta eta theta k₁ A B U
            A.natDegree B.natDegree U.natDegree hBpos hBne
              rfl rfl rfl hOne) hunique
      · have hUpos : 0 < U.natDegree := by omega
        have hUne : U ≠ 0 := by
          intro hzero
          subst U
          simp at hUpos
        rcases lt_trichotomy (4 * B.natDegree) (3 * U.natDegree) with
          hBU | hBU | hBU
        · have hunique : fanOneU3Unique410
              A.natDegree B.natDegree U.natDegree := by
            simp only [fanOneU3Unique410]
            omega
          exact (fanOneU3_not_unique_of_posU410
            l beta gamma delta zeta eta theta k₁ A B U
              A.natDegree B.natDegree U.natDegree hUpos hUne
                rfl rfl rfl hOne) hunique
        · have hunique : fanTwoBU2Unique410
              A.natDegree B.natDegree U.natDegree := by
            simp only [fanTwoBU2Unique410]
            omega
          exact (fanTwoBU2_not_unique_of_posBU410
            l beta gamma delta zeta eta theta k₂ A B U
              A.natDegree B.natDegree U.natDegree hBpos hUpos hBne hUne
                rfl rfl rfl hTwo) hunique
        · have hunique : fanOneB4Unique410
              A.natDegree B.natDegree U.natDegree := by
            simp only [fanOneB4Unique410]
            omega
          exact (fanOneB4_not_unique_of_posB410
            l beta gamma delta zeta eta theta k₁ A B U
              A.natDegree B.natDegree U.natDegree hBpos hBne
                rfl rfl rfl hOne) hunique
  · have hApos : 0 < A.natDegree := by omega
    have hAne : A ≠ 0 := by
      intro hzero
      subst A
      simp at hApos
    by_cases hB0 : B.natDegree = 0
    · by_cases hU0 : U.natDegree = 0
      · have hunique : fanTwoA5Unique410
            A.natDegree B.natDegree U.natDegree := by
          simp only [fanTwoA5Unique410]
          omega
        exact (fanTwoA5_not_unique_of_posA410
          l beta gamma delta zeta eta theta k₂ A B U
            A.natDegree B.natDegree U.natDegree hApos hl hAne
              rfl rfl rfl hTwo) hunique
      · have hUpos : 0 < U.natDegree := by omega
        have hUne : U ≠ 0 := by
          intro hzero
          subst U
          simp at hUpos
        by_cases hBzero : B = 0
        · by_cases hUA : U.natDegree < 2 * A.natDegree
          · have hunique : fanTwoA5Unique410
                A.natDegree B.natDegree U.natDegree := by
              simp only [fanTwoA5Unique410]
              omega
            exact (fanTwoA5_not_unique_of_posA410
              l beta gamma delta zeta eta theta k₂ A B U
                A.natDegree B.natDegree U.natDegree hApos hl hAne
                  rfl rfl rfl hTwo) hunique
          · have hunique : fanOneU3Unique410
                A.natDegree B.natDegree U.natDegree := by
              simp only [fanOneU3Unique410]
              omega
            exact (fanOneU3_not_unique_of_posU410
              l beta gamma delta zeta eta theta k₁ A B U
                A.natDegree B.natDegree U.natDegree hUpos hUne
                  rfl rfl rfl hOne) hunique
        · rcases lt_trichotomy (4 * A.natDegree) (3 * U.natDegree) with
            hAU | hAU | hAU
          · have hunique : fanOneU3Unique410
                A.natDegree B.natDegree U.natDegree := by
              simp only [fanOneU3Unique410]
              omega
            exact (fanOneU3_not_unique_of_posU410
              l beta gamma delta zeta eta theta k₁ A B U
                A.natDegree B.natDegree U.natDegree hUpos hUne
                  rfl rfl rfl hOne) hunique
          · have hunique : fanTwoA5Unique410
                A.natDegree B.natDegree U.natDegree := by
              simp only [fanTwoA5Unique410]
              omega
            exact (fanTwoA5_not_unique_of_posA410
              l beta gamma delta zeta eta theta k₂ A B U
                A.natDegree B.natDegree U.natDegree hApos hl hAne
                  rfl rfl rfl hTwo) hunique
          · have hunique : fanOneA4BUnique410
                A.natDegree B.natDegree U.natDegree := by
              simp only [fanOneA4BUnique410]
              omega
            exact (fanOneA4B_not_unique_of_posA410
              l beta gamma delta zeta eta theta k₁ A B U
                A.natDegree B.natDegree U.natDegree hApos hl hAne hBzero
                  rfl rfl rfl hOne) hunique
    · have hBpos : 0 < B.natDegree := by omega
      have hBne : B ≠ 0 := by
        intro hzero
        subst B
        simp at hBpos
      by_cases hU0 : U.natDegree = 0
      · rcases lt_trichotomy (4 * A.natDegree) (3 * B.natDegree) with
          hAB | hAB | hAB
        · have hunique : fanOneB4Unique410
              A.natDegree B.natDegree U.natDegree := by
            simp only [fanOneB4Unique410]
            omega
          exact (fanOneB4_not_unique_of_posB410
            l beta gamma delta zeta eta theta k₁ A B U
              A.natDegree B.natDegree U.natDegree hBpos hBne
                rfl rfl rfl hOne) hunique
        · have hdiv : 3 ∣ A.natDegree := by
            apply (by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_right
            use B.natDegree
            omega
          obtain ⟨n, hnShape⟩ := hdiv
          have hn : 0 < n := by omega
          apply lWall410_lowU_chamber_impossible
            l beta gamma delta zeta eta theta k₂ k₁ A B U n hn
              hAne hBne
          · omega
          · omega
          · omega
          · exact hTwo
          · exact hOne
        · have hunique : fanTwoA5Unique410
              A.natDegree B.natDegree U.natDegree := by
            simp only [fanTwoA5Unique410]
            omega
          exact (fanTwoA5_not_unique_of_posA410
            l beta gamma delta zeta eta theta k₂ A B U
              A.natDegree B.natDegree U.natDegree hApos hl hAne
                rfl rfl rfl hTwo) hunique
      · exact hU0 ((hboundary.resolve_left hA0).resolve_left hB0)

/-! ## Unconditional l-wall closure -/

theorem lWall410_discriminant_unconditional_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ terminal : k)
    (A B U : k[X]) (hl : l ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁)
    (hTerminal : lWallTerminalNumerator410
      l beta gamma delta zeta eta theta A B U = C terminal) : False := by
  by_cases hboundary :
      A.natDegree = 0 ∨ B.natDegree = 0 ∨ U.natDegree = 0
  · exact lWall410_discriminant_zero_degree_impossible
      l beta gamma delta zeta eta theta k₂ k₁ terminal A B U
        hl hterminal hboundary hTwo hOne hTerminal
  · have hApos : 0 < A.natDegree := by omega
    have hBpos : 0 < B.natDegree := by omega
    have hUpos : 0 < U.natDegree := by omega
    have hAne : A ≠ 0 := by
      intro hzero
      subst A
      simp at hApos
    have hBne : B ≠ 0 := by
      intro hzero
      subst B
      simp at hBpos
    have hUne : U ≠ 0 := by
      intro hzero
      subst U
      simp at hUpos
    exact lWall410_discriminant_all_positive_impossible
      l beta gamma delta zeta eta theta k₂ k₁ terminal A B U
        A.natDegree B.natDegree U.natDegree hApos hBpos hUpos hl
          hAne hBne hUne rfl rfl rfl hTwo hOne hTerminal

/-- No degree assumptions remain: a nonzero terminal constant excludes every
source-coordinate trajectory on the normalized `l ≠ 0` wall. -/
theorem lWall410_unconditional_original_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota
      k₂ k₁ terminal : k)
    (A B C0 : k[X]) (hl : l ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hTwoD :
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD :
      lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_discriminant_unconditional_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      (8192 * terminal) A B (A ^ 2 - (4 : k) • C0) hl
        (mul_ne_zero (by norm_num) hterminal) hTwoD hOneD hTerminalD

end LWallZeroDegree410

end Max11DegreeRoutes
