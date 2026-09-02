import Sol68LaterDeepLowerOpenDoubleFiveWallEarliestOffsetOneFiftySourceScratch

/-! # Uniform row-load cutoff at aligned offset 120 -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedOneTwentyLoad68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem doubleFiveWall_oneEighty_lattice_load_split68
    (n g : ℕ) (hn : 0 < n) (hndiv : 180 ∣ n) (hwall : 3 * g = 5 * n) :
    (n = 180 ∧ g = 300) ∨ 120 < 4 * n - 2 * g := by
  obtain ⟨u, hu⟩ := hndiv
  by_cases hone : u = 1
  · left
    constructor <;> omega
  · right
    have hu2 : 2 ≤ u := by omega
    omega

/-- The epsilon/A cubic-core pair cancels identically.  After removing it,
the genuinely lower `Vlow` tail gives a uniform offset-120 cutoff, including
the arithmetic equality point `n=180`. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_offsetOneTwenty_of_doubleFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hn120 : 120 ≤ n) (hg : 120 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - 120)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 121 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c D e rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Vtail := (2 / 3 * gamma : k) • c +
    (1 / 2 * delta : k) • B + C eta
  let C0c := (1 / 3 : k) • A ^ 2
  let Er := (1 / 3 : k) • (A * c) + e
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB (hc.trans (by omega))
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB (hc.trans (by omega)) hD (he.trans (by omega))
  have hVtail : Vtail.natDegree ≤ 4 * n - g - 120 := by
    simp only [Vtail]
    compute_degree
    omega
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g - 120 := by
    simp only [Er]
    compute_degree
    omega
  have hdecomp :
      cubicLoadRowOneDeepGapRestPolynomial68 alpha 0 gamma delta epsilon
          zeta eta A B c D e =
        Ur * derivative D +
          (2 : k) • ((alpha • c) * derivative Er) +
          (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
          (2 : k) • ((C epsilon : k[X]) * derivative Er) -
          (2 : k) • (C0c * derivative Vtail) -
          (2 : k) • (c * derivative Vr) -
          D * derivative Ur := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowOneDeepGapRestPolynomial68, Ur, Vr, Vtail,
      C0c, Er, cubicLoadVAlphaLowPolynomial68, zero_mul, zero_smul,
      zero_add, add_zero, sub_zero, derivative_add, derivative_smul,
      derivative_pow, derivative_mul, derivative_C,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_zero, RatFunc.algebraMap_C]
    simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  rw [hdecomp]
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - 121) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 121 :=
    fun p q hp hq => deepGap_natDegree_mul_derivative_lt68 p q u v
      (12 * n - 3 * g - 121) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - 121 :=
    hbound (2 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - 121 :=
    hbound (4 * n - g - 120) (6 * n - g - 120) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - 121 :=
    hbound (2 * n) (6 * n - g - 120) (by omega) (by omega) _ Er
      ((natDegree_smul_le _ A).trans hA) hEr
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have h4 : ((C epsilon : k[X]) * derivative Er).natDegree <
      12 * n - 3 * g - 121 :=
    hbound 0 (6 * n - g - 120) (by omega) (by omega) _ Er heps hEr
  have h5 : (C0c * derivative Vtail).natDegree <
      12 * n - 3 * g - 121 :=
    hbound (4 * n) (4 * n - g - 120) (by omega) (by omega)
      C0c Vtail hC0c hVtail
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - 121 :=
    hbound (4 * n - g - 120) (6 * n - g) (by omega) (by omega)
      c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 3 * g - 121 :=
    hbound (5 * n - g) (2 * n) (by omega) (by omega) D Ur hD hUr
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1
              (deepGap_natDegree_smul_lt68 (2 : k) h2))
              (deepGap_natDegree_smul_lt68 (2 : k) h3))
            (deepGap_natDegree_smul_lt68 (2 : k) h4))
          (deepGap_natDegree_smul_lt68 (2 : k) h5))
        (deepGap_natDegree_smul_lt68 (2 : k) h6)) h7

#print axioms doubleFiveWall_oneEighty_lattice_load_split68
#print axioms cubicLoadRowOnePolynomial68_degree_lt_offsetOneTwenty_of_doubleFiveWall

end LaterDeepLowerOpenDoubleFiveWallAlignedOneTwentyLoad68

end Max11DegreeRoutes
