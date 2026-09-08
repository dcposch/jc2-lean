import Sol68LaterDeepLowerOpenDoubleFiveWallStaggeredNinetySourceScratch

/-! # The exact row-one load at the first double-five lattice point -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallEarliestLoadAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- After the epsilon/A cubic-core cancellation is exposed, the row-one load
at the first lattice point `(n,g)=(90,150)` lies strictly below degree 539.
This is the equality case missed by the termwise offset-ninety cutoff. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_earliest_doubleFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X])
    (hA : A.natDegree ≤ 180)
    (hB : B.natDegree ≤ 120)
    (hc : c.natDegree ≤ 120)
    (hD : D.natDegree ≤ 300)
    (he : e.natDegree ≤ 240) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 539 := by
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
  have hUr : Ur.natDegree ≤ 180 := by
    simp [Ur, cubicLoadUAlphaRestPolynomial68]
    compute_degree
    omega
  have hVr : Vr.natDegree ≤ 390 := by
    simp [Vr, cubicLoadVAlphaRestPolynomial68]
    compute_degree
    omega
  have hVtail : Vtail.natDegree ≤ 120 := by
    simp only [Vtail]
    compute_degree
    omega
  have hC0c : C0c.natDegree ≤ 360 := by
    simp only [C0c]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 300 := by
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
  have hbound (u v : ℕ) (hv : 0 < v) (hu : u + v - 1 < 539) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 539 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v 539 hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 539 :=
    hbound 180 300 (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree < 539 :=
    hbound 120 300 (by omega) (by omega) (alpha • c) Er
      ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree < 539 :=
    hbound 180 300 (by omega) (by omega) _ Er
      ((natDegree_smul_le _ A).trans hA) hEr
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have h4 : ((C epsilon : k[X]) * derivative Er).natDegree < 539 :=
    hbound 0 300 (by omega) (by omega) _ Er heps hEr
  have h5 : (C0c * derivative Vtail).natDegree < 539 :=
    hbound 360 120 (by omega) (by omega) C0c Vtail hC0c hVtail
  have h6 : (c * derivative Vr).natDegree < 539 :=
    hbound 120 390 (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 539 :=
    hbound 300 180 (by omega) (by omega) D Ur hD hUr
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

#print axioms cubicLoadRowOnePolynomial68_degree_lt_earliest_doubleFiveWall

end LaterDeepLowerOpenDoubleFiveWallEarliestLoadAlgebra68

end Max11DegreeRoutes
