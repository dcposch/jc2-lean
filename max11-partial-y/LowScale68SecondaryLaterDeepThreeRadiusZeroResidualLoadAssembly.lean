import LowScale68SecondaryLaterDeepThreeRadiusZeroResidualLoad

/-! # Assembled load cutoff on the zero residual leaf `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusZeroResidualLoadAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_threeRadiusZeroResidual
    (alpha gamma delta epsilon zeta eta : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree < 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B)) 0).natDegree <
        12 * n - 3 * g - 1 := by
  have hD := threeRadiusZeroResidualD68_degree_le A B n g hA hB
  have hUr := threeRadiusZeroResidualUr68_degree_le
    gamma delta zeta A B c n g hwall hA hB
  have hVr := threeRadiusZeroResidualVr68_degree_le
    alpha gamma delta epsilon eta A B c n g hn hwall hA hB hc
  have hVlow := threeRadiusZeroResidualVlow68_degree_le
    gamma delta epsilon eta A B c n g hn hwall hA hB hc
  have hC0c := threeRadiusZeroResidualC0c68_degree_le A n hA
  have hEr := threeRadiusZeroResidualEr68_degree_le A c n g hn hwall hA hc
  have hE := threeRadiusZeroResidualE68_degree_le A c n g hA hc
  let D0 := threeRadiusZeroResidualD68 A B
  let Ur := threeRadiusZeroResidualUr68 gamma delta zeta A B c
  let Vr := threeRadiusZeroResidualVr68 alpha gamma delta epsilon eta A B c
  let Vlow := threeRadiusZeroResidualVlow68 gamma delta epsilon eta A B c
  let C0c := threeRadiusZeroResidualC0c68 A
  let Er := threeRadiusZeroResidualEr68 A c
  let E0 := threeRadiusZeroResidualE68 A c
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D0).natDegree < 12 * n - 3 * g - 1 :=
    hbound (2 * n) (5 * n - g) (by omega) (by omega) Ur D0 hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (2 * n) (6 * n - g) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er ((natDegree_smul_le _ A).trans hA) hEr
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have h4 : ((C epsilon : k[X]) * derivative E0).natDegree <
      12 * n - 3 * g - 1 :=
    hbound 0 (6 * n) (by omega) (by omega) _ E0 heps hE
  have h5 : (C0c * derivative Vlow).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (4 * n) (4 * n - g) (by omega) (by omega)
      C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      c Vr hc hVr
  have h7 : (D0 * derivative Ur).natDegree < 12 * n - 3 * g - 1 :=
    hbound (5 * n - g) (2 * n) (by omega) (by omega) D0 Ur hD hUr
  have hsum : (Ur * derivative D0 +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • ((C epsilon : k[X]) * derivative E0) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D0 * derivative Ur).natDegree < 12 * n - 3 * g - 1 :=
    deepGap_natDegree_sub_lt
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
  rw [show (1 / 3 : k) • (A * B) = threeRadiusZeroResidualD68 A B by rfl,
    cubicLoadRowOnePolynomial68_eq_threeRadiusZeroResidualLoad]
  simp only [threeRadiusZeroResidualLoadRowOne68,
    cubicLoadRowOneDeepGapRestPolynomial68, zero_mul, mul_zero, zero_smul,
    smul_zero, add_zero, zero_add]
  exact hsum

#print axioms cubicLoadRowOnePolynomial68_degree_lt_threeRadiusZeroResidual

end LaterDeepThreeRadiusZeroResidualLoadAssembly68

end Max11DegreeRoutes
