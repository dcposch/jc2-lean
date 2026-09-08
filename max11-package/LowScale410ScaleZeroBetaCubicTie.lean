import LowScale410ScaleZeroBetaCubicWall

/-!
# Closing the `C0 = 0` beta-cubic tie chamber

On the beta cubic wall, `C0 = 0` gives the binomial identity
`5 A^3 = 4 B^2`.  Its positive-degree ray exposes the zero-load monomial
`A^4 B` strictly above beta and every later load in the first invariant.
The degree-zero endpoint instead makes the terminal row vanish.  Hence the
entire chamber is empty without any later-load vanishing assumption.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section BetaCubicTie410

variable {k : Type*} [Field k] [CharZero k]

/-- On the `C0 = 0` cubic wall, the zero-load first invariant collapses to
one nonzero scalar multiple of `A^4 B`. -/
theorem zeroLoadTwo410_eq_singleFace_of_betaCubic_C0_zero
    (A B : k[X]) (hwall : betaOneCorePolynomial410 A B 0 = 0) :
    firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B 0 =
      (-35 / 64 : k) • (A ^ 4 * B) := by
  have hbinomial : (5 : k) • A ^ 3 - (4 : k) • B ^ 2 = 0 := by
    simpa [betaOneCorePolynomial410] using hwall
  have hface :
      (5 : k) • (A ^ 4 * B) - (4 : k) • (A * B ^ 3) = 0 := by
    calc
      (5 : k) • (A ^ 4 * B) - (4 : k) • (A * B ^ 3) =
          A * B * ((5 : k) • A ^ 3 - (4 : k) • B ^ 2) := by
            simp only [Polynomial.smul_eq_C_mul]
            ring
      _ = 0 := by rw [hbinomial, mul_zero]
  have hrel : (5 : k) • (A ^ 4 * B) =
      (4 : k) • (A * B ^ 3) := sub_eq_zero.mp hface
  have hN : A * B ^ 3 = (5 / 4 : k) • (A ^ 4 * B) := by
    calc
      A * B ^ 3 = (1 / 4 : k) • ((4 : k) • (A * B ^ 3)) := by
        module
      _ = (1 / 4 : k) • ((5 : k) • (A ^ 4 * B)) := by rw [← hrel]
      _ = (5 / 4 : k) • (A ^ 4 * B) := by module
  rw [zeroLoadTwo410_eq]
  simp only [mul_zero, zero_mul, smul_zero, add_zero, sub_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [hN]
  module

/-- Every beta-or-later contribution lies strictly below `A^4 B` on the
positive `3 deg A = 2 deg B` ray. -/
theorem betaAndLaterTwo410_natDegree_lt_singleFace
    (beta gamma delta zeta eta theta : k) (A B : k[X])
    (hApos : 0 < A.natDegree) (hBpos : 0 < B.natDegree)
    (hdegrees : 3 * A.natDegree = 2 * B.natDegree) :
    (betaLoadTwoPolynomial410 beta A B 0 +
        betaLoadTwoRest410 gamma delta zeta eta theta A B 0).natDegree <
      4 * A.natDegree + B.natDegree := by
  simp only [betaLoadTwoPolynomial410, betaLoadTwoRest410, mul_zero,
    zero_mul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

/-- The positive-degree `C0 = 0` cubic ray is incompatible with a constant
first invariant. -/
theorem betaCubicWall_C0_zero_positive_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B : k[X])
    (hB : B ≠ 0) (hApos : 0 < A.natDegree)
    (hwall : betaOneCorePolynomial410 A B 0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B 0 = C k2) : False := by
  have hsplit := betaCubicWall_degree_split A B 0 hB hwall
  have hdegrees : 3 * A.natDegree = 2 * B.natDegree := by
    rcases hsplit with hzero | hnonzero
    · exact hzero.2
    · exact (hnonzero.1 rfl).elim
  have hBpos : 0 < B.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    exact (lt_irrefl 0 hApos)
  have hface := zeroLoadTwo410_eq_singleFace_of_betaCubic_C0_zero
    A B hwall
  have hrest := betaAndLaterTwo410_natDegree_lt_singleFace
    beta gamma delta zeta eta theta A B hApos hBpos hdegrees
  have hMdeg : (A ^ 4 * B).natDegree =
      4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hB, natDegree_pow]
  have heq :
      (-35 / 64 : k) • (A ^ 4 * B) +
          (betaLoadTwoPolynomial410 beta A B 0 +
            betaLoadTwoRest410 gamma delta zeta eta theta A B 0) = C k2 := by
    rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
      loadCorrectionTwoPolynomial410_eq_beta_add_rest, hface] at hTwo
    simpa only [add_assoc] using hTwo
  exact (smul_add_lower_ne_C410 (-35 / 64 : k) k2 (A ^ 4 * B)
    (betaLoadTwoPolynomial410 beta A B 0 +
      betaLoadTwoRest410 gamma delta zeta eta theta A B 0)
    (4 * A.natDegree + B.natDegree) (by norm_num)
    (mul_ne_zero (pow_ne_zero 4 hA) hB) (by omega) hMdeg hrest) heq

/-- At the degree-zero endpoint, the terminal `Z` primitive has zero
derivative. -/
theorem derivative_integratedZPolynomial410_eq_zero_of_C0_zero
    (alpha beta gamma delta epsilon zeta eta iota : k) (A B : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0) :
    derivative
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta iota
        A B 0) = 0 := by
  have hdA : derivative A = 0 := derivative_eq_zero.mpr hA
  have hdB : derivative B = 0 := derivative_eq_zero.mpr hB
  simp only [integratedZPolynomial410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.derivative_zero, hdA, hdB, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero, smul_zero]

/-- The degree-zero endpoint of the cubic ray is excluded by the nonzero
terminal constant. -/
theorem betaCubicWall_C0_zero_constants_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B : k[X]) (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B 0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B 0) B 0 = C terminal) : False := by
  have hdZ := derivative_integratedZPolynomial410_eq_zero_of_C0_zero
    alpha beta gamma delta epsilon zeta eta iota A B hA hB
  have hzero : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B 0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B 0) B 0 = 0 := by
    simp only [lowerRowZeroPolynomial410, derivative_zero, mul_zero, hdZ,
      zero_mul, sub_zero]
  rw [hzero] at hLower
  exact hterminal (C_eq_zero.mp hLower.symm)

/-- Complete exclusion of the `C0 = 0` beta-cubic chamber.  Positive degree
is killed by the first invariant; degree zero is killed by the terminal
row. -/
theorem betaCubicWall_C0_zero_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B : k[X]) (hB : B ≠ 0) (hterminal : terminal ≠ 0)
    (hwall : betaOneCorePolynomial410 A B 0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B 0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B 0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B 0) B 0 = C terminal) : False := by
  by_cases hApos : 0 < A.natDegree
  · exact betaCubicWall_C0_zero_positive_impossible
      beta gamma delta zeta eta theta k2 A B hB hApos hwall hTwo
  · have hA0 : A.natDegree = 0 := by omega
    have hdegrees : 3 * A.natDegree = 2 * B.natDegree :=
      ((betaCubicWall_degree_split A B 0 hB hwall).resolve_right
        (by intro h; exact h.1 rfl)).2
    have hB0 : B.natDegree = 0 := by omega
    exact betaCubicWall_C0_zero_constants_impossible
      alpha beta gamma delta epsilon zeta eta theta iota terminal A B
        hA0 hB0 hterminal hLower

/-- Consequently every surviving beta-cubic trajectory has `C0 != 0` and
lies on the genuine three-face tie among `3 deg A`, `deg A + deg C0`, and
`2 deg B`. -/
theorem constantIntegral410_betaCubicWall_nonzeroC_degree_tie
    (alpha beta gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X]) (hB : B ≠ 0) (hterminal : terminal ≠ 0)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    C0 ≠ 0 ∧
      (((3 * A.natDegree =
            max (3 * A.natDegree)
              (max (A.natDegree + C0.natDegree) (2 * B.natDegree))) ∧
          (A.natDegree + C0.natDegree =
            max (3 * A.natDegree)
              (max (A.natDegree + C0.natDegree) (2 * B.natDegree)))) ∨
        ((3 * A.natDegree =
            max (3 * A.natDegree)
              (max (A.natDegree + C0.natDegree) (2 * B.natDegree))) ∧
          (2 * B.natDegree =
            max (3 * A.natDegree)
              (max (A.natDegree + C0.natDegree) (2 * B.natDegree)))) ∨
        ((A.natDegree + C0.natDegree =
            max (3 * A.natDegree)
              (max (A.natDegree + C0.natDegree) (2 * B.natDegree))) ∧
          (2 * B.natDegree =
            max (3 * A.natDegree)
              (max (A.natDegree + C0.natDegree) (2 * B.natDegree))))) := by
  have hC : C0 ≠ 0 := by
    intro hC0
    subst C0
    exact betaCubicWall_C0_zero_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
        A B hB hterminal hwall hTwo hLower
  refine ⟨hC, ?_⟩
  have htie := ((betaCubicWall_degree_split A B C0 hB hwall).resolve_left
    (by intro h; exact hC h.1)).2
  exact htie

end BetaCubicTie410

end Max11DegreeRoutes
