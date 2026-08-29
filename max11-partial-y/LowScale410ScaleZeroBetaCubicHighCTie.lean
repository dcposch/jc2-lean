import LowScale410ScaleZeroBetaCubicNonzeroCTie

/-!
# The strict high-`C0` beta-cubic chamber

On the strict high side, `2 deg A < deg C0`, the cubic tie is
`deg A + deg C0 = 2 deg B`.  The exact zero-load decomposition then exposes
`B C0^2` strictly above both earlier zero-load terms, beta, and every later
load.  Thus only the balanced wall `deg C0 = 2 deg A` survives.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section BetaCubicHighCTie410

variable {k : Type*} [Field k] [CharZero k]

/-- Everything except the distinguished high-`C0` face `B C0^2`. -/
def betaCubicHighCTwoRest410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (-35 / 64 : k) • (A ^ 4 * B) +
    (15 / 8 : k) • (A ^ 2 * B * C0) +
      betaLoadTwoPolynomial410 beta A B C0 +
        betaLoadTwoRest410 gamma delta zeta eta theta A B C0

theorem firstIntegralTwo410_eq_betaCubic_highFace_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    firstIntegralTwoPolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      (15 / 4 : k) • (B * C0 ^ 2) +
        betaCubicHighCTwoRest410 beta gamma delta zeta eta theta A B C0 := by
  rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionTwoPolynomial410_eq_beta_add_rest,
    zeroLoadTwo410_eq_betaCubic_decomposition A B C0 hwall]
  simp only [betaCubicHighCTwoRest410]
  abel

/-- Every omitted zero-load or loaded term is strictly below `B C0^2` in
the strict high-`C0` chamber. -/
theorem betaCubicHighCTwoRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree) (hCpos : 0 < C0.natDegree)
    (hhigh : 2 * A.natDegree < C0.natDegree)
    (htie : A.natDegree + C0.natDegree = 2 * B.natDegree) :
    (betaCubicHighCTwoRest410 beta gamma delta zeta eta theta
      A B C0).natDegree < B.natDegree + 2 * C0.natDegree := by
  simp only [betaCubicHighCTwoRest410, betaLoadTwoPolynomial410,
    betaLoadTwoRest410]
  compute_degree
  omega

/-- The strict high-`C0` chamber is incompatible with a constant first
invariant, with no assumption on later load coefficients. -/
theorem betaCubicWall_high_chamber_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hB : B ≠ 0) (hC0 : C0 ≠ 0)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hhigh : 2 * A.natDegree < C0.natDegree)
    (htie : A.natDegree + C0.natDegree = 2 * B.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) : False := by
  have hCpos : 0 < C0.natDegree := by omega
  have hBpos : 0 < B.natDegree := by omega
  have hrest := betaCubicHighCTwoRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hBpos hCpos hhigh htie
  have hMdeg : (B * C0 ^ 2).natDegree =
      B.natDegree + 2 * C0.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hC0), natDegree_pow]
  have heq :
      (15 / 4 : k) • (B * C0 ^ 2) +
          betaCubicHighCTwoRest410 beta gamma delta zeta eta theta A B C0 =
        C k2 := by
    rw [firstIntegralTwo410_eq_betaCubic_highFace_add_rest
      beta gamma delta zeta eta theta A B C0 hwall] at hTwo
    exact hTwo
  exact (smul_add_lower_ne_C410 (15 / 4 : k) k2 (B * C0 ^ 2)
    (betaCubicHighCTwoRest410 beta gamma delta zeta eta theta A B C0)
    (B.natDegree + 2 * C0.natDegree) (by norm_num)
    (mul_ne_zero hB (pow_ne_zero 2 hC0)) (by omega) hMdeg hrest) heq

/-- Every constant-integral beta-cubic trajectory is therefore on the
balanced wall `deg C0 = 2 deg A`. -/
theorem constantIntegral410_betaCubicWall_balanced
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
    C0.natDegree = 2 * A.natDegree := by
  rcases constantIntegral410_betaCubicWall_balanced_or_high
      alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
        A B C0 hB hterminal hwall hTwo hLower with hbalanced | hhigh
  · exact hbalanced
  · exact (betaCubicWall_high_chamber_impossible
      beta gamma delta zeta eta theta k2 A B C0 hB
        (by
          intro hzero
          rw [hzero, natDegree_zero] at hhigh
          omega)
        hwall hhigh.1 hhigh.2 hTwo).elim

end BetaCubicHighCTie410

end Max11DegreeRoutes
