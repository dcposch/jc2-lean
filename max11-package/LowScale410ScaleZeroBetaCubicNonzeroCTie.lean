import LowScale410ScaleZeroBetaCubicTie

/-!
# The strict low-`C0` chamber of the beta cubic wall

Modulo the cubic wall, the zero-load first invariant has a distinguished
`A^4 B` term and only two `C0`-dependent corrections.  In the chamber
`deg C0 < 2 deg A`, the exact cubic degree tie is `3 deg A = 2 deg B`, so
that distinguished term lies strictly above beta and every later load.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section BetaCubicNonzeroCTie410

variable {k : Type*} [Field k] [CharZero k]

/-- Exact reduction of the zero-load first invariant modulo the beta cubic
wall. -/
theorem zeroLoadTwo410_eq_betaCubic_decomposition
    (A B C0 : k[X]) (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 =
      (-35 / 64 : k) • (A ^ 4 * B) +
        (15 / 8 : k) • (A ^ 2 * B * C0) +
          (15 / 4 : k) • (B * C0 ^ 2) := by
  have hface :
      (5 : k) • (A ^ 4 * B) - (24 : k) • (A ^ 2 * B * C0) -
          (4 : k) • (A * B ^ 3) = 0 := by
    calc
      (5 : k) • (A ^ 4 * B) - (24 : k) • (A ^ 2 * B * C0) -
          (4 : k) • (A * B ^ 3) =
        A * B * betaOneCorePolynomial410 A B C0 := by
          simp only [betaOneCorePolynomial410, Polynomial.smul_eq_C_mul]
          ring
      _ = 0 := by rw [hwall, mul_zero]
  have hrel :
      (5 : k) • (A ^ 4 * B) - (24 : k) • (A ^ 2 * B * C0) =
        (4 : k) • (A * B ^ 3) := sub_eq_zero.mp hface
  have hN : A * B ^ 3 =
      (5 / 4 : k) • (A ^ 4 * B) -
        (6 : k) • (A ^ 2 * B * C0) := by
    calc
      A * B ^ 3 = (1 / 4 : k) • ((4 : k) • (A * B ^ 3)) := by
        module
      _ = (1 / 4 : k) •
          ((5 : k) • (A ^ 4 * B) -
            (24 : k) • (A ^ 2 * B * C0)) := by rw [← hrel]
      _ = (5 / 4 : k) • (A ^ 4 * B) -
          (6 : k) • (A ^ 2 * B * C0) := by module
  rw [zeroLoadTwo410_eq, hN]
  module

/-- Everything except the distinguished `A^4 B` zero-load face. -/
def betaCubicLowCTwoRest410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (15 / 8 : k) • (A ^ 2 * B * C0) +
    (15 / 4 : k) • (B * C0 ^ 2) +
      betaLoadTwoPolynomial410 beta A B C0 +
        betaLoadTwoRest410 gamma delta zeta eta theta A B C0

theorem firstIntegralTwo410_eq_betaCubic_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    firstIntegralTwoPolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      (-35 / 64 : k) • (A ^ 4 * B) +
        betaCubicLowCTwoRest410 beta gamma delta zeta eta theta A B C0 := by
  rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionTwoPolynomial410_eq_beta_add_rest,
    zeroLoadTwo410_eq_betaCubic_decomposition A B C0 hwall]
  simp only [betaCubicLowCTwoRest410]
  abel

/-- In the strict low-`C0` chamber every omitted term is below `A^4 B`.
No load coefficient is assumed to vanish. -/
theorem betaCubicLowCTwoRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree) (hBpos : 0 < B.natDegree)
    (hdegrees : 3 * A.natDegree = 2 * B.natDegree)
    (hC : C0.natDegree < 2 * A.natDegree) :
    (betaCubicLowCTwoRest410 beta gamma delta zeta eta theta
      A B C0).natDegree < 4 * A.natDegree + B.natDegree := by
  simp only [betaCubicLowCTwoRest410, betaLoadTwoPolynomial410,
    betaLoadTwoRest410]
  compute_degree
  omega

/-- The strict low-`C0` chamber is empty.  The first invariant alone gives
the contradiction after the terminal row is used only to invoke the exact
three-face selector. -/
theorem betaCubicWall_nonzeroC_low_chamber_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X]) (hB : B ≠ 0) (hC0 : C0 ≠ 0)
    (hterminal : terminal ≠ 0)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hClow : C0.natDegree < 2 * A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have htie := constantIntegral410_betaCubicWall_nonzeroC_degree_tie
    alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
      A B C0 hB hterminal hwall hTwo hLower
  have hdegrees : 3 * A.natDegree = 2 * B.natDegree := by
    rcases htie.2 with h12 | h13 | h23
    · omega
    · exact h13.1.trans h13.2.symm
    · omega
  have hApos : 0 < A.natDegree := by omega
  have hBpos : 0 < B.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    exact (lt_irrefl 0 hApos)
  have hrest := betaCubicLowCTwoRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hApos hBpos hdegrees hClow
  have hMdeg : (A ^ 4 * B).natDegree =
      4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hB, natDegree_pow]
  have heq :
      (-35 / 64 : k) • (A ^ 4 * B) +
          betaCubicLowCTwoRest410 beta gamma delta zeta eta theta A B C0 =
        C k2 := by
    rw [firstIntegralTwo410_eq_betaCubic_face_add_rest
      beta gamma delta zeta eta theta A B C0 hwall] at hTwo
    exact hTwo
  exact (smul_add_lower_ne_C410 (-35 / 64 : k) k2 (A ^ 4 * B)
    (betaCubicLowCTwoRest410 beta gamma delta zeta eta theta A B C0)
    (4 * A.natDegree + B.natDegree) (by norm_num)
    (mul_ne_zero (pow_ne_zero 4 hA) hB) (by omega) hMdeg hrest) heq

/-- Every remaining beta-cubic trajectory lies either on the balanced
`deg C0 = 2 deg A` wall or in the strict high-`C0` chamber, where the cubic
tie is necessarily `deg A + deg C0 = 2 deg B`. -/
theorem constantIntegral410_betaCubicWall_balanced_or_high
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
    C0.natDegree = 2 * A.natDegree ∨
      (2 * A.natDegree < C0.natDegree ∧
        A.natDegree + C0.natDegree = 2 * B.natDegree) := by
  have hnonzeroTie := constantIntegral410_betaCubicWall_nonzeroC_degree_tie
    alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
      A B C0 hB hterminal hwall hTwo hLower
  rcases lt_trichotomy C0.natDegree (2 * A.natDegree) with hlow | heq | hhigh
  · exact (betaCubicWall_nonzeroC_low_chamber_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
        A B C0 hB hnonzeroTie.1 hterminal hwall hlow hTwo hLower).elim
  · exact Or.inl heq
  · right
    refine ⟨hhigh, ?_⟩
    rcases hnonzeroTie.2 with h12 | h13 | h23
    · omega
    · omega
    · exact h23.1.trans h23.2.symm

end BetaCubicNonzeroCTie410

end Max11DegreeRoutes
