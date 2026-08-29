import LowScale410ScaleZeroGammaConstantUAndHighBFan

/-!
# Exact first-invariant rays on the positive high-`B` cone

Under `2 deg U <= deg B`, the first invariant has only three possible top
faces: `delta A^2 B`, the fixed `A B^2 U` face, and `B^4`.  Thus the broad
cone reduces to three exact rays when `delta != 0`, and to the single ray
`deg A + deg U = 2 deg B` when `delta = 0`.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaHighBFirstInvariantRays410

variable {k : Type*} [Field k] [CharZero k]

private def highBThreeTie410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
    (d2 = m ∧ d3 = m)

private theorem highB_threeTerm_degree_tie410
    (P1 P2 P3 : k[X]) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hbelow : (P1 + P2 + P3).natDegree <
      max P1.natDegree (max P2.natDegree P3.natDegree)) :
    highBThreeTie410 P1.natDegree P2.natDegree P3.natDegree
      (max P1.natDegree (max P2.natDegree P3.natDegree)) := by
  let m := max P1.natDegree (max P2.natDegree P3.natDegree)
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : (P1 + P2 + P3).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ highBThreeTie410 P1.natDegree P2.natDegree P3.natDegree m
    at hnot
  rcases hcases with h1 | h2 | h3
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highBThreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highBThreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highBThreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highBThreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highBThreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highBThreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree]]
      at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)

private theorem highB_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

def gammaHighBInvariantOneRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(1536 * gamma) : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B - (40 : k) • U ^ 3 +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_highB_threeFaces
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(320 * delta) : k) • (A ^ 2 * B) +
        (960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
        gammaHighBInvariantOneRest410 gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410,
    gammaHighBInvariantOneRest410]
  module

def GammaHighBFirstInvariantRays410
    (delta : k) (A B U : k[X]) : Prop :=
  (delta = 0 ∧ A.natDegree + U.natDegree = 2 * B.natDegree) ∨
    (delta ≠ 0 ∧
      (A.natDegree = B.natDegree + U.natDegree ∨
        2 * A.natDegree = 3 * B.natDegree ∨
        A.natDegree + U.natDegree = 2 * B.natDegree))

theorem gamma_positive_highB_firstInvariant_rays
    (gamma delta zeta eta theta q1 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 2 * U.natDegree ≤ B.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1) :
    GammaHighBFirstInvariantRays410 delta A B U := by
  rw [discriminantInvariantOne410_highB_threeFaces] at hOne
  let P1 : k[X] := (-(320 * delta) : k) • (A ^ 2 * B)
  let P2 : k[X] := (960 : k) • (A * B ^ 2 * U)
  let P3 : k[X] := (-(320 : k)) • B ^ 4
  let R : k[X] := gammaHighBInvariantOneRest410
    gamma delta zeta eta theta A B U
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) hU)
  have hP3 : P3 ≠ 0 := by
    dsimp only [P3]
    exact smul_ne_zero (by norm_num) (pow_ne_zero 4 hB)
  have hP2deg : P2.natDegree =
      A.natDegree + 2 * B.natDegree + U.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
  have hP3deg : P3.natDegree = 4 * B.natDegree := by
    dsimp only [P3]
    rw [natDegree_smul _ (by norm_num), natDegree_pow]
  by_cases hdelta : delta = 0
  · left
    refine ⟨hdelta, ?_⟩
    subst delta
    simp only [mul_zero, neg_zero, zero_smul, zero_add] at hOne
    have hsum : P2 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R]
      linear_combination hOne
    have hR : R.natDegree < max P2.natDegree P3.natDegree := by
      dsimp only [R, gammaHighBInvariantOneRest410]
      rw [hP2deg, hP3deg]
      compute_degree
      omega
    have hbelow : (P2 + P3).natDegree < max P2.natDegree P3.natDegree := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hP2deg, hP3deg]; omega) hR)
    have heq := highB_twoTerm_degree_eq410 P2 P3 hP2 hP3 hbelow
    rw [hP2deg, hP3deg] at heq
    omega
  · right
    refine ⟨hdelta, ?_⟩
    have hP1 : P1 ≠ 0 := by
      dsimp only [P1]
      exact smul_ne_zero
        (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
        (mul_ne_zero (pow_ne_zero 2 hA) hB)
    have hP1deg : P1.natDegree = 2 * A.natDegree + B.natDegree := by
      dsimp only [P1]
      rw [natDegree_smul _
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)),
        natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
    have hsum : P1 + P2 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R]
      linear_combination hOne
    have hR : R.natDegree <
        max P1.natDegree (max P2.natDegree P3.natDegree) := by
      dsimp only [R, gammaHighBInvariantOneRest410]
      rw [hP1deg, hP2deg, hP3deg]
      compute_degree
      omega
    have hbelow : (P1 + P2 + P3).natDegree <
        max P1.natDegree (max P2.natDegree P3.natDegree) := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hP1deg, hP2deg, hP3deg]; omega) hR)
    have htie := highB_threeTerm_degree_tie410
      P1 P2 P3 hP1 hP2 hP3 hbelow
    rw [hP1deg, hP2deg, hP3deg] at htie
    simp only [highBThreeTie410] at htie
    omega

def GammaHighBRefinedPositiveOffTieCones410
    (delta : k) (A B U : k[X]) : Prop :=
  3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree ∨
    (2 * U.natDegree ≤ B.natDegree ∧
      GammaHighBFirstInvariantRays410 delta A B U)

def GammaHighBRefinedSelector410
    (delta : k) (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      GammaHighBRefinedPositiveOffTieCones410 delta A B U

def HighBRefinedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaHighBRefinedSelector410 delta A B (A ^ 2 - (4 : k) • C0)

def HighBRefinedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    HighBRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_highBRefinedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota k2 k1
      terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    l = 0 ∧ HighBRefinedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_constantBoundariesDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hOne0 : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1 := by
    simpa [hold.1, hold.2.1] using hOne
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hdesc := hold.2.2.2.2.1
  have hsel := hold.2.2.2.2.2
  refine ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1,
    hdesc, hsel.1, hsel.2.1, hsel.2.2.1,
    hsel.2.2.2.1, hsel.2.2.2.2.1, ?_⟩
  simp only [GammaHighBRefinedPositiveOffTieCones410]
  rcases hsel.2.2.2.2.2 with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨h4,
      gamma_positive_highB_firstInvariant_rays
        gamma delta zeta eta theta (2048 * k1) A B U
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 h4 hOneD⟩))

theorem integrated410_highBRefinedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ HighBRefinedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_highBRefinedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_highBRefinedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        HighBRefinedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_highBRefinedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaHighBFirstInvariantRays410

end Max11DegreeRoutes
