import LowScale410ScaleZeroDeltaLaterFixedTie

/-!
# Exact principal-face fan for the delta-plus-later-load sibling

For positive coordinate degrees, the zeta/eta/theta tail lies strictly below
the five principal I2 faces.  Constancy therefore forces at least two of
those five faces to share the maximal degree.  We expose the resulting nine
degree hyperplanes, retaining degree-zero boundaries explicitly.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaLaterEnvelopeFan410

variable {k : Type*} [Field k] [CharZero k]

private def deltaLaterFiveDegreeTie410
    (d1 d2 d3 d4 d5 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d1 = m ∧ d5 = m) ∨
  (d2 = m ∧ d3 = m) ∨ (d2 = m ∧ d4 = m) ∨
  (d2 = m ∧ d5 = m) ∨ (d3 = m ∧ d4 = m) ∨
  (d3 = m ∧ d5 = m) ∨ (d4 = m ∧ d5 = m)

private theorem deltaLater_fiveTerm_degree_tie410
    (P1 P2 P3 P4 P5 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hP4 : P4 ≠ 0) (hP5 : P5 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4 + P5).natDegree <
      max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) :
    deltaLaterFiveDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
      P4.natDegree P5.natDegree
      (max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) := by
  let m := max P1.natDegree (max P2.natDegree
    (max P3.natDegree (max P4.natDegree P5.natDegree)))
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have h4le : P4.natDegree ≤ m := by dsimp [m]; omega
  have h5le : P5.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m ∨ P4.natDegree = m ∨ P5.natDegree = m := by
    dsimp [m]
    omega
  have hsumcoeff : (P1 + P2 + P3 + P4 + P5).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ deltaLaterFiveDegreeTie410 P1.natDegree P2.natDegree
    P3.natDegree P4.natDegree P5.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h1, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h2, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h3, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h4, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h5, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h5, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h5, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveDegreeTie410, h5, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      show P5.coeff m = P5.leadingCoeff by rw [← h5, coeff_natDegree]]
      at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP5) (by simpa using hsumcoeff)

def deltaLaterI2PrincipalSum410 (delta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 + (-(1280 : k)) • (A * B ^ 3) +
    (-(640 * delta : k)) • (A * U) +
    (1280 * delta : k) • B ^ 2 + (480 : k) • (B * U ^ 2)

theorem discriminantInvariantTwo410_zeroGamma_eq_principal_add_tail
    (delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 0 delta zeta eta theta A B U =
      deltaLaterI2PrincipalSum410 delta A B U +
        deltaLaterI2Tail410 zeta eta theta A B U := by
  simp [discriminantInvariantTwoNumerator410,
    deltaLaterI2PrincipalSum410, deltaLaterI2Tail410] <;> module

def DeltaLaterPositivePrincipalDegreeFan410 (A B U : k[X]) : Prop :=
  2 * A.natDegree = 3 * B.natDegree ∨
    U.natDegree = 2 * A.natDegree ∨
    3 * A.natDegree = 2 * B.natDegree ∨
    3 * A.natDegree = B.natDegree + 2 * U.natDegree ∨
    U.natDegree = 3 * B.natDegree ∨
    A.natDegree + 2 * B.natDegree = 2 * U.natDegree ∨
    A.natDegree + U.natDegree = 2 * B.natDegree ∨
    A.natDegree = B.natDegree + U.natDegree ∨
    B.natDegree = 2 * U.natDegree

theorem constantDiscriminantI2_deltaLater_positive_principal_fan
    (delta zeta eta theta q : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hApos : 0 < A.natDegree) (hBpos : 0 < B.natDegree)
    (hUpos : 0 < U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q) :
    DeltaLaterPositivePrincipalDegreeFan410 A B U := by
  let P1 : k[X] := (320 * delta : k) • A ^ 3
  let P2 : k[X] := (-(1280 : k)) • (A * B ^ 3)
  let P3 : k[X] := (-(640 * delta : k)) • (A * U)
  let P4 : k[X] := (1280 * delta : k) • B ^ 2
  let P5 : k[X] := (480 : k) • (B * U ^ 2)
  let T : k[X] := deltaLaterI2Tail410 zeta eta theta A B U
  let M : ℕ := max P1.natDegree (max P2.natDegree
    (max P3.natDegree (max P4.natDegree P5.natDegree)))
  have hP1 : P1 ≠ 0 := by
    dsimp only [P1]
    exact smul_ne_zero (mul_ne_zero (by norm_num) hdelta) (pow_ne_zero 3 hA)
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (by norm_num) (mul_ne_zero hA (pow_ne_zero 3 hB))
  have hP3 : P3 ≠ 0 := by
    dsimp only [P3]
    exact smul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
      (mul_ne_zero hA hU)
  have hP4 : P4 ≠ 0 := by
    dsimp only [P4]
    exact smul_ne_zero (mul_ne_zero (by norm_num) hdelta) (pow_ne_zero 2 hB)
  have hP5 : P5 ≠ 0 := by
    dsimp only [P5]
    exact smul_ne_zero (by norm_num) (mul_ne_zero hB (pow_ne_zero 2 hU))
  have hP1deg : P1.natDegree = 3 * A.natDegree := by
    dsimp only [P1]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
  have hP2deg : P2.natDegree = A.natDegree + 3 * B.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hP3deg : P3.natDegree = A.natDegree + U.natDegree := by
    dsimp only [P3]
    rw [natDegree_smul _ (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)),
      natDegree_mul hA hU]
  have hP4deg : P4.natDegree = 2 * B.natDegree := by
    dsimp only [P4]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
  have hP5deg : P5.natDegree = B.natDegree + 2 * U.natDegree := by
    dsimp only [P5]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
  have hT : T.natDegree < M := by
    dsimp only [T, M]
    simp only [deltaLaterI2Tail410]
    rw [hP1deg, hP2deg, hP3deg, hP4deg, hP5deg]
    compute_degree
    omega
  have hMpos : 0 < M := by
    dsimp only [M]
    rw [hP1deg, hP2deg, hP3deg, hP4deg, hP5deg]
    omega
  have hdecomp := discriminantInvariantTwo410_zeroGamma_eq_principal_add_tail
    delta zeta eta theta A B U
  have hsumEq : P1 + P2 + P3 + P4 + P5 + T = C q := by
    rw [← hTwo, hdecomp]
    dsimp only [deltaLaterI2PrincipalSum410, P1, P2, P3, P4, P5, T]
  have hsum : P1 + P2 + P3 + P4 + P5 = C q - T := by
    linear_combination hsumEq
  have hC : (C q : k[X]).natDegree < M := by
    rw [natDegree_C]
    omega
  have hbelow : (P1 + P2 + P3 + P4 + P5).natDegree < M := by
    rw [hsum]
    exact (natDegree_sub_le _ _).trans_lt (max_lt hC hT)
  have hties := deltaLater_fiveTerm_degree_tie410
    P1 P2 P3 P4 P5 hP1 hP2 hP3 hP4 hP5 (by simpa only [M] using hbelow)
  simp only [deltaLaterFiveDegreeTie410] at hties
  rcases hties with h12 | h13 | h14 | h15 | h23 | h24 | h25 | h34 | h35 | h45
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))))

def DeltaLaterExactEnvelopeFan410 (A B U : k[X]) : Prop :=
  A.natDegree = 0 ∨ B.natDegree = 0 ∨ U.natDegree = 0 ∨
    DeltaLaterPositivePrincipalDegreeFan410 A B U

def DeltaLaterEnvelopeFanPacket410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧ DeltaLaterExactEnvelopeFan410 A B U

theorem deltaLater_fixedTieDeleted_exactEnvelopeFan_refinement
    (delta zeta eta theta q : k) (A B U : k[X])
    (hdelta : delta ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q)
    (hold : DeltaLaterFixedTieDeletedPacket410 A B U) :
    DeltaLaterEnvelopeFanPacket410 A B U := by
  refine ⟨hold.1, hold.2.1, hold.2.2.1, ?_⟩
  by_cases hA0 : A.natDegree = 0
  · exact Or.inl hA0
  by_cases hB0 : B.natDegree = 0
  · exact Or.inr (Or.inl hB0)
  by_cases hU0 : U.natDegree = 0
  · exact Or.inr (Or.inr (Or.inl hU0))
  · exact Or.inr (Or.inr (Or.inr
      (constantDiscriminantI2_deltaLater_positive_principal_fan
        delta zeta eta theta q A B U hdelta hold.1 hold.2.1 hold.2.2.1
          (by omega) (by omega) (by omega) hTwo)))

def GammaClosedDeltaEnvelopeFanNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCorePrincipalWallDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DeltaLaterEnvelopeFanPacket410 A B
        (A ^ 2 - (4 : k) • C0))

theorem constantIntegral410_gammaClosedDeltaEnvelopeFanNoncubic_residual
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
    l = 0 ∧ GammaClosedDeltaEnvelopeFanNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaClosedDeltaFixedTieDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · exact Or.inl hgamma
  · right
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hTwo
    have hTwoD : discriminantInvariantTwoNumerator410
        0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
          C (2048 * k2) := by
      rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo0,
        Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
    exact ⟨hdelta.1, hdelta.2.1, hdelta.2.2.1, hdelta.2.2.2.1,
      deltaLater_fixedTieDeleted_exactEnvelopeFan_refinement
        delta zeta eta theta (2048 * k2) A B
          (A ^ 2 - (4 : k) • C0) hdelta.2.2.1 hTwoD
            hdelta.2.2.2.2⟩

theorem integrated410_gammaClosedDeltaEnvelopeFanNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaClosedDeltaEnvelopeFanNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaClosedDeltaEnvelopeFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaClosedDeltaEnvelopeFanNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaClosedDeltaEnvelopeFanNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaClosedDeltaEnvelopeFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end DeltaLaterEnvelopeFan410

end Max11DegreeRoutes
