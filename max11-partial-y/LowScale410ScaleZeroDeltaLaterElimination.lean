import LowScale410ScaleZeroDeltaLaterEnvelopeFan

/-!
# Elimination of the delta-plus-later-load sibling

The effective later loads are strictly below the five pure-delta faces in
both discriminant invariants and in the exact terminal primitive.  Thus the
three five-face ties from the pure delta wall survive unchanged.  Their
degree intersection is the `(8,7,11)` ray, whose two fixed-face leading
coefficient equations are incompatible.  The same argument also deletes
all degree-zero coordinate boundaries.
-/

noncomputable section

set_option maxHeartbeats 8000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaLaterElimination410

variable {k : Type*} [Field k] [CharZero k]

private def deltaLaterFiveTie410
    (d1 d2 d3 d4 d5 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d1 = m ∧ d5 = m) ∨
  (d2 = m ∧ d3 = m) ∨ (d2 = m ∧ d4 = m) ∨
  (d2 = m ∧ d5 = m) ∨ (d3 = m ∧ d4 = m) ∨
  (d3 = m ∧ d5 = m) ∨ (d4 = m ∧ d5 = m)

private theorem deltaLater_fiveTerm_tie410
    (P1 P2 P3 P4 P5 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hP4 : P4 ≠ 0) (hP5 : P5 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4 + P5).natDegree <
      max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) :
    deltaLaterFiveTie410 P1.natDegree P2.natDegree P3.natDegree
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
  change ¬ deltaLaterFiveTie410 P1.natDegree P2.natDegree
    P3.natDegree P4.natDegree P5.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h1, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h1, heq])
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
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h2, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h2, heq])
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
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h3, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h3, heq])
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
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h4, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h4, heq])
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
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h5, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h5, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h5, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [deltaLaterFiveTie410, h5, heq])
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

private def deltaLaterI2DegreeTie410 (a b u : ℕ) : Prop :=
  deltaLaterFiveTie410 (3 * a) (a + u) (2 * b) (a + 3 * b) (b + 2 * u)
    (max (3 * a) (max (a + u) (max (2 * b) (max (a + 3 * b) (b + 2 * u)))))

private def deltaLaterI1DegreeTie410 (a b u : ℕ) : Prop :=
  deltaLaterFiveTie410 (2 * a + b) (b + u) (a + 2 * b + u) (4 * b) (3 * u)
    (max (2 * a + b)
      (max (b + u) (max (a + 2 * b + u) (max (4 * b) (3 * u)))))

private def deltaLaterPrimitiveDegreeTie410 (a b u : ℕ) : Prop :=
  deltaLaterFiveTie410 (4 * a) (2 * a + u) (a + 2 * b) (3 * b + u) (2 * u)
    (max (4 * a)
      (max (2 * a + u) (max (a + 2 * b) (max (3 * b + u) (2 * u)))))

private theorem deltaLater_three_degree_ties_force_ray410
    (a b u : ℕ) (hpositive : 0 < a ∨ 0 < b ∨ 0 < u)
    (hTwo : deltaLaterI2DegreeTie410 a b u)
    (hOne : deltaLaterI1DegreeTie410 a b u)
    (hPrimitive : deltaLaterPrimitiveDegreeTie410 a b u) :
    a + 2 * b = 2 * u ∧ 7 * a = 8 * b ∧ 11 * a = 8 * u ∧
      0 < a ∧ 0 < b ∧ 0 < u := by
  simp only [deltaLaterI2DegreeTie410, deltaLaterI1DegreeTie410,
    deltaLaterPrimitiveDegreeTie410, deltaLaterFiveTie410] at hTwo hOne hPrimitive
  have hplane : a + 2 * b = 2 * u := by omega
  have hab : 7 * a = 8 * b := by omega
  have hau : 11 * a = 8 * u := by omega
  clear hTwo hOne hPrimitive
  omega

def deltaLaterInvariantOneTail410
    (zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(1536 * zeta) : k) • (A * B) + (2048 * theta : k) • B -
    (1024 * eta : k) • U

def deltaLaterInvariantOnePrincipal410
    (delta : k) (A B U : k[X]) : k[X] :=
  (-(320 * delta) : k) • (A ^ 2 * B) +
    (-(640 * delta) : k) • (B * U) +
    (960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
    (-(40 : k)) • U ^ 3

theorem discriminantInvariantOne410_zeroGamma_eq_principal_add_tail
    (delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 0 delta zeta eta theta A B U =
      deltaLaterInvariantOnePrincipal410 delta A B U +
        deltaLaterInvariantOneTail410 zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410,
    deltaLaterInvariantOnePrincipal410, deltaLaterInvariantOneTail410]
  module

def deltaLaterTerminalLoadPrimitive410
    (zeta theta : k) (A B U : k[X]) : k[X] :=
  (1280 * zeta : k) • A ^ 3 - (3072 * zeta : k) • B ^ 2 -
    (1536 * zeta : k) • (A * U) +
    (3072 * theta : k) • A ^ 2 - (2048 * theta : k) • U

def deltaLaterTerminalPrimitive410
    (delta zeta theta : k) (A B U : k[X]) : k[X] :=
  deltaTerminalPrimitive410 delta A B U +
    deltaLaterTerminalLoadPrimitive410 zeta theta A B U

def deltaLaterFiberPrimitive410
    (delta zeta theta q2 : k) (A B U : k[X]) : k[X] :=
  deltaLaterTerminalPrimitive410 delta zeta theta A B U - q2 • A

theorem lWallTerminal410_zeroGamma_eq_laterDerivative_sub
    (delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 delta zeta eta theta A B U =
      derivative (deltaLaterTerminalPrimitive410
        delta zeta theta A B U) -
        discriminantInvariantTwoNumerator410
          0 0 0 delta zeta eta theta A B U * derivative A := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410,
    deltaLaterTerminalPrimitive410,
    deltaTerminalPrimitive410, deltaLaterTerminalLoadPrimitive410,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [zero_mul, mul_zero, zero_smul, add_zero, sub_zero, neg_zero,
    map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem lWallTerminal410_zeroGamma_eq_laterFiberDerivative
    (delta zeta eta theta q2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q2) :
    lWallTerminalNumerator410 0 0 0 delta zeta eta theta A B U =
      derivative (deltaLaterFiberPrimitive410
        delta zeta theta q2 A B U) := by
  rw [lWallTerminal410_zeroGamma_eq_laterDerivative_sub, hTwo]
  simp only [deltaLaterFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

def deltaLaterI2FixedRest410
    (delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 - (640 * delta : k) • (A * U) +
    (1280 * delta : k) • B ^ 2 +
    deltaLaterI2Tail410 zeta eta theta A B U

def deltaLaterI1FixedRest410
    (delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(320 * delta) : k) • (A ^ 2 * B) +
    (-(640 * delta) : k) • (B * U) + (-(320 : k)) • B ^ 4 +
    deltaLaterInvariantOneTail410 zeta eta theta A B U

theorem discriminantInvariantTwo410_zeroGamma_fixed_decomposition
    (delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 0 delta zeta eta theta A B U =
      (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        deltaLaterI2FixedRest410 delta zeta eta theta A B U := by
  simp [discriminantInvariantTwoNumerator410,
    deltaLaterI2FixedRest410, deltaLaterI2Tail410]
  module

theorem discriminantInvariantOne410_zeroGamma_fixed_decomposition
    (delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 0 delta zeta eta theta A B U =
      (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
        deltaLaterI1FixedRest410 delta zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410,
    deltaLaterI1FixedRest410, deltaLaterInvariantOneTail410]
  module

theorem deltaLater_nonzero_coordinates_impossible
    (delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B U = C terminal) : False := by
  let a := A.natDegree
  let b := B.natDegree
  let u := U.natDegree
  have hDerivative : derivative
      (deltaLaterFiberPrimitive410 delta zeta theta q2 A B U) =
        C terminal := by
    rw [← lWallTerminal410_zeroGamma_eq_laterFiberDerivative
      delta zeta eta theta q2 A B U hTwo]
    exact hTerminal
  have hDegree : (deltaLaterFiberPrimitive410
      delta zeta theta q2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (deltaLaterFiberPrimitive410 delta zeta theta q2 A B U)
      terminal hterminal hDerivative
  have hpositive : 0 < a ∨ 0 < b ∨ 0 < u := by
    by_contra hnone
    push_neg at hnone
    have hle : (deltaLaterFiberPrimitive410
        delta zeta theta q2 A B U).natDegree ≤ 0 := by
      simp only [deltaLaterFiberPrimitive410, deltaLaterTerminalPrimitive410,
        deltaTerminalPrimitive410, deltaLaterTerminalLoadPrimitive410]
      compute_degree
      omega
    omega
  have hsmul {c : k} {P : k[X]} (hc : c ≠ 0) (hP : P ≠ 0) :
      c • P ≠ 0 := by
    intro hz
    exact hP ((smul_eq_zero.mp hz).resolve_left hc)
  have hc320d : (320 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc640d : (640 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc1280d : (1280 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc560d : (560 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc960d : (960 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  let M2 : ℕ := max (3 * a)
    (max (a + u) (max (2 * b) (max (a + 3 * b) (b + 2 * u))))
  have hM2pos : 0 < M2 := by dsimp only [M2]; omega
  have hTail2 : (deltaLaterI2Tail410 zeta eta theta A B U).natDegree < M2 := by
    dsimp only [M2]
    simp only [deltaLaterI2Tail410]
    compute_degree
    omega
  have hPrincipal2 :
      (320 * delta : k) • A ^ 3 + (-(640 * delta) : k) • (A * U) +
        (1280 * delta : k) • B ^ 2 + (-(1280 : k)) • (A * B ^ 3) +
          (480 : k) • (B * U ^ 2) =
        C q2 - deltaLaterI2Tail410 zeta eta theta A B U := by
    rw [discriminantInvariantTwo410_zeroGamma_eq_principal_add_tail] at hTwo
    simp only [deltaLaterI2PrincipalSum410] at hTwo
    linear_combination hTwo
  have hbelow2 :
      ((320 * delta : k) • A ^ 3 + (-(640 * delta) : k) • (A * U) +
        (1280 * delta : k) • B ^ 2 + (-(1280 : k)) • (A * B ^ 3) +
          (480 : k) • (B * U ^ 2)).natDegree < M2 := by
    rw [hPrincipal2]
    exact (natDegree_sub_le _ _).trans_lt
      (max_lt (by rw [natDegree_C]; exact hM2pos) hTail2)
  have hTie2 := deltaLater_fiveTerm_tie410
    ((320 * delta : k) • A ^ 3) ((-(640 * delta) : k) • (A * U))
    ((1280 * delta : k) • B ^ 2) ((-(1280 : k)) • (A * B ^ 3))
    ((480 : k) • (B * U ^ 2))
    (hsmul hc320d (pow_ne_zero 3 hA))
    (hsmul (neg_ne_zero.mpr hc640d) (mul_ne_zero hA hU))
    (hsmul hc1280d (pow_ne_zero 2 hB))
    (hsmul (by norm_num) (mul_ne_zero hA (pow_ne_zero 3 hB)))
    (hsmul (by norm_num) (mul_ne_zero hB (pow_ne_zero 2 hU)))
    (by
      simpa only [M2, natDegree_smul _ hc320d,
        natDegree_smul _ (neg_ne_zero.mpr hc640d),
        natDegree_smul _ hc1280d,
        natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (480 : k) ≠ 0), natDegree_pow,
        natDegree_mul hA hU, natDegree_mul hA (pow_ne_zero 3 hB),
        natDegree_mul hB (pow_ne_zero 2 hU), a, b, u] using hbelow2)
  let M1 : ℕ := max (2 * a + b)
    (max (b + u) (max (a + 2 * b + u) (max (4 * b) (3 * u))))
  have hM1pos : 0 < M1 := by dsimp only [M1]; omega
  have hTail1 : (deltaLaterInvariantOneTail410
      zeta eta theta A B U).natDegree < M1 := by
    dsimp only [M1]
    simp only [deltaLaterInvariantOneTail410]
    compute_degree
    omega
  have hPrincipal1 : deltaLaterInvariantOnePrincipal410 delta A B U =
      C q1 - deltaLaterInvariantOneTail410 zeta eta theta A B U := by
    rw [discriminantInvariantOne410_zeroGamma_eq_principal_add_tail] at hOne
    linear_combination hOne
  have hbelow1 : (deltaLaterInvariantOnePrincipal410
      delta A B U).natDegree < M1 := by
    rw [hPrincipal1]
    exact (natDegree_sub_le _ _).trans_lt
      (max_lt (by rw [natDegree_C]; exact hM1pos) hTail1)
  have hTie1 := deltaLater_fiveTerm_tie410
    ((-(320 * delta) : k) • (A ^ 2 * B))
    ((-(640 * delta) : k) • (B * U))
    ((960 : k) • (A * B ^ 2 * U)) ((-(320 : k)) • B ^ 4)
    ((-(40 : k)) • U ^ 3)
    (hsmul (neg_ne_zero.mpr hc320d) (mul_ne_zero (pow_ne_zero 2 hA) hB))
    (hsmul (neg_ne_zero.mpr hc640d) (mul_ne_zero hB hU))
    (hsmul (by norm_num)
      (mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) hU))
    (hsmul (by norm_num) (pow_ne_zero 4 hB))
    (hsmul (by norm_num) (pow_ne_zero 3 hU))
    (by
      simpa only [deltaLaterInvariantOnePrincipal410, M1,
        natDegree_smul _ (neg_ne_zero.mpr hc320d),
        natDegree_smul _ (neg_ne_zero.mpr hc640d),
        natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
        natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0), natDegree_pow,
        natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_mul hB hU,
        natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
        natDegree_mul hA (pow_ne_zero 2 hB), a, b, u] using hbelow1)
  let MP : ℕ := max (4 * a)
    (max (2 * a + u) (max (a + 2 * b) (max (3 * b + u) (2 * u))))
  have hMPpos : max 1 a < MP := by dsimp only [MP]; omega
  have hLoadP : (deltaLaterTerminalLoadPrimitive410
      zeta theta A B U).natDegree < MP := by
    dsimp only [MP]
    simp only [deltaLaterTerminalLoadPrimitive410]
    compute_degree
    omega
  have hPrincipalP :
      (560 * delta : k) • A ^ 4 +
        (-(960 * delta) : k) • (A ^ 2 * U) +
        (-(1280 * delta) : k) • (A * B ^ 2) +
        (1280 : k) • (B ^ 3 * U) + (320 * delta : k) • U ^ 2 =
      deltaLaterFiberPrimitive410 delta zeta theta q2 A B U + q2 • A -
        deltaLaterTerminalLoadPrimitive410 zeta theta A B U := by
    simp only [deltaLaterFiberPrimitive410, deltaLaterTerminalPrimitive410,
      deltaTerminalPrimitive410]
    module
  have hFiberA : (deltaLaterFiberPrimitive410 delta zeta theta q2 A B U +
      q2 • A).natDegree ≤ max 1 a := by
    compute_degree
    omega
  have hbelowP :
      ((560 * delta : k) • A ^ 4 +
        (-(960 * delta) : k) • (A ^ 2 * U) +
        (-(1280 * delta) : k) • (A * B ^ 2) +
        (1280 : k) • (B ^ 3 * U) + (320 * delta : k) • U ^ 2).natDegree <
          MP := by
    rw [hPrincipalP]
    exact (natDegree_sub_le _ _).trans_lt
      (max_lt (hFiberA.trans_lt hMPpos) hLoadP)
  have hTieP := deltaLater_fiveTerm_tie410
    ((560 * delta : k) • A ^ 4)
    ((-(960 * delta) : k) • (A ^ 2 * U))
    ((-(1280 * delta) : k) • (A * B ^ 2))
    ((1280 : k) • (B ^ 3 * U)) ((320 * delta : k) • U ^ 2)
    (hsmul hc560d (pow_ne_zero 4 hA))
    (hsmul (neg_ne_zero.mpr hc960d) (mul_ne_zero (pow_ne_zero 2 hA) hU))
    (hsmul (neg_ne_zero.mpr hc1280d) (mul_ne_zero hA (pow_ne_zero 2 hB)))
    (hsmul (by norm_num) (mul_ne_zero (pow_ne_zero 3 hB) hU))
    (hsmul hc320d (pow_ne_zero 2 hU))
    (by
      simpa only [MP, natDegree_smul _ hc560d,
        natDegree_smul _ (neg_ne_zero.mpr hc960d),
        natDegree_smul _ (neg_ne_zero.mpr hc1280d),
        natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
        natDegree_smul _ hc320d, natDegree_pow,
        natDegree_mul (pow_ne_zero 2 hA) hU,
        natDegree_mul hA (pow_ne_zero 2 hB),
        natDegree_mul (pow_ne_zero 3 hB) hU, a, b, u] using hbelowP)
  have hTie2D : deltaLaterI2DegreeTie410 a b u := by
    simpa only [deltaLaterI2DegreeTie410, M2,
    natDegree_smul _ hc320d,
    natDegree_smul _ (neg_ne_zero.mpr hc640d), natDegree_smul _ hc1280d,
    natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (480 : k) ≠ 0), natDegree_pow,
    natDegree_mul hA hU, natDegree_mul hA (pow_ne_zero 3 hB),
    natDegree_mul hB (pow_ne_zero 2 hU), a, b, u] using hTie2
  have hTie1D : deltaLaterI1DegreeTie410 a b u := by
    simpa only [deltaLaterI1DegreeTie410, M1,
    natDegree_smul _ (neg_ne_zero.mpr hc320d),
    natDegree_smul _ (neg_ne_zero.mpr hc640d),
    natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
    natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0), natDegree_pow,
    natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_mul hB hU,
    natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
    natDegree_mul hA (pow_ne_zero 2 hB), a, b, u] using hTie1
  have hTiePD : deltaLaterPrimitiveDegreeTie410 a b u := by
    simpa only [deltaLaterPrimitiveDegreeTie410, MP,
    natDegree_smul _ hc560d,
    natDegree_smul _ (neg_ne_zero.mpr hc960d),
    natDegree_smul _ (neg_ne_zero.mpr hc1280d),
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ hc320d, natDegree_pow,
    natDegree_mul (pow_ne_zero 2 hA) hU,
    natDegree_mul hA (pow_ne_zero 2 hB),
    natDegree_mul (pow_ne_zero 3 hB) hU, a, b, u] using hTieP
  have hdegrees := deltaLater_three_degree_ties_force_ray410
    a b u hpositive hTie2D hTie1D hTiePD
  rcases hdegrees with ⟨hplane, hab, hau, ha, hb, hu⟩
  have hRest2 : (deltaLaterI2FixedRest410
      delta zeta eta theta A B U).natDegree < a + 3 * b := by
    simp only [deltaLaterI2FixedRest410, deltaLaterI2Tail410]
    compute_degree
    omega
  have hRest1 : (deltaLaterI1FixedRest410
      delta zeta eta theta A B U).natDegree < 3 * u := by
    simp only [deltaLaterI1FixedRest410, deltaLaterInvariantOneTail410]
    compute_degree
    omega
  have hAB3deg : (A * B ^ 3).natDegree = a + 3 * b := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hBU2deg : (B * U ^ 2).natDegree = a + 3 * b := by
    rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * u := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * u := by rw [natDegree_pow]
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (a + 3 * b)) hTwo
  rw [discriminantInvariantTwo410_zeroGamma_fixed_decomposition,
    coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 3).coeff (a + 3 * b) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff (a + 3 * b) =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hRest2, add_zero,
    show (C q2 : k[X]).coeff (a + 3 * b) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff (3 * u)) hOne
  rw [discriminantInvariantOne410_zeroGamma_fixed_decomposition,
    coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff (3 * u) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow],
    show (U ^ 3).coeff (3 * u) = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hRest1, add_zero,
    show (C q1 : k[X]).coeff (3 * u) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hFaceTwo :
      -(8 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) +
        3 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (160 : k) ≠ 0) hBlc))
    linear_combination hTwoCoeff
  have hFaceOne :
      24 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
        U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (40 : k) ≠ 0) hUlc))
    linear_combination hOneCoeff
  have hzero : (64 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 3 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero hAlc (pow_ne_zero 2 hBlc))) hzero

theorem deltaLater_envelope_packet_impossible
    (delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B U = C terminal)
    (hpacket : DeltaLaterEnvelopeFanPacket410 A B U) : False :=
  deltaLater_nonzero_coordinates_impossible
    delta zeta eta theta q2 q1 terminal A B U hdelta hterminal
      hpacket.1 hpacket.2.1 hpacket.2.2.1 hTwo hOne hTerminal

def GammaOnlyEnvelopeNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    FullCorePrincipalWallDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_deltaLaterDeletedNoncubic_residual
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
    l = 0 ∧ GammaOnlyEnvelopeNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaClosedDeltaEnvelopeFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · exact hgamma
  · have hTwo0 : firstIntegralTwoPolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hTwo
    have hOne0 : firstIntegralOnePolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hOne
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
          A B C0) B C0 = C terminal := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hLower
    have hTwoD : discriminantInvariantTwoNumerator410
        0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
          C (2048 * k2) := by
      rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo0,
        Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
    have hOneD : discriminantInvariantOneNumerator410
        0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
          C (2048 * k1) := by
      rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne0,
        Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
    have hTerminalD : lWallTerminalNumerator410
        0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
          C (8192 * terminal) := by
      rw [← lowerRow410_discriminantTerminalNumerator, hLower0,
        Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
    exact (deltaLater_envelope_packet_impossible
      delta zeta eta theta (2048 * k2) (2048 * k1) (8192 * terminal)
        A B (A ^ 2 - (4 : k) • C0) hdelta.2.2.1
        (mul_ne_zero (by norm_num) hterminal) hTwoD hOneD hTerminalD
        hdelta.2.2.2.2).elim

theorem integrated410_deltaLaterDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaOnlyEnvelopeNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_deltaLaterDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_deltaLaterDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaOnlyEnvelopeNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_deltaLaterDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end DeltaLaterElimination410

end Max11DegreeRoutes
