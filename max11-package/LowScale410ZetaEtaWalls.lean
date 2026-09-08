import LowScale410ThetaWallElimination

/-!
# The pure zeta and eta walls for `(4,10)`, scale zero

The `eta` wall factors through the first invariant and has primitive
`1280 B^3 U`.  The `zeta` wall has a four-term primitive; its three Newton
constraints force the unique nondegenerate degree ray `(8,5,9)`, where the
two invariant faces are incompatible.  Closing these two pure walls in the
correct load order, then invoking the already closed pure `theta` wall,
isolates the remaining genuinely mixed-load residual.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section ZetaEtaWalls410

variable {k : Type*} [Field k] [CharZero k]

/-! ## Pure eta wall -/

def etaCoreTwo410 (eta : k) (A B U : k[X]) : k[X] :=
  -(1280 : k) • (A * B ^ 2) + (480 : k) • U ^ 2 +
    (4096 * eta : k) • (1 : k[X])

def etaTerminalPrimitive410 (B U : k[X]) : k[X] :=
  (1280 : k) • (B ^ 3 * U)

def etaFiberPrimitive410 (k2 : k) (A B U : k[X]) : k[X] :=
  etaTerminalPrimitive410 B U - k2 • A

theorem discriminantInvariantTwoNumerator410_eta_factor
    (eta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 0 0 0 0 0 eta 0 A B U =
      B * etaCoreTwo410 eta A B U := by
  simp only [discriminantInvariantTwoNumerator410, etaCoreTwo410,
    zero_mul, mul_zero, zero_smul, add_zero, sub_zero, mul_add, mul_smul_comm,
    mul_one]
  ring_nf
  module

theorem lWallTerminalNumerator410_eta_eq_derivative_sub
    (eta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 0 0 eta 0 A B U =
      derivative (etaTerminalPrimitive410 B U) -
        discriminantInvariantTwoNumerator410 0 0 0 0 0 eta 0 A B U *
          derivative A := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410, etaTerminalPrimitive410,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul, zero_mul, mul_zero, zero_smul, add_zero,
    sub_zero, neg_zero, Polynomial.C_0]
  push_cast
  simp only [Polynomial.C_ofNat, Polynomial.C_neg,
    Polynomial.derivative_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
  ring_nf

theorem lWallTerminalNumerator410_eta_eq_fiberDerivative
    (eta k2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta 0 A B U = C k2) :
    lWallTerminalNumerator410 0 0 0 0 0 eta 0 A B U =
      derivative (etaFiberPrimitive410 k2 A B U) := by
  rw [lWallTerminalNumerator410_eta_eq_derivative_sub, hTwo]
  simp only [etaFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

theorem etaCore410_reduced_secondInvariant
    (eta : k) (A B U : k[X])
    (hcore : etaCoreTwo410 eta A B U = 0) :
    discriminantInvariantOneNumerator410 0 0 0 0 0 eta 0 A B U =
      (320 : k) • (U ^ 3 - B ^ 4) + (2048 * eta : k) • U := by
  simp only [etaCoreTwo410] at hcore
  simp only [discriminantInvariantOneNumerator410, zero_mul, mul_zero,
    zero_smul, add_zero, sub_zero]
  have hscaled : (960 : k) • (A * B ^ 2 * U) =
      (360 : k) • U ^ 3 + (3072 * eta : k) • U := by
    calc
      (960 : k) • (A * B ^ 2 * U) =
          (3 / 4 : k) • (((1280 : k) • (A * B ^ 2)) * U) := by
            simp only [smul_mul_assoc, smul_smul]
            module
      _ = (3 / 4 : k) •
          (((480 : k) • U ^ 2 + (4096 * eta : k) • (1 : k[X])) * U) := by
            have hab : (1280 : k) • (A * B ^ 2) =
                (480 : k) • U ^ 2 + (4096 * eta : k) • (1 : k[X]) := by
              have hcore' : -((1280 : k) • (A * B ^ 2)) +
                  (480 : k) • U ^ 2 + (4096 * eta : k) • (1 : k[X]) = 0 := by
                simpa only [neg_smul] using hcore
              calc
                (1280 : k) • (A * B ^ 2) =
                    (1280 : k) • (A * B ^ 2) + 0 := by abel
                _ = (1280 : k) • (A * B ^ 2) +
                    (-((1280 : k) • (A * B ^ 2)) +
                      (480 : k) • U ^ 2 +
                        (4096 * eta : k) • (1 : k[X])) := by rw [hcore']
                _ = (480 : k) • U ^ 2 +
                    (4096 * eta : k) • (1 : k[X]) := by abel
            rw [hab]
      _ = (360 : k) • U ^ 3 + (3072 * eta : k) • U := by
            simp only [add_mul, smul_add, smul_mul_assoc, smul_smul, one_mul]
            rw [show U ^ 2 * U = U ^ 3 by ring]
            module
  rw [hscaled]
  module

/-- The pure `eta` constant-fiber trajectory is impossible. -/
theorem etaOnly410_discriminant_trajectory_impossible
    (eta k2 k1 terminal : k) (A B U : k[X])
    (heta : eta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 eta 0 A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 0 eta 0 A B U = C terminal) : False := by
  have hDerivative : derivative (etaFiberPrimitive410 k2 A B U) = C terminal := by
    rw [← lWallTerminalNumerator410_eta_eq_fiberDerivative eta k2 A B U hTwo]
    exact hTerminal
  have hDegree : (etaFiberPrimitive410 k2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (etaFiberPrimitive410 k2 A B U) terminal hterminal hDerivative
  have hProduct : B * etaCoreTwo410 eta A B U = C k2 := by
    rw [← discriminantInvariantTwoNumerator410_eta_factor]
    exact hTwo
  by_cases hk2 : k2 = 0
  · subst k2
    simp only [C_0] at hProduct
    have hProductZero : B * etaCoreTwo410 eta A B U = 0 := hProduct
    by_cases hBzero : B = 0
    · subst B
      simp [etaFiberPrimitive410, etaTerminalPrimitive410] at hDegree
    · have hcore : etaCoreTwo410 eta A B U = 0 :=
        (mul_eq_zero.mp hProductZero).resolve_left hBzero
      simp only [etaFiberPrimitive410, zero_smul, sub_zero,
        etaTerminalPrimitive410] at hDegree
      have hUne : U ≠ 0 := by
        intro hz
        subst U
        simp at hDegree
      have hdeg : 3 * B.natDegree + U.natDegree = 1 := by
        rw [natDegree_smul _ (by norm_num),
          natDegree_mul (pow_ne_zero 3 hBzero) hUne, natDegree_pow] at hDegree
        omega
      have hBdegree : B.natDegree = 0 := by omega
      have hUdegree : U.natDegree = 1 := by omega
      have hReduced := etaCore410_reduced_secondInvariant eta A B U hcore
      have hMainDegree : ((320 : k) • (U ^ 3 - B ^ 4)).natDegree = 3 := by
        have hU3 : (U ^ 3).natDegree = 3 := by
          rw [natDegree_pow, hUdegree]
        have hB4 : (B ^ 4).natDegree = 0 := by
          rw [natDegree_pow, hBdegree]
        rw [natDegree_smul _ (by norm_num), natDegree_sub_eq_left_of_natDegree_lt]
        · exact hU3
        · omega
      have hLowerDegree : ((2048 * eta : k) • U).natDegree < 3 := by
        compute_degree
        omega
      have hReducedDegree :
          ((320 : k) • (U ^ 3 - B ^ 4) + (2048 * eta : k) • U).natDegree =
            3 := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        · exact hMainDegree
        · rw [hMainDegree]
          exact hLowerDegree
      have hd := congrArg Polynomial.natDegree hOne
      rw [hReduced, hReducedDegree, natDegree_C] at hd
      omega
  · have hBne : B ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hProduct
      exact hk2 (C_eq_zero.mp hProduct.symm)
    have hCoreNe : etaCoreTwo410 eta A B U ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hProduct
      exact hk2 (C_eq_zero.mp hProduct.symm)
    have hProductDegree := congrArg Polynomial.natDegree hProduct
    rw [natDegree_mul hBne hCoreNe, natDegree_C] at hProductDegree
    have hBdegree : B.natDegree = 0 := by omega
    have hCoreDegree : (etaCoreTwo410 eta A B U).natDegree = 0 := by omega
    obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hBdegree
    have hbne : b ≠ 0 := by
      intro hb0
      apply hBne
      rw [← hb, hb0, C_0]
    obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hCoreDegree
    have hcoef : (1280 * b ^ 2 : k) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hbne)
    have hScaledA : (1280 * b ^ 2 : k) • A =
        (480 : k) • U ^ 2 + (4096 * eta : k) • (1 : k[X]) - C c := by
      have hAB : A * B ^ 2 = (b ^ 2 : k) • A := by
        rw [← hb, ← Polynomial.C_pow, Polynomial.smul_eq_C_mul]
        ring
      have hneg : (-(1280 : k)) • (A * B ^ 2) =
          -((1280 * b ^ 2 : k) • A) := by
        rw [hAB, smul_smul, ← neg_smul]
        congr 1
        ring
      have hc' : C c = -((1280 * b ^ 2 : k) • A) +
          (480 : k) • U ^ 2 + (4096 * eta : k) • (1 : k[X]) := by
        simpa only [etaCoreTwo410, hneg] using hc
      rw [hc']
      abel
    by_cases hUdegree : U.natDegree = 0
    · have hAle : A.natDegree = 0 := by
        have hd := congrArg Polynomial.natDegree hScaledA
        have hrhs : ((480 : k) • U ^ 2 +
            (4096 * eta : k) • (1 : k[X]) - C c).natDegree ≤ 0 := by
          compute_degree
          omega
        rw [natDegree_smul A hcoef] at hd
        omega
      have hle : (etaFiberPrimitive410 k2 A B U).natDegree ≤ 0 := by
        simp only [etaFiberPrimitive410, etaTerminalPrimitive410]
        compute_degree
        omega
      omega
    · have hUpos : 0 < U.natDegree := by omega
      have hUne : U ≠ 0 := by
        intro hz
        subst U
        exact hUdegree natDegree_zero
      have hRestDegree :
          ((4096 * eta : k) • (1 : k[X]) - C c).natDegree <
            2 * U.natDegree := by
        compute_degree
        omega
      have hLeadDegree : ((480 : k) • U ^ 2).natDegree =
          2 * U.natDegree := by
        rw [natDegree_smul _ (by norm_num), natDegree_pow]
      have hRhsDegree : ((480 : k) • U ^ 2 +
          (4096 * eta : k) • (1 : k[X]) - C c).natDegree =
            2 * U.natDegree := by
        rw [show (480 : k) • U ^ 2 + (4096 * eta : k) • (1 : k[X]) - C c =
            (480 : k) • U ^ 2 +
              ((4096 * eta : k) • (1 : k[X]) - C c) by abel,
          natDegree_add_eq_left_of_natDegree_lt]
        · exact hLeadDegree
        · rw [hLeadDegree]
          exact hRestDegree
      have hAdegree : A.natDegree = 2 * U.natDegree := by
        have hd := congrArg Polynomial.natDegree hScaledA
        rw [natDegree_smul A hcoef, hRhsDegree] at hd
        exact hd
      have hFirstDegree : ((1280 : k) • (B ^ 3 * U)).natDegree =
          U.natDegree := by
        rw [natDegree_smul _ (by norm_num),
          natDegree_mul (pow_ne_zero 3 hBne) hUne, natDegree_pow, hBdegree]
        omega
      have hSecondDegree : (k2 • A).natDegree = 2 * U.natDegree := by
        rw [natDegree_smul A hk2, hAdegree]
      have hFiberDegree : (etaFiberPrimitive410 k2 A B U).natDegree =
          2 * U.natDegree := by
        simp only [etaFiberPrimitive410, etaTerminalPrimitive410]
        rw [natDegree_sub_eq_right_of_natDegree_lt, hSecondDegree]
        rw [hFirstDegree]
        omega
      omega

/-! ## Pure zeta wall -/

def zetaTerminalPrimitive410 (zeta : k) (A B U : k[X]) : k[X] :=
  (1280 * zeta : k) • A ^ 3 - (1536 * zeta : k) • (A * U) +
    (1280 : k) • (B ^ 3 * U) - (3072 * zeta : k) • B ^ 2

def zetaFiberPrimitive410
    (zeta k2 : k) (A B U : k[X]) : k[X] :=
  zetaTerminalPrimitive410 zeta A B U - k2 • A

theorem lWallTerminalNumerator410_zeta_eq_derivative_sub
    (zeta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 0 zeta 0 0 A B U =
      derivative (zetaTerminalPrimitive410 zeta A B U) -
        discriminantInvariantTwoNumerator410 0 0 0 0 zeta 0 0 A B U *
          derivative A := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410, zetaTerminalPrimitive410,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul, zero_mul, mul_zero, zero_smul, add_zero,
    sub_zero, neg_zero, Polynomial.C_0]
  push_cast
  simp only [Polynomial.C_ofNat, Polynomial.C_neg,
    Polynomial.derivative_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
  ring_nf
  have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
    simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
  have h2 : (2 : k[X]) = (2 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 2).symm
  have h3 : (3 : k[X]) = (3 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 3).symm
  simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, _root_.smul_pow, one_pow]
  rw [h2, h3]
  simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

theorem lWallTerminalNumerator410_zeta_eq_fiberDerivative
    (zeta k2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta 0 0 A B U = C k2) :
    lWallTerminalNumerator410 0 0 0 0 zeta 0 0 A B U =
      derivative (zetaFiberPrimitive410 zeta k2 A B U) := by
  rw [lWallTerminalNumerator410_zeta_eq_derivative_sub, hTwo]
  simp only [zetaFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

private def fourDegreeTieZeta410 (d1 d2 d3 d4 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d2 = m ∧ d3 = m) ∨
  (d2 = m ∧ d4 = m) ∨ (d3 = m ∧ d4 = m)

private theorem fourTerm_degree_tie_zeta410
    (P1 P2 P3 P4 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0) (hP4 : P4 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4).natDegree <
      max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))) :
    fourDegreeTieZeta410 P1.natDegree P2.natDegree P3.natDegree P4.natDegree
      (max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))) := by
  let m := max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have h4le : P4.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m ∨ P4.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : (P1 + P2 + P3 + P4).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ fourDegreeTieZeta410 P1.natDegree P2.natDegree P3.natDegree
    P4.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieZeta410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree]] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hcoeff)

private theorem twoTerm_degree_eq_zeta410 (P Q : k[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

private def zetaLowerTwo410 (zeta : k) (A U : k[X]) : k[X] :=
  (768 * zeta : k) • A ^ 2 - (1536 * zeta : k) • U

private def zetaLowerOne410 (zeta : k) (A B : k[X]) : k[X] :=
  -(320 : k) • B ^ 4 - (1536 * zeta : k) • (A * B)

private theorem zetaOnly410_nonzero_polynomials_impossible
    (zeta k2 k1 terminal : k) (A B U : k[X]) (a b u : ℕ)
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta 0 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta 0 0 A B U = C k1)
    (hDegree : (zetaFiberPrimitive410 zeta k2 A B U).natDegree = 1) : False := by
  have hpositive : 0 < a ∨ 0 < b ∨ 0 < u := by
    by_contra hnone
    push_neg at hnone
    have hle : (zetaFiberPrimitive410 zeta k2 A B U).natDegree ≤ 0 := by
      simp only [zetaFiberPrimitive410, zetaTerminalPrimitive410]
      compute_degree
      omega
    omega
  have hsmul {c : k} {P : k[X]} (hc : c ≠ 0) (hP : P ≠ 0) : c • P ≠ 0 := by
    intro hzero
    exact hP ((smul_eq_zero.mp hzero).resolve_left hc)
  have hc768 : (768 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hc1536 : (1536 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hc1280 : (1280 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hc3072 : (3072 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hsumTwo : (-(1280 : k)) • (A * B ^ 3) +
      (480 : k) • (B * U ^ 2) + (768 * zeta : k) • A ^ 2 +
        (-(1536 * zeta) : k) • U = C k2 := by
    have hs := hTwo
    simp only [discriminantInvariantTwoNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    rw [neg_smul, neg_smul]
    calc
      -((1280 : k) • (A * B ^ 3)) + (480 : k) • (B * U ^ 2) +
          (768 * zeta : k) • A ^ 2 - (1536 * zeta : k) • U =
        (768 * zeta : k) • A ^ 2 - (1280 : k) • (A * B ^ 3) +
          (480 : k) • (B * U ^ 2) - (1536 * zeta : k) • U := by abel
      _ = C k2 := hs
  have hmTwoPos : 0 < max (a + 3 * b)
      (max (b + 2 * u) (max (2 * a) u)) := by omega
  have hbelowTwo :
      ((-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        (768 * zeta : k) • A ^ 2 + (-(1536 * zeta) : k) • U).natDegree <
          max (a + 3 * b) (max (b + 2 * u) (max (2 * a) u)) := by
    rw [hsumTwo, natDegree_C]
    exact hmTwoPos
  have hTieTwo := fourTerm_degree_tie_zeta410
    ((-(1280 : k)) • (A * B ^ 3)) ((480 : k) • (B * U ^ 2))
    ((768 * zeta : k) • A ^ 2) ((-(1536 * zeta) : k) • U)
    (hsmul (by norm_num) (mul_ne_zero hAne (pow_ne_zero 3 hBne)))
    (hsmul (by norm_num) (mul_ne_zero hBne (pow_ne_zero 2 hUne)))
    (hsmul hc768 (pow_ne_zero 2 hAne))
    (hsmul (neg_ne_zero.mpr hc1536) hUne)
    (by
      simpa only [natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
        natDegree_smul _ hc768, natDegree_smul _ (neg_ne_zero.mpr hc1536),
        natDegree_mul hAne (pow_ne_zero 3 hBne),
        natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
        using hbelowTwo)
  have hsumOne : (960 : k) • (A * B ^ 2 * U) +
      (-(320 : k)) • B ^ 4 + (-(40 : k)) • U ^ 3 +
        (-(1536 * zeta) : k) • (A * B) = C k1 := by
    have hs := hOne
    simp only [discriminantInvariantOneNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    calc
      (960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
          (-(40 : k)) • U ^ 3 + (-(1536 * zeta) : k) • (A * B) =
        (960 : k) • (A * B ^ 2 * U) - (1536 * zeta : k) • (A * B) -
          (320 : k) • B ^ 4 - (40 : k) • U ^ 3 := by module
      _ = C k1 := hs
  have hmOnePos : 0 < max (a + 2 * b + u)
      (max (4 * b) (max (3 * u) (a + b))) := by omega
  have hbelowOne :
      ((960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
        (-(40 : k)) • U ^ 3 + (-(1536 * zeta) : k) • (A * B)).natDegree <
          max (a + 2 * b + u) (max (4 * b) (max (3 * u) (a + b))) := by
    rw [hsumOne, natDegree_C]
    exact hmOnePos
  have hTieOne := fourTerm_degree_tie_zeta410
    ((960 : k) • (A * B ^ 2 * U)) ((-(320 : k)) • B ^ 4)
    ((-(40 : k)) • U ^ 3) ((-(1536 * zeta) : k) • (A * B))
    (hsmul (by norm_num)
      (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne))
    (hsmul (by norm_num) (pow_ne_zero 4 hBne))
    (hsmul (by norm_num) (pow_ne_zero 3 hUne))
    (hsmul (neg_ne_zero.mpr hc1536) (mul_ne_zero hAne hBne))
    (by
      simpa only [natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
        natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0),
        natDegree_smul _ (neg_ne_zero.mpr hc1536),
        natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
        natDegree_mul hAne (pow_ne_zero 2 hBne),
        natDegree_mul hAne hBne, natDegree_pow, hA, hB, hU]
        using hbelowOne)
  simp only [fourDegreeTieZeta410,
    natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
    natDegree_smul _ hc768, natDegree_smul _ (neg_ne_zero.mpr hc1536),
    natDegree_mul hAne (pow_ne_zero 3 hBne),
    natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
    at hTieTwo
  simp only [fourDegreeTieZeta410,
    natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
    natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0),
    natDegree_smul _ (neg_ne_zero.mpr hc1536),
    natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
    natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_mul hAne hBne,
    natDegree_pow, hA, hB, hU] at hTieOne
  have hPrimitiveForm : zetaTerminalPrimitive410 zeta A B U =
      zetaFiberPrimitive410 zeta k2 A B U + k2 • A := by
    simp only [zetaFiberPrimitive410]
    abel
  have hPrimitiveLe : (zetaTerminalPrimitive410 zeta A B U).natDegree ≤
      max 1 a := by
    rw [hPrimitiveForm]
    compute_degree
    omega
  have hmPrimitivePos : max 1 a < max (3 * a)
      (max (a + u) (max (3 * b + u) (2 * b))) := by omega
  have hbelowPrimitive :
      ((1280 * zeta : k) • A ^ 3 + (-(1536 * zeta) : k) • (A * U) +
        (1280 : k) • (B ^ 3 * U) + (-(3072 * zeta) : k) • B ^ 2).natDegree <
          max (3 * a) (max (a + u) (max (3 * b + u) (2 * b))) := by
    have hform :
        (1280 * zeta : k) • A ^ 3 + (-(1536 * zeta) : k) • (A * U) +
            (1280 : k) • (B ^ 3 * U) + (-(3072 * zeta) : k) • B ^ 2 =
          zetaTerminalPrimitive410 zeta A B U := by
      simp only [zetaTerminalPrimitive410, sub_eq_add_neg, neg_smul]
    rw [hform]
    exact hPrimitiveLe.trans_lt hmPrimitivePos
  have hTiePrimitive := fourTerm_degree_tie_zeta410
    ((1280 * zeta : k) • A ^ 3) ((-(1536 * zeta) : k) • (A * U))
    ((1280 : k) • (B ^ 3 * U)) ((-(3072 * zeta) : k) • B ^ 2)
    (hsmul hc1280 (pow_ne_zero 3 hAne))
    (hsmul (neg_ne_zero.mpr hc1536) (mul_ne_zero hAne hUne))
    (hsmul (by norm_num) (mul_ne_zero (pow_ne_zero 3 hBne) hUne))
    (hsmul (neg_ne_zero.mpr hc3072) (pow_ne_zero 2 hBne))
    (by
      simpa only [natDegree_smul _ hc1280,
        natDegree_smul _ (neg_ne_zero.mpr hc1536),
        natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
        natDegree_smul _ (neg_ne_zero.mpr hc3072),
        natDegree_mul hAne hUne, natDegree_mul (pow_ne_zero 3 hBne) hUne,
        natDegree_pow, hA, hB, hU] using hbelowPrimitive)
  simp only [fourDegreeTieZeta410, natDegree_smul _ hc1280,
    natDegree_smul _ (neg_ne_zero.mpr hc1536),
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ (neg_ne_zero.mpr hc3072),
    natDegree_mul hAne hUne, natDegree_mul (pow_ne_zero 3 hBne) hUne,
    natDegree_pow, hA, hB, hU] at hTiePrimitive
  have hplane : a + 2 * b = 2 * u := by omega
  have hab : 5 * a = 8 * b := by omega
  have hau : 9 * a = 8 * u := by omega
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hu : 0 < u := by omega
  have hLowerTwo : (zetaLowerTwo410 zeta A U).natDegree < a + 3 * b := by
    simp only [zetaLowerTwo410]
    compute_degree
    omega
  have hLowerOne : (zetaLowerOne410 zeta A B).natDegree < 3 * u := by
    simp only [zetaLowerOne410]
    compute_degree
    omega
  have hTwoFace : discriminantInvariantTwoNumerator410 0 0 0 0 zeta 0 0
      A B U = (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        zetaLowerTwo410 zeta A U := by
    simp only [discriminantInvariantTwoNumerator410, zetaLowerTwo410,
      zero_mul, mul_zero, zero_smul, add_zero, sub_zero, sub_eq_add_neg,
      neg_smul]
    module
  have hOneFace : discriminantInvariantOneNumerator410 0 0 0 0 zeta 0 0
      A B U = (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
        zetaLowerOne410 zeta A B := by
    simp only [discriminantInvariantOneNumerator410, zetaLowerOne410,
      zero_mul, mul_zero, zero_smul, add_zero, sub_zero, sub_eq_add_neg,
      neg_smul]
    module
  have hAB3deg : (A * B ^ 3).natDegree = a + 3 * b := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
  have hBU2deg : (B * U ^ 2).natDegree = a + 3 * b := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * u := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * u := by rw [natDegree_pow, hU]
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (a + 3 * b)) hTwo
  rw [hTwoFace, coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 3).coeff (a + 3 * b) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff (a + 3 * b) =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hLowerTwo, add_zero,
    show (C k2 : k[X]).coeff (a + 3 * b) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff (3 * u)) hOne
  rw [hOneFace, coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff (3 * u) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow],
    show (U ^ 3).coeff (3 * u) = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hLowerOne, add_zero,
    show (C k1 : k[X]).coeff (3 * u) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  have hFaceTwo : -(1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) +
      480 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hBle)
    linear_combination hTwoCoeff
  have hFaceOne : 960 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
      40 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hUle)
    linear_combination hOneCoeff
  have hzero : (10240 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 12 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero hAle (pow_ne_zero 2 hBle))) hzero

private theorem zetaFiber_degree_one_impossible_of_degrees_zero
    (zeta k2 : k) (A B U : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hU : U.natDegree = 0)
    (hDegree : (zetaFiberPrimitive410 zeta k2 A B U).natDegree = 1) : False := by
  have hle : (zetaFiberPrimitive410 zeta k2 A B U).natDegree ≤ 0 := by
    simp only [zetaFiberPrimitive410, zetaTerminalPrimitive410]
    compute_degree
    omega
  omega

private theorem zetaOnly410_zeroA_impossible
    (zeta k2 k1 : k) (A B U : k[X]) (hzeta : zeta ≠ 0) (hAzero : A = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta 0 0 A B U = C k2)
    (hDegree : (zetaFiberPrimitive410 zeta k2 A B U).natDegree = 1) : False := by
  subst A
  by_cases hBzero : B = 0
  · subst B
    have hUeq : (-(1536 * zeta) : k) • U = C k2 := by
      simpa [discriminantInvariantTwoNumerator410] using hTwo
    have hd := congrArg Polynomial.natDegree hUeq
    rw [natDegree_smul _ (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hzeta)),
      natDegree_C] at hd
    exact zetaFiber_degree_one_impossible_of_degrees_zero
      zeta k2 0 0 U (by simp) (by simp) (by omega) hDegree
  · by_cases hUzero : U = 0
    · subst U
      have hc : (3072 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
      have hd := hDegree
      have hform : zetaFiberPrimitive410 zeta k2 0 B 0 =
          -((3072 * zeta : k) • B ^ 2) := by
        simp [zetaFiberPrimitive410, zetaTerminalPrimitive410]
      rw [hform] at hd
      rw [natDegree_neg, natDegree_smul _ hc, natDegree_pow] at hd
      omega
    · have hsum : (480 : k) • (B * U ^ 2) +
          (-(1536 * zeta) : k) • U = C k2 := by
        have hs := hTwo
        simp [discriminantInvariantTwoNumerator410] at hs
        calc
          (480 : k) • (B * U ^ 2) + (-(1536 * zeta) : k) • U =
              (480 : k) • (B * U ^ 2) - (1536 * zeta : k) • U := by module
          _ = C k2 := hs
      have hpositive : 0 < B.natDegree ∨ 0 < U.natDegree := by
        by_contra hnone
        push_neg at hnone
        have hle : (zetaFiberPrimitive410 zeta k2 0 B U).natDegree ≤ 0 := by
          simp only [zetaFiberPrimitive410, zetaTerminalPrimitive410]
          compute_degree
          omega
        omega
      have hmpos : 0 < max (B.natDegree + 2 * U.natDegree) U.natDegree := by
        omega
      have hbelow : ((480 : k) • (B * U ^ 2) +
          (-(1536 * zeta) : k) • U).natDegree <
            max (B.natDegree + 2 * U.natDegree) U.natDegree := by
        rw [hsum, natDegree_C]
        exact hmpos
      have htie := twoTerm_degree_eq_zeta410
        ((480 : k) • (B * U ^ 2)) ((-(1536 * zeta) : k) • U)
        (by
          intro hz
          exact (mul_ne_zero hBzero (pow_ne_zero 2 hUzero))
            ((smul_eq_zero.mp hz).resolve_left (by norm_num)))
        (by
          intro hz
          exact hUzero ((smul_eq_zero.mp hz).resolve_left
            (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hzeta))) )
        (by
          simpa only [natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
            natDegree_smul _ (neg_ne_zero.mpr
              (mul_ne_zero (by norm_num : (1536 : k) ≠ 0) hzeta)),
            natDegree_mul hBzero (pow_ne_zero 2 hUzero), natDegree_pow]
            using hbelow)
      have heq : B.natDegree + 2 * U.natDegree = U.natDegree := by
        simpa only [natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
          natDegree_smul _ (neg_ne_zero.mpr
            (mul_ne_zero (by norm_num : (1536 : k) ≠ 0) hzeta)),
          natDegree_mul hBzero (pow_ne_zero 2 hUzero), natDegree_pow] using htie
      omega

private theorem zetaOnly410_zeroB_impossible
    (zeta k2 k1 : k) (A B U : k[X]) (hzeta : zeta ≠ 0) (hBzero : B = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta 0 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta 0 0 A B U = C k1)
    (hDegree : (zetaFiberPrimitive410 zeta k2 A B U).natDegree = 1) : False := by
  subst B
  have hUeq : (-(40 : k)) • U ^ 3 = C k1 := by
    simpa [discriminantInvariantOneNumerator410] using hOne
  have hdU := congrArg Polynomial.natDegree hUeq
  rw [natDegree_smul _ (by norm_num), natDegree_pow, natDegree_C] at hdU
  have hUdegree : U.natDegree = 0 := by omega
  by_cases hAdegree : A.natDegree = 0
  · exact zetaFiber_degree_one_impossible_of_degrees_zero
      zeta k2 A 0 U hAdegree (by simp) hUdegree hDegree
  · have hAne : A ≠ 0 := by
      intro hz
      subst A
      exact hAdegree natDegree_zero
    let R : k[X] := (-(1536 * zeta) : k) • U
    have hTwoForm : (768 * zeta : k) • A ^ 2 + R = C k2 := by
      have hs := hTwo
      simp [discriminantInvariantTwoNumerator410] at hs
      calc
        (768 * zeta : k) • A ^ 2 + R =
            (768 * zeta : k) • A ^ 2 - (1536 * zeta : k) • U := by
              dsimp only [R]
              module
        _ = C k2 := hs
    have hRdegree : R.natDegree < 2 * A.natDegree := by
      dsimp only [R]
      compute_degree
      omega
    exact smul_add_lower_ne_C410 (768 * zeta) k2 (A ^ 2) R
      (2 * A.natDegree) (mul_ne_zero (by norm_num) hzeta)
      (pow_ne_zero 2 hAne) (by omega) (by rw [natDegree_pow])
      hRdegree hTwoForm

private theorem zetaOnly410_zeroU_impossible
    (zeta k2 : k) (A B U : k[X]) (hzeta : zeta ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUzero : U = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta 0 0 A B U = C k2)
    (hDegree : (zetaFiberPrimitive410 zeta k2 A B U).natDegree = 1) : False := by
  subst U
  by_cases hAzero : A = 0
  · exact hAne hAzero
  · by_cases hBzero : B = 0
    · exact hBne hBzero
    · by_cases hconst : A.natDegree = 0 ∧ B.natDegree = 0
      · exact zetaFiber_degree_one_impossible_of_degrees_zero
          zeta k2 A B 0 hconst.1 hconst.2 (by simp) hDegree
      · have hpositive : 0 < A.natDegree ∨ 0 < B.natDegree := by omega
        have hc768 : (768 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
        have hsum : (-(1280 : k)) • (A * B ^ 3) +
            (768 * zeta : k) • A ^ 2 = C k2 := by
          have hs := hTwo
          simp [discriminantInvariantTwoNumerator410] at hs
          calc
            (-(1280 : k)) • (A * B ^ 3) + (768 * zeta : k) • A ^ 2 =
                -((1280 : k) • (A * B ^ 3)) +
                  (768 * zeta : k) • A ^ 2 := by rw [neg_smul]
            _ = (768 * zeta : k) • A ^ 2 -
                (1280 : k) • (A * B ^ 3) := by abel
            _ = C k2 := hs
        have hmpos : 0 < max (A.natDegree + 3 * B.natDegree)
            (2 * A.natDegree) := by omega
        have hbelow : ((-(1280 : k)) • (A * B ^ 3) +
            (768 * zeta : k) • A ^ 2).natDegree <
              max (A.natDegree + 3 * B.natDegree) (2 * A.natDegree) := by
          rw [hsum, natDegree_C]
          exact hmpos
        have htie := twoTerm_degree_eq_zeta410
          ((-(1280 : k)) • (A * B ^ 3)) ((768 * zeta : k) • A ^ 2)
          (by
            intro hz
            exact (mul_ne_zero hAzero (pow_ne_zero 3 hBzero))
              ((smul_eq_zero.mp hz).resolve_left (by norm_num)))
          (by
            intro hz
            exact (pow_ne_zero 2 hAzero)
              ((smul_eq_zero.mp hz).resolve_left hc768))
          (by
            simpa only [natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
              natDegree_smul _ hc768,
              natDegree_mul hAzero (pow_ne_zero 3 hBzero), natDegree_pow]
              using hbelow)
        have hplane : A.natDegree = 3 * B.natDegree := by
          have heq : A.natDegree + 3 * B.natDegree = 2 * A.natDegree := by
            simpa only [natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
              natDegree_smul _ hc768,
              natDegree_mul hAzero (pow_ne_zero 3 hBzero), natDegree_pow]
              using htie
          omega
        have hbpos : 0 < B.natDegree := by omega
        have haPos : 0 < A.natDegree := by omega
        have hc1280 : (1280 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
        let R : k[X] := -((3072 * zeta : k) • B ^ 2) - k2 • A
        have hFiberForm : zetaFiberPrimitive410 zeta k2 A B 0 =
            (1280 * zeta : k) • A ^ 3 + R := by
          have hTerminalZero : zetaTerminalPrimitive410 zeta A B 0 =
              (1280 * zeta : k) • A ^ 3 - (3072 * zeta : k) • B ^ 2 := by
            simp [zetaTerminalPrimitive410]
          rw [zetaFiberPrimitive410, hTerminalZero]
          dsimp only [R]
          abel
        have hRdegree : R.natDegree < 3 * A.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        have hMainDegree : ((1280 * zeta : k) • A ^ 3).natDegree =
            3 * A.natDegree := by
          rw [natDegree_smul _ hc1280, natDegree_pow]
        have hFiberDegree : (zetaFiberPrimitive410 zeta k2 A B 0).natDegree =
            3 * A.natDegree := by
          rw [hFiberForm, natDegree_add_eq_left_of_natDegree_lt]
          · exact hMainDegree
          · rw [hMainDegree]
            exact hRdegree
        omega

/-- The pure `zeta` constant-fiber trajectory is impossible. -/
theorem zetaOnly410_discriminant_trajectory_impossible
    (zeta k2 k1 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta 0 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta 0 0 A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 zeta 0 0 A B U = C terminal) : False := by
  have hDerivative : derivative (zetaFiberPrimitive410 zeta k2 A B U) =
      C terminal := by
    rw [← lWallTerminalNumerator410_zeta_eq_fiberDerivative
      zeta k2 A B U hTwo]
    exact hTerminal
  have hDegree : (zetaFiberPrimitive410 zeta k2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (zetaFiberPrimitive410 zeta k2 A B U) terminal hterminal hDerivative
  by_cases hAzero : A = 0
  · exact zetaOnly410_zeroA_impossible zeta k2 k1 A B U hzeta hAzero hTwo hDegree
  · by_cases hBzero : B = 0
    · exact zetaOnly410_zeroB_impossible zeta k2 k1 A B U hzeta hBzero
        hTwo hOne hDegree
    · by_cases hUzero : U = 0
      · exact zetaOnly410_zeroU_impossible zeta k2 A B U hzeta hAzero hBzero
          hUzero hTwo hDegree
      · exact zetaOnly410_nonzero_polynomials_impossible zeta k2 k1 terminal
          A B U A.natDegree B.natDegree U.natDegree hzeta hterminal
          hAzero hBzero hUzero rfl rfl rfl hTwo hOne hDegree

theorem etaOnly410_original_trajectory_impossible
    (alpha epsilon eta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (heta : eta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 0 eta 0 A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 0 eta 0 A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon 0 0 A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon 0 eta iota A B C0)
      B C0 = C terminal) : False := by
  have hTwoD : discriminantInvariantTwoNumerator410 0 0 0 0 0 eta 0 A B
      (A ^ 2 - (4 : k) • C0) = C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410 0 0 0 0 0 eta 0 A B
      (A ^ 2 - (4 : k) • C0) = C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410 0 0 0 0 0 eta 0 A B
      (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact etaOnly410_discriminant_trajectory_impossible eta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) heta (mul_ne_zero (by norm_num) hterminal)
      hTwoD hOneD hTerminalD

theorem zetaOnly410_original_trajectory_impossible
    (alpha epsilon zeta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta 0 0 A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta 0 0 A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta 0 A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta 0 iota A B C0)
      B C0 = C terminal) : False := by
  have hTwoD : discriminantInvariantTwoNumerator410 0 0 0 0 zeta 0 0 A B
      (A ^ 2 - (4 : k) • C0) = C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410 0 0 0 0 zeta 0 0 A B
      (A ^ 2 - (4 : k) • C0) = C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410 0 0 0 0 zeta 0 0 A B
      (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact zetaOnly410_discriminant_trajectory_impossible zeta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hzeta (mul_ne_zero (by norm_num) hterminal)
      hTwoD hOneD hTerminalD

/-- After closing all three pure terminal loads, every remaining trajectory
must carry at least two of `zeta`, `eta`, and `theta`.  Mixed-load walls are
the exact residual; no pure wall remains. -/
theorem zetaEtaTheta410_pairwise_nonzero_residual
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) :
    (zeta ≠ 0 ∧ eta ≠ 0) ∨ (zeta ≠ 0 ∧ theta ≠ 0) ∨
      (eta ≠ 0 ∧ theta ≠ 0) := by
  have hresidual := thetaWall410_earlierEffectiveLoad_residual
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  rcases hresidual with hzeta | heta
  · by_cases heta0 : eta = 0
    · subst eta
      have htheta : theta ≠ 0 := by
        intro htheta0
        subst theta
        exact zetaOnly410_original_trajectory_impossible alpha epsilon zeta iota
          k2 k1 terminal A B C0 hzeta hterminal hTwo hOne hLower
      exact Or.inr (Or.inl ⟨hzeta, htheta⟩)
    · exact Or.inl ⟨hzeta, heta0⟩
  · by_cases hzeta0 : zeta = 0
    · subst zeta
      have htheta : theta ≠ 0 := by
        intro htheta0
        subst theta
        exact etaOnly410_original_trajectory_impossible alpha epsilon eta iota
          k2 k1 terminal A B C0 heta hterminal hTwo hOne hLower
      exact Or.inr (Or.inr ⟨heta, htheta⟩)
    · exact Or.inl ⟨hzeta0, heta⟩

end ZetaEtaWalls410

end Max11DegreeRoutes
