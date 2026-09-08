import LowScale68SecondaryLaterDeepFiveRadiusTerminalLeafAssembly

/-! # The exact terminal equality face on `2g = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalEqualityFaceAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The first three scalar equations visible on the terminal equality wall.
The fourth field is the reduced row-one coefficient after the exact cubic
invariant has been substituted. -/
structure FiveRadiusTerminalEqualityFace68
    (a b c d e : k) : Prop where
  four : -b ^ 3 + 9 * b * e + 9 * c * d = 0
  three : -a * b * d - b ^ 2 * c + 3 * c * e = 0
  rowOne : a * b ^ 2 * c - c ^ 3 = 0

theorem secondaryResidualInvariantFourPolynomial68_coeff_terminalEquality
    (B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ n) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff n +
          9 * c.coeff (4 * n - g) * d.coeff 0) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) n hB he
  have hBei : (3 * n - g) + n = 9 * n - 3 * g := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) 0 hc hd
  have hcdi : (4 * n - g) + 0 = 9 * n - 3 * g := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

theorem secondaryResidualInvariantThreePolynomial68_coeff_terminalEquality
    (A B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ n) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff 0) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff n) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d
    (2 * n) (3 * n - g) 0 hA hB hd
  have hABdi : 2 * n + (3 * n - g) + 0 = 10 * n - 3 * g := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c
    (3 * n - g) (3 * n - g) (4 * n - g) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g) =
      10 * n - 3 * g := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) n hc he
  have hcei : (4 * n - g) + n = 10 * n - 3 * g := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_terminalEquality
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hB : B.natDegree ≤ 3 * n - g) (hd : d.natDegree ≤ 0) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - 3 * g := by
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
  simp only [zero_smul, zero_add]
  compute_degree
  omega

theorem secondaryLoadInvariantThreePolynomial68_degree_lt_terminalEquality
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) (he : e.natDegree ≤ n) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        10 * n - 3 * g := by
  rw [secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_delta]
  simp only [zero_smul, zero_add]
  compute_degree
  omega

def fiveRadiusTerminalEqualityRowOneCore68
    (A B c : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((-2 : k) • derivative (A * B ^ 2 * c) +
      (6 : k) • (c ^ 2 * derivative c))

def fiveRadiusTerminalEqualityRowOneTail68
    (gamma epsilon : k) (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((3 : k) • derivative (A * d ^ 2) +
        (3 : k) • derivative (B * c * d) +
        (6 : k) • (derivative B * c * d) +
        (-3 : k) • (B ^ 2 * derivative e) +
        (-18 : k) • (e * derivative e)) +
    gamma •
      ((2 / 3 : k) •
          (B * derivative d - d * derivative B -
            (2 : k) • (c * derivative c)) +
        (2 / 9 : k) • (derivative A * B ^ 2) +
        (4 / 9 : k) • (A * B * derivative B)) +
    (2 * epsilon : k) • derivative e

theorem fiveRadiusReducedRowOnePolynomial68_terminalEqualitySplit
    (gamma epsilon : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon 0 A B c d e =
      fiveRadiusTerminalEqualityRowOneCore68 A B c +
        fiveRadiusTerminalEqualityRowOneTail68 gamma epsilon A B c d e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusTerminalEqualityRowOneCore68,
    fiveRadiusTerminalEqualityRowOneTail68, zero_smul, add_zero]
  module

set_option maxHeartbeats 6000000 in
theorem fiveRadiusTerminalEqualityRowOneTail68_degree_lt
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0) (he : e.natDegree ≤ n) :
    (fiveRadiusTerminalEqualityRowOneTail68 gamma epsilon A B c d e).natDegree <
      12 * n - 3 * g - 1 := by
  let idx := 12 * n - 3 * g - 1
  have hAd2 : (derivative (A * d ^ 2)).natDegree < idx := by
    have hp : (A * d ^ 2).natDegree ≤ 2 * n := by
      compute_degree
      omega
    have hp' := natDegree_derivative_le (A * d ^ 2)
    dsimp [idx]
    omega
  have hBcd : (derivative (B * c * d)).natDegree < idx := by
    have hp : (B * c * d).natDegree ≤ 7 * n - 2 * g := by
      compute_degree
      omega
    have hp' := natDegree_derivative_le (B * c * d)
    dsimp [idx]
    omega
  have hBpcd : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hB2e : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hee : (e * derivative e).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hBd : (B * derivative d).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hdB : (d * derivative B).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hcc : (c * derivative c).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hApB2 : (derivative A * B ^ 2).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hABBp : (A * B * derivative B).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  have hep : (derivative e).natDegree < idx := by
    dsimp [idx]; compute_degree; omega
  simp only [fiveRadiusTerminalEqualityRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_smul_lt68 (-4 / 27 : k)
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_add_lt
                (deepGap_natDegree_smul_lt68 (3 : k) hAd2)
                (deepGap_natDegree_smul_lt68 (3 : k) hBcd))
              (deepGap_natDegree_smul_lt68 (6 : k) hBpcd))
            (deepGap_natDegree_smul_lt68 (-3 : k) hB2e))
          (deepGap_natDegree_smul_lt68 (-18 : k) hee)))
      (deepGap_natDegree_smul_lt68 gamma
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_smul_lt68 (2 / 3 : k)
              (deepGap_natDegree_sub_lt
                (deepGap_natDegree_sub_lt hBd hdB)
                (deepGap_natDegree_smul_lt68 (2 : k) hcc)))
            (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
          (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp))))
    (deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep)

set_option maxHeartbeats 6000000 in
theorem fiveRadiusTerminalEqualityRowOneCore68_coeff
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusTerminalEqualityRowOneCore68 A B c).coeff
        (12 * n - 3 * g - 1) =
      (4 / 3 : k) * (n : k) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g) - c.coeff (4 * n - g) ^ 3) := by
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hB
  have hB2 : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (2 * (3 * n - g)) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + 2 * (3 * n - g) + (4 * n - g) =
      12 * n - 3 * g := by omega
  rw [hiAB2c, hB2] at hAB2c
  have hAB2c' := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2c] at hAB2c'
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hic3 : 2 * (4 * n - g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hic3, hc2] at hc3
  simp only [fiveRadiusTerminalEqualityRowOneCore68, coeff_smul,
    coeff_add, smul_eq_mul, hAB2c', hc3]
  have hwallK : (2 : k) * (g : k) = (5 : k) * (n : k) := by
    exact_mod_cast hwall
  rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n),
    Nat.cast_sub (by omega : g ≤ 4 * n)]
  push_cast
  linear_combination
    (-4 / 9 : k) *
      (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) - c.coeff (4 * n - g) ^ 3) * hwallK

set_option maxHeartbeats 10000000 in
theorem polynomialFiveRadiusTerminalEqualityFace68
    (gamma epsilon i4 i3 : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0) (he : e.natDegree ≤ n)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : fiveRadiusReducedRowOnePolynomial68
      gamma epsilon 0 A B c d e = 0) :
    FiveRadiusTerminalEqualityFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff 0) (e.coeff n) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      secondaryResidualInvariantFourPolynomial68_coeff_terminalEquality
        B c d e n g hn hwall hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantFourPolynomial68_degree_lt_terminalEquality
          gamma epsilon A B c d e n g hn hwall hB hd), add_zero] at hz
    have hi : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hfac : (8 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hz).resolve_left hfac
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_terminalEquality
        A B c d e n g hn hwall hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_terminalEquality
          gamma epsilon A B c d e n g hn hwall hB hc he), add_zero] at hz
    have hi : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hfac : (8 / 9 : k) ≠ 0 := by norm_num
    have hz' := (mul_eq_zero.mp hz).resolve_left hfac
    linear_combination hz'
  · have htail := fiveRadiusTerminalEqualityRowOneTail68_degree_lt
      gamma epsilon A B c d e n g hn hwall hA hB hc hd he
    have hcore := fiveRadiusTerminalEqualityRowOneCore68_coeff
      A B c n g hn hwall hA hB hc
    have hz := congrArg
      (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrow
    rw [fiveRadiusReducedRowOnePolynomial68_terminalEqualitySplit, coeff_add,
      coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore, coeff_zero] at hz
    have hnK : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfac : (4 / 3 : k) * (n : k) ≠ 0 :=
      mul_ne_zero (by norm_num) hnK
    exact (mul_eq_zero.mp hz).resolve_left hfac

#print axioms polynomialFiveRadiusTerminalEqualityFace68

end LaterDeepFiveRadiusTerminalEqualityFaceAlgebra68

end Max11DegreeRoutes
