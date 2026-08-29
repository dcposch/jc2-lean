import LowScale68SecondaryLaterDeepLowerParentAssembly

/-! # Residual invariant faces on the exact wall `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusResidualFaces68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

structure ThreeRadiusResidualDoubleInvariantFace68
    (a b c d e : k) : Prop where
  four : -b ^ 3 + 9 * b * e + 9 * c * d = 0
  three : -a * b * d - b ^ 2 * c + 3 * c * e = 0

theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_threeRadiusWall
    (B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hgh : g < h) (hh : h < 2 * g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_threeRadiusWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hgh : g < h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d
    (2 * n) (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_threeRadiusWall
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hgh : g < h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_threeRadiusWall
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hgh : g < h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem polynomialSecondaryResidualBetweenFace68_of_threeRadiusWall
    (gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hgh : g < h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      secondaryResidualInvariantFourPolynomial68_coeff_middle_of_threeRadiusWall
        B c d e n g h hn hwall hgh hh hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_threeRadiusWall
          gamma delta epsilon zeta A B c d e n g h hn hwall hgh hh
          hA hB hc hd), add_zero] at hz
    have hi : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_middle_of_threeRadiusWall
        A B c d e n g h hn hwall hgh hh hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_threeRadiusWall
          gamma delta epsilon zeta A B c d e n g h hn hwall hgh hh
          hA hB hc hd he), add_zero] at hz
    have hi : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hz'

theorem secondaryResidualInvariantFourPolynomial68_coeff_double_of_threeRadiusWall
    (B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 3 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - 2 * g) hB he
  have hBei : (3 * n - g) + (6 * n - 2 * g) = 9 * n - 3 * g := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - 2 * g) hc hd
  have hcdi : (4 * n - g) + (5 * n - 2 * g) = 9 * n - 3 * g := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

theorem secondaryResidualInvariantThreePolynomial68_coeff_double_of_threeRadiusWall
    (A B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d
    (2 * n) (3 * n - g) (5 * n - 2 * g) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c
    (3 * n - g) (3 * n - g) (4 * n - g) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g) =
      10 * n - 3 * g := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g) + (6 * n - 2 * g) = 10 * n - 3 * g := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_threeRadiusWall
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_threeRadiusWall
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem polynomialThreeRadiusResidualDoubleInvariantFace68
    (gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    ThreeRadiusResidualDoubleInvariantFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      secondaryResidualInvariantFourPolynomial68_coeff_double_of_threeRadiusWall
        B c d e n g hn hwall hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_threeRadiusWall
          gamma delta epsilon zeta A B c d e n g hn hwall hA hB hc hd),
      add_zero] at hz
    have hi : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_double_of_threeRadiusWall
        A B c d e n g hn hwall hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_threeRadiusWall
          gamma delta epsilon zeta A B c d e n g hn hwall hA hB hc hd he),
      add_zero] at hz
    have hi : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hz'

#print axioms polynomialSecondaryResidualBetweenFace68_of_threeRadiusWall
#print axioms polynomialThreeRadiusResidualDoubleInvariantFace68

end LaterDeepThreeRadiusResidualFaces68

end Max11DegreeRoutes
