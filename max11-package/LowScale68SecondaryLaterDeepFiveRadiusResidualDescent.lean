import LowScale68SecondaryLaterDeepFiveRadiusWallElimination

/-! # Residual descent from the later-deep wall `2g = 5n`

The endpoint packet has `l=beta=delta=0` and a selected residual gap `h>g`.
The next quartic comparison is with the old `zeta*A` load at `2h=9n`.
Below that wall the ordinary residual face is exposed; above it `zeta=0`
and the same face is recovered up to `h=5n`.  The equality wall is retained
as one exact mixed scalar packet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusResidualDescent68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

structure FiveRadiusResidualZetaWallFace68
    (a b c d e zeta : k) : Prop where
  four : (8 / 3 : k) * (b * e + c * d) + zeta * a = 0
  three : -a * b * d + 3 * c * e = 0

/-! ## Homogeneous residual coefficients at the endpoint -/

theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_fiveRadiusWall
    (B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
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

theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_fiveRadiusWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
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
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
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

theorem secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      zeta • A + (2 * epsilon : k) • B + (4 * gamma : k) • d := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  module

theorem secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_delta
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    secondaryLoadInvariantThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
        (2 / 3 * gamma : k) • B ^ 2 := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_residual_of_fiveRadiusWall_below
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hbelow : 2 * h < 9 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - g - h := by
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
  compute_degree
  omega

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_residual_of_fiveRadiusWall_above
    (gamma epsilon : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (habove : 9 * n < 2 * h) (hh : h < 2 * g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - g - h := by
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
  simp only [zero_smul, zero_add]
  compute_degree
  omega

theorem secondaryLoadInvariantThreePolynomial68_degree_lt_residual_of_fiveRadiusWall
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hh : h < 2 * g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        10 * n - g - h := by
  rw [secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_delta]
  compute_degree
  omega

/-! ## Ordinary faces below and above the `zeta` wall -/

theorem polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_below
    (gamma epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (hbelow : 2 * h < 9 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      secondaryResidualInvariantFourPolynomial68_coeff_middle_of_fiveRadiusWall
        B c d e n g h hn hwall hgh hh hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantFourPolynomial68_degree_lt_residual_of_fiveRadiusWall_below
          gamma epsilon zeta A B c d e n g h hn hwall hbelow hA hB hd),
      add_zero] at hz
    have hi : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_middle_of_fiveRadiusWall
        A B c d e n g h hn hwall hgh hh hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_residual_of_fiveRadiusWall
          gamma epsilon zeta A B c d e n g h hn hwall hh hB hc he),
      add_zero] at hz
    have hi : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hz'

theorem cubicFirstIntegralFourPolynomial68_forces_zeta_of_fiveRadiusWall_above
    (gamma epsilon zeta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (habove : 9 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n) (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    zeta = 0 := by
  have hhom : (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
      2 * n := by
    have hB3 : (B ^ 3).natDegree < 2 * n := by compute_degree; omega
    have hBe : (B * e).natDegree < 2 * n := by compute_degree; omega
    have hcd : (c * d).natDegree < 2 * n := by compute_degree; omega
    simp only [secondaryResidualInvariantFourPolynomial68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (-8 / 27 : k) hB3)
        (deepGap_natDegree_smul_lt68 (8 / 3 : k) hBe))
      (deepGap_natDegree_smul_lt68 (8 / 3 : k) hcd)
  have hloadRest : (secondaryLoadInvariantFourPolynomial68
      0 0 gamma 0 epsilon 0 A B c
        ((1 / 3 : k) • (A * B) + d) e).natDegree < 2 * n := by
    rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
    simp only [zero_smul, zero_add]
    compute_degree
    omega
  have hloadEq : secondaryLoadInvariantFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e =
      zeta • A + secondaryLoadInvariantFourPolynomial68
        0 0 gamma 0 epsilon 0 A B c
          ((1 / 3 : k) • (A * B) + d) e := by
    rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta,
      secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
    simp only [zero_smul, zero_add]
    module
  have hz := congrArg (fun p : k[X] => p.coeff (2 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    hloadEq,
    coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt hhom,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hloadRest,
    add_zero, zero_add] at hz
  have hi : 2 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hz
  exact (mul_eq_zero.mp hz).resolve_right ha

theorem polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_above
    (gamma epsilon i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (habove : 9 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon 0 A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon 0 A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      secondaryResidualInvariantFourPolynomial68_coeff_middle_of_fiveRadiusWall
        B c d e n g h hn hwall hgh hh hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantFourPolynomial68_degree_lt_residual_of_fiveRadiusWall_above
          gamma epsilon A B c d e n g h hn hwall habove hh hB hd),
      add_zero] at hz
    have hi : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_middle_of_fiveRadiusWall
        A B c d e n g h hn hwall hgh hh hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_residual_of_fiveRadiusWall
          gamma epsilon 0 A B c d e n g h hn hwall hh hB hc he),
      add_zero] at hz
    have hi : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hz'

theorem polynomialFiveRadiusResidualZetaWallFace68
    (gamma epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hgh : g < h) (htie : 2 * h = 9 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    FiveRadiusResidualZetaWallFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) zeta := by
  have hh : h < 2 * g := by omega
  constructor
  · have hloadRest : (secondaryLoadInvariantFourPolynomial68
        0 0 gamma 0 epsilon 0 A B c
          ((1 / 3 : k) • (A * B) + d) e).natDegree < 2 * n := by
      rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
      simp only [zero_smul, zero_add]
      compute_degree
      omega
    have hloadEq : secondaryLoadInvariantFourPolynomial68
        0 0 gamma 0 epsilon zeta A B c
          ((1 / 3 : k) • (A * B) + d) e =
        zeta • A + secondaryLoadInvariantFourPolynomial68
          0 0 gamma 0 epsilon 0 A B c
            ((1 / 3 : k) • (A * B) + d) e := by
      rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta,
        secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
      simp only [zero_smul, zero_add]
      module
    have hidx : 9 * n - g - h = 2 * n := by omega
    have hz := congrArg (fun p : k[X] => p.coeff (2 * n)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
      cubicFirstIntegralFourPolynomial68_residualCoordinates,
      coeff_add, ← hidx,
      secondaryResidualInvariantFourPolynomial68_coeff_middle_of_fiveRadiusWall
        B c d e n g h hn hwall hgh hh hB hc hd he,
      hidx, hloadEq, coeff_add, coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hloadRest, add_zero] at hz
    have hi : 2 * n ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    exact hz
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
      cubicFirstIntegralThreePolynomial68_residualCoordinates,
      secondaryResidualInvariantThreePolynomial68_coeff_middle_of_fiveRadiusWall
        A B c d e n g h hn hwall hgh hh hA hB hc hd he,
      coeff_eq_zero_of_natDegree_lt
        (secondaryLoadInvariantThreePolynomial68_degree_lt_residual_of_fiveRadiusWall
          gamma epsilon zeta A B c d e n g h hn hwall hh hB hc he),
      add_zero] at hz
    have hi : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hi] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hz'

/-! ## Canonical source-level descent packet -/

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualDescent68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g = 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    let h := secondaryResidualGap68 n d ee
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      ((d = 0 ∧ ee = 0) ∨
        (h < 5 * n ∧
          ((2 * h < 9 * n ∧
              Be.coeff (3 * n - g) ≠ 0 ∧
              ce.coeff (4 * n - g) ≠ 0 ∧
              d.coeff (5 * n - h) ≠ 0 ∧
              ee.coeff (6 * n - h) ≠ 0 ∧
              Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
                3 * ce.coeff (4 * n - g) ^ 2 = 0) ∨
            (2 * h = 9 * n ∧
              (d.coeff (5 * n - h) ≠ 0 ∨
                ee.coeff (6 * n - h) ≠ 0) ∧
              FiveRadiusResidualZetaWallFace68
                (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
                (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
                (ee.coeff (6 * n - h)) zeta) ∨
            (9 * n < 2 * h ∧ zeta = 0 ∧
              Be.coeff (3 * n - g) ≠ 0 ∧
              ce.coeff (4 * n - g) ≠ 0 ∧
              d.coeff (5 * n - h) ≠ 0 ∧
              ee.coeff (6 * n - h) ≠ 0 ∧
              Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
                3 * ce.coeff (4 * n - g) ^ 2 = 0))) ∨
        (5 * n ≤ h ∧
          (d.coeff (5 * n - h) ≠ 0 ∨
            ee.coeff (6 * n - h) ≠ 0))) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change 2 * g = 5 * n at hwall
  have entry :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualEntry68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧
      ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h at entry
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hB := secondary.2.1
  have hc := secondary.2.2.1
  have hdbase : d.natDegree < 5 * n := entry.2.2.2.2.2.1.trans
    (by omega)
  have hebase : ee.natDegree < 6 * n := entry.2.2.2.2.2.2.1.trans
    (by omega)
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h :=
    secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hsupport : Be.coeff (3 * n - g) ≠ 0 ∨
      ce.coeff (4 * n - g) ≠ 0 := by
    rcases secondary.2.2.2.2.2 with hb | hc' | hD | he
    · exact Or.inl hb
    · exact Or.inr hc'
    · left
      intro hb
      have hab : Ae.coeff (2 * n) * Be.coeff (3 * n - g) = 0 := by
        rw [hb, mul_zero]
      rw [entry.2.2.2.2.1] at hab
      exact hD ((mul_eq_zero.mp hab).resolve_left (by norm_num))
    · exact False.elim (he entry.2.2.2.1)
  refine ⟨entry.1, entry.2.1, entry.2.2.1, entry.2.2.2.2.2.2.2,
    hbounds.1, hbounds.2, hsupport, ?_⟩
  by_cases hboth : d = 0 ∧ ee = 0
  · exact Or.inl hboth
  · have attained := secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hboth
    rcases lt_or_ge h (5 * n) with hlt | hge
    · refine Or.inr (Or.inl ⟨hlt, ?_⟩)
      have hh : h < 2 * g := by omega
      have hgh := entry.2.2.2.2.2.2.2
      have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
        simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
      have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
          (1 / 3 : k) • (Ae * ce) + ee := by
        simpa only [ce, ee] using
          cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
      have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
        simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
      obtain ⟨i4, hi4⟩ := hsys.firstFour
      obtain ⟨i3, hi3⟩ := hsys.firstThree
      have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
          Ae Be Ce De Ee = C i4 := by
        simpa only [Ae, Be, Ce, De, Ee] using
          expand_firstIntegralFourPolynomial68_of_eq
            l beta gamma delta epsilon zeta i4 A B C0 D E hi4
      have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
          Ae Be Ce De Ee = C i3 := by
        simpa only [Ae, Be, Ce, De, Ee] using
          expand_firstIntegralThreePolynomial68_of_eq
            l beta gamma delta epsilon zeta i3 A B C0 D E hi3
      have hi4c := hi4e
      rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
        hDrec, entry.1, entry.2.1, entry.2.2.1] at hi4c
      have hi3c := hi3e
      rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
        hDrec, entry.1, entry.2.1, entry.2.2.1] at hi3c
      rcases lt_trichotomy (2 * h) (9 * n) with hbelow | htie | habove
      · left
        have face := polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_below
          gamma epsilon zeta i4 i3 Ae Be ce d ee n g h hn hwall hgh hh hbelow
          hA hB hc hbounds.1 hbounds.2 hi4c hi3c
        have hclass := secondaryResidualBetweenFace68_classify_of_support
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
          (ee.coeff (6 * n - h)) ha hsupport attained face
        exact ⟨hbelow, hclass⟩
      · right; left
        exact ⟨htie, attained,
          polynomialFiveRadiusResidualZetaWallFace68
            gamma epsilon zeta i4 i3 Ae Be ce d ee n g h hn hwall hgh htie
            hA hB hc hbounds.1 hbounds.2 hi4c hi3c⟩
      · right; right
        have hzeta := cubicFirstIntegralFourPolynomial68_forces_zeta_of_fiveRadiusWall_above
          gamma epsilon zeta i4 Ae Be ce d ee n g h hn hwall habove
          hA ha hB hc hbounds.1 hbounds.2 hi4c
        have hi4z := hi4c
        have hi3z := hi3c
        rw [hzeta] at hi4z hi3z
        have face := polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_above
          gamma epsilon i4 i3 Ae Be ce d ee n g h hn hwall hgh hh habove
          hA hB hc hbounds.1 hbounds.2 hi4z hi3z
        have hclass := secondaryResidualBetweenFace68_classify_of_support
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
          (ee.coeff (6 * n - h)) ha hsupport attained face
        exact ⟨habove, hzeta, hclass⟩
    · exact Or.inr (Or.inr ⟨hge, attained⟩)

#print axioms FiveRadiusResidualZetaWallFace68
#print axioms polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_below
#print axioms cubicFirstIntegralFourPolynomial68_forces_zeta_of_fiveRadiusWall_above
#print axioms polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_above
#print axioms polynomialFiveRadiusResidualZetaWallFace68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualDescent68

end LaterDeepFiveRadiusResidualDescent68

end Max11DegreeRoutes
