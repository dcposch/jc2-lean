import LowScale68SecondaryLaterDeepThreeRadiusMiddleRight

/-! # Balanced attained middle face on `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusMiddleBalanced68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 8000000 in
/-- On `2h=3g` the cubic row-two face and the `d*e` face coincide. -/
theorem residualRowTwo_coeff_balancedChamber_of_threeRadius
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) *
        ((4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  change Q.natDegree ≤ 4 * n at hQ
  have hface : 11 * n - 2 * h = 11 * n - 3 * g := by omega
  have hidxQ : 6 * n - 1 < idx := by
    dsimp [idx]
    omega
  have hAQ : (A * derivative Q).natDegree < idx := by
    have hqder : (derivative Q).natDegree ≤ 4 * n - 1 :=
      (natDegree_derivative_le Q).trans (by omega)
    have hmul := natDegree_mul_le_of_le hA hqder
    have hi : 2 * n + (4 * n - 1) = 6 * n - 1 := by omega
    rw [hi] at hmul
    exact hmul.trans_lt hidxQ
  have hAQ' : (derivative A * Q).natDegree < idx := by
    have hader : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hmul := natDegree_mul_le_of_le hader hQ
    have hi : (2 * n - 1) + 4 * n = 6 * n - 1 := by omega
    rw [hi] at hmul
    exact hmul.trans_lt hidxQ
  have hB2d : (B ^ 2 * d).natDegree ≤ 11 * n - 2 * g - h := by
    compute_degree
    omega
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    have hder := natDegree_derivative_le (B ^ 2 * d)
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hp
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using hp
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using hp
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    have hidx_de : 11 * n - 2 * h - 1 = idx := by
      dsimp [idx]
      omega
    rw [← hidx_de, hde, hface]
  have hcore :
      ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
        ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
        ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    rw [hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
      (-18 : k) * ((11 * n - 3 * g : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, hde']
    linear_combination hcore
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  exact residualBalancedRowTwoScalar68
    ((11 * n - 3 * g : ℕ) : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hdisc

theorem residualRowTwo_balanced_forces_relation_of_threeRadius
    (A B c d e load : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    residualRowTwo_coeff_balancedChamber_of_threeRadius A B c d e n g h
      hn hg hgh hh hwall hbalanced hA hB hc hd he hQ hdisc] at hcoeff
  have hsc : (-8 / 27 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hcoeff).resolve_left (mul_ne_zero hsc hN)

set_option maxHeartbeats 12000000 in
/-- Source-facing exact balanced residual packet.  The previous left/right
closures leave this as the only attained middle leaf, and row two adds the
new scalar equation `4bc²=9de`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleBalancedRowTwo68
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
      2 * g = 3 * n)
    (hbalanced :
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
      2 * h = 3 * g) :
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
    Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (ee.coeff (6 * n - h)) ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 ∧
      (4 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h) = 0 := by
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
  change 2 * g = 3 * n at hwall
  change 2 * h = 3 * g at hbalanced
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
  have hg : 0 < g := secondary.1
  have hh : h < 2 * g := by omega
  have hgh : g < h := by omega
  have reduced :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleRowTwoSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hh)
  change (2 * h = 3 * g ∨ 3 * g < 2 * h) ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 ∧ _ at reduced
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusNonzeroResidualSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧ _
    at selector
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := secondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := secondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := selector.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - h := selector.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, selector.1, selector.2.1] at hi4c
  have hQ := residualIncidenceQ68_degree_le_fourRadius_of_threeRadius
    gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hwall hA hB hc
    (hd.trans (by omega)) (he.trans (by omega)) hi4c
  have hrowTwoe : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo : secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have hr := hrowTwoe
    rw [hCrec, hDrec, hErec] at hr
    exact polynomialSecondaryResidualRowTwo68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hr
  rw [selector.1, selector.2.1] at hrowTwo
  have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have hload := cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_threeRadius_beta
    alpha gamma delta epsilon zeta eta Ae Be ce
    ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg hwall
    hA hB hc hD (he.trans (by omega))
  have hrelation := residualRowTwo_balanced_forces_relation_of_threeRadius
    Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hn hg hgh hh hwall hbalanced hA hB hc hd he hQ
    reduced.2.2.2.2.2.1 hload hrowTwo
  exact ⟨reduced.2.1, reduced.2.2.1, reduced.2.2.2.1,
    reduced.2.2.2.2.1, reduced.2.2.2.2.2.2, reduced.2.2.2.2.2.1,
    hrelation⟩

#print axioms residualRowTwo_coeff_balancedChamber_of_threeRadius
#print axioms residualRowTwo_balanced_forces_relation_of_threeRadius
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusMiddleBalancedRowTwo68

end LaterDeepThreeRadiusMiddleBalanced68

end Max11DegreeRoutes
