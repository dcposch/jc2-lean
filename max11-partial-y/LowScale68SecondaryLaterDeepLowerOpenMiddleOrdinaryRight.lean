import LowScale68SecondaryLaterDeepLowerOpenMiddleFiveSumRowTwo

/-! # Fixed-face row-two obstruction in the strict open middle packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleOrdinaryRight68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 6000000 in
theorem fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (fiveRadiusRowTwoFixedCore68 A B c).coeff (11 * n - 3 * g - 1) =
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  set idx := 11 * n - 3 * g - 1
  change (fiveRadiusRowTwoFixedCore68 A B c).coeff idx = _
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
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
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
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
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
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
  simp only [fiveRadiusRowTwoFixedCore68, coeff_smul, coeff_add,
    smul_eq_mul, hABpow, hA3', hBc, hcast3, hcast2, hcast11, idx]
  have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) hdisc
  linear_combination (-4 / 27 : k) * hsc

set_option maxHeartbeats 5000000 in
theorem laterDeepFiveSumReducedRowTwo_rightFixed_impossible68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hright : 3 * g < 2 * h) (hdeltaBelow : 3 * g < 5 * n)
    (ha : A.coeff (2 * n) ≠ 0) (hb : B.coeff (3 * n - g) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0) : False := by
  let idx := 11 * n - 3 * g - 1
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc hdisc
  have hfixedNe : (fiveRadiusRowTwoFixedCore68 A B c).coeff idx ≠ 0 := by
    dsimp [idx]
    rw [hfixed]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num)
          (Nat.cast_ne_zero.mpr (by omega))) ha)
      (pow_ne_zero 3 hb)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree < idx := by
    have hp : (d * e).natDegree ≤
        (5 * n - h) + (6 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (d * e)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have htail : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree < idx := by
    have hBd : (derivative (B ^ 2 * d)).natDegree < idx := by
      have hp : (B ^ 2 * d).natDegree ≤
          (6 * n - 2 * g) + (5 * n - h) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B ^ 2 * d)
      dsimp [idx]
      omega
    have hAd : (derivative A).natDegree < idx := by
      dsimp [idx]
      compute_degree
      omega
    have hBc : (derivative (B * c)).natDegree < idx := by
      have hp : (B * c).natDegree ≤
          (3 * n - g) + (4 * n - g) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B * c)
      dsimp [idx]
      omega
    have hdd : (derivative d).natDegree < idx := by
      dsimp [idx]
      compute_degree
      omega
    have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
    have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hAd
    have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
    have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hdd
    simp only [fiveRadiusRowTwoTail68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4
  have hz : (zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree < idx := by
    have hp : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
      compute_degree
      omega
    have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have hdelta :
      (delta • derivative (laterDeepFiveSumDeltaPrimitive68 A B c e)).natDegree < idx := by
    have hp : (laterDeepFiveSumDeltaPrimitive68 A B c e).natDegree ≤ 6 * n := by
      simp only [laterDeepFiveSumDeltaPrimitive68]
      compute_degree
      omega
    have hder := natDegree_derivative_le
      (laterDeepFiveSumDeltaPrimitive68 A B c e)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have hzrow := congrArg (fun p : k[X] => p.coeff idx) hrow
  rw [laterDeepFiveSumReducedRowTwoPolynomial68,
    fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_eq_zero_of_natDegree_lt hz,
    coeff_eq_zero_of_natDegree_lt hdelta,
    coeff_zero] at hzrow
  simp only [add_zero] at hzrow
  exact hfixedNe hzrow

set_option maxHeartbeats 12000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hmiddle :
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
      h < 2 * g) :
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
    l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change h < 2 * g at hmiddle
  have selected :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      _ ∧ _ ∧ _ at selected
  refine ⟨selected.1, selected.2.1, selected.2.2.1,
    selected.2.2.2.1, selected.2.2.2.2.1, ?_⟩
  rcases lt_trichotomy (g + h) (5 * n) with hsum | hsum | hsum
  · rcases selected.2.2.2.2.2.2.2 with below | wall | above
    · exact below.2
    · exact False.elim ((ne_of_lt hsum) wall.1)
    · exact False.elim ((not_lt_of_ge (le_of_lt above.1)) hsum)
  · have five :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumOrdinary68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hsum)
    exact five.2
  · have above :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFiveSelector68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hsum)
    change delta = 0 ∧ _ at above
    rcases above.2 with below | wall | high
    · exact below.2
    · have seven :=
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSevenSumOrdinary68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys (by
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using wall.1)
      exact seven.2.2
    · exact high.2.2

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleRightImpossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hmiddle :
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
      h < 2 * g)
    (hright :
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
      3 * g < 2 * h ∧ 3 * g < 5 * n) : False := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change h < 2 * g at hmiddle
  change 3 * g < 2 * h ∧ 3 * g < 5 * n at hright
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧ _
    at ordinary
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, ordinary.1, ordinary.2.1] at hi4e
    exact hi4e
  have hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at hrowTwo
  have hrow := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [ordinary.1, ordinary.2.1] at hrow
  have hred := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
  exact laterDeepFiveSumReducedRowTwo_rightFixed_impossible68
    gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
    hmiddle hopen hright.1 hright.2 ha ordinary.2.2.2.2.2.1
    hA secondary.2.1 secondary.2.2.1 ordinary.2.2.2.1
    ordinary.2.2.2.2.1 ordinary.2.2.2.2.2.2.2.2.2 hred

#print axioms fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
#print axioms laterDeepFiveSumReducedRowTwo_rightFixed_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleRightImpossible68

end LaterDeepLowerOpenMiddleOrdinaryRight68

end Max11DegreeRoutes
