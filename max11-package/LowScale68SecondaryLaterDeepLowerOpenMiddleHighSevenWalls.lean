import LowScale68SecondaryLaterDeepLowerOpenMiddleHighZetaZeroEndgame

/-! # Exact seven-wall packets for the strict-high ordinary chamber

At degree `4n-1`, the `zeta*A^2` face ties the `d*e` face on
`2h=7n`, the fixed cubic face on `3g=7n`, and both faces when the two
walls coincide.  This file records the three exact packets and lifts them
back to an integrated source system.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighSevenWalls68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
theorem fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
    (gamma epsilon i4 : k) (A B c d : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hseven : 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      4 * n - 1 := by
  have hBd : (derivative (B ^ 2 * d)).natDegree < 4 * n - 1 := by
    have hp : (B ^ 2 * d).natDegree ≤
        (6 * n - 2 * g) + (5 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B ^ 2 * d)
    omega
  have hAd : (derivative A).natDegree < 4 * n - 1 := by
    compute_degree
    omega
  have hBc : (derivative (B * c)).natDegree < 4 * n - 1 := by
    have hp : (B * c).natDegree ≤
        (3 * n - g) + (4 * n - g) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c)
    omega
  have hdd : (derivative d).natDegree < 4 * n - 1 := by
    compute_degree
    omega
  have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
  have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hAd
  have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
  have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hdd
  simp only [fiveRadiusRowTwoTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwo_coeff_leftSevenWall68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 2 * h = 7 * n) (habove : 7 * n < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e).coeff
        (4 * n - 1) =
      (8 / 3 : k) * ((4 * n : ℕ) : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        zeta * (n : k) * A.coeff (2 * n) ^ 2 := by
  have hfixed := fiveRadiusRowTwoFixedCore68_degree_le_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc
  have hfixed' : (fiveRadiusRowTwoFixedCore68 A B c).natDegree <
      4 * n - 1 := by omega
  have hseven : 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g := by omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
    gamma epsilon i4 A B c d n g h hn hg hgh hopen hseven hA hB hc hd
  have hde := fiveRadiusRowTwoDE68_coeff d e n h hn (by omega) hd he
  have hdei : 11 * n - 2 * h - 1 = 4 * n - 1 := by omega
  have hdeN : 11 * n - 2 * h = 4 * n := by omega
  rw [hdei, hdeN] at hde
  have hz := derivative_quarterSquare_add_coeff_middleSevenSum68
    A c n g hn hg hA hc
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, coeff_eq_zero_of_natDegree_lt hfixed',
    coeff_eq_zero_of_natDegree_lt htail, zero_add, hde,
    coeff_smul, smul_eq_mul, hz]
  ring

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwo_coeff_rightSevenWall68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n) (habove : 7 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e).coeff
        (4 * n - 1) =
      (32 / 81 : k) * ((4 * n : ℕ) : k) *
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
        zeta * (n : k) * A.coeff (2 * n) ^ 2 := by
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc hdisc
  have hfixedi : 11 * n - 3 * g - 1 = 4 * n - 1 := by omega
  have hfixedN : 11 * n - 3 * g = 4 * n := by omega
  rw [hfixedi, hfixedN] at hfixed
  have hdeprod : (d * e).natDegree ≤
      (5 * n - h) + (6 * n - h) := by
    compute_degree
    omega
  have hdeder := natDegree_derivative_le (d * e)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree <
      4 * n - 1 := by
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have hseven : 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g := by omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
    gamma epsilon i4 A B c d n g h hn hg hgh hopen hseven hA hB hc hd
  have hz := derivative_quarterSquare_add_coeff_middleSevenSum68
    A c n g hn hg hA hc
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, hfixed, coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_smul, smul_eq_mul, hz]
  ring

set_option maxHeartbeats 6000000 in
theorem fiveRadiusReducedRowTwo_coeff_coincidentSevenWalls68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e).coeff
        (4 * n - 1) =
      (32 / 81 : k) * ((4 * n : ℕ) : k) *
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
        (8 / 3 : k) * ((4 * n : ℕ) : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        zeta * (n : k) * A.coeff (2 * n) ^ 2 := by
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc hdisc
  have hfixedi : 11 * n - 3 * g - 1 = 4 * n - 1 := by omega
  have hfixedN : 11 * n - 3 * g = 4 * n := by omega
  rw [hfixedi, hfixedN] at hfixed
  have hde := fiveRadiusRowTwoDE68_coeff d e n h hn (by omega) hd he
  have hdei : 11 * n - 2 * h - 1 = 4 * n - 1 := by omega
  have hdeN : 11 * n - 2 * h = 4 * n := by omega
  rw [hdei, hdeN] at hde
  have hseven : 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g := by omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
    gamma epsilon i4 A B c d n g h hn hg hgh hopen hseven hA hB hc hd
  have hz := derivative_quarterSquare_add_coeff_middleSevenSum68
    A c n g hn hg hA hc
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, hfixed, hde, coeff_eq_zero_of_natDegree_lt htail,
    coeff_smul, smul_eq_mul, hz]
  ring

theorem fiveRadiusReducedRowTwo_leftSevenWall_relation68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 2 * h = 7 * n) (habove : 7 * n < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    (8 / 3 : k) * ((4 * n : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) +
      zeta * (n : k) * A.coeff (2 * n) ^ 2 = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwo_coeff_leftSevenWall68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hopen hwall habove
    hA hB hc hd he, coeff_zero] at hz
  exact hz

theorem fiveRadiusReducedRowTwo_rightSevenWall_relation68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n) (habove : 7 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    (32 / 81 : k) * ((4 * n : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
      zeta * (n : k) * A.coeff (2 * n) ^ 2 = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwo_coeff_rightSevenWall68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hopen hwall habove
    hA hB hc hd he hdisc, coeff_zero] at hz
  exact hz

theorem fiveRadiusReducedRowTwo_coincidentSevenWalls_relation68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    (32 / 81 : k) * ((4 * n : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
      (8 / 3 : k) * ((4 * n : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) +
      zeta * (n : k) * A.coeff (2 * n) ^ 2 = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwo_coeff_coincidentSevenWalls68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hopen hwallH hwallG
    hA hB hc hd he hdisc, coeff_zero] at hz
  exact hz

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighSevenWalls_packet68
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
    (hseven :
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
      7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g)
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
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      2 * h = 7 * n ∨ 3 * g = 7 * n) :
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
    (2 * h = 7 * n ∧ 7 * n < 3 * g ∧
      (8 / 3 : k) * ((4 * n : ℕ) : k) *
          d.coeff (5 * n - h) * ee.coeff (6 * n - h) +
        zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
    (3 * g = 7 * n ∧ 7 * n < 2 * h ∧
      (32 / 81 : k) * ((4 * n : ℕ) : k) *
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 +
        zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
    (2 * h = 7 * n ∧ 3 * g = 7 * n ∧
      (32 / 81 : k) * ((4 * n : ℕ) : k) *
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 +
        (8 / 3 : k) * ((4 * n : ℕ) : k) *
          d.coeff (5 * n - h) * ee.coeff (6 * n - h) +
        zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) := by
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
  change 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g at hseven
  change 2 * h = 7 * n ∨ 3 * g = 7 * n at hwall
  have hhigh5 : 5 * n < 2 * h ∧ 5 * n < 3 * g := by omega
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighStrict_forces_delta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hhigh5)
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧ _ at ordinary
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
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, ordinary.1, ordinary.2.1, hdelta] at hi4e
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
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | hbalanced | hright
  · have hwH : 2 * h = 7 * n := by omega
    have habove : 7 * n < 3 * g := by
      rw [← hwH]
      exact hleft
    exact Or.inl ⟨hwH, habove,
      fiveRadiusReducedRowTwo_leftSevenWall_relation68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
        hopen hwH habove hA secondary.2.1 secondary.2.2.1
        ordinary.2.2.2.1 ordinary.2.2.2.2.1 hred⟩
  · have hwH : 2 * h = 7 * n := by omega
    have hwG : 3 * g = 7 * n := by omega
    exact Or.inr (Or.inr ⟨hwH, hwG,
      fiveRadiusReducedRowTwo_coincidentSevenWalls_relation68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
        hopen hwH hwG hA secondary.2.1 secondary.2.2.1
        ordinary.2.2.2.1 ordinary.2.2.2.2.1
        ordinary.2.2.2.2.2.2.2.2.2 hred⟩)
  · have hwG : 3 * g = 7 * n := by omega
    have habove : 7 * n < 2 * h := by
      rw [← hwG]
      exact hright
    exact Or.inr (Or.inl ⟨hwG, habove,
      fiveRadiusReducedRowTwo_rightSevenWall_relation68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
        hopen hwG habove hA secondary.2.1 secondary.2.2.1
        ordinary.2.2.2.1 ordinary.2.2.2.2.1
        ordinary.2.2.2.2.2.2.2.2.2 hred⟩)

#print axioms fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
#print axioms fiveRadiusReducedRowTwo_coeff_leftSevenWall68
#print axioms fiveRadiusReducedRowTwo_coeff_rightSevenWall68
#print axioms fiveRadiusReducedRowTwo_coeff_coincidentSevenWalls68
#print axioms fiveRadiusReducedRowTwo_leftSevenWall_relation68
#print axioms fiveRadiusReducedRowTwo_rightSevenWall_relation68
#print axioms fiveRadiusReducedRowTwo_coincidentSevenWalls_relation68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighSevenWalls_packet68

end LaterDeepLowerOpenMiddleHighSevenWalls68

end Max11DegreeRoutes
