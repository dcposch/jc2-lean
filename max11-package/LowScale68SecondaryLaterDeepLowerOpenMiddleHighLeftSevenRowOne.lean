import LowScale68SecondaryLaterDeepLowerOpenMiddleHighSevenWalls

/-! # Row-one closure for the strict left seven wall

The exact wall `2h=7n<3g` makes the `A*d^2` and `e*e'` terms tie at
degree `5n-1`.  All other reduced row-one terms lie strictly below this
degree.  The cubic invariant supplies the incidence relation, and the
resulting scalar is nonzero by the discriminant relation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighLeftSevenRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 7000000 in
theorem fiveRadiusSevenWallRowOneTail68_degree_lt_of_laterDeepLowerOpen_left
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hseven : 2 * h = 7 * n) (habove : 7 * n < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusSevenWallRowOneTail68 gamma epsilon zeta A B c d e).natDegree <
      5 * n - 1 := by
  have hAB2c : (derivative (A * B ^ 2 * c)).natDegree < 5 * n - 1 := by
    have hp : (A * B ^ 2 * c).natDegree ≤ 12 * n - 3 * g := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (A * B ^ 2 * c)
    omega
  have hc3 : (c ^ 2 * derivative c).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hBcd : (derivative (B * c * d)).natDegree < 5 * n - 1 := by
    have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c * d)
    omega
  have hBp : (derivative B * c * d).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hBe : (B ^ 2 * derivative e).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hep : (derivative e).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hApB : (derivative A * B).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hdp : (derivative d).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hs1 := deepGap_natDegree_smul_lt68 (-2 : k) hAB2c
  have hs2 := deepGap_natDegree_smul_lt68 (6 : k) hc3
  have hs3 := deepGap_natDegree_smul_lt68 (3 : k) hBcd
  have hs4 := deepGap_natDegree_smul_lt68 (6 : k) hBp
  have hs5 := deepGap_natDegree_smul_lt68 (-3 : k) hBe
  have hmain := deepGap_natDegree_smul_lt68 (-4 / 27 : k)
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt hs1 hs2) hs3) hs4) hs5)
  have hccs := deepGap_natDegree_smul_lt68 (2 : k) hcc
  have hginner := deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_smul_lt68 (2 / 3 : k)
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_sub_lt hBd hdB) hccs))
      (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
    (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp)
  have hgpart := deepGap_natDegree_smul_lt68 gamma hginner
  have hepart := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep
  have hzinner := deepGap_natDegree_add_lt
    (deepGap_natDegree_smul_lt68 (1 / 3 : k) hApB) hdp
  have hzpart := deepGap_natDegree_smul_lt68 zeta hzinner
  simp only [fiveRadiusSevenWallRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt hmain hgpart) hepart) hzpart

set_option maxHeartbeats 8000000 in
theorem fiveRadiusReducedRowOnePolynomial68_coeff_leftSeven_ne_zero
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hseven : 2 * h = 7 * n) (habove : 7 * n < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hddeg : d.natDegree ≤ 5 * n - h)
    (hedeg : e.natDegree ≤ 6 * n - h)
    (hc : c.coeff (4 * n - g) ≠ 0)
    (hd : d.coeff (5 * n - h) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) :
    (fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e).coeff
      (5 * n - 1) ≠ 0 := by
  have htail :=
    fiveRadiusSevenWallRowOneTail68_degree_lt_of_laterDeepLowerOpen_left
      gamma epsilon zeta A B c d e n g h hn hg hgh hh hopen hseven habove
      hA hB hcdeg hddeg hedeg
  have hcore := fiveRadiusSevenWallRowOneCore68_coeff
    A d e n h hn hseven hA hddeg hedeg
  rw [fiveRadiusReducedRowOnePolynomial68_sevenSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hscalar := fiveRadiusSevenWallScalar_ne_zero68
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hd hdisc hinc
  have hcast : (((6 * n - h : ℕ) : k)) = (5 / 2 : k) * (n : k) := by
    have hsevenK : (2 : k) * (h : k) = (7 : k) * (n : k) := by
      exact_mod_cast hseven
    have heq : (2 : k) * ((6 * n - h : ℕ) : k) = (5 : k) * (n : k) := by
      rw [Nat.cast_sub (by omega : h ≤ 6 * n)]
      push_cast
      linear_combination -hsevenK
    linear_combination (1 / 2 : k) * heq
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [hcast]
  intro hz
  push_cast at hz
  apply hscalar
  have hfactor : (-20 / 9 : k) * (n : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hncast
  have hzero : (-20 / 9 : k) * (n : k) *
      (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 -
        (3 : k) * e.coeff (6 * n - h) ^ 2) = 0 := by
    linear_combination hz
  exact (mul_eq_zero.mp hzero).resolve_left hfactor

set_option maxHeartbeats 12000000 in
theorem laterDeepLowerOpenMiddle_leftSeven_reducedRowOne_impossible68
    (alpha gamma epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hseven : 2 * h = 7 * n) (habove : 7 * n < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta A B c
          ((1 / 3 : k) • (A * B) + d) e = 0) : False := by
  have hsum : g + h < 7 * n := by omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
      gamma epsilon zeta A B c d e n g h hn hopen hsum hA hB hd
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
      gamma epsilon zeta i4 i3 A B c d e n g h hn hg hgh hh hopen
      hload hA hB hc hd he hi4 hi3
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon zeta eta i3 A B c d e hi3 hrow
  have hne := fiveRadiusReducedRowOnePolynomial68_coeff_leftSeven_ne_zero
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hopen hseven habove
    hA hB hc hd he hc0 hd0 hdisc face.four
  have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hreduced
  simp only [coeff_zero] at hz
  exact hne hz

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftSeven_impossible68
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
      2 * h = 7 * n ∧ 7 * n < 3 * g) : False := by
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
  change 2 * h = 7 * n ∧ 7 * n < 3 * g at hseven
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
  obtain ⟨i3, hi3⟩ := hsys.firstThree
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
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, ordinary.1, ordinary.2.1, hdelta] at hi3e
    exact hi3e
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  rw [hCrec, hDrec, hErec] at h1e
  have hrow := polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow
  exact laterDeepLowerOpenMiddle_leftSeven_reducedRowOne_impossible68
    alpha gamma epsilon zeta eta i4 i3 Ae Be ce d ee n g h hn hg
    ordinary.2.2.1 hmiddle hopen hseven.1 hseven.2 hA secondary.2.1
    secondary.2.2.1 ordinary.2.2.2.1 ordinary.2.2.2.2.1
    ordinary.2.2.2.2.2.2.1 ordinary.2.2.2.2.2.2.2.1
    ordinary.2.2.2.2.2.2.2.2.2 hi4c hi3c hrow

#print axioms fiveRadiusSevenWallRowOneTail68_degree_lt_of_laterDeepLowerOpen_left
#print axioms fiveRadiusReducedRowOnePolynomial68_coeff_leftSeven_ne_zero
#print axioms laterDeepLowerOpenMiddle_leftSeven_reducedRowOne_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftSeven_impossible68

end LaterDeepLowerOpenMiddleHighLeftSevenRowOne68

end Max11DegreeRoutes
