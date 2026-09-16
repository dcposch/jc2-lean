import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart06Scratch

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

set_option maxHeartbeats 11000000 in
theorem fiveRadiusBalancedRowOneCore68_coeff_of_coincidentSeven
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusBalancedRowOneCore68 A B c d e).coeff (5 * n - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 *
                c.coeff (4 * n - g)) * ((5 * n : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) *
            c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hd
  have hd2 : (d ^ 2).coeff (2 * (5 * n - h)) =
      d.coeff (5 * n - h) ^ 2 :=
    coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2)
    (2 * n) (2 * (5 * n - h)) hA hd2deg
  have hiAd2 : 2 * n + 2 * (5 * n - h) = 5 * n := by omega
  rw [hiAd2, hd2] at hAd2
  have hAd2' := coeff_derivative_at_bound68 (A * d ^ 2) (5 * n) (by omega)
  rw [hAd2] at hAd2'
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hB
  have hB2 : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (2 * (3 * n - g)) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + 2 * (3 * n - g) + (4 * n - g) = 5 * n := by
    omega
  rw [hiAB2c, hB2] at hAB2c
  have hAB2c' := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (5 * n) (by omega)
  rw [hAB2c] at hAB2c'
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hic3 : 2 * (4 * n - g) + (4 * n - g) - 1 = 5 * n - 1 := by
    omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 5 * n - 1 := by omega
  rw [hiee] at hee
  simp only [fiveRadiusBalancedRowOneCore68, coeff_smul, coeff_add,
    smul_eq_mul, hAd2', hAB2c', hc3, hee]
  ring

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

set_option maxHeartbeats 7000000 in
theorem fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hddeg : d.natDegree ≤ 5 * n - h)
    (hedeg : e.natDegree ≤ 6 * n - h)
    (hc : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e).coeff
      (5 * n - 1) ≠ 0 := by
  have htail := fiveRadiusCoincidentSevenRowOneTail68_degree_lt
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hwallH hwallG
    hA hB hcdeg hddeg hedeg
  have hcore := fiveRadiusBalancedRowOneCore68_coeff_of_coincidentSeven
    A B c d e n g h hn hg hwallH hwallG hA hB hcdeg hddeg hedeg
  rw [fiveRadiusReducedRowOnePolynomial68_coincidentSevenSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hbal : 2 * h = 3 * g := by omega
  have hbalK : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    exact_mod_cast hbal
  have hng : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    have hpos : 0 < 4 * n - g := by omega
    have hcast : (((4 * n - g : ℕ) : k)) =
        (4 : k) * (n : k) - (g : k) := by
      rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
      push_cast
      ring
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr hpos.ne'
  have hscalar := residualRowOneScalar_ne_zero68
    (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hng hbalK hdisc hinc hrel
  have heq := residualRowOneScalar68
    (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hbalK hdisc hinc hrel
  intro hz
  apply hscalar
  rw [← heq]
  rw [Nat.cast_sub (by omega : g ≤ 4 * n),
    Nat.cast_sub (by omega : h ≤ 6 * n)] at hz
  push_cast at hz
  have hwallGK : (3 : k) * (g : k) = (7 : k) * (n : k) := by
    exact_mod_cast hwallG
  have hfiveK : (12 : k) * (n : k) - (3 : k) * (g : k) =
      (5 : k) * (n : k) := by
    linear_combination -hwallGK
  rw [hfiveK]
  exact hz

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

set_option maxHeartbeats 16000000 in
theorem laterDeepLowerOpenMiddle_coincidentSeven_impossible68
    (alpha gamma epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow2 : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta A B c
          ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow0 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) = 0) :
    False := by
  have hsum : g + h < 7 * n := by omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
      gamma epsilon zeta A B c d e n g h hn hopen hsum hA hB hd
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
      gamma epsilon zeta i4 i3 A B c d e n g h hn hg hgh hh hopen
      hload hA hB hc hd he hi4 hi3
  have hrow0rel := coincidentSeven_rowZero_relation68
    alpha gamma epsilon zeta eta i4 A B c d e n g h hn hg hgh hh
    hwallH hwallG ha hA hB hc hd he hdisc hi4 hrow0
  have hrow2rel := fiveRadiusReducedRowTwo_coincidentSevenWalls_relation68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hopen hwallH hwallG
    hA hB hc hd he hdisc hrow2
  have hrel := coincidentSeven_balancedRelation_of_rowZero_rowTwo68
    zeta (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) n hn hdisc hrow0rel hrow2rel
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon zeta eta i3 A B c d e hi3 hrow1
  have hne := fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hwallH hwallG
    hA hB hc hd he hc0 hdisc face.four hrel
  have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hreduced
  simp only [coeff_zero] at hz
  exact hne hz

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

/-! ## Source-facing closure -/

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentSeven_impossible68
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
      2 * h = 7 * n ∧ 3 * g = 7 * n) : False := by
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
  change 2 * h = 7 * n ∧ 3 * g = 7 * n at hseven
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
  have hrow2r := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow2r
  have hred2 : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon zeta eta i4 Ae Be ce d ee hi4c hrow2r
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
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
  have hrow1 := polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow1
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  have hidx : 6 * n - 1 ≠ 59 := by omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff (6 * n - 1) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hrow0 := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hsum0
  rw [ordinary.1, ordinary.2.1, hdelta, coeff_add, hterm] at hrow0
  exact laterDeepLowerOpenMiddle_coincidentSeven_impossible68
    alpha gamma epsilon zeta eta i4 i3 Ae Be ce d ee n g h hn hg
    ordinary.2.2.1 hmiddle hopen hseven.1 hseven.2 ha
    ordinary.2.2.2.2.2.2.1 hA secondary.2.1 secondary.2.2.1
    ordinary.2.2.2.1 ordinary.2.2.2.2.1
    ordinary.2.2.2.2.2.2.2.2.2 hi4c hi3c hred2 hrow1 hrow0

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
