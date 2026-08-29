import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentFiveDeltaZero

/-! # The first nonzero `delta` load on the coincident five wall

The quartic first integral places the incidence defect exactly at degree
`4n`, with coefficient `-(3/32) * delta * a^2`.  Since the previous module
proves `delta != 0`, this is an attained source-facing edge.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentFiveDeltaLoad68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_degree_le_fourRadius_of_coincidentFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 5 * n) (hwallG : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma delta epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta]
    at hQeq
  rw [hQeq]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
theorem residualIncidenceQ68_coeff_fourRadius_of_coincidentFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 5 * n) (hwallG : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (4 * n) =
      -(3 / 32 : k) * delta * A.coeff (2 * n) ^ 2 := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma delta epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta]
    at hQeq
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hiA : 2 * (2 * n) = 4 * n := by omega
  rw [hiA] at hA2
  have hAlt : A.natDegree < 4 * n := hA.trans_lt (by omega)
  have hBlt : B.natDegree < 4 * n := hB.trans_lt (by omega)
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have hdlt : d.natDegree < 4 * n := hd.trans_lt (by omega)
  have hindex : 4 * n ≠ 0 := by omega
  rw [hQeq, coeff_smul, coeff_sub, coeff_C, if_neg hindex,
    coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_smul, coeff_smul, coeff_smul, coeff_smul, coeff_smul,
    smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hAlt,
    coeff_eq_zero_of_natDegree_lt hBlt,
    hA2,
    coeff_eq_zero_of_natDegree_lt hclt,
    coeff_eq_zero_of_natDegree_lt hdlt]
  ring

theorem residualIncidenceQ68_natDegree_eq_fourRadius_of_coincidentFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 5 * n) (hwallG : 3 * g = 5 * n)
    (ha : A.coeff (2 * n) ≠ 0) (hdelta : delta ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree = 4 * n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact residualIncidenceQ68_degree_le_fourRadius_of_coincidentFive
      gamma delta epsilon zeta i4 A B c d e n g h hn hwallH hwallG
      hA hB hc hd hi4
  · rw [residualIncidenceQ68_coeff_fourRadius_of_coincidentFive
      gamma delta epsilon zeta i4 A B c d e n g h hn hwallH hwallG
      hA hB hc hd hi4]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hdelta) (pow_ne_zero 2 ha)

set_option maxHeartbeats 18000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_deltaLoadPacket68
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
      2 * h = 5 * n ∧ 3 * g = 5 * n) :
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
    delta ≠ 0 ∧
      (residualIncidenceQ68 Be ce d ee).natDegree = 4 * n ∧
      (residualIncidenceQ68 Be ce d ee).coeff (4 * n) =
        -(3 / 32 : k) * delta * Ae.coeff (2 * n) ^ 2 := by
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
  change 2 * h = 5 * n ∧ 3 * g = 5 * n at hwall
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_forces_delta_ne_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hwall)
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧ _
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
  have hqdeg :=
    residualIncidenceQ68_natDegree_eq_fourRadius_of_coincidentFive
      gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hwall.1 hwall.2
      ha hdelta hA secondary.2.1 secondary.2.2.1 ordinary.2.2.2.1 hi4c
  have hqcoeff := residualIncidenceQ68_coeff_fourRadius_of_coincidentFive
    gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hwall.1 hwall.2
    hA secondary.2.1 secondary.2.2.1 ordinary.2.2.2.1 hi4c
  exact ⟨hdelta, hqdeg, hqcoeff⟩

#print axioms residualIncidenceQ68_degree_le_fourRadius_of_coincidentFive
#print axioms residualIncidenceQ68_coeff_fourRadius_of_coincidentFive
#print axioms residualIncidenceQ68_natDegree_eq_fourRadius_of_coincidentFive
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_deltaLoadPacket68

end LaterDeepLowerOpenMiddleHighCoincidentFiveDeltaLoad68

end Max11DegreeRoutes
