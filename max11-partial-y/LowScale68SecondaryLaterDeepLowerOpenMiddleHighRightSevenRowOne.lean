import LowScale68SecondaryLaterDeepLowerOpenMiddleHighLeftSevenRowOne
import LowScale68SecondaryLaterDeepFiveRadiusTerminalEqualityFaceAlgebra

/-! # Row-one closure for the strict right seven wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighRightSevenRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def fiveRadiusRightSevenRowOneTail68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  fiveRadiusTerminalEqualityRowOneTail68 gamma epsilon A B c d e +
    zeta • ((1 / 3 : k) • (derivative A * B) + derivative d)

theorem fiveRadiusReducedRowOnePolynomial68_rightSevenSplit
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e =
      fiveRadiusTerminalEqualityRowOneCore68 A B c +
        fiveRadiusRightSevenRowOneTail68 gamma epsilon zeta A B c d e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusTerminalEqualityRowOneCore68,
    fiveRadiusTerminalEqualityRowOneTail68,
    fiveRadiusRightSevenRowOneTail68]
  module

set_option maxHeartbeats 7000000 in
theorem fiveRadiusRightSevenRowOneTail68_degree_lt_of_laterDeepLowerOpen
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n) (habove : 7 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusRightSevenRowOneTail68
      gamma epsilon zeta A B c d e).natDegree < 5 * n - 1 := by
  let idx := 5 * n - 1
  have hAd2 : (derivative (A * d ^ 2)).natDegree < idx := by
    have hp : (A * d ^ 2).natDegree ≤ 12 * n - 2 * h := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (A * d ^ 2)
    dsimp [idx]
    omega
  have hBcd : (derivative (B * c * d)).natDegree < idx := by
    have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c * d)
    dsimp [idx]
    omega
  have hBpcd : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hB2e : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hee : (e * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hep : (derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB : (derivative A * B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdp : (derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  simp only [fiveRadiusRightSevenRowOneTail68,
    fiveRadiusTerminalEqualityRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
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
      (deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep))
    (deepGap_natDegree_smul_lt68 zeta
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (1 / 3 : k) hApB) hdp))

set_option maxHeartbeats 7000000 in
theorem fiveRadiusTerminalEqualityRowOneCore68_coeff_of_rightSeven
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusTerminalEqualityRowOneCore68 A B c).coeff (5 * n - 1) =
      (-4 / 27 : k) *
        ((-2 : k) * ((5 * n : ℕ) : k) *
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
              c.coeff (4 * n - g) +
          (6 : k) * ((4 * n - g : ℕ) : k) *
            c.coeff (4 * n - g) ^ 3) := by
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hB
  have hB2 : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (2 * (3 * n - g)) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + 2 * (3 * n - g) + (4 * n - g) =
      5 * n := by omega
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
  simp only [fiveRadiusTerminalEqualityRowOneCore68, coeff_smul,
    coeff_add, smul_eq_mul, hAB2c', hc3]
  ring

set_option maxHeartbeats 4000000 in
theorem fiveRadiusTerminalEqualityRowOneCore68_coeff_rightSeven_ne_zero
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hc : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (fiveRadiusTerminalEqualityRowOneCore68 A B c).coeff (5 * n - 1) ≠ 0 := by
  rw [fiveRadiusTerminalEqualityRowOneCore68_coeff_of_rightSeven
    A B c n g hn hg hwall hA hB hcdeg]
  have hN : 5 * n = 3 * (4 * n - g) := by omega
  have hfactor : (-32 / 9 : k) * (((4 * n - g : ℕ) : k)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  intro hz
  rw [hN] at hz
  push_cast at hz
  have hzero : (-32 / 9 : k) * (((4 * n - g : ℕ) : k)) *
      c.coeff (4 * n - g) ^ 3 = 0 := by
    linear_combination hz -
      (8 / 9 : k) * (((4 * n - g : ℕ) : k)) *
        c.coeff (4 * n - g) * hdisc
  exact (pow_ne_zero 3 hc) ((mul_eq_zero.mp hzero).resolve_left hfactor)

set_option maxHeartbeats 10000000 in
theorem laterDeepLowerOpenMiddle_rightSeven_reducedRowOne_impossible68
    (alpha gamma epsilon zeta eta i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n) (habove : 7 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta A B c
          ((1 / 3 : k) • (A * B) + d) e = 0) : False := by
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon zeta eta i3 A B c d e hi3 hrow
  have htail := fiveRadiusRightSevenRowOneTail68_degree_lt_of_laterDeepLowerOpen
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hopen hwall habove
    hA hB hc hd he
  have hcore := fiveRadiusTerminalEqualityRowOneCore68_coeff_rightSeven_ne_zero
    A B c n g hn hg hwall hA hB hc hc0 hdisc
  have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hreduced
  rw [fiveRadiusReducedRowOnePolynomial68_rightSevenSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, coeff_zero] at hz
  exact hcore hz

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightSeven_impossible68
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
      3 * g = 7 * n ∧ 7 * n < 2 * h) : False := by
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
  change 3 * g = 7 * n ∧ 7 * n < 2 * h at hseven
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
  obtain ⟨i3, hi3⟩ := hsys.firstThree
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
  exact laterDeepLowerOpenMiddle_rightSeven_reducedRowOne_impossible68
    alpha gamma epsilon zeta eta i3 Ae Be ce d ee n g h hn hg
    ordinary.2.2.1 hmiddle hopen hseven.1 hseven.2 hA secondary.2.1
    secondary.2.2.1 ordinary.2.2.2.1 ordinary.2.2.2.2.1
    ordinary.2.2.2.2.2.2.1 ordinary.2.2.2.2.2.2.2.2.2 hi3c hrow

#print axioms fiveRadiusReducedRowOnePolynomial68_rightSevenSplit
#print axioms fiveRadiusRightSevenRowOneTail68_degree_lt_of_laterDeepLowerOpen
#print axioms fiveRadiusTerminalEqualityRowOneCore68_coeff_of_rightSeven
#print axioms fiveRadiusTerminalEqualityRowOneCore68_coeff_rightSeven_ne_zero
#print axioms laterDeepLowerOpenMiddle_rightSeven_reducedRowOne_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightSeven_impossible68

end LaterDeepLowerOpenMiddleHighRightSevenRowOne68

end Max11DegreeRoutes
