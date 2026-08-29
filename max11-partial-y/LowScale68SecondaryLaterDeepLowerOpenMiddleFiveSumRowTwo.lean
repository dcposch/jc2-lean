import LowScale68SecondaryLaterDeepLowerOpenMiddleSevenSumRowTwo

/-! # Row two deletes the exceptional `delta` load on `g+h=5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleFiveSumRowTwo68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) :
    secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  module

/-- Primitive of the extra row-two term left by the `delta` part of I4. -/
def laterDeepFiveSumDeltaPrimitive68 (A B c e : k[X]) : k[X] :=
  (5 / 72 : k) • A ^ 3 + (1 / 2 : k) • (A * c) +
    (3 : k) • e - (3 / 4 : k) • B ^ 2

/-- I4-reduced row two without assuming `delta=0`. -/
def laterDeepFiveSumReducedRowTwoPolynomial68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X]) : k[X] :=
  fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e +
    delta • derivative (laterDeepFiveSumDeltaPrimitive68 A B c e)

set_option maxHeartbeats 16000000 in
theorem polynomialLaterDeepFiveSumReducedRowTwo68
    (alpha gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e =
      laterDeepFiveSumReducedRowTwoPolynomial68
        gamma delta epsilon zeta i4 A B c d e := by
  let Q := residualIncidenceQ68 B c d e
  have hi4' := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect,
    secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta]
      at hi4'
  change (8 / 3 : k) • Q +
      (zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d) = C i4 at hi4'
  have hQ : Q = (3 / 8 : k) •
      (C i4 - (zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d)) := by
    calc
      Q = (3 / 8 : k) • ((8 / 3 : k) • Q) := by
        rw [smul_smul]
        norm_num
      _ = (3 / 8 : k) •
          (C i4 - (zeta • A + (2 * epsilon : k) • B +
            (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
            (4 * gamma : k) • d)) := by
        rw [eq_sub_iff_add_eq.mpr hi4']
  rw [residualRowTwo_eq_inner68]
  simp only [residualRowTwoInner68]
  have hQ' : residualIncidenceQ68 B c d e = (3 / 8 : k) •
      (C i4 - (zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d)) := by
    simpa only [Q] using hQ
  rw [hQ']
  simp only [laterDeepFiveSumReducedRowTwoPolynomial68,
    laterDeepFiveSumDeltaPrimitive68, fiveRadiusReducedRowTwoPolynomial68,
    cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_smul, derivative_C]
  simp only [Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast,
    map_one, zero_mul, mul_zero, add_zero, zero_add]
  ring

theorem laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
    (alpha gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0 := by
  rw [← polynomialLaterDeepFiveSumReducedRowTwo68
    alpha gamma delta epsilon zeta eta i4 A B c d e hi4]
  exact hrow

set_option maxHeartbeats 4000000 in
theorem fiveRadiusReducedRowTwoPolynomial68_degree_lt_middleFiveSum
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : g + h = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e).natDegree < 6 * n - 1 := by
  let bound := 6 * n - 1
  have h1 : (A * B ^ 2 * derivative B).natDegree < bound := by
    dsimp [bound]; compute_degree; omega
  have h2 : (derivative A * B ^ 3).natDegree < bound := by
    dsimp [bound]; compute_degree; omega
  have h3 : (derivative (B ^ 2 * d)).natDegree < bound := by
    have hp : (B ^ 2 * d).natDegree ≤
        (6 * n - 2 * g) + (5 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B ^ 2 * d)
    dsimp [bound]
    omega
  have h4 : (derivative (B * c ^ 2)).natDegree < bound := by
    have hp : (B * c ^ 2).natDegree ≤
        (3 * n - g) + (8 * n - 2 * g) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c ^ 2)
    dsimp [bound]
    omega
  have h5 : (derivative (d * e)).natDegree < bound := by
    have hp : (d * e).natDegree ≤
        (5 * n - h) + (6 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (d * e)
    dsimp [bound]
    omega
  have h6 : (derivative A).natDegree < bound := by
    dsimp [bound]; compute_degree; omega
  have h7 : (derivative (B * c)).natDegree < bound := by
    have hp : (B * c).natDegree ≤
        (3 * n - g) + (4 * n - g) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c)
    dsimp [bound]
    omega
  have h8 : (derivative d).natDegree < bound := by
    dsimp [bound]; compute_degree; omega
  have h9 : (derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree < bound := by
    have hp : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
      compute_degree
      omega
    have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
    dsimp [bound]
    omega
  have h1s := deepGap_natDegree_smul_lt68 (-2 : k) h1
  have h2s := deepGap_natDegree_smul_lt68 (-2 / 3 : k) h2
  have h3s := deepGap_natDegree_smul_lt68 (6 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (6 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (-18 : k) h5
  have hcore := deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt (deepGap_natDegree_add_lt h1s h2s) h3s) h4s) h5s
  have hcores := deepGap_natDegree_smul_lt68 (-4 / 27 : k) hcore
  have h6s := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) h6
  have h7s := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) h7
  have h8s := deepGap_natDegree_smul_lt68 (2 * epsilon : k) h8
  have h9s := deepGap_natDegree_smul_lt68 zeta h9
  simp only [fiveRadiusReducedRowTwoPolynomial68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_sub_lt hcores h6s) h7s) h8s) h9s

set_option maxHeartbeats 3000000 in
theorem laterDeepFiveSumDeltaPrimitive68_derivative_coeff_sixRadius
    (A B c e : k[X]) (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hgh : g < h)
    (hwall : g + h = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (derivative (laterDeepFiveSumDeltaPrimitive68 A B c e)).coeff
        (6 * n - 1) =
      (5 / 12 : k) * (n : k) * A.coeff (2 * n) ^ 3 := by
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hiA : 3 * (2 * n) = 6 * n := by omega
  rw [hiA] at hA3
  let rest := (1 / 2 : k) • (A * c) + (3 : k) • e -
    (3 / 4 : k) • B ^ 2
  have hrest : rest.natDegree < 6 * n := by
    dsimp [rest]
    compute_degree
    omega
  have htop : (laterDeepFiveSumDeltaPrimitive68 A B c e).coeff (6 * n) =
      (5 / 72 : k) * A.coeff (2 * n) ^ 3 := by
    have heq : laterDeepFiveSumDeltaPrimitive68 A B c e =
        (5 / 72 : k) • A ^ 3 + rest := by
      simp only [laterDeepFiveSumDeltaPrimitive68, rest]
      module
    rw [heq, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero]
  have hder := coeff_derivative_at_bound68
    (laterDeepFiveSumDeltaPrimitive68 A B c e) (6 * n) (by omega)
  rw [htop] at hder
  rw [show 6 * n - 1 = (6 * n) - 1 by rfl, hder]
  push_cast
  ring

theorem laterDeepFiveSumReducedRowTwo_forces_delta68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : g + h = 5 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0) :
    delta = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hrow
  rw [laterDeepFiveSumReducedRowTwoPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (fiveRadiusReducedRowTwoPolynomial68_degree_lt_middleFiveSum
        gamma epsilon zeta i4 A B c d e n g h hn hgh hh hopen hwall
        hA hB hc hd he),
    coeff_smul, smul_eq_mul,
    laterDeepFiveSumDeltaPrimitive68_derivative_coeff_sixRadius
      A B c e n g h hn hg hgh hwall hA hB hc he,
    coeff_zero, zero_add] at hcoeff
  have hright : (5 / 12 : k) * (n : k) * A.coeff (2 * n) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'))
      (pow_ne_zero 3 ha)
  exact (mul_eq_zero.mp hcoeff).resolve_right hright

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumOrdinary68
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
      g + h = 5 * n) :
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
    delta = 0 ∧
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
  change g + h = 5 * n at hwall
  have selected :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧ _
    at selected
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
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, selected.1, selected.2.1] at hi4e
    exact hi4e
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, selected.1, selected.2.1] at hi3e
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
  have hrow := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [selected.1, selected.2.1] at hrow
  have hred := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
  have hdelta := laterDeepFiveSumReducedRowTwo_forces_delta68
    gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hg selected.2.2.1
    hmiddle hopen hwall ha hA secondary.2.1 secondary.2.2.1
    selected.2.2.2.1 selected.2.2.2.2.1 hred
  have hi4d := hi4c
  rw [hdelta] at hi4d
  have hi3d := hi3c
  rw [hdelta] at hi3d
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
      gamma epsilon zeta Ae Be ce d ee n g h hn hopen (by omega) hA
      secondary.2.1 selected.2.2.2.1
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
      gamma epsilon zeta i4 i3 Ae Be ce d ee n g h hn hg selected.2.2.1
      hmiddle hopen hload hA secondary.2.1 secondary.2.2.1
      selected.2.2.2.1 selected.2.2.2.2.1 hi4d hi3d
  have classified := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) ha selected.2.2.2.2.2.1
    selected.2.2.2.2.2.2.1 face
  exact ⟨hdelta, classified.1, classified.2.1, classified.2.2.1,
    classified.2.2.2.1, classified.2.2.2.2⟩

#print axioms polynomialLaterDeepFiveSumReducedRowTwo68
#print axioms laterDeepFiveSumDeltaPrimitive68_derivative_coeff_sixRadius
#print axioms laterDeepFiveSumReducedRowTwo_forces_delta68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumOrdinary68

end LaterDeepLowerOpenMiddleFiveSumRowTwo68

end Max11DegreeRoutes
