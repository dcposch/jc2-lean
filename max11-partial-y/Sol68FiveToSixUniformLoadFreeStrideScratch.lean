import Sol68ScaleZeroGlobalResidualScratch

/-! # Uniform load-free edge in the five-to-six chamber

The fixed offsets `60`, `90`, and `120` are instances of one coefficient
calculation.  At offset `s`, I4 is load-free exactly while
`s < 7n - 2g`; at equality the term `zeta*A_top` is the first load.  I3
remains ordinary throughout that range.  This file packages the resulting
source-facing edge classification and the expansion-lattice `60`-stride.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixUniformLoadFreeStride68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous I4 at an arbitrary positive offset before the first load. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_uniform_fiveToSix
    (B c d e : k[X]) (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - s) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s)) := by
  have hsg : s < g := by omega
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - s := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - s) hB he
  have hBei : (3 * n - g) + (6 * n - g - s) =
      9 * n - 2 * g - s := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - s) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - s) =
      9 * n - 2 * g - s := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Homogeneous I3 at the same arbitrary offset. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_uniform_fiveToSix
    (A B c d e : k[X]) (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 2 * g - s) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - s)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - s)) := by
  have hsg : s < g := by omega
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g - s) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g - s) =
      10 * n - 2 * g - s := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - s := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - g - s) hc he
  have hcei : (4 * n - g) + (6 * n - g - s) =
      10 * n - 2 * g - s := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 2 * g - s := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal I4 is ordinary on the full open interval before
`s = 7n-2g`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_uniform_loadFree_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - s) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s)) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_uniform_fiveToSix
      B c d e n g s hn hs hwindow hload hB hc hd he]
  have hloadA : (zeta • A).natDegree < 9 * n - 2 * g - s := by
    compute_degree
    omega
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - s := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - s := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadA,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

/-- Literal I3 stays ordinary throughout the I4 load-free interval. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_uniform_loadFree_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - s) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - s)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - s)) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_uniform_fiveToSix
      A B c d e n g s hn hs hwindow hload hA hB hc hd he]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - s := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - s := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - s := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - s := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- The two constant first integrals give the ordinary incidence face at
every positive offset strictly before the I4 load wall. -/
theorem polynomialSecondaryResidualUniformFace68_fiveToSix
    (gamma epsilon zeta i4 i3 : k) (A B c d e : k[X])
    (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - g - s))
      (e.coeff (6 * n - g - s)) := by
  constructor
  · have hz := congrArg
      (fun p : k[X] => p.coeff (9 * n - 2 * g - s)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_uniform_loadFree_fiveToSix
      gamma epsilon zeta A B c d e n g s hn hs hwindow hload
      hA hB hc hd he] at hz
    have hj : 9 * n - 2 * g - s ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg
      (fun p : k[X] => p.coeff (10 * n - 2 * g - s)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_uniform_loadFree_fiveToSix
      gamma epsilon zeta A B c d e n g s hn hs hwindow hload
      hA hB hc hd he] at hz
    have hj : 10 * n - 2 * g - s ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-- Source-facing uniform edge classification.  Its only alternatives are a
zero edge, which permits the next lattice stride, and the exact cusp
`a*b^2+3*c^2=0` with all four transverse directions nonzero. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hs : 0 < s)
    (hload :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      s < 7 * n - 2 * g)
    (hdrop :
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
      d.natDegree ≤ 5 * n - g - s ∧
        ee.natDegree ≤ 6 * n - g - s) :
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
    (d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0) ∨
      (Be.coeff (3 * n - g) ≠ 0 ∧
        ce.coeff (4 * n - g) ≠ 0 ∧
        d.coeff (5 * n - g - s) ≠ 0 ∧
        ee.coeff (6 * n - g - s) ≠ 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
          3 * ce.coeff (4 * n - g) ^ 2 = 0) := by
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
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change s < 7 * n - 2 * g at hload
  change d.natDegree ≤ 5 * n - g - s ∧
    ee.natDegree ≤ 6 * n - g - s at hdrop
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  rw [hdelta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4 hi3e
  have hface := polynomialSecondaryResidualUniformFace68_fiveToSix
    gamma epsilon zeta i4 i3 Ae Be ce d ee n g s data.hn hs hwindow hload
    data.hA data.hB data.hc hdrop.1 hdrop.2 hI4 hi3e
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hmain
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0) at hsecondary
  have hold := firstSecondary_mainFamily_attainment_split68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) data.ha hmain hsecondary.2.2.2.2.2
  exact firstSecondary_mainFamily_gapSucc_classify68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - s))
    (ee.coeff (6 * n - g - s)) data.ha hold hface

/-- If the cusp discriminant is nonzero, the uniform edge must be zero. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hs : 0 < s)
    (hload :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      s < 7 * n - 2 * g)
    (hdrop :
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
      d.natDegree ≤ 5 * n - g - s ∧
        ee.natDegree ≤ 6 * n - g - s)
    (hdisc :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 ≠ 0) :
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
    d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - s) = 0 := by
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
  change _ ≠ 0 at hdisc
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E s
      hterminal hsys hwindow hs hload hdrop
  change (_ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _ = 0) at hedge
  exact hedge.resolve_right (fun h => hdisc h.2.2.2.2)

/-- A zero coefficient advances a `60`-expanded polynomial by one complete
lattice stride, for either residue class of the ambient boundary. -/
theorem natDegree_expand_le_sub_next_sixty68
    (q : k[X]) (base offset : ℕ)
    (halign : 60 ∣ base - offset) (hnext : offset + 60 ≤ base)
    (hdeg : (expand k 60 q).natDegree ≤ base - offset)
    (hedge : (expand k 60 q).coeff (base - offset) = 0) :
    (expand k 60 q).natDegree ≤ base - (offset + 60) := by
  by_cases hq : expand k 60 q = 0
  · rw [hq, natDegree_zero]
    omega
  · have hlead :
        (expand k 60 q).coeff (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) q
        (expand k 60 q).natDegree hlead
    by_contra hnot
    have hlt : base - (offset + 60) < (expand k 60 q).natDegree := by omega
    obtain ⟨u, hu⟩ := halign
    obtain ⟨v, hv⟩ := hdiv
    have heq : (expand k 60 q).natDegree = base - offset := by omega
    exact hlead (by simpa only [heq] using hedge)

#print axioms secondaryResidualInvariantFourPolynomial68_coeff_uniform_fiveToSix
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_uniform_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_uniform_loadFree_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_uniform_loadFree_fiveToSix
#print axioms polynomialSecondaryResidualUniformFace68_fiveToSix
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge_zero68
#print axioms natDegree_expand_le_sub_next_sixty68

end FiveToSixUniformLoadFreeStride68

end Max11DegreeRoutes
