import LowScale68SecondaryLaterDeepFiveToSixRowOne

/-! # The first lower residual coefficient in the five-to-six chamber

After translating `D=A*B/3+d`, the first strict lower coefficients of `d`
and `e` occur at gaps `g+1`.  The two constant first integrals give the
usual residual incidence packet there, including the endpoint `2g=6n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixLowerCoefficient68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 18000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The relation `A_top B_top = 3 D_top` lowers the translated `D` defect
throughout the five-to-six window. -/
theorem secondaryDDefectPolynomial68_degree_lt_fiveToSix
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n := by omega
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by omega
  have hdegree : (secondaryDDefectPolynomial68 A B D).natDegree ≤
      5 * n - g := by
    simp only [secondaryDDefectPolynomial68]
    compute_degree
    omega
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  rw [hindex] at hAB
  have hcoeff : (secondaryDDefectPolynomial68 A B D).coeff
      (5 * n - g) = 0 := by
    simp only [secondaryDDefectPolynomial68, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hAB]
    linear_combination (-1 / 3 : k) * hface
  exact natDegree_lt_of_le_of_coeff_eq_zero68 _ (5 * n - g)
    (by omega) hdegree hcoeff

/-- Both translated odd residual directions drop at least one coefficient. -/
theorem firstSecondaryResidualDegreeDrops68_fiveToSix
    (A B D e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  refine ⟨secondaryDDefectPolynomial68_degree_lt_fiveToSix
    A B D n g hn hwindow hA hB hD hface, ?_⟩
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (by omega) he hetop

/-- Exact quartic invariant in translated residual coordinates after
`l=beta=delta=0`. -/
theorem cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantFourPolynomial68 B c d e +
        zeta • A + (2 * epsilon : k) • B + (4 * gamma : k) • d := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates]
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero]
  module

/-- Exact cubic invariant in the same residual coordinates. -/
theorem cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantThreePolynomial68 A B c d e +
        zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
          (2 / 3 * gamma : k) • B ^ 2 := by
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates]
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero]
  module

/-- The homogeneous quartic residual coefficient at the first strict lower
gap `g+1`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_gap_succ_fiveToSix
    (B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - 1) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 1) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 1)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - 1) hB he
  have hBei : (3 * n - g) + (6 * n - g - 1) =
      9 * n - 2 * g - 1 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - 1) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - 1) =
      9 * n - 2 * g - 1 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- The corresponding homogeneous cubic residual coefficient. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_gap_succ_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 2 * g - 1) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 1)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 1)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g - 1) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g - 1) =
      10 * n - 2 * g - 1 := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - g - 1) hc he
  have hcei : (4 * n - g) + (6 * n - g - 1) =
      10 * n - 2 * g - 1 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 2 * g - 1 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal quartic coefficient: every remaining old-weight load lies below
the first strict residual edge. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_gap_succ_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - 1) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 1) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 1)) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_gap_succ_fiveToSix
      B c d e n g hn hwindow hB hc hd he]
  have hloadA : (zeta • A).natDegree < 9 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - 1 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadA,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

/-- Literal cubic coefficient at the same first lower residual gap. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_gap_succ_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - 1) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 1)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 1)) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_gap_succ_fiveToSix
      A B c d e n g hn hwindow hA hB hc hd he]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - 1 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- The two literal constant invariants give the exact residual incidence
face at the first lower coefficient. -/
theorem polynomialSecondaryResidualGapSuccFace68_fiveToSix
    (gamma epsilon zeta i4 i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - g - 1))
      (e.coeff (6 * n - g - 1)) := by
  constructor
  · have hz := congrArg
      (fun p : k[X] => p.coeff (9 * n - 2 * g - 1)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_gap_succ_fiveToSix
      gamma epsilon zeta A B c d e n g hn hn2 hwindow hA hB hc hd he] at hz
    have hj : 9 * n - 2 * g - 1 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg
      (fun p : k[X] => p.coeff (10 * n - 2 * g - 1)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_gap_succ_fiveToSix
      gamma epsilon zeta A B c d e n g hn hwindow hA hB hc hd he] at hz
    have hj : 10 * n - 2 * g - 1 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-- Combining the old attainment split with the first lower residual face:
either both new edge coefficients vanish, or all four incidence directions
are nonzero and satisfy the discriminant equation. -/
theorem firstSecondary_mainFamily_gapSucc_classify68
    (a b c dTop eTop d e : k) (ha : a ≠ 0)
    (hold : (b ≠ 0 ∧ dTop ≠ 0) ∨
      (b = 0 ∧ dTop = 0 ∧ c ≠ 0))
    (hface : SecondaryResidualBetweenFace68 a b c d e) :
    (d = 0 ∧ e = 0) ∨
      (b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 ∧
        a * b ^ 2 + 3 * c ^ 2 = 0) := by
  rcases hold with hnonzero | hczero
  · by_cases hde : d = 0 ∧ e = 0
    · exact Or.inl hde
    · right
      have hattained : d ≠ 0 ∨ e ≠ 0 := by tauto
      exact secondaryResidualBetweenFace68_classify_of_support
        a b c d e ha (Or.inl hnonzero.1) hattained hface
  · left
    rcases hczero with ⟨hb0, _hdTop0, hc0⟩
    have hd0 : d = 0 := by
      have h := hface.four
      rw [hb0, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hc0
    have he0 : e = 0 := by
      have h := hface.three
      simp only [hb0, mul_zero, zero_mul, neg_zero, zero_add] at h
      have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
      exact (mul_eq_zero.mp hce).resolve_left hc0
    exact ⟨hd0, he0⟩

set_option maxHeartbeats 30000000 in
/-- Source-facing first lower residual packet in `5n < 2g ≤ 6n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_gapSuccPacket68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
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
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
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
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - 1))
        (ee.coeff (6 * n - g - 1)) ∧
      ((d.coeff (5 * n - g - 1) = 0 ∧
          ee.coeff (6 * n - g - 1) = 0) ∨
        (Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - g - 1) ≠ 0 ∧
          ee.coeff (6 * n - g - 1) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0)) := by
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
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - 1))
      (ee.coeff (6 * n - g - 1)) ∧ _
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hmain
  have hdrops := firstSecondaryResidualDegreeDrops68_fiveToSix
    Ae Be De ee n g data.hn hwindow data.hA data.hB data.hD data.he
    hmain.2 hmain.1
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hd : d.natDegree ≤ 5 * n - g - 1 := by omega
  have he : ee.natDegree ≤ 6 * n - g - 1 := by omega
  have hnTen : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E data.hn
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
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
  have hface := polynomialSecondaryResidualGapSuccFace68_fiveToSix
    gamma epsilon zeta i4 i3 Ae Be ce d ee n g data.hn (by omega) hwindow
    data.hA data.hB data.hc hd he hI4 hi3e
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
  refine ⟨hdrops.1, hdrops.2, hface, ?_⟩
  exact firstSecondary_mainFamily_gapSucc_classify68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 1))
    (ee.coeff (6 * n - g - 1)) data.ha hold hface

end LaterDeepFiveToSixLowerCoefficient68

#print axioms secondaryDDefectPolynomial68_degree_lt_fiveToSix
#print axioms firstSecondaryResidualDegreeDrops68_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_gap_succ_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_gap_succ_fiveToSix
#print axioms polynomialSecondaryResidualGapSuccFace68_fiveToSix
#print axioms firstSecondary_mainFamily_gapSucc_classify68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_gapSuccPacket68

end Max11DegreeRoutes
