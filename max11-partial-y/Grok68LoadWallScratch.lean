import LowScale68SecondaryLaterDeepFiveToSixEarliestWall

/-! # Offset-30 I4 load wall at `n=30`, `g=90`

The five-to-six stride descent isolates a unique arithmetic wall where
`9n-2g-30=2n`, so the `zeta*A` load ties the residual I4 face.  Off this
wall the same coefficient lies strictly above every old-weight load and
kills both translated defects at displacement `30`.  This file extracts
the tied coefficient exactly.

Degree dictionary on the wall, in expanded coordinates: `deg A=60`,
`B,c,d` constant, `deg e≤60`.  The `C` top at index `30` is off the
expansion lattice.  I4 at index `60` is therefore
`(8/3)*B_0*e_60+zeta*A_60=0`.  The companion live I3 coefficient is
`(-8/9)*A_60*B_0*d_0+(8/3)*c_0*e_60+4*gamma*e_60=0`.  Two-case
comparison of `e_60` against zero then yields either
`e_60=zeta=d_0=0`, or a nonzero `e_60` that determines `zeta` from I4
and a linear relation among `d_0,c_0,gamma` from I3.

The committed linear-model endgame excludes the wall, so the residual
is empty.  The identities above are the exact I4-tie bookkeeping that
the large-radius cutoff had omitted.

Exact gain: I4 identity with the `zeta*A` load; live I3 identity; two-case
`e_60` dictionary; source-facing `False`.
Next unused row: none on this wall.
Residual: empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixEarliestLoadWallI4Tie68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall arithmetic -/

/-- Index dictionary at the unique earliest I4 load wall. -/
theorem fiveToSix_earliestWall_index_arith68
    (n g : ℕ) (hwall : n = 30 ∧ g = 90) :
    3 * n - g = 0 ∧ 4 * n - g = 30 ∧ 5 * n - g = 60 ∧ 6 * n - g = 90 ∧
      5 * n - g - 30 = 30 ∧ 6 * n - g - 30 = 60 ∧
      9 * n - 2 * g = 90 ∧ 9 * n - 2 * g - 30 = 60 ∧
      10 * n - 2 * g = 120 ∧ 10 * n - 2 * g - 30 = 90 ∧
      2 * n = 60 ∧ 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧ 3 * n < 2 * g := by
  omega

/-! ## Exact I4 coefficient, including the `zeta*A` load -/

/-- Residual quartic coefficient at the tied index `60`, before the
expansion lattice kills `c_30*d_30`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_earliestWall68
    (B c d e : k[X])
    (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 30)
    (hd : d.natDegree ≤ 30)
    (he : e.natDegree ≤ 60) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff 60 =
      (8 / 3 : k) *
        (B.coeff 0 * e.coeff 60 + c.coeff 30 * d.coeff 30) := by
  have hB3 : (B ^ 3).natDegree < 60 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e 0 60 hB he
  have hcd := coeff_mul_at_bounds68 c d 30 30 hc hd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Literal I4 coefficient at the tie: residual face plus `zeta*A`.
The `epsilon*B` and `gamma*d` loads lie strictly below index `60`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_earliestWall68
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 60)
    (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 30)
    (hd : d.natDegree ≤ 30)
    (he : e.natDegree ≤ 60) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 60 =
      (8 / 3 : k) *
          (B.coeff 0 * e.coeff 60 + c.coeff 30 * d.coeff 30) +
        zeta * A.coeff 60 := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_earliestWall68
      B c d e hB hc hd he]
  have hloadB : ((2 * epsilon : k) • B).natDegree < 60 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 60 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  simp only [coeff_smul, smul_eq_mul]
  ring

/-- After the expansion lattice forces `c` and `d` constant, the `cd`
summand drops and I4 is exactly the `B e` / `zeta A` tie. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_earliestWall_constants68
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 60)
    (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 0)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 60) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 60 =
      (8 / 3 : k) * (B.coeff 0 * e.coeff 60) + zeta * A.coeff 60 := by
  have hc30 : c.natDegree ≤ 30 := by omega
  have hd30 : d.natDegree ≤ 30 := by omega
  have hfull :=
    cubicFirstIntegralFourPolynomial68_coeff_earliestWall68
      gamma epsilon zeta A B c d e hA hB hc30 hd30 he
  have hc0 : c.coeff 30 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hfull, hc0, zero_mul, add_zero]

/-! ## Exact live I3 coefficient after the constants -/

/-- Residual cubic coefficient at index `60` once `B,c,d` are constant. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_earliestWall68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 60)
    (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 0)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 60) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff 60 =
      (8 / 9 : k) *
        (-(A.coeff 60 * B.coeff 0 * d.coeff 0) +
          3 * c.coeff 0 * e.coeff 60) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d 60 0 0 hA hB hd
  have hB2c : (B ^ 2 * c).natDegree < 60 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e 0 60 hc he
  have hd2 : (d ^ 2).natDegree < 60 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal I3 coefficient at the live wall index.  The `zeta*B`,
`epsilon*c`, and `gamma*B^2` loads are constant; only `gamma*e` can
reach degree `60`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_earliestWall68
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 60)
    (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 0)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 60) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 60 =
      (8 / 9 : k) *
          (-(A.coeff 60 * B.coeff 0 * d.coeff 0) +
            3 * c.coeff 0 * e.coeff 60) +
        (4 * gamma : k) * e.coeff 60 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_earliestWall68
      A B c d e hA hB hc hd he]
  have hloadB : (zeta • B).natDegree < 60 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree < 60 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 60 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  simp only [coeff_smul, smul_eq_mul]
  ring

/-! ## Two-case `e_60` dictionary -/

/-- From the two live invariant coefficients: either the offset-30 `e`
edge vanishes and forces `zeta=d_0=0`, or it survives and I4/I3 become
linear relations for `zeta` and `d_0`. -/
theorem fiveToSix_earliestWall_i4_tie_two_case68
    (gamma zeta : k) (A B c d e : k[X])
    (ha : A.coeff 60 ≠ 0)
    (hb : B.coeff 0 ≠ 0)
    (hi4 : (8 / 3 : k) * (B.coeff 0 * e.coeff 60) +
      zeta * A.coeff 60 = 0)
    (hi3 : (8 / 9 : k) *
          (-(A.coeff 60 * B.coeff 0 * d.coeff 0) +
            3 * c.coeff 0 * e.coeff 60) +
        (4 * gamma : k) * e.coeff 60 = 0) :
    (e.coeff 60 = 0 ∧ zeta = 0 ∧ d.coeff 0 = 0) ∨
      (e.coeff 60 ≠ 0 ∧
        zeta * A.coeff 60 =
          -((8 / 3 : k) * (B.coeff 0 * e.coeff 60)) ∧
        (8 / 9 : k) * (-(A.coeff 60 * B.coeff 0 * d.coeff 0)) +
            e.coeff 60 * ((8 / 3 : k) * c.coeff 0 + (4 * gamma : k)) =
          0) := by
  by_cases he0 : e.coeff 60 = 0
  · left
    have hzeta : zeta = 0 := by
      have h : zeta * A.coeff 60 = 0 := by
        rw [he0] at hi4
        ring_nf at hi4
        exact hi4
      exact (mul_eq_zero.mp h).resolve_right ha
    have hd0 : d.coeff 0 = 0 := by
      have h : (8 / 9 : k) * (-(A.coeff 60 * B.coeff 0 * d.coeff 0)) = 0 := by
        rw [he0] at hi3
        ring_nf at hi3 ⊢
        exact hi3
      have hneg : -(A.coeff 60 * B.coeff 0 * d.coeff 0) = 0 :=
        (mul_eq_zero.mp h).resolve_left (by norm_num)
      have hprod : A.coeff 60 * B.coeff 0 * d.coeff 0 = 0 :=
        neg_eq_zero.mp hneg
      exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero ha hb)
    exact ⟨he0, hzeta, hd0⟩
  · right
    refine ⟨he0, ?_, ?_⟩
    · linear_combination hi4
    · convert hi3 using 1
      ring

/-! ## Source-facing packet -/

/-- Exact expanded degree dictionary on the wall. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_degrees68
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
      n = 30 ∧ g = 90) :
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
    n = 30 ∧ g = 90 ∧
      Ae.natDegree = 60 ∧ Be.natDegree = 0 ∧ ce.natDegree = 0 ∧
      d.natDegree = 0 ∧ ee.natDegree ≤ 60 ∧
      Ae.coeff 60 ≠ 0 ∧ Be.coeff 0 ≠ 0 := by
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
  let c : k[X] := cubicCDefectPolynomial68 A C0
  let d0 : k[X] := secondaryDDefectPolynomial68 A B D
  let e0 : k[X] := cubicEDefectPolynomial68 A C0 E
  change n = 30 ∧ g = 90 at hwall
  change n = 30 ∧ g = 90 ∧
    Ae.natDegree = 60 ∧ Be.natDegree = 0 ∧ ce.natDegree = 0 ∧
    d.natDegree = 0 ∧ ee.natDegree ≤ 60 ∧
    Ae.coeff 60 ≠ 0 ∧ Be.coeff 0 ≠ 0
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := by omega
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hdesc :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirtyDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 30 ∣ n ∧ 30 ∣ g ∧ _ ∧
    (secondaryDDefectPolynomial68 Ae Be De).natDegree ≤
      5 * n - g - 30 ∧ ee.natDegree ≤ 6 * n - g - 30 at hdesc
  have hAdeg : Ae.natDegree = 60 := by
    have hAle := data.hA
    rw [hwall.1] at hAle
    norm_num at hAle
    have ha60 : Ae.coeff 60 ≠ 0 := by
      simpa only [hwall.1] using data.ha
    exact le_antisymm hAle (le_natDegree_of_ne_zero ha60)
  have ha : Ae.coeff 60 ≠ 0 := by
    simpa only [hwall.1] using data.ha
  have hBdeg : Be.natDegree = 0 := by
    have h := data.hB
    simp only [hwall.1, hwall.2] at h
    have : Be.natDegree ≤ 0 := by simpa using h
    omega
  have hcexpand : ce = expand k 60 c := by
    simpa only [ce, Ae, Ce, c] using expand_cubicCDefectPolynomial68 60 A C0
  have hcdeg : ce.natDegree = 0 := by
    have h := data.hc
    simp only [hwall.1, hwall.2] at h
    rw [hcexpand, natDegree_expand] at h ⊢
    omega
  have hdexpand : d = expand k 60 d0 := by
    simpa only [d, Ae, Be, De, d0] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have hddeg : d.natDegree = 0 := by
    have h := hdesc.2.2.2.1
    simp only [hwall.1, hwall.2] at h
    change d.natDegree ≤ 30 at h
    rw [hdexpand, natDegree_expand] at h ⊢
    omega
  have hedeg : ee.natDegree ≤ 60 := by
    have h := hdesc.2.2.2.2
    simp only [hwall.1, hwall.2] at h
    simpa using h
  have htop :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 at htop
  have hc30 : ce.coeff (4 * n - g) = 0 := by
    rw [hwall.1, hwall.2]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hb : Be.coeff 0 ≠ 0 := by
    have hb' : Be.coeff (3 * n - g) ≠ 0 :=
      htop.resolve_right (fun hcne => hcne hc30)
    simpa only [hwall.1, hwall.2] using hb'
  exact ⟨hwall.1, hwall.2, hAdeg, hBdeg, hcdeg, hddeg, hedeg, ha, hb⟩

/-- Source-facing I4 tie and live I3 coefficient on the wall. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_i4_tie68
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
      n = 30 ∧ g = 90) :
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
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧
      (8 / 3 : k) * (Be.coeff 0 * ee.coeff 60) +
        zeta * Ae.coeff 60 = 0 ∧
      (8 / 9 : k) *
          (-(Ae.coeff 60 * Be.coeff 0 * d.coeff 0) +
            3 * ce.coeff 0 * ee.coeff 60) +
        (4 * gamma : k) * ee.coeff 60 = 0 := by
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
  change n = 30 ∧ g = 90 at hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧
    (8 / 3 : k) * (Be.coeff 0 * ee.coeff 60) +
      zeta * Ae.coeff 60 = 0 ∧
    (8 / 9 : k) *
        (-(Ae.coeff 60 * Be.coeff 0 * d.coeff 0) +
          3 * ce.coeff 0 * ee.coeff 60) +
      (4 * gamma : k) * ee.coeff 60 = 0
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := by omega
  have hdeg :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_degrees68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change n = 30 ∧ g = 90 ∧
    Ae.natDegree = 60 ∧ Be.natDegree = 0 ∧ ce.natDegree = 0 ∧
    d.natDegree = 0 ∧ ee.natDegree ≤ 60 ∧
    Ae.coeff 60 ≠ 0 ∧ Be.coeff 0 ≠ 0 at hdeg
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
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hi4raw⟩ := data.invariant
  have hI4 := hi4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4
  have hA60 : Ae.natDegree ≤ 60 := by omega
  have hB0 : Be.natDegree ≤ 0 := by omega
  have hc0 : ce.natDegree ≤ 0 := by omega
  have hd0 : d.natDegree ≤ 0 := by omega
  have he60 : ee.natDegree ≤ 60 := hdeg.2.2.2.2.2.2.1
  have hi4coeff := congrArg (fun p : k[X] => p.coeff 60) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_earliestWall_constants68
    gamma epsilon zeta Ae Be ce d ee hA60 hB0 hc0 hd0 he60] at hi4coeff
  have htarget : (60 : ℕ) ≠ 0 := by norm_num
  simp [coeff_C, htarget] at hi4coeff
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  rw [hDrec] at hi3e
  have hi3coeff := congrArg (fun p : k[X] => p.coeff 60) hi3e
  rw [cubicFirstIntegralThreePolynomial68_coeff_earliestWall68
    gamma epsilon zeta Ae Be ce d ee hA60 hB0 hc0 hd0 he60] at hi3coeff
  simp [coeff_C, htarget] at hi3coeff
  exact ⟨hl, hbeta, hdelta, hi4coeff, hi3coeff⟩

/-- Two-case dictionary transported to the canonical expanded source. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_two_case68
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
      n = 30 ∧ g = 90) :
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
    (ee.coeff 60 = 0 ∧ zeta = 0 ∧ d.coeff 0 = 0) ∨
      (ee.coeff 60 ≠ 0 ∧
        zeta * Ae.coeff 60 =
          -((8 / 3 : k) * (Be.coeff 0 * ee.coeff 60)) ∧
        (8 / 9 : k) * (-(Ae.coeff 60 * Be.coeff 0 * d.coeff 0)) +
            ee.coeff 60 * ((8 / 3 : k) * ce.coeff 0 + (4 * gamma : k)) =
          0) := by
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
  change n = 30 ∧ g = 90 at hwall
  change (ee.coeff 60 = 0 ∧ zeta = 0 ∧ d.coeff 0 = 0) ∨
    (ee.coeff 60 ≠ 0 ∧
      zeta * Ae.coeff 60 =
        -((8 / 3 : k) * (Be.coeff 0 * ee.coeff 60)) ∧
      (8 / 9 : k) * (-(Ae.coeff 60 * Be.coeff 0 * d.coeff 0)) +
          ee.coeff 60 * ((8 / 3 : k) * ce.coeff 0 + (4 * gamma : k)) =
        0)
  have hdeg :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_degrees68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change n = 30 ∧ g = 90 ∧
    Ae.natDegree = 60 ∧ Be.natDegree = 0 ∧ ce.natDegree = 0 ∧
    d.natDegree = 0 ∧ ee.natDegree ≤ 60 ∧
    Ae.coeff 60 ≠ 0 ∧ Be.coeff 0 ≠ 0 at hdeg
  have ha : Ae.coeff 60 ≠ 0 := hdeg.2.2.2.2.2.2.2.1
  have hb : Be.coeff 0 ≠ 0 := hdeg.2.2.2.2.2.2.2.2
  have htie :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_i4_tie68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧
    (8 / 3 : k) * (Be.coeff 0 * ee.coeff 60) +
      zeta * Ae.coeff 60 = 0 ∧
    (8 / 9 : k) *
        (-(Ae.coeff 60 * Be.coeff 0 * d.coeff 0) +
          3 * ce.coeff 0 * ee.coeff 60) +
      (4 * gamma : k) * ee.coeff 60 = 0 at htie
  exact fiveToSix_earliestWall_i4_tie_two_case68
    gamma zeta Ae Be ce d ee ha hb htie.2.2.2.1 htie.2.2.2.2

/-- The wall is empty.  The linear-model endgame consumes both sides of
the I4-tie dictionary. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_loadWall_impossible68
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
      n = 30 ∧ g = 90) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hwall

end FiveToSixEarliestLoadWallI4Tie68

#print axioms fiveToSix_earliestWall_index_arith68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_earliestWall68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_earliestWall68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_earliestWall_constants68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_earliestWall68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_earliestWall68
#print axioms fiveToSix_earliestWall_i4_tie_two_case68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_degrees68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_i4_tie68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_two_case68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_loadWall_impossible68

end Max11DegreeRoutes
