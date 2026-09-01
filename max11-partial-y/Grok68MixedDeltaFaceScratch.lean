import LowScale68SecondaryLaterDeepFiveRadiusTerminalEndgame

/-! # Mixed-delta face at `2g=5n`

The later-deep lower window isolates a unique first-face wall where
`9n-2g=4n`, so the `delta*A²` load ties residual I4.  Off this wall the
same coefficient lies strictly below the first-face index throughout
`2g<5n`, and strictly above every residual I4 index after the first-face
drops.  This file extracts the tied coefficient exactly.

Degree dictionary on the wall: `deg A=2n`, `B` at most `n/2`, `c` at most
`3n/2`, residual `d` at most `5n/2`, `e` at most `7n/2`.  I4 at index
`4n` is therefore
`(8/3)(B_{n/2} e_{7n/2} + c_{3n/2} d_{5n/2}) + (1/4) delta A_{2n}² = 0`.
The companion live I3 coefficient at index `5n` is ordinary: every
`delta` summand of I3 stops at `5n/2`.  Two-case comparison of `delta`
against zero then yields either `delta=0` with vanishing residual
`(Be+cd)`, or a nonzero `delta` that determines the same product from I4.

The committed five-radius terminal endgame excludes the wall, so the
residual is empty.  The identities above are the exact I4-tie bookkeeping
that the `delta=0` residual-coordinate cutoff had omitted.

Exact gain: residual I4 identity with the `delta*A²` load; live I3
identity; two-case `delta` dictionary; source-facing `False`.
Next unused row: none on this wall.
Residual: empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveRadiusMixedDeltaFaceI4Tie68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall arithmetic -/

/-- Index dictionary at the unique mixed-delta first-face wall. -/
theorem fiveRadius_mixedDelta_index_arith68
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n) :
    9 * n - 2 * g = 4 * n ∧ 10 * n - 2 * g = 5 * n ∧
      11 * n - 2 * g - 1 = 6 * n - 1 ∧
      13 * n - 2 * g - 1 = 8 * n - 1 ∧
      (3 * n - g) + (6 * n - g) = 4 * n ∧
      (4 * n - g) + (5 * n - g) = 4 * n ∧
      2 * n + (3 * n - g) + (5 * n - g) = 5 * n ∧
      (4 * n - g) + (6 * n - g) = 5 * n ∧
      2 * (5 * n - g) = 5 * n ∧
      3 * (3 * n - g) < 4 * n ∧
      n < 2 * g ∧ 3 * n < 2 * g ∧
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by
  omega

/-! ## Residual coordinates keeping the `delta` load -/

/-- Quartic old-weight load in translated residual coordinates, including
the `delta*A²` summand omitted by the five-to-six `delta=0` cutoff. -/
theorem secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_keepDelta
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) :
    secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  module

/-- Cubic old-weight load in the same coordinates.  After substituting
`D=AB/3+d` the `delta` pieces collapse to `3 delta d - (1/2) delta AB`. -/
theorem secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_keepDelta
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) :
    secondaryLoadInvariantThreePolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
        (2 / 3 * gamma : k) • B ^ 2 + (3 * delta : k) • d -
        (1 / 2 * delta : k) • (A * B) := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  module

/-- Exact quartic invariant in residual coordinates with the `delta` load. -/
theorem cubicFirstIntegralFourPolynomial68_fiveRadius_residualCoordinates
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantFourPolynomial68 B c d e +
        zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_keepDelta]
  abel

/-- Exact cubic invariant in the same residual coordinates. -/
theorem cubicFirstIntegralThreePolynomial68_fiveRadius_residualCoordinates
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) :
    cubicFirstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantThreePolynomial68 A B c d e +
        zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
          (2 / 3 * gamma : k) • B ^ 2 + (3 * delta : k) • d -
          (1 / 2 * delta : k) • (A * B) := by
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_keepDelta]
  abel

/-! ## Exact I4 coefficient, including the `delta*A²` load -/

/-- Residual quartic coefficient at the tied index `4n`.  The cubic `B³`
summand lies strictly below. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_fiveRadiusWall
    (B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (4 * n) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g)) := by
  have hB3 : (B ^ 3).natDegree < 4 * n := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
  have hBei : (3 * n - g) + (6 * n - g) = 4 * n := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - g) hc hd
  have hcdi : (4 * n - g) + (5 * n - g) = 4 * n := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Literal I4 coefficient at the tie: residual face plus `delta*A²`.
The `zeta*A`, `epsilon*B`, `delta*c`, and `gamma*d` loads lie strictly
below index `4n`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_fiveRadiusWall_residual
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (4 * n) =
      (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - g) +
            c.coeff (4 * n - g) * d.coeff (5 * n - g)) +
        (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 := by
  rw [cubicFirstIntegralFourPolynomial68_fiveRadius_residualCoordinates]
  simp only [coeff_add]
  rw [secondaryResidualInvariantFourPolynomial68_coeff_fiveRadiusWall
      B c d e n g hn hwall hB hc hd he]
  have hloadA : (zeta • A).natDegree < 4 * n := by
    compute_degree
    omega
  have hloadB : ((2 * epsilon : k) • B).natDegree < 4 * n := by
    compute_degree
    omega
  have hloadc : ((3 * delta : k) • c).natDegree < 4 * n := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 4 * n := by
    compute_degree
    omega
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hiA : 2 * (2 * n) = 4 * n := by omega
  rw [hiA] at hA2
  rw [coeff_eq_zero_of_natDegree_lt hloadA,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloadd]
  simp only [coeff_smul, smul_eq_mul, hA2]
  ring

/-! ## Exact live I3 coefficient after the wall arithmetic -/

/-- Residual cubic coefficient at index `5n`.  The `B²c` summand lies
strictly below; `d²` attains the face. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_fiveRadiusWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff (5 * n) =
      (8 / 9 : k) *
          (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
              d.coeff (5 * n - g)) +
            3 * c.coeff (4 * n - g) * e.coeff (6 * n - g)) +
        (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g) = 5 * n := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 5 * n := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
  have hcei : (4 * n - g) + (6 * n - g) = 5 * n := by omega
  rw [hcei] at hce
  have hd2 := coeff_pow_at_bound68 d (5 * n - g) 2 hd
  have hd2i : 2 * (5 * n - g) = 5 * n := by omega
  rw [hd2i] at hd2
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce, hd2]
  ring

/-- Literal I3 coefficient at the live wall index.  Every old-weight load,
including both `delta` pieces, stops strictly below `5n`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_fiveRadiusWall_residual
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (5 * n) =
      (8 / 9 : k) *
          (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
              d.coeff (5 * n - g)) +
            3 * c.coeff (4 * n - g) * e.coeff (6 * n - g)) +
        (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveRadius_residualCoordinates]
  simp only [coeff_add, coeff_sub]
  rw [secondaryResidualInvariantThreePolynomial68_coeff_fiveRadiusWall
      A B c d e n g hn hwall hA hB hc hd he]
  have hloadB : (zeta • B).natDegree < 5 * n := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree < 5 * n := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < 5 * n := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 5 * n := by
    compute_degree
    omega
  have hloadd : ((3 * delta : k) • d).natDegree < 5 * n := by
    compute_degree
    omega
  have hloadAB : ((1 / 2 * delta : k) • (A * B)).natDegree < 5 * n := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2,
    coeff_eq_zero_of_natDegree_lt hloadd,
    coeff_eq_zero_of_natDegree_lt hloadAB]
  ring

/-! ## Two-case `delta` dictionary -/

/-- From the two live invariant coefficients: either the mixed `delta`
load vanishes and forces the residual `(Be+cd)` product to vanish, or it
survives and I4 becomes a linear relation for `delta`. -/
theorem fiveRadius_mixedDelta_i4_tie_two_case68
    (delta : k) (A B c d e : k[X]) (n g : ℕ)
    (hwall : 2 * g = 5 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - g) +
            c.coeff (4 * n - g) * d.coeff (5 * n - g)) +
        (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 = 0)
    (hi3 : (8 / 9 : k) *
          (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
              d.coeff (5 * n - g)) +
            3 * c.coeff (4 * n - g) * e.coeff (6 * n - g)) +
        (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0) :
    (delta = 0 ∧
      B.coeff (3 * n - g) * e.coeff (6 * n - g) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g) = 0) ∨
      (delta ≠ 0 ∧
        (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 =
          -((8 / 3 : k) *
            (B.coeff (3 * n - g) * e.coeff (6 * n - g) +
              c.coeff (4 * n - g) * d.coeff (5 * n - g))) ∧
        (8 / 9 : k) *
              (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
                  d.coeff (5 * n - g)) +
                3 * c.coeff (4 * n - g) * e.coeff (6 * n - g)) +
            (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0) := by
  by_cases hdelta0 : delta = 0
  · left
    have hsigma :
        B.coeff (3 * n - g) * e.coeff (6 * n - g) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g) = 0 := by
      have h : (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - g) +
            c.coeff (4 * n - g) * d.coeff (5 * n - g)) = 0 := by
        rw [hdelta0] at hi4
        convert hi4 using 1
        ring
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    exact ⟨hdelta0, hsigma⟩
  · right
    refine ⟨hdelta0, ?_, hi3⟩
    linear_combination hi4

/-! ## Source-facing packet -/

/-- Source-facing I4 tie and live I3 coefficient on the wall. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_i4_tie68
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
      2 * g = 5 * n) :
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
    l = 0 ∧ beta = 0 ∧
      (8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - g)) +
        (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0 ∧
      (8 / 9 : k) *
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
              d.coeff (5 * n - g)) +
            3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g)) +
        (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0 := by
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
  change 2 * g = 5 * n at hwall
  change l = 0 ∧ beta = 0 ∧
    (8 / 3 : k) *
        (Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - g)) +
      (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0 ∧
    (8 / 9 : k) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - g)) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g)) +
      (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hA := data.hA
  have hB := data.hB
  have hc := data.hc
  have hD := data.hD
  have he := data.he
  have hgt3 : 3 * n < 2 * g := by
    have hfive : 5 * n = 2 * g := hwall.symm
    rw [← hfive]
    exact Nat.mul_lt_mul_of_pos_right (by norm_num : (3 : ℕ) < 5) hn
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  have h6 : 2 * (3 * n) = 6 * n := by rw [← Nat.mul_assoc]
  have hg3 : g ≤ 3 * n := by
    have h2 : 2 * g ≤ 2 * (3 * n) := by
      rw [hwall, h6]
      exact Nat.mul_le_mul_right n (by norm_num : (5 : ℕ) ≤ 6)
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num : (0 : ℕ) < 2)
  have hsum : 2 * n + 3 * n = 5 * n := by rw [← Nat.add_mul]
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by
    rw [← Nat.add_sub_assoc hg3, hsum]
  have hd : d.natDegree ≤ 5 * n - g := by
    simp only [d, secondaryDDefectPolynomial68]
    refine (natDegree_sub_le _ _).trans ?_
    rw [sup_le_iff]
    constructor
    · exact hD
    · have hmul := (natDegree_mul_le (p := Ae) (q := Be)).trans
        (Nat.add_le_add hA hB)
      have hsmul := (natDegree_smul_le (1 / 3 : k) (Ae * Be)).trans hmul
      rwa [hindex] at hsmul
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4raw⟩ := data.invariant
  have hI4 := hi4raw
  rw [hl, hbeta] at hI4
  rw [hDrec] at hI4
  have hi4coeff := congrArg (fun p : k[X] => p.coeff (4 * n)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_fiveRadiusWall_residual
    gamma delta epsilon zeta Ae Be ce d ee n g hn hwall
    hA hB hc hd he] at hi4coeff
  have htarget4 : 4 * n ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (by norm_num) hn)
  simp [coeff_C, htarget4] at hi4coeff
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
    hl, hbeta] at hi3e
  rw [hDrec] at hi3e
  have hi3coeff := congrArg (fun p : k[X] => p.coeff (5 * n)) hi3e
  rw [cubicFirstIntegralThreePolynomial68_coeff_fiveRadiusWall_residual
    gamma delta epsilon zeta Ae Be ce d ee n g hn hwall
    hA hB hc hd he] at hi3coeff
  have htarget5 : 5 * n ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (by norm_num) hn)
  simp [coeff_C, htarget5] at hi3coeff
  refine ⟨hl, hbeta, ?_, ?_⟩
  · convert hi4coeff using 1 <;> try ring
  · convert hi3coeff using 1 <;> try ring

/-- Two-case dictionary transported to the canonical expanded source. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_two_case68
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
      2 * g = 5 * n) :
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
    (delta = 0 ∧
      Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - g) = 0) ∨
      (delta ≠ 0 ∧
        (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 =
          -((8 / 3 : k) *
            (Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
              ce.coeff (4 * n - g) * d.coeff (5 * n - g))) ∧
        (8 / 9 : k) *
              (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                  d.coeff (5 * n - g)) +
                3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g)) +
            (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0) := by
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
  change 2 * g = 5 * n at hwall
  change (delta = 0 ∧
      Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - g) = 0) ∨
    (delta ≠ 0 ∧
      (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 =
        -((8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - g))) ∧
      (8 / 9 : k) *
            (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - g)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g)) +
          (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have ha : Ae.coeff (2 * n) ≠ 0 := data.ha
  have htie :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_i4_tie68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧
    (8 / 3 : k) *
        (Be.coeff (3 * n - g) * ee.coeff (6 * n - g) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - g)) +
      (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0 ∧
    (8 / 9 : k) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - g)) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g)) +
      (4 / 3 : k) * d.coeff (5 * n - g) ^ 2 = 0 at htie
  exact fiveRadius_mixedDelta_i4_tie_two_case68
    delta Ae Be ce d ee n g hwall ha htie.2.2.1 htie.2.2.2

/-- The wall is empty.  The five-radius terminal endgame consumes both
sides of the mixed-delta I4-tie dictionary. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_impossible68
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
      2 * g = 5 * n) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEndgame68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hwall

end FiveRadiusMixedDeltaFaceI4Tie68

#print axioms fiveRadius_mixedDelta_index_arith68
#print axioms secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_keepDelta
#print axioms secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_keepDelta
#print axioms cubicFirstIntegralFourPolynomial68_fiveRadius_residualCoordinates
#print axioms cubicFirstIntegralThreePolynomial68_fiveRadius_residualCoordinates
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_fiveRadiusWall
#print axioms cubicFirstIntegralFourPolynomial68_coeff_fiveRadiusWall_residual
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_fiveRadiusWall
#print axioms cubicFirstIntegralThreePolynomial68_coeff_fiveRadiusWall_residual
#print axioms fiveRadius_mixedDelta_i4_tie_two_case68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_i4_tie68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_two_case68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveRadius_mixedDelta_impossible68

end Max11DegreeRoutes
