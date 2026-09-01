import Sol68LaterDeepLowerOpenMiddleBelowFiveClosureScratch

/-! # Residual packets in the strict interior `3n<2g<5n`

After the open first-face drops, residual I4 lives at `9n-g-h` and I3 at
`10n-g-h`.  The residual-coordinate cutoff
`secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta`
drops the `delta*A²` load.  That load sits at index `4n`, so it ties the
residual quartic precisely on `g+h=5n` and is otherwise strictly below or
strictly above that index.

Degree dictionary after the first-face drops: `deg A=2n`, `B` at most
`3n-g`, `c` at most `4n-g`, residual `d` at most `5n-h`, `e` at most
`6n-h`.  On the five-sum wall `g+h=5n` one has `h<2g`, hence `3g>5n` and
`2h>5n`, and I4 at index `4n` is
`(8/3)(B_{3n-g} e_{6n-h} + c_{4n-g} d_{5n-h}) + (1/4) delta A_{2n}² = 0`.
The companion live I3 coefficient at index `5n` is ordinary: every
`delta` summand of I3 stops strictly below `5n`.  Two-case comparison of
`delta` against zero then yields either `delta=0` with vanishing residual
`(Be+cd)`, or a nonzero `delta` that determines the same product from I4.

Off the five-sum wall the same identities are parametrized in `(n,g,h)`:
below `g+h<5n` the `delta*A²` load lies strictly under residual I4, and
above `5n<g+h` it lies strictly over residual I4 and forces `delta=0`.
The middle child `h<2g` and the double child `h≥2g` are the remaining
packet families.

The committed later-deep terminal endgames exclude every named family, so
the residual is empty.  The identities above are the exact I4-tie
bookkeeping that the `delta=0` residual-coordinate cutoff had omitted.

Exact gain: parametrized residual I4 identity with the `delta*A²` load;
live I3 identity; two-case `delta` dictionary on `g+h=5n`; source-facing
`False` for the whole interior.
Next unused row: none in `3n<2g<5n`.
Residual: empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenResidualPacketsI4Tie68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall arithmetic -/

/-- Index dictionary at the residual five-sum I4 tie, parametrized in
`(n,g,h)`. -/
theorem laterDeepLowerOpen_residualPackets_index_arith68
    (n g h : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (hwall : g + h = 5 * n) :
    9 * n - g - h = 4 * n ∧ 10 * n - g - h = 5 * n ∧
      5 * n - h = g ∧ 6 * n - h = n + g ∧
      (3 * n - g) + (6 * n - h) = 4 * n ∧
      (4 * n - g) + (5 * n - h) = 4 * n ∧
      2 * n + (3 * n - g) + (5 * n - h) = 5 * n ∧
      (4 * n - g) + (6 * n - h) = 5 * n ∧
      2 * (5 * n - h) = 2 * g ∧
      2 * g < 5 * n ∧ 5 * n < 3 * g ∧ 5 * n < 2 * h ∧
      3 * (3 * n - g) < 4 * n ∧
      4 * n < 9 * n - 2 * g := by
  omega

/-- The dropped `delta*A²` load at `4n` sits strictly below, on, or
strictly above residual I4 according as `g+h ? 5n`. -/
theorem laterDeepLowerOpen_residualPackets_load_trichotomy68
    (n g h : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hgh : g < h) (hh : h < 2 * g) :
    (g + h < 5 * n ∧ 4 * n < 9 * n - g - h) ∨
      (g + h = 5 * n ∧ 9 * n - g - h = 4 * n) ∨
      (5 * n < g + h ∧ 9 * n - g - h < 4 * n) := by
  rcases lt_trichotomy (g + h) (5 * n) with hlt | heq | hgt
  · exact Or.inl ⟨hlt, by omega⟩
  · exact Or.inr (Or.inl ⟨heq, by omega⟩)
  · exact Or.inr (Or.inr ⟨hgt, by omega⟩)

/-! ## Residual coordinates keeping the `delta` load -/

/-- Cubic old-weight load in translated residual coordinates, including
the `delta` summands omitted by the `_of_l_beta_delta` cutoff.  After
substituting `D=AB/3+d` the `delta` pieces collapse to
`3 delta d - (1/2) delta AB`. -/
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

/-- Exact quartic invariant in residual coordinates with the `delta`
load.  The quartic load identity is the already-committed
`secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta`. -/
theorem cubicFirstIntegralFourPolynomial68_residualPackets_residualCoordinates
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantFourPolynomial68 B c d e +
        zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • d := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta]
  abel

/-- Exact cubic invariant in the same residual coordinates. -/
theorem cubicFirstIntegralThreePolynomial68_residualPackets_residualCoordinates
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
summand lies strictly below because `h<2g`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_fiveSumWall
    (B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (hwall : g + h = 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (4 * n) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 4 * n := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 4 * n := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 4 * n := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Literal I4 coefficient at the residual five-sum tie: residual face
plus `delta*A²`.  The `zeta*A`, `epsilon*B`, `delta*c`, and `gamma*d`
loads lie strictly below index `4n`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_fiveSumWall_residual
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (hwall : g + h = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (4 * n) =
      (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
            c.coeff (4 * n - g) * d.coeff (5 * n - h)) +
        (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 := by
  rw [cubicFirstIntegralFourPolynomial68_residualPackets_residualCoordinates]
  simp only [coeff_add]
  rw [secondaryResidualInvariantFourPolynomial68_coeff_fiveSumWall
      B c d e n g h hn hopen hgh hh hwall hB hc hd he]
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
strictly below because `h<2g`; `d²` is strictly below because `2g<5n`. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_fiveSumWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (hwall : g + h = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff (5 * n) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) = 5 * n := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 5 * n := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 5 * n := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 5 * n := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal I3 coefficient at the live residual index.  Every old-weight
load, including both `delta` pieces, stops strictly below `5n`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_fiveSumWall_residual
    (gamma delta epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hgh : g < h) (hh : h < 2 * g) (hwall : g + h = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (5 * n) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  rw [cubicFirstIntegralThreePolynomial68_residualPackets_residualCoordinates]
  simp only [coeff_add, coeff_sub]
  rw [secondaryResidualInvariantThreePolynomial68_coeff_fiveSumWall
      A B c d e n g h hn hopen hgh hh hwall hA hB hc hd he]
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
theorem laterDeepLowerOpen_fiveSumWall_i4_tie_two_case68
    (delta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hwall : g + h = 5 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
            c.coeff (4 * n - g) * d.coeff (5 * n - h)) +
        (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 = 0)
    (hi3 : (8 / 9 : k) *
          (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
              d.coeff (5 * n - h)) +
            3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) = 0) :
    (delta = 0 ∧
      B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) ∨
      (delta ≠ 0 ∧
        (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 =
          -((8 / 3 : k) *
            (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
              c.coeff (4 * n - g) * d.coeff (5 * n - h))) ∧
        (8 / 9 : k) *
              (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
                  d.coeff (5 * n - h)) +
                3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) = 0) := by
  by_cases hdelta0 : delta = 0
  · left
    have hsigma :
        B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0 := by
      have h : (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
            c.coeff (4 * n - g) * d.coeff (5 * n - h)) = 0 := by
        rw [hdelta0] at hi4
        convert hi4 using 1
        ring
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    exact ⟨hdelta0, hsigma⟩
  · right
    refine ⟨hdelta0, ?_, hi3⟩
    linear_combination hi4

/-! ## Source-facing packet -/

/-- Source-facing I4 tie and live I3 coefficient on the residual five-sum
wall. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_fiveSumWall_i4_tie68
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
    l = 0 ∧ beta = 0 ∧ g < h ∧ h < 2 * g ∧
      (8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
        (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0 ∧
      (8 / 9 : k) *
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
              d.coeff (5 * n - h)) +
            3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h)) = 0 := by
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
  change g + h = 5 * n at hwall
  change l = 0 ∧ beta = 0 ∧ g < h ∧ h < 2 * g ∧
    (8 / 3 : k) *
        (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
      (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0 ∧
    (8 / 9 : k) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h)) = 0
  have hmiddle :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change h < 2 * g at hmiddle
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hg : 0 < g := data.hg
  have hA := data.hA
  have hB := data.hB
  have hc := data.hc
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hd : d.natDegree ≤ 5 * n - h := bounds.1
  have he : ee.natDegree ≤ 6 * n - h := bounds.2
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4raw⟩ := data.invariant
  have hI4 := hi4raw
  rw [drops.1, drops.2.1] at hI4
  rw [hDrec] at hI4
  have hi4coeff := congrArg (fun p : k[X] => p.coeff (4 * n)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_fiveSumWall_residual
    gamma delta epsilon zeta Ae Be ce d ee n g h hn hopen
    drops.2.2.2.2.2.2 hmiddle hwall hA hB hc hd he] at hi4coeff
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
    drops.1, drops.2.1] at hi3e
  rw [hDrec] at hi3e
  have hi3coeff := congrArg (fun p : k[X] => p.coeff (5 * n)) hi3e
  rw [cubicFirstIntegralThreePolynomial68_coeff_fiveSumWall_residual
    gamma delta epsilon zeta Ae Be ce d ee n g h hn hopen
    drops.2.2.2.2.2.2 hmiddle hwall hA hB hc hd he] at hi3coeff
  have htarget5 : 5 * n ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (by norm_num) hn)
  simp [coeff_C, htarget5] at hi3coeff
  refine ⟨drops.1, drops.2.1, drops.2.2.2.2.2.2, hmiddle, ?_, ?_⟩
  · convert hi4coeff using 1 <;> try ring
  · exact mul_eq_zero.mpr (Or.inr hi3coeff)

/-- Two-case dictionary transported to the canonical expanded source. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_fiveSumWall_two_case68
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
    (delta = 0 ∧
      Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) ∨
      (delta ≠ 0 ∧
        (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 =
          -((8 / 3 : k) *
            (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
              ce.coeff (4 * n - g) * d.coeff (5 * n - h))) ∧
        (8 / 9 : k) *
              (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                  d.coeff (5 * n - h)) +
                3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h)) = 0) := by
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
  change g + h = 5 * n at hwall
  change (delta = 0 ∧
      Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) ∨
    (delta ≠ 0 ∧
      (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 =
        -((8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - h))) ∧
      (8 / 9 : k) *
            (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - h)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h)) = 0)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have ha : Ae.coeff (2 * n) ≠ 0 := data.ha
  have htie :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_fiveSumWall_i4_tie68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hwall)
  change l = 0 ∧ beta = 0 ∧ g < h ∧ h < 2 * g ∧
    (8 / 3 : k) *
        (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
      (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0 ∧
    (8 / 9 : k) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h)) = 0 at htie
  exact laterDeepLowerOpen_fiveSumWall_i4_tie_two_case68
    delta Ae Be ce d ee n g h hwall ha htie.2.2.2.2.1 htie.2.2.2.2.2

/-! ## Family-by-family endgames -/

/-- The double residual child `h≥2g` is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_residualPackets_impossible68
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
    (hdouble :
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
      2 * g ≤ h) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hopen hdouble

/-- The ordinary residual packet below the five-sum wall is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBelowFive_residualPackets_impossible68
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
    (hbelow :
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
      g + h < 5 * n) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBelowFive_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hopen hbelow

/-- The residual five-sum wall is empty.  The later-deep five-sum
endgame consumes both sides of the mixed-delta I4-tie dictionary. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_residualPackets_impossible68
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
      g + h = 5 * n) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hopen hwall

/-- The residual packet above the five-sum wall is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_residualPackets_impossible68
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
    (habove :
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
      5 * n < g + h) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hopen habove

/-- The strict interior is empty.  The later-deep open terminal endgame
consumes every residual packet family. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_residualPackets_impossible68
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
      3 * n < 2 * g ∧ 2 * g < 5 * n) : False :=
  maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hopen

end LaterDeepLowerOpenResidualPacketsI4Tie68

#print axioms laterDeepLowerOpen_residualPackets_index_arith68
#print axioms laterDeepLowerOpen_residualPackets_load_trichotomy68
#print axioms secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_keepDelta
#print axioms cubicFirstIntegralFourPolynomial68_residualPackets_residualCoordinates
#print axioms cubicFirstIntegralThreePolynomial68_residualPackets_residualCoordinates
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_fiveSumWall
#print axioms cubicFirstIntegralFourPolynomial68_coeff_fiveSumWall_residual
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_fiveSumWall
#print axioms cubicFirstIntegralThreePolynomial68_coeff_fiveSumWall_residual
#print axioms laterDeepLowerOpen_fiveSumWall_i4_tie_two_case68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_fiveSumWall_i4_tie68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_fiveSumWall_two_case68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_residualPackets_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBelowFive_residualPackets_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_residualPackets_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_residualPackets_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_residualPackets_impossible68

end Max11DegreeRoutes
