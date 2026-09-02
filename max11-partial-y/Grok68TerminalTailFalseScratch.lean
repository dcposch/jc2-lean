import Sol68FiveToSixHZeroInventoryScratch

/-! # Terminal-zero and large-terminal-cusp tail of the `(6,8)` scale-zero residual

Untracked working note. No tracked file was edited.

`FiveToSixTerminalZeroPacket68` is the zero child of the symbolic terminal
packet: `deg d ≤ g-2n`, `deg e ≤ g-n`, `zeta=0`, and both top coefficients
vanish.  The green large-aligned consumer
`integratedPolynomialLowerSystem68_fiveToSix_consume_largeAligned_terminalZero68`
advances one `60`-stride beyond the load wall, where the wall load
`zeta*A_top` is already dead, producing
`FiveToSixLargeTerminalZeroSuccessor68`.  This file iterates that
beyond-wall edge.  Every zero child drops both supports by a lattice
stride; after finitely many strides the residual defects vanish, and the
constant-`B` one-form comparison contradicts `terminal ≠ 0`.  Off the
`60`-lattice a cusp cannot occupy both `d` and `e` indices at once, so the
staggered family is only the zero descent.  The unique arithmetic wall
`n=30`, `g=90` is already `False` by
`maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68`.

The sibling at-wall packet
`FiveToSixLargeTerminalAllNonzeroCuspResidual68` is the honest all-nonzero
cusp at offset `7n-2g` in the large aligned family.  Its leading face is
consistent.  The vanishing `d=e=0` child is now `False` for every `B`, including
constant `B`, once `deg A ≥ 2`.  Source `d=0` with constant `B` is
likewise `False` (I4 forces `e` constant, then the same row-zero
identity).  On `n ≤ 120` the expanded `B` bound is `< 60`, so source
`B` is constant: the terminal-zero packet reduces to producing source
`d=0`.  The unique wall `n=30` remains `False` by
`maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68`.

Exact gain: load-free beyond-wall I4/I3 identities at arbitrary
displacement `t ≤ g-2n`; source-facing beyond-wall edge; lattice
iteration past the dead wall; full `d=e=0` exclusion; `d=0` with
constant `B`; wall `n=30`; source-`B` constancy on `n ≤ 120`.
Next unused row: third-jet I4/I3 pair on the large terminal
all-nonzero cusp and on any beyond-wall cusp at `7n-2g+60k`; source
`d=0` descent on `120 < n`.
Residual: `FiveToSixTerminalTailOpenResidual68` (aligned beyond-wall
cusp spawned by the terminal-zero packet, and
`FiveToSixLargeTerminalAllNonzeroCuspResidual68`).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalTailFalse68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Residual `d=e=0` endgame -/

/-- With both residual defects zero and `zeta=0`, I4 is the cubic in `B`
plus the `epsilon` load. -/
theorem fiveToSix_I4_of_de_zero68 (gamma epsilon : k) (A B c : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B)) 0 =
      (-8 / 27 : k) • B ^ 3 + (2 * epsilon : k) • B := by
  have hD : (1 / 3 : k) • (A * B) = (1 / 3 : k) • (A * B) + (0 : k[X]) :=
    (add_zero _).symm
  rw [hD, cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  simp only [secondaryResidualInvariantFourPolynomial68, zero_mul, mul_zero,
    add_zero, zero_add, zero_smul, smul_zero]

/-- A non-constant `B` makes that I4 have positive degree, so it cannot be
a constant first integral. -/
theorem fiveToSix_deZero_B_nonconstant_I4_impossible68
    (gamma epsilon i4 : k) (A B c : k[X])
    (hB : 1 ≤ B.natDegree)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4) : False := by
  have hform := fiveToSix_I4_of_de_zero68 gamma epsilon A B c
  rw [hform] at hi4
  have hBne : B ≠ 0 := fun hB0 => by
    have : B.natDegree = 0 := by simp [hB0]
    omega
  have hpow : (B ^ 3).natDegree = 3 * B.natDegree := by
    rw [natDegree_pow (p := B) (n := 3)]
  have hleft : ((-8 / 27 : k) • B ^ 3).natDegree = 3 * B.natDegree := by
    rw [smul_eq_C_mul, natDegree_C_mul (by norm_num : (-8 / 27 : k) ≠ 0),
      hpow]
  have hright : ((2 * epsilon : k) • B).natDegree ≤ B.natDegree :=
    natDegree_smul_le (2 * epsilon) B
  have hlt :
      ((2 * epsilon : k) • B).natDegree <
        ((-8 / 27 : k) • B ^ 3).natDegree := by
    rw [hleft]
    exact lt_of_le_of_lt hright (by omega)
  have hsum :
      ((-8 / 27 : k) • B ^ 3 + (2 * epsilon : k) • B).natDegree =
        3 * B.natDegree := by
    rw [← hleft]
    exact natDegree_add_eq_left_of_natDegree_lt hlt
  have hC : (C i4).natDegree ≤ 0 := le_of_eq (natDegree_C i4)
  have hEq : (C i4).natDegree = 3 * B.natDegree := by
    rw [← hi4, hsum]
  omega

/-- With `l=beta=delta=zeta=0` and `B=D=0`, the integrated `U` vanishes. -/
theorem fiveToSix_U_of_B_D_zeta_zero68
    (alpha gamma : k) (A C0 E : k[X]) :
    integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0 C0 0 E = 0 := by
  simp only [integratedUPolynomial68, zero_smul, smul_zero, mul_zero,
    zero_mul, add_zero, sub_zero, C_0]

/-- The `B=0` child of `d=e=0` makes row zero the zero polynomial, hence
`terminal=0`. -/
theorem fiveToSix_deZero_B_zero_terminal_impossible68
    (alpha gamma epsilon eta terminal : k) (A C0 E : k[X])
    (hterminal : terminal ≠ 0)
    (hrow0 : lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0 C0 0 E)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0 C0 0 E)
      0 E = C terminal) : False := by
  have hU := fiveToSix_U_of_B_D_zeta_zero68 alpha gamma A C0 E
  simp only [lowerRowZeroPolynomial68, hU, zero_mul, zero_sub,
    derivative_zero, mul_zero, sub_zero] at hrow0
  exact hterminal (C_eq_zero.mp hrow0.symm)

/-- A polynomial of degree at most zero with vanishing constant term is
zero. -/
theorem eq_zero_of_natDegree_le_zero_coeff_zero68 (p : k[X])
    (hdeg : p.natDegree ≤ 0) (h0 : p.coeff 0 = 0) : p = 0 := by
  have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hdeg
  rw [hpC, h0, C_0]

/-! ## Load-free beyond-wall identities at an arbitrary positive offset -/

/-- Homogeneous I4 at displacement `t` past the terminal wall.  The cubic
`B³` term stays strictly below because `t ≤ g-2n` and `5n<2g`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_beyondWall_offset68
    (B c d e : k[X]) (n g t : ℕ) (hn : 0 < n) (ht : 0 < t)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (2 * n - t) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n - t) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hB3 : (B ^ 3).natDegree < 2 * n - t := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (g - n - t) hB he
  have hBei : (3 * n - g) + (g - n - t) = 2 * n - t := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (g - 2 * n - t) hc hd
  have hcdi : (4 * n - g) + (g - 2 * n - t) = 2 * n - t := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Homogeneous I3 at the same beyond-wall displacement. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_beyondWall_offset68
    (A B c d e : k[X]) (n g t : ℕ) (hn : 0 < n) (ht : 0 < t)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (3 * n - t) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n - t)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n) (3 * n - g)
    (g - 2 * n - t) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (g - 2 * n - t) = 3 * n - t := by
    omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 3 * n - t := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (g - n - t) hc he
  have hcei : (4 * n - g) + (g - n - t) = 3 * n - t := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 3 * n - t := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal I4 is load-free past the wall once `zeta=0`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_beyondWall_offset68
    (gamma epsilon : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n) (ht : 0 < t)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (2 * n - t) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n - t) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hloadB : ((2 * epsilon : k) • B).natDegree < 2 * n - t := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 2 * n - t := by
    compute_degree
    omega
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  rw [coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_beyondWall_offset68
      B c d e n g t hn ht ⟨hw5, hw6⟩ htle hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

/-- Literal I3 is load-free at the same displacement. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_beyondWall_offset68
    (gamma epsilon : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n) (ht : 0 < t)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (3 * n - t) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n - t)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hloadc : ((2 * epsilon : k) • c).natDegree < 3 * n - t := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < 3 * n - t := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 3 * n - t := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  rw [coeff_sub, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_beyondWall_offset68
      A B c d e n g t hn ht ⟨hw5, hw6⟩ htle hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- Constant first integrals give the ordinary incidence face at every
positive displacement `t ≤ g-2n` past the dead wall. -/
theorem polynomialSecondaryResidualBeyondWallFace68_offset
    (gamma epsilon i4 i3 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n) (ht : 0 < t)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (g - 2 * n - t))
      (e.coeff (g - n - t)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (2 * n - t)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_beyondWall_offset68
      gamma epsilon A B c d e n g t hn ht hwindow htle hB hc hd he] at hz
    have hj : 2 * n - t ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (3 * n - t)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_beyondWall_offset68
      gamma epsilon A B c d e n g t hn ht hwindow htle hA hB hc hd he] at hz
    have hj : 3 * n - t ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-! ## Source-facing beyond-wall edge -/

set_option maxHeartbeats 25000000 in
/-- Source-facing classification at displacement `t` past the wall on a
`zeta=0` packet. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (t : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (ht : 0 < t)
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
    (hzeta : zeta = 0)
    (htle :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      t ≤ g - 2 * n)
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
      d.natDegree ≤ g - 2 * n - t ∧ ee.natDegree ≤ g - n - t) :
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
    (d.coeff (g - 2 * n - t) = 0 ∧ ee.coeff (g - n - t) = 0) ∨
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t) := by
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
  change t ≤ g - 2 * n at htle
  change d.natDegree ≤ g - 2 * n - t ∧ ee.natDegree ≤ g - n - t at hdrop
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
  rw [hzeta] at hI4 hi3e
  have hface := polynomialSecondaryResidualBeyondWallFace68_offset
    gamma epsilon i4 i3 Ae Be ce d ee n g t data.hn ht hwindow htle
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
  have hclass := firstSecondary_mainFamily_gapSucc_classify68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) (d.coeff (g - 2 * n - t))
    (ee.coeff (g - n - t)) data.ha hold hface
  rcases hclass with hzero | hcusp
  · exact Or.inl hzero
  · right
    have hidxd : 5 * n - g - (7 * n - 2 * g + t) = g - 2 * n - t := by
      omega
    have hidxe : 6 * n - g - (7 * n - 2 * g + t) = g - n - t := by
      omega
    exact ⟨hcusp.1, hcusp.2.1,
      by rw [hidxd]; exact hcusp.2.2.1,
      by rw [hidxe]; exact hcusp.2.2.2.1,
      hcusp.2.2.2.2⟩

/-- Terminal-wall index dictionary, isolated so `omega` does not see
expansion-lattice `dvd` hypotheses. -/
theorem fiveToSix_terminal_index_d68 (n g : ℕ)
    (hw : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
    5 * n - g - (7 * n - 2 * g) = g - 2 * n ∧
      6 * n - g - (7 * n - 2 * g) = g - n ∧
      5 * n - g - (7 * n - 2 * g + 60) = g - 2 * n - 60 ∧
      6 * n - g - (7 * n - 2 * g + 60) = g - n - 60 := by
  obtain ⟨hw5, hw6⟩ := hw
  have : 2 * n ≤ g := by omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

theorem fiveToSix_terminal_index_d_dvd68 (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g)
    (hw : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
    60 ∣ 5 * n - g - (7 * n - 2 * g) ∧
      60 ∣ 6 * n - g - (7 * n - 2 * g) := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨G, hG⟩ := hg
  have hidx := fiveToSix_terminal_index_d68 n g hw
  have h2 : 2 * N ≤ G := by
    have : 2 * n ≤ g := by
      have := hw.1
      omega
    omega
  constructor
  · rw [hidx.1, hN, hG]
    refine ⟨G - 2 * N, ?_⟩
    have hmul : 2 * (60 * N) = 60 * (2 * N) := by ring
    rw [hmul, ← Nat.mul_sub]
  · rw [hidx.2.1, hN, hG]
    refine ⟨G - N, ?_⟩
    have : N ≤ G := by omega
    rw [← Nat.mul_sub]

/-- `60`-multiple subtraction identity used by the beyond-wall iterator. -/
theorem fiveToSix_sixty_mul_sub_sub68 (N G r : ℕ)
    (h : 2 * N + r ≤ G) :
    60 * G - 2 * (60 * N) - 60 * r = 60 * (G - 2 * N - r) := by
  have h1 : 2 * (60 * N) = 60 * (2 * N) := by ring
  rw [h1, ← Nat.mul_sub, ← Nat.mul_sub]

theorem fiveToSix_sixty_mul_sub_sub_one68 (N G r : ℕ)
    (h : N + r ≤ G) :
    60 * G - 60 * N - 60 * r = 60 * (G - N - r) := by
  rw [← Nat.mul_sub, ← Nat.mul_sub]

theorem fiveToSix_le_of_sixty_mul68 {a b : ℕ}
    (h : 60 * a ≤ 60 * b) : a ≤ b :=
  Nat.le_of_mul_le_mul_left h (by norm_num : 0 < 60)

/-- Room `60(r+1) ≤ 60G - 120N` implies `2N+r ≤ G`. -/
theorem fiveToSix_room_implies_G68 (N G r : ℕ)
    (h : 60 * r + 60 ≤ 60 * G - 2 * (60 * N))
    (h2 : 2 * (60 * N) ≤ 60 * G) :
    2 * N + r ≤ G := by
  have hsum : 2 * (60 * N) + (60 * r + 60) ≤ 60 * G := by omega
  have : 60 * (2 * N + r + 1) ≤ 60 * G := by
    convert hsum using 1
    ring
  have hsucc : 2 * N + r + 1 ≤ G := fiveToSix_le_of_sixty_mul68 this
  exact Nat.le_of_succ_le (by simpa [Nat.succ_eq_add_one] using hsucc)

/-! ## Lattice iteration past the wall -/

set_option maxHeartbeats 40000000 in
/-- On a `60`-aligned `zeta=0` packet, iterate `m` lattice strides past the
wall: either an honest cusp appears, or both supports drop by `60m`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWall_iterate68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (m : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hn60 : 60 ∣ weightedRadius68 A B C0 D E)
    (hg60 :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ g)
    (hzeta : zeta = 0)
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
      d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧
        d.coeff (g - 2 * n) = 0 ∧ ee.coeff (g - n) = 0)
    (hroom :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 * m ≤ g - 2 * n) :
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
    (∃ j, 0 < j ∧ j ≤ m ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g
          (7 * n - 2 * g + 60 * j)) ∨
      (d.natDegree ≤ g - 2 * n - 60 * m ∧
        ee.natDegree ≤ g - n - 60 * m) := by
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
  change 60 ∣ n at hn60
  change 60 ∣ g at hg60
  change d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧
    d.coeff (g - 2 * n) = 0 ∧ ee.coeff (g - n) = 0 at hdrop
  change 60 * m ≤ g - 2 * n at hroom
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g at hglobal
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hsteps : ∀ r : ℕ,
      60 * r ≤ g - 2 * n →
      ((∃ j, 0 < j ∧ j ≤ r ∧
          FiveToSixCuspEdge68 Ae Be ce d ee n g
            (7 * n - 2 * g + 60 * j)) ∨
        (d.natDegree ≤ g - 2 * n - 60 * r ∧
          ee.natDegree ≤ g - n - 60 * r)) := by
    intro r
    induction r with
    | zero =>
        intro _
        right
        exact ⟨hdrop.1, hdrop.2.1⟩
    | succ r ih =>
        intro hroomr
        have hprev := ih (by omega)
        rcases hprev with hcusp | hprev
        · left
          rcases hcusp with ⟨j, hjpos, hjle, hcusp⟩
          exact ⟨j, hjpos, by omega, hcusp⟩
        · by_cases hr0 : r = 0
          · subst r
            have hidx := fiveToSix_terminal_index_d68 n g hwindow
            have hdiv := fiveToSix_terminal_index_d_dvd68 n g hn60 hg60 hwindow
            right
            constructor
            · rw [hdexpand, ← hidx.2.2.1]
              refine natDegree_expand_le_sub_next_sixty68
                (secondaryDDefectPolynomial68 A B D) (5 * n - g)
                (7 * n - 2 * g) hdiv.1 (by
                  have := hwindow.1
                  have := hwindow.2
                  have := fiveToSix_terminal_index_d68 n g hwindow
                  omega) ?_ ?_
              · rw [hidx.1, ← hdexpand]
                exact hdrop.1
              · rw [hidx.1, ← hdexpand]
                exact hdrop.2.2.1
            · rw [heexpand, ← hidx.2.2.2]
              refine natDegree_expand_le_sub_next_sixty68
                (cubicEDefectPolynomial68 A C0 E) (6 * n - g)
                (7 * n - 2 * g) hdiv.2 (by
                  have := hwindow.1
                  have := hwindow.2
                  have := fiveToSix_terminal_index_d68 n g hwindow
                  omega) ?_ ?_
              · rw [hidx.2.1, ← heexpand]
                exact hdrop.2.1
              · rw [hidx.2.1, ← heexpand]
                exact hdrop.2.2.2
          · have htpos : 0 < 60 * r := by
              clear hn60 hg60
              omega
            have hedge :=
              maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
                l alpha beta gamma delta epsilon zeta eta terminal
                A B C0 D E (60 * r) hterminal hsys htpos
                (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
                  hwindow)
                hzeta
                (by
                  simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
                    (show 60 * r ≤ g - 2 * n by
                      clear hn60 hg60
                      omega))
                (by
                  simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
                    hprev)
            change (d.coeff (g - 2 * n - 60 * r) = 0 ∧
                ee.coeff (g - n - 60 * r) = 0) ∨
              FiveToSixCuspEdge68 Ae Be ce d ee n g
                (7 * n - 2 * g + 60 * r) at hedge
            rcases hedge with hedge | hcusp
            · right
              obtain ⟨N, hN⟩ := hn60
              obtain ⟨G, hG⟩ := hg60
              have hnext_d : 60 * r + 60 ≤ g - 2 * n := by
                have : 60 * Nat.succ r = 60 * r + 60 := by
                  rw [Nat.succ_eq_add_one, mul_add, mul_one]
                rwa [← this]
              have hnext_e : 60 * r + 60 ≤ g - n :=
                hnext_d.trans
                  (Nat.sub_le_sub_left
                    (Nat.le_mul_of_pos_left n (by omega : 0 < 2)) g)
              have hleG : 2 * N + r ≤ G := by
                refine fiveToSix_room_implies_G68 N G r ?_ ?_
                · have := hnext_d
                  simpa [hN, hG] using this
                · have : 2 * n ≤ g := by
                    have := hwindow.1
                    omega
                  simpa [hN, hG] using this
              have hdphase : 60 ∣ g - 2 * n - 60 * r :=
                ⟨G - 2 * N - r, by
                  rw [hN, hG, fiveToSix_sixty_mul_sub_sub68 N G r hleG]⟩
              have hephase : 60 ∣ g - n - 60 * r :=
                ⟨G - N - r, by
                  have hle : N + r ≤ G := by omega
                  rw [hN, hG, fiveToSix_sixty_mul_sub_sub_one68 N G r hle]⟩
              constructor
              · rw [hdexpand]
                exact natDegree_expand_le_sub_next_sixty68
                  (secondaryDDefectPolynomial68 A B D) (g - 2 * n)
                  (60 * r) hdphase hnext_d
                  (by simpa only [hdexpand] using hprev.1)
                  (by simpa only [hdexpand] using hedge.1)
              · rw [heexpand]
                exact natDegree_expand_le_sub_next_sixty68
                  (cubicEDefectPolynomial68 A C0 E) (g - n)
                  (60 * r) hephase hnext_e
                  (by simpa only [heexpand] using hprev.2)
                  (by simpa only [heexpand] using hedge.2)
            · left
              exact ⟨r, Nat.pos_of_ne_zero hr0, Nat.le_succ r, hcusp⟩
  exact hsteps m hroom

/-- The product `A * A'` attains `m * a²` at index `2m-1`. -/
theorem coeff_mul_derivative_top68 (A : k[X]) (hA : 1 ≤ A.natDegree) :
    (A * derivative A).coeff (2 * A.natDegree - 1) =
      (A.natDegree : k) * A.coeff A.natDegree ^ 2 := by
  have hder : (derivative A).natDegree ≤ A.natDegree - 1 :=
    natDegree_derivative_le A
  have hsum : A.natDegree + (A.natDegree - 1) = 2 * A.natDegree - 1 := by
    omega
  have hmul := coeff_mul_at_bounds68 A (derivative A) A.natDegree
    (A.natDegree - 1) le_rfl hder
  rw [hsum] at hmul
  rw [hmul, coeff_derivative]
  have hidx : A.natDegree - 1 + 1 = A.natDegree := by omega
  rw [hidx]
  have hcast : (A.natDegree - 1 : ℕ) + (1 : k) = (A.natDegree : k) :=
    (by exact_mod_cast hidx)
  rw [hcast]
  ring

/-- Source `d=e=0` is `False` when `B` is non-constant or `B=0`. -/
theorem fiveToSix_deZero_B_zero_or_nonconstant_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A B D = 0)
    (he : cubicEDefectPolynomial68 A C0 E = 0)
    (hBsplit : B = 0 ∨ 1 ≤ B.natDegree) : False := by
  have hDrec : D = (1 / 3 : k) • (A * B) := by
    have h := secondaryDDefectPolynomial68_reconstruct A B D
    rw [hd, add_zero] at h
    exact h
  have hCrec : C0 = (1 / 3 : k) • A ^ 2 + cubicCDefectPolynomial68 A C0 :=
    cubicCDefectPolynomial68_reconstruct A C0
  have hErec : E = (1 / 27 : k) • A ^ 3 +
      (1 / 3 : k) • (A * cubicCDefectPolynomial68 A C0) := by
    have h := cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
    rw [he, add_zero] at h
    exact h
  obtain ⟨i4, hi4raw⟩ := hsys.firstFour
  have hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B (cubicCDefectPolynomial68 A C0) ((1 / 3 : k) • (A * B)) 0 =
      C i4 := by
    have h := hi4raw
    rw [hl, hbeta, hdelta, hzeta, hCrec] at h
    have hEfull := cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
    rw [hEfull] at h
    rw [firstIntegralFourPolynomial68_cubicCoordinates] at h
    rw [he, hDrec] at h
    simpa using h
  rcases hBsplit with hBzero | hBpos
  · have hD0 : D = 0 := by
      rw [hDrec, hBzero, mul_zero, smul_zero]
    have hrow0 := hsys.rowZero
    rw [hl, hbeta, hdelta, hzeta, hBzero, hD0] at hrow0
    exact fiveToSix_deZero_B_zero_terminal_impossible68 alpha gamma epsilon
      eta terminal A C0 E hterminal hrow0
  · exact fiveToSix_deZero_B_nonconstant_I4_impossible68 gamma epsilon i4 A B
      (cubicCDefectPolynomial68 A C0) hBpos hi4

/-! ## Constant-`B` vanishing endgame -/

/-- With residual `d=0` and `zeta=0`, I4 is the cubic in `B` plus the
`B e` pairing and the `epsilon` load. -/
theorem fiveToSix_I4_of_d_zero68 (gamma epsilon : k) (A B c e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B)) e =
      (-8 / 27 : k) • B ^ 3 + (8 / 3 : k) • (B * e) +
        (2 * epsilon : k) • B := by
  have hD : (1 / 3 : k) • (A * B) = (1 / 3 : k) • (A * B) + (0 : k[X]) :=
    (add_zero _).symm
  rw [hD, cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  simp only [secondaryResidualInvariantFourPolynomial68, zero_mul, mul_zero,
    add_zero, zero_add, zero_smul, smul_zero]

/-- A constant nonzero `B` and a constant I4 force `e` itself to be
constant, once `d=0`. -/
theorem fiveToSix_dZero_B_constant_forces_e_constant68
    (gamma epsilon i4 : k) (A B c e : k[X])
    (hB : B.natDegree ≤ 0) (hBne : B ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) e = C i4) :
    e.natDegree ≤ 0 := by
  have hform := fiveToSix_I4_of_d_zero68 gamma epsilon A B c e
  rw [hform] at hi4
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hb : B.coeff 0 ≠ 0 := by
    intro hb0
    exact hBne (by rw [hBC, hb0, C_0])
  have hB3 : ((-8 / 27 : k) • B ^ 3).natDegree ≤ 0 := by
    rw [hBC]
    compute_degree
  have hBload : ((2 * epsilon : k) • B).natDegree ≤ 0 := by
    rw [hBC]
    compute_degree
  have hC : (C i4).natDegree ≤ 0 := le_of_eq (natDegree_C i4)
  have hBe : ((8 / 3 : k) • (B * e)).natDegree ≤ 0 := by
    have : (8 / 3 : k) • (B * e) =
        C i4 - ((-8 / 27 : k) • B ^ 3 + (2 * epsilon : k) • B) := by
      rw [← hi4]
      ring
    rw [this]
    exact (natDegree_sub_le _ _).trans
      (max_le hC ((natDegree_add_le _ _).trans (max_le hB3 hBload)))
  have hBe' : (B * e).natDegree ≤ 0 := by
    by_cases h0 : B * e = 0
    · simp [h0]
    · have hsc :
          ((8 / 3 : k) • (B * e)).natDegree = (B * e).natDegree := by
        rw [smul_eq_C_mul, natDegree_C_mul (by norm_num : (8 / 3 : k) ≠ 0)]
      omega
  by_cases he0 : e = 0
  · simp [he0]
  · have hBne' : B ≠ 0 := hBne
    rw [natDegree_mul hBne' he0] at hBe'
    omega

/-- Row zero on a constant nonzero `B`, vanishing `d`, and constant `e`
cannot be a nonzero constant once `deg A ≥ 2`. -/
theorem fiveToSix_dZero_eConstant_B_constant_rowZero_impossible68
    (alpha gamma epsilon eta terminal : k) (A B c d e : k[X])
    (hterminal : terminal ≠ 0) (hA : 2 ≤ A.natDegree)
    (hB : B.natDegree ≤ 0) (hBne : B ≠ 0) (hd : d = 0)
    (he : e.natDegree ≤ 0)
    (hrow0 : secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = C terminal) : False := by
  have hform := fiveToSix_pairZero_rowZero_polynomial68
    alpha gamma epsilon eta A B c d e hB hd he
  rw [hform] at hrow0
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hb : B.coeff 0 ≠ 0 := by
    intro hb0
    exact hBne (by rw [hBC, hb0, C_0])
  set inner : k[X] :=
    (4 : k) • c ^ 2 + (6 * gamma : k) • c -
      (4 * e.coeff 0 + 3 * epsilon : k) • A
  change (B.coeff 0 / 27 : k) • (derivative A * inner) = C terminal at hrow0
  have hAne : A ≠ 0 := fun hA0 => by
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have htop : A.coeff A.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hAne
  have hder_coeff :
      (derivative A).coeff (A.natDegree - 1) =
        (A.natDegree : k) * A.coeff A.natDegree := by
    rw [coeff_derivative]
    have hidx : A.natDegree - 1 + 1 = A.natDegree := by omega
    rw [hidx]
    have hcast : (A.natDegree - 1 : ℕ) + (1 : k) = (A.natDegree : k) :=
      (by exact_mod_cast hidx)
    rw [hcast]
    ring
  have hnA : (A.natDegree : k) ≠ 0 := by
    exact_mod_cast (by omega : A.natDegree ≠ 0)
  have hA'ne : derivative A ≠ 0 := by
    intro h0
    have : (A.natDegree : k) * A.coeff A.natDegree = 0 := by
      rw [← hder_coeff, h0, coeff_zero]
    exact htop ((mul_eq_zero.mp this).resolve_left hnA)
  have hb27 : (B.coeff 0 / 27 : k) ≠ 0 :=
    div_ne_zero hb (by norm_num)
  by_cases hin : inner = 0
  · have : (0 : k[X]) = C terminal := by
      simpa [hin, smul_zero] using hrow0
    exact hterminal (C_eq_zero.mp this.symm)
  · have hdeg :
        ((B.coeff 0 / 27 : k) • (derivative A * inner)).natDegree =
          (derivative A).natDegree + inner.natDegree := by
      rw [smul_eq_C_mul, natDegree_C_mul hb27, natDegree_mul hA'ne hin]
    have hder_ge : 1 ≤ (derivative A).natDegree := by
      have hpos : (derivative A).coeff (A.natDegree - 1) ≠ 0 := by
        rw [hder_coeff]
        exact mul_ne_zero hnA htop
      have : A.natDegree - 1 ≤ (derivative A).natDegree :=
        le_natDegree_of_ne_zero hpos
      omega
    have hC : (C terminal).natDegree = 0 := natDegree_C terminal
    have : (C terminal).natDegree =
        (derivative A).natDegree + inner.natDegree := by
      rw [← hrow0, hdeg]
    omega

/-- Source `d=0` with constant `B` is `False` once `deg A ≥ 2`. -/
theorem fiveToSix_dZero_B_constant_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A B D = 0)
    (hB : B.natDegree ≤ 0) (hA : 2 ≤ A.natDegree) : False := by
  have hDrec : D = (1 / 3 : k) • (A * B) := by
    have h := secondaryDDefectPolynomial68_reconstruct A B D
    rw [hd, add_zero] at h
    exact h
  have hCrec : C0 = (1 / 3 : k) • A ^ 2 + cubicCDefectPolynomial68 A C0 :=
    cubicCDefectPolynomial68_reconstruct A C0
  let c := cubicCDefectPolynomial68 A C0
  let e := cubicEDefectPolynomial68 A C0 E
  have hErec : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e := by
    simpa only [c, e] using
      cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
  by_cases hB0 : B = 0
  · have hD0 : D = 0 := by
      rw [hDrec, hB0, mul_zero, smul_zero]
    have hrow0 := hsys.rowZero
    rw [hl, hbeta, hdelta, hzeta, hB0, hD0] at hrow0
    exact fiveToSix_deZero_B_zero_terminal_impossible68 alpha gamma epsilon
      eta terminal A C0 E hterminal hrow0
  · obtain ⟨i4, hi4raw⟩ := hsys.firstFour
    have hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B)) e = C i4 := by
      have h := hi4raw
      rw [hl, hbeta, hdelta, hzeta, hCrec] at h
      rw [hErec, firstIntegralFourPolynomial68_cubicCoordinates, hDrec] at h
      simpa [c, e] using h
    have he : e.natDegree ≤ 0 :=
      fiveToSix_dZero_B_constant_forces_e_constant68 gamma epsilon i4 A B c e
        hB hB0 hi4
    have hDrec0 : D = (1 / 3 : k) • (A * B) + (0 : k[X]) := by
      rw [add_zero]
      exact hDrec
    have hrow0 := hsys.rowZero
    rw [hCrec, hDrec0, hErec, cubicRowZeroPolynomial68_residualSplit,
      hl, hbeta, hdelta, hzeta] at hrow0
    exact fiveToSix_dZero_eConstant_B_constant_rowZero_impossible68
      alpha gamma epsilon eta terminal A B c (0 : k[X]) e hterminal hA hB
      hB0 rfl he hrow0

/-- Source `d=e=0` is empty for every `B`, once `deg A ≥ 2`. -/
theorem fiveToSix_deZero_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A B D = 0)
    (he : cubicEDefectPolynomial68 A C0 E = 0)
    (hA : 2 ≤ A.natDegree) : False := by
  by_cases hB0 : B = 0
  · exact fiveToSix_deZero_B_zero_or_nonconstant_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl hbeta hdelta hzeta hd he (Or.inl hB0)
  · by_cases hBpos : 1 ≤ B.natDegree
    · exact fiveToSix_deZero_B_zero_or_nonconstant_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hl hbeta hdelta hzeta hd he (Or.inr hBpos)
    · have hB : B.natDegree ≤ 0 := by omega
      exact fiveToSix_dZero_B_constant_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hl hbeta hdelta hzeta hd hB hA

/-- The expanded top `A_(2n) ≠ 0` pins the source degree `deg A = n/30`. -/
theorem fiveToSix_source_A_natDegree_eq68 (A B C0 D E : k[X])
    (ha : (expand k 60 A).coeff (2 * weightedRadius68 A B C0 D E) ≠ 0)
    (hA : (expand k 60 A).natDegree ≤
      2 * weightedRadius68 A B C0 D E) :
    A.natDegree = weightedRadius68 A B C0 D E / 30 := by
  let n := weightedRadius68 A B C0 D E
  have hAe : (expand k 60 A).natDegree = 2 * n :=
    le_antisymm hA (le_natDegree_of_ne_zero ha)
  have hmul : 60 * A.natDegree = 2 * n := by
    have h := hAe
    rw [natDegree_expand, mul_comm] at h
    exact h
  have h2 : 2 * (30 * A.natDegree) = 2 * n := by
    convert hmul using 1
    ring
  have hdeg : 30 * A.natDegree = n :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) h2
  change A.natDegree = n / 30
  rw [hdeg.symm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 30)]

/-- Expanded `B` of degree `< 60` is a source constant. -/
theorem fiveToSix_source_B_constant_of_expanded_lt_sixty68 (B : k[X])
    (hB : (expand k 60 B).natDegree < 60) :
    B.natDegree = 0 := by
  have : 60 * B.natDegree < 60 := by
    have h := hB
    rw [natDegree_expand, mul_comm] at h
    exact h
  omega

/-- Window `5n < 2g` and `n ≤ 120` force the expanded `B` bound below `60`. -/
theorem fiveToSix_gap_lt_sixty_of_le_oneTwenty68 (n g : ℕ)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n) (hn : n ≤ 120) :
    3 * n - g < 60 := by
  obtain ⟨hw5, hw6⟩ := hwindow
  omega

/-- Named residual after deleting the vanishing `d=0` child of the
terminal-zero packet: an honest beyond-wall cusp on the aligned family,
or the original at-wall large terminal all-nonzero cusp (the assembly
Prop of the same name is not imported here, so the at-wall disjunct is
written in place). -/
def FiveToSixTerminalTailOpenResidual68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  (60 ∣ n ∧ 60 ∣ g ∧ zeta = 0 ∧
      ∃ j, 0 < j ∧ 60 * j ≤ g - 2 * n ∧
        FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g + 60 * j)) ∨
    (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
      d.natDegree ≤ g - 2 * n ∧ e.natDegree ≤ g - n ∧ zeta = 0 ∧
      FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g))

set_option maxHeartbeats 25000000 in
/-- The arithmetic wall `n=30` is already empty, independently of the
terminal-zero coefficients. -/
theorem fiveToSix_terminalZero_n30_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hn : weightedRadius68 A B C0 D E = 30) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee
    (secondaryDDefectPolynomial68 Ae Be De) n g at hglobal
  rcases hglobal with
    ⟨hgt5, hle6, _hfour, _hthree, _hn30, hg30, hnLarge, _⟩
  change n = 30 at hn
  have hg : g = 90 := by omega
  exact maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys (by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
        (⟨hn, hg⟩ : n = 30 ∧ g = 90))

/-- On `n ≤ 120`, source `d=0` with the terminal-zero parameter vanishing
is `False`: the expanded `B` bound is `< 60`, so source `B` is constant. -/
theorem fiveToSix_terminalZero_source_dZero_le_oneTwenty_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A B D = 0)
    (hnle : weightedRadius68 A B C0 D E ≤ 120)
    (hn60 : 60 ≤ weightedRadius68 A B C0 D E) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hAdeg : A.natDegree = n / 30 :=
    fiveToSix_source_A_natDegree_eq68 A B C0 D E
      (by simpa only [n, Ae] using data.ha)
      (by simpa only [n, Ae] using data.hA)
  have hA : 2 ≤ A.natDegree := by
    change 60 ≤ n at hn60
    have : 2 ≤ n / 30 := by omega
    rwa [hAdeg]
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee
    (secondaryDDefectPolynomial68 Ae Be De) n g at hglobal
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hgap : 3 * n - g < 60 :=
    fiveToSix_gap_lt_sixty_of_le_oneTwenty68 n g hwindow hnle
  have hBexp : Be.natDegree < 60 :=
    lt_of_le_of_lt data.hB hgap
  have hB : B.natDegree = 0 :=
    fiveToSix_source_B_constant_of_expanded_lt_sixty68 B
      (by simpa only [Be] using hBexp)
  exact fiveToSix_dZero_B_constant_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hl hbeta hdelta hzeta hd (le_of_eq hB) hA

#print axioms fiveToSix_I4_of_de_zero68
#print axioms fiveToSix_deZero_B_nonconstant_I4_impossible68
#print axioms fiveToSix_U_of_B_D_zeta_zero68
#print axioms fiveToSix_deZero_B_zero_terminal_impossible68
#print axioms eq_zero_of_natDegree_le_zero_coeff_zero68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_beyondWall_offset68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_beyondWall_offset68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_beyondWall_offset68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_beyondWall_offset68
#print axioms fiveToSix_terminal_index_d68
#print axioms fiveToSix_terminal_index_d_dvd68
#print axioms fiveToSix_sixty_mul_sub_sub68
#print axioms fiveToSix_sixty_mul_sub_sub_one68
#print axioms fiveToSix_le_of_sixty_mul68
#print axioms fiveToSix_room_implies_G68
#print axioms polynomialSecondaryResidualBeyondWallFace68_offset
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWall_iterate68
#print axioms coeff_mul_derivative_top68
#print axioms fiveToSix_deZero_B_zero_or_nonconstant_impossible68
#print axioms fiveToSix_I4_of_d_zero68
#print axioms fiveToSix_dZero_B_constant_forces_e_constant68
#print axioms fiveToSix_dZero_eConstant_B_constant_rowZero_impossible68
#print axioms fiveToSix_dZero_B_constant_impossible68
#print axioms fiveToSix_deZero_impossible68
#print axioms fiveToSix_source_A_natDegree_eq68
#print axioms fiveToSix_source_B_constant_of_expanded_lt_sixty68
#print axioms fiveToSix_gap_lt_sixty_of_le_oneTwenty68
#print axioms fiveToSix_terminalZero_n30_impossible68
#print axioms fiveToSix_terminalZero_source_dZero_le_oneTwenty_impossible68

end FiveToSixTerminalTailFalse68

end Max11DegreeRoutes
