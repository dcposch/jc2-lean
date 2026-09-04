import Sol68FiveToSixCuspConsumerScratch

/-! # Large aligned consumer for the five-to-six terminal zero packet

The cusp consumer leaves the terminal zero packet or the large cusp
residual.  In the large aligned family `120 < n`, `60 ∣ n`, `60 ∣ g` the
zero packet advances one full lattice stride beyond the load wall: the
wall load `zeta * A_top` is dead because the packet pins `zeta = 0`, so
the I4 and I3 coefficients at degrees `2n - 60` and `3n - 60` are the
exact load-free incidence face at offset `7n - 2g + 60`.  The verified
attainment split then classifies the beyond-wall edge: either both new
coefficients vanish again, giving the smallest exact next recurrence, or
the edge is an honest aligned cusp one stride past the wall.  The large
cusp residual is preserved verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixLargeTerminalZeroConsumer68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous I4 one full lattice stride beyond the load wall on the
large aligned family. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_beyondWall_largeAligned68
    (B c d e : k[X]) (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g) (hbig : 120 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - 60)
    (he : e.natDegree ≤ g - n - 60) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (2 * n - 60) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n - 60) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n - 60)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hB3 : (B ^ 3).natDegree < 2 * n - 60 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (g - n - 60) hB he
  have hBei : (3 * n - g) + (g - n - 60) = 2 * n - 60 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (g - 2 * n - 60) hc hd
  have hcdi : (4 * n - g) + (g - 2 * n - 60) = 2 * n - 60 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Homogeneous I3 at the same beyond-wall stride. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_beyondWall_largeAligned68
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g) (hbig : 120 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - 60)
    (he : e.natDegree ≤ g - n - 60) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (3 * n - 60) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n - 60)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n - 60)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n) (3 * n - g)
    (g - 2 * n - 60) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (g - 2 * n - 60) = 3 * n - 60 := by
    omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 3 * n - 60 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (g - n - 60) hc he
  have hcei : (4 * n - g) + (g - n - 60) = 3 * n - 60 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 3 * n - 60 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal I4 is load-free at the first beyond-wall stride: the packet's
`zeta = 0` kills the wall load, and every remaining load term sits
strictly below degree `2n - 60` on the large aligned lattice. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_beyondWall_largeAligned68
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g) (hbig : 120 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - 60)
    (he : e.natDegree ≤ g - n - 60) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (2 * n - 60) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n - 60) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n - 60)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hloadB : ((2 * epsilon : k) • B).natDegree < 2 * n - 60 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 2 * n - 60 := by
    compute_degree
    omega
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  rw [coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_beyondWall_largeAligned68
      B c d e n g hn hg hbig ⟨hw5, hw6⟩ hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

/-- Literal I3 is also load-free at the first beyond-wall stride. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_beyondWall_largeAligned68
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g) (hbig : 120 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - 60)
    (he : e.natDegree ≤ g - n - 60) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (3 * n - 60) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n - 60)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n - 60)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hloadc : ((2 * epsilon : k) • c).natDegree < 3 * n - 60 := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < 3 * n - 60 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 3 * n - 60 := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  rw [coeff_sub, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_beyondWall_largeAligned68
      A B c d e n g hn hg hbig ⟨hw5, hw6⟩ hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- The two constant first integrals give the exact load-free incidence
face at the first beyond-wall offset of the large aligned family. -/
theorem polynomialSecondaryResidualBeyondWallFace68_largeAligned_fiveToSix
    (gamma epsilon i4 i3 : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g) (hbig : 120 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - 60)
    (he : e.natDegree ≤ g - n - 60)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (g - 2 * n - 60))
      (e.coeff (g - n - 60)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (2 * n - 60)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_beyondWall_largeAligned68
      gamma epsilon A B c d e n g hn hg hbig hwindow hB hc hd he] at hz
    have hj : 2 * n - 60 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (3 * n - 60)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_beyondWall_largeAligned68
      gamma epsilon A B c d e n g hn hg hbig hwindow hA hB hc hd he] at hz
    have hj : 3 * n - 60 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-- Smallest exact successor of the large aligned terminal zero packet:
both supports advance one full lattice stride beyond the load wall, and
the first beyond-wall edge is either again a zero pair or an honest
aligned cusp at offset `7n - 2g + 60`. -/
def FiveToSixLargeTerminalZeroSuccessor68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  d.natDegree ≤ g - 2 * n - 60 ∧ e.natDegree ≤ g - n - 60 ∧ zeta = 0 ∧
    ((d.coeff (g - 2 * n - 60) = 0 ∧ e.coeff (g - n - 60) = 0) ∨
      FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g + 60))

set_option maxHeartbeats 25000000 in
/-- Source-facing beyond-wall edge for the large aligned terminal zero
packet.  The pinned `zeta = 0` deletes the wall load, both supports
stride once more, and the verified attainment split classifies the new
edge exactly. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_largeAligned_beyondWallEdge68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hbig : 120 < weightedRadius68 A B C0 D E)
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
    (hpacket :
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g) :
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
    FiveToSixLargeTerminalZeroSuccessor68 zeta Ae Be ce d ee n g := by
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
  change 120 < n at hbig
  change 60 ∣ n at hn60
  change 60 ∣ g at hg60
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  obtain ⟨hdTop, heTop, hzeta, hdZero, heZero⟩ := hpacket
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g at hglobal
  have hw5 : 5 * n < 2 * g := hglobal.1
  have hw6 : 2 * g ≤ 6 * n := hglobal.2.1
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hd60 : d.natDegree ≤ g - 2 * n - 60 := by
    have hidx : 5 * n - g - (7 * n - 2 * g) = g - 2 * n := by omega
    have hidx60 : 5 * n - g - (7 * n - 2 * g + 60) = g - 2 * n - 60 := by
      omega
    rw [hdexpand, ← hidx60]
    refine natDegree_expand_le_sub_next_sixty68
      (secondaryDDefectPolynomial68 A B D) (5 * n - g) (7 * n - 2 * g)
      (by omega) (by omega) ?_ ?_
    · rw [hidx, ← hdexpand]
      exact hdTop
    · rw [hidx, ← hdexpand]
      exact hdZero
  have he60 : ee.natDegree ≤ g - n - 60 := by
    have hidx : 6 * n - g - (7 * n - 2 * g) = g - n := by omega
    have hidx60 : 6 * n - g - (7 * n - 2 * g + 60) = g - n - 60 := by
      omega
    rw [heexpand, ← hidx60]
    refine natDegree_expand_le_sub_next_sixty68
      (cubicEDefectPolynomial68 A C0 E) (6 * n - g) (7 * n - 2 * g)
      (by omega) (by omega) ?_ ?_
    · rw [hidx, ← heexpand]
      exact heTop
    · rw [hidx, ← heexpand]
      exact heZero
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
      hw5 data.hA data.hB data.hc data.hD data.he data.ha hI4
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
  have hface := polynomialSecondaryResidualBeyondWallFace68_largeAligned_fiveToSix
    gamma epsilon i4 i3 Ae Be ce d ee n g hn60 hg60 hbig ⟨hw5, hw6⟩
    data.hA data.hB data.hc hd60 he60 hI4 hi3e
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
        (⟨hw5, hw6⟩ : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n))
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
    (ee.coeff (6 * n - g)) (d.coeff (g - 2 * n - 60))
    (ee.coeff (g - n - 60)) data.ha hold hface
  show FiveToSixLargeTerminalZeroSuccessor68 zeta Ae Be ce d ee n g
  refine ⟨hd60, he60, hzeta, ?_⟩
  rcases hclass with hzero | hcusp
  · exact Or.inl hzero
  · right
    have hidxd : 5 * n - g - (7 * n - 2 * g + 60) = g - 2 * n - 60 := by
      omega
    have hidxe : 6 * n - g - (7 * n - 2 * g + 60) = g - n - 60 := by
      omega
    exact ⟨hcusp.1, hcusp.2.1,
      by rw [hidxd]; exact hcusp.2.2.1,
      by rw [hidxe]; exact hcusp.2.2.2.1,
      hcusp.2.2.2.2⟩

set_option maxHeartbeats 25000000 in
/-- Refined source consumer: the terminal zero packet now carries its own
large aligned beyond-wall advancement, while the large cusp residual
passes through verbatim. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_consume_largeAligned_terminalZero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
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
    (FiveToSixTerminalZeroPacket68 zeta d ee n g ∧
        (120 < n → 60 ∣ n → 60 ∣ g →
          FiveToSixLargeTerminalZeroSuccessor68 zeta Ae Be ce d ee n g)) ∨
      FiveToSixLargeCuspResidual68 zeta Ae Be ce d ee n g := by
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
  have hconsume := integratedPolynomialLowerSystem68_fiveToSix_consume_cusps68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
    FiveToSixLargeCuspResidual68 zeta Ae Be ce d ee n g at hconsume
  rcases hconsume with hzero | hres
  · left
    refine ⟨hzero, fun hbig hn60 hg60 => ?_⟩
    have hstep :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_largeAligned_beyondWallEdge68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n] using hbig)
        (by simpa only [n] using hn60)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hg60)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hzero)
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hstep
  · exact Or.inr hres

#print axioms secondaryResidualInvariantFourPolynomial68_coeff_beyondWall_largeAligned68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_beyondWall_largeAligned68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_beyondWall_largeAligned68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_beyondWall_largeAligned68
#print axioms polynomialSecondaryResidualBeyondWallFace68_largeAligned_fiveToSix
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_largeAligned_beyondWallEdge68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_consume_largeAligned_terminalZero68

end FiveToSixLargeTerminalZeroConsumer68

end Max11DegreeRoutes
