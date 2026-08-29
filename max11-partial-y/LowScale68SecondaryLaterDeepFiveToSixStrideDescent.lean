import LowScale68SecondaryLaterDeepFiveToSixNonzeroEdge

/-! # Expansion-stride descent in the later-deep five-to-six chamber

The canonical source polynomials are expanded by `60`.  The nonzero top
`A` edge first forces `30 ∣ n`; secondary-radius attainment then forces
`30 ∣ g`.  Hence both translated-defect boundary indices are multiples of
`30`, while every nonzero translated-defect coefficient still has index a
multiple of `60`.  This excludes every displacement `1 ≤ s < 30` and drops
both translated defects by thirty degrees.

The number `30` is sharp for support alone: at displacement `30` the two
residue classes modulo `60` can meet.  The final arithmetic lemma records
the only early I4 load wall, namely `n = 30`, `g = 90`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixStrideDescent68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A `60`-expanded coefficient whose reference boundary is divisible by
`30` vanishes at every strictly positive displacement below `30`. -/
theorem coeff_expand_zero_before_thirty_of_boundary_dvd_thirty68
    (q : k[X]) (base s : ℕ) (hbase : 30 ∣ base)
    (hspos : 1 ≤ s) (hslt : s < 30) (hsle : s ≤ base) :
    (expand k 60 q).coeff (base - s) = 0 := by
  by_contra hne
  have hdiv : 60 ∣ base - s :=
    coeff_expand_ne_zero_dvd68 60 (by norm_num) q (base - s) hne
  obtain ⟨u, hu⟩ := hbase
  obtain ⟨v, hv⟩ := hdiv
  omega

/-- The leading expanded `A` edge puts the weighted radius on the
thirty-lattice. -/
theorem expandedA_top_forces_thirty_dvd_radius68
    (A : k[X]) (n : ℕ)
    (ha : (expand k 60 A).coeff (2 * n) ≠ 0) : 30 ∣ n := by
  have hdiv : 60 ∣ 2 * n :=
    coeff_expand_ne_zero_dvd68 60 (by norm_num) A (2 * n) ha
  obtain ⟨u, hu⟩ := hdiv
  refine ⟨u, ?_⟩
  omega

/-- Once either the `B` or depressed-`C` secondary boundary is attained,
the secondary gap lies on the same thirty-lattice as the radius. -/
theorem expanded_secondary_top_forces_thirty_dvd_gap68
    (A B C0 : k[X]) (n g : ℕ) (hng : 30 ∣ n) (hg : g ≤ 3 * n)
    (htop :
      (expand k 60 B).coeff (3 * n - g) ≠ 0 ∨
      (cubicCDefectPolynomial68 (expand k 60 A) (expand k 60 C0)).coeff
        (4 * n - g) ≠ 0) :
    30 ∣ g := by
  obtain ⟨u, hu⟩ := hng
  rcases htop with hb | hc
  · have hdiv : 60 ∣ 3 * n - g :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) B (3 * n - g) hb
    obtain ⟨v, hv⟩ := hdiv
    refine ⟨3 * u - 2 * v, ?_⟩
    omega
  · have hcexpand := expand_cubicCDefectPolynomial68 60 A C0
    rw [hcexpand] at hc
    have hdiv : 60 ∣ 4 * n - g :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num)
        (cubicCDefectPolynomial68 A C0) (4 * n - g) hc
    obtain ⟨v, hv⟩ := hdiv
    refine ⟨4 * u - 2 * v, ?_⟩
    omega

/-- In the five-to-six chamber, the main family and secondary attainment
force at least one of the expanded `B` and depressed-`C` top edges to be
nonzero. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
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
    Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
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
  rcases hsecondary.2.2.2.2.2 with hb | hc | hd | he
  · exact Or.inl hb
  · exact Or.inr hc
  · left
    intro hb0
    have hthreeD : 3 * De.coeff (5 * n - g) = 0 := by
      rw [← hmain.2, hb0, mul_zero]
    have hD0 : De.coeff (5 * n - g) = 0 := by
      exact (mul_eq_zero.mp hthreeD).resolve_left (by norm_num)
    exact hd hD0
  · exact False.elim (he hmain.1)

/-- Source-facing expansion descent.  Both translated defects vanish at
every displacement `1,…,29`, and therefore their degrees fall by thirty
from the old secondary boundaries. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirtyDescent68
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
    30 ∣ n ∧ 30 ∣ g ∧
      (∀ s, 1 ≤ s → s < 30 →
        d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0) ∧
      d.natDegree ≤ 5 * n - g - 30 ∧
      ee.natDegree ≤ 6 * n - g - 30 := by
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
  change 30 ∣ n ∧ 30 ∣ g ∧
    (∀ s, 1 ≤ s → s < 30 →
      d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - s) = 0) ∧
    d.natDegree ≤ 5 * n - g - 30 ∧
    ee.natDegree ≤ 6 * n - g - 30
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn30 : 30 ∣ n :=
    expandedA_top_forces_thirty_dvd_radius68 A n data.ha
  have htop :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 at htop
  have hg30 : 30 ∣ g :=
    expanded_secondary_top_forces_thirty_dvd_gap68 A B C0 n g hn30
      (by omega) htop
  have hbaseD : 30 ∣ 5 * n - g := by
    obtain ⟨u, hu⟩ := hn30
    obtain ⟨v, hv⟩ := hg30
    refine ⟨5 * u - v, ?_⟩
    omega
  have hbaseE : 30 ∣ 6 * n - g := by
    obtain ⟨u, hu⟩ := hn30
    obtain ⟨v, hv⟩ := hg30
    refine ⟨6 * u - v, ?_⟩
    omega
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hcoeff : ∀ s, 1 ≤ s → s < 30 →
      d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - s) = 0 := by
    intro s hspos hslt
    have hsD : s ≤ 5 * n - g := by
      obtain ⟨u, hu⟩ := hn30
      have hu1 : 1 ≤ u := by omega
      omega
    have hsE : s ≤ 6 * n - g := by omega
    constructor
    · rw [hdexpand]
      exact coeff_expand_zero_before_thirty_of_boundary_dvd_thirty68
        (secondaryDDefectPolynomial68 A B D) (5 * n - g) s
        hbaseD hspos hslt hsD
    · rw [heexpand]
      exact coeff_expand_zero_before_thirty_of_boundary_dvd_thirty68
        (cubicEDefectPolynomial68 A C0 E) (6 * n - g) s
        hbaseE hspos hslt hsE
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_gapSuccPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ _ at hdrops
  have hdegD : d.natDegree ≤ 5 * n - g - 30 := by
    by_cases hd0 : d = 0
    · rw [hd0, natDegree_zero]
      obtain ⟨u, hu⟩ := hn30
      have hu1 : 1 ≤ u := by omega
      omega
    · have hlead0 : d.coeff d.natDegree ≠ 0 := by
        rw [coeff_natDegree, leadingCoeff]
        exact Polynomial.leadingCoeff_ne_zero.mpr hd0
      have hlead : (expand k 60
          (secondaryDDefectPolynomial68 A B D)).coeff d.natDegree ≠ 0 := by
        rw [← hdexpand]
        exact hlead0
      have hdiv : 60 ∣ d.natDegree :=
        coeff_expand_ne_zero_dvd68 60 (by norm_num)
          (secondaryDDefectPolynomial68 A B D) d.natDegree hlead
      obtain ⟨u, hu⟩ := hbaseD
      obtain ⟨v, hv⟩ := hdiv
      omega
  have hdegE : ee.natDegree ≤ 6 * n - g - 30 := by
    by_cases he0 : ee = 0
    · rw [he0, natDegree_zero]
      obtain ⟨u, hu⟩ := hn30
      have hu1 : 1 ≤ u := by omega
      omega
    · have hlead0 : ee.coeff ee.natDegree ≠ 0 := by
        rw [coeff_natDegree, leadingCoeff]
        exact Polynomial.leadingCoeff_ne_zero.mpr he0
      have hlead : (expand k 60
          (cubicEDefectPolynomial68 A C0 E)).coeff ee.natDegree ≠ 0 := by
        rw [← heexpand]
        exact hlead0
      have hdiv : 60 ∣ ee.natDegree :=
        coeff_expand_ne_zero_dvd68 60 (by norm_num)
          (cubicEDefectPolynomial68 A C0 E) ee.natDegree hlead
      obtain ⟨u, hu⟩ := hbaseE
      obtain ⟨v, hv⟩ := hdiv
      omega
  exact ⟨hn30, hg30, hcoeff, hdegD, hdegE⟩

/-- At the first arithmetically possible displacement, attainment of the
`B` top still kills the translated `D` edge, while attainment of the
depressed-`C` top kills the translated `E` edge.  Thus a surviving offset-30
edge must be crossed: `E` over the `B` branch or `D` over the `C` branch. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirty_oneSided68
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
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (Be.coeff (3 * n - g) ≠ 0 →
        d.coeff (5 * n - g - 30) = 0) ∧
      (ce.coeff (4 * n - g) ≠ 0 →
        ee.coeff (6 * n - g - 30) = 0) := by
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
  change (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    (Be.coeff (3 * n - g) ≠ 0 → d.coeff (5 * n - g - 30) = 0) ∧
    (ce.coeff (4 * n - g) ≠ 0 → ee.coeff (6 * n - g - 30) = 0)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn30 : 30 ∣ n :=
    expandedA_top_forces_thirty_dvd_radius68 A n data.ha
  have htop :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 at htop
  refine ⟨htop, ?_, ?_⟩
  · intro hb
    by_contra hd
    have hs30 : 30 ≤ 5 * n - g := by
      obtain ⟨u, hu⟩ := hn30
      have hu1 : 1 ≤ u := by omega
      omega
    have hdiv := expandedSecondaryDActiveEdge_stride_dvd68
      60 (by norm_num) A B D n g 30 (by omega) hs30
      data.ha hb hd
    norm_num at hdiv
  · intro hc
    have hAdiv : 60 ∣ 2 * n :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) A (2 * n) data.ha
    change (cubicCDefectPolynomial68 (expand k 60 A)
      (expand k 60 C0)).coeff (4 * n - g) ≠ 0 at hc
    have hcexpand := expand_cubicCDefectPolynomial68 60 A C0
    rw [hcexpand] at hc
    have hCdiv : 60 ∣ 4 * n - g :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num)
        (cubicCDefectPolynomial68 A C0) (4 * n - g) hc
    have hbase : 60 ∣ 6 * n - g := by
      have hadd := Nat.dvd_add hAdiv hCdiv
      have hi : 2 * n + (4 * n - g) = 6 * n - g := by omega
      simpa only [hi] using hadd
    have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
      simpa only [ee, Ae, Ce, Ee] using
        expand_cubicEDefectPolynomial68 60 A C0 E
    by_contra he
    rw [heexpand] at he
    have hedge : 60 ∣ 6 * n - g - 30 :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num)
        (cubicEDefectPolynomial68 A C0 E) (6 * n - g - 30) he
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hedge
    omega

/-- The homogeneous I4 face at the first possible stride displacement. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_gap_thirty_fiveToSix
    (B c d e : k[X]) (n g : ℕ) (hnBig : 30 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 30)
    (he : e.natDegree ≤ 6 * n - g - 30) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - 30) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 30) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 30)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - 30 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - 30) hB he
  have hBei : (3 * n - g) + (6 * n - g - 30) =
      9 * n - 2 * g - 30 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - 30) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - 30) =
      9 * n - 2 * g - 30 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Above the earliest radius wall, all old-weight I4 loads lie below the
offset-30 face. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_gap_thirty_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hnBig : 30 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 30)
    (he : e.natDegree ≤ 6 * n - g - 30) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - 30) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 30) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 30)) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_gap_thirty_fiveToSix
      B c d e n g hnBig hwindow hB hc hd he]
  have hloadA : (zeta • A).natDegree < 9 * n - 2 * g - 30 := by
    compute_degree
    omega
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - 30 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - 30 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadA,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

/-- Away from the earliest load wall, I4 couples the two one-sided support
zeros and kills both translated defects at displacement `30`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirty_bothZero_of_largeRadius68
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
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hnBig : 30 < weightedRadius68 A B C0 D E) :
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
    d.coeff (5 * n - g - 30) = 0 ∧
      ee.coeff (6 * n - g - 30) = 0 := by
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
  change 30 < n at hnBig
  change d.coeff (5 * n - g - 30) = 0 ∧
    ee.coeff (6 * n - g - 30) = 0
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
    d.natDegree ≤ 5 * n - g - 30 ∧
    ee.natDegree ≤ 6 * n - g - 30 at hdesc
  have hone :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirty_oneSided68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    (Be.coeff (3 * n - g) ≠ 0 → d.coeff (5 * n - g - 30) = 0) ∧
    (ce.coeff (4 * n - g) ≠ 0 → ee.coeff (6 * n - g - 30) = 0) at hone
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
  rw [hdelta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (9 * n - 2 * g - 30)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_gap_thirty_fiveToSix
    gamma epsilon zeta Ae Be ce d ee n g hnBig hwindow data.hA data.hB
    data.hc hdesc.2.2.2.1 hdesc.2.2.2.2] at hcoeff
  have htarget : 9 * n - 2 * g - 30 ≠ 0 := by omega
  simp only [coeff_C, if_neg htarget] at hcoeff
  have hincidence :
      Be.coeff (3 * n - g) * ee.coeff (6 * n - g - 30) +
        ce.coeff (4 * n - g) * d.coeff (5 * n - g - 30) = 0 := by
    have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hcoeff).resolve_left hscalar
  rcases hone.1 with hb | hc
  · have hd0 := hone.2.1 hb
    have he0 : ee.coeff (6 * n - g - 30) = 0 := by
      rw [hd0, mul_zero, add_zero] at hincidence
      exact (mul_eq_zero.mp hincidence).resolve_left hb
    exact ⟨hd0, he0⟩
  · have he0 := hone.2.2 hc
    have hd0 : d.coeff (5 * n - g - 30) = 0 := by
      rw [he0, mul_zero, zero_add] at hincidence
      exact (mul_eq_zero.mp hincidence).resolve_left hc
    exact ⟨hd0, he0⟩

/-- At displacement `30`, the I4 target `9n-2g-30` is still strictly above
the `zeta*A` load when `n>30`.  If it is not, lattice arithmetic collapses
the chamber to the single earliest wall `n=30`, `g=90`, where the target is
exactly `2n`. -/
theorem fiveToSix_strideThirty_i4_cutoff_or_earliest_wall68
    (n g : ℕ) (hn : 0 < n) (hn30 : 30 ∣ n) (hg30 : 30 ∣ g)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
    (30 < n ∧ 2 * n < 9 * n - 2 * g - 30) ∨
      (n = 30 ∧ g = 90 ∧ 9 * n - 2 * g - 30 = 2 * n) := by
  obtain ⟨u, hu⟩ := hn30
  obtain ⟨v, hv⟩ := hg30
  by_cases hsmall : n = 30
  · right
    have hg : g = 90 := by omega
    exact ⟨hsmall, hg, by omega⟩
  · left
    constructor
    · omega
    · omega

/-- Complete pre-stride descent.  Except at the unique earliest I4 load wall,
both translated defects vanish at every displacement strictly below `60`
and their degrees drop by the full expansion stride. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideSixty_or_earliestWall68
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
    (n = 30 ∧ g = 90) ∨
      (30 < n ∧
        (∀ s, 1 ≤ s → s < 60 →
          d.coeff (5 * n - g - s) = 0 ∧
          ee.coeff (6 * n - g - s) = 0) ∧
        d.natDegree ≤ 5 * n - g - 60 ∧
        ee.natDegree ≤ 6 * n - g - 60) := by
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
  change (n = 30 ∧ g = 90) ∨
    (30 < n ∧
      (∀ s, 1 ≤ s → s < 60 →
        d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0) ∧
      d.natDegree ≤ 5 * n - g - 60 ∧
      ee.natDegree ≤ 6 * n - g - 60)
  have hdesc :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirtyDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 30 ∣ n ∧ 30 ∣ g ∧ _ ∧
    d.natDegree ≤ 5 * n - g - 30 ∧
    ee.natDegree ≤ 6 * n - g - 30 at hdesc
  by_cases hnwall : n = 30
  · left
    obtain ⟨v, hv⟩ := hdesc.2.1
    exact ⟨hnwall, by omega⟩
  · right
    have hnBig : 30 < n := by
      obtain ⟨u, hu⟩ := hdesc.1
      omega
    have hthirty :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirty_bothZero_of_largeRadius68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by simpa only [n] using hnBig)
    change d.coeff (5 * n - g - 30) = 0 ∧
      ee.coeff (6 * n - g - 30) = 0 at hthirty
    have hbaseD : 30 ∣ 5 * n - g := by
      obtain ⟨u, hu⟩ := hdesc.1
      obtain ⟨v, hv⟩ := hdesc.2.1
      refine ⟨5 * u - v, ?_⟩
      omega
    have hbaseE : 30 ∣ 6 * n - g := by
      obtain ⟨u, hu⟩ := hdesc.1
      obtain ⟨v, hv⟩ := hdesc.2.1
      refine ⟨6 * u - v, ?_⟩
      omega
    have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
      simpa only [d, Ae, Be, De] using
        secondaryDDefectPolynomial68_expand 60 A B D
    have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
      simpa only [ee, Ae, Ce, Ee] using
        expand_cubicEDefectPolynomial68 60 A C0 E
    have hdegD : d.natDegree ≤ 5 * n - g - 60 := by
      by_cases hd0 : d = 0
      · rw [hd0, natDegree_zero]
        omega
      · have hlead0 : d.coeff d.natDegree ≠ 0 := by
          rw [coeff_natDegree, leadingCoeff]
          exact Polynomial.leadingCoeff_ne_zero.mpr hd0
        have hlead : (expand k 60
            (secondaryDDefectPolynomial68 A B D)).coeff d.natDegree ≠ 0 := by
          rw [← hdexpand]
          exact hlead0
        have hdiv : 60 ∣ d.natDegree :=
          coeff_expand_ne_zero_dvd68 60 (by norm_num)
            (secondaryDDefectPolynomial68 A B D) d.natDegree hlead
        have hne : d.natDegree ≠ 5 * n - g - 30 := by
          intro heq
          apply hlead0
          rw [heq]
          exact hthirty.1
        obtain ⟨u, hu⟩ := hbaseD
        obtain ⟨v, hv⟩ := hdiv
        omega
    have hdegE : ee.natDegree ≤ 6 * n - g - 60 := by
      by_cases he0 : ee = 0
      · rw [he0, natDegree_zero]
        omega
      · have hlead0 : ee.coeff ee.natDegree ≠ 0 := by
          rw [coeff_natDegree, leadingCoeff]
          exact Polynomial.leadingCoeff_ne_zero.mpr he0
        have hlead : (expand k 60
            (cubicEDefectPolynomial68 A C0 E)).coeff ee.natDegree ≠ 0 := by
          rw [← heexpand]
          exact hlead0
        have hdiv : 60 ∣ ee.natDegree :=
          coeff_expand_ne_zero_dvd68 60 (by norm_num)
            (cubicEDefectPolynomial68 A C0 E) ee.natDegree hlead
        have hne : ee.natDegree ≠ 6 * n - g - 30 := by
          intro heq
          apply hlead0
          rw [heq]
          exact hthirty.2
        obtain ⟨u, hu⟩ := hbaseE
        obtain ⟨v, hv⟩ := hdiv
        omega
    have hcoeff : ∀ s, 1 ≤ s → s < 60 →
        d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0 := by
      intro s hspos hslt
      constructor
      · apply coeff_eq_zero_of_natDegree_lt
        omega
      · apply coeff_eq_zero_of_natDegree_lt
        omega
    exact ⟨hnBig, hcoeff, hdegD, hdegE⟩

end LaterDeepFiveToSixStrideDescent68

#print axioms coeff_expand_zero_before_thirty_of_boundary_dvd_thirty68
#print axioms expandedA_top_forces_thirty_dvd_radius68
#print axioms expanded_secondary_top_forces_thirty_dvd_gap68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirtyDescent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirty_oneSided68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_gap_thirty_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_gap_thirty_fiveToSix
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirty_bothZero_of_largeRadius68
#print axioms fiveToSix_strideThirty_i4_cutoff_or_earliest_wall68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideSixty_or_earliestWall68

end Max11DegreeRoutes
