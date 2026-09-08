import Sol68LaterDeepLowerOpenDoubleFiveWallStaggeredNinetyAlgebraScratch

/-! # Source closure of the offset-ninety degenerate face -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallStaggeredNinetySource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 90 < g) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g - 90 := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 10000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hload : 90 < 4 * n - 2 * g) (hg : 90 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - 90)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 91 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c D e rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 0 gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E0 := Ec + Er
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB (hc.trans (by omega))
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB (hc.trans (by omega)) hD (he.trans (by omega))
  have hVlow : Vlow.natDegree ≤ 4 * n - g :=
    cubicLoadVAlphaLowPolynomial68_degree_le_fourRadius_of_doubleFiveWall
      gamma delta epsilon eta A B c D n g hn hwall hA hB
      (hc.trans (by omega))
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g - 90 := by
    simp only [Er]
    compute_degree
    omega
  have hE0 : E0.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - 91) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 91 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 3 * g - 91) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - 91 :=
    hbound (2 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - 91 :=
    hbound (4 * n - g - 90) (6 * n - g - 90) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - 91 :=
    hbound (2 * n) (6 * n - g - 90) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er ((natDegree_smul_le _ A).trans hA) hEr
  have h4 : ((C epsilon : k[X]) * derivative E0).natDegree <
      12 * n - 3 * g - 91 :=
    hbound 0 (6 * n) (by omega) (by omega) _ E0 heps hE0
  have h5 : (C0c * derivative Vlow).natDegree <
      12 * n - 3 * g - 91 :=
    hbound (4 * n) (4 * n - g) (by omega) (by omega)
      C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - 91 :=
    hbound (4 * n - g - 90) (6 * n - g) (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 3 * g - 91 :=
    hbound (5 * n - g) (2 * n) (by omega) (by omega) D Ur hD hUr
  simp only [cubicLoadRowOneDeepGapRestPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  change (Ur * derivative D +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • ((C epsilon : k[X]) * derivative E0) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1
              (deepGap_natDegree_smul_lt68 (2 : k) h2))
              (deepGap_natDegree_smul_lt68 (2 : k) h3))
            (deepGap_natDegree_smul_lt68 (2 : k) h4))
          (deepGap_natDegree_smul_lt68 (2 : k) h5))
        (deepGap_natDegree_smul_lt68 (2 : k) h6)) h7

/-- On a staggered thirty-boundary, after the offset-thirty coefficient is
killed, sixty-support forces the degree below the next active edge, namely
offset ninety. -/
theorem natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
    (q : k[X]) (base : ℕ) (hbase : 30 ∣ base) (hstaggered : ¬60 ∣ base)
    (hninety : 90 ≤ base) (hdeg : (expand k 60 q).natDegree ≤ base - 30)
    (hedge : (expand k 60 q).coeff (base - 30) = 0) :
    (expand k 60 q).natDegree ≤ base - 90 := by
  by_cases hzero : expand k 60 q = 0
  · rw [hzero, natDegree_zero]
    omega
  · have hlead : (expand k 60 q).coeff
        (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hzero
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      expanded_coeff_ne_zero_dvd_sixty68 q (expand k 60 q).natDegree hlead
    have hne : (expand k 60 q).natDegree ≠ base - 30 := by
      intro heq
      exact hlead (heq ▸ hedge)
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hdiv
    omega

/-- On the exact double-five wall, the expanded leading coefficients force
`n` onto the ninety-lattice.  Consequently either the first lattice point
`(n,g)=(90,150)` is met, or the offset-ninety row load lies strictly below
the coefficient used below. -/
theorem doubleFiveWall_ninety_lattice_load_split68
    (n g : ℕ) (hn : 0 < n) (hndiv : 90 ∣ n) (hwall : 3 * g = 5 * n) :
    (n = 90 ∧ g = 150) ∨ 90 < 4 * n - 2 * g := by
  obtain ⟨u, hu⟩ := hndiv
  by_cases hone : u = 1
  · left
    constructor <;> omega
  · right
    have hu2 : 2 ≤ u := by omega
    omega

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateOffsetNinety68
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
      2 * g ≤ h)
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
      3 * g = 5 * n)
    (hdegenerate :
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
      ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0)
    (hcStaggered :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬60 ∣ 4 * n - g)
    (hdStaggered :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬60 ∣ 5 * n - 2 * g)
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
      90 < 4 * n - 2 * g) :
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
    ce.coeff (4 * n - g - 90) = 0 ∧
      d.coeff (5 * n - 2 * g - 90) = 0 := by
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
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change ¬60 ∣ 4 * n - g at hcStaggered
  change ¬60 ∣ 5 * n - 2 * g at hdStaggered
  change 90 < 4 * n - 2 * g at hload
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have next :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ at next
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have ht := bounds.1
    change d.natDegree ≤ 5 * n - h at ht
    rw [next.1] at ht
    exact ht
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [next.1] at ht
    exact ht
  have hAdiv := expanded_coeff_ne_zero_dvd_sixty68 A (2 * n) ha
  have hBdiv := expanded_coeff_ne_zero_dvd_sixty68 B (3 * n - g)
    hdegenerate.2.1
  have hndiv : 90 ∣ n := by
    obtain ⟨u, hu⟩ := hAdiv
    obtain ⟨v, hv⟩ := hBdiv
    refine ⟨u / 3, ?_⟩
    omega
  have hgdiv : 30 ∣ g := by
    obtain ⟨u, hu⟩ := hndiv
    refine ⟨5 * u, ?_⟩
    omega
  have hcbase : 30 ∣ 4 * n - g := by
    obtain ⟨u, hu⟩ := hndiv
    obtain ⟨v, hv⟩ := hgdiv
    refine ⟨12 * u - v, ?_⟩
    omega
  have hdbaseDiv : 30 ∣ 5 * n - 2 * g := by
    obtain ⟨u, hu⟩ := hndiv
    obtain ⟨v, hv⟩ := hgdiv
    refine ⟨15 * u - 2 * v, ?_⟩
    omega
  have hgap : 60 < g := by
    have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
      simpa only [ee, Ae, Ce, Ee] using
        expand_cubicEDefectPolynomial68 60 A C0 E
    apply doubleFiveWall_gap_gt_sixty_of_expanded_e_top68 A
      (cubicEDefectPolynomial68 A C0 E) n g hn hwall ha
    rw [← heexpand]
    exact hdegenerate.2.2.2
  have hceexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simp only [d, Ae, Be, De, secondaryDDefectPolynomial68,
      map_sub, expand_mul, Polynomial.smul_eq_C_mul, map_mul, expand_C]
  have hz30 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateOffsetThirty68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
  change ce.coeff (4 * n - g - 30) = 0 ∧
      d.coeff (5 * n - 2 * g - 30) = 0 at hz30
  have hc30deg : ce.natDegree ≤ 4 * n - g - 30 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (cubicCDefectPolynomial68 A C0) (4 * n - g) hcbase (by omega)
    · simpa only [← hceexpand] using secondary.2.2.1
    · rw [← hceexpand]
      exact hdegenerate.1
  have hd30deg : d.natDegree ≤ 5 * n - 2 * g - 30 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g)
      hdbaseDiv (by omega)
    · simpa only [← hdexpand] using hd2
    · rw [← hdexpand]
      exact hdegenerate.2.2.1
  have hc30 : ce.natDegree ≤ 4 * n - g - 90 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
      (cubicCDefectPolynomial68 A C0) (4 * n - g) hcbase hcStaggered
      (by omega)
    · simpa only [← hceexpand] using hc30deg
    · rw [← hceexpand]
      exact hz30.1
  have hd30 : d.natDegree ≤ 5 * n - 2 * g - 90 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
      (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g)
      hdbaseDiv hdStaggered (by omega)
    · simpa only [← hdexpand] using hd30deg
    · rw [← hdexpand]
      exact hz30.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hD : Dtr.natDegree ≤ 5 * n - g := by
    rw [← hDrec]
    exact secondary.2.2.2.1
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce Dtr ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68
        l beta gamma delta epsilon zeta Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1] at hi3e
    exact hi3e
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 3 * g - 90)) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_double_drop_ninety_of_fiveWall
      Ae Be ce d ee n g hn (by omega) hwall hA secondary.2.1 hc30 hd30 he2,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
        gamma delta epsilon zeta Ae Be ce Dtr ee n g hn (by omega) hwall
        hA secondary.2.1 secondary.2.2.1 hD he2), add_zero] at hcoeff3
  have hidx3 : 10 * n - 3 * g - 90 ≠ 0 := by omega
  simp only [coeff_C, if_neg hidx3] at hcoeff3
  have hi3scalar :
      -Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - 90) -
        Be.coeff (3 * n - g) ^ 2 * ce.coeff (4 * n - g - 90) +
        3 * ce.coeff (4 * n - g - 90) * ee.coeff (6 * n - 2 * g) = 0 := by
    have ht := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination ht
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowPoly : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at hr
    exact polynomialSecondaryResidualRowOne68
      0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee hr
  have hloadOne := cubicLoadRowOnePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
    alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee n g hn hload
    (by omega) hopen hwall hA secondary.2.1 hc30 hD he2
  have hcoeffOne := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 91)) hrowPoly
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hloadOne, add_zero,
    secondaryResidualRowOnePolynomial68_coeff_double_drop_ninety_of_fiveWall
      Ae Be ce d ee n g hn (by omega) hwall hA secondary.2.1 hc30 hd30 he2]
    at hcoeffOne
  have hrowScalar :
      2 * Ae.coeff (2 * n) ^ 2 * Be.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - 90) * (5 * (n : k) - 90) -
        6 * Ae.coeff (2 * n) * ce.coeff (4 * n - g - 90) *
          ee.coeff (6 * n - 2 * g) * (5 * (n : k) - 90) -
        4 * (n : k) * Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 *
          ce.coeff (4 * n - g - 90) = 0 := by
    have ht := (mul_eq_zero.mp hcoeffOne).resolve_left (by norm_num)
    have hcastM : (((5 * n - 90 : ℕ) : k)) = 5 * (n : k) - 90 := by
      rw [Nat.cast_sub (by omega : 90 ≤ 5 * n)]
      push_cast
      rfl
    rw [hcastM] at ht
    exact ht
  exact laterDeepLowerOpenDoubleFiveWall_degenerate_offsetNinety_edges_zero68
    n (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g - 90)) (d.coeff (5 * n - 2 * g - 90))
    (ee.coeff (6 * n - 2 * g)) hn ha hdegenerate.2.1 hi3scalar hrowScalar

#print axioms secondaryLoadInvariantThreePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
#print axioms cubicLoadRowOnePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
#print axioms natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
#print axioms doubleFiveWall_ninety_lattice_load_split68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateOffsetNinety68

end LaterDeepLowerOpenDoubleFiveWallStaggeredNinetySource68

end Max11DegreeRoutes
