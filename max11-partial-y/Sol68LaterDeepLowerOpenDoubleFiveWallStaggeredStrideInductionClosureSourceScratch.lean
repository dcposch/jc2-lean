import Sol68LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSourceScratch
import Sol68LaterDeepLowerOpenDoubleFiveWallStaggeredNinetySourceScratch

/-! # Uniform staggered-stride closure on the degenerate double-five wall

The fixed offsets 30, 90, and 150 are the first three members of the single
residue class `30 mod 60`.  The source step below only asks that the remaining
expanded boundaries, rather than the offset and the original boundaries, be
divisible by 60.  This is the invariant needed by the staggered lane.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallStaggeredStrideInductionClosureSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem laterDeepLowerOpenDoubleFiveWall_staggered_offset_source_step68
    (alpha gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (qc qd : k[X]) (i3 : k) (n g s : ℕ)
    (hn : 0 < n) (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hspos : 0 < s)
    (hs : s < 5 * n - 2 * g)
    (hcRemain : 60 ∣ 4 * n - g - s)
    (hdRemain : 60 ∣ 5 * n - 2 * g - s)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hd : d.natDegree ≤ 5 * n - 2 * g - s)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hcexpand : c = expand k 60 qc) (hdexpand : d = expand k 60 qd)
    (hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowPoly : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    c.natDegree ≤ 4 * n - g - (s + 60) ∧
      d.natDegree ≤ 5 * n - 2 * g - (s + 60) := by
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 3 * g - s)) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
      A B c d e n g s hn hopen hwall (by omega) hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
        gamma delta epsilon zeta A B c ((1 / 3 : k) • (A * B) + d) e
        n g s hn hopen hwall hs hA hB hc hD he), add_zero] at hcoeff3
  have hidx3 : 10 * n - 3 * g - s ≠ 0 := by omega
  simp only [coeff_C, if_neg hidx3] at hcoeff3
  have hi3scalar :
      -A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - s) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) +
        3 * c.coeff (4 * n - g - s) * e.coeff (6 * n - 2 * g) = 0 := by
    have ht := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination ht
  have hloadOne :=
    cubicLoadRowOnePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
      alpha gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g s hn hopen hwall hs
      hA hB hc hD he
  have hcoeffOne := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - s - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    coeff_eq_zero_of_natDegree_lt hloadOne, add_zero,
    secondaryResidualRowOnePolynomial68_coeff_aligned_offset_of_fiveWall
      A B c d e n g s hn hopen hwall hspos hs hA hB hc hd he]
    at hcoeffOne
  have hrowScalar :
      2 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - s) * (5 * (n : k) - (s : k)) -
        6 * A.coeff (2 * n) * c.coeff (4 * n - g - s) *
          e.coeff (6 * n - 2 * g) * (5 * (n : k) - (s : k)) -
        4 * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g - s) = 0 := by
    have ht := (mul_eq_zero.mp hcoeffOne).resolve_left (by norm_num)
    have hcastM : (((5 * n - s : ℕ) : k)) = 5 * (n : k) - (s : k) := by
      rw [Nat.cast_sub (by omega : s ≤ 5 * n)]
      push_cast
      rfl
    rw [hcastM] at ht
    exact ht
  have edges := laterDeepLowerOpenDoubleFiveWall_degenerate_aligned_offset_edges_zero68
    n s (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g - s)) (d.coeff (5 * n - 2 * g - s))
    (e.coeff (6 * n - 2 * g)) hn (by omega) ha hb hi3scalar hrowScalar
  constructor
  · have ht : c.natDegree ≤ (4 * n - g - s) - 60 := by
      rw [hcexpand]
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        qc (4 * n - g - s) hcRemain (by omega)
      · simpa only [← hcexpand] using hc
      · rw [← hcexpand]
        exact edges.1
    omega
  · have ht : d.natDegree ≤ (5 * n - 2 * g - s) - 60 := by
      rw [hdexpand]
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        qd (5 * n - 2 * g - s) hdRemain (by omega)
      · simpa only [← hdexpand] using hd
      · rw [← hdexpand]
        exact edges.2
    omega

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateStaggeredTerminalDescent68
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
    (hmisaligned :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      (¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g)) :
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
    (∃ j : ℕ, g = 90 + 60 * j) ∧
      ce.natDegree ≤ 4 * n - 2 * g ∧ d.natDegree ≤ 0 := by
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
  change (¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g) at hmisaligned
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
  have hAdiv := expanded_coeff_ne_zero_dvd_sixty68 A (2 * n) ha
  have hBdiv := expanded_coeff_ne_zero_dvd_sixty68 B (3 * n - g)
    hdegenerate.2.1
  have hndiv : 90 ∣ n := by
    obtain ⟨u, hu⟩ := hAdiv
    obtain ⟨v, hv⟩ := hBdiv
    refine ⟨u / 3, ?_⟩
    omega
  obtain ⟨u, hu⟩ := hndiv
  have hgu : g = 150 * u := by omega
  have hboundaryAlign :
      (60 ∣ 4 * n - g) ↔ (60 ∣ 5 * n - 2 * g) := by
    constructor
    · intro hc
      obtain huEven | huOdd := Nat.even_or_odd u
      · obtain ⟨v, hv⟩ := huEven
        refine ⟨5 * v, ?_⟩
        omega
      · obtain ⟨v, hv⟩ := huOdd
        obtain ⟨q, hq⟩ := hc
        omega
    · intro hd
      obtain huEven | huOdd := Nat.even_or_odd u
      · obtain ⟨v, hv⟩ := huEven
        refine ⟨7 * v, ?_⟩
        omega
      · obtain ⟨v, hv⟩ := huOdd
        obtain ⟨q, hq⟩ := hd
        omega
  have hcStaggered : ¬60 ∣ 4 * n - g := by
    intro hc
    exact hmisaligned.elim (fun ht => ht hc)
      (fun ht => ht (hboundaryAlign.mp hc))
  have hdStaggered : ¬60 ∣ 5 * n - 2 * g := by
    intro hd
    exact hmisaligned.elim (fun ht => ht (hboundaryAlign.mpr hd))
      (fun ht => ht hd)
  have huNotEven : ¬2 ∣ u := by
    rintro ⟨v, hv⟩
    apply hcStaggered
    refine ⟨7 * v, ?_⟩
    omega
  obtain huEven | huOdd := Nat.even_or_odd u
  · exfalso
    obtain ⟨w, hw⟩ := huEven
    apply huNotEven
    refine ⟨w, ?_⟩
    omega
  obtain ⟨v, hv⟩ := huOdd
  have hterminalForm : g = 90 + 60 * (1 + 5 * v) := by omega
  have hgdiv : 30 ∣ g := by
    refine ⟨5 * u, ?_⟩
    omega
  have hcbase : 30 ∣ 4 * n - g := by
    refine ⟨7 * u, ?_⟩
    omega
  have hdbaseDiv : 30 ∣ 5 * n - 2 * g := by
    refine ⟨5 * u, ?_⟩
    omega
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
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have hdbase : d.natDegree < 5 * n := by
      have drops :=
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      change _ ∧ _ ∧ _ ∧ _ ∧ d.natDegree < 5 * n - g ∧ _ ∧ _ at drops
      exact drops.2.2.2.2.1.trans (by omega)
    have hebase : ee.natDegree < 6 * n := secondary.2.2.2.2.1.trans_lt (by omega)
    have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
    have selector :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
    change h = 2 * g ∧ _ at selector
    have ht := bounds.1
    change d.natDegree ≤ 5 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have hd30deg : d.natDegree ≤ 5 * n - 2 * g - 30 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g)
      hdbaseDiv (by omega)
    · simpa only [← hdexpand] using hd2
    · rw [← hdexpand]
      exact hdegenerate.2.2.1
  have base : ce.natDegree ≤ 4 * n - g - 90 ∧
      d.natDegree ≤ 5 * n - 2 * g - 90 := by
    constructor
    · rw [hceexpand]
      apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
        (cubicCDefectPolynomial68 A C0) (4 * n - g) hcbase hcStaggered
        (by omega)
      · simpa only [← hceexpand] using hc30deg
      · rw [← hceexpand]
        exact hz30.1
    · rw [hdexpand]
      apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
        (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g)
        hdbaseDiv hdStaggered (by omega)
      · simpa only [← hdexpand] using hd30deg
      · rw [← hdexpand]
        exact hz30.2
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
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ at selector
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
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
  have hsteps : ∀ m : ℕ, 90 + 60 * m ≤ g →
      ce.natDegree ≤ 4 * n - g - (90 + 60 * m) ∧
        d.natDegree ≤ 5 * n - 2 * g - (90 + 60 * m) := by
    intro m
    induction m with
    | zero =>
        intro hm
        simpa using base
    | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hstep := laterDeepLowerOpenDoubleFiveWall_staggered_offset_source_step68
          alpha gamma delta epsilon zeta eta Ae Be ce d ee
          (cubicCDefectPolynomial68 A C0)
          (secondaryDDefectPolynomial68 A B D) i3 n g (90 + 60 * m)
          hn ha hdegenerate.2.1 hopen hwall (by omega) (by omega)
          (by refine ⟨7 * v + 2 - m, ?_⟩; omega)
          (by refine ⟨5 * v + 1 - m, ?_⟩; omega)
          hA secondary.2.1 hprev.1 hprev.2 hD he2
          hceexpand hdexpand hi3c hrowPoly
        constructor <;> omega
  have hterminalBounds := hsteps (1 + 5 * v) (by omega)
  refine ⟨⟨1 + 5 * v, hterminalForm⟩, ?_, ?_⟩
  · have ht := hterminalBounds.1
    rw [← hterminalForm] at ht
    simpa only [Nat.sub_sub, two_mul] using ht
  · have ht := hterminalBounds.2
    rw [← hterminalForm] at ht
    have hz : 5 * n - 2 * g - g = 0 := by omega
    simpa only [hz] using ht

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateStaggered_inconsistent68
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
    (hmisaligned :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      (¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g)) : False := by
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
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let e := ee.coeff (6 * n - 2 * g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change (¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g) at hmisaligned
  have terminalBounds :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateStaggeredTerminalDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hmisaligned)
  change (∃ j : ℕ, g = 90 + 60 * j) ∧
      ce.natDegree ≤ 4 * n - 2 * g ∧ d.natDegree ≤ 0 at terminalBounds
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
  have ha : a ≠ 0 := by
    dsimp only [a]
    simpa only [n, Ae] using core.2.2.2.2.2
  have hb : b ≠ 0 := by
    dsimp only [b]
    exact hdegenerate.2.1
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
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ ∧ LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      (n : k) a b (ce.coeff (4 * n - g))
      (d.coeff (5 * n - 2 * g)) e delta at selector
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have topPacket : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      (n : k) a b 0 0 e delta := by
    simpa only [hdegenerate.1, hdegenerate.2.2.1] using selector.2.2
  have topClass := laterDeepLowerOpenDoubleFiveWall_terminal_top_delta_classification68
    (n : k) a b e delta (Nat.cast_ne_zero.mpr hn.ne') ha hb topPacket
  have hDtr : Dtr.natDegree ≤ 5 * n - g := by
    simp only [Dtr]
    compute_degree
    omega
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at h2e
  have hrowPoly := polynomialSecondaryResidualRowTwo68
    0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee h2e
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
      Ae Be ce d ee n g hn hwall hA secondary.2.1
        terminalBounds.2.1 terminalBounds.2.2 he2,
    cubicLoadRowTwoPolynomial68_coeff_sixRadius_of_terminal_aligned_fiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee n g hn hwall
      hA secondary.2.1 terminalBounds.2.1 hDtr he2] at hcoeff
  have hrowTwo : (8 / 27 : k) * (n : k) * a * b * (b ^ 2 + 9 * e) +
      (2 / 3 : k) * (n : k) * delta * a ^ 3 = 0 := by
    simpa only [a, b, e] using hcoeff
  exact laterDeepLowerOpenDoubleFiveWall_terminal_rowTwo_inconsistent68
    (n : k) a b e delta (Nat.cast_ne_zero.mpr hn.ne') ha hb
    topClass.1 topClass.2.1 hrowTwo

#print axioms laterDeepLowerOpenDoubleFiveWall_staggered_offset_source_step68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateStaggeredTerminalDescent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateStaggered_inconsistent68

end LaterDeepLowerOpenDoubleFiveWallStaggeredStrideInductionClosureSource68

end Max11DegreeRoutes
