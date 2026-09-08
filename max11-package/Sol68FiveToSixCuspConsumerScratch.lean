import Sol68FiveToSixCompleteStrideScratch

/-! # Consumer for the five-to-six cusp alternatives

The complete stride theorem leaves an exact earlier cusp or a terminal
packet.  Expansion support deletes every finite earlier cusp and both
radius-`90` terminal cusps.  At `(n,g)=(60,180)`, the terminal all-nonzero
cusp is the contracted `(1,3)` chart; its independent positive row-zero
coefficient `4` gives the existing exact contradiction.  What remains is
therefore either the terminal pair-zero packet or an honestly aligned cusp
in the large family.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspConsumer68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The honest zero child of the symbolic terminal packet. -/
def FiveToSixTerminalZeroPacket68
    (zeta : k) (d e : k[X]) (n g : ℕ) : Prop :=
  d.natDegree ≤ g - 2 * n ∧ e.natDegree ≤ g - n ∧ zeta = 0 ∧
    d.coeff (g - 2 * n) = 0 ∧ e.coeff (g - n) = 0

/-- Exact residual after consuming all finite cusps.  The witness `s` is
retained, including whether it is earlier than or equal to the load wall. -/
def FiveToSixLargeCuspResidual68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  (∃ s, 120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧ 60 ∣ s ∧
      0 < s ∧ s < 7 * n - 2 * g ∧
      FiveToSixCuspEdge68 A B c d e n g s) ∨
    (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
      d.natDegree ≤ g - 2 * n ∧ e.natDegree ≤ g - n ∧ zeta = 0 ∧
      FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g))

/-- Every all-nonzero cusp whose five polynomials lie on the expansion
lattice has a `60`-aligned radius, gap, and edge offset. -/
theorem fiveToSix_expanded_cusp_alignment68
    (A B c d e : k[X]) (n g s : ℕ)
    (hgUpper : g ≤ 3 * n) (hgs : g + s ≤ 5 * n)
    (hcusp : FiveToSixCuspEdge68
      (expand k 60 A) (expand k 60 B) (expand k 60 c)
      (expand k 60 d) (expand k 60 e) n g s) :
    60 ∣ n ∧ 60 ∣ g ∧ 60 ∣ s := by
  have hBdiv : 60 ∣ 3 * n - g :=
    coeff_expand_ne_zero_dvd68 60 (by norm_num) B (3 * n - g) hcusp.1
  have hcdiv : 60 ∣ 4 * n - g :=
    coeff_expand_ne_zero_dvd68 60 (by norm_num) c (4 * n - g) hcusp.2.1
  have hddiv : 60 ∣ 5 * n - g - s :=
    coeff_expand_ne_zero_dvd68 60 (by norm_num) d (5 * n - g - s)
      hcusp.2.2.1
  obtain ⟨u, hu⟩ := hBdiv
  obtain ⟨v, hv⟩ := hcdiv
  have huv : u ≤ v := by omega
  have hn : 60 ∣ n := ⟨v - u, by omega⟩
  obtain ⟨q, hq⟩ := hn
  have huq : u ≤ 3 * q := by omega
  have hg : 60 ∣ g := ⟨3 * q - u, by omega⟩
  obtain ⟨w, hw⟩ := hg
  obtain ⟨t, ht⟩ := hddiv
  have hwqt : w + t ≤ 5 * q := by omega
  exact ⟨⟨q, hq⟩, ⟨w, hw⟩, ⟨5 * q - w - t, by omega⟩⟩

/-- The only expansion-compatible finite terminal cusp is the `(1,3)`
contracted chart.  The terminal I4 face and the positive source coefficient
`4` feed the verified one-three row-zero contradiction. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_sixty_terminalCusp_false68
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
      n = 60 ∧ g = 180)
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
      d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n)
    (hcusp :
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
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) : False := by
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
  let cu := cubicCDefectPolynomial68 A C0
  let du := secondaryDDefectPolynomial68 A B D
  let eu := cubicEDefectPolynomial68 A C0 E
  change n = 60 ∧ g = 180 at hwall
  change d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n at hdrop
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g) at hcusp
  have hlater : 3 * n ≤ 2 * g := by omega
  have hsource :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinety_with_terminalRHS68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change _ ∧ FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta
    terminal A B cu du eu at hsource
  have hadapter := hsource.2
  rw [hzeta] at hadapter
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, _hrow1, _hrow2, hrow0pos, _hiff⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hcexpand : ce = expand k 60 cu := by
    simpa only [ce, Ae, Ce, cu] using
      expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 du := by
    simpa only [d, Ae, Be, De, du] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 eu := by
    simpa only [ee, Ae, Ce, Ee, eu] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hA2 : A.natDegree ≤ 2 := by
    have h := data.hA
    simp only [Ae, natDegree_expand, hwall.1] at h
    omega
  have hB0deg : B.natDegree ≤ 0 := by
    have h := data.hB
    simp only [Be, natDegree_expand, hwall.1, hwall.2] at h
    omega
  have hc1deg : cu.natDegree ≤ 1 := by
    have h := data.hc
    rw [hcexpand, natDegree_expand, hwall.1, hwall.2] at h
    omega
  have hd1deg : du.natDegree ≤ 1 := by
    have h' : (expand k 60 du).natDegree ≤ g - 2 * n := by
      rw [← hdexpand]
      exact hdrop.1
    rw [natDegree_expand, hwall.1, hwall.2] at h'
    omega
  have he2deg : eu.natDegree ≤ 2 := by
    have h' : (expand k 60 eu).natDegree ≤ g - n := by
      rw [← heexpand]
      exact hdrop.2
    rw [natDegree_expand, hwall.1, hwall.2] at h'
    omega
  have ha2 : A.coeff 2 ≠ 0 := by
    simpa [Ae, hwall.1, coeff_expand] using data.ha
  have hb0 : B.coeff 0 ≠ 0 := by
    simpa [FiveToSixCuspEdge68, Be, hwall.1, hwall.2, coeff_expand] using hcusp.1
  have hx : du.coeff 1 ≠ 0 := by
    have h := hcusp.2.2.1
    simpa [FiveToSixCuspEdge68, hwall.1, hwall.2, hdexpand, coeff_expand] using h
  have hy : eu.coeff 2 ≠ 0 := by
    have h := hcusp.2.2.2.1
    simpa [FiveToSixCuspEdge68, hwall.1, hwall.2, heexpand, coeff_expand] using h
  have hdisc : A.coeff 2 * B.coeff 0 ^ 2 + 3 * cu.coeff 1 ^ 2 = 0 := by
    have h := hcusp.2.2.2.2
    simpa [FiveToSixCuspEdge68, Ae, Be, hwall.1, hwall.2,
      hcexpand, coeff_expand] using h
  have hoffset :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (n = 60 ∧ g = 180 ∧ _ ∧ _) ∨ _ at hoffset
  have hloaded := hoffset.resolve_right (fun h => by omega)
  have hfaceExpanded : Be.coeff (3 * n - g) *
        ee.coeff (6 * n - g - 60) +
      ce.coeff (4 * n - g) * d.coeff (5 * n - g - 60) = 0 := by
    have h := hloaded.2.2.1
    rw [hzeta, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hface : B.coeff 0 * eu.coeff 2 + cu.coeff 1 * du.coeff 1 = 0 := by
    simpa [Be, hwall.1, hwall.2, hcexpand, hdexpand, heexpand,
      coeff_expand] using hfaceExpanded
  exact fiveToSix_aligned_secondJet_oneThree_rowZero_source_false68
    alpha gamma epsilon eta i4 i3 A B cu du eu hA2 hB0deg hc1deg hd1deg
    he2deg ha2 hb0 hx hy hface hdisc hi4 hi3 (hrow0pos 4 (by norm_num))

/-- Source-facing cusp consumer.  All finite all-nonzero cusps are deleted.
The exact residual is a terminal zero edge or a large cusp whose radius,
gap, and (for an earlier cusp) witnessed offset all lie on the `60` lattice. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_consume_cusps68
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
    FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
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
  let cu := cubicCDefectPolynomial68 A C0
  let du := secondaryDDefectPolynomial68 A B D
  let eu := cubicEDefectPolynomial68 A C0 E
  have hcomplete := integratedPolynomialLowerSystem68_fiveToSix_completeStride68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change (∃ s, 0 < s ∧ s < 7 * n - 2 * g ∧
      FiveToSixCuspEdge68 Ae Be ce d ee n g s) ∨
    FiveToSixTerminalPacket68 zeta Ae Be ce d ee n g at hcomplete
  have hinventory := integratedPolynomialLowerSystem68_global_terminalLoad_inventory
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g ∧
    ((n = 60 ∧ g = 180 ∧ 7 * n - 2 * g = 60) ∨
      (n = 90 ∧ g = 240 ∧ 7 * n - 2 * g = 150) ∨
      (n = 90 ∧ g = 270 ∧ 7 * n - 2 * g = 90) ∨ 120 < n)
    at hinventory
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hinventory.1.1, hinventory.1.2.1⟩
  have hcexpand : ce = expand k 60 cu := by
    simpa only [ce, Ae, Ce, cu] using
      expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 du := by
    simpa only [d, Ae, Be, De, du] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 eu := by
    simpa only [ee, Ae, Ce, Ee, eu] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  rcases hcomplete with hearly | hterminalPacket
  · rcases hearly with ⟨s, hs, hsr, hcusp⟩
    have hcuspExpanded : FiveToSixCuspEdge68
        (expand k 60 A) (expand k 60 B) (expand k 60 cu)
        (expand k 60 du) (expand k 60 eu) n g s := by
      simpa only [Ae, Be, hcexpand, hdexpand, heexpand] using hcusp
    have halign := fiveToSix_expanded_cusp_alignment68 A B cu du eu n g s
      (by omega) (by omega) hcuspExpanded
    rcases hinventory.2 with h60 | h90240 | h90270 | hbig
    · rcases h60 with ⟨hn60, hg180, hr60⟩
      obtain ⟨q, hq⟩ := halign.2.2
      omega
    · have hdiv := halign.1
      rcases h90240 with ⟨hn90, _hg240, _hr150⟩
      rw [hn90] at hdiv
      norm_num at hdiv
    · have hdiv := halign.1
      rcases h90270 with ⟨hn90, _hg270, _hr90⟩
      rw [hn90] at hdiv
      norm_num at hdiv
    · right; left
      exact ⟨s, hbig, halign.1, halign.2.1, halign.2.2,
        hs, hsr, hcusp⟩
  · rcases hterminalPacket with ⟨hddeg, hedeg, hzeta, hzero | hcusp⟩
    · left
      exact ⟨hddeg, hedeg, hzeta, hzero.1, hzero.2⟩
    · have hcuspExpanded : FiveToSixCuspEdge68
          (expand k 60 A) (expand k 60 B) (expand k 60 cu)
          (expand k 60 du) (expand k 60 eu) n g (7 * n - 2 * g) := by
        simpa only [Ae, Be, hcexpand, hdexpand, heexpand] using hcusp
      have halign := fiveToSix_expanded_cusp_alignment68 A B cu du eu n g
        (7 * n - 2 * g) (by omega) (by omega) hcuspExpanded
      rcases hinventory.2 with h60 | h90240 | h90270 | hbig
      · exact False.elim
          (integratedPolynomialLowerSystem68_fiveToSix_sixty_terminalCusp_false68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys
            (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
                ⟨h60.1, h60.2.1⟩)
            hzeta
            (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
                ⟨hddeg, hedeg⟩)
            (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hcusp))
      · have hdiv := halign.1
        rcases h90240 with ⟨hn90, _hg240, _hr150⟩
        rw [hn90] at hdiv
        norm_num at hdiv
      · have hdiv := halign.1
        rcases h90270 with ⟨hn90, _hg270, _hr90⟩
        rw [hn90] at hdiv
        norm_num at hdiv
      · right; right
        exact ⟨hbig, halign.1, halign.2.1, hddeg, hedeg, hzeta, hcusp⟩

#print axioms fiveToSix_expanded_cusp_alignment68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_sixty_terminalCusp_false68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_consume_cusps68

end FiveToSixCuspConsumer68

end Max11DegreeRoutes
