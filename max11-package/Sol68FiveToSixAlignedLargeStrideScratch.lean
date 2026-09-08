import Sol68FiveToSixFinitePhaseStrideScratch

/-! # Aligned large-family stride for the five-to-six chamber -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixAlignedLargeStride68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Rounding an expanded support bound whose upper endpoint is halfway
between two `60`-lattice points. -/
theorem natDegree_expand_le_sub_ninety_of_halfPhase_bound68
    (q : k[X]) (base u : ℕ) (hbase : base = 60 * u + 30)
    (h90 : 90 ≤ base) (hdeg : (expand k 60 q).natDegree ≤ base - 60) :
    (expand k 60 q).natDegree ≤ base - 90 := by
  rw [natDegree_expand] at hdeg ⊢
  omega

theorem natDegree_expand_le_sub_thirty_of_halfPhase_bound68
    (q : k[X]) (upper u : ℕ) (hupper : upper = 60 * u + 30)
    (hdeg : (expand k 60 q).natDegree ≤ upper) :
    (expand k 60 q).natDegree ≤ upper - 30 := by
  rw [natDegree_expand] at hdeg ⊢
  omega

/-- A common aligned phase iterates by `60`.  Each source step either
exposes the exact all-nonzero cusp or advances both expanded supports. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_aligned_iterate68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s0 m : ℕ) (hterminal : terminal ≠ 0)
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
    (hs0 : 0 < s0)
    (hphase :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - g - s0 ∧ 60 ∣ 6 * n - g - s0)
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
      d.natDegree ≤ 5 * n - g - s0 ∧ ee.natDegree ≤ 6 * n - g - s0)
    (hbefore :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ∀ j, j < m → s0 + 60 * j < 7 * n - 2 * g)
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
      s0 + 60 * m ≤ 5 * n - g ∧ s0 + 60 * m ≤ 6 * n - g) :
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
    (∃ j, j < m ∧ FiveToSixCuspEdge68 Ae Be ce d ee n g (s0 + 60 * j)) ∨
      (d.natDegree ≤ 5 * n - g - (s0 + 60 * m) ∧
        ee.natDegree ≤ 6 * n - g - (s0 + 60 * m)) := by
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
  change 60 ∣ 5 * n - g - s0 ∧ 60 ∣ 6 * n - g - s0 at hphase
  change d.natDegree ≤ 5 * n - g - s0 ∧
    ee.natDegree ≤ 6 * n - g - s0 at hdrop
  change (∀ j, j < m → s0 + 60 * j < 7 * n - 2 * g) at hbefore
  change s0 + 60 * m ≤ 5 * n - g ∧
    s0 + 60 * m ≤ 6 * n - g at hroom
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using expand_cubicEDefectPolynomial68 60 A C0 E
  have hsteps : ∀ t : ℕ,
      (∀ j, j < t → s0 + 60 * j < 7 * n - 2 * g) →
      s0 + 60 * t ≤ 5 * n - g → s0 + 60 * t ≤ 6 * n - g →
      ((∃ j, j < t ∧
          FiveToSixCuspEdge68 Ae Be ce d ee n g (s0 + 60 * j)) ∨
        (d.natDegree ≤ 5 * n - g - (s0 + 60 * t) ∧
          ee.natDegree ≤ 6 * n - g - (s0 + 60 * t))) := by
    intro t
    induction t with
    | zero =>
        intro hb hdroom heroom
        right
        simpa using hdrop
    | succ t ih =>
        intro hb hdroom heroom
        have hprev := ih (fun j hj => hb j (by omega)) (by omega) (by omega)
        rcases hprev with hcusp | hprev
        · left
          rcases hcusp with ⟨j, hj, hcusp⟩
          exact ⟨j, by omega, hcusp⟩
        · have hedge :=
            maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
              l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
              (s0 + 60 * t) hterminal hsys
              (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
              (by omega)
              (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hb t (by omega))
              (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hprev)
          change (d.coeff (5 * n - g - (s0 + 60 * t)) = 0 ∧
              ee.coeff (6 * n - g - (s0 + 60 * t)) = 0) ∨
            FiveToSixCuspEdge68 Ae Be ce d ee n g (s0 + 60 * t) at hedge
          rcases hedge with hedge | hcusp
          · right
            have hdphase : 60 ∣ 5 * n - g - (s0 + 60 * t) := by
              obtain ⟨u, hu⟩ := hphase.1
              refine ⟨u - t, ?_⟩
              omega
            have hephase : 60 ∣ 6 * n - g - (s0 + 60 * t) := by
              obtain ⟨u, hu⟩ := hphase.2
              refine ⟨u - t, ?_⟩
              omega
            constructor
            · rw [hdexpand]
              exact natDegree_expand_le_sub_next_sixty68
                (secondaryDDefectPolynomial68 A B D) (5 * n - g)
                (s0 + 60 * t) hdphase (by omega)
                (by simpa only [hdexpand] using hprev.1)
                (by simpa only [hdexpand] using hedge.1)
            · rw [heexpand]
              exact natDegree_expand_le_sub_next_sixty68
                (cubicEDefectPolynomial68 A C0 E) (6 * n - g)
                (s0 + 60 * t) hephase (by omega)
                (by simpa only [heexpand] using hprev.2)
                (by simpa only [heexpand] using hedge.2)
          · left
            exact ⟨t, by omega, hcusp⟩
  exact hsteps m hbefore hroom.1 hroom.2

/-- The entire large common-phase family reaches the symbolic load unless
an earlier aligned source edge is the exact all-nonzero cusp. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_large_aligned68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hbig : 120 < weightedRadius68 A B C0 D E)
    (hnAligned : 60 ∣ weightedRadius68 A B C0 D E) :
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
    (∃ s, 0 < s ∧ s < 7 * n - 2 * g ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g s) ∨
      FiveToSixTerminalPacket68 zeta Ae Be ce d ee n g := by
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
  change 60 ∣ n at hnAligned
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g at hglobal
  rcases hglobal with
    ⟨hgt5, hle6, hfour, hthree, hn30, hg30, hnLarge, hvanish,
      hd60, he60, hpost, hnot120, holdCases⟩
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  obtain ⟨N, hN⟩ := hnAligned
  obtain ⟨G, hG⟩ := hg30
  have hr60 : 60 ∣ 7 * n - 2 * g := by
    refine ⟨7 * N - G, ?_⟩
    omega
  obtain ⟨q, hq⟩ := hr60
  have hqLarge : 2 ≤ q := by omega
  have hnLower : 10 < weightedRadius68 A B C0 D E := by
    change 10 < n
    omega
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using expand_cubicEDefectPolynomial68 60 A C0 E
  by_cases hgAligned : 60 ∣ g
  · obtain ⟨H, hH⟩ := hgAligned
    have hdphase : 60 ∣ 5 * n - g - 60 := by
      refine ⟨5 * N - H - 1, ?_⟩
      omega
    have hephase : 60 ∣ 6 * n - g - 60 := by
      refine ⟨6 * N - H - 1, ?_⟩
      omega
    have htarget : 60 + 60 * (q - 1) = 7 * n - 2 * g := by omega
    have hiter :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_aligned_iterate68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        60 (q - 1) hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by norm_num)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (⟨hdphase, hephase⟩ :
            60 ∣ 5 * n - g - 60 ∧ 60 ∣ 6 * n - g - 60))
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          (⟨hd60, he60⟩ :
            d.natDegree ≤ 5 * n - g - 60 ∧ ee.natDegree ≤ 6 * n - g - 60))
        (by
          simp only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
          intro j hj
          have ht : 60 + 60 * j < 60 + 60 * (q - 1) := by omega
          rw [htarget] at ht
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using ht)
        (by
          rw [htarget]
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using (show 7 * n - 2 * g ≤ 5 * n - g ∧
              7 * n - 2 * g ≤ 6 * n - g by constructor <;> omega))
    change (∃ j, j < q - 1 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (60 + 60 * j)) ∨
      (d.natDegree ≤ 5 * n - g - (60 + 60 * (q - 1)) ∧
        ee.natDegree ≤ 6 * n - g - (60 + 60 * (q - 1))) at hiter
    rcases hiter with hcusp | hdropTerminal
    · left
      rcases hcusp with ⟨j, hj, hcusp⟩
      have hslt : 60 + 60 * j < 7 * n - 2 * g := by
        have ht : 60 + 60 * j < 60 + 60 * (q - 1) := by omega
        rwa [htarget] at ht
      exact ⟨60 + 60 * j, by omega, hslt, hcusp⟩
    · right
      have hdrop : d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n := by
        constructor <;> omega
      exact maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hnLower
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop)
  · have hgmod : g % 60 = 30 := by omega
    have hgform : g = 60 * (g / 60) + 30 := by omega
    let H := g / 60
    have hdBase : 5 * n - g = 60 * (5 * N - H - 1) + 30 := by
      dsimp only [H]
      omega
    have heBase : 6 * n - g = 60 * (6 * N - H - 1) + 30 := by
      dsimp only [H]
      omega
    have hd90 : d.natDegree ≤ 5 * n - g - 90 := by
      rw [hdexpand]
      exact natDegree_expand_le_sub_ninety_of_halfPhase_bound68
        (secondaryDDefectPolynomial68 A B D) (5 * n - g)
        (5 * N - H - 1) hdBase (by omega)
        (by simpa only [hdexpand] using hd60)
    have he90 : ee.natDegree ≤ 6 * n - g - 90 := by
      rw [heexpand]
      exact natDegree_expand_le_sub_ninety_of_halfPhase_bound68
        (cubicEDefectPolynomial68 A C0 E) (6 * n - g)
        (6 * N - H - 1) heBase (by omega)
        (by simpa only [heexpand] using he60)
    have hdphase : 60 ∣ 5 * n - g - 90 := by
      refine ⟨5 * N - H - 2, ?_⟩
      omega
    have hephase : 60 ∣ 6 * n - g - 90 := by
      refine ⟨6 * N - H - 2, ?_⟩
      omega
    have htarget : 90 + 60 * (q - 1) = 7 * n - 2 * g + 30 := by omega
    have hiter :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_aligned_iterate68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        90 (q - 1) hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by norm_num)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (⟨hdphase, hephase⟩ :
            60 ∣ 5 * n - g - 90 ∧ 60 ∣ 6 * n - g - 90))
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          (⟨hd90, he90⟩ :
            d.natDegree ≤ 5 * n - g - 90 ∧ ee.natDegree ≤ 6 * n - g - 90))
        (by
          simp only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
          intro j hj
          have ht : 90 + 60 * j < 7 * n - 2 * g := by omega
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using ht)
        (by
          rw [htarget]
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using (show 7 * n - 2 * g + 30 ≤ 5 * n - g ∧
              7 * n - 2 * g + 30 ≤ 6 * n - g by constructor <;> omega))
    change (∃ j, j < q - 1 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (90 + 60 * j)) ∨
      (d.natDegree ≤ 5 * n - g - (90 + 60 * (q - 1)) ∧
        ee.natDegree ≤ 6 * n - g - (90 + 60 * (q - 1))) at hiter
    rcases hiter with hcusp | hdropTerminal
    · left
      rcases hcusp with ⟨j, hj, hcusp⟩
      have hslt : 90 + 60 * j < 7 * n - 2 * g := by omega
      exact ⟨90 + 60 * j, by omega, hslt, hcusp⟩
    · right
      have hdrop : d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n := by
        constructor <;> omega
      exact maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hnLower
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop)

/-- Minimal staggered source API still missing when the two support lattices
are thirty degrees out of phase.  The two coefficients must be coupled at
offsets `s` and `s+30`; separate same-offset edges cannot advance both. -/
def FiveToSixStaggeredCoupledEdge68
    (A B c d e : k[X]) (n g s : ℕ) : Prop :=
  (d.coeff (5 * n - g - s) = 0 ∧
      e.coeff (6 * n - g - (s + 30)) = 0) ∨
    (B.coeff (3 * n - g) ≠ 0 ∧ c.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - g - s) ≠ 0 ∧
      e.coeff (6 * n - g - (s + 30)) ≠ 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
        3 * c.coeff (4 * n - g) ^ 2 = 0)

/-- No new coupled coefficient identity is needed away from the terminal
load: two calls to the uniform edge, thirty degrees apart, advance the
staggered pair by a complete `60` stride.  Each apparent cusp is killed by
its off-lattice expanded coefficient. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_pair_step68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s N : ℕ) (hterminal : terminal ≠ 0)
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
    (hnform : weightedRadius68 A B C0 D E = 60 * N + 30)
    (hs : 0 < s)
    (hphase :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - g - s)
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
      d.natDegree ≤ 5 * n - g - s ∧ ee.natDegree ≤ 6 * n - g - s)
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
      s + 30 < 7 * n - 2 * g)
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
      s + 60 ≤ 5 * n - g ∧ s + 90 ≤ 6 * n - g) :
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
    d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - (s + 30)) = 0 ∧
      d.natDegree ≤ 5 * n - g - (s + 60) ∧
      ee.natDegree ≤ 6 * n - g - (s + 60) := by
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
  change n = 60 * N + 30 at hnform
  change 60 ∣ 5 * n - g - s at hphase
  change d.natDegree ≤ 5 * n - g - s ∧ ee.natDegree ≤ 6 * n - g - s at hdrop
  change s + 30 < 7 * n - 2 * g at hload
  change s + 60 ≤ 5 * n - g ∧ s + 90 ≤ 6 * n - g at hroom
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using expand_cubicEDefectPolynomial68 60 A C0 E
  obtain ⟨u, hu⟩ := hphase
  have heUpper : 6 * n - g - s = 60 * (u + N) + 30 := by omega
  have heOff : ee.coeff (6 * n - g - s) = 0 := by
    by_contra hne
    have hdiv : 60 ∣ 6 * n - g - s := by
      rw [heexpand] at hne
      exact coeff_expand_ne_zero_dvd68 60 (by norm_num)
        (cubicEDefectPolynomial68 A C0 E) (6 * n - g - s) hne
    obtain ⟨v, hv⟩ := hdiv
    omega
  have hedgeS :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E s
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      hs (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
        (show s < 7 * n - 2 * g by omega))
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop)
  change (d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - s) = 0) ∨
    FiveToSixCuspEdge68 Ae Be ce d ee n g s at hedgeS
  have hedgeS0 := hedgeS.resolve_right (fun hcusp => hcusp.2.2.2.1 heOff)
  have hdNext : d.natDegree ≤ 5 * n - g - (s + 60) := by
    rw [hdexpand]
    exact natDegree_expand_le_sub_next_sixty68
      (secondaryDDefectPolynomial68 A B D) (5 * n - g) s
      ⟨u, hu⟩ hroom.1 (by simpa only [hdexpand] using hdrop.1)
      (by simpa only [hdexpand] using hedgeS0.1)
  have heRound : ee.natDegree ≤ 6 * n - g - (s + 30) := by
    rw [heexpand]
    have ht := natDegree_expand_le_sub_thirty_of_halfPhase_bound68
      (cubicEDefectPolynomial68 A C0 E) (6 * n - g - s) (u + N)
      heUpper (by simpa only [heexpand] using hdrop.2)
    exact ht.trans (by omega)
  have hedgeT :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E (s + 30)
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      (by omega) (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hload)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
        (⟨hdNext.trans (by omega), heRound⟩ :
          d.natDegree ≤ 5 * n - g - (s + 30) ∧
            ee.natDegree ≤ 6 * n - g - (s + 30)))
  change (d.coeff (5 * n - g - (s + 30)) = 0 ∧
      ee.coeff (6 * n - g - (s + 30)) = 0) ∨
    FiveToSixCuspEdge68 Ae Be ce d ee n g (s + 30) at hedgeT
  have hdOff : d.coeff (5 * n - g - (s + 30)) = 0 := by
    by_contra hne
    have hdiv : 60 ∣ 5 * n - g - (s + 30) := by
      rw [hdexpand] at hne
      exact coeff_expand_ne_zero_dvd68 60 (by norm_num)
        (secondaryDDefectPolynomial68 A B D) (5 * n - g - (s + 30)) hne
    obtain ⟨v, hv⟩ := hdiv
    omega
  have hedgeT0 := hedgeT.resolve_right (fun hcusp => hcusp.2.2.1 hdOff)
  have hePhase : 60 ∣ 6 * n - g - (s + 30) := by
    refine ⟨u + N, ?_⟩
    omega
  have heNext : ee.natDegree ≤ 6 * n - g - (s + 90) := by
    rw [heexpand]
    exact natDegree_expand_le_sub_next_sixty68
      (cubicEDefectPolynomial68 A C0 E) (6 * n - g) (s + 30)
      hePhase hroom.2 (by simpa only [heexpand] using heRound)
      (by simpa only [heexpand] using hedgeT0.2)
  have heMono : 6 * n - g - (s + 90) ≤ 6 * n - g - (s + 60) :=
    Nat.sub_le_sub_left (by omega) (6 * n - g)
  exact ⟨hedgeS0.1, hedgeT0.2, hdNext, heNext.trans heMono⟩

/-- Exact phase arithmetic behind the required staggered API. -/
theorem fiveToSix_staggered_offsets_align68
    (n g s : ℕ) (hn30 : n = 60 * (n / 60) + 30)
    (hd : 60 ∣ 5 * n - g - s) (hroom : g + s + 30 ≤ 5 * n) :
    60 ∣ 6 * n - g - (s + 30) := by
  obtain ⟨u, hu⟩ := hd
  refine ⟨u + n / 60, ?_⟩
  omega

#print axioms natDegree_expand_le_sub_ninety_of_halfPhase_bound68
#print axioms natDegree_expand_le_sub_thirty_of_halfPhase_bound68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_aligned_iterate68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_large_aligned68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_pair_step68
#print axioms fiveToSix_staggered_offsets_align68

end FiveToSixAlignedLargeStride68

end Max11DegreeRoutes
