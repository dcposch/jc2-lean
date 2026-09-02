import Sol68FiveToSixAlignedLargeStrideScratch

/-! # Complete source stride for the five-to-six chamber -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCompleteStride68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Iteration of the verified pair step on a fixed staggered phase. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_iterate68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s0 m N : ℕ) (hterminal : terminal ≠ 0)
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
      60 ∣ 5 * n - g - s0)
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
      ∀ j, j < m → s0 + 60 * j + 30 < 7 * n - 2 * g)
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
      s0 + 60 * m ≤ 5 * n - g ∧ s0 + 60 * m + 30 ≤ 6 * n - g) :
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
    d.natDegree ≤ 5 * n - g - (s0 + 60 * m) ∧
      ee.natDegree ≤ 6 * n - g - (s0 + 60 * m) := by
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
  change 60 ∣ 5 * n - g - s0 at hphase
  change d.natDegree ≤ 5 * n - g - s0 ∧ ee.natDegree ≤ 6 * n - g - s0 at hdrop
  change (∀ j, j < m → s0 + 60 * j + 30 < 7 * n - 2 * g) at hbefore
  change s0 + 60 * m ≤ 5 * n - g ∧
    s0 + 60 * m + 30 ≤ 6 * n - g at hroom
  have hsteps : ∀ t : ℕ,
      (∀ j, j < t → s0 + 60 * j + 30 < 7 * n - 2 * g) →
      s0 + 60 * t ≤ 5 * n - g → s0 + 60 * t + 30 ≤ 6 * n - g →
      d.natDegree ≤ 5 * n - g - (s0 + 60 * t) ∧
        ee.natDegree ≤ 6 * n - g - (s0 + 60 * t) := by
    intro t
    induction t with
    | zero =>
        intro hb hdroom heroom
        simpa using hdrop
    | succ t ih =>
        intro hb hdroom heroom
        have hprev := ih (fun j hj => hb j (by omega)) (by omega) (by omega)
        have htphase : 60 ∣ 5 * n - g - (s0 + 60 * t) := by
          obtain ⟨u, hu⟩ := hphase
          refine ⟨u - t, ?_⟩
          omega
        have hstep :=
          maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_pair_step68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            (s0 + 60 * t) N hterminal hsys
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
            (by simpa only [n] using hnform) (by omega)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using htphase)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hprev)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hb t (by omega))
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
              (show s0 + 60 * t + 60 ≤ 5 * n - g ∧
                s0 + 60 * t + 90 ≤ 6 * n - g by constructor <;> omega))
        exact ⟨hstep.2.2.1, hstep.2.2.2⟩
  exact hsteps m hbefore hroom.1 hroom.2

/-- At the staggered endpoint `s+30=r`, the first uniform call advances `d`
and lattice rounding advances `e`; this is already the terminal support. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_endpoint68
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
    (hend :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      s + 30 = 7 * n - 2 * g) :
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
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change n = 60 * N + 30 at hnform
  change 60 ∣ 5 * n - g - s at hphase
  change d.natDegree ≤ 5 * n - g - s ∧ ee.natDegree ≤ 6 * n - g - s at hdrop
  change s + 30 = 7 * n - 2 * g at hend
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
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E s
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      hs (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
        (show s < 7 * n - 2 * g by omega))
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop)
  change (d.coeff (5 * n - g - s) = 0 ∧ ee.coeff (6 * n - g - s) = 0) ∨
    FiveToSixCuspEdge68 Ae Be ce d ee n g s at hedge
  have hedge0 := hedge.resolve_right (fun hcusp => hcusp.2.2.2.1 heOff)
  have hdNext : d.natDegree ≤ 5 * n - g - (s + 60) := by
    rw [hdexpand]
    exact natDegree_expand_le_sub_next_sixty68
      (secondaryDDefectPolynomial68 A B D) (5 * n - g) s
      ⟨u, hu⟩ (by omega) (by simpa only [hdexpand] using hdrop.1)
      (by simpa only [hdexpand] using hedge0.1)
  have heRound : ee.natDegree ≤ 6 * n - g - (s + 30) := by
    rw [heexpand]
    have ht := natDegree_expand_le_sub_thirty_of_halfPhase_bound68
      (cubicEDefectPolynomial68 A C0 E) (6 * n - g - s) (u + N)
      heUpper (by simpa only [heexpand] using hdrop.2)
    exact ht.trans (by omega)
  have hterminalDrop : d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n := by
    constructor <;> omega
  exact maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys (by change 10 < n; omega)
    (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
    (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hterminalDrop)

/-- The large `n = 30 mod 60` family reaches the terminal packet by the
staggered pair iteration; no cusp survives the off-lattice checks. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_large_staggered68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hbig : 120 < weightedRadius68 A B C0 D E)
    (hnmod : weightedRadius68 A B C0 D E % 60 = 30) :
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
  change n % 60 = 30 at hnmod
  have hnform : n = 60 * (n / 60) + 30 := by omega
  let N := n / 60
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g at hglobal
  rcases hglobal with
    ⟨hgt5, hle6, hfour, hthree, hn30, hg30, hnLarge, hvanish,
      hd60, he60, hpost, hnot120, holdCases⟩
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  have hzero120 := hpost.2.resolve_right (fun hcusp => by
    have hn60 : 60 ∣ n := hcusp.1
    obtain ⟨u, hu⟩ := hn60
    omega)
  have hdrop120 : d.natDegree ≤ 5 * n - g - 120 ∧
      ee.natDegree ≤ 6 * n - g - 120 :=
    ⟨hzero120.2.2.1, hzero120.2.2.2.1⟩
  obtain ⟨G, hG⟩ := hg30
  let Q := 7 * N + 3 - G
  have hrform : 7 * n - 2 * g = 60 * Q + 30 := by
    dsimp only [N, Q]
    omega
  have hQLarge : 2 ≤ Q := by omega
  by_cases hgAligned : 60 ∣ g
  · obtain ⟨H, hH⟩ := hgAligned
    have hd90 : d.natDegree ≤ 5 * n - g - 90 :=
      hdrop120.1.trans (Nat.sub_le_sub_left (by omega) (5 * n - g))
    have he90 : ee.natDegree ≤ 6 * n - g - 90 :=
      hdrop120.2.trans (Nat.sub_le_sub_left (by omega) (6 * n - g))
    have hdphase : 60 ∣ 5 * n - g - 90 := by
      refine ⟨5 * N - H + 1, ?_⟩
      dsimp only [N]
      omega
    have htarget : 90 + 60 * (Q - 1) = 7 * n - 2 * g := by omega
    have hiter :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_iterate68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        90 (Q - 1) N hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by simpa only [n, N] using hnform) (by norm_num)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdphase)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          (⟨hd90, he90⟩ :
            d.natDegree ≤ 5 * n - g - 90 ∧ ee.natDegree ≤ 6 * n - g - 90))
        (by
          simp only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
          intro j hj
          have ht : 90 + 60 * j + 30 < 90 + 60 * (Q - 1) := by omega
          rwa [htarget] at ht)
        (by
          rw [htarget]
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (show 7 * n - 2 * g ≤ 5 * n - g ∧
              7 * n - 2 * g + 30 ≤ 6 * n - g by constructor <;> omega))
    change d.natDegree ≤ 5 * n - g - (90 + 60 * (Q - 1)) ∧
      ee.natDegree ≤ 6 * n - g - (90 + 60 * (Q - 1)) at hiter
    have hdrop : d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n := by
      constructor <;> omega
    exact maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by change 10 < n; omega)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop)
  · have hgmod : g % 60 = 30 := by omega
    have hgform : g = 60 * (g / 60) + 30 := by omega
    let H := g / 60
    have hdphase : 60 ∣ 5 * n - g - 120 := by
      refine ⟨5 * N - H, ?_⟩
      dsimp only [N, H]
      omega
    have htarget : 120 + 60 * (Q - 2) = 7 * n - 2 * g - 30 := by omega
    have hendtarget : 120 + 60 * (Q - 2) + 30 = 7 * n - 2 * g := by omega
    have hroomExact : 120 + 60 * (Q - 2) ≤ 5 * n - g ∧
        120 + 60 * (Q - 2) + 30 ≤ 6 * n - g := by
      constructor
      · rw [htarget]
        omega
      · rw [hendtarget]
        omega
    have hiter :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_iterate68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        120 (Q - 2) N hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by simpa only [n, N] using hnform) (by norm_num)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdphase)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop120)
        (by
          simp only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
          intro j hj
          have ht : 120 + 60 * j + 30 < 120 + 60 * (Q - 2) + 30 := by omega
          rwa [hendtarget] at ht)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hroomExact)
    change d.natDegree ≤ 5 * n - g - (120 + 60 * (Q - 2)) ∧
      ee.natDegree ≤ 6 * n - g - (120 + 60 * (Q - 2)) at hiter
    exact maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_endpoint68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      (120 + 60 * (Q - 2)) N hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      (by simpa only [n, N] using hnform) (by omega)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 60 ∣ 5 * n - g - (120 + 60 * (Q - 2)) by
            obtain ⟨u, hu⟩ := hdphase
            refine ⟨u - (Q - 2), ?_⟩
            omega))
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hiter)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
        (show 120 + 60 * (Q - 2) + 30 = 7 * n - 2 * g by omega))

/-- Complete source-facing stride assembly: every radius phase now returns
only an earlier exact cusp or the symbolic terminal packet. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_completeStride68
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
  have hfinite := integratedPolynomialLowerSystem68_fiveToSix_finitePhase_or_large68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change (120 < n ∧ 30 ∣ n ∧ 30 ∣ g ∧
      (60 ∣ n ∨ (n % 60 = 30 ∧ ∀ s, g + s ≤ 5 * n →
        ¬ (60 ∣ 5 * n - g - s ∧ 60 ∣ 6 * n - g - s)))) ∨
    (∃ s, 0 < s ∧ s < 7 * n - 2 * g ∧
      FiveToSixCuspEdge68 Ae Be ce d ee n g s) ∨
    FiveToSixTerminalPacket68 zeta Ae Be ce d ee n g at hfinite
  rcases hfinite with hlarge | hcusp | hterminalPacket
  · rcases hlarge.2.2.2 with hn60 | hstaggered
    · exact integratedPolynomialLowerSystem68_fiveToSix_large_aligned68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by simpa only [n] using hlarge.1)
        (by simpa only [n] using hn60)
    · right
      exact integratedPolynomialLowerSystem68_fiveToSix_large_staggered68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by simpa only [n] using hlarge.1)
        (by simpa only [n] using hstaggered.1)
  · exact Or.inl hcusp
  · exact Or.inr hterminalPacket

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_iterate68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_staggered_endpoint68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_large_staggered68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_completeStride68

end FiveToSixCompleteStride68

end Max11DegreeRoutes
