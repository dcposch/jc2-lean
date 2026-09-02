import Grok68TerminalZeroCellsScratch

/-! # Large remainder of the `(6,8)` scale-zero terminal-zero packet

Untracked working note. No tracked file was edited.

Parent `Grok68TerminalZeroCellsScratch` closes `n=60`, `n=90`, `n=120`
(`g=330`), the unaligned `t=30` cusp (off-lattice), the aligned `t=60`
cusp (`14n+120<15n`), and the constant-`B` Q-higher `Y` certificate
(`8 c_n^3` at `3n` for `t>n/2`).  The residual was
`FiveToSixTerminalZeroLargeRemainder68`: aligned cusps at `t=60j` for
`j>1`, and leftover nonzero constant `d` on `120<n`.

This file inducts on the `60`-stride.  From a cusp at `t=60r`:

* `g<3n` or `14n+120r<15n` (`n>120r`): closable, reusing
  `fiveToSix_terminalZero_aligned_t60_cusp_closable68`.
* `g=3n` and `n<120r`: Q-higher `Y` certificate.
* `g=3n` and `n=120r`: the constant-`B` meeting cell `t=n/2`.

CAS `derive_68_terminal_zero_meeting.py` /
`derive_68_terminal_zero_meeting_elim.py` records that loaded row two
at `2n-1` is the mixed identity `8 J+(3/2) A_(2n) i_4=0` after `Fc`
is constant (the `γ A d'` / `γ d A'` pair cancels; `Extra` and `B c'`
drop below `2n-1`).  Together with `Y` at `3n`, the I4 face, and the
cusp this forces `i_4=(128/27) B_0^3`.  The next lattice coefficient
`tot2[2n-61]` is compatible with a geometric lower-jet progression, so
the meeting cell is not consumed here.

Leftover constant `d` is an extra beyond-wall edge at `t=g-2n`: vanish
forces source `d=0`; a cusp is Dpos-closable or Q-higher (`t=n` on
`g=3n`).  Unaligned `120<n` cusps are off-lattice; a vanish drops at
the binding extra-edge `t=g-2n-deg d` or `t=g-n-deg e`.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

Exact gain: stride induction on `t=60r`; leftover constant `d`;
unaligned `120<n` (cusp and dual extra-edge); mixed meeting identity
`8J+(3/2)A_(2n)i_4=0`.
Next unused row: meeting I3/tot2 lower jets after `i_4=(128/27)B_0^3`
(geometric `c_(n/2)` / `d_0` progression).
Residual: `FiveToSixTerminalZeroMeetingCell68`.
`IntegratedPolynomialLowerSystem68Exclusion` is not closed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalZeroLargeRemainder68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Named meeting residual -/

/-- Honest leftover after the stride induction: a constant-`B` meeting
cusp `t=n/2` with `120∣n` and `n≥240`.  Unaligned `120<n` is consumed
by the `t=30` off-lattice cusp, the `60`-lattice leftover `d=0`, and
the dual extra-edge at `t=g-2n-deg d` / `t=g-n-deg e`. -/
def FiveToSixTerminalZeroMeetingCell68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  120 < n ∧ FiveToSixTerminalZeroPacket68 zeta d e n g ∧
    240 ≤ n ∧ 120 ∣ n ∧ g = 3 * n ∧
    FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g + n / 2)

/-! ## Aligned cusp dispatch, excluding the meeting cell -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_aligned_cusp_closable_of68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (t : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
    (hd :
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
      d.natDegree ≤ g - 2 * n - t)
    (he :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ee.natDegree ≤ g - n - t)
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
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t))
    (hclosable :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < 3 * n ∨ 14 * n + 2 * t < 5 * g) :
    False :=
  fiveToSix_terminalTail_cusp_impossible_of_closable68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
    hterminal hsys hzeta htle hd he hcusp hclosable

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_aligned_cusp_nonmeeting_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (t : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
    (hd :
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
      d.natDegree ≤ g - 2 * n - t)
    (he :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ee.natDegree ≤ g - n - t)
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
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t))
    (hnonmeet :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬ (g = 3 * n ∧ n = 2 * t)) :
    False := by
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
  change t ≤ g - 2 * n at htle
  change d.natDegree ≤ g - 2 * n - t at hd
  change ee.natDegree ≤ g - n - t at he
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t) at hcusp
  change ¬ (g = 3 * n ∧ n = 2 * t) at hnonmeet
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hgle : g ≤ 3 * n := by
    obtain ⟨_, hw6⟩ := hwindow
    omega
  by_cases hD : g < 3 * n
  · exact fiveToSix_terminalZero_aligned_cusp_closable_of68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
      hterminal hsys hzeta htle hd he hcusp (Or.inl hD)
  · have hD0 : g = 3 * n := by omega
    by_cases hde : 2 * t < n
    · have hclosable : 14 * n + 2 * t < 5 * g := by
        rw [hD0]
        omega
      exact fiveToSix_terminalZero_aligned_cusp_closable_of68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
        hterminal hsys hzeta htle hd he hcusp (Or.inr hclosable)
    · have hQ : n < 2 * t := by
        have : ¬ (g = 3 * n ∧ n = 2 * t) := hnonmeet
        omega
      exact fiveToSix_terminalTail_cusp_impossible_of_constantB_Qhigher68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
        hterminal hsys hzeta htle hd he hcusp hD0 hQ

/-! ## Leftover constant `d`: extra edge at `t = g-2n` -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_leftover_constant_d_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hzeta : zeta = 0)
    (hd0 :
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
      d.natDegree ≤ 0)
    (he0 :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ee.natDegree ≤ n) :
    False := by
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
  change d.natDegree ≤ 0 at hd0
  change ee.natDegree ≤ n at he0
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, _, _, _, _⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hA : 2 ≤ A.natDegree := by
    have hdeg := fiveToSix_source_A_natDegree_eq68 A B C0 D E data.ha data.hA
    have hn30 : 30 ∣ n := hglobal.2.2.2.2.1
    have hnpos : 30 < n := hglobal.2.2.2.2.2.2.1
    obtain ⟨k, hk⟩ := hn30
    have hk2 : 2 ≤ k := by
      have hlt : 30 * 1 < 30 * k := by
        rw [mul_one]
        rwa [← hk]
      have : 1 < k := Nat.lt_of_mul_lt_mul_left hlt
      omega
    have : 2 ≤ n / 30 := by
      rw [hk, Nat.mul_div_cancel_left _ (by norm_num : 0 < 30)]
      exact hk2
    rwa [hdeg]
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have h2n : 2 * n ≤ g := by
    obtain ⟨hw5, _⟩ := hwindow
    omega
  have ht : 0 < g - 2 * n := by
    obtain ⟨hw5, _⟩ := hwindow
    omega
  have htle : g - 2 * n ≤ g - 2 * n := le_rfl
  have hd : d.natDegree ≤ g - 2 * n - (g - 2 * n) := by
    rw [Nat.sub_self]
    exact hd0
  have he : ee.natDegree ≤ g - n - (g - 2 * n) := by
    have hrew : g - (g - 2 * n) = 2 * n := Nat.sub_sub_self h2n
    have : g - n - (g - 2 * n) = 2 * n - n := by
      rw [Nat.sub_right_comm, hrew]
    rw [this]
    have : 2 * n - n = n := by omega
    rwa [this]
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      (g - 2 * n) hterminal hsys ht hwindow hzeta htle (⟨hd, he⟩)
  rcases hedge with hvan | hcusp
  · have hd00 : d.coeff 0 = 0 := by
      have hidx : g - 2 * n - (g - 2 * n) = 0 := Nat.sub_self _
      have h := hvan.1
      rwa [hidx] at h
    have hd_exp0 : d = 0 :=
      eq_zero_of_natDegree_le_zero_coeff_zero68 d hd0 hd00
    exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta hdelta
      hzeta
      (fiveToSix_source_d_of_expanded_zero68 A B D
        (by simpa only [d, Ae, Be, De] using hd_exp0)) hA
  · have hnm : ¬ (g = 3 * n ∧ n = 2 * (g - 2 * n)) := by
      intro ⟨hD0, hmeet⟩
      have : 2 * (g - 2 * n) = 2 * n := by
        rw [hD0]
        omega
      omega
    exact fiveToSix_terminalZero_aligned_cusp_nonmeeting_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      (g - 2 * n) hterminal hsys hzeta htle hd he hcusp hnm

theorem fiveToSix_sixty_dvd_gap_sub_two_n68 (n g : ℕ)
    (hn : 60 ∣ n) (hg : 60 ∣ g) (h2 : 2 * n ≤ g) :
    60 ∣ g - 2 * n := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨G, hG⟩ := hg
  refine ⟨G - 2 * N, ?_⟩
  have hle : 2 * N ≤ G := by
    have : 2 * (60 * N) ≤ 60 * G := by
      simpa [hN, hG] using h2
    have hmul : 2 * (60 * N) = 60 * (2 * N) := by ring
    exact fiveToSix_le_of_sixty_mul68 (by rwa [hmul] at this)
  rw [hN, hG]
  have hmul : 2 * (60 * N) = 60 * (2 * N) := by ring
  rw [hmul, ← Nat.mul_sub]

theorem fiveToSix_two_n_add_D_le_g68 (n g D : ℕ)
    (h2 : 2 * n ≤ g) (hD : D ≤ g - 2 * n) :
    2 * n + D ≤ g := by
  have h' : D + 2 * n ≤ g - 2 * n + 2 * n :=
    Nat.add_le_add_right hD (2 * n)
  have hc : g - 2 * n + 2 * n = g := Nat.sub_add_cancel h2
  have hD2 : D + 2 * n ≤ g := by
    rwa [hc] at h'
  rwa [Nat.add_comm D] at hD2

theorem fiveToSix_index_e_of_d_drop68 (n g D : ℕ)
    (h2 : 2 * n ≤ g) (hD : D ≤ g - 2 * n) :
    g - n - (g - 2 * n - D) = n + D := by
  have h2nD := fiveToSix_two_n_add_D_le_g68 n g D h2 hD
  have hsub : g - 2 * n - D = g - (2 * n + D) := Nat.sub_sub _ _ _
  rw [hsub, Nat.sub_right_comm, Nat.sub_sub_self h2nD]
  have hsplit : 2 * n + D = n + (n + D) := by
    rw [two_mul, Nat.add_assoc]
  rw [hsplit, Nat.add_sub_cancel_left]

theorem fiveToSix_n_add_E_le_g68 (n g E : ℕ)
    (h2 : 2 * n ≤ g) (hEg : E ≤ g - n) :
    n + E ≤ g := by
  have hn : n ≤ g :=
    (Nat.le_mul_of_pos_left n (by omega : 0 < 2)).trans h2
  have h' : n + E ≤ n + (g - n) := Nat.add_le_add_left hEg n
  have hc : n + (g - n) = g := Nat.add_sub_of_le hn
  rwa [hc] at h'

theorem fiveToSix_e_drop_le_gap_sub_two_n68 (n g E : ℕ)
    (h2 : 2 * n ≤ g) (hnE : n ≤ E) (hEg : E ≤ g - n) :
    g - n - E ≤ g - 2 * n := by
  have h1 : g - n - E = g - (n + E) := Nat.sub_sub _ _ _
  have h2' : g - 2 * n = g - (n + n) := by
    rw [two_mul]
  rw [h1, h2']
  exact Nat.sub_le_sub_left (Nat.add_le_add_left hnE n) g

theorem fiveToSix_index_d_of_e_drop68 (n g E : ℕ)
    (h2 : 2 * n ≤ g) (hnE : n ≤ E) (hEg : E ≤ g - n) :
    g - 2 * n - (g - n - E) = E - n := by
  have hnEadd := fiveToSix_n_add_E_le_g68 n g E h2 hEg
  have h1 : g - n - E = g - (n + E) := Nat.sub_sub _ _ _
  rw [h1, Nat.sub_right_comm, Nat.sub_sub_self hnEadd, two_mul,
    ← Nat.sub_sub, Nat.add_sub_cancel_left]

set_option maxHeartbeats 40000000 in
theorem fiveToSix_terminalZero_aligned_big_nonmeeting_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g)
    (hnbig : 120 < weightedRadius68 A B C0 D E)
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
    (hnonmeet :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬ (g = 3 * n ∧ 120 ∣ n)) :
    False := by
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
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  change 120 < n at hnbig
  change 60 ∣ n at hn60
  change 60 ∣ g at hg60
  change ¬ (g = 3 * n ∧ 120 ∣ n) at hnonmeet
  have hzeta : zeta = 0 := hpacket.2.2.1
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have h2n : 2 * n ≤ g := by
    obtain ⟨hw5, _⟩ := hwindow
    omega
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hgapd : 60 ∣ g - 2 * n :=
    fiveToSix_sixty_dvd_gap_sub_two_n68 n g hn60 hg60 h2n
  have hidx := fiveToSix_terminal_index_d68 n g hwindow
  have hdiv := fiveToSix_terminal_index_d_dvd68 n g hn60 hg60 hwindow
  have hsteps : ∀ r : ℕ,
      60 * r ≤ g - 2 * n →
      d.natDegree ≤ g - 2 * n - 60 * r ∧
        ee.natDegree ≤ g - n - 60 * r := by
    intro r
    induction r with
    | zero =>
        intro _
        exact ⟨hpacket.1, hpacket.2.1⟩
    | succ r ih =>
        intro hroomr
        have hprev := ih (by omega)
        by_cases hr0 : r = 0
        · subst r
          constructor
          · rw [hdexpand, ← hidx.2.2.1]
            refine natDegree_expand_le_sub_next_sixty68
              (secondaryDDefectPolynomial68 A B D) (5 * n - g)
              (7 * n - 2 * g) hdiv.1 (by
                have := hwindow.1
                have := hwindow.2
                omega) ?_ ?_
            · rw [hidx.1, ← hdexpand]
              exact hpacket.1
            · rw [hidx.1, ← hdexpand]
              exact hpacket.2.2.2.1
          · rw [heexpand, ← hidx.2.2.2]
            refine natDegree_expand_le_sub_next_sixty68
              (cubicEDefectPolynomial68 A C0 E) (6 * n - g)
              (7 * n - 2 * g) hdiv.2 (by
                have := hwindow.1
                have := hwindow.2
                omega) ?_ ?_
            · rw [hidx.2.1, ← heexpand]
              exact hpacket.2.1
            · rw [hidx.2.1, ← heexpand]
              exact hpacket.2.2.2.2
        · have htpos : 0 < 60 * r := by omega
          have htle : 60 * r ≤ g - 2 * n := by omega
          have hedge :=
            maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
              l alpha beta gamma delta epsilon zeta eta terminal
              A B C0 D E (60 * r) hterminal hsys htpos hwindow hzeta htle
              hprev
          rcases hedge with hvan | hcusp
          · obtain ⟨N, hN⟩ := hn60
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
              · simpa [hN, hG] using hnext_d
              · simpa [hN, hG] using h2n
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
                (by
                  have : d.coeff (g - 2 * n - 60 * r) = 0 := hvan.1
                  simpa [hdexpand] using this)
            · rw [heexpand]
              exact natDegree_expand_le_sub_next_sixty68
                (cubicEDefectPolynomial68 A C0 E) (g - n)
                (60 * r) hephase hnext_e
                (by simpa only [heexpand] using hprev.2)
                (by
                  have : ee.coeff (g - n - 60 * r) = 0 := hvan.2
                  simpa [heexpand] using this)
          · have hnonmeet' : ¬ (g = 3 * n ∧ n = 2 * (60 * r)) := by
              intro ⟨hD0, hmeet⟩
              have : 120 * r = n := by omega
              exact hnonmeet ⟨hD0, ⟨r, by omega⟩⟩
            exact False.elim
              (fiveToSix_terminalZero_aligned_cusp_nonmeeting_impossible68
                l alpha beta gamma delta epsilon zeta eta terminal
                A B C0 D E (60 * r) hterminal hsys hzeta htle hprev.1
                hprev.2 hcusp hnonmeet')
  have hleft := hsteps ((g - 2 * n) / 60) (Nat.mul_div_le (g - 2 * n) 60)
  have hm : 60 * ((g - 2 * n) / 60) = g - 2 * n :=
    Nat.mul_div_cancel' hgapd
  have hdle : d.natDegree ≤ 0 := by
    have h := hleft.1
    rw [hm] at h
    have : g - 2 * n - (g - 2 * n) = 0 := Nat.sub_self _
    rwa [this] at h
  have hele : ee.natDegree ≤ n := by
    have h := hleft.2
    rw [hm] at h
    have hrew : g - (g - 2 * n) = 2 * n := Nat.sub_sub_self h2n
    have hidx : g - n - (g - 2 * n) = n := by
      have : g - n - (g - 2 * n) = 2 * n - n := by
        rw [Nat.sub_right_comm, hrew]
      rw [this]
      omega
    rwa [hidx] at h
  exact fiveToSix_terminalZero_leftover_constant_d_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hzeta hdle hele

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_unaligned_big_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g)
    (hnbig : 120 < weightedRadius68 A B C0 D E)
    (hunalign :
      let n := weightedRadius68 A B C0 D E
      ¬ 60 ∣ n ∨
        let Ae := expand k 60 A
        let Be := expand k 60 B
        let Ce := expand k 60 C0
        let ce := cubicCDefectPolynomial68 Ae Ce
        let De := expand k 60 D
        let Ee := expand k 60 E
        let ee := cubicEDefectPolynomial68 Ae Ce Ee
        let g := cubicDefectGap68 n Be ce De ee
        ¬ 60 ∣ g) :
    False := by
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
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  change 120 < n at hnbig
  have hzeta : zeta = 0 := hpacket.2.2.1
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hcusp_off (t : ℕ) (htle : t ≤ g - 2 * n)
      (hcusp : FiveToSixCuspEdge68 Ae Be ce d ee n g
        (7 * n - 2 * g + t)) : False := by
    have hcusp' :
        FiveToSixCuspEdge68 (expand k 60 A) (expand k 60 B)
          (expand k 60 (cubicCDefectPolynomial68 A C0))
          (expand k 60 (secondaryDDefectPolynomial68 A B D))
          (expand k 60 (cubicEDefectPolynomial68 A C0 E)) n g
          (7 * n - 2 * g + t) := by
      simpa [Ae, Be, ← hcexpand, ← hdexpand, ← heexpand] using hcusp
    have halign :=
      fiveToSix_expanded_cusp_alignment68 A B
        (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + t)
        (by
          obtain ⟨_, hw6⟩ := hwindow
          omega) (by
          obtain ⟨hw5, _⟩ := hwindow
          have : 2 * n + t ≤ g := by omega
          omega) hcusp'
    rcases hunalign with hn | hg
    · exact hn halign.1
    · exact hg halign.2.1
  have hn30 : 30 ∣ n := hglobal.2.2.2.2.1
  have hg30 : 30 ∣ g := hglobal.2.2.2.2.2.1
  have h2n : 2 * n ≤ g := by
    obtain ⟨hw5, _⟩ := hwindow
    omega
  have htle30 : 30 ≤ g - 2 * n := by
    obtain ⟨hw5, _⟩ := hwindow
    omega
  have hd30 : d.natDegree ≤ g - 2 * n - 30 := by
    rw [hdexpand]
    by_cases hdv : 60 ∣ g - 2 * n
    · have hsixty : 60 ≤ g - 2 * n := by omega
      have := fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
        (secondaryDDefectPolynomial68 A B D) (g - 2 * n) hdv hsixty
        (by simpa [hdexpand] using hpacket.1)
        (by simpa [hdexpand] using hpacket.2.2.2.1)
      omega
    · have hfloor := fiveToSix_expand_natDegree_le_sixty_floor68
        (secondaryDDefectPolynomial68 A B D) (g - 2 * n)
        (by simpa [hdexpand] using hpacket.1)
      have : 60 * ((g - 2 * n) / 60) ≤ g - 2 * n - 30 := by
        have hrem : (g - 2 * n) % 60 ≠ 0 := fun hz =>
          hdv (Nat.dvd_iff_mod_eq_zero.mpr hz)
        have hdivmod := Nat.div_add_mod (g - 2 * n) 60
        have : (g - 2 * n) % 60 = 30 := by
          have : 30 ∣ g - 2 * n := by
            obtain ⟨N, hN⟩ := hn30
            obtain ⟨G, hG⟩ := hg30
            refine ⟨G - 2 * N, ?_⟩
            have hle : 2 * N ≤ G := by
              have : 2 * (30 * N) ≤ 30 * G := by
                simpa [hN, hG] using h2n
              have hmul : 2 * (30 * N) = 30 * (2 * N) := by ring
              rw [hmul] at this
              exact Nat.le_of_mul_le_mul_left this (by norm_num : 0 < 30)
            rw [hN, hG]
            have hmul : 2 * (30 * N) = 30 * (2 * N) := by ring
            rw [hmul, ← Nat.mul_sub]
          obtain ⟨q, hq⟩ := this
          have hparity : q % 2 = 0 ∨ q % 2 = 1 := Nat.mod_two_eq_zero_or_one q
          rcases hparity with hev | hodd
          · obtain ⟨k, hk⟩ := Nat.dvd_iff_mod_eq_zero.mpr hev
            have : g - 2 * n = 60 * k := by
              rw [hq, hk]
              ring
            exact False.elim (hdv ⟨k, this⟩)
          · have hdivmod' := Nat.div_add_mod q 2
            rw [hodd] at hdivmod'
            have : 30 * q = 30 * (2 * (q / 2) + 1) := by omega
            have : 30 * q = 60 * (q / 2) + 30 := by
              convert this using 1
              ring
            have : (g - 2 * n) % 60 = 30 := by
              rw [hq, this]
              omega
            exact this
        omega
      omega
  have he30 : ee.natDegree ≤ g - n - 30 := by
    rw [heexpand]
    by_cases hdv : 60 ∣ g - n
    · have hsixty : 60 ≤ g - n := by omega
      have := fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
        (cubicEDefectPolynomial68 A C0 E) (g - n) hdv hsixty
        (by simpa [heexpand] using hpacket.2.1)
        (by simpa [heexpand] using hpacket.2.2.2.2)
      omega
    · have hfloor := fiveToSix_expand_natDegree_le_sixty_floor68
        (cubicEDefectPolynomial68 A C0 E) (g - n)
        (by simpa [heexpand] using hpacket.2.1)
      have : 60 * ((g - n) / 60) ≤ g - n - 30 := by
        have : (g - n) % 60 ≠ 0 := fun hz =>
          hdv (Nat.dvd_iff_mod_eq_zero.mpr hz)
        omega
      omega
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
      hterminal hsys (by omega) hwindow hzeta htle30 (⟨hd30, he30⟩)
  rcases hedge with hvan | hcusp
  · have hdeq : d.natDegree =
        60 * (secondaryDDefectPolynomial68 A B D).natDegree := by
      rw [hdexpand, natDegree_expand, mul_comm]
    have heeq : ee.natDegree =
        60 * (cubicEDefectPolynomial68 A C0 E).natDegree := by
      rw [heexpand, natDegree_expand, mul_comm]
    rcases lt_or_ge d.natDegree 60 with hdlt | hdge
    · rcases lt_or_ge ee.natDegree 60 with helt | hege
      · have hd0 : d.natDegree ≤ 0 := by
          have : (secondaryDDefectPolynomial68 A B D).natDegree = 0 := by
            have : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
                < 60 := by rwa [← hdeq]
            omega
          rw [hdeq, this]
        have hele : ee.natDegree ≤ n := by
          have : (cubicEDefectPolynomial68 A C0 E).natDegree = 0 := by
            have : 60 * (cubicEDefectPolynomial68 A C0 E).natDegree
                < 60 := by rwa [← heeq]
            omega
          rw [heeq, this]
          omega
        exact fiveToSix_terminalZero_leftover_constant_d_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys hzeta hd0 hele
      · have hd0 : d.natDegree ≤ 0 := by
          have : (secondaryDDefectPolynomial68 A B D).natDegree = 0 := by
            have : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
                < 60 := by rwa [← hdeq]
            omega
          rw [hdeq, this]
        by_cases hEn : ee.natDegree ≤ n
        · exact fiveToSix_terminalZero_leftover_constant_d_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys hzeta hd0 hEn
        · have htpos : 0 < g - n - ee.natDegree := by
            have : ee.natDegree ≤ g - n - 30 := he30
            omega
          have htle : g - n - ee.natDegree ≤ g - 2 * n := by
            have : n ≤ ee.natDegree := Nat.le_of_not_ge (fun h => hEn h)
            omega
          have hd' : d.natDegree ≤ g - 2 * n - (g - n - ee.natDegree) := by
            have := hd0
            omega
          have he' : ee.natDegree ≤ g - n - (g - n - ee.natDegree) := by
            have : ee.natDegree ≤ g - n :=
              le_trans he30 (Nat.sub_le _ _)
            have : g - n - (g - n - ee.natDegree) = ee.natDegree :=
              Nat.sub_sub_self this
            omega
          have hedge' :=
            maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
              l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
              (g - n - ee.natDegree) hterminal hsys htpos hwindow hzeta htle
              ⟨hd', he'⟩
          rcases hedge' with hvan' | hcusp'
          · have hele0 : ee.natDegree ≤ n := by
              have hidx : g - n - (g - n - ee.natDegree) = ee.natDegree := by
                have : ee.natDegree ≤ g - n :=
                  le_trans he30 (Nat.sub_le _ _)
                exact Nat.sub_sub_self this
              have : ee.coeff ee.natDegree = 0 := by
                have h := hvan'.2
                rwa [hidx] at h
              have : ee = 0 := by
                rw [← leadingCoeff_eq_zero, leadingCoeff]
                rwa [coeff_natDegree] at this
              have : ee.natDegree = 0 := by rw [this, natDegree_zero]
              exact this.symm ▸ Nat.zero_le n
            exact fiveToSix_terminalZero_leftover_constant_d_impossible68
              l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
              hterminal hsys hzeta hd0 hele0
          · exact hcusp_off (g - n - ee.natDegree) htle hcusp'
    · have hDle : d.natDegree ≤ g - 2 * n :=
        le_trans hd30 (Nat.sub_le _ _)
      have hEle : ee.natDegree ≤ g - n :=
        le_trans he30 (Nat.sub_le _ _)
      by_cases hdropD : ee.natDegree ≤ n + d.natDegree
      · have htpos : 0 < g - 2 * n - d.natDegree := by
          have : d.natDegree ≤ g - 2 * n - 30 := hd30
          omega
        have htle : g - 2 * n - d.natDegree ≤ g - 2 * n := Nat.sub_le _ _
        have hd' : d.natDegree ≤ g - 2 * n - (g - 2 * n - d.natDegree) :=
          (Nat.sub_sub_self hDle).symm ▸ le_rfl
        have he' : ee.natDegree ≤ g - n - (g - 2 * n - d.natDegree) := by
          rw [fiveToSix_index_e_of_d_drop68 n g d.natDegree h2n hDle]
          exact hdropD
        have hedge' :=
          maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            (g - 2 * n - d.natDegree) hterminal hsys htpos hwindow hzeta htle
            ⟨hd', he'⟩
        rcases hedge' with hvan' | hcusp'
        · have hd00 : d.coeff d.natDegree = 0 := by
            have hidx : g - 2 * n - (g - 2 * n - d.natDegree) =
                d.natDegree := Nat.sub_sub_self hDle
            have h := hvan'.1
            rwa [hidx] at h
          have : d = 0 := by
            rw [← leadingCoeff_eq_zero, leadingCoeff]
            rwa [coeff_natDegree] at hd00
          have : d.natDegree = 0 := by rw [this, natDegree_zero]
          omega
        · exact hcusp_off (g - 2 * n - d.natDegree) htle hcusp'
      · have hlt : n + d.natDegree < ee.natDegree := Nat.not_le.mp hdropD
        have hnE : n ≤ ee.natDegree :=
          (Nat.le_add_right n d.natDegree).trans (Nat.le_of_lt hlt)
        have htpos : 0 < g - n - ee.natDegree := by
          have : ee.natDegree ≤ g - n - 30 := he30
          omega
        have htle : g - n - ee.natDegree ≤ g - 2 * n :=
          fiveToSix_e_drop_le_gap_sub_two_n68 n g ee.natDegree h2n hnE hEle
        have hd' : d.natDegree ≤ g - 2 * n - (g - n - ee.natDegree) := by
          rw [fiveToSix_index_d_of_e_drop68 n g ee.natDegree h2n hnE hEle]
          have hsum : d.natDegree + n ≤ ee.natDegree := by
            rw [Nat.add_comm]
            exact le_of_lt hlt
          exact (Nat.le_sub_iff_add_le hnE).mpr hsum
        have he' : ee.natDegree ≤ g - n - (g - n - ee.natDegree) :=
          (Nat.sub_sub_self hEle).symm ▸ le_rfl
        have hedge' :=
          maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            (g - n - ee.natDegree) hterminal hsys htpos hwindow hzeta htle
            ⟨hd', he'⟩
        rcases hedge' with hvan' | hcusp'
        · have he00 : ee.coeff ee.natDegree = 0 := by
            have hidx : g - n - (g - n - ee.natDegree) =
                ee.natDegree := Nat.sub_sub_self hEle
            have h := hvan'.2
            rwa [hidx] at h
          have : ee = 0 := by
            rw [← leadingCoeff_eq_zero, leadingCoeff]
            rwa [coeff_natDegree] at he00
          have : ee.natDegree = 0 := by rw [this, natDegree_zero]
          omega
        · exact hcusp_off (g - n - ee.natDegree) htle hcusp'
  · have hcusp' :
        FiveToSixCuspEdge68 (expand k 60 A) (expand k 60 B)
          (expand k 60 (cubicCDefectPolynomial68 A C0))
          (expand k 60 (secondaryDDefectPolynomial68 A B D))
          (expand k 60 (cubicEDefectPolynomial68 A C0 E)) n g
          (7 * n - 2 * g + 30) := by
      simpa [Ae, Be, ← hcexpand, ← hdexpand, ← heexpand] using hcusp
    have halign :=
      fiveToSix_expanded_cusp_alignment68 A B
        (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
        (by
          obtain ⟨_, hw6⟩ := hwindow
          omega) (by
          obtain ⟨hw5, _⟩ := hwindow
          have : 2 * n + 30 ≤ g := by omega
          omega) hcusp'
    rcases hunalign with hn | hg
    · exact hn halign.1
    · exact hg halign.2.1

/-! ## `120 < n` excluding the meeting cell -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_big_nonmeeting_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g)
    (hnbig :
      let n := weightedRadius68 A B C0 D E
      120 < n)
    (hnonmeet :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬ (g = 3 * n ∧ 120 ∣ n)) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  by_cases hn60 : 60 ∣ n
  · by_cases hg60 : 60 ∣ g
    · exact fiveToSix_terminalZero_aligned_big_nonmeeting_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hpacket hnbig hn60 hg60 hnonmeet
    · exact fiveToSix_terminalZero_unaligned_big_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hpacket hnbig (Or.inr hg60)
  · exact fiveToSix_terminalZero_unaligned_big_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hpacket hnbig (Or.inl hn60)

/-! ## Terminal-zero packet excluding the meeting cell -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_nonmeeting_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g)
    (hnonmeet :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬ (240 ≤ n ∧ 120 ∣ n ∧ g = 3 * n)) :
    False := by
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
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  change ¬ (240 ≤ n ∧ 120 ∣ n ∧ g = 3 * n) at hnonmeet
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  rcases hglobal with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, holdCases⟩
  rcases holdCases with hn60g | hn90 | hn120 | hbig
  · exact fiveToSix_terminalZero_n60_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn60g.1 hpacket
  · exact fiveToSix_terminalZero_n90_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn90.1
  · exact fiveToSix_terminalZero_n120_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn120.1 hpacket
  · have hnbig : 120 < n := hbig
    have hnm : ¬ (g = 3 * n ∧ 120 ∣ n) := by
      intro ⟨hD0, h120⟩
      have : 240 ≤ n := by omega
      exact hnonmeet ⟨this, h120, hD0⟩
    exact fiveToSix_terminalZero_big_nonmeeting_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hpacket hnbig hnm

/-! ## Thin residual excluding the meeting cell -/

set_option maxHeartbeats 25000000 in
theorem integratedPolynomialLowerSystem68_thinResidual_nonmeeting_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hres : IntegratedPolynomialLowerSystem68ThinResidual alpha gamma
      epsilon zeta eta terminal A B C0 D E)
    (hnonmeet :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ¬ (240 ≤ n ∧ 120 ∣ n ∧ g = 3 * n)) :
    False := by
  dsimp only [IntegratedPolynomialLowerSystem68ThinResidual] at hres
  rcases hres with hzero | hvan | hterm
  · exact fiveToSix_terminalZero_nonmeeting_impossible68 l alpha beta gamma
      delta epsilon zeta eta terminal A B C0 D E hterminal hsys hzero
      hnonmeet
  · obtain ⟨N, G, S, _, _, hvan'⟩ := hvan
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_open_impossible68
      alpha gamma epsilon zeta eta terminal A B
      (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S hterminal hvan'
  · exact fiveToSix_largeTerminal_allNonzero_cusp_impossible68 l alpha beta
      gamma delta epsilon zeta eta terminal A B C0 D E hterminal hsys
      hterm

#print axioms fiveToSix_terminalZero_aligned_cusp_nonmeeting_impossible68
#print axioms fiveToSix_terminalZero_leftover_constant_d_impossible68
#print axioms fiveToSix_terminalZero_aligned_big_nonmeeting_impossible68
#print axioms fiveToSix_terminalZero_unaligned_big_impossible68
#print axioms fiveToSix_terminalZero_nonmeeting_impossible68
#print axioms integratedPolynomialLowerSystem68_thinResidual_nonmeeting_impossible68

end FiveToSixTerminalZeroLargeRemainder68

end Max11DegreeRoutes

