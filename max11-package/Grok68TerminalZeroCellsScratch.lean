import Grok68TerminalTailClosureScratch

/-! # Terminal-zero cells of the `(6,8)` scale-zero residual

Untracked working note. No tracked file was edited.

Parent `Grok68TerminalTailClosureScratch` closes every `D>0` cell, the
constant-`B` `de`-higher cell `t<n/2`, the at-wall large terminal
all-nonzero cusp, and `fiveToSix_terminalZero_impossible68` on `n=30`
and on source `d=0` with `n≤120`.  The remaining thin-residual cells
are the beyond-wall constant-`B` cusp `t≥n/2` (model `n=60`, `g=180`,
the terminal-zero successor) and the unaligned `n=90` staggered
support, together with the `n=120` and `120<n` terminal-zero children.

This file salvages the kernel-accepted constant-`B` Q-higher `Y`
certificate and the `n=60` successor from the previous ungreen draft.

CAS `derive_68_terminal_zero_constant_B.py` records: for `g=3n` and
`t>n/2`, loaded row one at `3n-1` is the `Y` top `A B² c` / `c³` after
the `ε` mix of `A c'` cancels the `Rc` contribution at `deg c=n`.  On
the cusp this is `8 c_n³`.  The `n=60` successor is a lattice drop of
the terminal-zero tops, then `beyondWallEdge` at `t=60`: vanish forces
source `d=0`, cusp is Q-higher.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

Exact gain: constant-`B` Q-higher `Y` certificate (`8 c_n³`);
`n=60` successor; `n=90` (`B≠0` via I3 `ABd`, `B=0` constant `d≠0`
via source row-zero `U=(4/9)AD+αD`); `n=120` `g=330` with explicit
floor bounds and the collapsed-cusp comparison `g=3n`; unaligned
`t=30` cusps off-lattice; aligned `t=60` cusps closable
(`14n+120<15n`).
Next unused row: constant-`B` meeting I3-at-`deg c=n` (`ABd`/`ce` on
a general `A`) and the row-two `ε` mix of `B A'` at `2n-1`
(`derive_68_terminal_zero_meeting.py`).
Residual: `FiveToSixTerminalZeroLargeRemainder68` (aligned cusps at
`60j` for `j>1`, including meeting `t=n/2` when `120∣n`; leftover
nonzero constant `d` on `120<n`).
`IntegratedPolynomialLowerSystem68Exclusion` is not closed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalZeroCells68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## `Rc` at `deg c = n` on constant `B` -/

theorem fiveToSix_terminalTail_Rc_coeff_deg_c_constantB68
    (gamma epsilon i3 : k) (A B c d e : k[X]) (n : ℕ)
    (hn : 0 < n) (hB : B.natDegree ≤ 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rc := R + (9 / 2 * gamma : k) • e
    Rc.coeff n = -((9 / 4 : k) * epsilon) * c.coeff n := by
  intro R Rc
  have h := fiveToSix_terminalTail_Rc_of_I3_constant68 gamma epsilon i3
    A B c d e hi3
  dsimp only [R, Rc] at h ⊢
  rw [h]
  have hn0 : n ≠ 0 := by omega
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_C,
    ite_eq_right hn0]
  have hB2 : (B ^ 2).coeff n = 0 := by
    have hdeg : (B ^ 2).natDegree ≤ 0 := by
      compute_degree
      omega
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
  rw [hB2]
  ring

/-! ## `Y` at `3n` on constant `B` (`g=3n`, `t ≥ n/2`) -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalTail_Y_coeff_constantB68
    (alpha gamma epsilon eta i3 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hD0 : g = 3 * n)
    (hge : n ≤ 2 * t)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff (3 * n) = 0 := by
  intro Y
  let D0 := (1 / 3 : k) • (A * B) + d
  let R := -(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2
  let Rc := R + (9 / 2 * gamma : k) • e
  let Extra := FiveToSixTerminalTailRowOneExtra68 A B c d e
  let TY := 3 * n
  let K := TY - 1
  have hB0 : B.natDegree ≤ 0 := by
    have : 3 * n - g = 0 := by omega
    omega
  have hBder : derivative B = 0 := by
    rw [eq_C_of_natDegree_le_zero hB0, derivative_C]
  have hg2 : 2 * n ≤ g := by
    obtain ⟨_, hw6⟩ := hwindow
    omega
  have hKpos : 0 < K := by
    dsimp only [K, TY]
    omega
  have hCc : 4 * n - g = n := by omega
  have hRcdeg : Rc.natDegree ≤ n := by
    dsimp only [Rc, R]
    have hraw := fiveToSix_terminalTail_Rc_natDegree68 gamma epsilon i3
      A B c d e n g hg2 hc hB hi3
    dsimp only [R, Rc] at hraw
    have : 4 * n - g = n := hCc
    omega
  have hExlt : Extra.natDegree < K := by
    have hg : g ≤ 3 * n := by omega
    have htle' : 2 * n + t ≤ g := by omega
    have hraw := fiveToSix_terminalTail_Extra1_natDegree68 A B c d e n g t
      hg htle' hB hc hd he
    dsimp only [Extra] at hraw ⊢
    have : 5 * n - g - t < K := by
      dsimp only [K, TY]
      omega
    exact lt_of_le_of_lt hraw this
  have hD0deg : D0.natDegree ≤ 2 * n := by
    have hraw := fiveToSix_terminalTail_D0_natDegree68 A B d n g t
      hwindow htle hA hB hd
    have : 5 * n - g = 2 * n := by omega
    have h' : D0.natDegree ≤ 5 * n - g := by
      simpa [D0] using hraw
    omega
  have hBD0lt : (B * derivative D0).natDegree < K := by
    have hdD : (derivative D0).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le D0).trans (by omega)
    have hmul := natDegree_mul_le (p := B) (q := derivative D0)
    have : B.natDegree + (derivative D0).natDegree < K := by
      dsimp only [K, TY]
      omega
    exact lt_of_le_of_lt hmul this
  have hD0Blt : (D0 * derivative B).natDegree < K := by
    simp [hBder]
    exact hKpos
  have hcclt : (c * derivative c).natDegree < K := by
    have hd : (derivative c).natDegree ≤ n - 1 :=
      (natDegree_derivative_le c).trans (by omega)
    have hmul := natDegree_mul_le (p := c) (q := derivative c)
    have : c.natDegree + (derivative c).natDegree < K := by
      dsimp only [K, TY]
      omega
    exact lt_of_le_of_lt hmul this
  have helt : (derivative e).natDegree < K := by
    have hle : (derivative e).natDegree ≤ g - n - t :=
      (natDegree_derivative_le e).trans (by omega)
    have : g - n - t < K := by
      dsimp only [K, TY]
      omega
    omega
  have hload :=
    fiveToSix_terminalTail_load_rowOne_translated68 alpha gamma epsilon
      eta A B c d e
  have hsum :
      secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0 := hrow
  rw [hload] at hsum
  have hcancel :=
    fiveToSix_terminalTail_rowOne_cancelled68 gamma A B c d e
  have hBD00 :
      (B * derivative ((1 / 3 : k) • (A * B) + d)).coeff K = 0 := by
    simpa [D0] using coeff_eq_zero_of_natDegree_lt hBD0lt
  have hD0B0 :
      (((1 / 3 : k) • (A * B) + d) * derivative B).coeff K = 0 := by
    simpa [D0] using coeff_eq_zero_of_natDegree_lt hD0Blt
  have hcc0 : (c * derivative c).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hcclt
  have he0 : (derivative e).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt helt
  have hrowAe :
      (secondaryResidualRowOnePolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative e)).coeff K +
        (2 / 3 * epsilon : k) * (A * derivative c).coeff K = 0 := by
    have hK := congrArg (fun p : k[X] => p.coeff K) hsum
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_zero,
      hBD00, hD0B0, hcc0, he0, mul_zero, add_zero, sub_zero, zero_mul,
      neg_zero] at hK
    simp only [coeff_add, coeff_smul, smul_eq_mul]
    linear_combination hK
  have hEx0 : Extra.coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hExlt
  have hcancelK :
      (secondaryResidualRowOnePolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative e)).coeff K =
        ((-4 / 27 : k) •
          (derivative Y - (2 : k) • (A * derivative Rc) + Extra)).coeff K := by
    have h := congrArg (fun p : k[X] => p.coeff K) hcancel
    dsimp only [R, Rc, Extra, Y] at h ⊢
    simpa using h
  have hmix :
      ((-4 / 27 : k) •
          (derivative Y - (2 : k) • (A * derivative Rc) + Extra)).coeff K +
        (2 / 3 * epsilon : k) * (A * derivative c).coeff K = 0 := by
    rw [← hcancelK]
    exact hrowAe
  have hRc_n :
      Rc.coeff n = -((9 / 4 : k) * epsilon) * c.coeff n :=
    fiveToSix_terminalTail_Rc_coeff_deg_c_constantB68 gamma epsilon i3
      A B c d e n hn hB0 hi3
  have hdRc : (derivative Rc).natDegree ≤ n - 1 :=
    (natDegree_derivative_le Rc).trans (by omega)
  have hdc : (derivative c).natDegree ≤ n - 1 :=
    (natDegree_derivative_le c).trans (by omega)
  have hidx : 2 * n + (n - 1) = K := by
    dsimp only [K, TY]
    omega
  have hARc :
      (A * derivative Rc).coeff K =
        A.coeff (2 * n) * ((n : k) * Rc.coeff n) := by
    have hmul := coeff_mul_at_bounds68 A (derivative Rc) (2 * n) (n - 1)
      hA hdRc
    have hderc : (derivative Rc).coeff (n - 1) =
        Rc.coeff n * (n : k) :=
      coeff_derivative_at_bound68 Rc n hn
    rw [hidx] at hmul
    rw [hmul, hderc]
    ring
  have hAc :
      (A * derivative c).coeff K =
        A.coeff (2 * n) * ((n : k) * c.coeff n) := by
    have hmul := coeff_mul_at_bounds68 A (derivative c) (2 * n) (n - 1)
      hA hdc
    have hderc : (derivative c).coeff (n - 1) =
        c.coeff n * (n : k) :=
      coeff_derivative_at_bound68 c n hn
    rw [hidx] at hmul
    rw [hmul, hderc]
    ring
  have hY' : (derivative Y).coeff K = 0 := by
    have hexp :
        ((-4 / 27 : k) •
            (derivative Y - (2 : k) • (A * derivative Rc) + Extra)).coeff K +
          (2 / 3 * epsilon : k) * (A * derivative c).coeff K =
          (-4 / 27 : k) *
              ((derivative Y).coeff K -
                (2 : k) * (A * derivative Rc).coeff K + Extra.coeff K) +
            (2 / 3 * epsilon : k) * (A * derivative c).coeff K := by
      simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
    rw [hexp, hEx0, hARc, hAc, hRc_n] at hmix
    have hred :
        (-4 / 27 : k) *
            ((derivative Y).coeff K -
              (2 : k) * (A.coeff (2 * n) * ((n : k) *
                (-((9 / 4 : k) * epsilon) * c.coeff n))) + 0) +
          (2 / 3 * epsilon : k) *
            (A.coeff (2 * n) * ((n : k) * c.coeff n)) =
          (-4 / 27 : k) * (derivative Y).coeff K := by
      ring
    rw [hred] at hmix
    exact (mul_eq_zero.mp hmix).resolve_left (by norm_num : (-4 / 27 : k) ≠ 0)
  have hder : (derivative Y).coeff K = ((K : k) + 1) * Y.coeff (K + 1) := by
    rw [coeff_derivative, mul_comm]
  have hcast : ((K : k) + 1) ≠ 0 := by
    have hk : K + 1 ≠ 0 := by
      dsimp only [K, TY]
      omega
    have hcst : ((K + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast hk
    push_cast at hcst
    exact hcst
  rw [hder] at hY'
  have hY0 : Y.coeff (K + 1) = 0 :=
    (mul_eq_zero.mp hY').resolve_left hcast
  have hK1 : K + 1 = TY := by
    dsimp only [K]
    omega
  rwa [hK1] at hY0

/-! ## Q-higher: `Y` reduces to `A B² c` / `c³` -/

theorem fiveToSix_terminalTail_Y_AB2c_constantB_Qhigher68
    (A B c d e : k[X]) (n g t : ℕ)
    (hD0 : g = 3 * n) (hQ : n < 2 * t)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff (3 * n) =
      -(2 : k) * A.coeff (2 * n) * B.coeff 0 ^ 2 * c.coeff n +
        (2 : k) * c.coeff n ^ 3 := by
  intro Y
  have hB0 : B.natDegree ≤ 0 := by
    have : 3 * n - g = 0 := by omega
    omega
  have hAd2 : (A * d ^ 2).coeff (3 * n) = 0 := by
    have hd2 : (d ^ 2).natDegree ≤ 2 * (g - 2 * n - t) := by
      have h := (natDegree_pow (p := d) (n := 2)).le
      have : 2 * d.natDegree ≤ 2 * (g - 2 * n - t) :=
        Nat.mul_le_mul_left 2 hd
      omega
    have hmul := (natDegree_mul_le (p := A) (q := d ^ 2)).trans
      (Nat.add_le_add hA hd2)
    have : 2 * n + 2 * (g - 2 * n - t) < 3 * n := by omega
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hmul this)
  have he2 : (e ^ 2).coeff (3 * n) = 0 := by
    have h : (e ^ 2).natDegree ≤ 2 * (g - n - t) := by
      have hp := (natDegree_pow (p := e) (n := 2)).le
      have : 2 * e.natDegree ≤ 2 * (g - n - t) :=
        Nat.mul_le_mul_left 2 he
      omega
    have : 2 * (g - n - t) < 3 * n := by omega
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h this)
  have hBC : B ^ 2 = C (B.coeff 0 ^ 2) := by
    have hC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB0
    rw [hC]
    simp [C_pow]
  have hAc : (A * c).coeff (3 * n) =
      A.coeff (2 * n) * c.coeff n := by
    have hmul := coeff_mul_at_bounds68 A c (2 * n) n hA (by omega)
    have : 2 * n + n = 3 * n := by omega
    rwa [this] at hmul
  have hAB2c : (A * B ^ 2 * c).coeff (3 * n) =
      A.coeff (2 * n) * B.coeff 0 ^ 2 * c.coeff n := by
    rw [hBC, show A * C (B.coeff 0 ^ 2) * c = C (B.coeff 0 ^ 2) * (A * c) by
      ring]
    rw [coeff_C_mul, hAc]
    ring
  have hc3 : (c ^ 3).coeff (3 * n) = c.coeff n ^ 3 :=
    coeff_pow_at_bound68 c n 3 (by omega)
  simp only [Y, coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul,
    hAd2, he2, hAB2c, hc3]
  ring

theorem fiveToSix_terminalTail_constantB_Qhigher_cusp_false68
    (alpha gamma epsilon eta i3 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n) (hD0 : g = 3 * n)
    (hQ : n < 2 * t)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff 0 ≠ 0)
    (hc0 : c.coeff n ≠ 0)
    (hcusp : A.coeff (2 * n) * B.coeff 0 ^ 2 + (3 : k) * c.coeff n ^ 2 = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hge : n ≤ 2 * t := by omega
  have hY0 :=
    fiveToSix_terminalTail_Y_coeff_constantB68 alpha gamma epsilon eta i3
      A B c d e n g t hn hwindow htle hD0 hge hA hB hc hd he hi3 hrow
  have hYtop :=
    fiveToSix_terminalTail_Y_AB2c_constantB_Qhigher68 A B c d e n g t
      hD0 hQ htle hA hB hc hd he
  have hY :
      -(2 : k) * A.coeff (2 * n) * B.coeff 0 ^ 2 * c.coeff n +
        (2 : k) * c.coeff n ^ 3 = 0 := by
    dsimp only at hY0 hYtop
    rwa [hYtop] at hY0
  have hab :
      A.coeff (2 * n) * B.coeff 0 ^ 2 = -((3 : k) * c.coeff n ^ 2) :=
    add_eq_zero_iff_eq_neg.mp hcusp
  have h8 : (8 : k) * c.coeff n ^ 3 = 0 := by
    have hY' :
        -2 * (A.coeff (2 * n) * B.coeff 0 ^ 2) * c.coeff n +
          2 * c.coeff n ^ 3 = 0 := by
      convert hY using 1
      ring
    rw [hab] at hY'
    ring_nf at hY'
    linear_combination hY'
  exact hc0 (eq_zero_of_pow_eq_zero
    ((mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : k) ≠ 0)))

/-! ## Source-facing constant-`B` Q-higher cusp -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalTail_cusp_impossible_of_constantB_Qhigher68
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
    (hD0 :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g = 3 * n)
    (hQ :
      let n := weightedRadius68 A B C0 D E
      n < 2 * t) : False := by
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
  change g = 3 * n at hD0
  change n < 2 * t at hQ
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, ⟨i4, hi4⟩, ⟨i3, hi3⟩, hrow2, hrow1⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hidx := fiveToSix_terminalTail_cusp_indices68 n g t hwindow htle
  have ha : Ae.coeff (2 * n) ≠ 0 :=
    fiveToSix_terminalTail_cusp_A_top68 Ae Be ce d ee n g
      (7 * n - 2 * g + t) hcusp
  have hb : Be.coeff 0 ≠ 0 := by
    have hBidx : 3 * n - g = 0 := by omega
    have hb' := hcusp.1
    rwa [hBidx] at hb'
  have hc0 : ce.coeff n ≠ 0 := by
    have hCidx : 4 * n - g = n := by omega
    have hc' := hcusp.2.1
    rwa [hCidx] at hc'
  have hcuspEq :
      Ae.coeff (2 * n) * Be.coeff 0 ^ 2 + (3 : k) * ce.coeff n ^ 2 = 0 := by
    have hBidx : 3 * n - g = 0 := by omega
    have hCidx : 4 * n - g = n := by omega
    simpa [hBidx, hCidx] using hcusp.2.2.2.2
  exact fiveToSix_terminalTail_constantB_Qhigher_cusp_false68 alpha gamma
    epsilon eta i3 Ae Be ce d ee n g t data.hn hwindow htle hD0 hQ
    data.hA data.hB data.hc hd he ha hb hc0 hcuspEq hi3 hrow1

/-! ## I3 / I4 / lattice helpers on constant `B` -/

theorem fiveToSix_I3_coeff_ABd_top_constantB68
    (gamma epsilon : k) (A B c d e : k[X]) (u v : ℕ)
    (hB : B.natDegree ≤ 0)
    (hA : A.natDegree ≤ u)
    (hd : d.natDegree ≤ v)
    (hc : c.natDegree + e.natDegree < u + v)
    (hd2 : 2 * d.natDegree < u + v)
    (hpos : 0 < u + v) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (u + v) =
      (-8 / 9 : k) * B.coeff 0 * A.coeff u * d.coeff v := by
  have hB0 : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hABd : (A * B * d).coeff (u + v) =
      B.coeff 0 * A.coeff u * d.coeff v := by
    rw [hB0, show A * C (B.coeff 0) * d = C (B.coeff 0) * (A * d) by ring,
      coeff_C_mul, coeff_mul_at_bounds68 A d u v hA hd]
    simp [coeff_C]
    ring
  have hB2c : (B ^ 2 * c).natDegree < u + v := by
    have hB2 : (B ^ 2).natDegree ≤ 0 := by
      compute_degree
      omega
    have hmul := natDegree_mul_le (p := B ^ 2) (q := c)
    have : (B ^ 2).natDegree + c.natDegree < u + v := by omega
    exact lt_of_le_of_lt hmul this
  have hce : (c * e).natDegree < u + v := by
    have hmul := natDegree_mul_le (p := c) (q := e)
    exact lt_of_le_of_lt hmul hc
  have hd2' : (d ^ 2).natDegree < u + v := by
    have h := (natDegree_pow (p := d) (n := 2)).le
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree < u + v := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < u + v := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < u + v := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero, secondaryResidualInvariantThreePolynomial68,
    coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, coeff_eq_zero_of_natDegree_lt hce,
    coeff_eq_zero_of_natDegree_lt hd2',
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

theorem fiveToSix_I4_coeff_pos_constantB68
    (gamma epsilon : k) (A B c d e : k[X]) (m : ℕ)
    (hB : B.natDegree ≤ 0) (hm : 0 < m) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff m =
      (8 / 3 : k) *
          (B.coeff 0 * e.coeff m + (c * d).coeff m) +
        (4 * gamma : k) * d.coeff m := by
  have hid := fiveToSix_terminalTail_I4_F_identity68 gamma epsilon A B c d e
  have hB0 : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hBe : (B * e).coeff m = B.coeff 0 * e.coeff m := by
    rw [hB0, coeff_C_mul]
    simp [coeff_C]
  have hB3 : (B ^ 3).coeff m = 0 := by
    have : (B ^ 3).natDegree ≤ 0 := by
      compute_degree
      omega
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt this hm)
  have hBm : B.coeff m = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hB hm)
  dsimp only at hid
  rw [hid]
  simp only [coeff_add, coeff_smul, smul_eq_mul, coeff_sub]
  rw [hBe, hB3, hBm]
  ring

theorem fiveToSix_I3_forces_d_coeff_constantB68
    (gamma epsilon i3 : k) (A B c d e : k[X]) (u v : ℕ)
    (hB : B.natDegree ≤ 0)
    (hA : A.natDegree ≤ u) (hd : d.natDegree ≤ v)
    (hc : c.natDegree + e.natDegree < u + v)
    (hd2 : 2 * d.natDegree < u + v)
    (hpos : 0 < u + v)
    (ha : A.coeff u ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    d.coeff v = 0 := by
  have htop := fiveToSix_I3_coeff_ABd_top_constantB68 gamma epsilon A B c d e
    u v hB hA hd hc hd2 hpos
  have hz := congrArg (fun p : k[X] => p.coeff (u + v)) hi3
  rw [htop] at hz
  have hne : u + v ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hne] at hz
  have h89 : (-8 / 9 : k) ≠ 0 := by norm_num
  have hz' :
      (-8 / 9 : k) * (B.coeff 0 * (A.coeff u * d.coeff v)) = 0 := by
    convert hz using 1
    ring
  have h1 := (mul_eq_zero.mp hz').resolve_left h89
  have h2 := (mul_eq_zero.mp h1).resolve_left hb
  exact (mul_eq_zero.mp h2).resolve_left ha

theorem fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
    (q : k[X]) (base : ℕ) (hbase : 60 ∣ base) (hsixty : 60 ≤ base)
    (hdeg : (expand k 60 q).natDegree ≤ base)
    (htop : (expand k 60 q).coeff base = 0) :
    (expand k 60 q).natDegree ≤ base - 60 := by
  by_cases hzero : expand k 60 q = 0
  · rw [hzero, natDegree_zero]
    omega
  · have hlead : (expand k 60 q).coeff (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hzero
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) q
        (expand k 60 q).natDegree hlead
    have hne : (expand k 60 q).natDegree ≠ base := by
      intro heq
      exact hlead (heq ▸ htop)
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hdiv
    omega

theorem fiveToSix_expand_natDegree_le_sixty_floor68
    (q : k[X]) (bound : ℕ)
    (hdeg : (expand k 60 q).natDegree ≤ bound) :
    (expand k 60 q).natDegree ≤ 60 * (bound / 60) := by
  by_cases hzero : expand k 60 q = 0
  · rw [hzero, natDegree_zero]
    omega
  · have hlead : (expand k 60 q).coeff (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hzero
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) q
        (expand k 60 q).natDegree hlead
    obtain ⟨v, hv⟩ := hdiv
    have : v ≤ bound / 60 := by
      have : 60 * v ≤ bound := by
        rw [← hv]
        exact hdeg
      omega
    omega

theorem fiveToSix_Be_natDegree_le_zero_of_gap_lt_sixty68
    (B : k[X]) (n g : ℕ)
    (hB : (expand k 60 B).natDegree ≤ 3 * n - g)
    (hgap : 3 * n - g < 60) :
    (expand k 60 B).natDegree ≤ 0 := by
  have hlt : (expand k 60 B).natDegree < 60 := lt_of_le_of_lt hB hgap
  have hsrc : B.natDegree = 0 :=
    fiveToSix_source_B_constant_of_expanded_lt_sixty68 B hlt
  have : (expand k 60 B).natDegree = 60 * B.natDegree := by
    rw [natDegree_expand, mul_comm]
  omega

theorem fiveToSix_source_d_of_expanded_zero68
    (A B D : k[X])
    (h : secondaryDDefectPolynomial68 (expand k 60 A) (expand k 60 B)
      (expand k 60 D) = 0) :
    secondaryDDefectPolynomial68 A B D = 0 :=
  (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp
    (by rwa [secondaryDDefectPolynomial68_expand] at h)

/-! ## `n=90` open residual is the terminal-zero packet -/

theorem fiveToSix_n90_openResidual_terminalZero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hn : weightedRadius68 A B C0 D E = 90)
    (h : IntegratedPolynomialLowerSystem68OpenResidual alpha gamma epsilon
      zeta eta terminal A B C0 D E) :
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
    FiveToSixTerminalZeroPacket68 zeta d ee n g := by
  intro n Ae Be Ce ce De Ee ee g d
  dsimp only [IntegratedPolynomialLowerSystem68OpenResidual] at h
  rcases h with hZ | hearlier | hterm
  · exact hZ
  · obtain ⟨N, _, _, hn60, _, _⟩ := hearlier
    have : n = 60 * N := hn60
    omega
  · have : 120 < n := hterm.1
    omega

/-! ## `n=60` terminal-zero successor -/

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_n60_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hn60 : weightedRadius68 A B C0 D E = 60)
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g) : False := by
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
  change n = 60 at hn60
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  have hzeta : zeta = 0 := hpacket.2.2.1
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hg : g = 180 := by
    rcases hglobal with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, holdCases⟩
    rcases holdCases with h60 | h90 | h120 | hbig
    · exact h60.2
    · omega
    · omega
    · omega
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, _, _, _, _⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hA : 2 ≤ A.natDegree := by
    have hdeg := fiveToSix_source_A_natDegree_eq68 A B C0 D E data.ha data.hA
    have : 2 ≤ n / 30 := by omega
    rwa [hdeg]
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hdle : d.natDegree ≤ 0 := by
    rw [hdexpand]
    refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
      (secondaryDDefectPolynomial68 A B D) 60 (by norm_num) (by omega) ?_ ?_
    · have : g - 2 * n = 60 := by omega
      simpa [hdexpand, this] using hpacket.1
    · have : g - 2 * n = 60 := by omega
      simpa [hdexpand, this] using hpacket.2.2.2.1
  have hele : ee.natDegree ≤ 60 := by
    rw [heexpand]
    refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
      (cubicEDefectPolynomial68 A C0 E) 120 (by norm_num) (by omega) ?_ ?_
    · have : g - n = 120 := by omega
      simpa [heexpand, this] using hpacket.2.1
    · have : g - n = 120 := by omega
      simpa [heexpand, this] using hpacket.2.2.2.2
  have htle : 60 ≤ g - 2 * n := by
    rw [hg, hn60]
  have hdrop : d.natDegree ≤ g - 2 * n - 60 ∧
      ee.natDegree ≤ g - n - 60 := by
    constructor
    · rw [hg, hn60]
      exact hdle
    · rw [hg, hn60]
      exact hele
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 60
      hterminal hsys (by omega) hwindow hzeta htle hdrop
  rcases hedge with hzero | hcusp
  · change d.coeff (g - 2 * n - 60) = 0 ∧
        ee.coeff (g - n - 60) = 0 at hzero
    have hd00 : d.coeff 0 = 0 := by
      have hidx : g - 2 * n - 60 = 0 := by rw [hg, hn60]
      have h := hzero.1
      rwa [hidx] at h
    have hd0 : d = 0 :=
      eq_zero_of_natDegree_le_zero_coeff_zero68 d hdle hd00
    have hd_src0 : secondaryDDefectPolynomial68 A B D = 0 :=
      fiveToSix_source_d_of_expanded_zero68 A B D
        (by simpa only [d, Ae, Be, De] using hd0)
    exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta hdelta
      hzeta hd_src0 hA
  · have hdQ : d.natDegree ≤ g - 2 * n - 60 := by
      rw [hg, hn60]
      exact hdle
    have heQ : ee.natDegree ≤ g - n - 60 := by
      rw [hg, hn60]
      exact hele
    exact fiveToSix_terminalTail_cusp_impossible_of_constantB_Qhigher68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 60
      hterminal hsys hzeta htle hdQ heQ hcusp
      (by
        change g = 3 * n
        rw [hg, hn60])
      (by omega : n < 2 * 60)

/-! ## Source `U` with `B = 0`: tracked cubic split `U = (4/9) A D + α D` -/

/-- `LowScale68SecondaryExtraction.cubicHomogeneousUPolynomial68` is
`(4/9) A D + (4/9) B c`; `cubicLoadUPolynomial68` at
`l=β=δ=ζ=0` is `α D + (2/3) γ B`.  Vanishing `B` leaves
`U = ((4/9) A + C α) D`. -/
theorem fiveToSix_U_of_B_zero68
    (alpha gamma : k) (A C0 D E : k[X]) :
    integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0 C0 D E =
      ((4 / 9 : k) • A + C alpha) * D := by
  simp only [integratedUPolynomial68, zero_smul, smul_zero, mul_zero,
    zero_mul, add_zero, sub_zero, C_0, smul_eq_C_mul]
  ring

theorem fiveToSix_eq_C_of_expand_natDegree_le_zero68 (q : k[X])
    (h : (expand k 60 q).natDegree ≤ 0) :
    q = C ((expand k 60 q).coeff 0) := by
  have hmul : 60 * q.natDegree = (expand k 60 q).natDegree := by
    rw [natDegree_expand, mul_comm]
  have hq0 : q.natDegree ≤ 0 := by omega
  have hC : q = C (q.coeff 0) := eq_C_of_natDegree_le_zero hq0
  have hcoeff : (expand k 60 q).coeff 0 = q.coeff 0 := by
    rw [coeff_expand (by norm_num : 0 < 60)]
    simp
  rwa [← hcoeff] at hC

theorem fiveToSix_I4_H_constantB_constantD68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (m : ℕ)
    (hB : B.natDegree ≤ 0) (hd : d.natDegree ≤ 0) (hm : 0 < m)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    B.coeff 0 * e.coeff m + d.coeff 0 * c.coeff m = 0 := by
  have htop := fiveToSix_I4_coeff_pos_constantB68 gamma epsilon A B c d e
    m hB hm
  have hz := congrArg (fun p : k[X] => p.coeff m) hi4
  rw [htop] at hz
  have hne : m ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hne] at hz
  have hdC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd
  have hcd : (c * d).coeff m = d.coeff 0 * c.coeff m := by
    rw [hdC, mul_comm, coeff_C_mul, coeff_C_zero]
  have hdm : d.coeff m = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hm)
  have hred :
      (8 / 3 : k) * (B.coeff 0 * e.coeff m + d.coeff 0 * c.coeff m) = 0 := by
    convert hz using 1
    rw [hcd, hdm]
    ring
  exact (mul_eq_zero.mp hred).resolve_left (by norm_num : (8 / 3 : k) ≠ 0)

theorem fiveToSix_I4_forces_c_constant_of_B_zero_constant_d68
    (gamma epsilon i4 : k) (A c d e : k[X])
    (hd : d.natDegree ≤ 0) (hd0 : d.coeff 0 ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A 0 c ((1 / 3 : k) • (A * (0 : k[X])) + d) e = C i4) :
    c.natDegree ≤ 0 := by
  by_cases hc0 : c = 0
  · simp [hc0]
  · by_contra hpos
    have hm : 0 < c.natDegree := by omega
    have hH := fiveToSix_I4_H_constantB_constantD68 gamma epsilon i4 A 0 c d e
      c.natDegree (by simp) hd hm hi4
    have hB0 : (0 : k[X]).coeff 0 = 0 := by simp
    rw [hB0, zero_mul, zero_add] at hH
    have hclead : c.coeff c.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hc0
    exact hclead ((mul_eq_zero.mp hH).resolve_left hd0)

set_option maxHeartbeats 8000000 in
theorem fiveToSix_B_zero_constant_cd_residual_rowZero68
    (A e : k[X]) (c0 d0 : k) :
    secondaryResidualRowZeroPolynomial68 A 0 (C c0) (C d0) e =
      C d0 * derivative A *
        (-(4 / 27 : k) • (A * C c0) - (4 / 9 : k) • e) := by
  simp only [secondaryResidualRowZeroPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, zero_add, sub_zero, derivative_C]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_natCast, map_one]
  ring

set_option maxHeartbeats 12000000 in
theorem fiveToSix_B_zero_constant_cd_load_rowZero68
    (alpha gamma epsilon eta : k) (A e : k[X]) (c0 d0 : k) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A 0 (C c0) ((1 / 3 : k) • (A * (0 : k[X])) + C d0) e =
      C d0 * derivative A *
        (-(2 / 9 * gamma : k) • A - C ((1 / 3 : k) * epsilon)) := by
  simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, zero_mul, mul_zero,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast,
    map_one]
  ring

theorem fiveToSix_B_zero_constant_cd_rowZero_polynomial68
    (alpha gamma epsilon eta : k) (A e : k[X]) (c0 d0 : k) :
    secondaryResidualRowZeroPolynomial68 A 0 (C c0) (C d0) e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A 0 (C c0) ((1 / 3 : k) • (A * (0 : k[X])) + C d0) e =
      C d0 * derivative A *
        (-(4 / 27 : k) • (A * C c0) - (4 / 9 : k) • e -
          (2 / 9 * gamma : k) • A - C ((1 / 3 : k) * epsilon)) := by
  rw [fiveToSix_B_zero_constant_cd_residual_rowZero68,
    fiveToSix_B_zero_constant_cd_load_rowZero68]
  simp only [smul_eq_C_mul, ← C_neg]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

theorem fiveToSix_B_zero_constant_cd_rowZero_impossible68
    (alpha gamma epsilon eta terminal : k) (A e : k[X]) (c0 d0 : k)
    (hterminal : terminal ≠ 0) (hA : 2 ≤ A.natDegree) (hd0 : d0 ≠ 0)
    (hrow : secondaryResidualRowZeroPolynomial68 A 0 (C c0) (C d0) e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A 0 (C c0) ((1 / 3 : k) • (A * (0 : k[X])) + C d0) e =
        C terminal) : False := by
  have hform := fiveToSix_B_zero_constant_cd_rowZero_polynomial68
    alpha gamma epsilon eta A e c0 d0
  rw [hform] at hrow
  set Q : k[X] :=
    -(4 / 27 : k) • (A * C c0) - (4 / 9 : k) • e -
      (2 / 9 * gamma : k) • A - C ((1 / 3 : k) * epsilon)
  change C d0 * derivative A * Q = C terminal at hrow
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
    have hcast : ((A.natDegree - 1 : ℕ) : k) + 1 = (A.natDegree : k) := by
      exact_mod_cast hidx
    rw [hcast]
    ring
  have hnA : (A.natDegree : k) ≠ 0 := by
    exact_mod_cast (by omega : A.natDegree ≠ 0)
  have hA'ne : derivative A ≠ 0 := by
    intro h0
    have : (A.natDegree : k) * A.coeff A.natDegree = 0 := by
      rw [← hder_coeff, h0, coeff_zero]
    exact htop ((mul_eq_zero.mp this).resolve_left hnA)
  by_cases hQ : Q = 0
  · have : (0 : k[X]) = C terminal := by
      simpa [hQ, mul_zero] using hrow
    exact hterminal (C_eq_zero.mp this.symm)
  · have hdeg :
        (C d0 * derivative A * Q).natDegree =
          (derivative A).natDegree + Q.natDegree := by
      rw [mul_assoc, natDegree_C_mul hd0, natDegree_mul hA'ne hQ]
    have hder_ge : 1 ≤ (derivative A).natDegree := by
      have hpos : (derivative A).coeff (A.natDegree - 1) ≠ 0 := by
        rw [hder_coeff]
        exact mul_ne_zero hnA htop
      have : A.natDegree - 1 ≤ (derivative A).natDegree :=
        le_natDegree_of_ne_zero hpos
      omega
    have hC : (C terminal).natDegree = 0 := natDegree_C terminal
    have : (C terminal).natDegree =
        (derivative A).natDegree + Q.natDegree := by
      rw [← hrow, hdeg]
    omega

set_option maxHeartbeats 25000000 in
theorem fiveToSix_B_zero_constant_d_source_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A 0 C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A 0 D =
      C ((secondaryDDefectPolynomial68 A 0 D).coeff 0))
    (hd0 : (secondaryDDefectPolynomial68 A 0 D).coeff 0 ≠ 0)
    (hA : 2 ≤ A.natDegree) : False := by
  have hDrec : D = (1 / 3 : k) • (A * (0 : k[X])) +
      secondaryDDefectPolynomial68 A 0 D :=
    secondaryDDefectPolynomial68_reconstruct A 0 D
  have hCrec : C0 = (1 / 3 : k) • A ^ 2 + cubicCDefectPolynomial68 A C0 :=
    cubicCDefectPolynomial68_reconstruct A C0
  let c := cubicCDefectPolynomial68 A C0
  let e := cubicEDefectPolynomial68 A C0 E
  let d := secondaryDDefectPolynomial68 A 0 D
  have hErec : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e := by
    simpa only [c, e] using
      cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
  have hdC : d = C (d.coeff 0) := by
    simpa only [d] using hd
  obtain ⟨i4, hi4raw⟩ := hsys.firstFour
  have hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A 0 c ((1 / 3 : k) • (A * (0 : k[X])) + d) e = C i4 := by
    have h := hi4raw
    rw [hl, hbeta, hdelta, hzeta, hCrec] at h
    rw [hErec, firstIntegralFourPolynomial68_cubicCoordinates, hDrec] at h
    simpa [c, d, e] using h
  have hc : c.natDegree ≤ 0 :=
    fiveToSix_I4_forces_c_constant_of_B_zero_constant_d68 gamma epsilon i4
      A c d e (by
        have : d.natDegree ≤ 0 := by
          rw [hdC, natDegree_C]
        exact this) (by simpa only [d] using hd0) hi4
  have hcC : c = C (c.coeff 0) := eq_C_of_natDegree_le_zero hc
  have hrow0 := hsys.rowZero
  rw [hCrec, hDrec, hErec, cubicRowZeroPolynomial68_residualSplit,
    hl, hbeta, hdelta, hzeta] at hrow0
  rw [show cubicCDefectPolynomial68 A C0 = c from rfl] at hrow0
  rw [show secondaryDDefectPolynomial68 A 0 D = d from rfl, hdC, hcC]
    at hrow0
  exact fiveToSix_B_zero_constant_cd_rowZero_impossible68 alpha gamma
    epsilon eta terminal A e (c.coeff 0) (d.coeff 0) hterminal hA
    (by simpa only [d] using hd0) hrow0

/-! ## Unaligned `n=90` -/

set_option maxHeartbeats 40000000 in
theorem fiveToSix_terminalZero_n90_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hn90 : weightedRadius68 A B C0 D E = 90) : False := by
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
  change n = 90 at hn90
  have hopen :=
    integratedPolynomialLowerSystem68_openResidual l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys
  have hpacket := fiveToSix_n90_openResidual_terminalZero68 alpha gamma
    epsilon zeta eta terminal A B C0 D E hn90 hopen
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  have hzeta : zeta = 0 := hpacket.2.2.1
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, ⟨i4, hi4⟩, ⟨i3, hi3⟩, _, _⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  rcases hglobal with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, holdCases⟩
  have hg : g = 240 ∨ g = 270 := by
    rcases holdCases with h60 | h90 | h120 | hbig
    · omega
    · exact h90.2
    · omega
    · omega
  have hgap : 3 * n - g < 60 := by omega
  have hB0 : Be.natDegree ≤ 0 :=
    fiveToSix_Be_natDegree_le_zero_of_gap_lt_sixty68 B n g data.hB hgap
  have hA : 2 ≤ A.natDegree := by
    have hdeg := fiveToSix_source_A_natDegree_eq68 A B C0 D E data.ha data.hA
    have : 2 ≤ n / 30 := by omega
    rwa [hdeg]
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have ha : Ae.coeff (2 * n) ≠ 0 := data.ha
  have hcusp_off30 (hcusp : FiveToSixCuspEdge68 Ae Be ce d ee n g
      (7 * n - 2 * g + 30)) : False := by
    have : 60 ∣ n :=
      (fiveToSix_expanded_cusp_alignment68 A B
          (cubicCDefectPolynomial68 A C0)
          (secondaryDDefectPolynomial68 A B D)
          (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
          (by omega) (by omega)
          (by simpa [Ae, Be, hcexpand, hdexpand, heexpand] using hcusp)).1
    omega
  have hd_src_of_exp0 (hde0 : d = 0) : False :=
    fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta hdelta
      hzeta
      (fiveToSix_source_d_of_expanded_zero68 A B D
        (by simpa only [d, Ae, Be, De] using hde0)) hA
  have hBe0_src (hBe0 : Be = 0)
      (hdle : d.natDegree ≤ 0) (hdC0 : d.coeff 0 ≠ 0) : False := by
    have hBsrc : B = 0 :=
      (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp
        (by simpa only [Be] using hBe0)
    have hsrcdeg : (secondaryDDefectPolynomial68 A B D).natDegree ≤ 0 := by
      have : 60 * (secondaryDDefectPolynomial68 A B D).natDegree ≤ 0 := by
        have h := hdle
        rw [hdexpand, natDegree_expand, mul_comm] at h
        exact h
      omega
    have hd_src : secondaryDDefectPolynomial68 A B D =
        C ((secondaryDDefectPolynomial68 A B D).coeff 0) :=
      eq_C_of_natDegree_le_zero hsrcdeg
    have hd0src : (secondaryDDefectPolynomial68 A B D).coeff 0 ≠ 0 := by
      have h0 : (expand k 60 (secondaryDDefectPolynomial68 A B D)).coeff 0 =
          (secondaryDDefectPolynomial68 A B D).coeff 0 := by
        rw [coeff_expand (by norm_num : 0 < 60)]
        simp
      have hd0eq : d.coeff 0 =
          (secondaryDDefectPolynomial68 A B D).coeff 0 := by
        rw [hdexpand]
        exact h0
      rwa [← hd0eq]
    have hsys0 : IntegratedPolynomialLowerSystem68
        l alpha beta gamma delta epsilon zeta eta terminal A 0 C0 D E := by
      rw [← hBsrc]
      exact hsys
    exact fiveToSix_B_zero_constant_d_source_impossible68 l alpha beta
      gamma delta epsilon zeta eta terminal A C0 D E hterminal hsys0 hl
      hbeta hdelta hzeta (by rw [← hBsrc]; exact hd_src)
      (by rw [← hBsrc]; exact hd0src) hA
  have hBne_I3 (hb : Be.coeff 0 ≠ 0) (hdle : d.natDegree ≤ 0)
      (hcle : ce.natDegree + ee.natDegree < 2 * n) : d.coeff 0 = 0 :=
    fiveToSix_I3_forces_d_coeff_constantB68 gamma epsilon i3 Ae Be ce d ee
      (2 * n) 0 hB0 data.hA hdle hcle (by omega) (by omega) ha hb hi3
  rcases hg with hg240 | hg270
  · have h_g2n : g - 2 * n = 60 := by omega
    have h_gn : g - n = 150 := by omega
    have hdle : d.natDegree ≤ 0 := by
      rw [hdexpand]
      refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
        (secondaryDDefectPolynomial68 A B D) 60 (by norm_num) (by omega)
        ?_ ?_
      · simpa [hdexpand, h_g2n] using hpacket.1
      · simpa [hdexpand, h_g2n] using hpacket.2.2.2.1
    have hele : ee.natDegree ≤ 120 := by
      rw [heexpand]
      have hle : (expand k 60 (cubicEDefectPolynomial68 A C0 E)).natDegree
          ≤ 150 := by
        simpa [heexpand, h_gn] using hpacket.2.1
      have := fiveToSix_expand_natDegree_le_sixty_floor68
        (cubicEDefectPolynomial68 A C0 E) 150 hle
      omega
    have htle30 : 30 ≤ g - 2 * n := by omega
    have hd30 : d.natDegree ≤ g - 2 * n - 30 := by omega
    have he30 : ee.natDegree ≤ g - n - 30 := by omega
    have hedge :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
        hterminal hsys (by omega) hwindow hzeta htle30
        (by exact ⟨hd30, he30⟩)
    rcases hedge with hvan | hcusp
    · change d.coeff (g - 2 * n - 30) = 0 ∧
          ee.coeff (g - n - 30) = 0 at hvan
      have he120 : ee.coeff 120 = 0 := by
        have hidx : g - n - 30 = 120 := by omega
        have h := hvan.2
        rwa [hidx] at h
      have hele60 : ee.natDegree ≤ 60 := by
        rw [heexpand]
        refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
          (cubicEDefectPolynomial68 A C0 E) 120 (by norm_num) (by omega)
          ?_ ?_
        · simpa [heexpand] using hele
        · simpa [heexpand] using he120
      by_cases hdC0 : d.coeff 0 = 0
      · exact hd_src_of_exp0
          (eq_zero_of_natDegree_le_zero_coeff_zero68 d hdle hdC0)
      · by_cases hBe0 : Be = 0
        · exact hBe0_src hBe0 hdle hdC0
        · have hb : Be.coeff 0 ≠ 0 := by
            have hC : Be = C (Be.coeff 0) := eq_C_of_natDegree_le_zero hB0
            intro hb0
            exact hBe0 (by rw [hC, hb0, C_0])
          have hc120 : ce.coeff 120 = 0 := by
            have hH := fiveToSix_I4_H_constantB_constantD68 gamma epsilon i4
              Ae Be ce d ee 120 hB0 hdle (by omega) hi4
            have : Be.coeff 0 * ee.coeff 120 + d.coeff 0 * ce.coeff 120 =
                0 := hH
            rw [he120, mul_zero, zero_add] at this
            exact (mul_eq_zero.mp this).resolve_left hdC0
          have hcle60 : ce.natDegree ≤ 60 := by
            rw [hcexpand]
            refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
              (cubicCDefectPolynomial68 A C0) 120 (by norm_num) (by omega)
              ?_ ?_
            · have : 4 * n - g = 120 := by omega
              simpa [hcexpand, this] using data.hc
            · simpa [hcexpand] using hc120
          have hd00 : d.coeff 0 = 0 :=
            hBne_I3 hb hdle (by omega)
          exact hdC0 hd00
    · exact hcusp_off30 hcusp
  · have h_g2n : g - 2 * n = 90 := by omega
    have h_gn : g - n = 180 := by omega
    have hdle60 : d.natDegree ≤ 60 := by
      rw [hdexpand]
      have hle : (expand k 60 (secondaryDDefectPolynomial68 A B D)).natDegree
          ≤ 90 := by
        simpa [hdexpand, h_g2n] using hpacket.1
      have := fiveToSix_expand_natDegree_le_sixty_floor68
        (secondaryDDefectPolynomial68 A B D) 90 hle
      omega
    have hele : ee.natDegree ≤ 120 := by
      rw [heexpand]
      refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
        (cubicEDefectPolynomial68 A C0 E) 180 (by norm_num) (by omega)
        ?_ ?_
      · simpa [heexpand, h_gn] using hpacket.2.1
      · simpa [heexpand, h_gn] using hpacket.2.2.2.2
    have htle30 : 30 ≤ g - 2 * n := by omega
    have hd30 : d.natDegree ≤ g - 2 * n - 30 := by omega
    have he30 : ee.natDegree ≤ g - n - 30 := by omega
    have hedge :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
        hterminal hsys (by omega) hwindow hzeta htle30
        (by exact ⟨hd30, he30⟩)
    rcases hedge with hvan | hcusp
    · change d.coeff (g - 2 * n - 30) = 0 ∧
          ee.coeff (g - n - 30) = 0 at hvan
      have hd60z : d.coeff 60 = 0 := by
        have hidx : g - 2 * n - 30 = 60 := by omega
        have h := hvan.1
        rwa [hidx] at h
      have hdle : d.natDegree ≤ 0 := by
        rw [hdexpand]
        refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
          (secondaryDDefectPolynomial68 A B D) 60 (by norm_num) (by omega)
          ?_ ?_
        · simpa [hdexpand] using hdle60
        · simpa [hdexpand] using hd60z
      have hcle60 : ce.natDegree ≤ 60 := by
        rw [hcexpand]
        have hle : (expand k 60 (cubicCDefectPolynomial68 A C0)).natDegree
            ≤ 90 := by
          have : 4 * n - g = 90 := by omega
          simpa [hcexpand, this] using data.hc
        have := fiveToSix_expand_natDegree_le_sixty_floor68
          (cubicCDefectPolynomial68 A C0) 90 hle
        omega
      by_cases hdC0 : d.coeff 0 = 0
      · exact hd_src_of_exp0
          (eq_zero_of_natDegree_le_zero_coeff_zero68 d hdle hdC0)
      · by_cases hBe0 : Be = 0
        · exact hBe0_src hBe0 hdle hdC0
        · have hb : Be.coeff 0 ≠ 0 := by
            have hC : Be = C (Be.coeff 0) := eq_C_of_natDegree_le_zero hB0
            intro hb0
            exact hBe0 (by rw [hC, hb0, C_0])
          have he120 : ee.coeff 120 = 0 := by
            have hH := fiveToSix_I4_H_constantB_constantD68 gamma epsilon i4
              Ae Be ce d ee 120 hB0 hdle (by omega) hi4
            have hc120 : ce.coeff 120 = 0 :=
              coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcle60 (by omega))
            rw [hc120, mul_zero, add_zero] at hH
            exact (mul_eq_zero.mp hH).resolve_left hb
          have hele60 : ee.natDegree ≤ 60 := by
            rw [heexpand]
            refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
              (cubicEDefectPolynomial68 A C0 E) 120 (by norm_num) (by omega)
              ?_ ?_
            · simpa [heexpand] using hele
            · simpa [heexpand] using he120
          have hd00 : d.coeff 0 = 0 :=
            hBne_I3 hb hdle (by omega)
          exact hdC0 hd00
    · exact hcusp_off30 hcusp

/-! ## I3 on constant `B`, constant `d` -/

theorem fiveToSix_I3_coeff_constantB_constantD_mid68
    (gamma epsilon : k) (A B c d e : k[X]) (u : ℕ)
    (hB : B.natDegree ≤ 0) (hd : d.natDegree ≤ 0)
    (hA : A.natDegree ≤ u) (hc : c.natDegree < u)
    (he : e.natDegree < u) (hpos : 0 < u) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff u =
      (-8 / 9 : k) * B.coeff 0 * A.coeff u * d.coeff 0 +
        (8 / 3 : k) * (c * e).coeff u := by
  have hB0 : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hdC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd
  have hABd : (A * B * d).coeff u =
      B.coeff 0 * A.coeff u * d.coeff 0 := by
    rw [hB0, hdC,
      show A * C (B.coeff 0) * C (d.coeff 0) =
        C (B.coeff 0 * d.coeff 0) * A by
        simp [C_mul, mul_assoc, mul_left_comm, mul_comm],
      coeff_C_mul]
    simp [coeff_C]
    ring
  have hB2c : (B ^ 2 * c).natDegree < u := by
    have hB2 : (B ^ 2).natDegree ≤ 0 := by
      compute_degree
      omega
    have hmul := natDegree_mul_le (p := B ^ 2) (q := c)
    exact lt_of_le_of_lt hmul (by omega)
  have hd2 : (d ^ 2).natDegree < u := by
    have h := (natDegree_pow (p := d) (n := 2)).le
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree < u := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < u := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < u := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero, secondaryResidualInvariantThreePolynomial68,
    coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-! ## `n=120`, `g=330`: t=30 vanish / off-lattice cusp -/

set_option maxHeartbeats 40000000 in
theorem fiveToSix_terminalZero_n120_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hn120 : weightedRadius68 A B C0 D E = 120)
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
      FiveToSixTerminalZeroPacket68 zeta d ee n g) : False := by
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
  change n = 120 at hn120
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  have hzeta : zeta = 0 := hpacket.2.2.1
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, ⟨i4, hi4⟩, ⟨i3, hi3⟩, _, hrow1⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hg : g = 330 := by
    rcases hglobal with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, holdCases⟩
    rcases holdCases with h60 | h90 | h120 | hbig
    · omega
    · omega
    · exact h120.2
    · omega
  have h_g2n : g - 2 * n = 90 := by omega
  have h_gn : g - n = 210 := by omega
  have h_4ng : 4 * n - g = 150 := by omega
  have h_3ng : 3 * n - g = 30 := by omega
  have hgap : 3 * n - g < 60 := by omega
  have hB0 : Be.natDegree ≤ 0 :=
    fiveToSix_Be_natDegree_le_zero_of_gap_lt_sixty68 B n g data.hB hgap
  have hA : 2 ≤ A.natDegree := by
    have hdeg := fiveToSix_source_A_natDegree_eq68 A B C0 D E data.ha data.hA
    have : 2 ≤ n / 30 := by omega
    rwa [hdeg]
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have ha : Ae.coeff (2 * n) ≠ 0 := data.ha
  have hdle60 : d.natDegree ≤ 60 := by
    rw [hdexpand]
    have hle : (expand k 60 (secondaryDDefectPolynomial68 A B D)).natDegree
        ≤ 90 := by
      simpa [hdexpand, h_g2n] using hpacket.1
    have := fiveToSix_expand_natDegree_le_sixty_floor68
      (secondaryDDefectPolynomial68 A B D) 90 hle
    omega
  have hele180 : ee.natDegree ≤ 180 := by
    rw [heexpand]
    have hle : (expand k 60 (cubicEDefectPolynomial68 A C0 E)).natDegree
        ≤ 210 := by
      simpa [heexpand, h_gn] using hpacket.2.1
    have := fiveToSix_expand_natDegree_le_sixty_floor68
      (cubicEDefectPolynomial68 A C0 E) 210 hle
    omega
  have htle30 : 30 ≤ g - 2 * n := by omega
  have hd30 : d.natDegree ≤ g - 2 * n - 30 := by omega
  have he30 : ee.natDegree ≤ g - n - 30 := by omega
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
      hterminal hsys (by omega) hwindow hzeta htle30
      (by exact ⟨hd30, he30⟩)
  rcases hedge with hvan | hcusp
  · change d.coeff (g - 2 * n - 30) = 0 ∧
        ee.coeff (g - n - 30) = 0 at hvan
    have hd60z : d.coeff 60 = 0 := by
      have hidx : g - 2 * n - 30 = 60 := by omega
      have h := hvan.1
      rwa [hidx] at h
    have he180z : ee.coeff 180 = 0 := by
      have hidx : g - n - 30 = 180 := by omega
      have h := hvan.2
      rwa [hidx] at h
    have hdle : d.natDegree ≤ 0 := by
      rw [hdexpand]
      refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
        (secondaryDDefectPolynomial68 A B D) 60 (by norm_num) (by omega)
        ?_ ?_
      · simpa [hdexpand] using hdle60
      · simpa [hdexpand] using hd60z
    have hele120 : ee.natDegree ≤ 120 := by
      rw [heexpand]
      refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
        (cubicEDefectPolynomial68 A C0 E) 180 (by norm_num) (by omega)
        ?_ ?_
      · simpa [heexpand] using hele180
      · simpa [heexpand] using he180z
    have hcle120 : ce.natDegree ≤ 120 := by
      rw [hcexpand]
      have hle : (expand k 60 (cubicCDefectPolynomial68 A C0)).natDegree
          ≤ 150 := by
        simpa [hcexpand, h_4ng] using data.hc
      have := fiveToSix_expand_natDegree_le_sixty_floor68
        (cubicCDefectPolynomial68 A C0) 150 hle
      omega
    by_cases hdC0 : d.coeff 0 = 0
    · exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
        epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta
        hdelta hzeta
        (fiveToSix_source_d_of_expanded_zero68 A B D
          (by simpa only [d, Ae, Be, De] using
            eq_zero_of_natDegree_le_zero_coeff_zero68 d hdle hdC0)) hA
    · by_cases hBe0 : Be = 0
      · have hBsrc : B = 0 :=
          (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp
            (by simpa only [Be] using hBe0)
        have hsrcdeg :
            (secondaryDDefectPolynomial68 A B D).natDegree ≤ 0 := by
          have : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
              ≤ 0 := by
            have h := hdle
            rw [hdexpand, natDegree_expand, mul_comm] at h
            exact h
          omega
        have hd_src : secondaryDDefectPolynomial68 A B D =
            C ((secondaryDDefectPolynomial68 A B D).coeff 0) :=
          eq_C_of_natDegree_le_zero hsrcdeg
        have hd0src : (secondaryDDefectPolynomial68 A B D).coeff 0 ≠ 0 := by
          have h0 :
              (expand k 60 (secondaryDDefectPolynomial68 A B D)).coeff 0 =
                (secondaryDDefectPolynomial68 A B D).coeff 0 := by
            rw [coeff_expand (by norm_num : 0 < 60)]
            simp
          have hd0eq : d.coeff 0 =
              (secondaryDDefectPolynomial68 A B D).coeff 0 := by
            rw [hdexpand]
            exact h0
          rwa [← hd0eq]
        have hsys0 : IntegratedPolynomialLowerSystem68
            l alpha beta gamma delta epsilon zeta eta terminal A 0 C0 D E :=
          by
          rw [← hBsrc]
          exact hsys
        exact fiveToSix_B_zero_constant_d_source_impossible68 l alpha beta
          gamma delta epsilon zeta eta terminal A C0 D E hterminal hsys0
          hl hbeta hdelta hzeta (by rw [← hBsrc]; exact hd_src)
          (by rw [← hBsrc]; exact hd0src) hA
      · have hb : Be.coeff 0 ≠ 0 := by
          have hC : Be = C (Be.coeff 0) := eq_C_of_natDegree_le_zero hB0
          intro hb0
          exact hBe0 (by rw [hC, hb0, C_0])
        have hI3top :=
          fiveToSix_I3_coeff_constantB_constantD_mid68 gamma epsilon
            Ae Be ce d ee (2 * n) hB0 hdle data.hA
            (by omega) (by omega) (by omega)
        have hz := congrArg (fun p : k[X] => p.coeff (2 * n)) hi3
        rw [hI3top] at hz
        have hne : 2 * n ≠ 0 := by omega
        simp only [coeff_C, ite_eq_right hne] at hz
        have hce : (ce * ee).coeff (2 * n) =
            ce.coeff n * ee.coeff n := by
          have hmul := coeff_mul_at_bounds68 ce ee n n
            (by omega) (by omega)
          have : n + n = 2 * n := by omega
          rwa [this] at hmul
        have hH := fiveToSix_I4_H_constantB_constantD68 gamma epsilon i4
          Ae Be ce d ee n hB0 hdle (by omega) hi4
        have hred :
            (-8 / 9 : k) * Be.coeff 0 * Ae.coeff (2 * n) * d.coeff 0 +
              (8 / 3 : k) * (ce.coeff n * ee.coeff n) = 0 := by
          rw [← hce]
          exact hz
        have hcomb :
            (-8 / 9 : k) * d.coeff 0 *
                (Ae.coeff (2 * n) * Be.coeff 0 ^ 2 +
                  (3 : k) * ce.coeff n ^ 2) = 0 := by
          linear_combination Be.coeff 0 * hred -
            (8 / 3 : k) * ce.coeff n * hH
        have hcuspEq :
            Ae.coeff (2 * n) * Be.coeff 0 ^ 2 +
              (3 : k) * ce.coeff n ^ 2 = 0 := by
          have h89 : (-8 / 9 : k) ≠ 0 := by norm_num
          have hprod : (-8 / 9 : k) * d.coeff 0 ≠ 0 :=
            mul_ne_zero h89 hdC0
          exact (mul_eq_zero.mp hcomb).resolve_left hprod
        have hc0 : ce.coeff n ≠ 0 := by
          intro hc
          have hab : Ae.coeff (2 * n) * Be.coeff 0 ^ 2 = 0 := by
            simpa [hc] using hcuspEq
          have ha0 : Ae.coeff (2 * n) = 0 ∨ Be.coeff 0 ^ 2 = 0 :=
            mul_eq_zero.mp hab
          rcases ha0 with ha0 | hb2
          · exact ha ha0
          · exact hb (eq_zero_of_pow_eq_zero hb2)
        exact fiveToSix_terminalTail_constantB_Qhigher_cusp_false68
          alpha gamma epsilon eta i3 Ae Be ce d ee n (3 * n) (n - 30)
          data.hn (by omega) (by omega) rfl (by omega) data.hA
          (by
            have : 3 * n - 3 * n = 0 := by omega
            omega) (by omega) (by omega) (by omega) ha hb hc0 hcuspEq
          hi3 hrow1
  · have hcusp' :
        FiveToSixCuspEdge68 (expand k 60 A) (expand k 60 B)
          (expand k 60 (cubicCDefectPolynomial68 A C0))
          (expand k 60 (secondaryDDefectPolynomial68 A B D))
          (expand k 60 (cubicEDefectPolynomial68 A C0 E)) n g
          (7 * n - 2 * g + 30) := by
      simpa [Ae, Be, ← hcexpand, ← hdexpand, ← heexpand] using hcusp
    have : 60 ∣ g :=
      (fiveToSix_expanded_cusp_alignment68 A B
          (cubicCDefectPolynomial68 A C0)
          (secondaryDDefectPolynomial68 A B D)
          (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
          (by omega) (by omega) hcusp').2.1
    omega

/-! ## `120 < n`: first lattice drop.  Unaligned cusps are off-lattice.
Aligned `t = 60` is closable (`14n+120 < 15n`).  The meeting cell
`t = n/2` with `120 ∣ n` and the leftover vanish remainder are the
named residual. -/

/-- Honest leftover after closing `n ≤ 120`, the unaligned `t = 30`
cusp, and the aligned `t = 60` closable cusp.  CAS
`derive_68_terminal_zero_meeting.py` records the meeting I3-at-`n`
convolution and the row-two coefficient at `2n-1`; those rows are not
consumed here. -/
def FiveToSixTerminalZeroLargeRemainder68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  120 < n ∧ FiveToSixTerminalZeroPacket68 zeta d e n g ∧
    ((60 ∣ n ∧ 60 ∣ g ∧
        ∃ j, 1 < j ∧ 60 * j ≤ g - 2 * n ∧
          FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g + 60 * j)) ∨
      (d.natDegree ≤ 0 ∧ d ≠ 0))

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_unaligned_t30_cusp_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hnbig :
      let n := weightedRadius68 A B C0 D E
      120 < n ∧ ¬ 60 ∣ n)
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
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 30)) :
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
  change 120 < n ∧ ¬ 60 ∣ n at hnbig
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 30)
    at hcusp
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hcusp' :
      FiveToSixCuspEdge68 (expand k 60 A) (expand k 60 B)
        (expand k 60 (cubicCDefectPolynomial68 A C0))
        (expand k 60 (secondaryDDefectPolynomial68 A B D))
        (expand k 60 (cubicEDefectPolynomial68 A C0 E)) n g
        (7 * n - 2 * g + 30) := by
    simpa [Ae, Be, ← hcexpand, ← hdexpand, ← heexpand] using hcusp
  have : 60 ∣ n :=
    (fiveToSix_expanded_cusp_alignment68 A B
        (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
        (by omega) (by omega) hcusp').1
  exact hnbig.2 this

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_aligned_t60_cusp_closable68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hnbig :
      let n := weightedRadius68 A B C0 D E
      120 < n ∧ 60 ∣ n)
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
      60 ≤ g - 2 * n)
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
      d.natDegree ≤ g - 2 * n - 60)
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
      ee.natDegree ≤ g - n - 60)
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
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 60)) :
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
  change 120 < n ∧ 60 ∣ n at hnbig
  change 60 ∣ g at hg60
  change 60 ≤ g - 2 * n at htle
  change d.natDegree ≤ g - 2 * n - 60 at hd
  change ee.natDegree ≤ g - n - 60 at he
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + 60)
    at hcusp
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hclosable : g < 3 * n ∨ 14 * n + 2 * 60 < 5 * g := by
    by_cases hD : g < 3 * n
    · exact Or.inl hD
    · have : g = 3 * n := by omega
      have : 14 * n + 120 < 15 * n := by
        have : 120 < n := hnbig.1
        omega
      omega
  exact fiveToSix_terminalTail_cusp_impossible_of_closable68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 60
    hterminal hsys hzeta htle hd he hcusp hclosable

#print axioms fiveToSix_terminalTail_constantB_Qhigher_cusp_false68
#print axioms fiveToSix_terminalZero_n60_impossible68
#print axioms fiveToSix_terminalTail_cusp_impossible_of_constantB_Qhigher68
#print axioms fiveToSix_I3_forces_d_coeff_constantB68
#print axioms fiveToSix_U_of_B_zero68
#print axioms fiveToSix_B_zero_constant_cd_rowZero_impossible68
#print axioms fiveToSix_terminalZero_n90_impossible68
#print axioms fiveToSix_terminalZero_n120_impossible68
#print axioms fiveToSix_terminalZero_unaligned_t30_cusp_impossible68
#print axioms fiveToSix_terminalZero_aligned_t60_cusp_closable68

end FiveToSixTerminalZeroCells68

end Max11DegreeRoutes
