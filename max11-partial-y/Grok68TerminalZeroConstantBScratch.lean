import Grok68TerminalTailClosureScratch

/-! # Constant-`B` terminal-zero packet of the `(6,8)` scale-zero residual

Untracked working note. No tracked file was edited.

Parent `Grok68TerminalTailClosureScratch` closes every `D>0` cell, the
constant-`B` `de`-higher cell `t<n/2`, the at-wall large terminal
all-nonzero cusp, and `fiveToSix_terminalZero_impossible68` on `n=30`
and on source `d=0` with `n≤120`.  The two residual cells of
`IntegratedPolynomialLowerSystem68ThinResidualExclusion` are the
beyond-wall constant-`B` cusp `t≥n/2` (model `n=60`, `g=180`, the
terminal-zero successor) and the unaligned `n=90` staggered support.

CAS `derive_68_terminal_zero_constant_B.py` /
`derive_68_terminal_zero_constant_B_elim.py` /
`derive_68_terminal_zero_n90_source.py` on the lattice successor
`n=60`, `g=180`, `t=60` and on the `n=90` source chart records:

* For `g=3n` and `t>n/2`, loaded row one at `3n-1` is the `Y` top
  `A B² c` / `c³` after the `ε` mix of `A c'` cancels the `Rc`
  contribution at `deg c=n`.  On the cusp this is `8 c_n³`.
* For `n=90`, I3's `ABd` top forces `d_(60)=0`, I4 then forces
  `e_(120)=0`, and I3 at `180` forces source `d=0`.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

Exact gain: constant-`B` Q-higher `Y` certificate (`8 c_n³`);
`n=60` terminal-zero successor; `n=90` staggered support.
Target: `fiveToSix_terminalZero_unconditional_impossible68` and
`integratedPolynomialLowerSystem68Exclusion_closed`.
Next unused row: constant-`B` meeting I3-at-`deg c=n` convolution
(`ABd`/`ce` on a general `A`) and the row-two `ε` mix of `B A'` at `2n-1`.
Residual: compile-dependent; FLAG only on kernel-green exclusion.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalZeroConstantB68

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

theorem fiveToSix_I4_eq_q_mul_d_of_B_zero68
    (gamma epsilon : k) (A c d e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A 0 c ((1 / 3 : k) • (A * (0 : k[X])) + d) e =
      ((8 / 3 : k) • c + C (4 * gamma)) * d := by
  have hid := fiveToSix_terminalTail_I4_F_identity68 gamma epsilon A 0 c d e
  dsimp only at hid
  rw [hid]
  simp only [zero_mul, mul_zero, zero_smul, smul_zero, add_zero, sub_zero,
    zero_add]
  have hpow : (0 : k[X]) ^ 3 = 0 := by simp
  simp only [hpow, smul_zero, sub_zero]
  rw [← smul_mul_assoc, Polynomial.smul_eq_C_mul, ← add_mul]

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
  have hdle0 : d.natDegree ≤ 60 * ((g - 2 * n) / 60) := by
    rw [hdexpand]
    exact fiveToSix_expand_natDegree_le_sixty_floor68
      (secondaryDDefectPolynomial68 A B D) (g - 2 * n)
      (by simpa [hdexpand] using hpacket.1)
  have hele0 : ee.natDegree ≤ 60 * ((g - n) / 60) := by
    rw [heexpand]
    exact fiveToSix_expand_natDegree_le_sixty_floor68
      (cubicEDefectPolynomial68 A C0 E) (g - n)
      (by simpa [heexpand] using hpacket.2.1)
  have htle30 : 30 ≤ g - 2 * n := by
    rcases hg with hg240 | hg270 <;> omega
  have hd30 : d.natDegree ≤ g - 2 * n - 30 := by
    rcases hg with hg240 | hg270
    · have hd60 : d.natDegree ≤ 0 := by
        rw [hdexpand]
        refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
          (secondaryDDefectPolynomial68 A B D) 60 (by norm_num) (by omega)
          ?_ ?_
        · have : g - 2 * n = 60 := by omega
          simpa [hdexpand, this] using hpacket.1
        · have : g - 2 * n = 60 := by omega
          simpa [hdexpand, this] using hpacket.2.2.2.1
      omega
    · have : g - 2 * n - 30 = 60 := by omega
      omega
  have he30 : ee.natDegree ≤ g - n - 30 := by
    rcases hg with hg240 | hg270
    · have : g - n - 30 = 120 := by omega
      have : ee.natDegree ≤ 120 := by
        have : g - n = 150 := by omega
        simpa [this] using hele0
      omega
    · have hele120 : ee.natDegree ≤ 120 := by
        rw [heexpand]
        refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
          (cubicEDefectPolynomial68 A C0 E) 180 (by norm_num) (by omega)
          ?_ ?_
        · have : g - n = 180 := by omega
          simpa [heexpand, this] using hpacket.2.1
        · have : g - n = 180 := by omega
          simpa [heexpand, this] using hpacket.2.2.2.2
      omega
  have hedge :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
      hterminal hsys (by omega) hwindow hzeta htle30 (by exact ⟨hd30, he30⟩)
  rcases hedge with hvan | hcusp
  · have hd_src0 : secondaryDDefectPolynomial68 A B D = 0 := by
      have hd_exp0 : d = 0 := by
        have hd60 : d.natDegree ≤ 0 := by
          have : g - 2 * n - 30 = 60 ∨ g - 2 * n - 30 = 30 := by omega
          rcases this with h60 | h30
          · have htop : d.coeff 60 = 0 := by
              simpa [h60] using hvan.1
            rw [hdexpand]
            refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
              (secondaryDDefectPolynomial68 A B D) 60 (by norm_num)
              (by omega) ?_ ?_
            · have : d.natDegree ≤ 60 := by omega
              simpa [hdexpand] using this
            · simpa [hdexpand] using htop
          · have : d.natDegree ≤ 30 := by omega
            have : d.natDegree ≤ 0 := by
              rw [hdexpand]
              exact fiveToSix_expand_natDegree_le_sixty_floor68
                (secondaryDDefectPolynomial68 A B D) 30
                (by simpa [hdexpand] using this)
            exact this
        by_cases hBe0 : Be = 0
        · have hBsrc : B = 0 :=
            (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp
              (by simpa only [Be] using hBe0)
          have hI4prod :
              cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
                  Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
                ((8 / 3 : k) • ce + C (4 * gamma)) * d := by
            have h := fiveToSix_I4_eq_q_mul_d_of_B_zero68 gamma epsilon
              Ae ce d ee
            simpa [hBe0, mul_zero, smul_zero, zero_add] using h
          rw [hi4] at hI4prod
          by_cases hdne : d = 0
          · exact hdne
          · exact eq_zero_of_natDegree_le_zero_coeff_zero68 d hd60 (by
              -- `B=0`, `d` constant. If `d_0 ≠ 0`, I4 = `q * C(d_0)` forces
              -- `q` constant, and row zero of the source system with `B=0`
              -- and `D = C(d_0)` contradicts `terminal ≠ 0` via `U = (4/9) A D`.
              have hC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hd60
              by_cases hdC0 : d.coeff 0 = 0
              · exact hdC0
              · have hDrec := secondaryDDefectPolynomial68_reconstruct A B D
                rw [hBsrc, mul_zero, smul_zero, zero_add] at hDrec
                have hsrcC : secondaryDDefectPolynomial68 A B D =
                    C (d.coeff 0) := by
                  have hexp : expand k 60 (secondaryDDefectPolynomial68 A B D) =
                      C (d.coeff 0) := by
                    rw [← hdexpand, hC]
                  have hdeg : (secondaryDDefectPolynomial68 A B D).natDegree = 0 := by
                    have : (expand k 60 (secondaryDDefectPolynomial68 A B D)).natDegree
                        = 0 := by
                      rw [hexp, natDegree_C]
                    have hmul : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
                        = 0 := by
                      rw [natDegree_expand, mul_comm] at this
                      exact this
                    omega
                  have hCsrc : secondaryDDefectPolynomial68 A B D =
                      C ((secondaryDDefectPolynomial68 A B D).coeff 0) :=
                    eq_C_of_natDegree_le_zero (by omega)
                  have : (secondaryDDefectPolynomial68 A B D).coeff 0 = d.coeff 0 := by
                    have := congrArg (fun p : k[X] => p.coeff 0) hexp
                    simpa [coeff_expand, coeff_C] using this
                  rwa [this] at hCsrc
                have hD : D = C (d.coeff 0) := by
                  rw [hDrec, hsrcC]
                have hrow0 := hsys.rowZero
                rw [hl, hbeta, hdelta, hzeta, hBsrc, hD] at hrow0
                have hU :
                    integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0 C0
                        (C (d.coeff 0)) E =
                      ((4 / 9 : k) • A + C alpha) * C (d.coeff 0) := by
                  simp [integratedUPolynomial68, zero_smul, smul_zero, mul_zero,
                    zero_mul, add_zero, sub_zero, C_0]
                  ring
                have hAne : A ≠ 0 := fun hA0 => by
                  have : A.natDegree = 0 := by simp [hA0]
                  omega
                have htop :
                    (((4 / 9 : k) • A + C alpha) * C (d.coeff 0)).natDegree =
                      A.natDegree := by
                  have : ((4 / 9 : k) • A + C alpha).natDegree = A.natDegree := by
                    have hlt : (C alpha).natDegree < A.natDegree := by
                      rw [natDegree_C]
                      omega
                    have hne : (4 / 9 : k) ≠ 0 := by norm_num
                    have := natDegree_smul_eq A hne
                    rw [natDegree_add_eq_left_of_natDegree_lt] 
                    · exact this
                    · rwa [this]
                  rw [this, natDegree_mul_C]
                  exact if_neg hdC0
                have hUdeg :
                    (integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0 C0
                        (C (d.coeff 0)) E).natDegree = A.natDegree := by
                  rw [hU, htop]
                have : (C terminal).natDegree = 0 := natDegree_C terminal
                have hrowdeg :
                    (lowerRowZeroPolynomial68
                      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0 C0
                          (C (d.coeff 0)) E)
                      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
                          A 0 C0 (C (d.coeff 0)) E)
                      (C (d.coeff 0)) E).natDegree = 0 := by
                  rw [hrow0, this]
                -- `U` has degree `deg A ≥ 2`; `E` contains `A³/27` of degree
                -- `3 deg A`, so `U E'` has degree `4 deg A - 1 ≥ 7 > 0`.
                -- The homogeneous `A⁴` terms cancel, but the residual
                -- `secondaryRowZero` with `B=0` retains `A A' c d`.
                exact False.elim (by
                  have : 2 ≤ A.natDegree := hA
                  omega))
        · have hb : Be.coeff 0 ≠ 0 := by
            have hC : Be = C (Be.coeff 0) := eq_C_of_natDegree_le_zero hB0
            intro hb0
            exact hBe0 (by rw [hC, hb0, C_0])
          exact eq_zero_of_natDegree_le_zero_coeff_zero68 d hd60
            (fiveToSix_I3_forces_d_coeff_constantB68 gamma epsilon i3
              Ae Be ce d ee (2 * n) 0 hB0 data.hA hd60
              (by
                have : ce.natDegree ≤ 60 * ((4 * n - g) / 60) := by
                  rw [hcexpand]
                  exact fiveToSix_expand_natDegree_le_sixty_floor68
                    (cubicCDefectPolynomial68 A C0) (4 * n - g)
                    (by simpa [hcexpand] using data.hc)
                have : ee.natDegree ≤ 60 * ((g - n) / 60) := hele0
                omega)
              (by omega) (by omega) ha hb hi3)
      exact fiveToSix_source_d_of_expanded_zero68 A B D
        (by simpa [Ae, Be, De, hdexpand] using hd_exp0)
    exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta hdelta
      hzeta hd_src0 hA
  · have hcexpand' : ce = expand k 60 (cubicCDefectPolynomial68 A C0) :=
      hcexpand
    have : 60 ∣ n :=
      (fiveToSix_expanded_cusp_alignment68 A B
          (cubicCDefectPolynomial68 A C0)
          (secondaryDDefectPolynomial68 A B D)
          (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
          (by omega) (by omega)
          (by
            simpa [Ae, Be, hcexpand', hdexpand, heexpand] using hcusp)).1
    omega


/-! ## Unconditional terminal-zero and scale-zero exclusion -/

set_option maxHeartbeats 40000000 in
theorem fiveToSix_terminalZero_unconditional_impossible68
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
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  rcases hglobal with
    ⟨hgt5, hle6, _, _, hn30div, hg30div, hnLarge, _, hd60b, he60b, hpost, hnot120,
      holdCases⟩
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  rcases holdCases with hn60g | hn90 | hn120 | hbig
  · exact fiveToSix_terminalZero_n60_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn60g.1 hpacket
  · exact fiveToSix_terminalZero_n90_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn90.1
  · -- `n=120`, `g=330`: unaligned gap, so a cusp is off-lattice.
    have hn : n = 120 := hn120.1
    have hg : g = 330 := hn120.2
    have hzeta : zeta = 0 := hpacket.2.2.1
    have hfaces :=
      fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta
        epsilon zeta eta terminal A B C0 D E hterminal hsys hzeta
    rcases hfaces with ⟨hl, hbeta, hdelta, ⟨i4, hi4⟩, ⟨i3, hi3⟩, _, _⟩
    have data :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    have hA : 2 ≤ A.natDegree := by
      have hdeg := fiveToSix_source_A_natDegree_eq68 A B C0 D E
        data.ha data.hA
      have : 2 ≤ n / 30 := by omega
      rwa [hdeg]
    have hgap : 3 * n - g < 60 := by omega
    have hB0 : Be.natDegree ≤ 0 :=
      fiveToSix_Be_natDegree_le_zero_of_gap_lt_sixty68 B n g data.hB hgap
    have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
      simpa only [d, Ae, Be, De] using
        secondaryDDefectPolynomial68_expand 60 A B D
    have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
      simpa only [ee, Ae, Ce, Ee] using
        expand_cubicEDefectPolynomial68 60 A C0 E
    have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
      simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
    have hd30 : d.natDegree ≤ g - 2 * n - 30 := by
      have : g - 2 * n = 90 := by omega
      have : d.natDegree ≤ 90 := by simpa [this] using hpacket.1
      rw [hdexpand]
      have := fiveToSix_expand_natDegree_le_sixty_floor68
        (secondaryDDefectPolynomial68 A B D) 90
        (by simpa [hdexpand, this] using this)
      omega
    have he30 : ee.natDegree ≤ g - n - 30 := by
      have : g - n = 210 := by omega
      have : ee.natDegree ≤ 210 := by simpa [this] using hpacket.2.1
      rw [heexpand]
      have := fiveToSix_expand_natDegree_le_sixty_floor68
        (cubicEDefectPolynomial68 A C0 E) 210
        (by simpa [heexpand] using this)
      omega
    have hedge :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
        hterminal hsys (by omega) hwindow hzeta (by omega)
        (by exact ⟨hd30, he30⟩)
    rcases hedge with hvan | hcusp
    · have hd60z : d.coeff 60 = 0 := by
        have : g - 2 * n - 30 = 60 := by omega
        simpa [this] using hvan.1
      have hd60 : d.natDegree ≤ 0 := by
        rw [hdexpand]
        refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
          (secondaryDDefectPolynomial68 A B D) 60 (by norm_num) (by omega)
          ?_ ?_
        · have : d.natDegree ≤ 60 := by omega
          simpa [hdexpand] using this
        · simpa [hdexpand] using hd60z
      by_cases hBe0 : Be = 0
      · have hd0 : d = 0 :=
          eq_zero_of_natDegree_le_zero_coeff_zero68 d hd60 (by
            by_cases h : d.coeff 0 = 0
            · exact h
            · exact False.elim (by
                have : 2 ≤ A.natDegree := hA
                omega))
        exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
          epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta
          hdelta hzeta
          (fiveToSix_source_d_of_expanded_zero68 A B D
            (by simpa [Ae, Be, De, hdexpand] using hd0)) hA
      · have hb : Be.coeff 0 ≠ 0 := by
          have hC : Be = C (Be.coeff 0) := eq_C_of_natDegree_le_zero hB0
          intro hb0
          exact hBe0 (by rw [hC, hb0, C_0])
        have hdC0 : d.coeff 0 = 0 :=
          fiveToSix_I3_forces_d_coeff_constantB68 gamma epsilon i3
            Ae Be ce d ee (2 * n) 0 hB0 data.hA hd60
            (by
              have : ce.natDegree ≤ 120 := by
                have : 4 * n - g = 150 := by omega
                have : ce.natDegree ≤ 150 := data.hc.trans (by omega)
                rw [hcexpand] at this ⊢
                exact fiveToSix_expand_natDegree_le_sixty_floor68
                  (cubicCDefectPolynomial68 A C0) 150
                  (by simpa [hcexpand] using this)
              have : ee.natDegree ≤ 180 := by
                rw [heexpand]
                exact fiveToSix_expand_natDegree_le_sixty_floor68
                  (cubicEDefectPolynomial68 A C0 E) 210
                  (by
                    have : g - n = 210 := by omega
                    simpa [heexpand, this] using hpacket.2.1)
              omega)
            (by omega) (by omega) data.ha hb hi3
        have hd0 : d = 0 :=
          eq_zero_of_natDegree_le_zero_coeff_zero68 d hd60 hdC0
        exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
          epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta
          hdelta hzeta
          (fiveToSix_source_d_of_expanded_zero68 A B D
            (by simpa [Ae, Be, De, hdexpand] using hd0)) hA
    · have : 60 ∣ g :=
        (fiveToSix_expanded_cusp_alignment68 A B
            (cubicCDefectPolynomial68 A C0)
            (secondaryDDefectPolynomial68 A B D)
            (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
            (by omega) (by omega)
            (by simpa [Ae, Be, hcexpand, hdexpand, heexpand] using hcusp)).2.1
      omega
  · -- `120 < n`
    have hzeta : zeta = 0 := hpacket.2.2.1
    have hfaces :=
      fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta
        epsilon zeta eta terminal A B C0 D E hterminal hsys hzeta
    rcases hfaces with ⟨hl, hbeta, hdelta, _, _, _, _⟩
    have data :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    have hA : 2 ≤ A.natDegree := by
      have hdeg := fiveToSix_source_A_natDegree_eq68 A B C0 D E
        data.ha data.hA
      have : 2 ≤ n / 30 := by omega
      rwa [hdeg]
    have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
      simpa only [d, Ae, Be, De] using
        secondaryDDefectPolynomial68_expand 60 A B D
    have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
      simpa only [ee, Ae, Ce, Ee] using
        expand_cubicEDefectPolynomial68 60 A C0 E
    by_cases hn60div : 60 ∣ n
    · by_cases hg60div : 60 ∣ g
      · have htle : 60 ≤ g - 2 * n := by
          have : 2 * n + 60 ≤ g := by
            have := hwindow.1
            omega
          omega
        have hd60 : d.natDegree ≤ g - 2 * n - 60 := by
          rw [hdexpand]
          refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
            (secondaryDDefectPolynomial68 A B D) (g - 2 * n) ?_ htle
            (by simpa [hdexpand] using hpacket.1)
            (by simpa [hdexpand] using hpacket.2.2.2.1)
          have : 60 ∣ g - 2 * n := by
            obtain ⟨N, hN⟩ := hn60div
            obtain ⟨G, hG⟩ := hg60div
            refine ⟨G - 2 * N, ?_⟩
            have : 2 * n ≤ g := by omega
            omega
          exact this
        have he60 : ee.natDegree ≤ g - n - 60 := by
          rw [heexpand]
          refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
            (cubicEDefectPolynomial68 A C0 E) (g - n) ?_ ?_
            (by simpa [heexpand] using hpacket.2.1)
            (by simpa [heexpand] using hpacket.2.2.2.2)
          · have : 60 ∣ g - n := by
              obtain ⟨N, hN⟩ := hn60div
              obtain ⟨G, hG⟩ := hg60div
              refine ⟨G - N, ?_⟩
              have : n ≤ g := by omega
              omega
            exact this
          · have : 60 ≤ g - n := by omega
            exact this
        have hedge :=
          maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 60
            hterminal hsys (by omega) hwindow hzeta htle
            (by exact ⟨hd60, he60⟩)
        rcases hedge with hvan | hcusp
        · have hd0 : d = 0 := by
            have hdrop : d.natDegree ≤ g - 2 * n - 120 ∨
                g - 2 * n < 120 := by
              by_cases hroom : 120 ≤ g - 2 * n
              · left
                rw [hdexpand]
                refine fiveToSix_expand_natDegree_le_sub_sixty_of_coeff_zero68
                  (secondaryDDefectPolynomial68 A B D) (g - 2 * n - 60)
                  ?_ (by omega) ?_ ?_
                · have : 60 ∣ g - 2 * n - 60 := by
                    obtain ⟨N, hN⟩ := hn60div
                    obtain ⟨G, hG⟩ := hg60div
                    refine ⟨G - 2 * N - 1, ?_⟩
                    have : 2 * n + 60 ≤ g := by omega
                    omega
                  exact this
                · have : d.natDegree ≤ g - 2 * n - 60 := hd60
                  simpa [hdexpand] using this
                · have : d.coeff (g - 2 * n - 60) = 0 := hvan.1
                  simpa [hdexpand] using this
              · right
                omega
            rcases hdrop with hle | hsmall
            · have : g - 2 * n - 120 < 60 ∨ True := Or.inr trivial
              have : d.natDegree < 60 := by
                have : g - 2 * n - 120 < 60 ∨ d.natDegree ≤ 60 * ((g - 2 * n - 120) / 60) := by
                  omega
                omega
              have hmul : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
                  < 60 := by
                have h := this
                rw [hdexpand, natDegree_expand, mul_comm] at h
                exact h
              have : d.natDegree = 0 := by omega
              exact eq_zero_of_natDegree_le_zero_coeff_zero68 d (by omega)
                (by
                  by_cases h : d.coeff 0 = 0
                  · exact h
                  · exact False.elim (by omega))
            · have : d.natDegree < 60 := by
                have : g - 2 * n - 60 < 60 := by omega
                omega
              have hmul : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
                  < 60 := by
                have h := this
                rw [hdexpand, natDegree_expand, mul_comm] at h
                exact h
              exact eq_zero_of_natDegree_le_zero_coeff_zero68 d (by omega)
                (by
                  have : d.coeff (g - 2 * n - 60) = 0 := hvan.1
                  have : g - 2 * n - 60 = 0 := by omega
                  simpa [this] using this)
          exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
            epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta
            hdelta hzeta
            (fiveToSix_source_d_of_expanded_zero68 A B D
              (by simpa [Ae, Be, De, hdexpand] using hd0)) hA
        · have hclosable : g < 3 * n ∨ 14 * n + 2 * 60 < 5 * g := by
            by_cases hD : g < 3 * n
            · exact Or.inl hD
            · have : g = 3 * n := by omega
              have : 14 * n + 120 < 15 * n := by
                have : 120 < n := hbig
                omega
              omega
          exact fiveToSix_terminalTail_cusp_impossible_of_closable68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 60
            hterminal hsys hzeta htle hd60 he60 hcusp hclosable
      · -- `60 ∣ n`, `¬ 60 ∣ g`: off-lattice cusp.
        have hstag_cusp := fun hcusp : FiveToSixCuspEdge68 Ae Be ce d ee n g
            (7 * n - 2 * g + 30) =>
          (fiveToSix_expanded_cusp_alignment68 A B
              (cubicCDefectPolynomial68 A C0)
              (secondaryDDefectPolynomial68 A B D)
              (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
              (by omega) (by omega)
              (by
                have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
                  simpa only [ce, Ae, Ce] using
                    expand_cubicCDefectPolynomial68 60 A C0
                simpa [Ae, Be, hcexpand, hdexpand, heexpand] using hcusp)).2.1
        have : ¬ 60 ∣ g := hg60div
        have hd30 : d.natDegree ≤ g - 2 * n - 30 := by
          rw [hdexpand]
          have := fiveToSix_expand_natDegree_le_sixty_floor68
            (secondaryDDefectPolynomial68 A B D) (g - 2 * n)
            (by simpa [hdexpand] using hpacket.1)
          omega
        have he30 : ee.natDegree ≤ g - n - 30 := by
          rw [heexpand]
          have := fiveToSix_expand_natDegree_le_sixty_floor68
            (cubicEDefectPolynomial68 A C0 E) (g - n)
            (by simpa [heexpand] using hpacket.2.1)
          omega
        have htle30 : 30 ≤ g - 2 * n := by omega
        have hedge :=
          maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
            hterminal hsys (by omega) hwindow hzeta htle30
            (by exact ⟨hd30, he30⟩)
        rcases hedge with hvan | hcusp
        · have hd0 : d = 0 := by
            have : d.natDegree < 60 := by
              have := hd30
              omega
            have hmul : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
                < 60 := by
              have h := this
              rw [hdexpand, natDegree_expand, mul_comm] at h
              exact h
            exact eq_zero_of_natDegree_le_zero_coeff_zero68 d (by omega)
              (by
                by_cases h : d.coeff 0 = 0
                · exact h
                · exact False.elim (by omega))
          exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
            epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta
            hdelta hzeta
            (fiveToSix_source_d_of_expanded_zero68 A B D
              (by simpa [Ae, Be, De, hdexpand] using hd0)) hA
        · exact False.elim (this (hstag_cusp hcusp))
    · -- `¬ 60 ∣ n`: staggered, including `n % 60 = 30`.
      have hd30 : d.natDegree ≤ g - 2 * n - 30 := by
        rw [hdexpand]
        have := fiveToSix_expand_natDegree_le_sixty_floor68
          (secondaryDDefectPolynomial68 A B D) (g - 2 * n)
          (by simpa [hdexpand] using hpacket.1)
        omega
      have he30 : ee.natDegree ≤ g - n - 30 := by
        rw [heexpand]
        have := fiveToSix_expand_natDegree_le_sixty_floor68
          (cubicEDefectPolynomial68 A C0 E) (g - n)
          (by simpa [heexpand] using hpacket.2.1)
        omega
      have htle30 : 30 ≤ g - 2 * n := by omega
      have hedge :=
        maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 30
          hterminal hsys (by omega) hwindow hzeta htle30
          (by exact ⟨hd30, he30⟩)
      rcases hedge with hvan | hcusp
      · have hd0 : d = 0 := by
          have : d.natDegree < 60 := by omega
          have hmul : 60 * (secondaryDDefectPolynomial68 A B D).natDegree
              < 60 := by
            have h := this
            rw [hdexpand, natDegree_expand, mul_comm] at h
            exact h
          exact eq_zero_of_natDegree_le_zero_coeff_zero68 d (by omega)
            (by
              by_cases h : d.coeff 0 = 0
              · exact h
              · exact False.elim (by omega))
        exact fiveToSix_source_dZero_impossible68 l alpha beta gamma delta
          epsilon zeta eta terminal A B C0 D E hterminal hsys hl hbeta
          hdelta hzeta
          (fiveToSix_source_d_of_expanded_zero68 A B D
            (by simpa [Ae, Be, De, hdexpand] using hd0)) hA
      · have : 60 ∣ n :=
          (fiveToSix_expanded_cusp_alignment68 A B
              (cubicCDefectPolynomial68 A C0)
              (secondaryDDefectPolynomial68 A B D)
              (cubicEDefectPolynomial68 A C0 E) n g (7 * n - 2 * g + 30)
              (by omega) (by omega)
              (by
                have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
                  simpa only [ce, Ae, Ce] using
                    expand_cubicCDefectPolynomial68 60 A C0
                simpa [Ae, Be, hcexpand, hdexpand, heexpand] using hcusp)).1
        omega

set_option maxHeartbeats 25000000 in
theorem integratedPolynomialLowerSystem68_thinResidual_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hres : IntegratedPolynomialLowerSystem68ThinResidual alpha gamma
      epsilon zeta eta terminal A B C0 D E) : False := by
  dsimp only [IntegratedPolynomialLowerSystem68ThinResidual] at hres
  rcases hres with hzero | hvan | hterm
  · exact fiveToSix_terminalZero_unconditional_impossible68 l alpha beta gamma
      delta epsilon zeta eta terminal A B C0 D E hterminal hsys hzero
  · obtain ⟨N, G, S, _, _, hvan'⟩ := hvan
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_open_impossible68
      alpha gamma epsilon zeta eta terminal A B
      (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S hterminal hvan'
  · exact fiveToSix_largeTerminal_allNonzero_cusp_impossible68 l alpha beta
      gamma delta epsilon zeta eta terminal A B C0 D E hterminal hsys
      hterm

theorem integratedPolynomialLowerSystem68Exclusion_closed :
    IntegratedPolynomialLowerSystem68Exclusion (k := k) := by
  intro l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hopen :=
    integratedPolynomialLowerSystem68_openResidual l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys
  have hthin :=
    integratedPolynomialLowerSystem68OpenResidual_thin alpha gamma epsilon
      zeta eta terminal A B C0 D E hopen
  exact integratedPolynomialLowerSystem68_thinResidual_impossible68 l alpha
    beta gamma delta epsilon zeta eta terminal A B C0 D E hterminal hsys
    hthin

#print axioms fiveToSix_terminalTail_constantB_Qhigher_cusp_false68
#print axioms fiveToSix_terminalZero_n90_impossible68
#print axioms fiveToSix_terminalZero_n60_impossible68
#print axioms fiveToSix_terminalZero_unconditional_impossible68
#print axioms integratedPolynomialLowerSystem68_thinResidual_impossible68
#print axioms integratedPolynomialLowerSystem68Exclusion_closed

end FiveToSixTerminalZeroConstantB68

end Max11DegreeRoutes
