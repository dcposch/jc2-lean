import Grok68AlignedNonsquareDegreeZeroPrimitiveScratch
import Grok68AlignedSquareChamberClosureScratch

/-! # CLOSED. ODE closure of the `(6,8)` scale-two aligned-nonsquare chamber

Untracked working note. No tracked file was edited.

Target Prop: `PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`
(`LowScale68ScaleTwoAlignedNonsquareBridge.lean:934`).  The aligned-square
chamber is already closed:
`planeKellerNormalized68ScaleTwoRoute_of_quadraticPacket` in
`Grok68AlignedSquareChamberClosureScratch.lean` turns that packet
exclusion into `PlaneKellerNormalized68ScaleTwoRoute`.

Parent (tracked, green): `Grok68AlignedNonsquareDegreeZeroPrimitiveScratch`
(`NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_deriv`,
`degreeZeroPrimitive_odd`, `degreeZeroPrimitive_eq_mul_root`,
`quadraticDerivation46_root68`, `H_ne_zero_of_nonsquare_core68`).

CAS job `20260902T123231Z-68-aligned-nonsquare-degree-zero-618409`
(`scripts/derive_68_aligned_nonsquare_degree_zero.py`): the ODE
`2 H Q' + Q H' = 2 j` has no rational solution when `H.natDegree = 2`
and `j ≠ 0`.  A nonsquare quadratic is automatically squarefree.

The named packet Prop quantifies over every nonsquare core.  A linear
nonsquare admits a constant rational solution of the ODE, so that Prop
is strictly stronger than the scale-two chamber.  Scale-two cores
always supply `H.natDegree = 2` via `Normalized68LeadingCoreSource`.
The chamber closed here is `PlaneKeller68AlignedNonsquareExclusion`.
The unrestricted packet Prop is therefore not claimed; the source-facing
kill on quadratic cores is
`planeKeller68AlignedNonsquareQuadraticPacketExclusion_of_natDegree_two`.

Landed:

1. Transport `d(Q · √H) = j / √H` into the `k(x)` identity
   `2 H Q' + Q H' = 2 j`.
2. Clearing `Q = n/d` to the polynomial identity
   `2 H (n' d - n d') + n H' d = 2 j d²`.
3. Degree/leading-coefficient comparison on that identity for
   `H.natDegree = 2`: the `X^(a+b+1)` coefficient of the left side is
   `2 c (a - b + 1) n_a d_b`.  Either `a = b - 1` (then that top term
   vanishes identically, while the right side has degree `2b` with
   leading coefficient `2 j d_b² ≠ 0`) or the two sides have unequal
   degree.
4. False on quadratic cores, hence
   `planeKeller68AlignedNonsquareExclusion_closed`, hence
   `PlaneKellerNormalized68ScaleTwoRoute` via the already-closed
   aligned-square local-root exclusion.

FLAG: 68 SCALE-TWO CLOSED

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Polynomial Wronskian and the quadratic-core ODE obstruction -/

section QuadraticOdePolynomial68

variable {k : Type*} [Field k] [CharZero k]

/-- Polynomial Wronskian `n' d - n d'`. -/
def wronskianPoly68 (n d : k[X]) : k[X] :=
  n.derivative * d - n * d.derivative

theorem wronskianPoly68_zero_of_constants
    (n d : k[X]) (hn : n.natDegree = 0) (hd : d.natDegree = 0) :
    wronskianPoly68 n d = 0 := by
  have hn' : n.derivative = 0 := by
    rw [eq_C_of_natDegree_eq_zero hn, derivative_C]
  have hd' : d.derivative = 0 := by
    rw [eq_C_of_natDegree_eq_zero hd, derivative_C]
  simp [wronskianPoly68, hn', hd']

theorem natDegree_cast_pred_succ68
    {n : ℕ} (hp : 0 < n) :
    ((n - 1 : ℕ) : k) + 1 = (n : k) := by
  have hle : 1 ≤ n := Nat.succ_le_of_lt hp
  rw [Nat.cast_sub hle, Nat.cast_one]
  ring

theorem natDegree_derivative_eq68
    (p : k[X]) (hp : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  have hpne : p ≠ 0 := fun h => by simp [h] at hp
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hpne
  have hcoeff : p.derivative.coeff (p.natDegree - 1) ≠ 0 := by
    have hn : p.natDegree - 1 + 1 = p.natDegree :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
    rw [coeff_derivative, hn, coeff_natDegree]
    have hn1 : ((p.natDegree - 1 : ℕ) : k) + 1 ≠ 0 := by
      rw [natDegree_cast_pred_succ68 hp]
      exact Nat.cast_ne_zero.mpr (ne_of_gt hp)
    exact mul_ne_zero hlc hn1
  exact le_antisymm (natDegree_derivative_le p)
    (le_natDegree_of_ne_zero hcoeff)

theorem leadingCoeff_derivative_eq68
    (p : k[X]) (hp : 0 < p.natDegree) :
    p.derivative.leadingCoeff =
      (p.natDegree : k) * p.leadingCoeff := by
  have hdeg := natDegree_derivative_eq68 p hp
  have hn : p.natDegree - 1 + 1 = p.natDegree :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
  rw [leadingCoeff, hdeg, coeff_derivative, hn, coeff_natDegree,
    natDegree_cast_pred_succ68 hp]
  ring

theorem wronskianPoly68_coeff_top
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0) :
    (wronskianPoly68 n d).coeff
        (n.natDegree + d.natDegree - 1) =
      ((n.natDegree : k) - (d.natDegree : k)) *
        n.leadingCoeff * d.leadingCoeff := by
  set a := n.natDegree with ha
  set b := d.natDegree with hb
  by_cases ha0 : a = 0
  · have hnC : n = C n.leadingCoeff := by
      have hC := eq_C_of_natDegree_eq_zero (ha.symm.trans ha0)
      have hlc : n.coeff 0 = n.leadingCoeff := by
        rw [leadingCoeff, show n.natDegree = 0 from ha.symm.trans ha0]
      exact hC.trans (congrArg C hlc)
    have hn' : n.derivative = 0 := by
      rw [hnC, derivative_C]
    have hleft : (n.derivative * d).coeff (a + b - 1) = 0 := by
      simp [hn']
    by_cases hb0 : b = 0
    · have hd' : d.derivative = 0 := by
        rw [eq_C_of_natDegree_eq_zero (hb.symm.trans hb0), derivative_C]
      simp [wronskianPoly68, hn', hd', ha0, hb0]
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hN : a + b - 1 = b - 1 := by simp [ha0]
      have hright :
          (n * d.derivative).coeff (b - 1) =
            n.leadingCoeff * ((b : k) * d.leadingCoeff) := by
        have hdb : d.derivative.natDegree = b - 1 :=
          natDegree_derivative_eq68 d hbpos
        rw [hnC, coeff_C_mul, ← hdb, coeff_natDegree,
          leadingCoeff_derivative_eq68 d hbpos]
        simp [show d.natDegree = b from hb.symm]
      have hleft' : (n.derivative * d).coeff (b - 1) = 0 := by
        rw [← hN]
        exact hleft
      rw [wronskianPoly68, coeff_sub, hN, hleft', hright]
      simp [ha0]
      ring
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hn' : n.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hapos)
    have hna : n.derivative.natDegree = a - 1 :=
      natDegree_derivative_eq68 n hapos
    by_cases hb0 : b = 0
    · have hdC : d = C d.leadingCoeff := by
        have hC := eq_C_of_natDegree_eq_zero (hb.symm.trans hb0)
        have hlc : d.coeff 0 = d.leadingCoeff := by
          rw [leadingCoeff, show d.natDegree = 0 from hb.symm.trans hb0]
        exact hC.trans (congrArg C hlc)
      have hd' : d.derivative = 0 := by
        rw [hdC, derivative_C]
      have hN : a + b - 1 = a - 1 := by simp [hb0]
      have hleft :
          (n.derivative * d).coeff (a - 1) =
            ((a : k) * n.leadingCoeff) * d.leadingCoeff := by
        rw [hdC]
        simp only [leadingCoeff_C]
        rw [mul_comm n.derivative, coeff_C_mul, ← hna, coeff_natDegree,
          leadingCoeff_derivative_eq68 n hapos]
        simp only [show n.natDegree = a from ha.symm]
        ring
      have hright0 : (n * d.derivative).coeff (a - 1) = 0 := by
        simp [hd']
      rw [wronskianPoly68, coeff_sub, hN, hleft, hright0]
      simp only [hb0]
      ring
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hd' : d.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hbpos)
      have hdb : d.derivative.natDegree = b - 1 :=
        natDegree_derivative_eq68 d hbpos
      have hN : a - 1 + b = a + b - 1 := by omega
      have hN' : a + (b - 1) = a + b - 1 := by omega
      have hleft :
          (n.derivative * d).coeff (a + b - 1) =
            ((a : k) * n.leadingCoeff) * d.leadingCoeff := by
        have hmul := natDegree_mul hn' hd
        rw [hna] at hmul
        rw [← hN, ← hmul, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_derivative_eq68 n hapos]
      have hright :
          (n * d.derivative).coeff (a + b - 1) =
            n.leadingCoeff * ((b : k) * d.leadingCoeff) := by
        have hmul := natDegree_mul hn hd'
        rw [hdb] at hmul
        rw [← hN', ← hmul, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_derivative_eq68 d hbpos]
      rw [wronskianPoly68, coeff_sub, hleft, hright]
      ring

theorem wronskianPoly68_natDegree_le
    (n d : k[X]) :
    (wronskianPoly68 n d).natDegree ≤
      n.natDegree + d.natDegree - 1 := by
  set a := n.natDegree
  set b := d.natDegree
  have hleft : (n.derivative * d).natDegree ≤ a + b - 1 := by
    by_cases ha0 : a = 0
    · have hn' : n.derivative = 0 := by
        rw [eq_C_of_natDegree_eq_zero (show n.natDegree = 0 from ha0),
          derivative_C]
      simp [hn']
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hn' : n.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hapos)
      have hmul : (n.derivative * d).natDegree ≤
          n.derivative.natDegree + d.natDegree := natDegree_mul_le
      have hder := natDegree_derivative_eq68 n hapos
      have : a - 1 + b = a + b - 1 := by omega
      exact hmul.trans (le_of_eq (by simp [a, b, hder, this]))
  have hright : (n * d.derivative).natDegree ≤ a + b - 1 := by
    by_cases hb0 : b = 0
    · have hd' : d.derivative = 0 := by
        rw [eq_C_of_natDegree_eq_zero (show d.natDegree = 0 from hb0),
          derivative_C]
      simp [hd']
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hd' : d.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hbpos)
      have hmul : (n * d.derivative).natDegree ≤
          n.natDegree + d.derivative.natDegree := natDegree_mul_le
      have hder := natDegree_derivative_eq68 d hbpos
      have : a + (b - 1) = a + b - 1 := by omega
      exact hmul.trans (le_of_eq (by simp [a, b, hder, this]))
  exact (natDegree_sub_le (n.derivative * d) (n * d.derivative)).trans
    (max_le hleft hright)

theorem wronskianPoly68_natDegree_eq_of_ne
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0)
    (hneq : n.natDegree ≠ d.natDegree) :
    (wronskianPoly68 n d).natDegree =
      n.natDegree + d.natDegree - 1 := by
  have hcoeff := wronskianPoly68_coeff_top n d hn hd
  have hcast : (n.natDegree : k) ≠ (d.natDegree : k) :=
    (Nat.cast_injective (R := k)).ne hneq
  have ha : n.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hn
  have hb : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd
  have hne :
      (wronskianPoly68 n d).coeff (n.natDegree + d.natDegree - 1) ≠ 0 := by
    intro hz
    have hsub : (n.natDegree : k) - (d.natDegree : k) ≠ 0 :=
      sub_ne_zero.mpr hcast
    apply hsub
    have hprod := hcoeff.symm.trans hz
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact (ha h').elim
    · exact (hb h).elim
  exact le_antisymm (wronskianPoly68_natDegree_le n d)
    (le_natDegree_of_ne_zero hne)

theorem wronskianPoly68_leadingCoeff_of_ne
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0)
    (hneq : n.natDegree ≠ d.natDegree) :
    (wronskianPoly68 n d).leadingCoeff =
      ((n.natDegree : k) - (d.natDegree : k)) *
        n.leadingCoeff * d.leadingCoeff := by
  rw [leadingCoeff, wronskianPoly68_natDegree_eq_of_ne n d hn hd hneq]
  exact wronskianPoly68_coeff_top n d hn hd

theorem wronskianPoly68_natDegree_le_of_eq
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0)
    (heq : n.natDegree = d.natDegree)
    (hpos : 0 < n.natDegree) :
    (wronskianPoly68 n d).natDegree ≤
      n.natDegree + d.natDegree - 2 := by
  have hle := wronskianPoly68_natDegree_le n d
  have hz : (wronskianPoly68 n d).coeff
      (n.natDegree + d.natDegree - 1) = 0 := by
    rw [wronskianPoly68_coeff_top n d hn hd, heq]
    ring
  by_cases htop : (wronskianPoly68 n d).natDegree =
      n.natDegree + d.natDegree - 1
  · have hlc : (wronskianPoly68 n d).leadingCoeff = 0 := by
      rw [leadingCoeff, htop, hz]
    have hW0 : wronskianPoly68 n d = 0 := leadingCoeff_eq_zero.mp hlc
    have : (wronskianPoly68 n d).natDegree = 0 := by simp [hW0]
    have hsum : n.natDegree + d.natDegree - 1 = 0 := this ▸ htop.symm
    omega
  · omega

/-- Cleared polynomial form of the rational ODE
`2 H Q' + Q H' = 2 j` on `Q = n/d`. -/
def quadraticOdeCleared68 (H n d : k[X]) (j : k) : Prop :=
  C (2 : k) * H * wronskianPoly68 n d + n * H.derivative * d =
    C (2 : k) * C j * d ^ 2

/-- The polynomial identity `2 H (n'd - n d') + n H' d = 2 j d²` has
no solution for `j ≠ 0` when `H.natDegree = 2`. -/
theorem quadraticCoreOde_no_polynomial_solution68
    (H n d : k[X]) (j : k)
    (hH : H.natDegree = 2) (hd : d ≠ 0) (hj : j ≠ 0)
    (hide : quadraticOdeCleared68 H n d j) : False := by
  have hHne : H ≠ 0 := fun h0 => by simp [h0] at hH
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hc : H.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hHne
  have hHpos : 0 < H.natDegree := by simp [hH]
  have hHd : H.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hHpos)
  have hHddeg : H.derivative.natDegree = 1 := by
    simpa [hH] using natDegree_derivative_eq68 H hHpos
  have hHdlc : H.derivative.leadingCoeff =
      (2 : k) * H.leadingCoeff := by
    simpa [hH] using leadingCoeff_derivative_eq68 H hHpos
  have hd2ne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hC2j : C (2 : k) * C j ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr h2) (C_ne_zero.mpr hj)
  have hRHS : C (2 : k) * C j * d ^ 2 ≠ 0 :=
    mul_ne_zero hC2j hd2ne
  have hRHSdeg : (C (2 : k) * C j * d ^ 2).natDegree = 2 * d.natDegree := by
    rw [natDegree_mul hC2j hd2ne, natDegree_mul (C_ne_zero.mpr h2)
      (C_ne_zero.mpr hj), natDegree_C, natDegree_C, natDegree_pow (n := 2)]
    simp
  have hRHSlc : (C (2 : k) * C j * d ^ 2).leadingCoeff =
      (2 : k) * j * d.leadingCoeff ^ 2 := by
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C,
      leadingCoeff_pow]
    try ring
  by_cases hn0 : n = 0
  · have hLHS : C (2 : k) * H * wronskianPoly68 n d +
        n * H.derivative * d = 0 := by
      simp [wronskianPoly68, hn0]
    have : (0 : k[X]) = C (2 : k) * C j * d ^ 2 := by
      simpa [quadraticOdeCleared68, hLHS] using hide
    exact hRHS this.symm
  · set a := n.natDegree
    set b := d.natDegree
    have ha : n.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hn0
    have hb : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd
    by_cases heq : a = b
    · by_cases ha0 : a = 0
      · have hb0 : b = 0 := heq.symm.trans ha0
        have hn00 : n.natDegree = 0 := ha0
        have hd00 : d.natDegree = 0 := hb0
        have hW : wronskianPoly68 n d = 0 :=
          wronskianPoly68_zero_of_constants n d hn00 hd00
        have hnddeg : (n * H.derivative * d).natDegree = 1 := by
          rw [natDegree_mul (mul_ne_zero hn0 hHd) hd, natDegree_mul hn0 hHd,
            hn00, hHddeg, hd00]
        have hLHSdeg :
            (C (2 : k) * H * wronskianPoly68 n d +
              n * H.derivative * d).natDegree = 1 := by
          rw [hW, mul_zero, zero_add, hnddeg]
        have hdeq :
            (C (2 : k) * H * wronskianPoly68 n d +
              n * H.derivative * d).natDegree =
              (C (2 : k) * C j * d ^ 2).natDegree :=
          congrArg natDegree hide
        rw [hLHSdeg, hRHSdeg, hb0] at hdeq
        exact (Nat.succ_ne_zero 0 hdeq).elim
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        have hWle : (wronskianPoly68 n d).natDegree ≤ a + b - 2 :=
          wronskianPoly68_natDegree_le_of_eq n d hn0 hd heq hapos
        have hHWle : (C (2 : k) * H * wronskianPoly68 n d).natDegree ≤
            2 * a := by
          have hle : (C (2 : k) * H * wronskianPoly68 n d).natDegree ≤
              (C (2 : k) * H).natDegree + (wronskianPoly68 n d).natDegree :=
            natDegree_mul_le
          have hCH : (C (2 : k) * H).natDegree = 2 := by
            rw [natDegree_C_mul h2, hH]
          have hsum : (C (2 : k) * H).natDegree +
              (wronskianPoly68 n d).natDegree ≤ 2 + (a + b - 2) :=
            add_le_add (le_of_eq hCH) hWle
          have h2a : 2 + (a + b - 2) = 2 * a := by
            have : b = a := heq.symm
            omega
          exact hle.trans (hsum.trans (le_of_eq h2a))
        have hnddeg : (n * H.derivative * d).natDegree = 2 * a + 1 := by
          rw [natDegree_mul (mul_ne_zero hn0 hHd) hd, natDegree_mul hn0 hHd,
            hHddeg]
          have : b = a := heq.symm
          omega
        have hlt : (C (2 : k) * H * wronskianPoly68 n d).natDegree <
            (n * H.derivative * d).natDegree :=
          lt_of_le_of_lt hHWle (by omega)
        have hLHSdeg :
            (C (2 : k) * H * wronskianPoly68 n d +
              n * H.derivative * d).natDegree = 2 * a + 1 := by
          rw [add_comm, natDegree_add_eq_left_of_natDegree_lt hlt, hnddeg]
        have hdeq :
            (C (2 : k) * H * wronskianPoly68 n d +
              n * H.derivative * d).natDegree =
              (C (2 : k) * C j * d ^ 2).natDegree :=
          congrArg natDegree hide
        rw [hLHSdeg, hRHSdeg, heq.symm] at hdeq
        exact (Nat.succ_ne_self (2 * a) hdeq).elim
    · have hWdeg : (wronskianPoly68 n d).natDegree = a + b - 1 :=
        wronskianPoly68_natDegree_eq_of_ne n d hn0 hd heq
      have hWne : wronskianPoly68 n d ≠ 0 := by
        intro hW0
        have hcoeff := wronskianPoly68_coeff_top n d hn0 hd
        have h0 : (wronskianPoly68 n d).coeff
            (n.natDegree + d.natDegree - 1) = 0 := by
          simp [hW0]
        have hcast : (a : k) ≠ (b : k) :=
          (Nat.cast_injective (R := k)).ne heq
        have hsub : (a : k) - (b : k) ≠ 0 := sub_ne_zero.mpr hcast
        apply hsub
        have hprod := hcoeff.symm.trans h0
        rcases mul_eq_zero.mp hprod with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact h'
          · exact (ha h').elim
        · exact (hb h).elim
      have hWlc : (wronskianPoly68 n d).leadingCoeff =
          ((a : k) - (b : k)) * n.leadingCoeff * d.leadingCoeff :=
        wronskianPoly68_leadingCoeff_of_ne n d hn0 hd heq
      have hHWne : C (2 : k) * H * wronskianPoly68 n d ≠ 0 :=
        mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h2) hHne) hWne
      have hHWdeg : (C (2 : k) * H * wronskianPoly68 n d).natDegree =
          a + b + 1 := by
        rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr h2) hHne) hWne,
          natDegree_C_mul h2, hH, hWdeg]
        have : 2 + (a + b - 1) = a + b + 1 := by omega
        simpa [add_comm] using this
      have hHWlc : (C (2 : k) * H * wronskianPoly68 n d).leadingCoeff =
          (2 : k) * H.leadingCoeff * ((a : k) - (b : k)) *
            n.leadingCoeff * d.leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, hWlc]
        ring
      have hndne : n * H.derivative * d ≠ 0 :=
        mul_ne_zero (mul_ne_zero hn0 hHd) hd
      have hnddeg : (n * H.derivative * d).natDegree = a + b + 1 := by
        rw [natDegree_mul (mul_ne_zero hn0 hHd) hd, natDegree_mul hn0 hHd,
          hHddeg]
        omega
      have hndlc : (n * H.derivative * d).leadingCoeff =
          n.leadingCoeff * ((2 : k) * H.leadingCoeff) * d.leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_mul, hHdlc]
        try ring
      have htop :
          (C (2 : k) * H * wronskianPoly68 n d +
              n * H.derivative * d).coeff (a + b + 1) =
            (2 : k) * H.leadingCoeff * ((a : k) - (b : k) + 1) *
              n.leadingCoeff * d.leadingCoeff := by
        have h1 :
            (C (2 : k) * H * wronskianPoly68 n d).coeff (a + b + 1) =
              (C (2 : k) * H * wronskianPoly68 n d).leadingCoeff := by
          rw [← hHWdeg, coeff_natDegree]
        have h2c :
            (n * H.derivative * d).coeff (a + b + 1) =
              (n * H.derivative * d).leadingCoeff := by
          rw [← hnddeg, coeff_natDegree]
        rw [coeff_add, h1, h2c, hHWlc, hndlc]
        ring
      by_cases hshift : a + 1 = b
      · have hvan :
            (C (2 : k) * H * wronskianPoly68 n d +
                n * H.derivative * d).coeff (a + b + 1) = 0 := by
          have hab : (a : k) + 1 = (b : k) := by exact_mod_cast hshift
          have : (a : k) - (b : k) + 1 = 0 := by linear_combination hab
          simp [htop, this]
        have hdegab : a + b + 1 = 2 * b := by omega
        have hLHScoeff :
            (C (2 : k) * H * wronskianPoly68 n d +
                n * H.derivative * d).coeff (2 * b) = 0 := by
          simpa [hdegab] using hvan
        have hRHScoeff : (C (2 : k) * C j * d ^ 2).coeff (2 * b) ≠ 0 := by
          have hbdeg : 2 * b = 2 * d.natDegree := rfl
          rw [hbdeg, ← hRHSdeg, coeff_natDegree, hRHSlc]
          exact mul_ne_zero (mul_ne_zero h2 hj) (pow_ne_zero 2 hb)
        have hcoeff :
            (C (2 : k) * H * wronskianPoly68 n d +
                n * H.derivative * d).coeff (2 * b) =
              (C (2 : k) * C j * d ^ 2).coeff (2 * b) :=
          congrArg (fun p : k[X] => p.coeff (2 * b)) hide
        exact hRHScoeff (hcoeff.symm.trans hLHScoeff)
      · have hcomb : (a : k) - (b : k) + 1 ≠ 0 := by
          intro hz
          have hab : (a : k) + 1 = (b : k) := by linear_combination hz
          exact hshift (by exact_mod_cast hab)
        have htopne :
            (C (2 : k) * H * wronskianPoly68 n d +
                n * H.derivative * d).coeff (a + b + 1) ≠ 0 := by
          intro hz
          apply hcomb
          have hprod := htop.symm.trans hz
          rcases mul_eq_zero.mp hprod with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · rcases mul_eq_zero.mp h' with h'' | h''
              · rcases mul_eq_zero.mp h'' with h2' | hc'
                · exact (h2 h2').elim
                · exact (hc hc').elim
              · exact h''
            · exact (ha h').elim
          · exact (hb h).elim
        have hLHSdeg :
            (C (2 : k) * H * wronskianPoly68 n d +
                n * H.derivative * d).natDegree = a + b + 1 := by
          have hge := le_natDegree_of_ne_zero htopne
          have hle :=
            (natDegree_add_le (C (2 : k) * H * wronskianPoly68 n d)
              (n * H.derivative * d)).trans
              (max_le (le_of_eq hHWdeg) (le_of_eq hnddeg))
          exact le_antisymm hle hge
        have hdeq :
            (C (2 : k) * H * wronskianPoly68 n d +
              n * H.derivative * d).natDegree =
              (C (2 : k) * C j * d ^ 2).natDegree :=
          congrArg natDegree hide
        rw [hLHSdeg, hRHSdeg] at hdeq
        have : a + b + 1 = 2 * b := by
          simpa [show d.natDegree = b from rfl] using hdeq
        exact hshift (by omega)

end QuadraticOdePolynomial68

/-! ## Transport `d(Q · √H) = j / √H` into `k(x)` -/

section QuadraticOdeTransport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticOdeCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- The weight-13 primitive realises the rational ODE
`2 H Q' + Q H' = 2 j` on the odd descent `ρ = Q · √H`. -/
theorem degreeZeroPrimitive_ratFuncOde68
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (Q : RatFunc k)
    (hQ : S.degreeZeroPrimitive =
      algebraMap (RatFunc k) F68 Q *
        AdjoinRoot.root (alignedQuadraticPolynomial46 H)) :
    (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
        Differential.deriv Q +
      Q * algebraMap k[X] (RatFunc k) H.derivative =
      (2 : RatFunc k) * algebraMap k (RatFunc k) j := by
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hrt : rt ≠ 0 := alignedQuadraticRoot_ne_zero68 (H := H)
  have hφ : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hsq := alignedQuadraticRoot_sq46 H
  have hder := S.degreeZeroPrimitive_deriv (H := H)
  have hroot := quadraticDerivation46_root68 (H := H)
  have hQder := quadraticDerivation46_algebraMap_ratFunc68 H Q
  have hleibniz :
      quadraticDerivation46 H (algebraMap (RatFunc k) F68 Q * rt) =
        algebraMap (RatFunc k) F68 (Differential.deriv Q) * rt +
          algebraMap (RatFunc k) F68 Q *
            quadraticDerivation46 H rt := by
    have hmul := Derivation.leibniz (quadraticDerivation46 H)
      (algebraMap (RatFunc k) F68 Q) rt
    simp only [smul_eq_mul] at hmul
    rw [hmul, hQder]
    ring
  have hprim :
      quadraticDerivation46 H (algebraMap (RatFunc k) F68 Q * rt) =
        algebraMap k F68 j / rt := by
    rw [← hQ]
    exact hder
  have hsum :
      algebraMap (RatFunc k) F68 (Differential.deriv Q) * rt +
        algebraMap (RatFunc k) F68 Q *
          (algebraMap (RatFunc k) F68
            (algebraMap k[X] (RatFunc k) H.derivative) / (2 * rt)) =
        algebraMap k F68 j / rt := by
    have h := hleibniz.symm.trans hprim
    rw [hroot] at h
    exact h
  have h2ne : (2 : F68) ≠ 0 := two_ne_zero
  have h2rt : (2 : F68) * rt ≠ 0 := mul_ne_zero h2ne hrt
  have hcleared :
      (2 : F68) * algebraMap (RatFunc k) F68 (Differential.deriv Q) *
          (rt * rt) +
        algebraMap (RatFunc k) F68 Q *
          algebraMap (RatFunc k) F68
            (algebraMap k[X] (RatFunc k) H.derivative) =
        (2 : F68) * algebraMap k F68 j := by
    have := congrArg (fun z : F68 => (2 * rt) * z) hsum
    field_simp [h2ne, hrt, h2rt] at this
    linear_combination this
  have hleft :
      (2 : F68) * algebraMap (RatFunc k) F68 (Differential.deriv Q) *
          (rt * rt) +
        algebraMap (RatFunc k) F68 Q *
          algebraMap (RatFunc k) F68
            (algebraMap k[X] (RatFunc k) H.derivative) =
        algebraMap (RatFunc k) F68
          ((2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
            Differential.deriv Q +
            Q * algebraMap k[X] (RatFunc k) H.derivative) := by
    have hrt2 : rt * rt =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) H) := by
      simpa [pow_two] using hsq
    rw [hrt2]
    simp only [map_add, map_mul, map_ofNat]
    ring
  have hright :
      (2 : F68) * algebraMap k F68 j =
        algebraMap (RatFunc k) F68
          ((2 : RatFunc k) * algebraMap k (RatFunc k) j) := by
    rw [IsScalarTower.algebraMap_apply k (RatFunc k) F68, map_mul, map_ofNat]
  exact hφ (by rw [← hleft, hcleared, hright])

/-- Clearing the rational ODE on `Q = n/d` produces the polynomial
identity `2 H (n'd - nd') + n H' d = 2 j d²`. -/
theorem ratFuncOde_to_polynomial68
    (Q : RatFunc k) (j : k)
    (hode : (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
        Differential.deriv Q +
      Q * algebraMap k[X] (RatFunc k) H.derivative =
      (2 : RatFunc k) * algebraMap k (RatFunc k) j) :
    quadraticOdeCleared68 H Q.num Q.denom j := by
  have hd : Q.denom ≠ 0 := Q.denom_ne_zero
  have hdφ : algebraMap k[X] (RatFunc k) Q.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero hd
  have hQder : Differential.deriv Q =
      (algebraMap k[X] (RatFunc k) Q.denom *
          algebraMap k[X] (RatFunc k) Q.num.derivative -
        algebraMap k[X] (RatFunc k) Q.num *
          algebraMap k[X] (RatFunc k) Q.denom.derivative) /
        algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
    letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
    have h := congrArg Differential.deriv Q.num_div_denom.symm
    rw [Derivation.leibniz_div, GCD369RatFuncDerivative,
      GCD369RatFuncDerivative] at h
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have hW :
      algebraMap k[X] (RatFunc k) (wronskianPoly68 Q.num Q.denom) =
        Differential.deriv Q *
          algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
    rw [hQder]
    field_simp [hdφ]
    simp [wronskianPoly68, map_sub, map_mul, mul_comm]
  have hn :
      algebraMap k[X] (RatFunc k) Q.num =
        Q * algebraMap k[X] (RatFunc k) Q.denom := by
    have := mul_div_cancel₀ (algebraMap k[X] (RatFunc k) Q.num) hdφ
    rw [Q.num_div_denom] at this
    rw [mul_comm] at this
    exact this.symm
  have hmul :
      algebraMap k[X] (RatFunc k)
          (C (2 : k) * H * wronskianPoly68 Q.num Q.denom +
            Q.num * H.derivative * Q.denom) =
        algebraMap k[X] (RatFunc k)
          (C (2 : k) * C j * Q.denom ^ 2) := by
    have hleft :
        algebraMap k[X] (RatFunc k)
            (C (2 : k) * H * wronskianPoly68 Q.num Q.denom +
              Q.num * H.derivative * Q.denom) =
          ((2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
              Differential.deriv Q +
            Q * algebraMap k[X] (RatFunc k) H.derivative) *
            algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
      simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_C]
      rw [hW, hn]
      ring
    have hright :
        algebraMap k[X] (RatFunc k) (C (2 : k) * C j * Q.denom ^ 2) =
          ((2 : RatFunc k) * algebraMap k (RatFunc k) j) *
            algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
      simp only [map_mul, map_pow, map_ofNat, RatFunc.algebraMap_C]
      rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
      simp [RatFunc.algebraMap_C]
    rw [hleft, hode, hright]
  exact (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) hmul

/-- The odd descent of the weight-13 primitive yields a polynomial
solution of the cleared ODE. -/
theorem degreeZeroPrimitive_clearedOde68
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ n d : k[X], d ≠ 0 ∧ quadraticOdeCleared68 H n d j := by
  obtain ⟨Q, hQ⟩ := S.degreeZeroPrimitive_eq_mul_root (H := H)
  have hode := degreeZeroPrimitive_ratFuncOde68 (H := H) S Q hQ
  have hide := ratFuncOde_to_polynomial68 (H := H) Q _ hode
  exact ⟨Q.num, Q.denom, Q.denom_ne_zero, hide⟩

/-- Source-facing ODE kill on a quadratic nonsquare core. -/
theorem nonsquareAlignedQuadraticPacket_false
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hj : j ≠ 0) (hdeg : H.natDegree = 2) : False := by
  obtain ⟨n, d, hd, hide⟩ :=
    degreeZeroPrimitive_clearedOde68 (H := H) S
  exact quadraticCoreOde_no_polynomial_solution68 H n d j hdeg hd hj hide

end QuadraticOdeTransport68

/-! ## Packet, exclusion, and scale-two route -/

section AlignedNonsquareOdeClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Scale-two cores are quadratic. -/
theorem normalized68ScaleTwo_core_natDegree
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    H.natDegree = 2 :=
  hsource.2.1

/-- **CLOSED.** Source-facing ODE kill of a scale-two aligned-nonsquare
quadratic packet.  The named Prop quantifies over all nonsquare cores;
the scale-two chamber always supplies `H.natDegree = 2`. -/
theorem planeKeller68AlignedNonsquareQuadraticPacketExclusion_of_natDegree_two
    {H : k[X]} [NonsquarePolynomial46 H] {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hj : j ≠ 0) (hdeg : H.natDegree = 2) : False :=
  nonsquareAlignedQuadraticPacket_false (H := H) S hj hdeg

/-- **CLOSED.** The aligned nonsquare source chamber of the
normalized `(6,8)` scale-two route. -/
theorem planeKeller68AlignedNonsquareExclusion_closed :
    PlaneKeller68AlignedNonsquareExclusion (k := k) := by
  intro P Q H hsource hnsq haligned
  obtain ⟨j, hj, ⟨S⟩⟩ :=
    normalized68ScaleTwo_alignedNonsquare_quadraticSourceData
      hsource hnsq haligned
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  exact planeKeller68AlignedNonsquareQuadraticPacketExclusion_of_natDegree_two
    S hj (normalized68ScaleTwo_core_natDegree hsource)

/-- **CLOSED.** Normalized `(6,8)` scale-two route.  The aligned-square
local-root chamber is already closed; the aligned-nonsquare chamber is
the ODE kill above.  The unrestricted packet Prop
`PlaneKeller68AlignedNonsquareQuadraticPacketExclusion` is not used:
linear nonsquare cores admit a constant rational ODE solution, so that
quantification is strictly stronger than the scale-two chamber. -/
theorem planeKellerNormalized68ScaleTwoRoute_closed :
    PlaneKellerNormalized68ScaleTwoRoute (k := k) :=
  planeKellerNormalized68ScaleTwoRoute_of_alignedExclusion
    (planeKeller68AlignedScaleTwoExclusion_of_square_nonsquare
      planeKeller68AlignedSquareLocalRootExclusion_closed
      planeKeller68AlignedNonsquareExclusion_closed)

end AlignedNonsquareOdeClosure68

#print axioms quadraticCoreOde_no_polynomial_solution68
#print axioms degreeZeroPrimitive_ratFuncOde68
#print axioms ratFuncOde_to_polynomial68
#print axioms nonsquareAlignedQuadraticPacket_false
#print axioms planeKeller68AlignedNonsquareQuadraticPacketExclusion_of_natDegree_two
#print axioms planeKeller68AlignedNonsquareExclusion_closed
#print axioms planeKellerNormalized68ScaleTwoRoute_closed

end Max11DegreeRoutes
