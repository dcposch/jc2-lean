import Grok68TerminalTailThirdJetScratch
import LowScale68SecondaryResidualRowTwoSystem
import LowScale68SecondaryResidualRowOneSystem

/-! # Loaded row-two / row-one tops on the `(6,8)` terminal-tail residual

Untracked working note. No tracked file was edited.

Parent residual `FiveToSixTerminalTailOpenResidual68`: an aligned
beyond-wall cusp at `7n-2g+60k`, or the original at-wall large terminal
all-nonzero cusp.  The third-jet I4/I3 pair is a compatibility on the
same singular face matrix; closed neighbours died from the extra
row-two top `J=Q-3de` and row-one top `Y`, which do not meet the I4
face on this chamber.

CAS `derive_68_terminal_tail_row_two.py` computes the exact degrees at
the terminal offset `t` (`s=7n-2g+t`):
`Q` at `11n-3g`, `de` at `2g-3n-2t`, `Y` at
`max(12n-3g, 2g-2n-2t)`, I4 face at `2n-t`.  The comparison
`5g ? 14n+2t` splits `Q` vs `de` and the two `Y` groups together.

* `5g < 14n+2t` (`Q`-higher): loaded row two at `11n-3g-1` is `Q`.
  On the cusp `3Q+(1/3)b·cusp=4bc²`, so `c=0`.
* `5g > 14n+2t` (`de`-higher): the same row is `-3de`, contradicting
  the cusp edge.
* `5g=14n+2t` and `g<3n`: `Q` meets `de` and both `Y` groups meet.
  Loaded row two kills `J` and loaded row one kills `Y`; together with
  the I4 face this is the neighbour `e⁴` certificate.
* `g=3n` (constant `B`): I4 forces `Fc` constant.  The I3 coefficient
  at `deg c=n` (where `B²c` and `d²` attain) eliminates `epsilon`;
  `Q`-higher still yields `4bc²=0`, and the meeting cell yields the
  same `e⁴` after that I3 jet.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

This file records the chamber Groebner, the I4/I3 faces at every
`t ≥ 0`, the compensated `Fc` identity, the row-two `J` factorisation
with `γ A d'` absorption, `alpha`/`eta` cancellation in loaded row two,
the `H`-support extra degree, and the leading `Q`/`de`/`Y`
coefficients.  It does not yet assemble those identities into
`fiveToSix_terminalTail_impossible68`.

Exact gain: terminal-tail `J`/`Y` scalar certificates (including the
constant-`B` I3-at-`deg c` variants); I4/I3 faces at `t ≥ 0`; `Fc`;
row-two core/`J` factor; loaded row-two `alpha`/`eta` cancellation.
Next unused row: assemble the coefficient comparison at
`max(11n-3g, 2g-3n-2t)-1` (and `Y` at its top on the meeting cell)
into `fiveToSix_terminalTail_impossible68`; fourth-jet I4/I3 at
`9n-2g-s-180` / `10n-2g-s-180` remains unused.
Residual: `FiveToSixTerminalTailOpenResidual68` (both cusps remain).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalTailRowTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Scalar leading-jet identities -/

/-- `Q` and the cusp cannot vanish together. -/
theorem fiveToSix_terminalTail_Q_cusp_false68
    (a b c : k) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hQ : b * c ^ 2 - (1 / 9 : k) * a * b ^ 3 = 0) :
    False := by
  have h4 : (4 : k) * (b * c ^ 2) = 0 := by
    linear_combination (3 : k) * hQ + (1 / 3 : k) * b * hcusp
  have hbc : b * c ^ 2 = 0 :=
    (mul_eq_zero.mp h4).resolve_left (by norm_num : (4 : k) ≠ 0)
  exact hc (eq_zero_of_pow_eq_zero
    ((mul_eq_zero.mp hbc).resolve_left hb))

/-- The four leading coefficients of the cusp, of `Be+cd`, of
`Q-3de`, and of `Y` cannot vanish together.  Same multipliers as
`Grok68B3EqualityWallPacketsFalseScratch`. -/
theorem fiveToSix_terminalTail_leading_jet_false68
    (a b c d e : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hH : b * e + c * d = 0)
    (hJ : b * c ^ 2 - (1 / 9 : k) * a * b ^ 3 - (3 : k) * d * e = 0)
    (hY : -(2 : k) * a * b ^ 2 * c + (3 : k) * a * d ^ 2 +
        (2 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0) :
    False := by
  have hJred : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0 := by
    linear_combination (3 : k) * hJ + (1 / 3 : k) * b * hcusp
  have hYred : (3 : k) * a * d ^ 2 + (8 : k) * c ^ 3 -
      (9 : k) * e ^ 2 = 0 := by
    linear_combination hY + (2 : k) * c * hcusp
  have hce : (4 : k) * c ^ 3 + (9 : k) * e ^ 2 = 0 := by
    have hprod : d * ((4 : k) * c ^ 3 + (9 : k) * e ^ 2) = 0 := by
      linear_combination (4 : k) * c ^ 2 * hH - e * hJred
    exact (mul_eq_zero.mp hprod).resolve_left hd
  have hsq : b ^ 2 * e ^ 2 = c ^ 2 * d ^ 2 := by
    calc
      b ^ 2 * e ^ 2 = (b * e) ^ 2 := by ring
      _ = (-(c * d)) ^ 2 := by rw [add_eq_zero_iff_eq_neg.mp hH]
      _ = (c * d) ^ 2 := by ring
      _ = c ^ 2 * d ^ 2 := by ring
  have had : a * d ^ 2 + (3 : k) * e ^ 2 = 0 := by
    have hprod :
        c ^ 2 * d ^ 2 * (a * d ^ 2 + (3 : k) * e ^ 2) = 0 := by
      calc
        c ^ 2 * d ^ 2 * (a * d ^ 2 + (3 : k) * e ^ 2) =
            a * d ^ 2 * (c ^ 2 * d ^ 2) +
              (3 : k) * c ^ 2 * d ^ 2 * e ^ 2 := by ring
        _ = a * d ^ 2 * (b ^ 2 * e ^ 2) +
              (3 : k) * c ^ 2 * d ^ 2 * e ^ 2 := by rw [hsq]
        _ = (a * b ^ 2 + (3 : k) * c ^ 2) * d ^ 2 * e ^ 2 := by ring
        _ = 0 := by rw [hcusp, zero_mul, zero_mul]
    have hcd2 : c ^ 2 * d ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hd)
    exact (mul_eq_zero.mp hprod).resolve_left hcd2
  have hce' : (4 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0 := by
    have h8 : (8 : k) * c ^ 3 - (18 : k) * e ^ 2 = 0 := by
      linear_combination hYred - (3 : k) * had
    linear_combination (1 / 2 : k) * h8
  have he2 : (18 : k) * e ^ 2 = 0 := by
    linear_combination hce - hce'
  have h18 : (18 : k) ≠ 0 := by norm_num
  have hz : e ^ 2 = 0 := (mul_eq_zero.mp he2).resolve_left h18
  exact he (eq_zero_of_pow_eq_zero hz)

/-- Constant-`B` meeting cell: I3 at `deg c`, the mixed `J` (with
`epsilon`), and `Y` force `d=0`. -/
theorem fiveToSix_terminalTail_constantB_meeting_false68
    (a b c d e eps : k)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hH : b * e + c * d = 0)
    (hI3 : -(8 / 9 : k) * b ^ 2 * c + (4 / 3 : k) * d ^ 2 +
        (2 : k) * eps * c = 0)
    (hJ : (8 : k) * b * c ^ 2 - (4 / 3 : k) * a * b ^ 3 -
        (24 : k) * d * e + (3 : k) * a * b * eps = 0)
    (hY : -(2 : k) * a * b ^ 2 * c + (3 : k) * a * d ^ 2 +
        (2 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0) :
    False := by
  have hYred : (3 : k) * a * d ^ 2 + (8 : k) * c ^ 3 -
      (9 : k) * e ^ 2 = 0 := by
    linear_combination hY + (2 : k) * c * hcusp
  have hsq : b * e = -(c * d) := add_eq_zero_iff_eq_neg.mp hH
  have hcusp' : a * b ^ 2 = -((3 : k) * c ^ 2) :=
    add_eq_zero_iff_eq_neg.mp hcusp
  have hJc : (8 : k) * b * c ^ 3 - (4 / 3 : k) * a * b ^ 3 * c -
      (24 : k) * c * d * e + (3 : k) * a * b * eps * c = 0 := by
    linear_combination c * hJ
  have hI3c : (3 : k) * a * b * eps * c =
      (4 / 3 : k) * a * b ^ 3 * c - (2 : k) * a * b * d ^ 2 := by
    linear_combination (3 / 2 : k) * a * b * hI3
  have hred : (8 : k) * b * c ^ 3 - (24 : k) * c * d * e -
      (2 : k) * a * b * d ^ 2 = 0 := by
    linear_combination hJc - hI3c
  have hred' : a * b * d ^ 2 + (12 : k) * c * d * e -
      (4 : k) * b * c ^ 3 = 0 := by
    linear_combination (-1 / 2 : k) * hred
  have hce : (12 : k) * c * d * (b * e) =
      -((12 : k) * c ^ 2 * d ^ 2) := by
    rw [hsq]
    ring
  have hredb : a * b ^ 2 * d ^ 2 - (12 : k) * c ^ 2 * d ^ 2 -
      (4 : k) * b ^ 2 * c ^ 3 = 0 := by
    linear_combination b * hred' - hce
  have hc2 : (15 : k) * c ^ 2 * d ^ 2 + (4 : k) * b ^ 2 * c ^ 3 = 0 := by
    have h := hredb
    rw [hcusp'] at h
    linear_combination -h
  have h15 : (15 : k) * d ^ 2 + (4 : k) * b ^ 2 * c = 0 := by
    have hprod : c ^ 2 * ((15 : k) * d ^ 2 + (4 : k) * b ^ 2 * c) = 0 := by
      linear_combination hc2
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hc)
  have he2 : e ^ 2 * b ^ 2 = c ^ 2 * d ^ 2 := by
    calc
      e ^ 2 * b ^ 2 = (b * e) ^ 2 := by ring
      _ = (-(c * d)) ^ 2 := by rw [hsq]
      _ = (c * d) ^ 2 := by ring
      _ = c ^ 2 * d ^ 2 := by ring
  have hYb : (3 : k) * a * d ^ 2 * b ^ 2 + (8 : k) * c ^ 3 * b ^ 2 -
      (9 : k) * c ^ 2 * d ^ 2 = 0 := by
    linear_combination b ^ 2 * hYred + (9 : k) * he2
  have hYb' : (3 : k) * (a * b ^ 2) * d ^ 2 + (8 : k) * b ^ 2 * c ^ 3 -
      (9 : k) * c ^ 2 * d ^ 2 = 0 := by
    convert hYb using 1
    ring
  have hYc : (8 : k) * b ^ 2 * c ^ 3 - (18 : k) * c ^ 2 * d ^ 2 = 0 := by
    rw [hcusp'] at hYb'
    linear_combination hYb'
  have h49 : (4 : k) * b ^ 2 * c - (9 : k) * d ^ 2 = 0 := by
    have hprod : (2 : k) *
        (c ^ 2 * ((4 : k) * b ^ 2 * c - (9 : k) * d ^ 2)) = 0 := by
      linear_combination hYc
    have hinner : c ^ 2 * ((4 : k) * b ^ 2 * c - (9 : k) * d ^ 2) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (by norm_num : (2 : k) ≠ 0)
    exact (mul_eq_zero.mp hinner).resolve_left (pow_ne_zero 2 hc)
  have hd2 : (24 : k) * d ^ 2 = 0 := by
    linear_combination h15 - h49
  have h24 : (24 : k) ≠ 0 := by norm_num
  exact hd (eq_zero_of_pow_eq_zero
    ((mul_eq_zero.mp hd2).resolve_left h24))

/-- Constant-`B` `Q`-higher cell: I3 at `deg c` (no `d²`) and the mixed
`Q` (no `de`) force `c=0`. -/
theorem fiveToSix_terminalTail_constantB_Qhigher_false68
    (a b c eps : k) (hb : b ≠ 0) (hc : c ≠ 0)
    (hI3 : -(8 / 9 : k) * b ^ 2 * c + (2 : k) * eps * c = 0)
    (hJ : (8 : k) * b * c ^ 2 - (4 / 3 : k) * a * b ^ 3 +
        (3 : k) * a * b * eps = 0) :
    False := by
  have hI3' : -(8 / 9 : k) * b ^ 2 + (2 : k) * eps = 0 := by
    have hprod : c * (-(8 / 9 : k) * b ^ 2 + (2 : k) * eps) = 0 := by
      linear_combination hI3
    exact (mul_eq_zero.mp hprod).resolve_left hc
  have hJc : (8 : k) * b * c ^ 3 - (4 / 3 : k) * a * b ^ 3 * c +
      (3 : k) * a * b * eps * c = 0 := by
    linear_combination c * hJ
  have h8 : (8 : k) * (b * c ^ 3) = 0 := by
    linear_combination hJc - (3 / 2 : k) * a * b * c * hI3'
  have hbc : b * c ^ 3 = 0 :=
    (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : k) ≠ 0)
  exact hc (eq_zero_of_pow_eq_zero
    ((mul_eq_zero.mp hbc).resolve_left hb))

/-! ## I4 / I3 faces at an arbitrary offset `t ≥ 0` -/

theorem secondaryResidualInvariantFourPolynomial68_coeff_terminalTail68
    (B c d e : k[X]) (n g t : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (2 * n - t) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n - t) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hB3 : (B ^ 3).natDegree < 2 * n - t := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (g - n - t) hB he
  have hBei : (3 * n - g) + (g - n - t) = 2 * n - t := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (g - 2 * n - t) hc hd
  have hcdi : (4 * n - g) + (g - 2 * n - t) = 2 * n - t := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

theorem secondaryResidualInvariantThreePolynomial68_coeff_terminalTail68
    (A B c d e : k[X]) (n g t : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (3 * n - t) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n - t)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n) (3 * n - g)
    (g - 2 * n - t) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (g - 2 * n - t) = 3 * n - t := by
    omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 3 * n - t := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (g - n - t) hc he
  have hcei : (4 * n - g) + (g - n - t) = 3 * n - t := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 3 * n - t := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

theorem cubicFirstIntegralFourPolynomial68_coeff_terminalTail68
    (gamma epsilon : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (2 * n - t) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n - t) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hloadB : ((2 * epsilon : k) • B).natDegree < 2 * n - t := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 2 * n - t := by
    compute_degree
    omega
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  rw [coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_terminalTail68
      B c d e n g t hn ⟨hw5, hw6⟩ htle hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

theorem cubicFirstIntegralThreePolynomial68_coeff_terminalTail68
    (gamma epsilon : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (3 * n - t) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n - t)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n - t)) := by
  obtain ⟨hw5, hw6⟩ := hwindow
  have hloadc : ((2 * epsilon : k) • c).natDegree < 3 * n - t := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < 3 * n - t := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 3 * n - t := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  rw [coeff_sub, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_terminalTail68
      A B c d e n g t hn ⟨hw5, hw6⟩ htle hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

theorem fiveToSix_terminalTail_H_face68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (n g t : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    B.coeff (3 * n - g) * e.coeff (g - n - t) +
      c.coeff (4 * n - g) * d.coeff (g - 2 * n - t) = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (2 * n - t)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_terminalTail68
    gamma epsilon A B c d e n g t hn hwindow htle hB hc hd he] at hz
  have hj : 2 * n - t ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hj] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-! ## Compensated I4 remainder `Fc` -/

/-- `I4 = (8/3) F + 2ε B + 4γ d` with `F = Be+cd-(1/9)B³`. -/
theorem fiveToSix_terminalTail_I4_F_identity68
    (gamma epsilon : k) (A B c d e : k[X]) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e =
      (8 / 3 : k) • F + (2 * epsilon : k) • B + (4 * gamma : k) • d := by
  intro F
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero, secondaryResidualInvariantFourPolynomial68]
  dsimp only [F]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

theorem fiveToSix_terminalTail_Fc_of_I4_constant68
    (gamma epsilon i4 : k) (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    Fc = (3 / 8 : k) • C i4 - (3 / 4 * epsilon : k) • B := by
  intro F Fc
  have hid := fiveToSix_terminalTail_I4_F_identity68 gamma epsilon A B c d e
  have hF : (8 / 3 : k) • F + (2 * epsilon : k) • B +
      (4 * gamma : k) • d = C i4 := by
    simpa [F] using hid.symm.trans hi4
  have hlin : (8 / 3 : k) • Fc = (8 / 3 : k) • F + (4 * gamma : k) • d := by
    dsimp only [Fc]
    module
  have hFc : (8 / 3 : k) • Fc = C i4 - (2 * epsilon : k) • B := by
    linear_combination hlin + hF
  have hscale : Fc = (3 / 8 : k) • ((8 / 3 : k) • Fc) := by
    module
  rw [hscale, hFc]
  module

theorem fiveToSix_terminalTail_Fc_natDegree68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (n g : ℕ)
    (hB : B.natDegree ≤ 3 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    Fc.natDegree ≤ 3 * n - g := by
  intro F Fc
  have h := fiveToSix_terminalTail_Fc_of_I4_constant68 gamma epsilon i4
    A B c d e hi4
  dsimp only [F, Fc] at h ⊢
  rw [h]
  compute_degree
  omega

/-! ## Row-two core and `J` factorisation -/

/-- Residual row-two inner polynomial without the `H`-support extra
`6 B² d'+12 B B' d`. -/
def FiveToSixTerminalTailRowTwoCore68 (A B c d e : k[X]) : k[X] :=
  -(6 : k) • (A * B * derivative e) -
    (6 : k) • (A * derivative B * e) -
    (6 : k) • (A * c * derivative d) -
    (6 : k) • (A * derivative c * d) -
    derivative A * B ^ 3 +
    (3 : k) • (derivative A * B * e) +
    (3 : k) • (derivative A * c * d) +
    (12 : k) • (B * c * derivative c) +
    (6 : k) • (derivative B * c ^ 2) -
    (18 : k) • (d * derivative e) -
    (18 : k) • (derivative d * e)

def FiveToSixTerminalTailRowTwoExtra68 (A B c d e : k[X]) : k[X] :=
  (6 : k) • (B ^ 2 * derivative d) +
    (12 : k) • (B * derivative B * d)

theorem secondaryResidualRowTwoPolynomial68_terminalTail_core_extra68
    (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) •
        (FiveToSixTerminalTailRowTwoCore68 A B c d e +
          FiveToSixTerminalTailRowTwoExtra68 A B c d e) := by
  unfold secondaryResidualRowTwoPolynomial68
    FiveToSixTerminalTailRowTwoCore68
    FiveToSixTerminalTailRowTwoExtra68
  congr 1
  module

theorem fiveToSix_terminalTail_rowTwo_core_factor_raw68 (A B c d e : k[X]) :
    FiveToSixTerminalTailRowTwoCore68 A B c d e =
      -(6 : k) • (A * derivative (B * e + c * d)) +
        (3 : k) • (derivative A * (B * e + c * d)) -
        derivative A * B ^ 3 +
        (6 : k) • derivative (B * c ^ 2) -
        (18 : k) • derivative (d * e) := by
  have hcSq : derivative (c ^ 2) = (2 : k) • (c * derivative c) := by
    rw [show c ^ 2 = c * c by ring, derivative_mul,
      show derivative c * c = c * derivative c by ring]
    module
  have hc2 : derivative (B * c ^ 2) =
      (2 : k) • (B * c * derivative c) + derivative B * c ^ 2 := by
    rw [derivative_mul, hcSq]
    simp only [mul_smul_comm, mul_assoc]
    module
  rw [hc2]
  simp only [FiveToSixTerminalTailRowTwoCore68, derivative_add,
    derivative_mul, mul_add, add_mul, mul_assoc]
  module

theorem fiveToSix_terminalTail_rowTwo_core_factor68 (A B c d e : k[X]) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    FiveToSixTerminalTailRowTwoCore68 A B c d e =
      -(6 : k) • (A * derivative F) + (3 : k) • (derivative A * F) +
        (6 : k) • derivative J := by
  intro F J
  have hraw := fiveToSix_terminalTail_rowTwo_core_factor_raw68 A B c d e
  dsimp only [F, J]
  rw [hraw]
  simp only [derivative_sub, derivative_smul, derivative_mul, mul_sub,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add,
    smul_smul, mul_assoc]
  module

theorem fiveToSix_terminalTail_rowTwo_load_factor68
    (gamma : k) (A B c d e : k[X]) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    FiveToSixTerminalTailRowTwoCore68 A B c d e -
        (9 * gamma : k) • (A * derivative d) +
        (9 / 2 * gamma : k) • (d * derivative A) =
      -(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
        (6 : k) • derivative J := by
  intro F Fc J
  have hbase :
      FiveToSixTerminalTailRowTwoCore68 A B c d e =
        -(6 : k) • (A * derivative F) + (3 : k) • (derivative A * F) +
          (6 : k) • derivative J := by
    simpa [F, J] using
      fiveToSix_terminalTail_rowTwo_core_factor68 A B c d e
  rw [hbase]
  dsimp only [Fc]
  simp only [derivative_add, derivative_smul, mul_add, mul_smul_comm,
    smul_mul_assoc, smul_add, smul_sub, smul_smul]
  rw [show d * derivative A = derivative A * d by ring]
  module

theorem fiveToSix_terminalTail_rowTwo_cancelled68
    (gamma : k) (A B c d e : k[X]) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    let Extra := FiveToSixTerminalTailRowTwoExtra68 A B c d e
    secondaryResidualRowTwoPolynomial68 A B c d e +
        (4 / 3 * gamma : k) • (A * derivative d) -
        (2 / 3 * gamma : k) • (d * derivative A) =
      (-4 / 27 : k) •
        (-(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
          (6 : k) • derivative J + Extra) := by
  intro F Fc J Extra
  have hcore :=
    secondaryResidualRowTwoPolynomial68_terminalTail_core_extra68 A B c d e
  have hfactor :=
    fiveToSix_terminalTail_rowTwo_load_factor68 gamma A B c d e
  have hC :
      FiveToSixTerminalTailRowTwoCore68 A B c d e =
        -(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
          (6 : k) • derivative J +
          (9 * gamma : k) • (A * derivative d) -
          (9 / 2 * gamma : k) • (d * derivative A) := by
    linear_combination hfactor
  rw [hcore, hC]
  dsimp only [Extra]
  module

/-! ## Load remainder after the `γ A d'` absorption -/

theorem cubicLoadRowTwoPolynomial68_alpha_cancel68
    (alpha : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 0 0 0
        A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  have hS : cubicLoadSPolynomial68 0 alpha 0 0 A B c = alpha • B := by
    simp [cubicLoadSPolynomial68]
  have hT : cubicLoadTPolynomial68 0 alpha 0 0 0 A B c D0 = alpha • C0 := by
    simp [cubicLoadTPolynomial68, C0]
    module
  have hU : cubicLoadUPolynomial68 0 alpha 0 0 0 0 A B c D0 e =
      alpha • D0 := by
    simp [cubicLoadUPolynomial68]
  have hV : cubicLoadVPolynomial68 0 alpha 0 0 0 0 0 A B c D0 e =
      alpha • E0 := by
    simp [cubicLoadVPolynomial68, E0]
    module
  have hform :
      cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 0 0 0 A B c D0 e =
        (alpha • D0) * derivative C0 +
          (2 : k) • ((alpha • C0) * derivative D0) +
          (3 : k) • ((alpha • B) * derivative E0) -
          (3 : k) • (B * derivative (alpha • E0)) -
          (2 : k) • (C0 * derivative (alpha • D0)) -
          D0 * derivative (alpha • C0) := by
    unfold cubicLoadRowTwoPolynomial68
    rw [hS, hT, hU, hV]
  rw [hform]
  simp only [derivative_smul, Polynomial.smul_eq_C_mul, derivative_mul,
    derivative_C, mul_zero, add_zero, zero_add, zero_mul]
  ring

theorem cubicLoadRowTwoPolynomial68_eta_cancel68
    (eta : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  have hS : cubicLoadSPolynomial68 0 0 0 0 A B c = 0 := by
    simp [cubicLoadSPolynomial68]
  have hT : cubicLoadTPolynomial68 0 0 0 0 0 A B c
      ((1 / 3 : k) • (A * B) + d) = C 0 := by
    simp [cubicLoadTPolynomial68]
  have hU : cubicLoadUPolynomial68 0 0 0 0 0 0 A B c
      ((1 / 3 : k) • (A * B) + d) e = 0 := by
    simp [cubicLoadUPolynomial68]
  have hV : cubicLoadVPolynomial68 0 0 0 0 0 0 eta A B c
      ((1 / 3 : k) • (A * B) + d) e = C eta := by
    simp [cubicLoadVPolynomial68]
  unfold cubicLoadRowTwoPolynomial68
  rw [hS, hT, hU, hV]
  simp only [derivative_C, derivative_zero, mul_zero, smul_zero, zero_mul,
    add_zero, sub_zero, C_0]

theorem fiveToSix_terminalTail_Extra_natDegree68
    (A B c d e : k[X]) (n g t : ℕ)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t) :
    (FiveToSixTerminalTailRowTwoExtra68 A B c d e).natDegree ≤
      2 * (3 * n - g) + (g - 2 * n - t) := by
  unfold FiveToSixTerminalTailRowTwoExtra68
  have hB2 : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    have h := (natDegree_pow (p := B) (n := 2)).le
    have : 2 * B.natDegree ≤ 2 * (3 * n - g) :=
      Nat.mul_le_mul_left 2 hB
    omega
  have hd' : (derivative d).natDegree ≤ g - 2 * n - t := by
    have := natDegree_derivative_le d
    omega
  have h1 : (B ^ 2 * derivative d).natDegree ≤
      2 * (3 * n - g) + (g - 2 * n - t) :=
    (natDegree_mul_le).trans (Nat.add_le_add hB2 hd')
  have hBder : (derivative B).natDegree ≤ 3 * n - g := by
    have := natDegree_derivative_le B
    omega
  have hBdB : (B * derivative B).natDegree ≤ 2 * (3 * n - g) :=
    (natDegree_mul_le).trans (by
      have := Nat.add_le_add hB hBder
      omega)
  have h2 : (B * derivative B * d).natDegree ≤
      2 * (3 * n - g) + (g - 2 * n - t) :=
    (natDegree_mul_le).trans (Nat.add_le_add hBdB hd)
  have hsm1 : ((6 : k) • (B ^ 2 * derivative d)).natDegree ≤
      2 * (3 * n - g) + (g - 2 * n - t) :=
    (natDegree_smul_le _ _).trans h1
  have hsm2 : ((12 : k) • (B * derivative B * d)).natDegree ≤
      2 * (3 * n - g) + (g - 2 * n - t) :=
    (natDegree_smul_le _ _).trans h2
  exact (natDegree_add_le _ _).trans (Nat.max_le.mpr ⟨hsm1, hsm2⟩)

/-! ## Homogeneous `J` coefficient at a strict top -/

theorem fiveToSix_terminalTail_J_coeff_of_rowTwo_top68
    (A B c d e : k[X]) (idx : ℕ) (hidx : 0 < idx)
    (hJ : ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
        (3 : k) • (d * e)).natDegree ≤ idx)
    (hbelow : ∀ p : k[X], p.natDegree < idx → p.coeff (idx - 1) = 0)
    (hrow : (derivative ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
        (3 : k) • (d * e))).coeff (idx - 1) = 0) :
    ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) -
        (3 : k) • (d * e)).coeff idx = 0 := by
  have hder := coeff_derivative_at_bound68
    ((B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)) idx hidx
  have hcast : (idx : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hder] at hrow
  exact (mul_eq_zero.mp hrow).resolve_right hcast

/-! ## Source-facing extraction -/

/-- Expanded residual row two from the integrated system. -/
theorem fiveToSix_terminalTail_expanded_rowTwo68
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
    let d := secondaryDDefectPolynomial68 Ae Be De
    secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
  intro n Ae Be Ce ce De Ee ee d
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hrowTwoe : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hr := hrowTwoe
  rw [hCrec, hDrec, hErec] at hr
  exact polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hr

theorem fiveToSix_terminalTail_expanded_rowOne68
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
    let d := secondaryDDefectPolynomial68 Ae Be De
    secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
  intro n Ae Be Ce ce De Ee ee d
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hrowOnee : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hr := hrowOnee
  rw [hCrec, hDrec, hErec] at hr
  exact polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hr

/-! ## Polynomial-level contradiction on a cusp edge -/

/-- Auxiliary: leading coefficient of `Q` at `11n-3g`. -/
theorem fiveToSix_terminalTail_Q_coeff68
    (A B c : k[X]) (n g : ℕ)
    (hg : g ≤ 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)).coeff (11 * n - 3 * g) =
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (1 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  have hg4 : g ≤ 4 * n := by omega
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    have h := (natDegree_pow (p := c) (n := 2)).le
    have : 2 * c.natDegree ≤ 2 * (4 * n - g) :=
      Nat.mul_le_mul_left 2 hc
    omega
  have hc2top : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hBc2 := coeff_mul_at_bounds68 B (c ^ 2) (3 * n - g)
    (2 * (4 * n - g)) hB hc2deg
  have hsum1 : (3 * n - g) + 2 * (4 * n - g) = 11 * n - 3 * g := by omega
  rw [hsum1, hc2top] at hBc2
  have hB3deg : (B ^ 3).natDegree ≤ 3 * (3 * n - g) := by
    have h := (natDegree_pow (p := B) (n := 3)).le
    have : 3 * B.natDegree ≤ 3 * (3 * n - g) :=
      Nat.mul_le_mul_left 3 hB
    omega
  have hB3top : (B ^ 3).coeff (3 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 3 :=
    coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hAB3 := coeff_mul_at_bounds68 A (B ^ 3) (2 * n)
    (3 * (3 * n - g)) hA hB3deg
  have hsum2 : 2 * n + 3 * (3 * n - g) = 11 * n - 3 * g := by omega
  rw [hsum2, hB3top] at hAB3
  simp only [coeff_sub, coeff_smul, smul_eq_mul, hBc2, hAB3]
  ring

/-- Auxiliary: leading coefficient of `de` at `2g-3n-2t`. -/
theorem fiveToSix_terminalTail_de_coeff68
    (d e : k[X]) (n g t : ℕ)
    (htle : 2 * n + t ≤ g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    (d * e).coeff (2 * g - 3 * n - 2 * t) =
      d.coeff (g - 2 * n - t) * e.coeff (g - n - t) := by
  have h := coeff_mul_at_bounds68 d e (g - 2 * n - t) (g - n - t) hd he
  have hsum : (g - 2 * n - t) + (g - n - t) = 2 * g - 3 * n - 2 * t := by
    omega
  rwa [hsum] at h

/-- Auxiliary: leading coefficient of `Y` when all four edges meet. -/
theorem fiveToSix_terminalTail_Y_coeff_meeting68
    (A B c d e : k[X]) (n g t : ℕ)
    (hmeet : 5 * g = 14 * n + 2 * t)
    (hg : g ≤ 3 * n) (htle : 2 * n + t ≤ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (he : e.natDegree ≤ g - n - t) :
    let TY := 12 * n - 3 * g
    (-(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
        (2 : k) • c ^ 3 - (9 : k) • e ^ 2).coeff TY =
      -(2 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g) +
        (3 : k) * A.coeff (2 * n) * d.coeff (g - 2 * n - t) ^ 2 +
        (2 : k) * c.coeff (4 * n - g) ^ 3 -
        (9 : k) * e.coeff (g - n - t) ^ 2 := by
  intro TY
  have hTY : TY = 2 * g - 2 * n - 2 * t := by
    dsimp only [TY]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    have h := (natDegree_pow (p := B) (n := 2)).le
    have : 2 * B.natDegree ≤ 2 * (3 * n - g) :=
      Nat.mul_le_mul_left 2 hB
    omega
  have hB2top : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c :=
    coeff_mul_mul_at_bounds68 A (B ^ 2) c (2 * n) (2 * (3 * n - g))
      (4 * n - g) hA hB2deg hc
  have hsum1 : 2 * n + 2 * (3 * n - g) + (4 * n - g) = TY := by
    dsimp only [TY]; omega
  rw [hsum1, hB2top] at hAB2c
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (g - 2 * n - t) := by
    have h := (natDegree_pow (p := d) (n := 2)).le
    have : 2 * d.natDegree ≤ 2 * (g - 2 * n - t) :=
      Nat.mul_le_mul_left 2 hd
    omega
  have hd2top : (d ^ 2).coeff (2 * (g - 2 * n - t)) =
      d.coeff (g - 2 * n - t) ^ 2 :=
    coeff_pow_at_bound68 d (g - 2 * n - t) 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2) (2 * n)
    (2 * (g - 2 * n - t)) hA hd2deg
  have hsum2 : 2 * n + 2 * (g - 2 * n - t) = TY := by
    dsimp only [TY]; omega
  rw [hsum2, hd2top] at hAd2
  have hc3top : (c ^ 3).coeff (3 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 3 :=
    coeff_pow_at_bound68 c (4 * n - g) 3 hc
  have hsum3 : 3 * (4 * n - g) = TY := by dsimp only [TY]; omega
  rw [hsum3] at hc3top
  have he2deg : (e ^ 2).natDegree ≤ 2 * (g - n - t) := by
    have h := (natDegree_pow (p := e) (n := 2)).le
    have : 2 * e.natDegree ≤ 2 * (g - n - t) :=
      Nat.mul_le_mul_left 2 he
    omega
  have he2top : (e ^ 2).coeff (2 * (g - n - t)) =
      e.coeff (g - n - t) ^ 2 :=
    coeff_pow_at_bound68 e (g - n - t) 2 he
  have hsum4 : 2 * (g - n - t) = TY := by dsimp only [TY]; omega
  rw [hsum4] at he2top
  simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul,
    hAB2c, hAd2, hc3top, he2top]
  ring

#print axioms fiveToSix_terminalTail_Q_cusp_false68
#print axioms fiveToSix_terminalTail_leading_jet_false68
#print axioms fiveToSix_terminalTail_constantB_meeting_false68
#print axioms fiveToSix_terminalTail_constantB_Qhigher_false68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_terminalTail68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_terminalTail68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_terminalTail68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_terminalTail68
#print axioms fiveToSix_terminalTail_H_face68
#print axioms fiveToSix_terminalTail_I4_F_identity68
#print axioms fiveToSix_terminalTail_Fc_of_I4_constant68
#print axioms fiveToSix_terminalTail_Fc_natDegree68
#print axioms secondaryResidualRowTwoPolynomial68_terminalTail_core_extra68
#print axioms fiveToSix_terminalTail_rowTwo_core_factor_raw68
#print axioms fiveToSix_terminalTail_rowTwo_core_factor68
#print axioms fiveToSix_terminalTail_rowTwo_load_factor68
#print axioms fiveToSix_terminalTail_rowTwo_cancelled68
#print axioms cubicLoadRowTwoPolynomial68_alpha_cancel68
#print axioms cubicLoadRowTwoPolynomial68_eta_cancel68
#print axioms fiveToSix_terminalTail_Extra_natDegree68
#print axioms fiveToSix_terminalTail_J_coeff_of_rowTwo_top68
#print axioms fiveToSix_terminalTail_expanded_rowTwo68
#print axioms fiveToSix_terminalTail_expanded_rowOne68
#print axioms fiveToSix_terminalTail_Q_coeff68
#print axioms fiveToSix_terminalTail_de_coeff68
#print axioms fiveToSix_terminalTail_Y_coeff_meeting68

end FiveToSixTerminalTailRowTwo68

end Max11DegreeRoutes
