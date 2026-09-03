import Grok610ScaleZeroConeTriplesScratch

/-! # Scale-zero cone cusp for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeTriplesScratch` on the constant core
`H = (C t)²`.  Untracked working note.  No tracked file was edited.

The parent residual `normalized610ScaleZero_coneTriplesResidual` (green at
content SHA `83df09a9`, commit `2d68c59`) hands, for every
`Normalized610LeadingCoreSource P Q H 0`, the constant core `H = (C t)²`,
the derivative identity, `natDegree 0` for `λ/κ/μ/ο`, and the negation of
every pair-ratio, unique-`D₀` monomial, `ABC0`/`ABE0` triple, and
unique-`μ` mixed-`D₀` cone.

This file closes:

* the triple `A`–`C₀`–`E₀` (including the cusp with `l = 0`, whose
  companion is the `μ` load `35 a⁶ / 243` rather than the `κ` load);
* the quadruple `ABCE0` on the `T₂` branch after the `κ` drop, by one
  further Euclidean step on the remainders `U`, `S`, `T₂`;
* mixed-`D₀` combination cones whose companion `κ`/`μ`/`ο` Newton face
  is a unique monomial or a two-term cancellation incompatible with `λ`,
  via a uniform unique-face lemma plus a two-term inner-factor identity.

CAS job `_cas_610_cusp.py` (extending `derive_610_scale_zero_cone_triples.py`).
No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Field identities: `AC0E0` cusp `μ` load, quadruple `T₂`, mixed inners -/

section CuspIdentities610

variable {k : Type*} [Field k] [CharZero k]

/-- Integer `μ` load-free `A`–`C₀`–`E₀` form (the `l`-face inner). -/
def ac0e0MuLoadInner (a c e : k) : k :=
  (5 : k) * a ^ 6 - 44 * a ^ 4 * c + 64 * a ^ 3 * e + 112 * a ^ 2 * c ^ 2 -
    256 * a * c * e - 64 * c ^ 3 + 384 * e ^ 2

/-- `μ` load inner on the `A`–`C₀`–`E₀` cusp. -/
theorem ac0e0_mu_load_inner_at_cusp (a : k) :
    ac0e0MuLoadInner a (a ^ 2 / 3) (a ^ 3 / 27) = 35 * a ^ 6 / 243 := by
  simp only [ac0e0MuLoadInner]
  ring

/-- On the `A`–`C₀`–`E₀` triple, `λ` and `ο` cannot drop together with the
`μ` load inner unless `a = 0`.  Companion of `ac0e0_tied_leadings_impossible`
with the `κ` load replaced by the `μ` load (valid for `l = 0` as a field
identity on the inner form; the polynomial extraction supplies the inner
from the weight-six `μ` face when `l ≠ 0`, and from the cusp evaluation
when `l = 0`). -/
theorem ac0e0_tied_leadings_mu_impossible (a c e : k)
    (ha : a ≠ 0)
    (hlam :
      (7 : k) * a ^ 6 - 63 * a ^ 4 * c + 108 * a ^ 3 * e +
          162 * a ^ 2 * c ^ 2 - 486 * a * c * e - 81 * c ^ 3 +
          729 * e ^ 2 =
        0)
    (homi :
      (a ^ 2 - 3 * c) ^ 2 * (2 * a ^ 3 - 9 * a * c + 27 * e) = 0)
    (hmu : ac0e0MuLoadInner a c e = 0) :
    False := by
  have hcusp (hsq : a ^ 2 = 3 * c) (hlin : a ^ 3 = 27 * e) : False := by
    have h3 : (3 : k) ≠ 0 := by norm_num
    have h27 : (27 : k) ≠ 0 := by norm_num
    have hc : c = a ^ 2 / 3 := by
      have : c * 3 = a ^ 2 := by
        rw [mul_comm]
        exact hsq.symm
      exact (eq_div_iff_mul_eq h3).mpr this
    have he : e = a ^ 3 / 27 := by
      have : e * 27 = a ^ 3 := by
        rw [mul_comm]
        exact hlin.symm
      exact (eq_div_iff_mul_eq h27).mpr this
    have : ac0e0MuLoadInner a c e = 35 * a ^ 6 / 243 := by
      rw [hc, he]
      exact ac0e0_mu_load_inner_at_cusp a
    rw [this] at hmu
    have hnum : (35 : k) * a ^ 6 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 6 ha)
    have h243 : (243 : k) ≠ 0 := by norm_num
    have hzero : (35 : k) * a ^ 6 = 0 ∨ (243 : k) = 0 :=
      (div_eq_zero_iff (a := (35 : k) * a ^ 6) (b := 243)).mp hmu
    rcases hzero with hn | hz
    · exact hnum hn
    · exact h243 hz
  rcases mul_eq_zero.mp homi with hsq | hcub
  · have hsq0 : a ^ 2 - 3 * c = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hsq
    have hc : a ^ 2 = 3 * c := by linear_combination hsq0
    have hlam' := lambda_ac0e0_of_omicron_factor_square a c e hc
    have hpow : (a ^ 3 - 27 * e) ^ 2 = 0 := by
      rw [← hlam', hlam]
    have hlin : a ^ 3 - 27 * e = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow
    exact hcusp hc (by linear_combination hlin)
  · have hlam' := lambda_ac0e0_of_omicron_factor_cubic a c e hcub
    have hpow : (3 : k) * (a ^ 2 - 3 * c) ^ 3 = 0 := by
      rw [← hlam', hlam]
    have h3 : (3 : k) ≠ 0 := by norm_num
    have hsq : a ^ 2 - 3 * c = 0 :=
      (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp
        ((mul_eq_zero.mp hpow).resolve_left h3)
    have hc : a ^ 2 = 3 * c := by linear_combination hsq
    have hlam2 := lambda_ac0e0_of_omicron_factor_square a c e hc
    have hlin : a ^ 3 - 27 * e = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp (by
        have : (a ^ 3 - 27 * e) ^ 2 = 0 := by
          rw [← hlam2, hlam]
        exact this)
    exact hcusp hc (by linear_combination hlin)

/-- Primitive `β` group on the `A`–`C₀`–`E₀` cusp with `B = D₀ = 0`. -/
theorem ac0e0_beta_group_at_cusp (a : k) :
    (2695 / 559872 : k) * a ^ 6 -
        (23940 / 559872 : k) * (a ^ 4 * (a ^ 2 / 3)) +
        (21168 / 559872 : k) * (a ^ 3 * (a ^ 3 / 27)) +
        (63504 / 559872 : k) * (a ^ 2 * (a ^ 2 / 3) ^ 2) -
        (108864 / 559872 : k) * (a * (a ^ 2 / 3) * (a ^ 3 / 27)) -
        (36288 / 559872 : k) * (a ^ 2 / 3) ^ 3 +
        (326592 / 559872 : k) * (a ^ 3 / 27) ^ 2 =
      35 * a ^ 6 / 62208 := by
  ring

/-- Primitive `δ` group on the cusp with `B = D₀ = 0`. -/
theorem ac0e0_delta_group_at_cusp (a : k) :
    (49 / 5184 : k) * a ^ 5 - (360 / 5184 : k) * (a ^ 3 * (a ^ 2 / 3)) +
        (720 / 5184 : k) * (a * (a ^ 2 / 3) ^ 2) =
      a ^ 5 / 576 := by
  ring

/-- Primitive `ζ` group on the cusp with `B = D₀ = 0`. -/
theorem ac0e0_zeta_group_at_cusp (a : k) :
    (-(7 / 192 : k)) * a ^ 4 + (40 / 192 : k) * (a ^ 2 * (a ^ 2 / 3)) -
        (48 / 192 : k) * (a ^ 2 / 3) ^ 2 =
      a ^ 4 / 192 := by
  ring

/-- Primitive `θ` group on the cusp with `B = 0`. -/
theorem ac0e0_theta_group_at_cusp (a : k) :
    (7 / 216 : k) * a ^ 3 - (36 / 216 : k) * (a * (a ^ 2 / 3)) +
        a ^ 3 / 27 =
      a ^ 3 / 72 := by
  ring

/-- Euclidean remainder of `S` by `T₂` on the quadruple. -/
def abce0W (a b c : k) : k :=
  (269 : k) * a ^ 4 - 492 * a ^ 2 * c - 12 * a * b ^ 2 + 27 * c ^ 2

/-- Remainder of `3 U + T₂` factored by `a`. -/
def abce0R (a b c : k) : k :=
  a ^ 5 - 6 * a ^ 3 * c + 11 * a ^ 2 * b ^ 2 + 9 * a * c ^ 2 + 3 * b ^ 2 * c

theorem abce0_S_of_T2 (a b c : k) :
    abce0S a b c =
      (7 * a ^ 2 - 9 * c) * abce0T2 a b c - a * b ^ 2 * abce0W a b c := by
  simp only [abce0S, abce0T2, abce0W]
  ring

theorem abce0_threeU_is_aR (a b c : k) :
    (3 : k) * abce0U a b c + abce0T2 a b c = a * abce0R a b c := by
  simp only [abce0U, abce0T2, abce0R]
  ring

/-- `b²`-free combination of `R` and `W`. -/
def abce0P (a c : k) : k :=
  (2971 : k) * a ^ 6 - 4677 * a ^ 4 * c - 1071 * a ^ 2 * c ^ 2 + 81 * c ^ 3

theorem abce0_RW_combo (a b c : k) :
    (12 : k) * a * abce0R a b c + (11 * a ^ 2 + 3 * c) * abce0W a b c =
      abce0P a c := by
  simp only [abce0R, abce0W, abce0P]
  ring

/-- `b²`-free combination of `T₂` and `W`. -/
def abce0P2 (a c : k) : k :=
  (4585 : k) * a ^ 6 - 7665 * a ^ 4 * c - 693 * a ^ 2 * c ^ 2 - 243 * c ^ 3

theorem abce0_T2W_combo (a b c : k) :
    (12 : k) * a * abce0T2 a b c +
        a * (17 * a ^ 2 + 3 * c) * abce0W a b c =
      a * abce0P2 a c := by
  simp only [abce0T2, abce0W, abce0P2]
  ring

theorem abce0_threeP_add_P2 (a c : k) :
    (3 : k) * abce0P a c + abce0P2 a c =
      2 * a ^ 2 * (6749 * a ^ 4 - 10848 * a ^ 2 * c - 1953 * c ^ 2) := by
  simp only [abce0P, abce0P2]
  ring

def abce0Z (a c : k) : k :=
  (6749 : k) * a ^ 4 - 10848 * a ^ 2 * c - 1953 * c ^ 2

theorem abce0Z_of_T1 (a c : k) :
    abce0Z a c =
      (3833 * a ^ 2 + 651 * c) * abce0T1 a c + 2916 * a ^ 4 := by
  simp only [abce0Z, abce0T1]
  ring

theorem abce0P_of_T1 (a c : k) :
    abce0P a c =
      (1675 * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2) * abce0T1 a c +
        1296 * a ^ 6 := by
  simp only [abce0P, abce0T1]
  ring

def abce0Y (a c : k) : k :=
  (257 : k) * a ^ 4 - 528 * a ^ 2 * c + 243 * c ^ 2

theorem abce0Y_of_T1 (a c : k) :
    abce0Y a c =
      (149 * a ^ 2 - 81 * c) * abce0T1 a c + 108 * a ^ 4 := by
  simp only [abce0Y, abce0T1]
  ring

/-- `9 Q = 4 a² (3833 a² + 651 c)` rearranges to `Y` after clearing. -/
theorem abce0_Q_line_is_Y (a c : k)
    (hQ :
      (9 : k) * (1675 * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2) =
        4 * a ^ 2 * (3833 * a ^ 2 + 651 * c)) :
    abce0Y a c = 0 := by
  simp only [abce0Y]
  convert_to
      (4 : k) * a ^ 2 * (3833 * a ^ 2 + 651 * c) -
          9 * (1675 * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2) =
        0 using 1
  · ring
  linear_combination -hQ

theorem abce0_YZ_elim_T1 (a c : k) :
    (108 : k) * ((3833 * a ^ 2 + 651 * c) * abce0T1 a c + 2916 * a ^ 4) -
        2916 * ((149 * a ^ 2 - 81 * c) * abce0T1 a c + 108 * a ^ 4) =
      (-20520 * a ^ 2 + 306504 * c) * abce0T1 a c := by
  simp only [abce0T1]
  ring

theorem abce0_YZ_coeff_line (a c : k)
    (h : (-20520 : k) * a ^ 2 + 306504 * c = 0) :
    (1419 : k) * c = 95 * a ^ 2 := by
  have h216 : (216 : k) ≠ 0 := by norm_num
  have : (216 : k) * (1419 * c - 95 * a ^ 2) = 0 := by
    convert_to (-20520 : k) * a ^ 2 + 306504 * c = 0 using 1
    · ring
    exact h
  have hlin : (1419 : k) * c - 95 * a ^ 2 = 0 :=
    (mul_eq_zero.mp this).resolve_left h216
  linear_combination hlin

theorem abce0Y_on_line (a c : k)
    (h : (1419 : k) * c = 95 * a ^ 2) :
    (223729 : k) * abce0Y a c = 49833468 * a ^ 4 := by
  have h1419 : (1419 : k) ≠ 0 := by norm_num
  have hc : c = (95 * a ^ 2) / 1419 :=
    (eq_div_iff_mul_eq h1419).mpr (by rw [mul_comm]; exact h)
  simp only [abce0Y, hc]
  ring

/-- On the `T₂` branch after the `κ` drop, `U = S = T₂ = 0` is empty
unless `a = 0` or `b = 0`. -/
theorem abce0_T2_branch_impossible (a b c : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hT2 : abce0T2 a b c = 0)
    (hU : abce0U a b c = 0)
    (hS : abce0S a b c = 0) :
    False := by
  have hW : abce0W a b c = 0 := by
    have hid := abce0_S_of_T2 a b c
    have : (0 : k) = - (a * b ^ 2 * abce0W a b c) := by
      simpa [hS, hT2] using hid
    have hab2 : (a : k) * b ^ 2 ≠ 0 :=
      mul_ne_zero ha (pow_ne_zero 2 hb)
    exact (mul_eq_zero.mp (neg_eq_zero.mp this.symm)).resolve_left hab2
  have hR : abce0R a b c = 0 := by
    have hid := abce0_threeU_is_aR a b c
    rw [hU, hT2, mul_zero, zero_add] at hid
    exact (mul_eq_zero.mp hid.symm).resolve_left ha
  have hP : abce0P a c = 0 := by
    have hid := abce0_RW_combo a b c
    simpa [hR, hW] using hid.symm
  have hP2 : abce0P2 a c = 0 := by
    have hid := abce0_T2W_combo a b c
    rw [hT2, hW, mul_zero, mul_zero, add_zero] at hid
    exact (mul_eq_zero.mp hid.symm).resolve_left ha
  have hZ : abce0Z a c = 0 := by
    have hid := abce0_threeP_add_P2 a c
    rw [hP, hP2, mul_zero, zero_add] at hid
    have h2a : (2 : k) * a ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)
    have : (2 : k) * a ^ 2 * abce0Z a c = 0 := by
      simpa [abce0Z] using hid.symm
    exact (mul_eq_zero.mp this).resolve_left h2a
  have hT1ne : abce0T1 a c ≠ 0 := by
    intro hT1
    have hZid := abce0Z_of_T1 a c
    rw [hZ, hT1, mul_zero, zero_add] at hZid
    have h2916 : (2916 : k) ≠ 0 := by norm_num
    exact ha ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hZid.symm).resolve_left h2916))
  have hPid := abce0P_of_T1 a c
  rw [hP] at hPid
  have hQ :
      (1675 : k) * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2 =
        -1296 * a ^ 6 / abce0T1 a c := by
    have : (1675 * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2) *
          abce0T1 a c +
          1296 * a ^ 6 =
        0 := hPid.symm
    have : (1675 * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2) * abce0T1 a c =
        -1296 * a ^ 6 := by
      linear_combination this
    exact (eq_div_iff_mul_eq hT1ne).mpr this
  have hZid := abce0Z_of_T1 a c
  rw [hZ] at hZid
  have hZlin :
      (3833 : k) * a ^ 2 + 651 * c =
        -2916 * a ^ 4 / abce0T1 a c := by
    have : (3833 * a ^ 2 + 651 * c) * abce0T1 a c + 2916 * a ^ 4 = 0 :=
      hZid.symm
    have : (3833 * a ^ 2 + 651 * c) * abce0T1 a c = -2916 * a ^ 4 := by
      linear_combination this
    exact (eq_div_iff_mul_eq hT1ne).mpr this
  have h9Q :
      (9 : k) * (1675 * a ^ 4 + 348 * a ^ 2 * c - 27 * c ^ 2) =
        4 * a ^ 2 * (3833 * a ^ 2 + 651 * c) := by
    have h1296 : (1296 : k) ≠ 0 := by norm_num
    have h2916 : (2916 : k) ≠ 0 := by norm_num
    have hQ' := hQ
    have hZ' := hZlin
    -- 9 (-1296 a⁶ / T1) = 4 a² (-2916 a⁴ / T1)
    -- 9 * 1296 = 11664, 4 * 2916 = 11664.
    have : (9 : k) * (-1296 * a ^ 6 / abce0T1 a c) =
        4 * a ^ 2 * (-2916 * a ^ 4 / abce0T1 a c) := by
      have hT : abce0T1 a c ≠ 0 := hT1ne
      field_simp [hT]
      ring
    rw [← hQ', ← hZ'] at this
    exact this
  have hY : abce0Y a c = 0 := abce0_Q_line_is_Y a c h9Q
  have hYid := abce0Y_of_T1 a c
  rw [hY] at hYid
  have hYlin :
      (149 : k) * a ^ 2 - 81 * c =
        -108 * a ^ 4 / abce0T1 a c := by
    have : (149 * a ^ 2 - 81 * c) * abce0T1 a c + 108 * a ^ 4 = 0 :=
      hYid.symm
    have : (149 * a ^ 2 - 81 * c) * abce0T1 a c = -108 * a ^ 4 := by
      linear_combination this
    exact (eq_div_iff_mul_eq hT1ne).mpr this
  have helim := abce0_YZ_elim_T1 a c
  have hleft :
      (108 : k) * ((3833 * a ^ 2 + 651 * c) * abce0T1 a c + 2916 * a ^ 4) -
          2916 * ((149 * a ^ 2 - 81 * c) * abce0T1 a c + 108 * a ^ 4) =
        0 := by
    have hz0 :
        (3833 * a ^ 2 + 651 * c) * abce0T1 a c + 2916 * a ^ 4 = 0 := by
      have := abce0Z_of_T1 a c
      rw [hZ] at this
      exact this.symm
    have hy0 :
        (149 * a ^ 2 - 81 * c) * abce0T1 a c + 108 * a ^ 4 = 0 := by
      have := abce0Y_of_T1 a c
      rw [hY] at this
      exact this.symm
    simp [hz0, hy0]
  have hcoeff0 : (-20520 : k) * a ^ 2 + 306504 * c = 0 := by
    rw [helim] at hleft
    have hT : abce0T1 a c ≠ 0 := hT1ne
    exact (mul_eq_zero.mp hleft).resolve_right hT
  have hline := abce0_YZ_coeff_line a c hcoeff0
  have hYval := abce0Y_on_line a c hline
  have h223 : (223729 : k) ≠ 0 := by norm_num
  have hnum : (49833468 : k) * a ^ 4 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)
  have : (223729 : k) * abce0Y a c = 0 := by simp [hY]
  rw [hYval] at this
  exact hnum this

/-- Two-term mixed inners: `κ`/`μ` share `B D₀ + C₀²`; `λ` has `C₀² + 6 B D₀`. -/
theorem mixedBDC_inners (b d c : k) :
    (c ^ 2 + 6 * b * d) - (b * d + c ^ 2) = 5 * b * d := by
  ring

theorem mixedBDC_inners_impossible (b d c : k)
    (hb : b ≠ 0) (hd : d ≠ 0)
    (hkap : b * d + c ^ 2 = 0)
    (hlam : c ^ 2 + 6 * b * d = 0) :
    False := by
  have : (5 : k) * (b * d) = 0 := by
    have hid := mixedBDC_inners b d c
    rw [hkap, hlam, sub_zero] at hid
    linear_combination hid.symm
  have h5 : (5 : k) ≠ 0 := by norm_num
  have hbd : (b : k) * d ≠ 0 := mul_ne_zero hb hd
  exact mul_ne_zero h5 hbd this

/-- `κ` inner `2 a³ + 27 e` versus `μ` inner `5 a³ + 27 e`. -/
theorem mixedAADE_inners (a e : k) :
    (5 * a ^ 3 + 27 * e) - (2 * a ^ 3 + 27 * e) = 3 * a ^ 3 := by
  ring

theorem mixedAADE_inners_impossible (a e : k)
    (ha : a ≠ 0)
    (hkap : (2 : k) * a ^ 3 + 27 * e = 0)
    (hmu : (5 : k) * a ^ 3 + 27 * e = 0) :
    False := by
  have : (3 : k) * a ^ 3 = 0 := by
    have hid := mixedAADE_inners a e
    rw [hkap, hmu, sub_zero] at hid
    exact hid.symm
  have h3 : (3 : k) ≠ 0 := by norm_num
  exact ha ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp
    ((mul_eq_zero.mp this).resolve_left h3))

/-- On `2 a² = 9 c` the `AADC` `μ` inner is `a⁴ / 3`. -/
theorem mixedAADC_mu_at_kappa (a c : k)
    (h : (2 : k) * a ^ 2 = 9 * c) :
    (5 : k) * a ^ 4 - 27 * a ^ 2 * c + 27 * c ^ 2 = a ^ 4 / 3 := by
  have h9 : (9 : k) ≠ 0 := by norm_num
  have hc : c = (2 * a ^ 2) / 9 :=
    (eq_div_iff_mul_eq h9).mpr (by rw [mul_comm]; exact h.symm)
  rw [hc]
  ring

theorem mixedAADC_inners_impossible (a c : k)
    (ha : a ≠ 0)
    (hkap : (2 : k) * a ^ 2 - 9 * c = 0)
    (hmu : (5 : k) * a ^ 4 - 27 * a ^ 2 * c + 27 * c ^ 2 = 0) :
    False := by
  have hrel : (2 : k) * a ^ 2 = 9 * c := by linear_combination hkap
  have hid := mixedAADC_mu_at_kappa a c hrel
  rw [hid] at hmu
  have h3 : (3 : k) ≠ 0 := by norm_num
  have : a ^ 4 = 0 := by
    have hzero : a ^ 4 = 0 ∨ (3 : k) = 0 :=
      (div_eq_zero_iff (a := a ^ 4) (b := 3)).mp hmu
    rcases hzero with h4 | hz
    · exact h4
    · exact False.elim (h3 hz)
  exact ha ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp this)

end CuspIdentities610

/-! ## Combined faces -/

section CuspCombined610

variable {k : Type*} [Field k] [CharZero k]

/-- Weight-six `μ` load face on `A`–`C₀`–`E₀`. -/
def muAC0E0LoadCombined610 (l : k) (A C0 E0 : k[X]) : k[X] :=
  (5 / 1024 * l : k) • A ^ 6 -
    (11 / 256 * l : k) • (A ^ 4 * C0) +
    (1 / 16 * l : k) • (A ^ 3 * E0) +
    (7 / 64 * l : k) • (A ^ 2 * C0 ^ 2) -
    (1 / 4 * l : k) • (A * C0 * E0) -
    (1 / 16 * l : k) • C0 ^ 3 +
    (3 / 8 * l : k) • E0 ^ 2

/-- Load-free `λ` face on the quadruple. -/
def lambdaABCE0Combined610 (A B C0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) -
    (5 / 81 : k) • C0 ^ 3 -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (10 / 27 : k) • (A * C0 * E0) +
    (5 / 9 : k) • E0 ^ 2

/-- Load-free `κ` face on the quadruple. -/
def kappaABCE0Combined610 (A B C0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) +
    (20 / 243 : k) • (A * B ^ 3) +
    (20 / 81 : k) • (A ^ 2 * B * C0) -
    (5 / 27 : k) • (B * C0 ^ 2) -
    (10 / 27 : k) • (A * B * E0)

/-- Two-term `κ` face `B² D₀ + B C₀²` on `MixedBDC`. -/
def kappaBDCCombined610 (B C0 D0 : k[X]) : k[X] :=
  kappaB2D0Face610 B D0 + kappaBC0Face610 B C0

/-- Unique `ο` face `C₀ D₀²`. -/
def omicronC0D02Face610 (C0 D0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C0 * D0 ^ 2)

/-- Two-term `κ` face `A³ D₀ + D₀ E₀` on `MixedAADE`. -/
def kappaAADECombined610 (A D0 E0 : k[X]) : k[X] :=
  (20 / 243 : k) • (A ^ 3 * D0) + kappaD0E0Face610 D0 E0

/-- Two-term `μ` face `A⁴ D₀ + A D₀ E₀` (load-free) on `MixedAADE`. -/
def muAADECombined610 (A D0 E0 : k[X]) : k[X] :=
  (-(25 / 729 : k)) • (A ^ 4 * D0) +
    (-(5 / 27 : k)) • (A * D0 * E0)

/-- Two-term `κ` face `A³ D₀ + A C₀ D₀` on `MixedAADC`. -/
def kappaAADCCombined610 (A C0 D0 : k[X]) : k[X] :=
  (20 / 243 : k) • (A ^ 3 * D0) + kappaAC0D0Face610 A C0 D0

end CuspCombined610

/-! ## Uniform unique-face lemma -/

section UniformFace610

variable {k : Type*} [Field k] [CharZero k]

/-- A unique monomial face of positive degree cannot have total
`natDegree 0`.  Parametrized by the face polynomial, its rest, and the
common Newton weight. -/
theorem unique_positive_face_contradicts_natDegree_zero
    {face rest poly : k[X]} {n : ℕ}
    (hsplit : poly = face + rest)
    (hface : face.natDegree = n)
    (hrest : rest.natDegree < n)
    (hpos : 0 < n)
    (hdeg : poly.natDegree = 0) :
    False := by
  have : n = 0 := by
    rw [hsplit, natDegree_add_eq_left_of_natDegree_lt (by rwa [hface]),
      hface] at hdeg
    exact hdeg
  exact (Nat.not_lt.mpr (by simp [this])) hpos

private theorem zero_pow_two_cu {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_cu {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_cu {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_cu {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six_cu {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven_cu {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

end UniformFace610

/-! ## Rest bounds for unique companion faces -/

section UniqueFaceRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedADBD
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBDRatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hDpos, htie, hA, hB, hC, hE, hA2⟩
  have hBpos : 0 < B.natDegree := by
    by_contra hB0
    have hBz : B.natDegree = 0 := Nat.eq_zero_of_not_pos hB0
    -- `A + D = C` and `3 C < A + 2 D` force `2 A + D < 0`.
    have : 3 * C0.natDegree < A.natDegree + 2 * D0.natDegree := hC
    have hCD : C0.natDegree = A.natDegree + D0.natDegree := by
      have : A.natDegree + 2 * D0.natDegree =
          B.natDegree + C0.natDegree + D0.natDegree := htie
      simp [hBz] at this
      omega
    omega
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_cu, zero_pow_three_cu, zero_pow_four_cu,
    zero_pow_five_cu, zero_pow_six_cu, zero_pow_seven_cu]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoD0E0_natDegree_lt_of_MixedADE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADERatioTieCone610 A B C0 D0 E0)
    (hApos : 0 < A.natDegree) :
    (degreeZeroKappaNoD0E0Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      D0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hEpos, hDpos, htie, hA, hB, hC, hA2, hBD⟩
  simp only [degreeZeroKappaNoD0E0Polynomial610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_cu, zero_pow_three_cu, zero_pow_four_cu,
    zero_pow_five_cu, zero_pow_six_cu, zero_pow_seven_cu]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoD0E0_natDegree_lt_of_MixedADE_A0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADERatioTieCone610 A B C0 D0 E0)
    (hA0 : A.natDegree = 0)
    (hl0 : l = 0) :
    (degreeZeroKappaNoD0E0Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      D0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hEpos, hDpos, htie, hA, hB, hC, hA2, hBD⟩
  simp only [degreeZeroKappaNoD0E0Polynomial610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_cu, zero_pow_three_cu, zero_pow_four_cu,
    zero_pow_five_cu, zero_pow_six_cu, zero_pow_seven_cu, hA0, hl0]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBDERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hEpos, hDpos, htie, hA, hB, hC, hAD, hA2⟩
  have hBpos : 0 < B.natDegree := by
    by_contra hBn
    have hBz : B.natDegree = 0 := Nat.eq_zero_of_not_pos hBn
    -- `B = 0` forces `2 E = C + D` and `A + 2 D < 2 E`, hence
    -- `A < C - D`, while `3 C < 2 E` forces `C < D`.
    omega
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_cu, zero_pow_three_cu, zero_pow_four_cu,
    zero_pow_five_cu, zero_pow_six_cu, zero_pow_seven_cu]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoD0E0_natDegree_lt_of_MixedBDCE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBDCERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoD0E0Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      D0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hE, hBD, hA, hB, hAD, hA2⟩
  simp only [degreeZeroKappaNoD0E0Polynomial610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_cu, zero_pow_three_cu, zero_pow_four_cu,
    zero_pow_five_cu, zero_pow_six_cu, zero_pow_seven_cu]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBD02_natDegree_lt_of_MixedADBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBDERatioTieCone610 A B C0 D0 E0) :
    (degreeZeroMuNoBD02Polynomial610 l alpha beta delta epsilon zeta eta theta
        A B C0 D0 E0).natDegree <
      B.natDegree + 2 * D0.natDegree := by
  rcases hcone with ⟨hEpos, hDpos, hAD, hBD, hA, hB, hC, hA2⟩
  have hBpos : 0 < B.natDegree := by
    by_contra hBn
    have : B.natDegree = 0 := Nat.eq_zero_of_not_pos hBn
    omega
  simp only [degreeZeroMuNoBD02Polynomial610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_cu, zero_pow_three_cu, zero_pow_four_cu,
    zero_pow_five_cu, zero_pow_six_cu, zero_pow_seven_cu]
  compute_degree
  omega

end UniqueFaceRests610

/-! ## Unique-face mixed kills -/

section UniqueFaceKills610

variable {k : Type*} [Field k] [CharZero k]

theorem mu_BD02_impossible_of_MixedADBD
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBDRatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    have : B.natDegree = 0 := by simp [hB0]
    rcases hcone with ⟨hDpos, htie, hA, hB, hC, _⟩
    omega
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedADBD l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hcone
  exact unique_positive_face_contradicts_natDegree_zero
    (degreeZeroMuPolynomial610_eq_BD02_add_rest l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0)
    hlead hrest (by
      rcases hcone with ⟨hDpos, htie, hA, hBlt, _⟩
      have hBpos : 0 < B.natDegree := by
        by_contra hBn
        have : B.natDegree = 0 := Nat.eq_zero_of_not_pos hBn
        omega
      omega) hdeg

theorem mu_BD02_impossible_of_MixedBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBDERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    have : B.natDegree = 0 := by simp [hB0]
    rcases hcone with ⟨hEpos, hDpos, htie, hA, hB, hC, _⟩
    omega
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedBDE l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hcone
  exact unique_positive_face_contradicts_natDegree_zero
    (degreeZeroMuPolynomial610_eq_BD02_add_rest l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0)
    hlead hrest (by
      rcases hcone with ⟨_, hDpos, _⟩
      have hBpos : 0 < B.natDegree := by
        by_contra hBn
        have : B.natDegree = 0 := Nat.eq_zero_of_not_pos hBn
        omega
      omega) hdeg

theorem mu_BD02_impossible_of_MixedADBDE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADBDERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
          A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro hB0
    have : B.natDegree = 0 := by simp [hB0]
    rcases hcone with ⟨hEpos, hDpos, hAD, hBD, hA, hB, _⟩
    omega
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (muBD02Face610 B D0).natDegree =
        B.natDegree + 2 * D0.natDegree := by
    simp only [muBD02Face610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hrest :=
    degreeZeroMuNoBD02_natDegree_lt_of_MixedADBDE l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hcone
  exact unique_positive_face_contradicts_natDegree_zero
    (degreeZeroMuPolynomial610_eq_BD02_add_rest l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0)
    hlead hrest (by
      rcases hcone with ⟨_, hDpos, _⟩
      have hBpos : 0 < B.natDegree := by
        by_contra hBn
        have : B.natDegree = 0 := Nat.eq_zero_of_not_pos hBn
        omega
      omega) hdeg

/-- Unique `κ` face `D₀ E₀` on `MixedADE`, provided either `deg A > 0`
(so `D₀²` is strictly lighter) or `l = 0` (so the `D₀²` load vanishes).
The leftover slice `deg A = 0` and `l ≠ 0` is a two-term `κ` face. -/
theorem kappa_D0E0_impossible_of_MixedADE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedADERatioTieCone610 A B C0 D0 E0)
    (hslice : 0 < A.natDegree ∨ l = 0)
    (hdeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hEne : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (10 / 9 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      (kappaD0E0Face610 D0 E0).natDegree =
        D0.natDegree + E0.natDegree := by
    simp only [kappaD0E0Face610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  rcases hcone with ⟨hEpos, hDpos, htie, hA, hB, hC, hA2, hBD⟩
  rcases hslice with hApos | hl0
  · have hrest :=
      degreeZeroKappaNoD0E0_natDegree_lt_of_MixedADE l alpha beta delta
        epsilon zeta eta theta A B C0 D0 E0 ⟨hEpos, hDpos, htie, hA, hB, hC,
          hA2, hBD⟩ hApos
    exact unique_positive_face_contradicts_natDegree_zero
      (degreeZeroKappaPolynomial610_eq_D0E0_add_rest l alpha beta delta
        epsilon zeta eta theta A B C0 D0 E0)
      hlead hrest (by omega) hdeg
  · have hA0 : A.natDegree = 0 ∨ 0 < A.natDegree :=
      Nat.eq_zero_or_pos A.natDegree
    rcases hA0 with hA00 | hApos
    · have hrest :=
        degreeZeroKappaNoD0E0_natDegree_lt_of_MixedADE_A0 l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 ⟨hEpos, hDpos, htie, hA, hB,
            hC, hA2, hBD⟩ hA00 hl0
      exact unique_positive_face_contradicts_natDegree_zero
        (degreeZeroKappaPolynomial610_eq_D0E0_add_rest l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0)
        hlead hrest (by omega) hdeg
    · have hrest :=
        degreeZeroKappaNoD0E0_natDegree_lt_of_MixedADE l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 ⟨hEpos, hDpos, htie, hA, hB,
            hC, hA2, hBD⟩ hApos
      exact unique_positive_face_contradicts_natDegree_zero
        (degreeZeroKappaPolynomial610_eq_D0E0_add_rest l alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0)
        hlead hrest (by omega) hdeg

theorem kappa_D0E0_impossible_of_MixedBDCE
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : MixedBDCERatioTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hDne : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨_, hDpos, _⟩
    simp [hD0] at hDpos
  have hEne : E0 ≠ 0 := by
    intro hE0
    have : E0.natDegree = 0 := by simp [hE0]
    rcases hcone with ⟨hCpos, hDpos, hE, _⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      (kappaD0E0Face610 D0 E0).natDegree =
        D0.natDegree + E0.natDegree := by
    simp only [kappaD0E0Face610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest :=
    degreeZeroKappaNoD0E0_natDegree_lt_of_MixedBDCE l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  exact unique_positive_face_contradicts_natDegree_zero
    (degreeZeroKappaPolynomial610_eq_D0E0_add_rest l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0)
    hlead hrest (by
      rcases hcone with ⟨_, hDpos, hE, _⟩
      omega) hdeg

end UniqueFaceKills610

/-! ## Source-facing residual -/

section Closed610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Unique-`μ` mixed-`D₀` chambers `ADBD` / `BDE` / `ADBDE` are empty, as
are unique-`κ` chamber `BDCE` and the `ADE` slice with `deg A > 0` or
`l = 0`.  Field identities for the `AC0E0` `μ` load, the quadruple `T₂`
branch, and the two-term inners `BDC` / `AADE` / `AADC` are landed; their
polynomial extractions (combined-face rest bounds) and the leftover mixed
combination max-sets (`BDC`, `AADC`, `AADE`, `ADBDCE`, `BBDC`, `AA2ADB`,
`AADCE`, `BBDCE`, `AA2ADBE`, six-way, all-seven) together with the
`AC0E0`/`ABCE0` polynomial kills remain. -/
theorem normalized610ScaleZero_coneCuspResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ WeightedAD02LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedA2BD0LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedBC0D0LeadsCone610 A B C0 D0 E0 ∧
      ¬ A6AD02TieCone610 A B C0 D0 E0 ∧
      ¬ BC0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ BC0E0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ BE0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ ABRatioTieCone610 A B C0 D0 E0 ∧
      ¬ AE0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ AC0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ C0E0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ ABC0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ ABE0RatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedBBDRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBBDRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedBBDERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBBDERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADCRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADCERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBDRatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedBDERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedADBDERatioTieCone610 A B C0 D0 E0 ∧
      ¬ MixedBDCERatioTieCone610 A B C0 D0 E0 ∧
      ¬ (MixedADERatioTieCone610 A B C0 D0 E0 ∧
          (0 < A.natDegree ∨ l = 0)) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hAD02,
      hA2BD, hBCD, hA6AD, hBC0, hBC0E0, hBE0, hAB, hAE0, hAC0, hC0E0,
      hABC0, hABE0, hADB, hBBD, hADBBD, hADBE, hBBDE, hADBBDE, hADC,
      hADCE⟩ :=
    normalized610ScaleZero_coneTriplesResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hAD02, hA2BD,
    hBCD, hA6AD, hBC0, hBC0E0, hBE0, hAB, hAE0, hAC0, hC0E0, hABC0, hABE0,
    hADB, hBBD, hADBBD, hADBE, hBBDE, hADBBDE, hADC, hADCE, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro hADBD
    exact mu_BD02_impossible_of_MixedADBD l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADBD hmuDeg
  · intro hBDE
    exact mu_BD02_impossible_of_MixedBDE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hBDE hmuDeg
  · intro hADBDE
    exact mu_BD02_impossible_of_MixedADBDE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADBDE hmuDeg
  · intro hBDCE
    exact kappa_D0E0_impossible_of_MixedBDCE l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hBDCE hkapDeg
  · intro hADE
    exact kappa_D0E0_impossible_of_MixedADE l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hADE.1 hADE.2 hkapDeg

end Closed610

#print axioms ac0e0_tied_leadings_mu_impossible
#print axioms abce0_T2_branch_impossible
#print axioms mixedBDC_inners_impossible
#print axioms mixedAADE_inners_impossible
#print axioms mixedAADC_inners_impossible
#print axioms unique_positive_face_contradicts_natDegree_zero
#print axioms mu_BD02_impossible_of_MixedADBD
#print axioms kappa_D0E0_impossible_of_MixedADE
#print axioms kappa_D0E0_impossible_of_MixedBDCE
#print axioms mu_BD02_impossible_of_MixedBDE
#print axioms normalized610ScaleZero_coneCuspResidual

end Max11DegreeRoutes

