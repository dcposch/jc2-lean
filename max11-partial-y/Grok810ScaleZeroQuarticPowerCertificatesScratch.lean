import Grok810ScaleZeroQuarticSigmaLadderScratch

/-! # Power-target certificates, `(8,10)` scale zero

The residual after Files B/C module 30 (`QuarticChamberResidual4810`, 205
chambers) still contains **78** single-leaf chambers whose JSON certificate is
`power_target` with `cofactors = null` and whose load columns already clear.
Those 78 collapse to 24 distinct face systems; 13 further residual
`power_target` systems live on carrier-refined cells (the CEG `g^4` system
is omitted: its `μ/γ` column does not clear).  Together these are **37**
saturating face systems.

CAS (`scripts/derive_810_scale_zero_quartic_power_certs.py`, Singular `lift`
plus the isobaric engine of `scripts/emit_810_quartic_chambers.py`):

* S00 (`κ, ξ`), target `a^2*b^2*c^2*e^2` (recorded), cofactor sizes 1+1, 8 chamber(s).
* S01 (`κ, μ, ξ`), target `f^4` (recorded), cofactor sizes 3+1+3, 2 chamber(s).
* S02 (`κ, ξ`), target `a^2*b^2*g^2` (recorded), cofactor sizes 1+1, 4 chamber(s).
* S03 (`μ, ξ`), target `a^3*b^3*c^3*g^3` (recorded), cofactor sizes 1+1, 2 chamber(s).
* S04 (`μ, ξ`), target `b^2*c^2*g^2` (recorded), cofactor sizes 1+1, 1 chamber(s).
* S05 (`μ, π`), target `a^2*c^2*d^2` (recorded), cofactor sizes 1+1, 8 chamber(s).
* S06 (`κ, μ, ξ, π`), target `e^6` (recorded), cofactor sizes 7+5+7+4, 4 chamber(s).
* S07 (`κ, μ, ξ, π`), target `a^3*b^3*c^3*d^3*f^3` (recorded), cofactor sizes 2+2+5+1, 4 chamber(s).
* S08 (`κ, μ, π`), target `c^7` (recorded), cofactor sizes 2+5+2, 6 chamber(s).
* S09 (`κ, μ, π`), target `a^2*b^2*c^2*d^2*g^2` (recorded), cofactor sizes 3+2+1, 1 chamber(s).
* S10 (`κ, μ, ξ`), target `e^5` (recorded), cofactor sizes 2+4+4, 4 chamber(s).
* S11 (`κ, ξ`), target `a^3*b^3*c^3*e^3*g^3` (recorded), cofactor sizes 1+1, 4 chamber(s).
* S12 (`κ, μ, ξ, π`), target `g^4` (recorded), cofactor sizes 7+7+6+5, 1 chamber(s).
* S13 (`κ, μ, ξ, π`), target `e^6` (recorded), cofactor sizes 4+5+3+1, 4 chamber(s).
* S14 (`κ, ξ, π`), target `g^4` (recorded), cofactor sizes 3+2+3, 4 chamber(s).
* S15 (`κ, μ, ξ, π`), target `e^5` (recorded), cofactor sizes 3+2+2+1, 4 chamber(s).
* S16 (`κ, μ, π`), target `a*b*c*f*g` (recorded), cofactor sizes 1+1+1, 3 chamber(s).
* S17 (`κ, ν`), target `a*b*c*e*f*g` (recorded), cofactor sizes 1+1, 2 chamber(s).
* S18 (`κ, ξ`), target `a*b*e*g` (recorded), cofactor sizes 1+1, 3 chamber(s).
* S19 (`κ, μ, ν, ξ, π`), target `f^3` (recorded), cofactor sizes 2+1+2+2+2, 2 chamber(s).
* S20 (`μ, ξ, π`), target `a^2*b^2*d^2*e^2*f^2*g^2` (recorded), cofactor sizes 1+4+2, 2 chamber(s).
* S21 (`κ, μ, ν, ξ, π`), target `g^3` (recorded), cofactor sizes 2+1+2+2+3, 2 chamber(s).
* S22 (`μ, ξ, π`), target `a^2*c^2*d^2*e^2*f^2*g^2` (recorded), cofactor sizes 1+4+1, 2 chamber(s).
* S23 (`κ, ν, ο`), target `a*b*c*d*e*f*g` (recorded), cofactor sizes 3+2+2, 1 chamber(s).
* S25 (`κ, μ, ξ, π`), target `a^2*b^2*c^2*d^2*e^2*g^2` (recorded), cofactor sizes 7+6+6+5, 2 chamber(s).
* S26 (`κ, ν`), target `a^2*b^2*c^2*d^2*e^2*g^2` (recorded), cofactor sizes 3+2, 2 chamber(s).
* S27 (`κ, ν`), target `b^2*c^2*d^2*e^2*g^2` (recorded), cofactor sizes 1+2, 2 chamber(s).
* S28 (`κ, ξ`), target `b^2*c^2*d^2*e^2*g^2` (recorded), cofactor sizes 1+2, 2 chamber(s).
* S29 (`κ, μ, ξ, π`), target `a^3*b^3*c^3*d^3*f^3*g^3` (recorded), cofactor sizes 2+2+6+1, 2 chamber(s).
* S30 (`κ, μ, ξ, π`), target `a*b*c*d*f*g` (recorded), cofactor sizes 3+1+2+1, 2 chamber(s).
* S31 (`κ, ν`), target `a*b*c*d*f*g` (recorded), cofactor sizes 2+1, 2 chamber(s).
* S32 (`κ, μ, ξ, π`), target `a^3*b^3*c^3*e^3*f^3*g^3` (recorded), cofactor sizes 8+9+14+4, 2 chamber(s).
* S33 (`κ, ξ`), target `b*c*e*f*g` (recorded), cofactor sizes 1+1, 2 chamber(s).
* S34 (`κ, μ, ξ, π`), target `a*c*d*e*f*g` (recorded), cofactor sizes 2+2+2+1, 2 chamber(s).
* S35 (`κ, μ, ν, π`), target `g^4` (recorded), cofactor sizes 2+3+2+3, 2 chamber(s).
* S36 (`κ, ν`), target `b*c*d*f*g` (recorded), cofactor sizes 1+1, 1 chamber(s).
* S37 (`κ, μ, ν, π`), target `g^4` (recorded), cofactor sizes 2+3+2+3, 1 chamber(s).

Each identity is a standalone scalar equation over a `CharZero` field, in the
shape of `quarticNoTargetInner_ABCF_identity`.  The kill hypothesises that the
face polynomials vanish and that the involved leading coefficients are nonzero,
and concludes `False`.  Identities verified by expansion and at random rational
points; Singular `lift` of the same monomial target succeeds.  No `sorry`, no
new axioms, no finite-root shortcut.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticPowerCertificates810

/-! ## Face system S00 (`a^2*b^2*c^2*e^2`) -/

/-- Face of `κ` on power system 00. -/
def kappaQuarticPowerInnerS00810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `ξ` on power system 00. -/
def xiQuarticPowerInnerS00810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (15 / 512 : k) * a * b ^ 2 * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*b^2*c^2*e^2 ∈ ⟨faces⟩` on power system 00. -/
theorem quarticPowerInnerS00810_identity (a b c d e f g : k) :
    a ^ 2 * b ^ 2 * c ^ 2 * e ^ 2 =
      ((-(64 / 5) : k) * a ^ 2 * b * e ^ 2) * kappaQuarticPowerInnerS00810 a b c d e f g +
      ((64 / 15 : k) * a ^ 2 * b ^ 2 * e) * xiQuarticPowerInnerS00810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS00810, xiQuarticPowerInnerS00810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*b^2*c^2*e^2 = 0`, contradiction. -/
theorem quarticPowerInnerS00810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS00810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS00810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    : False := by
  have hid := quarticPowerInnerS00810_identity a b c d e f g
  have hpow : a ^ 2 * b ^ 2 * c ^ 2 * e ^ 2 = 0 := by
    rw [hkap, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h3 | h3
  · -- the left factor
    rcases (mul_eq_zero.mp h3) with h2 | h2
    · -- the left factor
      rcases (mul_eq_zero.mp h2) with h1 | h1
      · -- the left factor
        exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
    · -- the right factor
      exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
  · -- the right factor
    exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)

/-! ## Face system S01 (`f^4`) -/

/-- Face of `κ` on power system 01. -/
def kappaQuarticPowerInnerS01810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * c * f +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 01. -/
def muQuarticPowerInnerS01810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 64) : k) * a * b * f +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 01. -/
def xiQuarticPowerInnerS01810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * f ^ 2 +
      (-(15 / 2048) : k) * a * b ^ 4 +
      (45 / 512 : k) * b ^ 2 * c ^ 2 +
      (-(25 / 128) : k) * b * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `f^4 ∈ ⟨faces⟩` on power system 01. -/
theorem quarticPowerInnerS01810_identity (a b c d e f g : k) :
    f ^ 4 =
      ((1 / 10 : k) * b ^ 3 * c ^ 2 +
      (14 / 3 : k) * b * f ^ 2 +
      (-(19 / 20) : k) * b ^ 2 * c * f) * kappaQuarticPowerInnerS01810 a b c d e f g +
      ((-(1 / 60) : k) * b ^ 3 * f) * muQuarticPowerInnerS01810 a b c d e f g +
      ((32 / 5 : k) * f ^ 2 +
      (2 / 15 : k) * b ^ 2 * c ^ 2 +
      (-(4 / 3) : k) * b * c * f) * xiQuarticPowerInnerS01810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS01810, muQuarticPowerInnerS01810, xiQuarticPowerInnerS01810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `f^4 = 0`, contradiction. -/
theorem quarticPowerInnerS01810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS01810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS01810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS01810 a b c d e f g = 0)
    (hf : f ≠ 0)
    : False := by
  have hid := quarticPowerInnerS01810_identity a b c d e f g
  have hpow : f ^ 4 = 0 := by
    rw [hkap, hmu, hxi] at hid
    simpa using hid
  exact hf ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S02 (`a^2*b^2*g^2`) -/

/-- Face of `κ` on power system 02. -/
def kappaQuarticPowerInnerS02810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `ξ` on power system 02. -/
def xiQuarticPowerInnerS02810 (a b c d e f g : k) : k :=
  (-(15 / 2048) : k) * a * b ^ 4 +
      (-(5 / 64) : k) * b ^ 2 * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*b^2*g^2 ∈ ⟨faces⟩` on power system 02. -/
theorem quarticPowerInnerS02810_identity (a b c d e f g : k) :
    a ^ 2 * b ^ 2 * g ^ 2 =
      ((24 / 5 : k) * a ^ 2 * b * g) * kappaQuarticPowerInnerS02810 a b c d e f g +
      ((32 / 5 : k) * a ^ 2 * g) * xiQuarticPowerInnerS02810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS02810, xiQuarticPowerInnerS02810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*b^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS02810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS02810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS02810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS02810_identity a b c d e f g
  have hpow : a ^ 2 * b ^ 2 * g ^ 2 = 0 := by
    rw [hkap, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h2 | h2
  · -- the left factor
    rcases (mul_eq_zero.mp h2) with h1 | h1
    · -- the left factor
      exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
    · -- the right factor
      exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)

/-! ## Face system S03 (`a^3*b^3*c^3*g^3`) -/

/-- Face of `μ` on power system 03. -/
def muQuarticPowerInnerS03810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 16 : k) * c * g +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 03. -/
def xiQuarticPowerInnerS03810 (a b c d e f g : k) : k :=
  (-(15 / 2048) : k) * a * b ^ 4 +
      (-(5 / 64) : k) * b ^ 2 * g +
      (45 / 512 : k) * b ^ 2 * c ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^3*b^3*c^3*g^3 ∈ ⟨faces⟩` on power system 03. -/
theorem quarticPowerInnerS03810_identity (a b c d e f g : k) :
    a ^ 3 * b ^ 3 * c ^ 3 * g ^ 3 =
      ((16 / 5 : k) * a ^ 3 * b ^ 3 * g ^ 3) * muQuarticPowerInnerS03810 a b c d e f g +
      ((64 / 5 : k) * a ^ 3 * b * c * g ^ 3) * xiQuarticPowerInnerS03810 a b c d e f g := by
  simp only [muQuarticPowerInnerS03810, xiQuarticPowerInnerS03810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^3*b^3*c^3*g^3 = 0`, contradiction. -/
theorem quarticPowerInnerS03810_false (a b c d e f g : k)
    (hmu : muQuarticPowerInnerS03810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS03810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS03810_identity a b c d e f g
  have hpow : a ^ 3 * b ^ 3 * c ^ 3 * g ^ 3 = 0 := by
    rw [hmu, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h3 | h3
  · -- the left factor
    rcases (mul_eq_zero.mp h3) with h2 | h2
    · -- the left factor
      rcases (mul_eq_zero.mp h2) with h1 | h1
      · -- the left factor
        exact ha ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hb ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
    · -- the right factor
      exact hc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h2)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h3)

/-! ## Face system S04 (`b^2*c^2*g^2`) -/

/-- Face of `μ` on power system 04. -/
def muQuarticPowerInnerS04810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 16 : k) * c * g

/-- Face of `ξ` on power system 04. -/
def xiQuarticPowerInnerS04810 (a b c d e f g : k) : k :=
  (-(5 / 64) : k) * b ^ 2 * g +
      (45 / 512 : k) * b ^ 2 * c ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `b^2*c^2*g^2 ∈ ⟨faces⟩` on power system 04. -/
theorem quarticPowerInnerS04810_identity (a b c d e f g : k) :
    b ^ 2 * c ^ 2 * g ^ 2 =
      ((18 / 5 : k) * b ^ 2 * c * g) * muQuarticPowerInnerS04810 a b c d e f g +
      ((8 / 5 : k) * c ^ 2 * g) * xiQuarticPowerInnerS04810 a b c d e f g := by
  simp only [muQuarticPowerInnerS04810, xiQuarticPowerInnerS04810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `b^2*c^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS04810_false (a b c d e f g : k)
    (hmu : muQuarticPowerInnerS04810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS04810 a b c d e f g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS04810_identity a b c d e f g
  have hpow : b ^ 2 * c ^ 2 * g ^ 2 = 0 := by
    rw [hmu, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h2 | h2
  · -- the left factor
    rcases (mul_eq_zero.mp h2) with h1 | h1
    · -- the left factor
      exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
    · -- the right factor
      exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)

/-! ## Face system S05 (`a^2*c^2*d^2`) -/

/-- Face of `μ` on power system 05. -/
def muQuarticPowerInnerS05810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2

/-- Face of `π` on power system 05. -/
def piQuarticPowerInnerS05810 (a b c d e f g : k) : k :=
  (15 / 256 : k) * c ^ 4 +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*c^2*d^2 ∈ ⟨faces⟩` on power system 05. -/
theorem quarticPowerInnerS05810_identity (a b c d e f g : k) :
    a ^ 2 * c ^ 2 * d ^ 2 =
      ((384 / 25 : k) * a * c ^ 2) * muQuarticPowerInnerS05810 a b c d e f g +
      ((256 / 25 : k) * a * c) * piQuarticPowerInnerS05810 a b c d e f g := by
  simp only [muQuarticPowerInnerS05810, piQuarticPowerInnerS05810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*c^2*d^2 = 0`, contradiction. -/
theorem quarticPowerInnerS05810_false (a b c d e f g : k)
    (hmu : muQuarticPowerInnerS05810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS05810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    : False := by
  have hid := quarticPowerInnerS05810_identity a b c d e f g
  have hpow : a ^ 2 * c ^ 2 * d ^ 2 = 0 := by
    rw [hmu, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h2 | h2
  · -- the left factor
    rcases (mul_eq_zero.mp h2) with h1 | h1
    · -- the left factor
      exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
    · -- the right factor
      exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
  · -- the right factor
    exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)

/-! ## Face system S06 (`e^6`) -/

/-- Face of `κ` on power system 06. -/
def kappaQuarticPowerInnerS06810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * d * e +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 06. -/
def muQuarticPowerInnerS06810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 06. -/
def xiQuarticPowerInnerS06810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (15 / 512 : k) * a * b ^ 2 * e +
      (15 / 256 : k) * a * b * c * d

/-- Face of `π` on power system 06. -/
def piQuarticPowerInnerS06810 (a b c d e f g : k) : k :=
  (15 / 256 : k) * c ^ 4 +
      (-(5 / 8) : k) * c * e ^ 2 +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (-(45 / 512) : k) * a * b ^ 2 * c ^ 2 +
      (5 / 32 : k) * a * c * d ^ 2 +
      (5 / 16 : k) * a * b * d * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `e^6 ∈ ⟨faces⟩` on power system 06. -/
theorem quarticPowerInnerS06810_identity (a b c d e f g : k) :
    e ^ 6 =
      ((-(879 / 6400) : k) * a ^ 2 * b ^ 3 * e ^ 2 +
      (3 / 320 : k) * a ^ 2 * b ^ 3 * c ^ 3 +
      (3 / 6400 : k) * a ^ 3 * b ^ 5 * c +
      (4 / 5 : k) * a * d * e ^ 3 +
      (-(11 / 40) : k) * a * c ^ 3 * d * e +
      (83 / 320 : k) * a * b * c ^ 2 * e ^ 2 +
      (-(819 / 3200) : k) * a ^ 2 * b ^ 2 * c * d * e) * kappaQuarticPowerInnerS06810 a b c d e f g +
      ((32 / 5 : k) * e ^ 4 +
      (-(3 / 80) : k) * a * b ^ 2 * c ^ 4 +
      (-(3 / 1600) : k) * a ^ 2 * b ^ 4 * c ^ 2 +
      (16 / 25 : k) * a * b ^ 2 * c * e ^ 2 +
      (89 / 50 : k) * a * b * c ^ 2 * d * e) * muQuarticPowerInnerS06810 a b c d e f g +
      ((-(32 / 15) : k) * c * e ^ 3 +
      (1 / 1280 : k) * a ^ 2 * b ^ 4 * e +
      (-(317 / 120) : k) * a * b * d * e ^ 2 +
      (-(67 / 320) : k) * a * b ^ 2 * c ^ 2 * e +
      (-(11 / 15) : k) * a * c * d ^ 2 * e +
      (1 / 24 : k) * a * b * c ^ 3 * d +
      (1 / 480 : k) * a ^ 2 * b ^ 3 * c * d) * xiQuarticPowerInnerS06810 a b c d e f g +
      ((-(1 / 40) : k) * a * b ^ 2 * c ^ 3 +
      (-(1 / 800) : k) * a ^ 2 * b ^ 4 * c +
      (9 / 25 : k) * a * b ^ 2 * e ^ 2 +
      (18 / 25 : k) * a * b * c * d * e) * piQuarticPowerInnerS06810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS06810, muQuarticPowerInnerS06810, xiQuarticPowerInnerS06810, piQuarticPowerInnerS06810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `e^6 = 0`, contradiction. -/
theorem quarticPowerInnerS06810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS06810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS06810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS06810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS06810 a b c d e f g = 0)
    (he : e ≠ 0)
    : False := by
  have hid := quarticPowerInnerS06810_identity a b c d e f g
  have hpow : e ^ 6 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  exact he ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S07 (`a^3*b^3*c^3*d^3*f^3`) -/

/-- Face of `κ` on power system 07. -/
def kappaQuarticPowerInnerS07810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * c * f +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 07. -/
def muQuarticPowerInnerS07810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (-(5 / 64) : k) * a * b * f +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 07. -/
def xiQuarticPowerInnerS07810 (a b c d e f g : k) : k :=
  (-(5 / 64) : k) * a * d * f +
      (15 / 256 : k) * a * b * c * d

/-- Face of `π` on power system 07. -/
def piQuarticPowerInnerS07810 (a b c d e f g : k) : k :=
  (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * a * f ^ 2 +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (-(45 / 512) : k) * a * b ^ 2 * c ^ 2 +
      (5 / 32 : k) * a * c * d ^ 2 +
      (5 / 32 : k) * a * b * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^3*b^3*c^3*d^3*f^3 ∈ ⟨faces⟩` on power system 07. -/
theorem quarticPowerInnerS07810_identity (a b c d e f g : k) :
    a ^ 3 * b ^ 3 * c ^ 3 * d ^ 3 * f ^ 3 =
      ((-(4096 / 345) : k) * a ^ 2 * c ^ 2 * d * f ^ 5 +
      (-(512 / 345) : k) * a ^ 3 * b ^ 2 * d * f ^ 5) * kappaQuarticPowerInnerS07810 a b c d e f g +
      ((-(32768 / 345) : k) * a ^ 2 * d * f ^ 6 +
      (14336 / 345 : k) * a ^ 2 * b * c * d * f ^ 5) * muQuarticPowerInnerS07810 a b c d e f g +
      ((16384 / 207 : k) * a ^ 2 * b * f ^ 6 +
      (16384 / 345 : k) * a ^ 2 * d ^ 2 * f ^ 5 +
      (-(16384 / 1035) : k) * a ^ 2 * b ^ 2 * c * f ^ 5 +
      (256 / 15 : k) * a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * f ^ 3 +
      (1024 / 45 : k) * a ^ 2 * b * c * d ^ 2 * f ^ 4) * xiQuarticPowerInnerS07810 a b c d e f g +
      ((4096 / 1035 : k) * a ^ 2 * b * d * f ^ 5) * piQuarticPowerInnerS07810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS07810, muQuarticPowerInnerS07810, xiQuarticPowerInnerS07810, piQuarticPowerInnerS07810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^3*b^3*c^3*d^3*f^3 = 0`, contradiction. -/
theorem quarticPowerInnerS07810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS07810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS07810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS07810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS07810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    : False := by
  have hid := quarticPowerInnerS07810_identity a b c d e f g
  have hpow : a ^ 3 * b ^ 3 * c ^ 3 * d ^ 3 * f ^ 3 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact ha ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hb ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h2)
    · -- the right factor
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h3)
  · -- the right factor
    exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h4)

/-! ## Face system S08 (`c^7`) -/

/-- Face of `κ` on power system 08. -/
def kappaQuarticPowerInnerS08810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 08. -/
def muQuarticPowerInnerS08810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 16 : k) * c * g +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `π` on power system 08. -/
def piQuarticPowerInnerS08810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (-(45 / 512) : k) * a * b ^ 2 * c ^ 2 +
      (5 / 64 : k) * a * b ^ 2 * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `c^7 ∈ ⟨faces⟩` on power system 08. -/
theorem quarticPowerInnerS08810_identity (a b c d e f g : k) :
    c ^ 7 =
      ((-(296 / 15) : k) * a * b * c ^ 3 +
      (-(352 / 15) : k) * a * b * c * g) * kappaQuarticPowerInnerS08810 a b c d e f g +
      ((368 / 15 : k) * c ^ 4 +
      (11264 / 45 : k) * g ^ 2 +
      (-(7424 / 45) : k) * c ^ 2 * g +
      (12 / 5 : k) * a * b ^ 2 * c ^ 2 +
      (704 / 45 : k) * a * b ^ 2 * g) * muQuarticPowerInnerS08810 a b c d e f g +
      ((1504 / 45 : k) * c ^ 3 +
      (-(2816 / 45) : k) * c * g) * piQuarticPowerInnerS08810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS08810, muQuarticPowerInnerS08810, piQuarticPowerInnerS08810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `c^7 = 0`, contradiction. -/
theorem quarticPowerInnerS08810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS08810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS08810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS08810 a b c d e f g = 0)
    (hc : c ≠ 0)
    : False := by
  have hid := quarticPowerInnerS08810_identity a b c d e f g
  have hpow : c ^ 7 = 0 := by
    rw [hkap, hmu, hpi] at hid
    simpa using hid
  exact hc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S09 (`a^2*b^2*c^2*d^2*g^2`) -/

/-- Face of `κ` on power system 09. -/
def kappaQuarticPowerInnerS09810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g

/-- Face of `μ` on power system 09. -/
def muQuarticPowerInnerS09810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `π` on power system 09. -/
def piQuarticPowerInnerS09810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*b^2*c^2*d^2*g^2 ∈ ⟨faces⟩` on power system 09. -/
theorem quarticPowerInnerS09810_identity (a b c d e f g : k) :
    a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * g ^ 2 =
      ((-(128 / 15) : k) * a ^ 2 * b * d ^ 2 * g ^ 2 +
      (-(128 / 33) : k) * a * b * c ^ 3 * g ^ 2 +
      (8192 / 165 : k) * a * b * c * g ^ 3) * kappaQuarticPowerInnerS09810 a b c d e f g +
      ((-(1024 / 15) : k) * a * b ^ 2 * g ^ 3 +
      (1024 / 55 : k) * a * b ^ 2 * c ^ 2 * g ^ 2) * muQuarticPowerInnerS09810 a b c d e f g +
      ((256 / 55 : k) * a * b ^ 2 * c * g ^ 2) * piQuarticPowerInnerS09810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS09810, muQuarticPowerInnerS09810, piQuarticPowerInnerS09810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*b^2*c^2*d^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS09810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS09810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS09810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS09810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS09810_identity a b c d e f g
  have hpow : a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * g ^ 2 = 0 := by
    rw [hkap, hmu, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
    · -- the right factor
      exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)

/-! ## Face system S10 (`e^5`) -/

/-- Face of `κ` on power system 10. -/
def kappaQuarticPowerInnerS10810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * c * f +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 10. -/
def muQuarticPowerInnerS10810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 32 : k) * e ^ 2 +
      (-(5 / 64) : k) * a * b * f +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 10. -/
def xiQuarticPowerInnerS10810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (15 / 512 : k) * a * b ^ 2 * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `e^5 ∈ ⟨faces⟩` on power system 10. -/
theorem quarticPowerInnerS10810_identity (a b c d e f g : k) :
    e ^ 5 =
      ((-(4 / 5) : k) * a * b * c ^ 2 * e +
      (16 / 5 : k) * a * c * e * f) * kappaQuarticPowerInnerS10810 a b c d e f g +
      ((32 / 5 : k) * e ^ 3 +
      (-(64 / 15) : k) * c ^ 3 * e +
      (4 / 15 : k) * a * b ^ 2 * c * e +
      (16 / 5 : k) * a * b * e * f) * muQuarticPowerInnerS10810 a b c d e f g +
      ((64 / 45 : k) * c ^ 4 +
      (-(352 / 45) : k) * c * e ^ 2 +
      (128 / 15 : k) * a * f ^ 2 +
      (-(32 / 9) : k) * a * b * c * f) * xiQuarticPowerInnerS10810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS10810, muQuarticPowerInnerS10810, xiQuarticPowerInnerS10810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `e^5 = 0`, contradiction. -/
theorem quarticPowerInnerS10810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS10810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS10810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS10810 a b c d e f g = 0)
    (he : e ≠ 0)
    : False := by
  have hid := quarticPowerInnerS10810_identity a b c d e f g
  have hpow : e ^ 5 = 0 := by
    rw [hkap, hmu, hxi] at hid
    simpa using hid
  exact he ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S11 (`a^3*b^3*c^3*e^3*g^3`) -/

/-- Face of `κ` on power system 11. -/
def kappaQuarticPowerInnerS11810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `ξ` on power system 11. -/
def xiQuarticPowerInnerS11810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (5 / 16 : k) * e * g +
      (15 / 512 : k) * a * b ^ 2 * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^3*b^3*c^3*e^3*g^3 ∈ ⟨faces⟩` on power system 11. -/
theorem quarticPowerInnerS11810_identity (a b c d e f g : k) :
    a ^ 3 * b ^ 3 * c ^ 3 * e ^ 3 * g ^ 3 =
      ((-(256 / 5) : k) * a ^ 2 * c ^ 3 * e ^ 3 * g ^ 3) * kappaQuarticPowerInnerS11810 a b c d e f g +
      ((256 / 5 : k) * a ^ 2 * b * c ^ 3 * e ^ 2 * g ^ 3) * xiQuarticPowerInnerS11810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS11810, xiQuarticPowerInnerS11810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^3*b^3*c^3*e^3*g^3 = 0`, contradiction. -/
theorem quarticPowerInnerS11810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS11810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS11810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS11810_identity a b c d e f g
  have hpow : a ^ 3 * b ^ 3 * c ^ 3 * e ^ 3 * g ^ 3 = 0 := by
    rw [hkap, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact ha ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hb ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h2)
    · -- the right factor
      exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h3)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h4)

/-! ## Face system S12 (`g^4`) -/

/-- Face of `κ` on power system 12. -/
def kappaQuarticPowerInnerS12810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 12. -/
def muQuarticPowerInnerS12810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 16 : k) * c * g +
      (-(5 / 64) : k) * a * b * f +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 12. -/
def xiQuarticPowerInnerS12810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * f ^ 2 +
      (-(15 / 2048) : k) * a * b ^ 4 +
      (-(5 / 64) : k) * b ^ 2 * g +
      (45 / 512 : k) * b ^ 2 * c ^ 2 +
      (-(25 / 128) : k) * b * c * f

/-- Face of `π` on power system 12. -/
def piQuarticPowerInnerS12810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * a * f ^ 2 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (-(45 / 512) : k) * a * b ^ 2 * c ^ 2 +
      (5 / 64 : k) * a * b ^ 2 * g +
      (5 / 32 : k) * a * b * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `g^4 ∈ ⟨faces⟩` on power system 12. -/
theorem quarticPowerInnerS12810_identity (a b c d e f g : k) :
    g ^ 4 =
      ((-(43 / 280) : k) * a * b * g ^ 2 +
      (-(3 / 8960) : k) * a ^ 2 * b ^ 3 * g +
      (3 / 280 : k) * a * b * c ^ 4 +
      (891 / 4480 : k) * a ^ 2 * b * f ^ 2 +
      (-(183 / 2560) : k) * a ^ 2 * b ^ 2 * c * f +
      (-(47 / 280) : k) * a * c * f * g +
      (29 / 2240 : k) * a * b * c ^ 2 * g) * kappaQuarticPowerInnerS12810 a b c d e f g +
      ((1 / 70 : k) * c ^ 5 +
      (-(127 / 840) : k) * c ^ 3 * g +
      (137 / 105 : k) * c * g ^ 2 +
      (297 / 1120 : k) * a * c * f ^ 2 +
      (-(61 / 640) : k) * a * b * c ^ 2 * f +
      (-(1 / 84) : k) * a * b ^ 2 * c * g +
      (173 / 280 : k) * a * b * f * g) * muQuarticPowerInnerS12810 a b c d e f g +
      ((2 / 105 : k) * a * c ^ 4 +
      (13 / 70 : k) * a * g ^ 2 +
      (99 / 280 : k) * a ^ 2 * f ^ 2 +
      (-(157 / 1680) : k) * a * c ^ 2 * g +
      (-(1 / 2240) : k) * a ^ 2 * b ^ 2 * g +
      (-(61 / 480) : k) * a ^ 2 * b * c * f) * xiQuarticPowerInnerS12810 a b c d e f g +
      ((1 / 105 : k) * c ^ 4 +
      (4 / 5 : k) * g ^ 2 +
      (-(53 / 420) : k) * c ^ 2 * g +
      (99 / 560 : k) * a * f ^ 2 +
      (-(61 / 960) : k) * a * b * c * f) * piQuarticPowerInnerS12810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS12810, muQuarticPowerInnerS12810, xiQuarticPowerInnerS12810, piQuarticPowerInnerS12810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `g^4 = 0`, contradiction. -/
theorem quarticPowerInnerS12810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS12810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS12810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS12810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS12810 a b c d e f g = 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS12810_identity a b c d e f g
  have hpow : g ^ 4 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  exact hg ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S13 (`e^6`) -/

/-- Face of `κ` on power system 13. -/
def kappaQuarticPowerInnerS13810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * d * e +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 13. -/
def muQuarticPowerInnerS13810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (-(5 / 64) : k) * a * b * f

/-- Face of `ξ` on power system 13. -/
def xiQuarticPowerInnerS13810 (a b c d e f g : k) : k :=
  (-(5 / 64) : k) * a * d * f +
      (15 / 512 : k) * a * b ^ 2 * e

/-- Face of `π` on power system 13. -/
def piQuarticPowerInnerS13810 (a b c d e f g : k) : k :=
  (-(5 / 16) : k) * a * f ^ 2 +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (5 / 16 : k) * a * b * d * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `e^6 ∈ ⟨faces⟩` on power system 13. -/
theorem quarticPowerInnerS13810_identity (a b c d e f g : k) :
    e ^ 6 =
      ((20 / 11 : k) * a ^ 2 * f ^ 3 +
      (-(15 / 88) : k) * a ^ 2 * d ^ 3 * e +
      (163 / 110 : k) * a * d * e ^ 3 +
      (1 / 220 : k) * a ^ 2 * b * d * e * f) * kappaQuarticPowerInnerS13810 a b c d e f g +
      ((32 / 5 : k) * e ^ 4 +
      (-(15 / 11) : k) * a * d ^ 2 * e ^ 2 +
      (5 / 22 : k) * a ^ 2 * b ^ 2 * f ^ 2 +
      (-(5 / 44) : k) * a ^ 2 * b * d ^ 2 * f +
      (16 / 5 : k) * a * b * e ^ 2 * f) * muQuarticPowerInnerS13810 a b c d e f g +
      ((5 / 88 : k) * a ^ 2 * b * d ^ 3 +
      (1208 / 165 : k) * a * e * f ^ 2 +
      (-(163 / 330) : k) * a * b * d * e ^ 2) * xiQuarticPowerInnerS13810 a b c d e f g +
      ((-(2 / 165) : k) * a * d * e * f) * piQuarticPowerInnerS13810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS13810, muQuarticPowerInnerS13810, xiQuarticPowerInnerS13810, piQuarticPowerInnerS13810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `e^6 = 0`, contradiction. -/
theorem quarticPowerInnerS13810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS13810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS13810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS13810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS13810 a b c d e f g = 0)
    (he : e ≠ 0)
    : False := by
  have hid := quarticPowerInnerS13810_identity a b c d e f g
  have hpow : e ^ 6 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  exact he ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S14 (`g^4`) -/

/-- Face of `κ` on power system 14. -/
def kappaQuarticPowerInnerS14810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 16 : k) * d * e +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `ξ` on power system 14. -/
def xiQuarticPowerInnerS14810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * e * g +
      (15 / 512 : k) * a * b ^ 2 * e

/-- Face of `π` on power system 14. -/
def piQuarticPowerInnerS14810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (5 / 64 : k) * a * b ^ 2 * g +
      (5 / 16 : k) * a * b * d * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `g^4 ∈ ⟨faces⟩` on power system 14. -/
theorem quarticPowerInnerS14810_identity (a b c d e f g : k) :
    g ^ 4 =
      ((-(3 / 640) : k) * a ^ 2 * b ^ 3 * g +
      (-(1 / 4) : k) * a * b * g ^ 2 +
      (21 / 440 : k) * a ^ 2 * b ^ 2 * d * e) * kappaQuarticPowerInnerS14810 a b c d e f g +
      ((-(7 / 704) : k) * a ^ 2 * b ^ 3 * d +
      (-(79 / 220) : k) * a * b * d * g) * xiQuarticPowerInnerS14810 a b c d e f g +
      ((4 / 5 : k) * g ^ 2 +
      (1 / 80 : k) * a * b ^ 2 * g +
      (-(21 / 440) : k) * a * b * d * e) * piQuarticPowerInnerS14810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS14810, xiQuarticPowerInnerS14810, piQuarticPowerInnerS14810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `g^4 = 0`, contradiction. -/
theorem quarticPowerInnerS14810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS14810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS14810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS14810 a b c d e f g = 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS14810_identity a b c d e f g
  have hpow : g ^ 4 = 0 := by
    rw [hkap, hxi, hpi] at hid
    simpa using hid
  exact hg ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S15 (`e^5`) -/

/-- Face of `κ` on power system 15. -/
def kappaQuarticPowerInnerS15810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * c * f +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 15. -/
def muQuarticPowerInnerS15810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2

/-- Face of `ξ` on power system 15. -/
def xiQuarticPowerInnerS15810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (-(5 / 64) : k) * a * d * f

/-- Face of `π` on power system 15. -/
def piQuarticPowerInnerS15810 (a b c d e f g : k) : k :=
  (15 / 256 : k) * c ^ 4 +
      (-(5 / 8) : k) * c * e ^ 2 +
      (-(5 / 16) : k) * a * f ^ 2 +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `e^5 ∈ ⟨faces⟩` on power system 15. -/
theorem quarticPowerInnerS15810_identity (a b c d e f g : k) :
    e ^ 5 =
      ((1 / 8 : k) * a * c ^ 3 * d +
      (4 / 5 : k) * a * d * e ^ 2 +
      (-1 : k) * a * c * e * f) * kappaQuarticPowerInnerS15810 a b c d e f g +
      ((32 / 5 : k) * e ^ 3 +
      (-3 : k) * c ^ 3 * e) * muQuarticPowerInnerS15810 a b c d e f g +
      ((1 / 2 : k) * c ^ 4 +
      (-(4 / 5) : k) * c * e ^ 2) * xiQuarticPowerInnerS15810 a b c d e f g +
      ((-1 : k) * c ^ 2 * e) * piQuarticPowerInnerS15810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS15810, muQuarticPowerInnerS15810, xiQuarticPowerInnerS15810, piQuarticPowerInnerS15810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `e^5 = 0`, contradiction. -/
theorem quarticPowerInnerS15810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS15810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS15810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS15810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS15810 a b c d e f g = 0)
    (he : e ≠ 0)
    : False := by
  have hid := quarticPowerInnerS15810_identity a b c d e f g
  have hpow : e ^ 5 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  exact he ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S16 (`a*b*c*f*g`) -/

/-- Face of `κ` on power system 16. -/
def kappaQuarticPowerInnerS16810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f

/-- Face of `μ` on power system 16. -/
def muQuarticPowerInnerS16810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * c * g +
      (-(5 / 64) : k) * a * b * f

/-- Face of `π` on power system 16. -/
def piQuarticPowerInnerS16810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (-(5 / 16) : k) * a * f ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*b*c*f*g ∈ ⟨faces⟩` on power system 16. -/
theorem quarticPowerInnerS16810_identity (a b c d e f g : k) :
    a * b * c * f * g =
      ((8 / 5 : k) * a * c * f) * kappaQuarticPowerInnerS16810 a b c d e f g +
      ((-(32 / 5) : k) * c * g) * muQuarticPowerInnerS16810 a b c d e f g +
      ((8 / 5 : k) * c ^ 2) * piQuarticPowerInnerS16810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS16810, muQuarticPowerInnerS16810, piQuarticPowerInnerS16810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*b*c*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS16810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS16810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS16810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS16810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS16810_identity a b c d e f g
  have hpow : a * b * c * f * g = 0 := by
    rw [hkap, hmu, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact ha h1
        · -- the right factor
          exact hb h1
      · -- the right factor
        exact hc h2
    · -- the right factor
      exact hf h3
  · -- the right factor
    exact hg h4

/-! ## Face system S17 (`a*b*c*e*f*g`) -/

/-- Face of `κ` on power system 17. -/
def kappaQuarticPowerInnerS17810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f

/-- Face of `ν` on power system 17. -/
def nuQuarticPowerInnerS17810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * e * f +
      (-(5 / 128) : k) * a * b * g +
      (-(5 / 128) : k) * a * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*b*c*e*f*g ∈ ⟨faces⟩` on power system 17. -/
theorem quarticPowerInnerS17810_identity (a b c d e f g : k) :
    a * b * c * e * f * g =
      ((2 / 5 : k) * a ^ 2 * b * c * g) * kappaQuarticPowerInnerS17810 a b c d e f g +
      ((16 / 5 : k) * a * b * c * g) * nuQuarticPowerInnerS17810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS17810, nuQuarticPowerInnerS17810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*b*c*e*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS17810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS17810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS17810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS17810_identity a b c d e f g
  have hpow : a * b * c * e * f * g = 0 := by
    rw [hkap, hnu] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha h1
          · -- the right factor
            exact hb h1
        · -- the right factor
          exact hc h2
      · -- the right factor
        exact he h3
    · -- the right factor
      exact hf h4
  · -- the right factor
    exact hg h5

/-! ## Face system S18 (`a*b*e*g`) -/

/-- Face of `κ` on power system 18. -/
def kappaQuarticPowerInnerS18810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `ξ` on power system 18. -/
def xiQuarticPowerInnerS18810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * e * g +
      (15 / 512 : k) * a * b ^ 2 * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*b*e*g ∈ ⟨faces⟩` on power system 18. -/
theorem quarticPowerInnerS18810_identity (a b c d e f g : k) :
    a * b * e * g =
      ((24 / 5 : k) * a * e) * kappaQuarticPowerInnerS18810 a b c d e f g +
      ((-(8 / 5) : k) * a * b) * xiQuarticPowerInnerS18810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS18810, xiQuarticPowerInnerS18810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*b*e*g = 0`, contradiction. -/
theorem quarticPowerInnerS18810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS18810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS18810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS18810_identity a b c d e f g
  have hpow : a * b * e * g = 0 := by
    rw [hkap, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h3 | h3
  · -- the left factor
    rcases (mul_eq_zero.mp h3) with h2 | h2
    · -- the left factor
      rcases (mul_eq_zero.mp h2) with h1 | h1
      · -- the left factor
        exact ha h1
      · -- the right factor
        exact hb h1
    · -- the right factor
      exact he h2
  · -- the right factor
    exact hg h3

/-! ## Face system S19 (`f^3`) -/

/-- Face of `κ` on power system 19. -/
def kappaQuarticPowerInnerS19810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 19. -/
def muQuarticPowerInnerS19810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * d * f +
      (-(5 / 64) : k) * a * b * f

/-- Face of `ν` on power system 19. -/
def nuQuarticPowerInnerS19810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * d * g +
      (5 / 16 : k) * e * f +
      (-(5 / 128) : k) * a * b * g +
      (-(5 / 128) : k) * a * d * e

/-- Face of `ξ` on power system 19. -/
def xiQuarticPowerInnerS19810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * f ^ 2 +
      (5 / 16 : k) * e * g +
      (-(5 / 64) : k) * a * d * f

/-- Face of `π` on power system 19. -/
def piQuarticPowerInnerS19810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (-(5 / 16) : k) * a * f ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `f^3 ∈ ⟨faces⟩` on power system 19. -/
theorem quarticPowerInnerS19810_identity (a b c d e f g : k) :
    f ^ 3 =
      ((-(4 / 15) : k) * a ^ 2 * e +
      (52 / 15 : k) * a * g) * kappaQuarticPowerInnerS19810 a b c d e f g +
      ((64 / 15 : k) * a * f) * muQuarticPowerInnerS19810 a b c d e f g +
      ((-(32 / 5) : k) * g +
      (-(32 / 15) : k) * a * e) * nuQuarticPowerInnerS19810 a b c d e f g +
      ((32 / 5 : k) * f +
      (-(32 / 15) : k) * a * d) * xiQuarticPowerInnerS19810 a b c d e f g +
      ((8 / 5 : k) * d +
      (-(16 / 15) : k) * a * b) * piQuarticPowerInnerS19810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS19810, muQuarticPowerInnerS19810, nuQuarticPowerInnerS19810, xiQuarticPowerInnerS19810, piQuarticPowerInnerS19810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `f^3 = 0`, contradiction. -/
theorem quarticPowerInnerS19810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS19810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS19810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS19810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS19810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS19810 a b c d e f g = 0)
    (hf : f ≠ 0)
    : False := by
  have hid := quarticPowerInnerS19810_identity a b c d e f g
  have hpow : f ^ 3 = 0 := by
    rw [hkap, hmu, hnu, hxi, hpi] at hid
    simpa using hid
  exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S20 (`a^2*b^2*d^2*e^2*f^2*g^2`) -/

/-- Face of `μ` on power system 20. -/
def muQuarticPowerInnerS20810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (-(5 / 64) : k) * a * b * f

/-- Face of `ξ` on power system 20. -/
def xiQuarticPowerInnerS20810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * e * g +
      (-(5 / 64) : k) * a * d * f

/-- Face of `π` on power system 20. -/
def piQuarticPowerInnerS20810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (-(5 / 16) : k) * a * f ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*b^2*d^2*e^2*f^2*g^2 ∈ ⟨faces⟩` on power system 20. -/
theorem quarticPowerInnerS20810_identity (a b c d e f g : k) :
    a ^ 2 * b ^ 2 * d ^ 2 * e ^ 2 * f ^ 2 * g ^ 2 =
      ((-(256 / 5) : k) * b * e ^ 4 * f * g ^ 2) * muQuarticPowerInnerS20810 a b c d e f g +
      ((-(256 / 5) : k) * b ^ 2 * e ^ 3 * g ^ 3 +
      (128 / 5 : k) * b * d * e ^ 4 * g ^ 2 +
      (128 / 5 : k) * b * e ^ 5 * f * g +
      (-(64 / 5) : k) * a * b ^ 2 * d * e ^ 2 * f * g ^ 2) * xiQuarticPowerInnerS20810 a b c d e f g +
      ((64 / 5 : k) * b ^ 2 * e ^ 4 * g ^ 2 +
      (-(32 / 5) : k) * b * d * e ^ 5 * g) * piQuarticPowerInnerS20810 a b c d e f g := by
  simp only [muQuarticPowerInnerS20810, xiQuarticPowerInnerS20810, piQuarticPowerInnerS20810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*b^2*d^2*e^2*f^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS20810_false (a b c d e f g : k)
    (hmu : muQuarticPowerInnerS20810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS20810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS20810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS20810_identity a b c d e f g
  have hpow : a ^ 2 * b ^ 2 * d ^ 2 * e ^ 2 * f ^ 2 * g ^ 2 = 0 := by
    rw [hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
          · -- the right factor
            exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
      · -- the right factor
        exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
    · -- the right factor
      exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h5)

/-! ## Face system S21 (`g^3`) -/

/-- Face of `κ` on power system 21. -/
def kappaQuarticPowerInnerS21810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * c * f +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 21. -/
def muQuarticPowerInnerS21810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g +
      (5 / 16 : k) * d * f

/-- Face of `ν` on power system 21. -/
def nuQuarticPowerInnerS21810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * d * g +
      (5 / 16 : k) * e * f +
      (-(5 / 128) : k) * a * c * f +
      (-(5 / 128) : k) * a * d * e

/-- Face of `ξ` on power system 21. -/
def xiQuarticPowerInnerS21810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * f ^ 2 +
      (5 / 16 : k) * e * g +
      (-(5 / 64) : k) * a * d * f

/-- Face of `π` on power system 21. -/
def piQuarticPowerInnerS21810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (-(5 / 16) : k) * a * f ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `g^3 ∈ ⟨faces⟩` on power system 21. -/
theorem quarticPowerInnerS21810_identity (a b c d e f g : k) :
    g ^ 3 =
      ((-(19 / 100) : k) * a ^ 3 * f +
      (1 / 100 : k) * a ^ 4 * d) * kappaQuarticPowerInnerS21810 a b c d e f g +
      ((16 / 25 : k) * a ^ 2 * g) * muQuarticPowerInnerS21810 a b c d e f g +
      ((-(6 / 25) : k) * a ^ 2 * f +
      (2 / 25 : k) * a ^ 3 * d) * nuQuarticPowerInnerS21810 a b c d e f g +
      ((-(8 / 25) : k) * a ^ 2 * e +
      (8 / 5 : k) * a * g) * xiQuarticPowerInnerS21810 a b c d e f g +
      ((4 / 5 : k) * g +
      (-(4 / 25) : k) * a ^ 2 * c +
      (-(2 / 5) : k) * a * e) * piQuarticPowerInnerS21810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS21810, muQuarticPowerInnerS21810, nuQuarticPowerInnerS21810, xiQuarticPowerInnerS21810, piQuarticPowerInnerS21810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `g^3 = 0`, contradiction. -/
theorem quarticPowerInnerS21810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS21810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS21810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS21810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS21810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS21810 a b c d e f g = 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS21810_identity a b c d e f g
  have hpow : g ^ 3 = 0 := by
    rw [hkap, hmu, hnu, hxi, hpi] at hid
    simpa using hid
  exact hg ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S22 (`a^2*c^2*d^2*e^2*f^2*g^2`) -/

/-- Face of `μ` on power system 22. -/
def muQuarticPowerInnerS22810 (a b c d e f g : k) : k :=
  (5 / 32 : k) * e ^ 2 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `ξ` on power system 22. -/
def xiQuarticPowerInnerS22810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * e * g +
      (-(5 / 64) : k) * a * d * f

/-- Face of `π` on power system 22. -/
def piQuarticPowerInnerS22810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (-(5 / 16) : k) * a * f ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*c^2*d^2*e^2*f^2*g^2 ∈ ⟨faces⟩` on power system 22. -/
theorem quarticPowerInnerS22810_identity (a b c d e f g : k) :
    a ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * f ^ 2 * g ^ 2 =
      ((256 / 5 : k) * c * e ^ 4 * g ^ 3) * muQuarticPowerInnerS22810 a b c d e f g +
      ((-(256 / 5) : k) * c ^ 2 * e ^ 3 * g ^ 3 +
      (-(128 / 5) : k) * c * e ^ 5 * g ^ 2 +
      (-(64 / 5) : k) * a * c ^ 2 * d * e ^ 2 * f * g ^ 2 +
      (-(32 / 5) : k) * a * c * d * e ^ 4 * f * g) * xiQuarticPowerInnerS22810 a b c d e f g +
      ((8 / 5 : k) * a * c * d ^ 2 * e ^ 4 * g) * piQuarticPowerInnerS22810 a b c d e f g := by
  simp only [muQuarticPowerInnerS22810, xiQuarticPowerInnerS22810, piQuarticPowerInnerS22810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*c^2*d^2*e^2*f^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS22810_false (a b c d e f g : k)
    (hmu : muQuarticPowerInnerS22810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS22810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS22810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS22810_identity a b c d e f g
  have hpow : a ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * f ^ 2 * g ^ 2 = 0 := by
    rw [hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
          · -- the right factor
            exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
      · -- the right factor
        exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
    · -- the right factor
      exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h5)

/-! ## Face system S23 (`a*b*c*d*e*f*g`) -/

/-- Face of `κ` on power system 23. -/
def kappaQuarticPowerInnerS23810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f +
      (5 / 16 : k) * d * e

/-- Face of `ν` on power system 23. -/
def nuQuarticPowerInnerS23810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * d * g +
      (5 / 16 : k) * e * f +
      (-(5 / 128) : k) * a * b * g +
      (-(5 / 128) : k) * a * c * f +
      (-(5 / 128) : k) * a * d * e

/-- Face of `ο` on power system 23. -/
def omicronQuarticPowerInnerS23810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * f * g +
      (-(5 / 128) : k) * a * d * g +
      (-(5 / 128) : k) * a * e * f +
      (-(5 / 2048) : k) * a ^ 2 * b * g +
      (-(5 / 2048) : k) * a ^ 2 * c * f +
      (-(5 / 2048) : k) * a ^ 2 * d * e

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*b*c*d*e*f*g ∈ ⟨faces⟩` on power system 23. -/
theorem quarticPowerInnerS23810_identity (a b c d e f g : k) :
    a * b * c * d * e * f * g =
      ((-(3 / 40) : k) * a ^ 3 * b * c ^ 2 * f +
      (-(3 / 40) : k) * a ^ 3 * b ^ 2 * c * g +
      (16 / 5 : k) * a * b * c * f * g) * kappaQuarticPowerInnerS23810 a b c d e f g +
      ((-(2 / 5) : k) * a ^ 2 * b * c ^ 2 * f +
      (-(2 / 5) : k) * a ^ 2 * b ^ 2 * c * g) * nuQuarticPowerInnerS23810 a b c d e f g +
      ((-(16 / 5) : k) * a * b * c ^ 2 * f +
      (-(16 / 5) : k) * a * b ^ 2 * c * g) * omicronQuarticPowerInnerS23810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS23810, nuQuarticPowerInnerS23810, omicronQuarticPowerInnerS23810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*b*c*d*e*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS23810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS23810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS23810 a b c d e f g = 0)
    (homi : omicronQuarticPowerInnerS23810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS23810_identity a b c d e f g
  have hpow : a * b * c * d * e * f * g = 0 := by
    rw [hkap, hnu, homi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h6 | h6
  · -- the left factor
    rcases (mul_eq_zero.mp h6) with h5 | h5
    · -- the left factor
      rcases (mul_eq_zero.mp h5) with h4 | h4
      · -- the left factor
        rcases (mul_eq_zero.mp h4) with h3 | h3
        · -- the left factor
          rcases (mul_eq_zero.mp h3) with h2 | h2
          · -- the left factor
            rcases (mul_eq_zero.mp h2) with h1 | h1
            · -- the left factor
              exact ha h1
            · -- the right factor
              exact hb h1
          · -- the right factor
            exact hc h2
        · -- the right factor
          exact hd h3
      · -- the right factor
        exact he h4
    · -- the right factor
      exact hf h5
  · -- the right factor
    exact hg h6

/-! ## Face system S25 (`a^2*b^2*c^2*d^2*e^2*g^2`) -/

/-- Face of `κ` on power system 25. -/
def kappaQuarticPowerInnerS25810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 25. -/
def muQuarticPowerInnerS25810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `ξ` on power system 25. -/
def xiQuarticPowerInnerS25810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (5 / 16 : k) * e * g +
      (15 / 256 : k) * a * b * c * d

/-- Face of `π` on power system 25. -/
def piQuarticPowerInnerS25810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*b^2*c^2*d^2*e^2*g^2 ∈ ⟨faces⟩` on power system 25. -/
theorem quarticPowerInnerS25810_identity (a b c d e f g : k) :
    a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 =
      ((-(9728 / 1925) : k) * a ^ 2 * b ^ 3 * g ^ 4 +
      (2432 / 1925 : k) * a ^ 2 * b ^ 3 * c ^ 2 * g ^ 3 +
      (-(2176 / 1155) : k) * a * c ^ 3 * d * e ^ 3 * g +
      (-(128 / 15) : k) * a ^ 2 * b * d ^ 2 * e ^ 2 * g ^ 2 +
      (-(16 / 385) : k) * a ^ 3 * b ^ 3 * c * d ^ 2 * g ^ 2 +
      (128 / 15 : k) * a ^ 2 * b ^ 2 * d * e * g ^ 3 +
      (145408 / 5775 : k) * a * c * d * e ^ 3 * g ^ 2) * kappaQuarticPowerInnerS25810 a b c d e f g +
      ((-(22429696 / 525525) : k) * c * e ^ 4 * g ^ 2 +
      (5692416 / 175175 : k) * c ^ 3 * e ^ 4 * g +
      (-(3648 / 1925) : k) * a ^ 2 * b ^ 4 * c * g ^ 3 +
      (-(1024 / 15) : k) * a * b * d * e ^ 3 * g ^ 2 +
      (-(470016 / 175175) : k) * a * b * c ^ 2 * d * e ^ 3 * g +
      (1152 / 1925 : k) * a ^ 2 * b ^ 3 * c * d * e * g ^ 2) * muQuarticPowerInnerS25810 a b c d e f g +
      ((16384 / 65 : k) * e ^ 3 * g ^ 3 +
      (-(474368 / 105105) : k) * c ^ 4 * e ^ 3 * g +
      (4141056 / 175175 : k) * c ^ 2 * e ^ 3 * g ^ 2 +
      (-(25472 / 5775) : k) * a ^ 2 * b ^ 3 * d * g ^ 3 +
      (-(32 / 385) : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g ^ 2 +
      (34816 / 35035 : k) * a * c * d ^ 2 * e ^ 3 * g) * xiQuarticPowerInnerS25810 a b c d e f g +
      ((-(4096 / 65) : k) * e ^ 4 * g ^ 2 +
      (2432 / 1925 : k) * a ^ 2 * b ^ 4 * g ^ 3 +
      (948736 / 75075 : k) * c ^ 2 * e ^ 4 * g +
      (64 / 275 : k) * a ^ 2 * b ^ 3 * d * e * g ^ 2 +
      (-(26112 / 25025) : k) * a * b * c * d * e ^ 3 * g) * piQuarticPowerInnerS25810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS25810, muQuarticPowerInnerS25810, xiQuarticPowerInnerS25810, piQuarticPowerInnerS25810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*b^2*c^2*d^2*e^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS25810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS25810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS25810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS25810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS25810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS25810_identity a b c d e f g
  have hpow : a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
          · -- the right factor
            exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
      · -- the right factor
        exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
    · -- the right factor
      exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h5)

/-! ## Face system S26 (`a^2*b^2*c^2*d^2*e^2*g^2`) -/

/-- Face of `κ` on power system 26. -/
def kappaQuarticPowerInnerS26810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * d * e

/-- Face of `ν` on power system 26. -/
def nuQuarticPowerInnerS26810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * d +
      (5 / 16 : k) * d * g +
      (-(5 / 128) : k) * a * b * g +
      (-(5 / 128) : k) * a * d * e +
      (15 / 1024 : k) * a * b * c ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^2*b^2*c^2*d^2*e^2*g^2 ∈ ⟨faces⟩` on power system 26. -/
theorem quarticPowerInnerS26810_identity (a b c d e f g : k) :
    a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 =
      ((-(16 / 15) : k) * a ^ 3 * b ^ 3 * e * g ^ 3 +
      (-(16 / 15) : k) * a ^ 3 * b ^ 2 * d * e ^ 2 * g ^ 2 +
      (128 / 15 : k) * a ^ 2 * b ^ 2 * d * e * g ^ 3) * kappaQuarticPowerInnerS26810 a b c d e f g +
      ((-(128 / 15) : k) * a ^ 2 * b ^ 3 * e * g ^ 3 +
      (-(128 / 15) : k) * a ^ 2 * b ^ 2 * d * e ^ 2 * g ^ 2) * nuQuarticPowerInnerS26810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS26810, nuQuarticPowerInnerS26810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^2*b^2*c^2*d^2*e^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS26810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS26810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS26810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS26810_identity a b c d e f g
  have hpow : a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 = 0 := by
    rw [hkap, hnu] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
          · -- the right factor
            exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
      · -- the right factor
        exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
    · -- the right factor
      exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h5)

/-! ## Face system S27 (`b^2*c^2*d^2*e^2*g^2`) -/

/-- Face of `κ` on power system 27. -/
def kappaQuarticPowerInnerS27810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * d * e

/-- Face of `ν` on power system 27. -/
def nuQuarticPowerInnerS27810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * d +
      (5 / 16 : k) * d * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `b^2*c^2*d^2*e^2*g^2 ∈ ⟨faces⟩` on power system 27. -/
theorem quarticPowerInnerS27810_identity (a b c d e f g : k) :
    b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 =
      ((128 / 15 : k) * b ^ 2 * d * e * g ^ 3) * kappaQuarticPowerInnerS27810 a b c d e f g +
      ((-(128 / 15) : k) * b ^ 3 * e * g ^ 3 +
      (-(128 / 15) : k) * b ^ 2 * d * e ^ 2 * g ^ 2) * nuQuarticPowerInnerS27810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS27810, nuQuarticPowerInnerS27810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `b^2*c^2*d^2*e^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS27810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS27810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS27810 a b c d e f g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS27810_identity a b c d e f g
  have hpow : b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 = 0 := by
    rw [hkap, hnu] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
    · -- the right factor
      exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)

/-! ## Face system S28 (`b^2*c^2*d^2*e^2*g^2`) -/

/-- Face of `κ` on power system 28. -/
def kappaQuarticPowerInnerS28810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * d * e

/-- Face of `ξ` on power system 28. -/
def xiQuarticPowerInnerS28810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (5 / 16 : k) * e * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `b^2*c^2*d^2*e^2*g^2 ∈ ⟨faces⟩` on power system 28. -/
theorem quarticPowerInnerS28810_identity (a b c d e f g : k) :
    b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 =
      ((128 / 15 : k) * b ^ 2 * d * e * g ^ 3) * kappaQuarticPowerInnerS28810 a b c d e f g +
      ((-(128 / 15) : k) * b ^ 3 * d * g ^ 3 +
      (-(128 / 15) : k) * b ^ 2 * d ^ 2 * e * g ^ 2) * xiQuarticPowerInnerS28810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS28810, xiQuarticPowerInnerS28810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `b^2*c^2*d^2*e^2*g^2 = 0`, contradiction. -/
theorem quarticPowerInnerS28810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS28810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS28810 a b c d e f g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS28810_identity a b c d e f g
  have hpow : b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * g ^ 2 = 0 := by
    rw [hkap, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1)
      · -- the right factor
        exact hd ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h2)
    · -- the right factor
      exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h3)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h4)

/-! ## Face system S29 (`a^3*b^3*c^3*d^3*f^3*g^3`) -/

/-- Face of `κ` on power system 29. -/
def kappaQuarticPowerInnerS29810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 29. -/
def muQuarticPowerInnerS29810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 16 : k) * c * g +
      (-(5 / 64) : k) * a * b * f +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 29. -/
def xiQuarticPowerInnerS29810 (a b c d e f g : k) : k :=
  (-(5 / 64) : k) * a * d * f +
      (15 / 256 : k) * a * b * c * d

/-- Face of `π` on power system 29. -/
def piQuarticPowerInnerS29810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * a * f ^ 2 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (-(45 / 512) : k) * a * b ^ 2 * c ^ 2 +
      (5 / 64 : k) * a * b ^ 2 * g +
      (5 / 32 : k) * a * b * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^3*b^3*c^3*d^3*f^3*g^3 ∈ ⟨faces⟩` on power system 29. -/
theorem quarticPowerInnerS29810_identity (a b c d e f g : k) :
    a ^ 3 * b ^ 3 * c ^ 3 * d ^ 3 * f ^ 3 * g ^ 3 =
      ((32 / 15 : k) * a ^ 3 * b * d ^ 3 * f ^ 4 * g ^ 3 +
      (128 / 15 : k) * a ^ 2 * c * d ^ 3 * f ^ 3 * g ^ 4) * kappaQuarticPowerInnerS29810 a b c d e f g +
      ((-(128 / 15) : k) * a ^ 2 * c * d ^ 3 * f ^ 4 * g ^ 3 +
      (128 / 15 : k) * a ^ 2 * b * d ^ 3 * f ^ 3 * g ^ 4) * muQuarticPowerInnerS29810 a b c d e f g +
      ((-(4096 / 45) : k) * a * d ^ 2 * f ^ 3 * g ^ 5 +
      (1024 / 45 : k) * a ^ 2 * d ^ 2 * f ^ 5 * g ^ 3 +
      (-(256 / 45) : k) * a ^ 2 * b ^ 2 * d ^ 2 * f ^ 3 * g ^ 4 +
      (1024 / 45 : k) * a * c ^ 2 * d ^ 2 * f ^ 3 * g ^ 4 +
      (256 / 15 : k) * a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * f ^ 3 * g ^ 3 +
      (1024 / 45 : k) * a ^ 2 * b * c * d ^ 2 * f ^ 4 * g ^ 3) * xiQuarticPowerInnerS29810 a b c d e f g +
      ((-(256 / 45) : k) * a ^ 2 * d ^ 3 * f ^ 4 * g ^ 3) * piQuarticPowerInnerS29810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS29810, muQuarticPowerInnerS29810, xiQuarticPowerInnerS29810, piQuarticPowerInnerS29810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^3*b^3*c^3*d^3*f^3*g^3 = 0`, contradiction. -/
theorem quarticPowerInnerS29810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS29810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS29810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS29810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS29810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS29810_identity a b c d e f g
  have hpow : a ^ 3 * b ^ 3 * c ^ 3 * d ^ 3 * f ^ 3 * g ^ 3 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
          · -- the right factor
            exact hb ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h2)
      · -- the right factor
        exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h3)
    · -- the right factor
      exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h4)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h5)

/-! ## Face system S30 (`a*b*c*d*f*g`) -/

/-- Face of `κ` on power system 30. -/
def kappaQuarticPowerInnerS30810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f

/-- Face of `μ` on power system 30. -/
def muQuarticPowerInnerS30810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `ξ` on power system 30. -/
def xiQuarticPowerInnerS30810 (a b c d e f g : k) : k :=
  (-(5 / 64) : k) * a * d * f +
      (15 / 256 : k) * a * b * c * d

/-- Face of `π` on power system 30. -/
def piQuarticPowerInnerS30810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*b*c*d*f*g ∈ ⟨faces⟩` on power system 30. -/
theorem quarticPowerInnerS30810_identity (a b c d e f g : k) :
    a * b * c * d * f * g =
      ((-(144 / 35) : k) * a * b * d * g +
      (-(6 / 7) : k) * a * b * c ^ 2 * d +
      (16 / 7 : k) * a * c * d * f) * kappaQuarticPowerInnerS30810 a b c d e f g +
      ((144 / 35 : k) * a * b ^ 2 * c * d) * muQuarticPowerInnerS30810 a b c d e f g +
      ((64 / 7 : k) * c ^ 2 * f +
      (-(704 / 35) : k) * b * c * g) * xiQuarticPowerInnerS30810 a b c d e f g +
      ((36 / 35 : k) * a * b ^ 2 * d) * piQuarticPowerInnerS30810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS30810, muQuarticPowerInnerS30810, xiQuarticPowerInnerS30810, piQuarticPowerInnerS30810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*b*c*d*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS30810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS30810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS30810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS30810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS30810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS30810_identity a b c d e f g
  have hpow : a * b * c * d * f * g = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha h1
          · -- the right factor
            exact hb h1
        · -- the right factor
          exact hc h2
      · -- the right factor
        exact hd h3
    · -- the right factor
      exact hf h4
  · -- the right factor
    exact hg h5

/-! ## Face system S31 (`a*b*c*d*f*g`) -/

/-- Face of `κ` on power system 31. -/
def kappaQuarticPowerInnerS31810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f

/-- Face of `ν` on power system 31. -/
def nuQuarticPowerInnerS31810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * d +
      (5 / 16 : k) * d * g +
      (-(5 / 128) : k) * a * b * g +
      (-(5 / 128) : k) * a * c * f +
      (15 / 1024 : k) * a * b * c ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*b*c*d*f*g ∈ ⟨faces⟩` on power system 31. -/
theorem quarticPowerInnerS31810_identity (a b c d e f g : k) :
    a * b * c * d * f * g =
      ((-(2 / 5) : k) * a ^ 2 * b ^ 2 * g +
      (16 / 5 : k) * a * b * d * g) * kappaQuarticPowerInnerS31810 a b c d e f g +
      ((-(16 / 5) : k) * a * b ^ 2 * g) * nuQuarticPowerInnerS31810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS31810, nuQuarticPowerInnerS31810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*b*c*d*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS31810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS31810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS31810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS31810_identity a b c d e f g
  have hpow : a * b * c * d * f * g = 0 := by
    rw [hkap, hnu] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha h1
          · -- the right factor
            exact hb h1
        · -- the right factor
          exact hc h2
      · -- the right factor
        exact hd h3
    · -- the right factor
      exact hf h4
  · -- the right factor
    exact hg h5

/-! ## Face system S32 (`a^3*b^3*c^3*e^3*f^3*g^3`) -/

/-- Face of `κ` on power system 32. -/
def kappaQuarticPowerInnerS32810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f +
      (5 / 512 : k) * a * b ^ 3

/-- Face of `μ` on power system 32. -/
def muQuarticPowerInnerS32810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (5 / 16 : k) * c * g +
      (-(5 / 64) : k) * a * b * f +
      (15 / 512 : k) * a * b ^ 2 * c

/-- Face of `ξ` on power system 32. -/
def xiQuarticPowerInnerS32810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (5 / 16 : k) * e * g +
      (15 / 512 : k) * a * b ^ 2 * e

/-- Face of `π` on power system 32. -/
def piQuarticPowerInnerS32810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * a * f ^ 2 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (15 / 4096 : k) * a ^ 2 * b ^ 4 +
      (-(45 / 512) : k) * a * b ^ 2 * c ^ 2 +
      (5 / 64 : k) * a * b ^ 2 * g +
      (5 / 32 : k) * a * b * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a^3*b^3*c^3*e^3*f^3*g^3 ∈ ⟨faces⟩` on power system 32. -/
theorem quarticPowerInnerS32810_identity (a b c d e f g : k) :
    a ^ 3 * b ^ 3 * c ^ 3 * e ^ 3 * f ^ 3 * g ^ 3 =
      ((-(14336 / 135) : k) * a * c * e ^ 3 * f * g ^ 6 +
      (-(9856 / 135) : k) * a ^ 2 * b * e ^ 3 * f ^ 2 * g ^ 5 +
      (-(248 / 45) : k) * a ^ 3 * b ^ 3 * e ^ 3 * f ^ 2 * g ^ 4 +
      (-(64 / 5) : k) * a ^ 3 * b * e ^ 3 * f ^ 4 * g ^ 3 +
      (12 / 5 : k) * a ^ 4 * b ^ 3 * e ^ 3 * f ^ 4 * g ^ 2 +
      (2176 / 45 : k) * a ^ 2 * c * e ^ 3 * f ^ 3 * g ^ 4 +
      (-(256 / 45) : k) * a ^ 2 * b ^ 2 * c * e ^ 3 * f * g ^ 5 +
      (992 / 45 : k) * a ^ 2 * b * c ^ 2 * e ^ 3 * f ^ 2 * g ^ 4) * kappaQuarticPowerInnerS32810 a b c d e f g +
      ((-(7936 / 45) : k) * a * c ^ 3 * e ^ 3 * f ^ 2 * g ^ 4 +
      (-(3968 / 45) : k) * a ^ 2 * b * e ^ 3 * f ^ 3 * g ^ 4 +
      (-(2048 / 27) : k) * a * b * e ^ 3 * f * g ^ 6 +
      (-(256 / 5) : k) * a ^ 2 * c * e ^ 3 * f ^ 4 * g ^ 3 +
      (77312 / 135 : k) * a * c * e ^ 3 * f ^ 2 * g ^ 5 +
      (48 / 5 : k) * a ^ 3 * b ^ 2 * c * e ^ 3 * f ^ 4 * g ^ 2 +
      (256 / 5 : k) * a ^ 2 * b * c ^ 2 * e ^ 3 * f ^ 3 * g ^ 3 +
      (512 / 45 : k) * a * b * c ^ 2 * e ^ 3 * f * g ^ 5 +
      (1984 / 45 : k) * a ^ 2 * b ^ 2 * c * e ^ 3 * f ^ 2 * g ^ 4) * muQuarticPowerInnerS32810 a b c d e f g +
      ((-(16384 / 15) : k) * a * e ^ 2 * f ^ 2 * g ^ 6 +
      (4096 / 15 : k) * a ^ 2 * e ^ 2 * f ^ 4 * g ^ 4 +
      (-(11264 / 45) : k) * a * c ^ 2 * e ^ 2 * f ^ 2 * g ^ 5 +
      (-(124 / 135) : k) * a ^ 3 * b ^ 4 * e ^ 2 * f ^ 2 * g ^ 4 +
      (-(64 / 5) : k) * a ^ 3 * b ^ 2 * e ^ 2 * f ^ 4 * g ^ 3 +
      (-(4 / 5) : k) * a ^ 4 * b ^ 4 * e ^ 2 * f ^ 4 * g ^ 2 +
      (256 / 15 : k) * a ^ 2 * c ^ 2 * e ^ 2 * f ^ 4 * g ^ 3 +
      (1984 / 135 : k) * a * c ^ 4 * e ^ 2 * f ^ 2 * g ^ 4 +
      (-(256 / 15) : k) * a ^ 2 * b * c ^ 3 * e ^ 2 * f ^ 3 * g ^ 3 +
      (-(16 / 5) : k) * a ^ 3 * b ^ 2 * c ^ 2 * e ^ 2 * f ^ 4 * g ^ 2 +
      (64 / 135 : k) * a ^ 2 * b ^ 3 * c * e ^ 2 * f * g ^ 5 +
      (256 / 135 : k) * a * b * c ^ 3 * e ^ 2 * f * g ^ 5 +
      (2048 / 15 : k) * a * b * c * e ^ 2 * f * g ^ 6 +
      (5888 / 45 : k) * a ^ 2 * b * c * e ^ 2 * f ^ 3 * g ^ 4) * xiQuarticPowerInnerS32810 a b c d e f g +
      ((4096 / 15 : k) * a * e ^ 3 * f ^ 2 * g ^ 5 +
      (-(3968 / 45) : k) * a * c ^ 2 * e ^ 3 * f ^ 2 * g ^ 4 +
      (992 / 45 : k) * a ^ 2 * b ^ 2 * e ^ 3 * f ^ 2 * g ^ 4 +
      (512 / 45 : k) * a * b * c * e ^ 3 * f * g ^ 5) * piQuarticPowerInnerS32810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS32810, muQuarticPowerInnerS32810, xiQuarticPowerInnerS32810, piQuarticPowerInnerS32810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a^3*b^3*c^3*e^3*f^3*g^3 = 0`, contradiction. -/
theorem quarticPowerInnerS32810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS32810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS32810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS32810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS32810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS32810_identity a b c d e f g
  have hpow : a ^ 3 * b ^ 3 * c ^ 3 * e ^ 3 * f ^ 3 * g ^ 3 = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
          · -- the right factor
            exact hb ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h1)
        · -- the right factor
          exact hc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h2)
      · -- the right factor
        exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h3)
    · -- the right factor
      exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h4)
  · -- the right factor
    exact hg ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h5)

/-! ## Face system S33 (`b*c*e*f*g`) -/

/-- Face of `κ` on power system 33. -/
def kappaQuarticPowerInnerS33810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f

/-- Face of `ξ` on power system 33. -/
def xiQuarticPowerInnerS33810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (5 / 16 : k) * e * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `b*c*e*f*g ∈ ⟨faces⟩` on power system 33. -/
theorem quarticPowerInnerS33810_identity (a b c d e f g : k) :
    b * c * e * f * g =
      ((16 / 5 : k) * b * e * g) * kappaQuarticPowerInnerS33810 a b c d e f g +
      ((-(16 / 5) : k) * b ^ 2 * g) * xiQuarticPowerInnerS33810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS33810, xiQuarticPowerInnerS33810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `b*c*e*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS33810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS33810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS33810 a b c d e f g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS33810_identity a b c d e f g
  have hpow : b * c * e * f * g = 0 := by
    rw [hkap, hxi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact hb h1
        · -- the right factor
          exact hc h1
      · -- the right factor
        exact he h2
    · -- the right factor
      exact hf h3
  · -- the right factor
    exact hg h4

/-! ## Face system S34 (`a*c*d*e*f*g`) -/

/-- Face of `κ` on power system 34. -/
def kappaQuarticPowerInnerS34810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * c * f +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 34. -/
def muQuarticPowerInnerS34810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `ξ` on power system 34. -/
def xiQuarticPowerInnerS34810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * e +
      (5 / 16 : k) * e * g +
      (-(5 / 64) : k) * a * d * f

/-- Face of `π` on power system 34. -/
def piQuarticPowerInnerS34810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a*c*d*e*f*g ∈ ⟨faces⟩` on power system 34. -/
theorem quarticPowerInnerS34810_identity (a b c d e f g : k) :
    a * c * d * e * f * g =
      ((4 / 35 : k) * a * c ^ 2 * d * e +
      (48 / 35 : k) * a * d * e * g) * kappaQuarticPowerInnerS34810 a b c d e f g +
      ((-(96 / 35) : k) * c ^ 2 * e ^ 2 +
      (384 / 35 : k) * e ^ 2 * g) * muQuarticPowerInnerS34810 a b c d e f g +
      ((16 / 35 : k) * c ^ 3 * e +
      (-(256 / 35) : k) * c * e * g) * xiQuarticPowerInnerS34810 a b c d e f g +
      ((-(32 / 35) : k) * c * e ^ 2) * piQuarticPowerInnerS34810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS34810, muQuarticPowerInnerS34810, xiQuarticPowerInnerS34810, piQuarticPowerInnerS34810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a*c*d*e*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS34810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS34810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS34810 a b c d e f g = 0)
    (hxi : xiQuarticPowerInnerS34810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS34810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS34810_identity a b c d e f g
  have hpow : a * c * d * e * f * g = 0 := by
    rw [hkap, hmu, hxi, hpi] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h5 | h5
  · -- the left factor
    rcases (mul_eq_zero.mp h5) with h4 | h4
    · -- the left factor
      rcases (mul_eq_zero.mp h4) with h3 | h3
      · -- the left factor
        rcases (mul_eq_zero.mp h3) with h2 | h2
        · -- the left factor
          rcases (mul_eq_zero.mp h2) with h1 | h1
          · -- the left factor
            exact ha h1
          · -- the right factor
            exact hc h1
        · -- the right factor
          exact hd h2
      · -- the right factor
        exact he h3
    · -- the right factor
      exact hf h4
  · -- the right factor
    exact hg h5

/-! ## Face system S35 (`g^4`) -/

/-- Face of `κ` on power system 35. -/
def kappaQuarticPowerInnerS35810 (a b c d e f g : k) : k :=
  (5 / 16 : k) * c * f +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 35. -/
def muQuarticPowerInnerS35810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `ν` on power system 35. -/
def nuQuarticPowerInnerS35810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * d +
      (5 / 16 : k) * d * g +
      (-(5 / 128) : k) * a * c * f +
      (-(5 / 128) : k) * a * d * e

/-- Face of `π` on power system 35. -/
def piQuarticPowerInnerS35810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `g^4 ∈ ⟨faces⟩` on power system 35. -/
theorem quarticPowerInnerS35810_identity (a b c d e f g : k) :
    g ^ 4 =
      ((7 / 2816 : k) * a ^ 2 * c ^ 3 * d +
      (-(79 / 3520) : k) * a ^ 2 * c * d * g) * kappaQuarticPowerInnerS35810 a b c d e f g +
      ((63 / 1760 : k) * c ^ 5 +
      (-(117 / 440) : k) * c ^ 3 * g +
      (97 / 55 : k) * c * g ^ 2) * muQuarticPowerInnerS35810 a b c d e f g +
      ((7 / 352 : k) * a * c ^ 3 * d +
      (-(79 / 440) : k) * a * c * d * g) * nuQuarticPowerInnerS35810 a b c d e f g +
      ((4 / 5 : k) * g ^ 2 +
      (21 / 880 : k) * c ^ 4 +
      (-(53 / 220) : k) * c ^ 2 * g) * piQuarticPowerInnerS35810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS35810, muQuarticPowerInnerS35810, nuQuarticPowerInnerS35810, piQuarticPowerInnerS35810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `g^4 = 0`, contradiction. -/
theorem quarticPowerInnerS35810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS35810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS35810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS35810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS35810 a b c d e f g = 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS35810_identity a b c d e f g
  have hpow : g ^ 4 = 0 := by
    rw [hkap, hmu, hnu, hpi] at hid
    simpa using hid
  exact hg ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

/-! ## Face system S36 (`b*c*d*f*g`) -/

/-- Face of `κ` on power system 36. -/
def kappaQuarticPowerInnerS36810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f

/-- Face of `ν` on power system 36. -/
def nuQuarticPowerInnerS36810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * d +
      (5 / 16 : k) * d * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `b*c*d*f*g ∈ ⟨faces⟩` on power system 36. -/
theorem quarticPowerInnerS36810_identity (a b c d e f g : k) :
    b * c * d * f * g =
      ((16 / 5 : k) * b * d * g) * kappaQuarticPowerInnerS36810 a b c d e f g +
      ((-(16 / 5) : k) * b ^ 2 * g) * nuQuarticPowerInnerS36810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS36810, nuQuarticPowerInnerS36810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `b*c*d*f*g = 0`, contradiction. -/
theorem quarticPowerInnerS36810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS36810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS36810 a b c d e f g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS36810_identity a b c d e f g
  have hpow : b * c * d * f * g = 0 := by
    rw [hkap, hnu] at hid
    simpa using hid
  rcases (mul_eq_zero.mp hpow) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact hb h1
        · -- the right factor
          exact hc h1
      · -- the right factor
        exact hd h2
    · -- the right factor
      exact hf h3
  · -- the right factor
    exact hg h4

/-! ## Face system S37 (`g^4`) -/

/-- Face of `κ` on power system 37. -/
def kappaQuarticPowerInnerS37810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * b * c ^ 2 +
      (5 / 16 : k) * b * g +
      (5 / 16 : k) * c * f +
      (5 / 16 : k) * d * e

/-- Face of `μ` on power system 37. -/
def muQuarticPowerInnerS37810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
      (-(5 / 128) : k) * a * d ^ 2 +
      (5 / 16 : k) * c * g

/-- Face of `ν` on power system 37. -/
def nuQuarticPowerInnerS37810 (a b c d e f g : k) : k :=
  (-(15 / 128) : k) * c ^ 2 * d +
      (5 / 16 : k) * d * g +
      (-(5 / 128) : k) * a * b * g +
      (-(5 / 128) : k) * a * c * f +
      (-(5 / 128) : k) * a * d * e +
      (15 / 1024 : k) * a * b * c ^ 2

/-- Face of `π` on power system 37. -/
def piQuarticPowerInnerS37810 (a b c d e f g : k) : k :=
  (5 / 4 : k) * g ^ 2 +
      (15 / 256 : k) * c ^ 4 +
      (-(5 / 16) : k) * c ^ 2 * g +
      (5 / 32 : k) * a * c * d ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `g^4 ∈ ⟨faces⟩` on power system 37. -/
theorem quarticPowerInnerS37810_identity (a b c d e f g : k) :
    g ^ 4 =
      ((7 / 2816 : k) * a ^ 2 * c ^ 3 * d +
      (-(79 / 3520) : k) * a ^ 2 * c * d * g) * kappaQuarticPowerInnerS37810 a b c d e f g +
      (c * g ^ 2 +
      (-(3 / 40) : k) * c ^ 3 * g +
      (-(21 / 220) : k) * a * c ^ 2 * d ^ 2) * muQuarticPowerInnerS37810 a b c d e f g +
      ((7 / 352 : k) * a * c ^ 3 * d +
      (-(79 / 440) : k) * a * c * d * g) * nuQuarticPowerInnerS37810 a b c d e f g +
      ((4 / 5 : k) * g ^ 2 +
      (-(1 / 20) : k) * c ^ 2 * g +
      (-(21 / 880) : k) * a * c * d ^ 2) * piQuarticPowerInnerS37810 a b c d e f g := by
  simp only [kappaQuarticPowerInnerS37810, muQuarticPowerInnerS37810, nuQuarticPowerInnerS37810, piQuarticPowerInnerS37810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `g^4 = 0`, contradiction. -/
theorem quarticPowerInnerS37810_false (a b c d e f g : k)
    (hkap : kappaQuarticPowerInnerS37810 a b c d e f g = 0)
    (hmu : muQuarticPowerInnerS37810 a b c d e f g = 0)
    (hnu : nuQuarticPowerInnerS37810 a b c d e f g = 0)
    (hpi : piQuarticPowerInnerS37810 a b c d e f g = 0)
    (hg : g ≠ 0)
    : False := by
  have hid := quarticPowerInnerS37810_identity a b c d e f g
  have hpow : g ^ 4 = 0 := by
    rw [hkap, hmu, hnu, hpi] at hid
    simpa using hid
  exact hg ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

end QuarticPowerCertificates810

#print axioms quarticPowerInnerS00810_identity
#print axioms quarticPowerInnerS00810_false
#print axioms quarticPowerInnerS01810_identity
#print axioms quarticPowerInnerS01810_false
#print axioms quarticPowerInnerS02810_identity
#print axioms quarticPowerInnerS02810_false
#print axioms quarticPowerInnerS03810_identity
#print axioms quarticPowerInnerS03810_false
#print axioms quarticPowerInnerS04810_identity
#print axioms quarticPowerInnerS04810_false
#print axioms quarticPowerInnerS05810_identity
#print axioms quarticPowerInnerS05810_false
#print axioms quarticPowerInnerS06810_identity
#print axioms quarticPowerInnerS06810_false
#print axioms quarticPowerInnerS07810_identity
#print axioms quarticPowerInnerS07810_false
#print axioms quarticPowerInnerS08810_identity
#print axioms quarticPowerInnerS08810_false
#print axioms quarticPowerInnerS09810_identity
#print axioms quarticPowerInnerS09810_false
#print axioms quarticPowerInnerS10810_identity
#print axioms quarticPowerInnerS10810_false
#print axioms quarticPowerInnerS11810_identity
#print axioms quarticPowerInnerS11810_false
#print axioms quarticPowerInnerS12810_identity
#print axioms quarticPowerInnerS12810_false
#print axioms quarticPowerInnerS13810_identity
#print axioms quarticPowerInnerS13810_false
#print axioms quarticPowerInnerS14810_identity
#print axioms quarticPowerInnerS14810_false
#print axioms quarticPowerInnerS15810_identity
#print axioms quarticPowerInnerS15810_false
#print axioms quarticPowerInnerS16810_identity
#print axioms quarticPowerInnerS16810_false
#print axioms quarticPowerInnerS17810_identity
#print axioms quarticPowerInnerS17810_false
#print axioms quarticPowerInnerS18810_identity
#print axioms quarticPowerInnerS18810_false
#print axioms quarticPowerInnerS19810_identity
#print axioms quarticPowerInnerS19810_false
#print axioms quarticPowerInnerS20810_identity
#print axioms quarticPowerInnerS20810_false
#print axioms quarticPowerInnerS21810_identity
#print axioms quarticPowerInnerS21810_false
#print axioms quarticPowerInnerS22810_identity
#print axioms quarticPowerInnerS22810_false
#print axioms quarticPowerInnerS23810_identity
#print axioms quarticPowerInnerS23810_false
#print axioms quarticPowerInnerS25810_identity
#print axioms quarticPowerInnerS25810_false
#print axioms quarticPowerInnerS26810_identity
#print axioms quarticPowerInnerS26810_false
#print axioms quarticPowerInnerS27810_identity
#print axioms quarticPowerInnerS27810_false
#print axioms quarticPowerInnerS28810_identity
#print axioms quarticPowerInnerS28810_false
#print axioms quarticPowerInnerS29810_identity
#print axioms quarticPowerInnerS29810_false
#print axioms quarticPowerInnerS30810_identity
#print axioms quarticPowerInnerS30810_false
#print axioms quarticPowerInnerS31810_identity
#print axioms quarticPowerInnerS31810_false
#print axioms quarticPowerInnerS32810_identity
#print axioms quarticPowerInnerS32810_false
#print axioms quarticPowerInnerS33810_identity
#print axioms quarticPowerInnerS33810_false
#print axioms quarticPowerInnerS34810_identity
#print axioms quarticPowerInnerS34810_false
#print axioms quarticPowerInnerS35810_identity
#print axioms quarticPowerInnerS35810_false
#print axioms quarticPowerInnerS36810_identity
#print axioms quarticPowerInnerS36810_false
#print axioms quarticPowerInnerS37810_identity
#print axioms quarticPowerInnerS37810_false

end Max11DegreeRoutes
