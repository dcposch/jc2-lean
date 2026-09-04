import Grok810ScaleZeroQuarticSigmaLadderScratch

/-! # Certificates for the 12 `no_monomial_target` chambers, `(8,10)` scale zero

The JSON taxonomy (`scripts/out_810_scale_zero_quartic_chambers.json`) records
twelve leaves whose saturating carrier set is known but for which the original
Groebner scan never produced cofactors (it searched only pure powers `v^k` and
the product of *all* live leading coefficients, including letters that do not
appear in the faces).  Those twelve leaves collapse to three face systems.

CAS (`scripts/derive_810_scale_zero_quartic_notarget_certs.py`, Singular
`lift` plus the isobaric engine of `scripts/emit_810_quartic_chambers.py`):

* ABCF (`κ, μ, π`), argmin `BF·CF·BBB·BBC·BCC·CCC` (six live sets):
  `a * b * f^3 = Σ h_Φ Φ`, cofactor sizes 3+3+2.
* BCEG (`κ, μ, π`), argmin `CG·EE·CCC` (four live sets):
  `b * g^2 = Σ h_Φ Φ`, cofactor sizes 2+1+1.
* ABCDFG (`κ, ν`), argmin `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG` (two live sets):
  `d * g = Σ h_Φ Φ`, cofactor sizes 1+1.

Each identity is a standalone scalar equation over a `CharZero` field, in the
shape of `cubicSigmaInner_BC_identity`.  The kill hypothesises that the face
polynomials vanish and that the involved leading coefficients are nonzero, and
concludes `False`.  Identities verified by expansion and at random rational
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

section QuarticChamberCertificates810

/-! ## Face system ABCF -/

def kappaQuarticNoTargetInnerABCF810 (a b c f : k) : k :=
  (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * c * f + (5 / 512 : k) * a * b ^ 3

def muQuarticNoTargetInnerABCF810 (a b c f : k) : k :=
  (-5 / 128 : k) * c ^ 3 + (-5 / 64 : k) * a * b * f + (15 / 512 : k) * a * b ^ 2 * c

def piQuarticNoTargetInnerABCF810 (a b c f : k) : k :=
  (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * a * f ^ 2 + (15 / 4096 : k) * a ^ 2 * b ^ 4 +
    (-45 / 512 : k) * a * b ^ 2 * c ^ 2 + (5 / 32 : k) * a * b * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `a * b * f ^ 3 ∈ ⟨faces⟩` on the ABCF system. -/
theorem quarticNoTargetInner_ABCF_identity
    (a b c f : k) :
    ((-4 / 15 : k) * c ^ 2 * f + a * b ^ 2 * f + (-1 / 10 : k) * a * b ^ 3 * c) * kappaQuarticNoTargetInnerABCF810 a b c f +
      ((-32 / 15 : k) * f ^ 2 + (2 / 5 : k) * b ^ 2 * c ^ 2 + (-16 / 5 : k) * b * c * f) * muQuarticNoTargetInnerABCF810 a b c f +
      ((-8 / 3 : k) * b * f + (4 / 15 : k) * b ^ 2 * c) * piQuarticNoTargetInnerABCF810 a b c f =
      a * b * f ^ 3 := by
  simp only [kappaQuarticNoTargetInnerABCF810, muQuarticNoTargetInnerABCF810, piQuarticNoTargetInnerABCF810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `a * b * f ^ 3 = 0`, contradiction. -/
theorem quarticNoTargetInner_ABCF_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False := by
  have hid := quarticNoTargetInner_ABCF_identity a b c f
  have hpow : a * b * f ^ 3 = 0 := by
    rw [hkap, hmu, hpi] at hid
    simpa using hid.symm
  rcases (mul_eq_zero.mp hpow) with h | h
  · rcases (mul_eq_zero.mp h) with h | h
    · exact (ha h).elim
    · exact (hb h).elim
  · exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h)

/-! ## Face system BCEG -/

def kappaQuarticNoTargetInnerBCEG810 (b c e g : k) : k :=
  (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g

def muQuarticNoTargetInnerBCEG810 (b c e g : k) : k :=
  (-5 / 128 : k) * c ^ 3 + (5 / 32 : k) * e ^ 2 + (5 / 16 : k) * c * g

def piQuarticNoTargetInnerBCEG810 (b c e g : k) : k :=
  (5 / 4 : k) * g ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 8 : k) * c * e ^ 2 +
    (-5 / 16 : k) * c ^ 2 * g

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `b * g ^ 2 ∈ ⟨faces⟩` on the BCEG system. -/
theorem quarticNoTargetInner_BCEG_identity
    (b c e g : k) :
    ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * kappaQuarticNoTargetInnerBCEG810 b c e g +
      ((72 / 55 : k) * b * c) * muQuarticNoTargetInnerBCEG810 b c e g +
      ((18 / 55 : k) * b) * piQuarticNoTargetInnerBCEG810 b c e g =
      b * g ^ 2 := by
  simp only [kappaQuarticNoTargetInnerBCEG810, muQuarticNoTargetInnerBCEG810, piQuarticNoTargetInnerBCEG810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `b * g ^ 2 = 0`, contradiction. -/
theorem quarticNoTargetInner_BCEG_zero_impossible
    (b c e g : k)
    (hkap : kappaQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hmu : muQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hpi : piQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticNoTargetInner_BCEG_identity b c e g
  have hpow : b * g ^ 2 = 0 := by
    rw [hkap, hmu, hpi] at hid
    simpa using hid.symm
  rcases (mul_eq_zero.mp hpow) with h | h
  · exact (hb h).elim
  · exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h)

/-! ## Face system ABCDFG -/

def kappaQuarticNoTargetInnerABCDFG810 (a b c d f g : k) : k :=
  (5 / 16 : k) * b * g + (5 / 16 : k) * c * f

def nuQuarticNoTargetInnerABCDFG810 (a b c d f g : k) : k :=
  (5 / 16 : k) * d * g + (-5 / 128 : k) * a * b * g + (-5 / 128 : k) * a * c * f

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `d * g ∈ ⟨faces⟩` on the ABCDFG system. -/
theorem quarticNoTargetInner_ABCDFG_identity
    (a b c d f g : k) :
    ((2 / 5 : k) * a) * kappaQuarticNoTargetInnerABCDFG810 a b c d f g +
      ((16 / 5 : k)) * nuQuarticNoTargetInnerABCDFG810 a b c d f g =
      d * g := by
  simp only [kappaQuarticNoTargetInnerABCDFG810, nuQuarticNoTargetInnerABCDFG810]
  ring

set_option maxHeartbeats 64000000 in
/-- Saturating faces vanish and the involved leading coefficients
are nonzero: `d * g = 0`, contradiction. -/
theorem quarticNoTargetInner_ABCDFG_zero_impossible
    (a b c d f g : k)
    (hkap : kappaQuarticNoTargetInnerABCDFG810 a b c d f g = 0)
    (hnu : nuQuarticNoTargetInnerABCDFG810 a b c d f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticNoTargetInner_ABCDFG_identity a b c d f g
  have hpow : d * g = 0 := by
    rw [hkap, hnu] at hid
    simpa using hid.symm
  rcases (mul_eq_zero.mp hpow) with h | h
  · exact (hd h).elim
  · exact (hg h).elim

/-! ## The twelve chamber kills -/

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDF5810` (live `BCDF`, argmin `BF·CF·BBB·BBC·BCC·CCC`). -/
theorem quarticChamberBCDF5810_faces_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False :=
  quarticNoTargetInner_ABCF_zero_impossible a b c f hkap hmu hpi ha hb hc hf

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCEF5810` (live `BCEF`, argmin `BF·CF·BBB·BBC·BCC·CCC`). -/
theorem quarticChamberBCEF5810_faces_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False :=
  quarticNoTargetInner_ABCF_zero_impossible a b c f hkap hmu hpi ha hb hc hf

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCEG18810` (live `BCEG`, argmin `CG·EE·CCC`). -/
theorem quarticChamberBCEG18810_faces_zero_impossible
    (b c e g : k)
    (hkap : kappaQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hmu : muQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hpi : piQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False :=
  quarticNoTargetInner_BCEG_zero_impossible b c e g hkap hmu hpi hb hc he hg

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDEF5810` (live `BCDEF`, argmin `BF·CF·BBB·BBC·BCC·CCC`). -/
theorem quarticChamberBCDEF5810_faces_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False :=
  quarticNoTargetInner_ABCF_zero_impossible a b c f hkap hmu hpi ha hb hc hf

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDEG36810` (live `BCDEG`, argmin `CG·EE·CCC`). -/
theorem quarticChamberBCDEG36810_faces_zero_impossible
    (b c e g : k)
    (hkap : kappaQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hmu : muQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hpi : piQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False :=
  quarticNoTargetInner_BCEG_zero_impossible b c e g hkap hmu hpi hb hc he hg

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDFG10810` (live `BCDFG`, argmin `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`). -/
theorem quarticChamberBCDFG10810_faces_zero_impossible
    (a b c d f g : k)
    (hkap : kappaQuarticNoTargetInnerABCDFG810 a b c d f g = 0)
    (hnu : nuQuarticNoTargetInnerABCDFG810 a b c d f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False :=
  quarticNoTargetInner_ABCDFG_zero_impossible a b c d f g hkap hnu ha hb hc hd hf hg

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDFG17810` (live `BCDFG`, argmin `BF·CF·BBB·BBC·BCC·CCC`). -/
theorem quarticChamberBCDFG17810_faces_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False :=
  quarticNoTargetInner_ABCF_zero_impossible a b c f hkap hmu hpi ha hb hc hf

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCEFG17810` (live `BCEFG`, argmin `BF·CF·BBB·BBC·BCC·CCC`). -/
theorem quarticChamberBCEFG17810_faces_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False :=
  quarticNoTargetInner_ABCF_zero_impossible a b c f hkap hmu hpi ha hb hc hf

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCEFG54810` (live `BCEFG`, argmin `CG·EE·CCC`). -/
theorem quarticChamberBCEFG54810_faces_zero_impossible
    (b c e g : k)
    (hkap : kappaQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hmu : muQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hpi : piQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False :=
  quarticNoTargetInner_BCEG_zero_impossible b c e g hkap hmu hpi hb hc he hg

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDEFG13810` (live `BCDEFG`, argmin `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`). -/
theorem quarticChamberBCDEFG13810_faces_zero_impossible
    (a b c d f g : k)
    (hkap : kappaQuarticNoTargetInnerABCDFG810 a b c d f g = 0)
    (hnu : nuQuarticNoTargetInnerABCDFG810 a b c d f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False :=
  quarticNoTargetInner_ABCDFG_zero_impossible a b c d f g hkap hnu ha hb hc hd hf hg

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDEFG29810` (live `BCDEFG`, argmin `BF·CF·BBB·BBC·BCC·CCC`). -/
theorem quarticChamberBCDEFG29810_faces_zero_impossible
    (a b c f : k)
    (hkap : kappaQuarticNoTargetInnerABCF810 a b c f = 0)
    (hmu : muQuarticNoTargetInnerABCF810 a b c f = 0)
    (hpi : piQuarticNoTargetInnerABCF810 a b c f = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hf : f ≠ 0) :
    False :=
  quarticNoTargetInner_ABCF_zero_impossible a b c f hkap hmu hpi ha hb hc hf

set_option maxHeartbeats 64000000 in
/-- Scalar kill of chamber `QuarticChamberBCDEFG108810` (live `BCDEFG`, argmin `CG·EE·CCC`). -/
theorem quarticChamberBCDEFG108810_faces_zero_impossible
    (b c e g : k)
    (hkap : kappaQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hmu : muQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hpi : piQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False :=
  quarticNoTargetInner_BCEG_zero_impossible b c e g hkap hmu hpi hb hc he hg

end QuarticChamberCertificates810

#print axioms quarticNoTargetInner_ABCF_identity
#print axioms quarticNoTargetInner_ABCF_zero_impossible
#print axioms quarticNoTargetInner_BCEG_identity
#print axioms quarticNoTargetInner_BCEG_zero_impossible
#print axioms quarticNoTargetInner_ABCDFG_identity
#print axioms quarticNoTargetInner_ABCDFG_zero_impossible
#print axioms quarticChamberBCDF5810_faces_zero_impossible
#print axioms quarticChamberBCEF5810_faces_zero_impossible
#print axioms quarticChamberBCEG18810_faces_zero_impossible
#print axioms quarticChamberBCDEF5810_faces_zero_impossible
#print axioms quarticChamberBCDEG36810_faces_zero_impossible
#print axioms quarticChamberBCDFG10810_faces_zero_impossible
#print axioms quarticChamberBCDFG17810_faces_zero_impossible
#print axioms quarticChamberBCEFG17810_faces_zero_impossible
#print axioms quarticChamberBCEFG54810_faces_zero_impossible
#print axioms quarticChamberBCDEFG13810_faces_zero_impossible
#print axioms quarticChamberBCDEFG29810_faces_zero_impossible
#print axioms quarticChamberBCDEFG108810_faces_zero_impossible

end Max11DegreeRoutes
