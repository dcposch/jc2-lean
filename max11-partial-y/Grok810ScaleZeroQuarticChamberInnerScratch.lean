import Grok810ScaleZeroQuarticChamberCertificatesScratch
import Grok810ScaleZeroQuarticChamberNuFacesScratch

/-! # Inner scalars, ideal identities and top-coefficient extraction

8 certificate systems over 15 (carrier, packet) faces: the face evaluated at the
leading coefficients, the isobaric membership identity with the
cofactors of `scripts/out_810_scale_zero_quartic_chambers.json`
(re-verified by `sympy` in
`scripts/derive_810_quartic_chamber_killplan4.py`), the `False` lemma,
and the `_coeff_top` bridge `(face).coeff d = inner(A.leadingCoeff, …)`.
The `no_monomial_target` systems reuse the green scalar identities of
`Grok810ScaleZeroQuarticChamberCertificatesScratch`.
Untracked working note.
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

section QuarticChamberInner810

/-! ## Inner scalars and the ideal identities -/

/-- The face of `κ` on packet 1, at the leading coefficients. -/
def kappaQuarticChamberInner1810 (a b c d e f g : k) : k :=
  (5 / 512 : k) * a * b ^ 3 +
    (-(15 / 128) : k) * b * c ^ 2

/-- The face of `μ` on packet 3, at the leading coefficients. -/
def muQuarticChamberInner3810 (a b c d e f g : k) : k :=
  (15 / 512 : k) * a * b ^ 2 * c +
    (-(5 / 128) : k) * c ^ 3

/-- The face of `κ` on packet 7, at the leading coefficients. -/
def kappaQuarticChamberInner7810 (a b c d e f g : k) : k :=
  (5 / 512 : k) * a * b ^ 3 +
    (5 / 16 : k) * b * g

/-- The face of `π` on packet 3, at the leading coefficients. -/
def piQuarticChamberInner3810 (a b c d e f g : k) : k :=
  (15 / 4096 : k) * a ^ 2 * b ^ 4 +
    (5 / 64 : k) * a * b ^ 2 * g +
    (5 / 4 : k) * g ^ 2

/-- The face of `μ` on packet 7, at the leading coefficients. -/
def muQuarticChamberInner7810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * c ^ 3 +
    (5 / 16 : k) * c * g

/-- The face of `π` on packet 1, at the leading coefficients. -/
def piQuarticChamberInner1810 (a b c d e f g : k) : k :=
  (15 / 256 : k) * c ^ 4 +
    (-(5 / 16) : k) * c ^ 2 * g +
    (5 / 4 : k) * g ^ 2

/-- The face of `ξ` on packet 19, at the leading coefficients. -/
def xiQuarticChamberInner19810 (a b c d e f g : k) : k :=
  (15 / 512 : k) * a * b ^ 2 * e +
    (5 / 16 : k) * e * g

/-- The face of `μ` on packet 8, at the leading coefficients. -/
def muQuarticChamberInner8810 (a b c d e f g : k) : k :=
  (-(5 / 128) : k) * a * d ^ 2 +
    (5 / 16 : k) * d * f

/-- The face of `ξ` on packet 3, at the leading coefficients. -/
def xiQuarticChamberInner3810 (a b c d e f g : k) : k :=
  (-(5 / 64) : k) * a * d * f +
    (5 / 32 : k) * f ^ 2

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `c^5 ∈ ⟨faces⟩` for the packet system 0. -/
theorem quarticChamberInnerSystem0810_identity (a b c d e f g : k) :
    ((-(36 / 5) : k) * a * b * c) *
        (kappaQuarticChamberInner1810 a b c d e f g) +
      ((-(128 / 5) : k) * c ^ 2 +
      (12 / 5 : k) * a * b ^ 2) *
        (muQuarticChamberInner3810 a b c d e f g) =
      c ^ 5 := by
  simp only [kappaQuarticChamberInner1810, muQuarticChamberInner3810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticChamberInnerSystem0810_zero_impossible (a b c d e f g : k)
    (hf0 : kappaQuarticChamberInner1810 a b c d e f g = 0)
    (hf1 : muQuarticChamberInner3810 a b c d e f g = 0)
    (hCc : c ≠ 0) :
    False := by
  have hid := quarticChamberInnerSystem0810_identity a b c d e f g
  have hz : c ^ 5 = 0 := by
    rw [hf0, hf1] at hid
    simpa using hid.symm
  exact hCc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hz)

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `g^3 ∈ ⟨faces⟩` for the packet system 1. -/
theorem quarticChamberInnerSystem1810_identity (a b c d e f g : k) :
    ((-(3 / 640) : k) * a ^ 2 * b ^ 3 +
      (-(1 / 4) : k) * a * b * g) *
        (kappaQuarticChamberInner7810 a b c d e f g) +
      ((4 / 5 : k) * g +
      (1 / 80 : k) * a * b ^ 2) *
        (piQuarticChamberInner3810 a b c d e f g) =
      g ^ 3 := by
  simp only [kappaQuarticChamberInner7810, piQuarticChamberInner3810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticChamberInnerSystem1810_zero_impossible (a b c d e f g : k)
    (hf0 : kappaQuarticChamberInner7810 a b c d e f g = 0)
    (hf1 : piQuarticChamberInner3810 a b c d e f g = 0)
    (hGc : g ≠ 0) :
    False := by
  have hid := quarticChamberInnerSystem1810_identity a b c d e f g
  have hz : g ^ 3 = 0 := by
    rw [hf0, hf1] at hid
    simpa using hid.symm
  exact hGc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hz)

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `(a*b*c*e*g)^1 ∈ ⟨faces⟩` for the packet system 3. -/
theorem quarticChamberInnerSystem3810_identity (a b c d e f g : k) :
    ((-(8 / 5) : k) * a * c * e) *
        (kappaQuarticNoTargetInnerBCEG810 b c e g) +
      ((24 / 5 : k) * a * b * e) *
        (muQuarticChamberInner7810 a b c d e f g) =
      a * b * c * e * g := by
  simp only [kappaQuarticNoTargetInnerBCEG810, muQuarticChamberInner7810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticChamberInnerSystem3810_zero_impossible (a b c d e f g : k)
    (hf0 : kappaQuarticNoTargetInnerBCEG810 b c e g = 0)
    (hf1 : muQuarticChamberInner7810 a b c d e f g = 0)
    (hAc : a ≠ 0)
    (hBc : b ≠ 0)
    (hCc : c ≠ 0)
    (hEc : e ≠ 0)
    (hGc : g ≠ 0) :
    False := by
  have hid := quarticChamberInnerSystem3810_identity a b c d e f g
  have hz : a * b * c * e * g = 0 := by
    rw [hf0, hf1] at hid
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact hAc h1
        · -- the right factor
          exact hBc h1
      · -- the right factor
        exact hCc h2
    · -- the right factor
      exact hEc h3
  · -- the right factor
    exact hGc h4

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `c^5 ∈ ⟨faces⟩` for the packet system 5. -/
theorem quarticChamberInnerSystem5810_identity (a b c d e f g : k) :
    ((-(512 / 5) : k) * g +
      (64 / 5 : k) * c ^ 2) *
        (muQuarticChamberInner7810 a b c d e f g) +
      ((128 / 5 : k) * c) *
        (piQuarticChamberInner1810 a b c d e f g) =
      c ^ 5 := by
  simp only [muQuarticChamberInner7810, piQuarticChamberInner1810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticChamberInnerSystem5810_zero_impossible (a b c d e f g : k)
    (hf0 : muQuarticChamberInner7810 a b c d e f g = 0)
    (hf1 : piQuarticChamberInner1810 a b c d e f g = 0)
    (hCc : c ≠ 0) :
    False := by
  have hid := quarticChamberInnerSystem5810_identity a b c d e f g
  have hz : c ^ 5 = 0 := by
    rw [hf0, hf1] at hid
    simpa using hid.symm
  exact hCc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hz)

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `(a*b*e*f*g)^1 ∈ ⟨faces⟩` for the packet system 6. -/
theorem quarticChamberInnerSystem6810_identity (a b c d e f g : k) :
    ((24 / 5 : k) * a * e * f) *
        (kappaQuarticChamberInner7810 a b c d e f g) +
      ((-(8 / 5) : k) * a * b * f) *
        (xiQuarticChamberInner19810 a b c d e f g) =
      a * b * e * f * g := by
  simp only [kappaQuarticChamberInner7810, xiQuarticChamberInner19810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticChamberInnerSystem6810_zero_impossible (a b c d e f g : k)
    (hf0 : kappaQuarticChamberInner7810 a b c d e f g = 0)
    (hf1 : xiQuarticChamberInner19810 a b c d e f g = 0)
    (hAc : a ≠ 0)
    (hBc : b ≠ 0)
    (hEc : e ≠ 0)
    (hFc : f ≠ 0)
    (hGc : g ≠ 0) :
    False := by
  have hid := quarticChamberInnerSystem6810_identity a b c d e f g
  have hz : a * b * e * f * g = 0 := by
    rw [hf0, hf1] at hid
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with h4 | h4
  · -- the left factor
    rcases (mul_eq_zero.mp h4) with h3 | h3
    · -- the left factor
      rcases (mul_eq_zero.mp h3) with h2 | h2
      · -- the left factor
        rcases (mul_eq_zero.mp h2) with h1 | h1
        · -- the left factor
          exact hAc h1
        · -- the right factor
          exact hBc h1
      · -- the right factor
        exact hEc h2
    · -- the right factor
      exact hFc h3
  · -- the right factor
    exact hGc h4

set_option maxHeartbeats 64000000 in
/-- Isobaric membership `f^3 ∈ ⟨faces⟩` for the packet system 7. -/
theorem quarticChamberInnerSystem7810_identity (a b c d e f g : k) :
    ((32 / 15 : k) * a * f) *
        (muQuarticChamberInner8810 a b c d e f g) +
      ((32 / 5 : k) * f +
      (-(16 / 15) : k) * a * d) *
        (xiQuarticChamberInner3810 a b c d e f g) =
      f ^ 3 := by
  simp only [muQuarticChamberInner8810, xiQuarticChamberInner3810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticChamberInnerSystem7810_zero_impossible (a b c d e f g : k)
    (hf0 : muQuarticChamberInner8810 a b c d e f g = 0)
    (hf1 : xiQuarticChamberInner3810 a b c d e f g = 0)
    (hFc : f ≠ 0) :
    False := by
  have hid := quarticChamberInnerSystem7810_identity a b c d e f g
  have hz : f ^ 3 = 0 := by
    rw [hf0, hf1] at hid
    simpa using hid.symm
  exact hFc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hz)

/-! ## Top-coefficient extraction -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff := by
  simp only [kappaQuarticChamberFace6810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  simp only [kappaQuarticNoTargetInnerABCF810]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace9810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace9810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff := by
  simp only [muQuarticChamberFace9810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  simp only [muQuarticNoTargetInnerABCF810]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace2000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace2000810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticNoTargetInnerABCF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff F.leadingCoeff := by
  simp only [piQuarticChamberFace2000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  simp only [piQuarticNoTargetInnerABCF810]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace10810_coeff_top
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace10810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      kappaQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace10810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((B * C ^ 2)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((B * C ^ 2)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [kappaQuarticNoTargetInnerBCEG810]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace11810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + G.natDegree = 3 * C.natDegree)
    (ht2 : 2 * E.natDegree = 3 * C.natDegree) :
    (muQuarticChamberFace11810 A B C D E F G).coeff
        (3 * C.natDegree) =
      muQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace11810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 3).natDegree = 3 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc1 : ((C * G)).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (E ^ 2).natDegree = 3 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (3 * C.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  simp only [muQuarticNoTargetInnerBCEG810]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace4810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + G.natDegree = 4 * C.natDegree)
    (ht2 : C.natDegree + 2 * E.natDegree = 4 * C.natDegree)
    (ht3 : 2 * G.natDegree = 4 * C.natDegree) :
    (piQuarticChamberFace4810 A B C D E F G).coeff
        (4 * C.natDegree) =
      piQuarticNoTargetInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace4810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 4).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 4).coeff (4 * C.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * G)).coeff (4 * C.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * E ^ 2)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C * E ^ 2)).coeff (4 * C.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (4 * C.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  simp only [piQuarticNoTargetInnerBCEG810]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace1810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace1810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace1810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [kappaQuarticChamberInner1810]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace3810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace3810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace3810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [muQuarticChamberInner3810]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace7810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace7810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace7810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [kappaQuarticChamberInner7810]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace3810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace3810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace3810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  simp only [piQuarticChamberInner3810]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace7810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + G.natDegree = 3 * C.natDegree) :
    (muQuarticChamberFace7810 A B C D E F G).coeff
        (3 * C.natDegree) =
      muQuarticChamberInner7810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace7810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 3).natDegree = 3 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc1 : ((C * G)).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [muQuarticChamberInner7810]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace1810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + G.natDegree = 4 * C.natDegree)
    (ht2 : 2 * G.natDegree = 4 * C.natDegree) :
    (piQuarticChamberFace1810 A B C D E F G).coeff
        (4 * C.natDegree) =
      piQuarticChamberInner1810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace1810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 4).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 4).coeff (4 * C.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * G)).coeff (4 * C.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (G ^ 2).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (G ^ 2).coeff (4 * C.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  simp only [piQuarticChamberInner1810]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace19810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace19810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticChamberInner19810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace19810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [xiQuarticChamberInner19810]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace8810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : D.natDegree + F.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace8810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticChamberInner8810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace8810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((D * F)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hDne hFne]
    all_goals omega
  have hc1 : ((D * F)).coeff (A.natDegree + 2 * D.natDegree) = D.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [muQuarticChamberInner8810]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace3810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : 2 * F.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace3810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      xiQuarticChamberInner3810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace3810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (F ^ 2).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (F ^ 2).coeff (A.natDegree + D.natDegree + F.natDegree) = F.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  simp only [xiQuarticChamberInner3810]
  ring


end QuarticChamberInner810

end Max11DegreeRoutes
