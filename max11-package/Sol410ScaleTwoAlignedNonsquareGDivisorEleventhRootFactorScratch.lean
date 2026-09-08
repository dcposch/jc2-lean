import Sol410ScaleTwoAlignedNonsquareGDivisorComplementScratch

/-! # Scalar factorization of the reduced `(4,10)` eleventh defect -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {K : Type*} [Field K] [CharZero K]

/-- The exact order-seventeen part of the eleventh defect after
`p₃=H²g₁`, `p₂=Hr`, and `p₁=Hs`, evaluated at a root of `H`. -/
def alignedEleventhRootLeading410
    (p0 s r g κ3 κ7 : K) : K :=
  (125829120 : K) * p0 ^ 2 * s -
    (62914560 : K) * p0 * s * r ^ 2 -
    (62914560 : K) * p0 ^ 2 * r * g +
    (7864320 : K) * s * r ^ 4 +
    (31457280 : K) * p0 * r ^ 3 * g -
    (3932160 : K) * r ^ 5 * g -
    κ7 * ((512 : K) * s - (256 : K) * r * g) -
    κ3 * ((786432 : K) * p0 * s -
      (196608 : K) * s * r ^ 2 -
      (393216 : K) * p0 * r * g +
      (98304 : K) * r ^ 3 * g)

/-- The companion factor left after the terminal quotient
`2s-rg` is removed. -/
def alignedEleventhRootCompanion410
    (p0 r κ3 κ7 : K) : K :=
  -(1536 : K) * κ3 * p0 + (384 : K) * κ3 * r ^ 2 - κ7 +
    (245760 : K) * p0 ^ 2 - (122880 : K) * p0 * r ^ 2 +
    (15360 : K) * r ^ 4

/-- Exact factorization of the reduced eleventh row. -/
theorem alignedEleventhRootLeading_factor410
    (p0 s r g κ3 κ7 : K) :
    alignedEleventhRootLeading410 p0 s r g κ3 κ7 =
      (256 : K) * (2 * s - r * g) *
        alignedEleventhRootCompanion410 p0 r κ3 κ7 := by
  simp only [alignedEleventhRootLeading410,
    alignedEleventhRootCompanion410]
  ring

/-- Vanishing of the reduced row splits into the terminal quotient and its
new companion; the scalar `256` is harmless in characteristic zero. -/
theorem alignedEleventhRootLeading_split410
    (p0 s r g κ3 κ7 : K)
    (hrow : alignedEleventhRootLeading410 p0 s r g κ3 κ7 = 0) :
    (2 * s - r * g) = 0 ∨
      alignedEleventhRootCompanion410 p0 r κ3 κ7 = 0 := by
  rw [alignedEleventhRootLeading_factor410] at hrow
  have hrow' : (256 : K) * ((2 * s - r * g) *
      alignedEleventhRootCompanion410 p0 r κ3 κ7) = 0 := by
    simpa only [mul_assoc] using hrow
  have hproduct : (2 * s - r * g) *
      alignedEleventhRootCompanion410 p0 r κ3 κ7 = 0 :=
    (mul_eq_zero.mp hrow').resolve_left (by norm_num)
  exact mul_eq_zero.mp hproduct

#print axioms alignedEleventhRootLeading_factor410
#print axioms alignedEleventhRootLeading_split410

end Max11DegreeRoutes
