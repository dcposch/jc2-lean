import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3I4ElevenAffineCellsScratch

/-! # Independence audit for the retained base-affine scalar rows -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroBaseCoeffStructuralAudit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_baseAffine_cross_iff68
    (sigma r a b gm2 gm1 coeff const delta : k)
    (hgm2 : gm2 ≠ 0)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (htransport : delta =
      (2 * a * sigma * r ^ 3 * b) / (27 * gm2)) :
    gm2 * const + 2 * a * gm1 * coeff = 0 ↔
      const + coeff * delta = 0 := by
  have hden : (27 : k) * gm2 ≠ 0 := mul_ne_zero (by norm_num) hgm2
  have htransportClear :
      delta * (27 * gm2) - 2 * a * sigma * r ^ 3 * b = 0 := by
    have ht := (eq_div_iff hden).mp htransport
    linear_combination ht
  have hDeltaClear : gm2 * delta - 2 * a * gm1 = 0 := by
    linear_combination (1 / 27 : k) * htransportClear -
      (2 * a / 27 : k) * hray
  constructor
  · intro hcross
    have hscaled : gm2 * (const + coeff * delta) = 0 := by
      linear_combination hcross + coeff * hDeltaClear
    exact (mul_eq_zero.mp hscaled).resolve_left hgm2
  · intro haffine
    exact rhoOne_boundaryG_terminalZeroB6_affine_transport_cross68
      sigma r a b gm2 gm1 coeff const delta hgm2 hray htransport haffine

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_baseAffine_retained_rows_admit_both_cells68
    (sigma r a b gm2 gm1 delta : k)
    (hgm2 : gm2 ≠ 0)
    (hdelta : delta ≠ 0)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (htransport : delta =
      (2 * a * sigma * r ^ 3 * b) / (27 * gm2)) :
    (∃ coeff const : k,
      coeff = 0 ∧ const = 0 ∧
      const + coeff * delta = 0 ∧
      gm2 * const + 2 * a * gm1 * coeff = 0) ∧
    (∃ coeff const : k,
      coeff ≠ 0 ∧ const ≠ 0 ∧ delta = -const / coeff ∧
      const + coeff * delta = 0 ∧
      gm2 * const + 2 * a * gm1 * coeff = 0) := by
  constructor
  · exact ⟨0, 0, rfl, rfl, by ring, by ring⟩
  · refine ⟨1, -delta, one_ne_zero, neg_ne_zero.mpr hdelta, ?_, ?_, ?_⟩
    · field_simp
    · ring
    · exact (rhoOne_boundaryG_baseAffine_cross_iff68
        sigma r a b gm2 gm1 1 (-delta) delta hgm2 hray htransport).2
          (by ring)

def rhoOne_boundaryG_baseCoeffRetainedRowsAudit68 : Prop :=
  ∀ sigma r a b gm2 gm1 coeff const delta : k,
    gm2 ≠ 0 →
    27 * gm1 = sigma * r ^ 3 * b →
    delta = (2 * a * sigma * r ^ 3 * b) / (27 * gm2) →
    (gm2 * const + 2 * a * gm1 * coeff = 0 ↔
      const + coeff * delta = 0)

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffStructuralAudit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3I4ElevenAffineCells68 T ∧
  rhoOne_boundaryG_baseCoeffRetainedRowsAudit68 (k := k)

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_baseCoeff_structural_audit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R :
      RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3I4ElevenAffineCells68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffStructuralAudit68 T := by
  refine ⟨R, ?_⟩
  intro sigma r a b gm2 gm1 coeff const delta hgm2 hray htransport
  exact rhoOne_boundaryG_baseAffine_cross_iff68
    sigma r a b gm2 gm1 coeff const delta hgm2 hray htransport

end AlignedSquareBoundaryGSignedRayLinearDZeroBaseCoeffStructuralAudit68

end Max11DegreeRoutes
