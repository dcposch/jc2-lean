import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminantsScratch

/-! # Finite-jet form of the exact `I3(9)` `B[6]` slope -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i3nineB6SlopeExpanded68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  (-(8 / 9 : k)) *
    (A.coeff (-2) * F.coeff 5 + A.coeff (-1) * F.coeff 4 +
     A.coeff 0 * F.coeff 3 + A.coeff 1 * F.coeff 2 +
     A.coeff 2 * F.coeff 1 + A.coeff 3 * F.coeff 0) -
  (16 / 9 : k) * B.coeff 2 * C.coeff 1

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i3nine_B6_slope_expanded68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hb3 : (ratFuncAtHahn46 T.root T.source.B).coeff 3 = 0) :
    rhoOne_boundaryG_i3nineB6Slope68 T =
      rhoOne_boundaryG_i3nineB6SlopeExpanded68 T := by
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
  let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
  let A := ratFuncAtHahn46 T.root AR
  let B := ratFuncAtHahn46 T.root BR
  let C := ratFuncAtHahn46 T.root CR
  let F := ratFuncAtHahn46 T.root FR
  let AL := ratFuncAtLaurent46 T.root AR
  let BL := ratFuncAtLaurent46 T.root BR
  let CL := ratFuncAtLaurent46 T.root CR
  let FL := ratFuncAtLaurent46 T.root FR
  have hCmap : C = rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, CR, AR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : F = rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, FR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(((-2 : ℤ) : ℚ)) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root AR).orderTop := by
    dsimp only [AR]
    convert hA using 1 <;> norm_num
  have hBH : (↑(((2 : ℤ) : ℚ)) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by
    dsimp only [BR]
    convert hB using 1 <;> norm_num
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root AR (-2) hAH
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root BR 2 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root CR 0
    (by
      change (↑(0 : ℚ) : WithTop ℚ) ≤ C.orderTop
      rw [hCmap]
      exact hC)
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root FR 0
    (by
      change (↑(0 : ℚ) : WithTop ℚ) ≤ F.orderTop
      rw [hFmap]
      exact hF)
  have hAFL := laurent_coeff_mul_lower_five68 AL FL (-2) 0 hAL hFL
  have hBCL := laurent_coeff_mul_lower_succ68 BL CL 2 0 hBL hCL
  norm_num at hAFL hBCL
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root R n
  have hAFprod := hcs (AR * FR) 3
  have hBCprod := hcs (BR * CR) 3
  simp only [map_mul] at hAFprod hBCprod
  norm_num at hAFprod hBCprod
  have hAF : (A * F).coeff 3 =
      A.coeff (-2) * F.coeff 5 + A.coeff (-1) * F.coeff 4 +
      A.coeff 0 * F.coeff 3 + A.coeff 1 * F.coeff 2 +
      A.coeff 2 * F.coeff 1 + A.coeff 3 * F.coeff 0 := by
    dsimp only [A, F]
    rw [hAFprod]
    have h := hAFL
    simp only [AL, FL, ← hcs AR (-2), ← hcs AR (-1), ← hcs AR 0,
      ← hcs AR 1, ← hcs AR 2, ← hcs AR 3,
      ← hcs FR 0, ← hcs FR 1, ← hcs FR 2, ← hcs FR 3,
      ← hcs FR 4, ← hcs FR 5] at h
    exact h
  have hBC : (B * C).coeff 3 = B.coeff 2 * C.coeff 1 := by
    dsimp only [B, C]
    rw [hBCprod]
    have h := hBCL
    simp only [BL, CL, ← hcs BR 2, ← hcs BR 3,
      ← hcs CR 0, ← hcs CR 1] at h
    norm_num at h
    have hb3R : (ratFuncAtHahn46 T.root BR).coeff (3 : ℚ) = 0 := by
      dsimp only [BR]
      exact hb3
    rw [hb3R, zero_mul, add_zero] at h
    simpa using h
  have hCneg3 : C.coeff (-3) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have hlt : (↑(-3 : ℚ) : WithTop ℚ) < (0 : WithTop ℚ) :=
      WithTop.coe_lt_coe.mpr (by norm_num)
    exact lt_of_lt_of_le hlt (by rw [hCmap]; exact hC)
  have hremove :
      (rhoOne_boundaryG_replaceB6_68 B 0 * C).coeff 3 = (B * C).coeff 3 := by
    have hs : (HahnSeries.single (6 : ℚ) (B.coeff 6) * C).coeff 3 = 0 := by
      rw [HahnSeries.coeff_single_mul]
      norm_num
      simp [hCneg3]
    dsimp only [rhoOne_boundaryG_replaceB6_68]
    simp only [add_mul, sub_mul, HahnSeries.coeff_add, HahnSeries.coeff_sub]
    simp [hs]
  dsimp only [A, AR] at hAF
  rw [hFmap] at hAF
  dsimp only [B, BR] at hBC hremove
  rw [hCmap] at hBC hremove
  dsimp only [rhoOne_boundaryG_i3nineB6Slope68,
    rhoOne_boundaryG_i3nineB6SlopeExpanded68]
  rw [hAF, hremove, hBC]
  ring

def rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeJetCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9jet := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantCells68 T sigma r ∧
    rhoOne_boundaryG_i3nineB6Slope68 T = N9jet ∧
    ((N9jet = 0 ∧ J90 = 0) ∨
     (N9jet ≠ 0 ∧ B.coeff 6 = -J90 / N9jet))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68 T ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeJetCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine_slope_jet68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68] at Rc
  rcases Rc.2 with ⟨sigma, r, hr0, hr, hcellsOld⟩
  have Rred := Rc.1
  have Rredc := Rred
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68] at Rredc
  have Rwall := Rredc.1.1
  have Rwallc := Rwall
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68] at Rwallc
  have Rsplit := Rwallc.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68] at Rsplit
  rcases Rsplit.2 with ⟨sigma', r', hsigma, hr0', hb, hgm2, hr', hray,
    hrf, hlinear, hb3, hwitness, hcells'⟩
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  have hslopeExpanded := T.rhoOne_boundaryG_i3nine_B6_slope_expanded68
    P.2.1.1 hB hC hF hb3
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeJetCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeJetCells68]
    intro hD
    have hold := hcellsOld hD
    have hs := hold.2
    have hsc := hs
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68] at hsc
    have hslopeJet : rhoOne_boundaryG_i3nineB6Slope68 T =
        rhoOne_boundaryG_i3nineB6SlopeExpanded68 T := hslopeExpanded
    have hsplit := hsc.2.1
    have hsplitJet :
        (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T = 0 ∧
          rhoOne_boundaryG_i3nineAtB6_68 T 0 = 0) ∨
        (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T ≠ 0 ∧
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 =
            -rhoOne_boundaryG_i3nineAtB6_68 T 0 /
              rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) := by
      rw [← hslopeJet]
      exact hsplit
    exact ⟨hcellsOld, hslopeJet, hsplitJet⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68]
  exact ⟨R, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68

end Max11DegreeRoutes
