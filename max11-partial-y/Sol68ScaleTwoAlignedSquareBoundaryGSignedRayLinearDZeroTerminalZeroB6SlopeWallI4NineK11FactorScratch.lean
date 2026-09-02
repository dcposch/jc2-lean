import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11ReductionScratch

/-! # Signed-ray factorization of the ninth-row `B[11]` slope -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_AF_negTwo68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.A).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop) :
    ((ratFuncAtHahn46 T.root T.source.A) *
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff (-2) =
      (ratFuncAtHahn46 T.root T.source.A).coeff (-2) *
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 0 := by
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
  let A := ratFuncAtHahn46 T.root AR
  let F := ratFuncAtHahn46 T.root FR
  let AL := ratFuncAtLaurent46 T.root AR
  let FL := ratFuncAtLaurent46 T.root FR
  have hFmap : F = rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, FR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root AR (-2)
    (by dsimp only [AR]; exact hA)
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root FR 0
    (by change (0 : WithTop ℚ) ≤ F.orderTop; rw [hFmap]; exact hF)
  have hmul := laurent_coeff_mul_lower68 AL FL (-2) 0 hAL hFL
  norm_num at hmul
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root R n
  have hprod := hcs (AR * FR) (-2)
  simp only [map_mul] at hprod
  norm_num at hprod
  have hlocal : (A * F).coeff (-2) = A.coeff (-2) * F.coeff 0 := by
    dsimp only [A, F]
    rw [hprod]
    have h := hmul
    simp only [AL, FL, ← hcs AR (-2), ← hcs FR 0] at h
    exact h
  dsimp only [A, AR] at hlocal
  rw [hFmap] at hlocal
  exact hlocal

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_signed_factor68
    (sigma r a f gm1 gm2 g3 n : k) (hr0 : r ≠ 0)
    (hr : r ^ 2 = -3 * a) (hrf : r * f = 3 * sigma * gm1) :
    (8 : k) * g3 * ((-(8 / 9 : k)) * a * f) -
        3 * n * ((8 / 3 : k) * gm2) =
      (8 / 9 : k) * (8 * sigma * r * g3 * gm1 - 9 * n * gm2) := by
  have ha : a = -(r ^ 2) / 3 := by
    calc
      a = -(1 / 3 : k) * (-3 * a) := by field_simp
      _ = -(1 / 3 : k) * r ^ 2 := by rw [← hr]
      _ = -(r ^ 2) / 3 := by ring
  have hf : f = 3 * sigma * gm1 / r := by
    apply (eq_div_iff hr0).2
    simpa only [mul_comm] using hrf
  rw [ha, hf]
  field_simp [hr0]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_wall_split68
    (D K Wall b : k)
    (hfac : K = (8 / 9 : k) * Wall)
    (hsplit : (K = 0 ∧ D = 0) ∨ (K ≠ 0 ∧ b = -D / K)) :
    (Wall = 0 ∧ D = 0) ∨
      (Wall ≠ 0 ∧ b = -(9 : k) * D / ((8 : k) * Wall)) := by
  have h89 : (8 / 9 : k) ≠ 0 := by norm_num
  rcases hsplit with hz | hn
  · left
    refine ⟨?_, hz.2⟩
    have hm : (8 / 9 : k) * Wall = 0 := by rw [← hfac]; exact hz.1
    exact (mul_eq_zero.mp hm).resolve_left h89
  · right
    have hWall : Wall ≠ 0 := by
      intro hw
      apply hn.1
      rw [hfac, hw, mul_zero]
    refine ⟨hWall, ?_⟩
    rw [hn.2, hfac]
    field_simp [hWall]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4nineK11Wall68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  8 * sigma * r * G.coeff 3 * G.coeff (-1) -
    9 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T * G.coeff (-2)

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11FactorCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigmaCell rCell sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let W90 := rhoOne_boundaryG_i4nineAtB6_68 T 0
  let G3 := G.coeff 3
  let J110 := rhoOne_boundaryG_i3nineAtB6B11_68 T 0
  let W110 := rhoOne_boundaryG_i4nineAtB6B11_68 T 0
  let D11 := (8 : k) * G3 * J110 - 3 * N9 * W110
  let K11 := (8 : k) * G3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
    3 * N9 * ((8 / 3 : k) * G.coeff (-2))
  let Wall := rhoOne_boundaryG_i4nineK11Wall68 T sigma r
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineB11Cells68 T sigmaCell rCell ∧
    (A * F).coeff (-2) = A.coeff (-2) * F.coeff 0 ∧
    K11 = (8 / 9 : k) * Wall ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * W90 = 0 →
      (Wall = 0 ∧ D11 = 0) ∨
      (Wall ≠ 0 ∧ B.coeff 11 = -(9 : k) * D11 / ((8 : k) * Wall)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68 T ∧
  ∃ sigmaCell rCell sigma r : k,
    rCell ≠ 0 ∧
    rCell ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    sigma ^ 2 = 1 ∧ r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    r * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      3 * sigma * (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11FactorCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_factor68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, hrCell0, hrCell, hcellsOld⟩
  have Rdet := Rc.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68] at Rdet
  have Ri4 := Rdet.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68] at Ri4
  have Rjet := Ri4.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68] at Rjet
  have Rcells := Rjet.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68] at Rcells
  have Rred := Rcells.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68] at Rred
  have Ri3 := Rred.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3Nine68] at Ri3
  have Rwall := Ri3.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68] at Rwall
  have Rsplit := Rwall.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68] at Rsplit
  rcases Rsplit.2 with ⟨sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hsourceCells⟩
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdetOld⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcrossOld⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  have hAF := T.rhoOne_boundaryG_AF_negTwo68 P.2.1.1 hF
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hfac :
      (8 : k) * G.coeff 3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
          3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
            ((8 / 3 : k) * G.coeff (-2)) =
        (8 / 9 : k) * rhoOne_boundaryG_i4nineK11Wall68 T sigma r := by
    rw [hAF]
    dsimp only [rhoOne_boundaryG_i4nineK11Wall68, A, B, C, F, G]
    simpa only [mul_assoc] using rhoOne_boundaryG_K11_signed_factor68 sigma r
      ((ratFuncAtHahn46 T.root T.source.A).coeff (-2))
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff 3)
      (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) hr0 hr hrf
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4NineK11FactorCells68
      T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11FactorCells68]
    intro hD
    have hold := hcellsOld hD
    refine ⟨hcellsOld, hAF, hfac, ?_⟩
    intro hdbl
    have hsplit := hold.2 hdbl
    exact rhoOne_boundaryG_K11_wall_split68
      ((8 : k) * G.coeff 3 * rhoOne_boundaryG_i3nineAtB6B11_68 T 0 -
        3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
          rhoOne_boundaryG_i4nineAtB6B11_68 T 0)
      ((8 : k) * G.coeff 3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
        3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
          ((8 / 3 : k) * G.coeff (-2)))
      (rhoOne_boundaryG_i4nineK11Wall68 T sigma r)
      (B.coeff 11) hfac hsplit.2.2.2
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hr, hrf, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68

end Max11DegreeRoutes
