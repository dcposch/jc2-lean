import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineScratch

/-! # Exact `B[6]` reduction of source-backed `I3(9)` on the slope-wall cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_replaceB6_68 (B : HahnSeries ℚ k) (b6 : k) : HahnSeries ℚ k :=
  B - HahnSeries.single 6 (B.coeff 6) + HahnSeries.single 6 b6

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceB6_self68 (B : HahnSeries ℚ k) :
    rhoOne_boundaryG_replaceB6_68 B (B.coeff 6) = B := by
  dsimp only [rhoOne_boundaryG_replaceB6_68]
  abel

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i3nineAtB6_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (b6 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI3CapFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon) A
    (rhoOne_boundaryG_replaceB6_68 B b6) C F G).coeff 9

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i3nineB6Slope68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let B0 := rhoOne_boundaryG_replaceB6_68 B 0
  (-(8 / 9 : k)) * (A * F).coeff 3 -
    (16 / 9 : k) * (B0 * C).coeff 3

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3nine_replace_affine68
    (gamma epsilon : k) (A B C F G : HahnSeries ℚ k)
    (hCneg3 : C.coeff (-3) = 0) (hB3 : B.coeff 3 = 0)
    (b6 : k) :
    (rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        A (rhoOne_boundaryG_replaceB6_68 B b6) C F G).coeff 9 =
      (rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        A (rhoOne_boundaryG_replaceB6_68 B 0) C F G).coeff 9 +
      ((-(8 / 9 : k)) * (A * F).coeff 3 -
        (16 / 9 : k) *
          (rhoOne_boundaryG_replaceB6_68 B 0 * C).coeff 3) * b6 := by
  let B0 := rhoOne_boundaryG_replaceB6_68 B 0
  let s : HahnSeries ℚ k := HahnSeries.single 6 b6
  have hBform : rhoOne_boundaryG_replaceB6_68 B b6 = B0 + s := by
    dsimp only [B0, s, rhoOne_boundaryG_replaceB6_68]
    simp
  have hB03 : B0.coeff 3 = 0 := by
    dsimp only [B0, rhoOne_boundaryG_replaceB6_68]
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub,
      HahnSeries.coeff_single, if_neg (by norm_num : (3 : ℚ) ≠ 6),
      sub_zero, add_zero]
    exact hB3
  have hpoly :
      rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          A (B0 + s) C F G =
        rhoOneI3CapFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          A B0 C F G +
        HahnSeries.C (-(8 / 9 : k)) * (s * (A * F)) +
        HahnSeries.C (-(16 / 9 : k)) * (s * (B0 * C)) +
        HahnSeries.C (-(8 / 9 : k)) * (s ^ 2 * C) +
        HahnSeries.C (-(4 / 3 : k) * gamma) * (s * B0) +
        HahnSeries.C (-(2 / 3 : k) * gamma) * s ^ 2 := by
    simp only [rhoOneI3CapFactored68, HahnSeries.C_eq_algebraMap,
      map_mul, map_neg, map_div₀, map_ofNat]
    ring
  have hsAF : (s * (A * F)).coeff 9 = b6 * (A * F).coeff 3 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hsBC : (s * (B0 * C)).coeff 9 = b6 * (B0 * C).coeff 3 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hs2C : (s ^ 2 * C).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
    norm_num
    simp [hCneg3]
  have hsB0 : (s * B0).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [hB03]
  have hs2 : (s ^ 2).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single]
    norm_num
  have hscale (c : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C c * X).coeff n = c * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hBform, hpoly]
  simp only [HahnSeries.coeff_add, hscale, hsAF, hsBC, hs2C, hsB0,
    hs2, mul_zero, add_zero]
  ring

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i3nine_actual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_i3nineAtB6_68 T
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6) =
      rhoOne_boundaryG_i3nineFactoredSourceRow68 T := by
  dsimp only [rhoOne_boundaryG_i3nineAtB6_68,
    rhoOne_boundaryG_i3nineFactoredSourceRow68]
  rw [rhoOne_boundaryG_replaceB6_self68]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3nine_cross_terminal68
    (J N Base Slope b6 : k)
    (hJ : J + N * b6 = 0) (hT : Base + Slope * b6 = 0) :
    N * Base - Slope * J = 0 := by
  linear_combination N * hT - Slope * hJ

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3nine_zero_slope_split68
    (J N b6 : k) (hJ : J + N * b6 = 0) :
    (N = 0 ∧ J = 0) ∨ (N ≠ 0 ∧ b6 = -J / N) := by
  by_cases hN : N = 0
  · left
    constructor
    · exact hN
    · rw [hN, zero_mul, add_zero] at hJ
      exact hJ
  · right
    refine ⟨hN, ?_⟩
    apply (eq_div_iff hN).2
    linear_combination hJ

def rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  let J80 := rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0
  let N8 := rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r
  let V0 := rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0
  let G2 := G.coeff 2
  let Base := rhoOne_boundaryG_terminalZeroB6BaseSource68 T
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let Wall := rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6Slope68 T
  rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68 T sigma r ∧
  ((M = 0 ∧
      ((Slope = 0 ∧ Base = 0 ∧ Wall = 0 ∧
          ((N9 = 0 ∧ J90 = 0) ∨
           (N9 ≠ 0 ∧ B.coeff 6 = -J90 / N9))) ∨
       (Slope ≠ 0 ∧ B.coeff 6 = -Base / Slope ∧
        J80 = N8 * Base / Slope ∧ V0 = G2 * Base / Slope ∧
        N9 * Base - Slope * J90 = 0))) ∨
   (M ≠ 0 ∧
      ((Slope = 0 ∧ Base = 0 ∧ Wall = 0 ∧
          ((N9 = 0 ∧ J90 = 0) ∨
           (N9 ≠ 0 ∧ B.coeff 6 = -J90 / N9))) ∨
       (Slope ≠ 0 ∧ B.coeff 6 = -Base / Slope ∧
        K0 = M * Base / Slope ∧
        N9 * Base - Slope * J90 = 0))))

def rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3Nine68 T ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine_reduction68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3Nine68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3Nine68] at Rc
  have Rwall := Rc.1
  have Rwallc := Rwall
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68] at Rwallc
  rcases Rwallc.2 with ⟨sigma, r, hr0, hr, hcellsWall⟩
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
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  have hCneg3 : C.coeff (-3) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hC
  have hactual : rhoOne_boundaryG_i3nineAtB6_68 T (B.coeff 6) = 0 := by
    rw [T.rhoOne_boundaryG_i3nine_actual68]
    exact Rc.2
  have haff := rhoOne_boundaryG_i3nine_replace_affine68 T.source.gamma
    T.source.epsilon A B C
    (rhoOneTangentDDefectHahn68 A B (ratFuncAtHahn46 T.root T.source.D))
    (rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E)))
    hCneg3
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallCells68]
    intro hD
    have hold := hcellsWall hD
    have hs := hold.2
    have hsc := hs
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68] at hsc
    have hb3 : B.coeff 3 = 0 := by
      have Rsplit := Rwallc.1
      dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68] at Rsplit
      rcases Rsplit with ⟨Rold, sigma', r', hsigma', hr0', hb', hgm2',
        hr', hray', hrf', hlinear', hb3', hwitness', hcells'⟩
      exact hb3'
    have hJaff := haff hb3 (B.coeff 6)
    have hJ : rhoOne_boundaryG_i3nineAtB6_68 T 0 +
        rhoOne_boundaryG_i3nineB6Slope68 T * B.coeff 6 = 0 := by
      dsimp only [A, B, C, rhoOne_boundaryG_i3nineAtB6_68,
        rhoOne_boundaryG_i3nineB6Slope68] at hJaff ⊢
      rw [← hJaff]
      exact hactual
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68
        T sigma r := by
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68]
      rcases hsc.2 with hm | hm
      · rcases hm.2 with hz | hn
        · exact ⟨hs, Or.inl ⟨hm.1, Or.inl
            ⟨hz.1, hz.2.1, hz.2.2,
              rhoOne_boundaryG_i3nine_zero_slope_split68 _ _ _ hJ⟩⟩⟩
        · have hcross := rhoOne_boundaryG_i3nine_cross_terminal68
            (rhoOne_boundaryG_i3nineAtB6_68 T 0)
            (rhoOne_boundaryG_i3nineB6Slope68 T)
            (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
            (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
            (B.coeff 6) hJ
            (by
              rw [hn.2.1]
              field_simp [hn.1]
              ring
            )
          exact ⟨hs, Or.inl ⟨hm.1, Or.inr
            ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hcross⟩⟩⟩
      · rcases hm.2 with hz | hn
        · exact ⟨hs, Or.inr ⟨hm.1, Or.inl
            ⟨hz.1, hz.2.1, hz.2.2,
              rhoOne_boundaryG_i3nine_zero_slope_split68 _ _ _ hJ⟩⟩⟩
        · have hcross := rhoOne_boundaryG_i3nine_cross_terminal68
            (rhoOne_boundaryG_i3nineAtB6_68 T 0)
            (rhoOne_boundaryG_i3nineB6Slope68 T)
            (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
            (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
            (B.coeff 6) hJ
            (by
              rw [hn.2.1]
              field_simp [hn.1]
              ring
            )
          exact ⟨hs, Or.inr ⟨hm.1, Or.inr
            ⟨hn.1, hn.2.1, hn.2.2, hcross⟩⟩⟩
    have hold' : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallCells68
        T sigma r := by
      exact hcellsWall
    exact ⟨hold', hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68]
  exact ⟨R, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68

end Max11DegreeRoutes
