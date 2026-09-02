import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJetScratch

/-! # Exact source-backed `I4(9)` on the finite `I3(9)` slope cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4nineFactoredSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI4ZeroFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon) B C F G).coeff 9

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i4nine_factored68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon)
      (ratFuncAtHahn46 root B) (ratFuncAtHahn46 root C)
      (ratFuncAtHahn46 root F) (ratFuncAtHahn46 root G)).coeff 9 = 0 := by
  have hi4H := congrArg (ratFuncAtHahn46 root) hi4
  have hi4H' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon)
      (ratFuncAtHahn46 root B) (ratFuncAtHahn46 root C)
      (ratFuncAtHahn46 root F) (ratFuncAtHahn46 root G) = HahnSeries.C i4 := by
    simpa only [rhoOneI4ZeroFactored68, map_add, map_mul, map_pow,
      map_neg, map_div₀, map_ofNat, ratFuncAtHahn46_C] using hi4H
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff 9) hi4H'
  simpa [HahnSeries.C_apply] using hc

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4nine_factored_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i4nineFactoredSourceRow68 T = 0 := by
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
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hCmap : ratFuncAtHahn46 T.root C = rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F = rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E = rhoOneEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G = rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hrow := ratFunc_boundaryG_i4nine_factored68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hi4f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4nineAtB6_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (b6 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (rhoOneI4ZeroFactored68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon)
    (rhoOne_boundaryG_replaceB6_68 B b6) C F G).coeff 9

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4nineB6Slope68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (8 / 3 : k) * G.coeff 3

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i4nine_replace_affine68
    (gamma epsilon : k) (B C F G : HahnSeries ℚ k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (b6 : k) :
    (rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        (rhoOne_boundaryG_replaceB6_68 B b6) C F G).coeff 9 =
      (rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
        (rhoOne_boundaryG_replaceB6_68 B 0) C F G).coeff 9 +
      (8 / 3 : k) * G.coeff 3 * b6 := by
  let B0 := rhoOne_boundaryG_replaceB6_68 B 0
  let s : HahnSeries ℚ k := HahnSeries.single 6 b6
  have hBform : rhoOne_boundaryG_replaceB6_68 B b6 = B0 + s := by
    dsimp only [B0, s, rhoOne_boundaryG_replaceB6_68]
    simp
  have hsix : (↑(2 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (6 : ℚ) (B.coeff 6) : HahnSeries ℚ k).orderTop := by
    by_cases hb : B.coeff 6 = 0
    · simp [hb]
    · rw [HahnSeries.orderTop_single hb]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  have hB0 : (↑(2 : ℚ) : WithTop ℚ) ≤ B0.orderTop := by
    dsimp only [B0, rhoOne_boundaryG_replaceB6_68]
    rw [show (HahnSeries.single (6 : ℚ) (0 : k) : HahnSeries ℚ k) = 0 by
      simp, add_zero]
    have hmin : (↑(2 : ℚ) : WithTop ℚ) ≤
        min B.orderTop
          (HahnSeries.single (6 : ℚ) (B.coeff 6) : HahnSeries ℚ k).orderTop :=
      min_le_min hB hsix
    exact le_trans hmin HahnSeries.min_orderTop_le_orderTop_sub
  have hB02 : (↑(4 : ℚ) : WithTop ℚ) ≤ (B0 ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by convert add_le_add hB0 hB0 using 1 <;> norm_num)
      HahnSeries.orderTop_add_le_mul
  have hB02c3 : (B0 ^ 2).coeff 3 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB02)
  have hB0neg3 : B0.coeff (-3) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB0)
  have hsB02 : (s * B0 ^ 2).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [hB02c3]
  have hs2B0 : (s ^ 2 * B0).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
    norm_num
    simp [hB0neg3]
  have hs3 : (s ^ 3).coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single]
    norm_num
  have hsG : (s * G).coeff 9 = b6 * G.coeff 3 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hs : s.coeff 9 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single]
    norm_num
  have hpoly :
      rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          (B0 + s) C F G =
        rhoOneI4ZeroFactored68 (HahnSeries.C gamma) (HahnSeries.C epsilon)
          B0 C F G +
        HahnSeries.C (-(24 / 27 : k)) * (s * B0 ^ 2) +
        HahnSeries.C (-(24 / 27 : k)) * (s ^ 2 * B0) +
        HahnSeries.C (-(8 / 27 : k)) * s ^ 3 +
        HahnSeries.C (8 / 3 : k) * (s * G) +
        HahnSeries.C (2 * epsilon) * s := by
    simp only [rhoOneI4ZeroFactored68, HahnSeries.C_eq_algebraMap,
      map_mul, map_neg, map_div₀, map_ofNat]
    ring_nf
  have hscale (c : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C c * X).coeff n = c * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hBform, hpoly]
  simp only [HahnSeries.coeff_add, hscale, hsB02, hs2B0, hs3,
    hsG, hs, mul_zero, add_zero]
  ring

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4nine_actual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_i4nineAtB6_68 T
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6) =
      rhoOne_boundaryG_i4nineFactoredSourceRow68 T := by
  dsimp only [rhoOne_boundaryG_i4nineAtB6_68,
    rhoOne_boundaryG_i4nineFactoredSourceRow68]
  rw [rhoOne_boundaryG_replaceB6_self68]

def rhoOne_boundaryG_signedRayLinearDZeroI4NineCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6Slope68 T
  let W90 := rhoOne_boundaryG_i4nineAtB6_68 T 0
  let L9 := rhoOne_boundaryG_i4nineB6Slope68 T
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeJetCells68 T sigma r ∧
    rhoOne_boundaryG_i4nineAtB6_68 T (B.coeff 6) = 0 ∧
    W90 + L9 * B.coeff 6 = 0 ∧
    L9 * J90 - N9 * W90 = 0 ∧
    ((L9 = 0 ∧ W90 = 0) ∨
     (L9 ≠ 0 ∧ B.coeff 6 = -W90 / L9))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68 T ∧
  rhoOne_boundaryG_i4nineFactoredSourceRow68 T = 0 ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4NineCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68 T := by
  have hrow := T.rhoOne_boundaryG_i4nine_factored_source68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68] at Rc
  rcases Rc.2 with ⟨sigma, r, hr0, hr, hcellsOld⟩
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
  let B := ratFuncAtHahn46 T.root T.source.B
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4NineCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineCells68]
    intro hD
    have hold := hcellsOld hD
    have hactual : rhoOne_boundaryG_i4nineAtB6_68 T (B.coeff 6) = 0 := by
      rw [T.rhoOne_boundaryG_i4nine_actual68]
      exact hrow
    have haff := rhoOne_boundaryG_i4nine_replace_affine68 T.source.gamma
      T.source.epsilon B
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A) B
        (ratFuncAtHahn46 T.root T.source.D))
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))) hB (B.coeff 6)
    have hW : rhoOne_boundaryG_i4nineAtB6_68 T 0 +
        rhoOne_boundaryG_i4nineB6Slope68 T * B.coeff 6 = 0 := by
      dsimp only [B, rhoOne_boundaryG_i4nineAtB6_68,
        rhoOne_boundaryG_i4nineB6Slope68] at haff ⊢
      rw [← haff]
      exact hactual
    have hNsplit := hold.2.2
    have hslopeJet := hold.2.1
    have hJ : rhoOne_boundaryG_i3nineAtB6_68 T 0 +
        rhoOne_boundaryG_i3nineB6Slope68 T * B.coeff 6 = 0 := by
      rcases hNsplit with hz | hn
      · rw [hslopeJet, hz.1, hz.2, zero_mul, add_zero]
      · rw [hslopeJet, hn.2]
        field_simp [hn.1]
        ring
    have hcross := rhoOne_boundaryG_signedRayLinear_i4eight_cross68
      (rhoOne_boundaryG_i3nineAtB6_68 T 0)
      (rhoOne_boundaryG_i3nineB6Slope68 T)
      (rhoOne_boundaryG_i4nineAtB6_68 T 0)
      (rhoOne_boundaryG_i4nineB6Slope68 T)
      (B.coeff 6) hJ hW
    have hsplit := rhoOne_boundaryG_i3nine_zero_slope_split68
      (rhoOne_boundaryG_i4nineAtB6_68 T 0)
      (rhoOne_boundaryG_i4nineB6Slope68 T) (B.coeff 6) hW
    exact ⟨hcellsOld, hactual, hW, hcross, hsplit⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68]
  exact ⟨R, hrow, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68

end Max11DegreeRoutes
