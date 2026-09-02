import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI4EightSourceScratch

/-! # Cross the exact `I4(8)` row with the frozen `I3(8)` cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI4EightCross68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let b := B.coeff 2
  (-(b ^ 2 * B.coeff 4) / 3 +
    b * G.coeff 6 + B.coeff 4 * G.coeff 4 +
    B.coeff 5 * G.coeff 3 + b6 * G.coeff 2 +
    B.coeff 7 * G.coeff 1 + B.coeff 8 * G.coeff 0 +
    B.coeff 9 * (sigma * r ^ 3 * b / 27) +
    B.coeff 10 * G.coeff (-2) -
    (sigma * r * b / 3) * F.coeff 7 +
    C.coeff 2 * F.coeff 6 + C.coeff 3 * F.coeff 5 +
    C.coeff 4 * F.coeff 4 + C.coeff 5 * F.coeff 3 +
    C.coeff 6 * F.coeff 2 +
    C.coeff 7 * (A.coeff (-1) * b / 3) +
    C.coeff 8 * (r ^ 2 * b / 9) +
    (3 / 4 : k) * T.source.epsilon * B.coeff 8)

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i4eight_reduce68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0)
    (hray : 27 * (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2)
    (hrf : r * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      3 * sigma * (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    (hlinear : 3 * (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 + sigma * r *
      (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0)
    (hb3 : (ratFuncAtHahn46 T.root T.source.B).coeff 3 = 0)
    (hD : 3 * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
      (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
        (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0)
    (hi4 : rhoOne_boundaryG_i4eightExpandedSourceRow68 T = 0) :
    rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6) = 0 := by
  have hgm1 : (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hc1 : (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 =
      -(sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hf0mul : r * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      r * (r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) := by
    rw [hrf, hgm1]
    calc
      3 * sigma * (sigma * r ^ 3 *
          (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27) =
          sigma ^ 2 * r ^ 3 *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9 := by ring
      _ = r * (r ^ 2 *
          (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) := by
        rw [hsigma]
        ring
  have hf0 : (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9 :=
    mul_left_cancel₀ hr0 hf0mul
  have hf1 : (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1 =
      (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
        (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3 := by
    linear_combination (1 / 3 : k) * hD
  dsimp only [rhoOne_boundaryG_i4eightExpandedSourceRow68,
    rhoOne_boundaryG_i4eightHahnRow68,
    rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68] at hi4 ⊢
  rw [hb3, hgm1, hc1, hf0, hf1] at hi4
  linear_combination hi4

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i4eight_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r b6 =
      rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0 +
        G.coeff 2 * b6 := by
  dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_i4eight_cross68
    (X0 X1 Y0 Y1 b : k)
    (hx : X0 + X1 * b = 0) (hy : Y0 + Y1 * b = 0) :
    Y1 * X0 - X1 * Y0 = 0 := by
  linear_combination Y1 * hx - X1 * hy

def rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68
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
  let H0 := rhoOne_boundaryG_signedRayLinearDZeroI4SevenAtB6_68 T sigma r 0
  let G1 := G.coeff 1
  let V0 := rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0
  let G2 := G.coeff 2
  rhoOne_boundaryG_signedRayLinearDZeroI3EightMSplit68 T sigma r ∧
  rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r
    (B.coeff 6) = 0 ∧
  ((M = 0 ∧ G2 * J80 - N8 * V0 = 0 ∧
      G2 * H0 - G1 * V0 = 0) ∨
   (M ≠ 0 ∧ M * V0 - G2 * K0 = 0))

def rhoOne_boundaryG_signedRayLinearDZeroI4EightCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI3EightCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4EightCross68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3EightReduction68 T ∧
  rhoOne_boundaryG_i4eightExpandedSourceRow68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4EightCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i4eight_cross68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3EightReduction68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4EightCross68 T := by
  have hrow := T.rhoOne_boundaryG_i4eight_expanded_source68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3EightReduction68] at Rc
  rcases Rc with ⟨Rold, hi3eight, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4EightCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4EightCells68]
    intro hD
    have hactual := rhoOne_boundaryG_signedRayLinear_dZero_i4eight_reduce68
      T sigma r hsigma hr0 hray hrf hlinear hb3 hD hrow
    have haff := rhoOne_boundaryG_signedRayLinear_dZero_i4eight_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    dsimp only at haff
    have hV : rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68
          T sigma r 0 + (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 2 *
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← haff]
      exact hactual
    have hOldCells := hcellsOld hD
    have hOldSplit := hOldCells.2
    have hJactual := hOldSplit.2.1
    have hJaff := rhoOne_boundaryG_signedRayLinear_dZero_i3eight_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    have hJ : rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68
          T sigma r 0 + rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68
            T r * (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← hJaff]
      exact hJactual
    have hOld4 := hOldSplit.1
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68
        T sigma r := by
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3EightMSplit68] at hOldSplit
      rcases hOldSplit.2.2 with hm | hm
      · have hdJ := rhoOne_boundaryG_signedRayLinear_i4eight_cross68
            (rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0)
            (rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r)
            (rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0)
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 6) hJ hV
        have h4c := hOld4
        dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4SevenMSplit68] at h4c
        rcases h4c with h4 | h4
        · have h4aff := rhoOne_boundaryG_signedRayLinear_dZero_i4seven_affine68
              T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
          dsimp only at h4aff
          have hH : rhoOne_boundaryG_signedRayLinearDZeroI4SevenAtB6_68
                T sigma r 0 + (rhoOneTangentEDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0))
                  (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.E))).coeff 1 *
                (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
            rw [← h4aff]
            exact h4.2.2.2.2.1
          have hdH := rhoOne_boundaryG_signedRayLinear_i4eight_cross68
            _ _ _ _ _ hH hV
          dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68]
          exact ⟨hOldSplit, hactual, Or.inl ⟨hm.1, hdJ, hdH⟩⟩
        · exact False.elim (h4.1 hm.1)
      · have ht := rhoOne_boundaryG_signedRayLinear_dZero_i3seven_M_transport68
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
              (3 / 4 : k) * T.source.epsilon)
            (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
            (rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0)
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
            hm.1 (by
              have h4c := hOld4
              dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4SevenMSplit68] at h4c
              rcases h4c with h4 | h4
              · exact False.elim (hm.1 h4.1)
              · exact h4.2.1) hV
        dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68]
        exact ⟨hOldSplit, hactual, Or.inr ⟨hm.1, ht⟩⟩
    exact ⟨hcellsOld, hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4EightCross68]
  exact ⟨R, hrow, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroI4EightCross68

end Max11DegreeRoutes
