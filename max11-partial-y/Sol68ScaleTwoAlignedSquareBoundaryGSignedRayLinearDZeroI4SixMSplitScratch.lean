import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI4SixCrossScratch

/-! # The exact `M = G[0] + 3 epsilon / 4` split after `I4(6)` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI4SixMSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Pure scalar normalization of the affine `I4(6)` packet.  The zero cell
forces the B6-free coefficient to vanish.  On the nonzero cell all three
affine quantities are transported exactly through `K0 / M`. -/
theorem rhoOne_boundaryG_signedRayLinear_dZero_i4six_M_split68
    (sigma r b L J0 I4b M K0 b6 : k)
    (h6 : K0 + M * b6 = 0)
    (h36 : 81 * M * J0 + 8 * L * K0 = 0)
    (h46 : sigma * r ^ 3 * b * K0 - 27 * M * I4b = 0) :
    (M = 0 ∧ K0 = 0) ∨
      (M ≠ 0 ∧ b6 = -K0 / M ∧
        J0 = -(8 * L * K0) / (81 * M) ∧
        I4b = sigma * r ^ 3 * b * K0 / (27 * M)) := by
  by_cases hM : M = 0
  · left
    refine ⟨hM, ?_⟩
    rw [hM] at h6
    simpa using h6
  · right
    have h81M : (81 : k) * M ≠ 0 := mul_ne_zero (by norm_num) hM
    have h27M : (27 : k) * M ≠ 0 := mul_ne_zero (by norm_num) hM
    refine ⟨hM, ?_, ?_, ?_⟩
    · apply (eq_div_iff hM).2
      linear_combination h6
    · apply (eq_div_iff h81M).2
      linear_combination h36
    · apply (eq_div_iff h27M).2
      linear_combination -h46

/-- The two old `K` cells refined by the exact `M` dichotomy.  The imported
`I4(6)` packet remains a conjunct of the source-facing wrapper, so no prior
equation or sibling is discarded here. -/
def rhoOne_boundaryG_signedRayLinearDZeroI4SixMSplitCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let K := r ^ 4 * B.coeff 2 ^ 2 - 162 * C.coeff 2 * G.coeff (-2)
  let T0 := rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
    T sigma r 0
  let I0 := rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
    T sigma r 0
  let I4b := rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r
  let J0 := rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0
  let L := -3 * r ^ 2 * F.coeff 2 +
    3 * A.coeff (-1) ^ 2 * B.coeff 2 + A.coeff 0 * r ^ 2 * B.coeff 2
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  let MSplit :=
    (M = 0 ∧ K0 = 0) ∨
      (M ≠ 0 ∧ B.coeff 6 = -K0 / M ∧
        J0 = -(8 * L * K0) / (81 * M) ∧
        I4b = sigma * r ^ 3 * B.coeff 2 * K0 / (27 * M))
  D0 = 0 →
    ((K = 0 ∧ C.coeff 2 ≠ 0 ∧ I0 = 0 ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧ MSplit) ∨
      (K ≠ 0 ∧ (T0 = 0 ↔ I0 = 0) ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧ MSplit))

/-- Source-facing `M`-split successor. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixMSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4SixMSplitCells68 T sigma r

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i4six_M_split68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixMSplit68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixCross68] at Rc
  rcases Rc with ⟨Rold, hi4sixSource, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4SixMSplitCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4SixMSplitCells68]
    intro hD
    have h6aff := rhoOne_boundaryG_signedRayLinear_dZero_i4six_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    dsimp only at h6aff
    rcases hcellsOld hD with hz | hn
    · rcases hz with ⟨hK, hC2, hI0, hlead, h3actual, h6actual,
        hprior, h36, h46⟩
      have h6base :
          rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0 +
            ((rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
              (3 / 4 : k) * T.source.epsilon) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
        rw [← h6aff]
        exact h6actual
      have hsplit := rhoOne_boundaryG_signedRayLinear_dZero_i4six_M_split68
        sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
        (-3 * r ^ 2 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 2 +
         3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-1) ^ 2 *
           (ratFuncAtHahn46 T.root T.source.B).coeff 2 +
         (ratFuncAtHahn46 T.root T.source.A).coeff 0 * r ^ 2 *
           (ratFuncAtHahn46 T.root T.source.B).coeff 2)
        (rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0)
        (rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r)
        ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
          (3 / 4 : k) * T.source.epsilon)
        (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
        h6base h36 h46
      exact Or.inl ⟨hK, hC2, hI0, hlead, hsplit⟩
    · rcases hn with ⟨hK, hTI, hlead, h3actual, h6actual,
        hprior, h36, h46⟩
      have h6base :
          rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0 +
            ((rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
              (3 / 4 : k) * T.source.epsilon) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
        rw [← h6aff]
        exact h6actual
      have hsplit := rhoOne_boundaryG_signedRayLinear_dZero_i4six_M_split68
        sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
        (-3 * r ^ 2 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 2 +
         3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-1) ^ 2 *
           (ratFuncAtHahn46 T.root T.source.B).coeff 2 +
         (ratFuncAtHahn46 T.root T.source.A).coeff 0 * r ^ 2 *
           (ratFuncAtHahn46 T.root T.source.B).coeff 2)
        (rhoOne_boundaryG_signedRayLinearDZeroI3SixAtB6_68 T sigma r 0)
        (rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r)
        ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
          (3 / 4 : k) * T.source.epsilon)
        (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
        h6base h36 h46
      exact Or.inr ⟨hK, hTI, hlead, hsplit⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixMSplit68]
  exact ⟨R, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

/-- Outer selector preserving coordinate, QR, and nonsingular siblings. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i4six_M_split_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SixMSplit68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_i4six_cross_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hzero | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_i4six_M_split68 hzero)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroI4SixMSplit68

end Max11DegreeRoutes
