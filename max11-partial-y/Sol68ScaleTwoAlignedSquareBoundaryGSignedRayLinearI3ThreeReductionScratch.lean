import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearI3ThreeScratch

/-! # Reduction of `I3(3)` on the signed linear factor -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearI3ThreeReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The cleared `I3(3)` row after substituting the signed ray, the linear
factor, and `B[3]=0`. -/
def rhoOne_boundaryG_signedRayLinearI3ThreeReduced68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 c4 c5
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k) : k :=
  -108 * a0 * b * f1 - 12 * a1 * b * b4 * r ^ 2 -
    108 * a1 * b * f2 - 12 * aOne * b ^ 2 * r ^ 2 +
    4 * b * b5 * r ^ 4 + 12 * b * c4 * r ^ 3 * sigma +
    72 * b * f3 * r ^ 2 - 108 * b * g2 * r * sigma +
    36 * b4 * f1 * r ^ 2 + 324 * c2 * g1 +
    243 * c3 * epsilon + 324 * c3 * g0 + 324 * c5 * gm2 +
    324 * f1 * f2

omit [IsAlgClosed k] in
/-- The part of the reduced row independent of `F[2]`. -/
def rhoOne_boundaryG_signedRayLinearI3ThreeBase68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 c4 c5
      f1 f3 g2 g1 g0 gm2 epsilon : k) : k :=
  -108 * a0 * b * f1 - 12 * a1 * b * b4 * r ^ 2 -
    12 * aOne * b ^ 2 * r ^ 2 + 4 * b * b5 * r ^ 4 +
    12 * b * c4 * r ^ 3 * sigma + 72 * b * f3 * r ^ 2 -
    108 * b * g2 * r * sigma + 36 * b4 * f1 * r ^ 2 +
    324 * c2 * g1 + 243 * c3 * epsilon + 324 * c3 * g0 +
    324 * c5 * gm2

omit [IsAlgClosed k] in
/-- The part of the cleared terminal scalar independent of `F[2]`. -/
def rhoOne_boundaryG_signedRayLinearTerminalBase68
    (sigma r a1 a0 b b4 c2 gm2 : k) : k :=
  -2187 * a0 * b * gm2 ^ 2 +
    162 * a1 * b ^ 2 * gm2 * r ^ 3 * sigma +
    2 * b ^ 3 * r ^ 8 + 81 * b * c2 * gm2 * r ^ 4 +
    729 * b4 * gm2 ^ 2 * r ^ 2

omit [IsAlgClosed k] in
/-- The compact `F[2]`-resultant of the reduced `I3(3)` and terminal
rows.  It contains no `F[2]`. -/
def rhoOne_boundaryG_signedRayLinearI3ThreeTerminalElim68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 c4 c5
      f1 f3 g2 g1 g0 gm2 epsilon : k) : k :=
  -243 * gm2 ^ 2 *
      rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r a1 a0 aOne
        b b4 b5 c2 c3 c4 c5 f1 f3 g2 g1 g0 gm2 epsilon -
    4 * (3 * f1 - a1 * b) *
      rhoOne_boundaryG_signedRayLinearTerminalBase68
        sigma r a1 a0 b b4 c2 gm2

omit [IsAlgClosed k] in
/-- Direct cross-simplification of `I3(3)`. -/
theorem rhoOne_boundaryG_signedRay_linear_i3three_reduce68
    (sigma r a a1 a0 aOne b b3 b4 b5 c1 c2 c3 c4 c5
      f0 f1 f2 f3 gm2 gm1 g0 g1 g2 epsilon : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0)
    (hr : r ^ 2 = -3 * a)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (hrf : r * f0 = 3 * sigma * gm1)
    (hlinear : 3 * c1 + sigma * r * b = 0)
    (hb3 : b3 = 0)
    (hi3 :
      (-(8 / 9 : k)) *
          (a * b * f3 + (a * b3 + a1 * b) * f2 +
            (a * b4 + a1 * b3 + a0 * b) * f1 +
            (a * b5 + a1 * b4 + a0 * b3 + aOne * b) * f0) +
        (8 / 3 : k) *
          (c1 * g2 + c2 * g1 + c3 * g0 + c4 * gm1 + c5 * gm2) +
        (8 / 3 : k) * (f0 * f3 + f1 * f2) + 2 * epsilon * c3 = 0) :
    rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r a1 a0 aOne
      b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0 := by
  have ha : a = -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgm1 : gm1 = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hf0 : f0 = r ^ 2 * b / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgm1]
    linear_combination (r ^ 3 * b / 9) * hsigma
  have hc1 : c1 = -(sigma * r * b / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  rw [ha, hb3, hc1, hf0, hgm1] at hi3
  dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeReduced68]
  linear_combination (243 / 2 : k) * hi3

omit [IsAlgClosed k] in
/-- Eliminate `F[2]` between the reduced row and the cleared terminal
scalar.  This is a strict finite-coordinate gain, not a contradiction. -/
theorem rhoOne_boundaryG_signedRay_linear_i3three_terminal_elim68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 c4 c5
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k)
    (hi3 : rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0)
    (hterminal : rhoOne_boundaryG_signedRayLinearTerminalResidual68 sigma r
      a1 a0 b b4 c2 f2 gm2 = 0) :
    rhoOne_boundaryG_signedRayLinearI3ThreeTerminalElim68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f3 g2 g1 g0 gm2 epsilon = 0 := by
  dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeTerminalElim68,
    rhoOne_boundaryG_signedRayLinearI3ThreeBase68,
    rhoOne_boundaryG_signedRayLinearTerminalBase68,
    rhoOne_boundaryG_signedRayLinearI3ThreeReduced68,
    rhoOne_boundaryG_signedRayLinearTerminalResidual68] at *
  linear_combination
    -243 * gm2 ^ 2 * hi3 - 4 * (3 * f1 - a1 * b) * hterminal

/-- Source-honest linear-factor packet after the I3/terminal
cross-elimination. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-1) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧
    B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearTerminalResidual68 sigma r
      (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
      (C.coeff 2) (F.coeff 2) (G.coeff (-2)) = 0 ∧
    rhoOne_boundaryG_i3threeSourceRow68 T = 0 ∧
    rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
      (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
      (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 2)
      (F.coeff 3) (G.coeff 2) (G.coeff 1) (G.coeff 0)
      (G.coeff (-2)) T.source.epsilon = 0 ∧
    rhoOne_boundaryG_signedRayLinearI3ThreeTerminalElim68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
      (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
      (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 3)
      (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
      T.source.epsilon = 0

/-- Attach the reduced and `F[2]`-eliminated rows to the exact source
witnesses already present in the linear packet. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_i3three_reduction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (S : RhoOneAlignedSquareGNegTwoSignedRayLinearI3Three68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68 T := by
  have Sc := S
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearI3Three68] at Sc
  rcases Sc with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf,
    hlinear, hb3, hterminal, hi3⟩
  have hi3c := hi3
  dsimp only [rhoOne_boundaryG_i3threeSourceRow68] at hi3c
  have hred := rhoOne_boundaryG_signedRay_linear_i3three_reduce68 sigma r
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
    ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
    ((ratFuncAtHahn46 T.root T.source.A).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 3)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 4)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 5)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 1)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
    T.source.epsilon hsigma hr0 hr hray hrf hlinear hb3 hi3c
  have helim := rhoOne_boundaryG_signedRay_linear_i3three_terminal_elim68
    sigma r
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
    ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
    ((ratFuncAtHahn46 T.root T.source.A).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 4)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 5)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 1)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
    T.source.epsilon hred hterminal
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68]
  exact ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hlinear,
    hb3, hterminal, hi3, hred, helim⟩

/-- Source selector preserving the Q/R, coordinate, and nonsingular
siblings exactly. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_i3three_reduction_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_i3three_selector68
      hp hH hp6 hp5 hp4 R with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hlinear | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_i3three_reduction68 hlinear)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearI3ThreeReduction68

end Max11DegreeRoutes
