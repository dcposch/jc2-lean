import Grok68AlignedSquareLocalRootNextScratch

/-! # Coordinate-gain `I3(4)` and QR `I4(4)` on the quadratic `G[-2]` residual

Untracked working note. No tracked file was edited.

The local-root next step consumed coordinate-gain `I4(5)` and QR `I3(3)`,
and named two unused rows: the coordinate-gain `I3(4)` face at the
raised orders `ord B ≥ 5`, `ord F ≥ 2`, and the unused `I4(4)` source
row on `RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68`.  This file
consumes both.  It does not reopen the Hahn algebra, delete a chamber,
or claim the full local-root exclusion
`PlaneKeller68AlignedSquareLocalRootExclusion`.

CAS `derive_68_aligned_square_local_root_i3four.py` records the
specializations and a remaining-row count on every open cell of
`RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68`.
No cell dies: `1` is not in the sliced ideals, and explicit samples
survive.  `C[6]` absorbs coordinate-gain `I3(4)` given `G[-2] ≠ 0`;
`B[6]` absorbs QR `I4(4)` given `G[-2] ≠ 0`.  Descent, noncubic, early
cubic, exceptional, `F[-1] ≠ 0`, the pre-quadratic `G[-2]` remainder,
the nonsingular transport, and the local final residual do not carry
these two named jets.

Remaining proven `I3`/`I4` source rows after this step (so the
coordinator can see convergence): coordinate-gain 13 (`I3(5..11)` and
`I4(6..11)`); QR 15 (`I3(4..11)` and `I4(5..11)`); nonsingular 17
(`I3(3..11)` and `I4(4..11)`).  Each consumed row introduces a new
absorbing coefficient.  The truncated jet is not shrinking.

On the coordinate-gain zeros the already recorded `I3(4)` source row
collapses to
`(8/3)(C[1] G[3] + C[2] G[2] + C[3] G[1] + C[4] G[0] + C[6] G[-2])
+ (4/3) F[2]^2 + 2 ε C[4] = 0`.
This is the first surviving `F^2` term at the raised orders, together
with the new support `C[6]`, `G[3]`.  Strict finite-coordinate gain.

On the QR cell the signed-ray substitutions reduce `I4(4)` to a
polynomial whose genuinely new support is `B[6]`.  The row is
independent of the `Q0/R0` factor and of the terminal scalar.  Strict
finite-coordinate gain.

Exact gain: the coordinate-gain cell attaches the specialized `I3(4)`
face at the raised orders.  The QR cell attaches the `I4(4)` source
row and its signed-ray reduction.  The nonsingular transport and the
pre-quadratic `G[-2]` remainder are unchanged.

Next unused row: the coordinate-gain `I3(5)` face at the same raised
orders, and the unused `I3(4)` source row on the QR residual.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareLocalRootI3Four68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] [CharZero k] in
/-- Specialized `I3(4)` after the coordinate-gain vanishings.  The first
surviving `F^2` term is `F[2]^2`; the new support is `C[6]`, `G[3]`. -/
def rhoOne_boundaryG_coordinateGainI3FourReduced68
    (c1 c2 c3 c4 c6 g3 g2 g1 g0 gm2 f2 epsilon : k) : k :=
  (8 / 3 : k) * (c1 * g3 + c2 * g2 + c3 * g1 + c4 * g0 + c6 * gm2) +
    (4 / 3 : k) * f2 ^ 2 + 2 * epsilon * c4

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i3four_reduce68
    (am2 am1 a0 a1 a2 b2 b3 b4 b5 b6
      c0 c1 c2 c3 c4 c5 c6
      f0 f1 f2 f3 f4
      g3 g2 g1 g0 gm1 gm2 gamma epsilon : k)
    (hb2 : b2 = 0) (hb3 : b3 = 0) (hb4 : b4 = 0)
    (hf0 : f0 = 0) (hf1 : f1 = 0) (hgm1 : gm1 = 0)
    (hi3 :
      (-(8 / 9 : k)) *
          (am2 * b2 * f4 +
            (am2 * b3 + am1 * b2) * f3 +
            (am2 * b4 + am1 * b3 + a0 * b2) * f2 +
            (am2 * b5 + am1 * b4 + a0 * b3 + a1 * b2) * f1 +
            (am2 * b6 + am1 * b5 + a0 * b4 + a1 * b3 + a2 * b2) * f0) -
        (8 / 9 : k) * b2 ^ 2 * c0 +
        (8 / 3 : k) *
          (c1 * g3 + c2 * g2 + c3 * g1 + c4 * g0 +
            c5 * gm1 + c6 * gm2) +
        (4 / 3 : k) * (2 * f0 * f4 + 2 * f1 * f3 + f2 ^ 2) -
        (2 / 3 : k) * gamma * b2 ^ 2 + 2 * epsilon * c4 = 0) :
    rhoOne_boundaryG_coordinateGainI3FourReduced68
      c1 c2 c3 c4 c6 g3 g2 g1 g0 gm2 f2 epsilon = 0 := by
  rw [hb2, hb3, hb4, hf0, hf1, hgm1] at hi3
  dsimp only [rhoOne_boundaryG_coordinateGainI3FourReduced68]
  linear_combination hi3

/-- Source-facing coordinate-gain packet after consuming `I3(4)`. -/
def RhoOneAlignedSquareGNegTwoCoordinateGainI3Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68 T g u ∧
  rhoOne_boundaryG_i3fourSourceRow68 T = 0 ∧
  rhoOne_boundaryG_coordinateGainI3FourReduced68
    (C.coeff 1) (C.coeff 2) (C.coeff 3) (C.coeff 4) (C.coeff 6)
    (G.coeff 3) (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
    (F.coeff 2) T.source.epsilon = 0

set_option maxHeartbeats 800000 in
/-- Unpack the after-`I4(5)` coordinate-gain cell, consume `I3(4)`, and
attach the specialized face. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_coordinateGain_i3four68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGainI3Four68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68] at Rc
  rcases Rc with ⟨R4, hi4threeSrc, hi4fiveSrc, hi4threeRed, hi4fiveRed, htrans⟩
  have R4c := R4
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68] at R4c
  rcases R4c with ⟨R0, hgm2, hb3, hf1, hb4, hBord, hFord, hi4four,
    hi3one, hi3src, hi3three⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68] at R0c
  rcases R0c with ⟨Q, hB2, hF0, hGm1, hBord0, hFord0, hi4fourOld⟩
  have hi3fourSrc := T.rhoOne_boundaryG_i3four_source68 Q
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hi3fourc := hi3fourSrc
  dsimp only [rhoOne_boundaryG_i3fourSourceRow68,
    rhoOne_boundaryG_i3fourHahnRow68] at hi3fourc
  have hi3fourRed := rhoOne_boundaryG_coordinateGain_i3four_reduce68
    (A.coeff (-2)) (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (A.coeff 2)
    (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5) (B.coeff 6)
    (C.coeff 0) (C.coeff 1) (C.coeff 2) (C.coeff 3) (C.coeff 4)
    (C.coeff 5) (C.coeff 6)
    (F.coeff 0) (F.coeff 1) (F.coeff 2) (F.coeff 3) (F.coeff 4)
    (G.coeff 3) (G.coeff 2) (G.coeff 1) (G.coeff 0)
    (G.coeff (-1)) (G.coeff (-2)) T.source.gamma T.source.epsilon
    hB2 hb3 hb4 hF0 hf1 hGm1 (by convert hi3fourc using 1 <;> norm_num)
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI3Four68]
  exact ⟨R, hi3fourSrc, hi3fourRed⟩

omit [IsAlgClosed k] in
/-- The cleared `I4(4)` row after the signed-ray substitutions.  The
genuinely new support is `B[6]`. -/
def rhoOne_boundaryG_signedRayQRI4FourReduced68
    (sigma r b b3 b4 b5 b6 c1 c2 c3 c4
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k) : k :=
  108 * b * g2 + 108 * b3 * g1 + 108 * b4 * g0 +
    4 * b * b5 * sigma * r ^ 3 + 108 * b6 * gm2 +
    108 * c1 * f3 + 108 * c2 * f2 + 108 * c3 * f1 +
    12 * b * c4 * r ^ 2 + 81 * epsilon * b4

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRay_qr_i4four_reduce68
    (sigma r b b3 b4 b5 b6 c1 c2 c3 c4
      f0 f1 f2 f3 gm1 g0 g1 g2 gm2 epsilon : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (hrf : r * f0 = 3 * sigma * gm1)
    (hi4 :
      b * g2 + b3 * g1 + b4 * g0 + b5 * gm1 + b6 * gm2 +
        c1 * f3 + c2 * f2 + c3 * f1 + c4 * f0 +
        (3 / 4 : k) * epsilon * b4 = 0) :
    rhoOne_boundaryG_signedRayQRI4FourReduced68 sigma r
      b b3 b4 b5 b6 c1 c2 c3 c4 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0 := by
  have hgm1 : gm1 = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hf0 : f0 = r ^ 2 * b / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgm1]
    linear_combination (r ^ 3 * b / 9) * hsigma
  rw [hf0, hgm1] at hi4
  dsimp only [rhoOne_boundaryG_signedRayQRI4FourReduced68]
  linear_combination (108 : k) * hi4

/-- Source-facing QR packet after consuming `I4(4)`. -/
def RhoOneAlignedSquareGNegTwoSignedRayQRI4Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let Q0 := (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 2 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 1 +
        (A.coeff (-1) * B.coeff 3 + A.coeff 0 * B.coeff 2) * F.coeff 0) +
    (8 / 3 : k) * (C.coeff 1 * G.coeff 1 + C.coeff 2 * G.coeff 0 +
      C.coeff 4 * G.coeff (-2)) +
    (4 / 3 : k) * (2 * F.coeff 0 * F.coeff 2 + F.coeff 1 ^ 2) +
    2 * T.source.epsilon * C.coeff 2
  let R0 := B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
    B.coeff 5 * G.coeff (-2) + C.coeff 1 * F.coeff 2 +
    C.coeff 2 * F.coeff 1 + (3 / 4 : k) * T.source.epsilon * B.coeff 3
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-1) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    -9 * Q0 + 8 * sigma * r * R0 = 0 ∧
    rhoOne_boundaryG_signedRayTerminalResidual68 sigma r
      (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
      (C.coeff 1) (C.coeff 2) (F.coeff 2) (G.coeff (-2)) = 0 ∧
    rhoOne_boundaryG_i3threeSourceRow68 T = 0 ∧
    rhoOne_boundaryG_signedRayQRI3ThreeReduced68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
      (B.coeff 3) (B.coeff 4) (B.coeff 5) (C.coeff 1)
      (C.coeff 2) (C.coeff 3) (C.coeff 4) (C.coeff 5)
      (F.coeff 1) (F.coeff 2) (F.coeff 3) (G.coeff 2)
      (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon = 0 ∧
    rhoOne_boundaryG_i4fourSourceRow68 T = 0 ∧
    rhoOne_boundaryG_signedRayQRI4FourReduced68 sigma r
      (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5) (B.coeff 6)
      (C.coeff 1) (C.coeff 2) (C.coeff 3) (C.coeff 4)
      (F.coeff 1) (F.coeff 2) (F.coeff 3) (G.coeff 2)
      (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon = 0

/-- Attach the `I4(4)` source row and its signed-ray reduction to the
after-`I3(3)` QR witnesses. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_qr_i4four68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (S : RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayQRI4Four68 T := by
  have hrow := T.rhoOne_boundaryG_i4four_source68 Q
  have Sc := S
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68] at Sc
  rcases Sc with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hqr,
    hterminal, hi3src, hi3red⟩
  have hi4c := hrow
  dsimp only [rhoOne_boundaryG_i4fourSourceRow68] at hi4c
  have hred := rhoOne_boundaryG_signedRay_qr_i4four_reduce68 sigma r
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 3)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 4)
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
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
    T.source.epsilon hsigma hr0 hray hrf
    (by convert hi4c using 1 <;> norm_num)
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayQRI4Four68]
  exact ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hqr, hterminal,
    hi3src, hi3red, hrow, hred⟩

/-- Quadratic `G[-2]` residual after consuming coordinate-gain `I3(4)`
and QR `I4(4)`.  The nonsingular transport is copied literally. -/
def RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootI3Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  RhoOneAlignedSquareGNegTwoCoordinateGainI3Four68 T g u ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      RhoOneAlignedSquareGNegTwoSignedRayQRI4Four68 T) ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
      let G := rhoOneTangentEDefectHahn68 A C
        (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
      A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0)

/-- Literal `G[-2]` inventory residual after the local-root `I3(4)` step. -/
def RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootI3Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (G.coeff (-2 : ℚ) ≠ 0 ∧
    ¬ RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) ∨
  RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootI3Four68 T g u

/-- Normalized inventory with coordinate-gain `I3(4)` and QR `I4(4)`
consumed. -/
def RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootI3Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
  RhoOneZeroLNoncubicSourcePacket68 T g u ∨
  RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
  RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68 T ∨
  RhoOneAlignedSquareExceptionalGBoxBoundarySibling68 T ∨
  F.coeff (-1 : ℚ) ≠ 0 ∨
  RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootI3Four68 T g u ∨
  RhoOneAlignedSquareLocalFinalResidual68 T g u

/-- Source-facing quadratic selector after consuming coordinate-gain
`I3(4)` and QR `I4(4)`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_localRootI3Four_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootI3Four68
      T g u := by
  rcases T.rhoOne_boundaryG_localRootNext_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl (T.rhoOne_boundaryG_coordinateGain_i3four68 hcoord)
  · exact Or.inr (Or.inl ⟨hsigned.1,
      T.rhoOne_boundaryG_signedRay_qr_i4four68 hsigned.1 hsigned.2⟩)
  · exact Or.inr (Or.inr hnon)

/-- The old `G[-2] != 0` inventory residual, after consuming
coordinate-gain `I3(4)` and QR `I4(4)`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_localRootI3Four_GnegTwo_inventory68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hG :
      RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootNext68
        T g u) :
    RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootI3Four68
      T g u := by
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootNext68] at hG
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootI3Four68]
  rcases hG with hpre | hquad
  · exact Or.inl hpre
  · refine Or.inr
      (T.rhoOne_boundaryG_localRootI3Four_selector68
        hp hH hp6 hp5 hp4 ?_)
    dsimp only
      [RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootNext68] at hquad
    rcases hquad with hcoord | hqr | hnon
    · have hcoordc := hcoord
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68] at hcoordc
      have hcoord4 := hcoordc.1
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68] at hcoord4
      have hcoord0 := hcoord4.1
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68] at hcoord0
      exact hcoord0.1
    · exact hqr.1
    · exact hnon.1

/-- Refine the after-local-root-next inventory by consuming `I3(4)`
and QR `I4(4)`.  No other sibling is touched. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_localRootI3Four68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68
      T g u) :
    RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootI3Four68
      T g u := by
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68] at R
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootI3Four68]
  rcases R with hdesc | hnoncubic | hearly | hpre | hgbox | hFne | hGne | hfinal
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · exact Or.inr (Or.inr (Or.inl hearly))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgbox))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFne)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (T.rhoOne_boundaryG_localRootI3Four_GnegTwo_inventory68
        hp hH hp6 hp5 hp4 hGne)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hfinal))))))

/-- Normalized aligned-square source wrapper after consuming
coordinate-gain `I3(4)` and QR `I4(4)`. -/
theorem normalized68ScaleTwo_alignedSquare_finalInventory_after_localRootI3Four
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
        (g u : k[X]),
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootI3Four68
        T g u := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, T, g, u, hp5, hp4, R⟩ :=
    normalized68ScaleTwo_alignedSquare_finalInventory_after_localRootNext
      hsource hh0 hH haligned
  exact ⟨j, T, g, u, hp5, hp4,
    T.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_localRootI3Four68
      hp hH hp6 hp5 hp4 R⟩

end AlignedSquareLocalRootI3Four68

end Max11DegreeRoutes
