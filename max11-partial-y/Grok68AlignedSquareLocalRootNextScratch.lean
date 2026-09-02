import Grok68AlignedSquareCoordinateGainScratch

/-! # Coordinate-gain `I4(5)` and QR `I3(3)` on the quadratic `G[-2]` residual

Untracked working note. No tracked file was edited.

The coordinate-gain `I4(4)` step raised `ord B` to five and `ord F` to
two, and named two unused rows: the coordinate-gain `I4(5)` face at
those orders, and the unused `I3(3)` alternative-determinant row on
`RhoOneAlignedSquareGNegTwoSignedRayQRResidual68`.  This file consumes
both.  It does not reopen the Hahn algebra, delete a chamber, or claim
the full local-root exclusion `PlaneKeller68AlignedSquareLocalRootExclusion`.

On the coordinate-gain zeros the already recorded `I4(3)` identity
collapses to `B[5] G[-2] + C[1] F[2] = 0`.  The existing `I4(5)` source
row collapses to
`B[5] G[0] + B[7] G[-2] + C[1] F[4] + C[2] F[3] + C[3] F[2] + (3/4) ε B[5] = 0`.
Clearing `B[5]` between those two faces leaves a `B[5]`-free transport.
This is a strict finite-coordinate gain, not a contradiction.

On the QR cell the signed-ray substitutions reduce `I3(3)` to a
polynomial whose genuinely new support is `B[5]`, `C[5]`, `F[3]`, and
`G[2]`.  The row is independent of the `Q0/R0` factor and of the
terminal scalar.  This is likewise a strict finite-coordinate gain.

Exact gain: the coordinate-gain cell attaches the specialized `I4(3)`
face and consumes `I4(5)` at the raised orders, replacing that face by
the displayed three-plus-epsilon transport after clearing `B[5]`.  The
QR cell attaches the `I3(3)` source row and its signed-ray reduction.
The nonsingular transport and the pre-quadratic `G[-2]` remainder are
unchanged.

Next unused row: the coordinate-gain `I3(4)` face at the same raised
orders, and the unused `I4(4)` source row on the QR residual.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareLocalRootNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] [CharZero k] in
/-- Specialized `I4(3)` after the coordinate-gain vanishings. -/
def rhoOne_boundaryG_coordinateGainI4ThreeReduced68
    (b5 gm2 c1 f2 : k) : k :=
  b5 * gm2 + c1 * f2

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i4three_reduce68
    (b2 b3 b4 b5 g1 g0 gm1 gm2 c1 c2 c3 f0 f1 f2 epsilon : k)
    (hb2 : b2 = 0) (hb3 : b3 = 0) (hb4 : b4 = 0)
    (hf0 : f0 = 0) (hf1 : f1 = 0) (hgm1 : gm1 = 0)
    (hi4 : b2 * g1 + b3 * g0 + b4 * gm1 + b5 * gm2 +
      c1 * f2 + c2 * f1 + c3 * f0 +
      (3 / 4 : k) * epsilon * b3 = 0) :
    rhoOne_boundaryG_coordinateGainI4ThreeReduced68 b5 gm2 c1 f2 = 0 := by
  rw [hb2, hb3, hb4, hf0, hf1, hgm1] at hi4
  dsimp only [rhoOne_boundaryG_coordinateGainI4ThreeReduced68]
  linear_combination hi4

omit [IsAlgClosed k] [CharZero k] in
/-- Specialized `I4(5)` after the coordinate-gain vanishings. -/
def rhoOne_boundaryG_coordinateGainI4FiveReduced68
    (b5 b7 gm2 c1 c2 c3 f2 f3 f4 g0 epsilon : k) : k :=
  b5 * g0 + b7 * gm2 + c1 * f4 + c2 * f3 + c3 * f2 +
    (3 / 4 : k) * epsilon * b5

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i4five_reduce68
    (b2 b3 b4 b5 b6 b7 g3 g2 g1 g0 gm1 gm2
      c1 c2 c3 c4 c5 f0 f1 f2 f3 f4 epsilon : k)
    (hb2 : b2 = 0) (hb3 : b3 = 0) (hb4 : b4 = 0)
    (hf0 : f0 = 0) (hf1 : f1 = 0) (hgm1 : gm1 = 0)
    (hi4 : b2 * g3 + b3 * g2 + b4 * g1 + b5 * g0 + b6 * gm1 +
      b7 * gm2 + c1 * f4 + c2 * f3 + c3 * f2 + c4 * f1 +
      c5 * f0 + (3 / 4 : k) * epsilon * b5 = 0) :
    rhoOne_boundaryG_coordinateGainI4FiveReduced68
      b5 b7 gm2 c1 c2 c3 f2 f3 f4 g0 epsilon = 0 := by
  rw [hb2, hb3, hb4, hf0, hf1, hgm1] at hi4
  dsimp only [rhoOne_boundaryG_coordinateGainI4FiveReduced68]
  linear_combination hi4

omit [IsAlgClosed k] [CharZero k] in
/-- `B[5]`-free transport of the specialized `I4(5)` against `I4(3)`. -/
def rhoOne_boundaryG_coordinateGainI4FiveTransport68
    (b7 gm2 c1 c2 c3 f2 f3 f4 g0 epsilon : k) : k :=
  b7 * gm2 ^ 2 + c1 * f4 * gm2 + c2 * f3 * gm2 + c3 * f2 * gm2 -
    c1 * f2 * g0 - (3 / 4 : k) * epsilon * c1 * f2

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i4five_transport68
    (b5 b7 gm2 c1 c2 c3 f2 f3 f4 g0 epsilon : k)
    (hi4three : rhoOne_boundaryG_coordinateGainI4ThreeReduced68
      b5 gm2 c1 f2 = 0)
    (hi4five : rhoOne_boundaryG_coordinateGainI4FiveReduced68
      b5 b7 gm2 c1 c2 c3 f2 f3 f4 g0 epsilon = 0) :
    rhoOne_boundaryG_coordinateGainI4FiveTransport68
      b7 gm2 c1 c2 c3 f2 f3 f4 g0 epsilon = 0 := by
  dsimp only [rhoOne_boundaryG_coordinateGainI4ThreeReduced68,
    rhoOne_boundaryG_coordinateGainI4FiveReduced68,
    rhoOne_boundaryG_coordinateGainI4FiveTransport68] at *
  linear_combination gm2 * hi4five -
    (g0 + (3 / 4 : k) * epsilon) * hi4three

/-- Source-coordinate form of the general boundary `I4(3)` row. -/
def rhoOne_boundaryG_i4threeSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
    B.coeff 4 * G.coeff (-1) + B.coeff 5 * G.coeff (-2) +
    C.coeff 1 * F.coeff 2 + C.coeff 2 * F.coeff 1 +
    C.coeff 3 * F.coeff 0 + (3 / 4 : k) * T.source.epsilon * B.coeff 3

/-- Exact source backwire for the general boundary `I4(3)` row. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i4three_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i4threeSourceRow68 T = 0 := by
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
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root C).orderTop := by rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root F).orderTop := by rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hrow := ratFunc_boundaryG_i4three68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS0) hi4f
  rw [hCmap, hFmap, hGmap] at hrow
  exact hrow

/-- Source-facing coordinate-gain packet after consuming `I4(5)`. -/
def RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68 T g u ∧
  rhoOne_boundaryG_i4threeSourceRow68 T = 0 ∧
  rhoOne_boundaryG_i4fiveExpandedSourceRow68 T = 0 ∧
  rhoOne_boundaryG_coordinateGainI4ThreeReduced68
    (B.coeff 5) (G.coeff (-2)) (C.coeff 1) (F.coeff 2) = 0 ∧
  rhoOne_boundaryG_coordinateGainI4FiveReduced68
    (B.coeff 5) (B.coeff 7) (G.coeff (-2)) (C.coeff 1) (C.coeff 2)
    (C.coeff 3) (F.coeff 2) (F.coeff 3) (F.coeff 4) (G.coeff 0)
    T.source.epsilon = 0 ∧
  rhoOne_boundaryG_coordinateGainI4FiveTransport68
    (B.coeff 7) (G.coeff (-2)) (C.coeff 1) (C.coeff 2) (C.coeff 3)
    (F.coeff 2) (F.coeff 3) (F.coeff 4) (G.coeff 0)
    T.source.epsilon = 0

set_option maxHeartbeats 800000 in
/-- Unpack the after-`I4(4)` coordinate-gain cell, consume `I4(5)`, and
attach the specialized `I4(3)` face together with the `B[5]` transport. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_coordinateGain_i4five68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68] at Rc
  rcases Rc with ⟨R0, hgm2, hb3, hf1, hb4, hBord, hFord, hi4four,
    hi3one, hi3src, hi3three⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68] at R0c
  rcases R0c with ⟨Q, hB2, hF0, hGm1, hBord0, hFord0, hi4fourOld⟩
  have hi4threeSrc := T.rhoOne_boundaryG_i4three_source68 Q
  have hi4fiveSrc := T.rhoOne_boundaryG_i4five_expanded_source68 Q
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hi4threec := hi4threeSrc
  dsimp only [rhoOne_boundaryG_i4threeSourceRow68] at hi4threec
  have hi4fivec := hi4fiveSrc
  dsimp only [rhoOne_boundaryG_i4fiveExpandedSourceRow68,
    rhoOne_boundaryG_i4fiveHahnRow68] at hi4fivec
  have hi4threeRed := rhoOne_boundaryG_coordinateGain_i4three_reduce68
    (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5)
    (G.coeff 1) (G.coeff 0) (G.coeff (-1)) (G.coeff (-2))
    (C.coeff 1) (C.coeff 2) (C.coeff 3)
    (F.coeff 0) (F.coeff 1) (F.coeff 2) T.source.epsilon
    hB2 hb3 hb4 hF0 hf1 hGm1 (by convert hi4threec using 1 <;> norm_num)
  have hi4fiveRed := rhoOne_boundaryG_coordinateGain_i4five_reduce68
    (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5) (B.coeff 6)
    (B.coeff 7) (G.coeff 3) (G.coeff 2) (G.coeff 1) (G.coeff 0)
    (G.coeff (-1)) (G.coeff (-2))
    (C.coeff 1) (C.coeff 2) (C.coeff 3) (C.coeff 4) (C.coeff 5)
    (F.coeff 0) (F.coeff 1) (F.coeff 2) (F.coeff 3) (F.coeff 4)
    T.source.epsilon
    hB2 hb3 hb4 hF0 hf1 hGm1 (by convert hi4fivec using 1 <;> norm_num)
  have htrans := rhoOne_boundaryG_coordinateGain_i4five_transport68
    (B.coeff 5) (B.coeff 7) (G.coeff (-2)) (C.coeff 1) (C.coeff 2)
    (C.coeff 3) (F.coeff 2) (F.coeff 3) (F.coeff 4) (G.coeff 0)
    T.source.epsilon hi4threeRed hi4fiveRed
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68]
  exact ⟨R, hi4threeSrc, hi4fiveSrc, hi4threeRed, hi4fiveRed, htrans⟩

omit [IsAlgClosed k] in
/-- The cleared `I3(3)` row after the signed-ray substitutions, without
the linear factor or `B[3]=0`. -/
def rhoOne_boundaryG_signedRayQRI3ThreeReduced68
    (sigma r a1 a0 aOne b b3 b4 b5 c1 c2 c3 c4 c5
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k) : k :=
  -12 * a0 * b * b3 * r ^ 2 - 108 * a0 * b * f1 -
    12 * a1 * b * b4 * r ^ 2 - 108 * a1 * b * f2 - 108 * a1 * b3 * f1 -
    12 * aOne * b ^ 2 * r ^ 2 + 4 * b * b5 * r ^ 4 +
    12 * b * c4 * r ^ 3 * sigma + 72 * b * f3 * r ^ 2 +
    36 * b3 * f2 * r ^ 2 + 36 * b4 * f1 * r ^ 2 +
    324 * c1 * g2 + 324 * c2 * g1 + 243 * c3 * epsilon +
    324 * c3 * g0 + 324 * c5 * gm2 + 324 * f1 * f2

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRay_qr_i3three_reduce68
    (sigma r a a1 a0 aOne b b3 b4 b5 c1 c2 c3 c4 c5
      f0 f1 f2 f3 gm2 gm1 g0 g1 g2 epsilon : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0)
    (hr : r ^ 2 = -3 * a)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (hrf : r * f0 = 3 * sigma * gm1)
    (hi3 :
      (-(8 / 9 : k)) *
          (a * b * f3 + (a * b3 + a1 * b) * f2 +
            (a * b4 + a1 * b3 + a0 * b) * f1 +
            (a * b5 + a1 * b4 + a0 * b3 + aOne * b) * f0) +
        (8 / 3 : k) *
          (c1 * g2 + c2 * g1 + c3 * g0 + c4 * gm1 + c5 * gm2) +
        (8 / 3 : k) * (f0 * f3 + f1 * f2) + 2 * epsilon * c3 = 0) :
    rhoOne_boundaryG_signedRayQRI3ThreeReduced68 sigma r a1 a0 aOne
      b b3 b4 b5 c1 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0 := by
  have ha : a = -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgm1 : gm1 = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hf0 : f0 = r ^ 2 * b / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgm1]
    linear_combination (r ^ 3 * b / 9) * hsigma
  rw [ha, hf0, hgm1] at hi3
  dsimp only [rhoOne_boundaryG_signedRayQRI3ThreeReduced68]
  linear_combination (243 / 2 : k) * hi3

/-- Source-facing QR packet after consuming `I3(3)`. -/
def RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68
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
      (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon = 0

/-- Attach the `I3(3)` source row and its signed-ray reduction to the
exact QR witnesses. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_qr_i3three68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (S : RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68 T := by
  have hrow := T.rhoOne_boundaryG_i3three_source68 Q
  have Sc := S
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayQRResidual68] at Sc
  rcases Sc with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hqr, hterminal⟩
  have hi3c := hrow
  dsimp only [rhoOne_boundaryG_i3threeSourceRow68] at hi3c
  have hred := rhoOne_boundaryG_signedRay_qr_i3three_reduce68 sigma r
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
    T.source.epsilon hsigma hr0 hr hray hrf
    (by convert hi3c using 1 <;> norm_num)
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68]
  exact ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hqr, hterminal,
    hrow, hred⟩

/-- Quadratic `G[-2]` residual after consuming coordinate-gain `I4(5)`
and QR `I3(3)`.  The nonsingular transport is copied literally. -/
def RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootNext68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  RhoOneAlignedSquareGNegTwoCoordinateGainI4Five68 T g u ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      RhoOneAlignedSquareGNegTwoSignedRayQRI3Three68 T) ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
      let G := rhoOneTangentEDefectHahn68 A C
        (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
      A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0)

/-- Literal `G[-2]` inventory residual after the local-root next step. -/
def RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootNext68
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
  RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootNext68 T g u

/-- Normalized inventory with coordinate-gain `I4(5)` and QR `I3(3)`
consumed. -/
def RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68
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
  RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootNext68 T g u ∨
  RhoOneAlignedSquareLocalFinalResidual68 T g u

/-- Source-facing quadratic selector after consuming coordinate-gain
`I4(5)` and QR `I3(3)`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_localRootNext_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoQuadraticChamberAfterLocalRootNext68
      T g u := by
  rcases T.rhoOne_boundaryG_coordinateGain_i4four_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl (T.rhoOne_boundaryG_coordinateGain_i4five68 hcoord)
  · exact Or.inr (Or.inl ⟨hsigned.1,
      T.rhoOne_boundaryG_signedRay_qr_i3three68 hsigned.1 hsigned.2⟩)
  · exact Or.inr (Or.inr hnon)

/-- The old `G[-2] != 0` inventory residual, after consuming
coordinate-gain `I4(5)` and QR `I3(3)`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_localRootNext_GnegTwo_inventory68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hG :
      RhoOneAlignedSquareGNegTwoInventoryResidualAfterCoordinateGainI4Four68
        T g u) :
    RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootNext68
      T g u := by
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterCoordinateGainI4Four68] at hG
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterLocalRootNext68]
  rcases hG with hpre | hquad
  · exact Or.inl hpre
  · refine Or.inr
      (T.rhoOne_boundaryG_localRootNext_selector68
        hp hH hp6 hp5 hp4 ?_)
    dsimp only
      [RhoOneAlignedSquareGNegTwoQuadraticChamberAfterCoordinateGainI4Four68] at hquad
    rcases hquad with hcoord | hqr | hnon
    · have hcoordc := hcoord
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68] at hcoordc
      have hcoord0 := hcoordc.1
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68] at hcoord0
      exact hcoord0.1
    · exact hqr.1
    · exact hnon.1

/-- Refine the after-coordinate-gain-`I4(4)` inventory by consuming
`I4(5)` and QR `I3(3)`.  No other sibling is touched. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_localRootNext68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterCoordinateGainI4Four68
      T g u) :
    RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68
      T g u := by
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterCoordinateGainI4Four68] at R
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68]
  rcases R with hdesc | hnoncubic | hearly | hpre | hgbox | hFne | hGne | hfinal
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · exact Or.inr (Or.inr (Or.inl hearly))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgbox))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFne)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (T.rhoOne_boundaryG_localRootNext_GnegTwo_inventory68
        hp hH hp6 hp5 hp4 hGne)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hfinal))))))

/-- Normalized aligned-square source wrapper after consuming
coordinate-gain `I4(5)` and QR `I3(3)`. -/
theorem normalized68ScaleTwo_alignedSquare_finalInventory_after_localRootNext
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
      RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLocalRootNext68
        T g u := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, T, g, u, hp5, hp4, R⟩ :=
    normalized68ScaleTwo_alignedSquare_finalInventory_after_coordinateGainI4Four
      hsource hh0 hH haligned
  exact ⟨j, T, g, u, hp5, hp4,
    T.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_localRootNext68
      hp hH hp6 hp5 hp4 R⟩

end AlignedSquareLocalRootNext68

end Max11DegreeRoutes
