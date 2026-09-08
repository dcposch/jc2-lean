import Grok68AlignedSquareInventoryContinuationScratch

/-! # Coordinate-gain `I4(4)` consumption on the quadratic `G[-2]` residual

Untracked working note. No tracked file was edited.

The inventory continuation deleted the signed-ray linear `D=0` child and
named the coordinate-gain `I4(4)` face on
`RhoOneAlignedSquareGNegTwoCoordinateGain68` as the next unused row of
that cell.  This file only consumes that face.  It does not reopen the
Hahn algebra, claim the full local-root exclusion, or touch the
alternative-determinant QR sibling.

On `B[2]=F[0]=G[-1]=0` the already stored `I4(1)` identity and the
Following `F[1]` cross force `B[3]=F[1]=0`.  The stored `I4(2)` identity
then forces `B[4]=0`.  Substituting those three vanishings into the
recorded `I4(4)` face leaves a three-term transport, and the same
substitutions clear `I3(3)` of every `A,B,F` block.  Orders rise to
`ord B ≥ 5` and `ord F ≥ 2`.  This is a strict finite-coordinate gain,
not a contradiction.

Exact gain: the coordinate-gain cell loses `B[3]`, `F[1]`, and `B[4]`,
raises `ord B` to five and `ord F` to two, and replaces the recorded
`I4(4)` face by `B[6] G[-2] + C[1] F[3] + C[2] F[2] = 0`.  Specialized
`I3(1)` and `I3(3)` are attached.  The QR factor and the nonsingular
transport are unchanged.

Next unused row: the coordinate-gain `I4(5)` face at the raised orders,
and the unused `I3(3)` alternative-determinant row on
`RhoOneAlignedSquareGNegTwoSignedRayQRResidual68`.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareCoordinateGainI4Four68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] [CharZero k] in
/-- `I4(1)` on the coordinate-gain zeros forces `B[3]=0`. -/
theorem rhoOne_boundaryG_coordinateGain_b3_zero68
    (b2 b3 gm1 gm2 c1 f0 : k)
    (hb2 : b2 = 0) (hgm1 : gm1 = 0) (hf0 : f0 = 0) (hgm2 : gm2 ≠ 0)
    (hi4one : b2 * gm1 + b3 * gm2 + c1 * f0 = 0) :
    b3 = 0 := by
  rw [hb2, hgm1, hf0] at hi4one
  have hz : b3 * gm2 = 0 := by linear_combination hi4one
  exact (mul_eq_zero.mp hz).resolve_right hgm2

omit [IsAlgClosed k] in
/-- The Following `F[1]` cross on the coordinate-gain zeros forces
`F[1]=0`. -/
theorem rhoOne_boundaryG_coordinateGain_f1_zero68
    (a a1 b2 f1 gm1 gm2 : k)
    (hb2 : b2 = 0) (hgm1 : gm1 = 0) (hgm2 : gm2 ≠ 0)
    (hcross : gm2 * (3 * f1 + a1 * b2) = a * b2 * gm1) :
    f1 = 0 := by
  rw [hb2, hgm1] at hcross
  have h3 : 3 * f1 = 0 := by
    have hz : gm2 * (3 * f1) = 0 := by linear_combination hcross
    exact (mul_eq_zero.mp hz).resolve_left hgm2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

omit [IsAlgClosed k] [CharZero k] in
/-- `I4(2)` on the coordinate-gain zeros and `B[3]=F[1]=0` forces
`B[4]=0`. -/
theorem rhoOne_boundaryG_coordinateGain_b4_zero68
    (b2 b3 b4 g0 gm1 gm2 c1 c2 f0 f1 epsilon : k)
    (hb2 : b2 = 0) (hb3 : b3 = 0) (hgm1 : gm1 = 0)
    (hf0 : f0 = 0) (hf1 : f1 = 0) (hgm2 : gm2 ≠ 0)
    (hi4two : b2 * g0 + b3 * gm1 + b4 * gm2 + c1 * f1 + c2 * f0 +
      (3 / 4 : k) * epsilon * b2 = 0) :
    b4 = 0 := by
  rw [hb2, hb3, hgm1, hf0, hf1] at hi4two
  have hz : b4 * gm2 = 0 := by linear_combination hi4two
  exact (mul_eq_zero.mp hz).resolve_right hgm2

omit [IsAlgClosed k] [CharZero k] in
/-- The recorded coordinate-gain `I4(4)` face after `B[3]=B[4]=F[1]=0`. -/
def rhoOne_boundaryG_coordinateGainI4FourReduced68
    (b6 gm2 c1 c2 f2 f3 : k) : k :=
  b6 * gm2 + c1 * f3 + c2 * f2

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i4four_reduce68
    (b3 b4 b6 g1 g0 gm2 c1 c2 c3 f1 f2 f3 epsilon : k)
    (hb3 : b3 = 0) (hb4 : b4 = 0) (hf1 : f1 = 0)
    (hi4 : b3 * g1 + b4 * g0 + b6 * gm2 + c1 * f3 + c2 * f2 +
      c3 * f1 + (3 / 4 : k) * epsilon * b4 = 0) :
    rhoOne_boundaryG_coordinateGainI4FourReduced68 b6 gm2 c1 c2 f2 f3 = 0 := by
  rw [hb3, hb4, hf1] at hi4
  dsimp only [rhoOne_boundaryG_coordinateGainI4FourReduced68]
  linear_combination hi4

omit [IsAlgClosed k] [CharZero k] in
/-- Specialized `I3(1)` after the coordinate-gain vanishings. -/
def rhoOne_boundaryG_coordinateGainI3OneReduced68
    (c1 c3 g0 gm2 epsilon : k) : k :=
  (8 / 3 : k) * (c1 * g0 + c3 * gm2) + 2 * epsilon * c1

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i3one_reduce68
    (am2 am1 b2 b3 f0 f1 c1 c2 c3 g0 gm1 gm2 epsilon : k)
    (hb2 : b2 = 0) (hb3 : b3 = 0) (hf0 : f0 = 0)
    (hf1 : f1 = 0) (hgm1 : gm1 = 0)
    (hi3 : (-(8 / 9 : k)) *
        (am2 * b2 * f1 + (am2 * b3 + am1 * b2) * f0) +
      (8 / 3 : k) * (c1 * g0 + c2 * gm1 + c3 * gm2) +
      (8 / 3 : k) * f0 * f1 + 2 * epsilon * c1 = 0) :
    rhoOne_boundaryG_coordinateGainI3OneReduced68 c1 c3 g0 gm2 epsilon = 0 := by
  rw [hb2, hb3, hf0, hf1, hgm1] at hi3
  dsimp only [rhoOne_boundaryG_coordinateGainI3OneReduced68]
  linear_combination hi3

omit [IsAlgClosed k] [CharZero k] in
/-- Specialized `I3(3)` after the coordinate-gain vanishings.  Every
`A,B,F` block is gone. -/
def rhoOne_boundaryG_coordinateGainI3ThreeReduced68
    (c1 c2 c3 c5 g2 g1 g0 gm2 epsilon : k) : k :=
  (8 / 3 : k) * (c1 * g2 + c2 * g1 + c3 * g0 + c5 * gm2) +
    2 * epsilon * c3

omit [IsAlgClosed k] [CharZero k] in
theorem rhoOne_boundaryG_coordinateGain_i3three_reduce68
    (am2 am1 a0 a1 b2 b3 b4 b5 c1 c2 c3 c4 c5
      f0 f1 f2 f3 g2 g1 g0 gm1 gm2 epsilon : k)
    (hb2 : b2 = 0) (hb3 : b3 = 0) (hb4 : b4 = 0)
    (hf0 : f0 = 0) (hf1 : f1 = 0) (hgm1 : gm1 = 0)
    (hi3 : (-(8 / 9 : k)) *
        (am2 * b2 * f3 + (am2 * b3 + am1 * b2) * f2 +
          (am2 * b4 + am1 * b3 + a0 * b2) * f1 +
          (am2 * b5 + am1 * b4 + a0 * b3 + a1 * b2) * f0) +
      (8 / 3 : k) *
        (c1 * g2 + c2 * g1 + c3 * g0 + c4 * gm1 + c5 * gm2) +
      (8 / 3 : k) * (f0 * f3 + f1 * f2) + 2 * epsilon * c3 = 0) :
    rhoOne_boundaryG_coordinateGainI3ThreeReduced68
      c1 c2 c3 c5 g2 g1 g0 gm2 epsilon = 0 := by
  rw [hb2, hb3, hb4, hf0, hf1, hgm1] at hi3
  dsimp only [rhoOne_boundaryG_coordinateGainI3ThreeReduced68]
  linear_combination hi3

/-- Source-facing coordinate-gain packet after consuming `I4(4)`. -/
def RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∧
  G.coeff (-2) ≠ 0 ∧
  B.coeff 3 = 0 ∧ F.coeff 1 = 0 ∧ B.coeff 4 = 0 ∧
  (↑(5 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
  (↑(2 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
  rhoOne_boundaryG_coordinateGainI4FourReduced68
    (B.coeff 6) (G.coeff (-2)) (C.coeff 1) (C.coeff 2)
    (F.coeff 2) (F.coeff 3) = 0 ∧
  rhoOne_boundaryG_coordinateGainI3OneReduced68
    (C.coeff 1) (C.coeff 3) (G.coeff 0) (G.coeff (-2))
    T.source.epsilon = 0 ∧
  rhoOne_boundaryG_i3threeSourceRow68 T = 0 ∧
  rhoOne_boundaryG_coordinateGainI3ThreeReduced68
    (C.coeff 1) (C.coeff 2) (C.coeff 3) (C.coeff 5)
    (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
    T.source.epsilon = 0

set_option maxHeartbeats 800000 in
/-- Unpack the coordinate-gain cell, consume `I4(4)`, and attach the
specialized `I3` rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_coordinateGain_i4four68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68] at Rc
  rcases Rc with ⟨Q, hB2, hF0, hGm1, hBord, hFord, hi4four⟩
  have hi3src := T.rhoOne_boundaryG_i3three_source68 Q
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
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB0, hC0, hFbase, hGbase,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hgm2 : G.coeff (-2) ≠ 0 := by
    convert hgneg using 1 <;> norm_num
  have hb3 := rhoOne_boundaryG_coordinateGain_b3_zero68
    (B.coeff 2) (B.coeff 3) (G.coeff (-1)) (G.coeff (-2))
    (C.coeff 1) (F.coeff 0) hB2 hGm1 hF0 hgm2 (by
      convert hi4one using 1 <;> norm_num)
  have hf1 := rhoOne_boundaryG_coordinateGain_f1_zero68
    (A.coeff (-2)) (A.coeff (-1)) (B.coeff 2) (F.coeff 1)
    (G.coeff (-1)) (G.coeff (-2)) hB2 hGm1 hgm2 (by
      convert hcross using 1 <;> norm_num)
  have hb4 := rhoOne_boundaryG_coordinateGain_b4_zero68
    (B.coeff 2) (B.coeff 3) (B.coeff 4) (G.coeff 0) (G.coeff (-1))
    (G.coeff (-2)) (C.coeff 1) (C.coeff 2) (F.coeff 0) (F.coeff 1)
    T.source.epsilon hB2 hb3 hGm1 hF0 hf1 hgm2 (by
      convert hi4two using 1 <;> norm_num)
  have hi4red := rhoOne_boundaryG_coordinateGain_i4four_reduce68
    (B.coeff 3) (B.coeff 4) (B.coeff 6) (G.coeff 1) (G.coeff 0)
    (G.coeff (-2)) (C.coeff 1) (C.coeff 2) (C.coeff 3)
    (F.coeff 1) (F.coeff 2) (F.coeff 3) T.source.epsilon
    hb3 hb4 hf1 (by convert hi4four using 1 <;> norm_num)
  have hi3oneRed := rhoOne_boundaryG_coordinateGain_i3one_reduce68
    (A.coeff (-2)) (A.coeff (-1)) (B.coeff 2) (B.coeff 3)
    (F.coeff 0) (F.coeff 1) (C.coeff 1) (C.coeff 2) (C.coeff 3)
    (G.coeff 0) (G.coeff (-1)) (G.coeff (-2)) T.source.epsilon
    hB2 hb3 hF0 hf1 hGm1 (by convert hi3one using 1 <;> norm_num)
  have hi3c := hi3src
  dsimp only [rhoOne_boundaryG_i3threeSourceRow68] at hi3c
  have hi3red := rhoOne_boundaryG_coordinateGain_i3three_reduce68
    (A.coeff (-2)) (A.coeff (-1)) (A.coeff 0) (A.coeff 1)
    (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5)
    (C.coeff 1) (C.coeff 2) (C.coeff 3) (C.coeff 4) (C.coeff 5)
    (F.coeff 0) (F.coeff 1) (F.coeff 2) (F.coeff 3)
    (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-1))
    (G.coeff (-2)) T.source.epsilon
    hB2 hb3 hb4 hF0 hf1 hGm1 (by convert hi3c using 1 <;> norm_num)
  have hB3c : B.coeff ((3 : ℤ) : ℚ) = 0 := by
    convert hb3 using 1 <;> norm_num
  have hB4ord := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root T.source.B 3 (by convert hBord using 1 <;> norm_num) hB3c
  have hB4c : B.coeff ((4 : ℤ) : ℚ) = 0 := by
    convert hb4 using 1 <;> norm_num
  have hB5ord := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root T.source.B 4 hB4ord hB4c
  let Fr : RatFunc k :=
    T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B
  have hFmap : ratFuncAtHahn46 T.root Fr = F := by
    dsimp only [Fr, F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hFord' : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root Fr).orderTop := by
    rw [hFmap]; exact hFord
  have hF1c : (ratFuncAtHahn46 T.root Fr).coeff ((1 : ℤ) : ℚ) = 0 := by
    rw [hFmap]; convert hf1 using 1 <;> norm_num
  have hF2ord := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root Fr 1 hFord' hF1c
  have hF2ord' : (↑(2 : ℚ) : WithTop ℚ) ≤ F.orderTop := by
    rw [← hFmap]
    convert hF2ord using 1 <;> norm_num
  dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68]
  refine ⟨R, hgm2, hb3, hf1, hb4, ?_, ?_, hi4red, hi3oneRed, hi3src, hi3red⟩
  · convert hB5ord using 1 <;> norm_num
  · convert hF2ord' using 1 <;> norm_num

/-- Quadratic `G[-2]` residual after consuming the coordinate-gain
`I4(4)` face.  QR and the nonsingular transport are copied literally. -/
def RhoOneAlignedSquareGNegTwoQuadraticChamberAfterCoordinateGainI4Four68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  RhoOneAlignedSquareGNegTwoCoordinateGainI4Four68 T g u ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T) ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
      let G := rhoOneTangentEDefectHahn68 A C
        (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
      A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0)

/-- Literal `G[-2]` inventory residual after the coordinate-gain `I4(4)`
step. -/
def RhoOneAlignedSquareGNegTwoInventoryResidualAfterCoordinateGainI4Four68
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
  RhoOneAlignedSquareGNegTwoQuadraticChamberAfterCoordinateGainI4Four68 T g u

/-- Normalized inventory with the coordinate-gain `I4(4)` face consumed. -/
def RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterCoordinateGainI4Four68
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
  RhoOneAlignedSquareGNegTwoInventoryResidualAfterCoordinateGainI4Four68 T g u ∨
  RhoOneAlignedSquareLocalFinalResidual68 T g u

/-- Source-facing quadratic selector after consuming coordinate-gain
`I4(4)`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_coordinateGain_i4four_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoQuadraticChamberAfterCoordinateGainI4Four68
      T g u := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_after_i4seven_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl (T.rhoOne_boundaryG_coordinateGain_i4four68 hcoord)
  · exact Or.inr (Or.inl hsigned)
  · exact Or.inr (Or.inr hnon)

/-- The old `G[-2] != 0` inventory residual, after consuming
coordinate-gain `I4(4)`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_coordinateGain_GnegTwo_inventory_after_i4four68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hG :
      RhoOneAlignedSquareGNegTwoInventoryResidualAfterSignedRayLinearDZero68
        T g u) :
    RhoOneAlignedSquareGNegTwoInventoryResidualAfterCoordinateGainI4Four68
      T g u := by
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterSignedRayLinearDZero68] at hG
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterCoordinateGainI4Four68]
  rcases hG with hpre | hquad
  · exact Or.inl hpre
  · refine Or.inr
      (T.rhoOne_boundaryG_coordinateGain_i4four_selector68
        hp hH hp6 hp5 hp4 ?_)
    dsimp only
      [RhoOneAlignedSquareGNegTwoQuadraticChamberAfterSignedRayLinearDZero68] at hquad
    rcases hquad with hcoord | hqr | hnon
    · have hcoordc := hcoord
      dsimp only [RhoOneAlignedSquareGNegTwoCoordinateGain68] at hcoordc
      exact hcoordc.1
    · exact hqr.1
    · exact hnon.1

/-- Refine the after-signed-ray-linear inventory by consuming the
coordinate-gain `I4(4)` face.  No other sibling is touched. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_coordinateGainI4Four68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterSignedRayLinearDZero68
      T g u) :
    RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterCoordinateGainI4Four68
      T g u := by
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterSignedRayLinearDZero68] at R
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterCoordinateGainI4Four68]
  rcases R with hdesc | hnoncubic | hearly | hpre | hgbox | hFne | hGne | hfinal
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · exact Or.inr (Or.inr (Or.inl hearly))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgbox))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFne)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (T.rhoOne_boundaryG_coordinateGain_GnegTwo_inventory_after_i4four68
        hp hH hp6 hp5 hp4 hGne)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hfinal))))))

/-- Normalized aligned-square source wrapper after the coordinate-gain
`I4(4)` consumption. -/
theorem normalized68ScaleTwo_alignedSquare_finalInventory_after_coordinateGainI4Four
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
      RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterCoordinateGainI4Four68
        T g u := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, T, g, u, hp5, hp4, R⟩ :=
    normalized68ScaleTwo_alignedSquare_finalInventory_after_signedRayLinearDZero
      hsource hh0 hH haligned
  exact ⟨j, T, g, u, hp5, hp4,
    T.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_coordinateGainI4Four68
      hp hH hp6 hp5 hp4 R⟩

end AlignedSquareCoordinateGainI4Four68

end Max11DegreeRoutes
