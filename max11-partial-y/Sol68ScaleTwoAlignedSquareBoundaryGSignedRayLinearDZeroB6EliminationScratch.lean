import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalCrossScratch

/-! # Eliminate the shared `B[6]` jet on the exact zero cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroB6Elimination68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The determinant `F[3]` value with its `B[6]` coordinate exposed. -/
def rhoOne_boundaryG_signedRayLinearDZeroF3AtB6Value68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let f1z := A.coeff (-1) * B.coeff 2 / 3
  let f2z := rhoOne_boundaryG_signedRayLinearDZeroF2Value68 T sigma r
  let R0 := rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
    (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
    (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
    (C.coeff 4) (C.coeff 5) f1z f2z
    (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let S0 := rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
    (B.coeff 2) (B.coeff 4) (B.coeff 5) b6
    (C.coeff 2) (C.coeff 3) (C.coeff 4) f1z f2z
    (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let f3z := -(R0 + 108 * r * sigma * S0) / (36 * B.coeff 2 * r ^ 2)
  f3z

/-- Terminal `-2` as an affine function of the exposed `B[6]`. -/
def rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let dA := ratFuncAtHahn46 T.root (Differential.deriv T.source.A)
  let f2z := rhoOne_boundaryG_signedRayLinearDZeroF2Value68 T sigma r
  486 * G.coeff (-2) * r ^ 2 *
      rhoOne_boundaryG_signedRayLinearDZeroF3AtB6Value68 T sigma r b6 -
    rhoOne_boundaryG_signedRayLinearDZeroTerminalNegTwoBase68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1)
      (B.coeff 2) (B.coeff 4) (B.coeff 5)
      (C.coeff 2) (C.coeff 3) f2z (G.coeff (-2)) (G.coeff 0)
      (dA.coeff (-2)) (dA.coeff (-1)) T.source.epsilon

/-- The F3-free `I3(4)` row as an affine function of `B[6]`. -/
def rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
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
  let f1z := A.coeff (-1) * b / 3
  let f2z := rhoOne_boundaryG_signedRayLinearDZeroF2Value68 T sigma r
  let R0 := rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
    (A.coeff (-1)) (A.coeff 0) (A.coeff 1) b (B.coeff 4)
    (B.coeff 5) (C.coeff 2) (C.coeff 3) (C.coeff 4) (C.coeff 5)
    f1z f2z (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let S0 := rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b
    (B.coeff 4) (B.coeff 5) b6 (C.coeff 2) (C.coeff 3)
    (C.coeff 4) f1z f2z (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let g2z := -(R0 + 216 * r * sigma * S0) / (108 * b * r * sigma)
  (-(8 / 9 : k)) *
      ((-(r ^ 2 / 3)) * b * F.coeff 4 +
        ((-(r ^ 2 / 3)) * B.coeff 4 + A.coeff 0 * b) * f2z +
        ((-(r ^ 2 / 3)) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 1 * b) * f1z +
        ((-(r ^ 2 / 3)) * b6 + A.coeff (-1) * B.coeff 5 +
          A.coeff 0 * B.coeff 4 + A.coeff 2 * b) * (r ^ 2 * b / 9)) -
    (8 / 9 : k) * b ^ 2 * C.coeff 0 +
    (8 / 3 : k) *
      ((-(sigma * r * b / 3)) * G.coeff 3 + C.coeff 2 * g2z +
        C.coeff 3 * G.coeff 1 + C.coeff 4 * G.coeff 0 +
        C.coeff 5 * (sigma * r ^ 3 * b / 27) + C.coeff 6 * G.coeff (-2)) +
    (4 / 3 : k) * (2 * (r ^ 2 * b / 9) * F.coeff 4 + f2z ^ 2) -
    (2 / 3 : k) * T.source.gamma * b ^ 2 +
    2 * T.source.epsilon * C.coeff 4

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_terminal_at_source_b6_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) :
    rhoOne_boundaryG_signedRayLinearDZeroTerminalTransportResidual68 T sigma r =
      rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68 T sigma r
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6) := by
  rfl

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3four_at_source_b6_68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) :
    rhoOne_boundaryG_signedRayLinearDZeroI3FourCrossResidual68 T sigma r =
      rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68 T sigma r
        ((ratFuncAtHahn46 T.root T.source.B).coeff 6) := by
  rfl

omit [IsAlgClosed k] in
/-- Cleared affine terminal identity. -/
theorem rhoOne_boundaryG_signedRayLinear_dZero_terminal_b6_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k)
    (hr : r ≠ 0)
    (hb : (ratFuncAtHahn46 T.root T.source.B).coeff 2 ≠ 0) :
    (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
        rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
          T sigma r b6 =
      (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
          rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
            T sigma r 0 -
        1458 * sigma *
          (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r * b6 := by
  dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68,
    rhoOne_boundaryG_signedRayLinearDZeroF3AtB6Value68,
    rhoOne_boundaryG_signedRayLinearI4FourBase68]
  field_simp [hb, hr]
  ring

omit [IsAlgClosed k] in
/-- Cleared affine `I3(4)` identity; its exposed coefficient is the factored
wall `r⁴B[2]²-162C[2]G[-2]`. -/
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3four_b6_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r b6 : k)
    (hsigma : sigma ^ 2 = 1) (hr : r ≠ 0)
    (hb : (ratFuncAtHahn46 T.root T.source.B).coeff 2 ≠ 0) :
    (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
        rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
          T sigma r b6 =
      (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
          rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
            T sigma r 0 +
        (8 / 243 : k) *
          (r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
            162 * (rhoOneCDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
              (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) * b6 := by
  have hs0 : sigma ≠ 0 := by
    intro hs
    rw [hs] at hsigma
    norm_num at hsigma
  dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68,
    rhoOne_boundaryG_signedRayLinearI4FourBase68]
  field_simp [hb, hr, hs0]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRayLinear_dZero_terminal_b6_coefficient_ne_zero68
    (sigma r gm2 : k) (hsigma : sigma ^ 2 = 1)
    (hr : r ≠ 0) (hgm2 : gm2 ≠ 0) :
    1458 * sigma * gm2 ^ 2 * r ≠ 0 := by
  have hs0 : sigma ≠ 0 := by
    intro hs
    rw [hs] at hsigma
    norm_num at hsigma
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hs0) (pow_ne_zero 2 hgm2)) hr

/-- Result after eliminating `B[6]`: the terminal row gives an explicit
division-free transport, and the cross resultant contains no `B[6]`. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    (((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 = 0) ∧
        1458 * sigma * G.coeff (-2) ^ 2 * r * B.coeff 6 =
          B.coeff 2 *
            rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
              T sigma r 0 ∧
        4 * (r ^ 4 * B.coeff 2 ^ 2 - 162 * C.coeff 2 * G.coeff (-2)) *
            rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
              T sigma r 0 +
          177147 * sigma * G.coeff (-2) ^ 2 * r *
            rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
              T sigma r 0 = 0) ∨
      ((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 ≠ 0) ∧
        4 * (3 * F.coeff 1 - A.coeff (-1) * B.coeff 2) *
            rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
              (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
              (C.coeff 2) (G.coeff (-2)) =
          -243 * G.coeff (-2) ^ 2 *
            rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
              (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
              (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
              (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 3)
              (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
              T.source.epsilon))

/-- Source-facing elimination of the shared `B[6]`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_b6_elimination68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68] at Rc
  rcases Rc with ⟨Rkeep, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hsplit⟩
  have hfinal :
      ((3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0) ∧
        1458 * sigma *
            (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r *
            (ratFuncAtHahn46 T.root T.source.B).coeff 6 =
          (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
            rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
              T sigma r 0 ∧
        4 * (r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
            162 * (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
              (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) *
            rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
              T sigma r 0 +
          177147 * sigma *
            (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r *
            rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
              T sigma r 0 = 0) ∨
      ((3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 ≠ 0) ∧
        4 * (3 * (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
            (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
              (ratFuncAtHahn46 T.root T.source.B).coeff 2) *
          rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
            ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
            ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
            ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
            ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) =
        -243 * (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 *
          rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
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
            T.source.epsilon) := by
    rcases hsplit with hzero | hnon
    · left
      have ht := hzero.2.2
      have hi := hzero.2.1
      rw [rhoOne_boundaryG_signedRayLinear_dZero_terminal_at_source_b6_68] at ht
      rw [rhoOne_boundaryG_signedRayLinear_dZero_i3four_at_source_b6_68] at hi
      have hta := rhoOne_boundaryG_signedRayLinear_dZero_terminal_b6_affine68
        T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6) hr0 hb
      have hia := rhoOne_boundaryG_signedRayLinear_dZero_i3four_b6_affine68
        T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
          hsigma hr0 hb
      rw [ht] at hta
      rw [hi] at hia
      have htransport :
          1458 * sigma *
              (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r *
              (ratFuncAtHahn46 T.root T.source.B).coeff 6 =
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
              rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
                T sigma r 0 := by
        linear_combination hta
      have hresb :
          (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
            (4 * (r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
                162 * (rhoOneCDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
                  (rhoOneTangentEDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (rhoOneCDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (ratFuncAtHahn46 T.root T.source.C0))
                    (rhoOneEDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) *
                rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
                  T sigma r 0 +
              177147 * sigma *
                (rhoOneTangentEDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (rhoOneCDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0))
                  (rhoOneEDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r *
                rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
                  T sigma r 0) = 0 := by
        linear_combination
          -(243 / 2 : k) *
            (1458 * sigma *
              (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r * hia +
              (8 / 243 : k) *
                (r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
                  162 * (rhoOneCDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
                    (rhoOneTangentEDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (rhoOneCDefectHahn68
                        (ratFuncAtHahn46 T.root T.source.A)
                        (ratFuncAtHahn46 T.root T.source.C0))
                      (rhoOneEDefectHahn68
                        (ratFuncAtHahn46 T.root T.source.A)
                        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) * hta)
      have hres :
          4 * (r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
              162 * (rhoOneCDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
                (rhoOneTangentEDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0))
                  (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) *
              rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
                T sigma r 0 +
            177147 * sigma *
              (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2 * r *
              rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
                T sigma r 0 = 0 := by
        apply (mul_left_cancel₀ hb)
        simpa only [mul_zero] using hresb
      exact ⟨hzero.1, htransport, hres⟩
    · exact Or.inr hnon
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68]
  exact ⟨R, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hfinal⟩

/-- Source selector: only the exact zero cell is strengthened. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_b6_elimination_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_cross_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hzero | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_b6_elimination68 hzero)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroB6Elimination68

end Max11DegreeRoutes
