import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearCoefficientSplitScratch

/-! # Determinant inversion on the signed linear factor -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDeterminantSolve68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The reduced `I3(3)` remainder after removing its `F[3]` and `G[2]`
terms. -/
def rhoOne_boundaryG_signedRayLinearI3ThreeRest68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 c4 c5
      f1 f2 g1 g0 gm2 epsilon : k) : k :=
  -108 * a0 * b * f1 - 12 * a1 * b * b4 * r ^ 2 -
    108 * a1 * b * f2 - 12 * aOne * b ^ 2 * r ^ 2 +
    4 * b * b5 * r ^ 4 + 12 * b * c4 * r ^ 3 * sigma +
    36 * b4 * f1 * r ^ 2 + 324 * c2 * g1 +
    243 * c3 * epsilon + 324 * c3 * g0 + 324 * c5 * gm2 +
    324 * f1 * f2

omit [IsAlgClosed k] in
/-- Invert the nonzero two-by-two determinant of the I3/I4 top faces.
Only `B[2]`, `r`, and `sigma` are divided by, each proved nonzero. -/
theorem rhoOne_boundaryG_signedRayLinear_determinant_solve68
    (sigma r a1 a0 aOne b b4 b5 b6 c2 c3 c4 c5
      f1 f2 f3 g2 g1 g0 gm2 epsilon : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0) (hb : b ≠ 0)
    (hi3 : rhoOne_boundaryG_signedRayLinearI3ThreeReduced68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 f3 g2 g1 g0 gm2 epsilon = 0)
    (hi4 : b * g2 - (sigma * r * b / 3) * f3 +
      rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r b b4 b5 b6
        c2 c3 c4 f1 f2 g0 gm2 epsilon = 0) :
    let R0 := rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
      a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 g1 g0 gm2 epsilon
    let S0 := rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
      b b4 b5 b6 c2 c3 c4 f1 f2 g0 gm2 epsilon
    f3 = -(R0 + 108 * r * sigma * S0) / (36 * b * r ^ 2) ∧
      g2 = -(R0 + 216 * r * sigma * S0) / (108 * b * r * sigma) := by
  dsimp only
  have hsigma0 : sigma ≠ 0 := by
    intro hs
    rw [hs] at hsigma
    norm_num at hsigma
  have hdenF : (36 : k) * b * r ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 hr0)
  have hdenG : (108 : k) * b * r * sigma ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb) hr0) hsigma0
  have hfclear :
      36 * b * r ^ 2 * f3 +
        rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
          a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 g1 g0 gm2 epsilon +
        108 * r * sigma *
          rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
            b b4 b5 b6 c2 c3 c4 f1 f2 g0 gm2 epsilon = 0 := by
    dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeReduced68,
      rhoOne_boundaryG_signedRayLinearI3ThreeRest68,
      rhoOne_boundaryG_signedRayLinearI4FourBase68] at *
    linear_combination hi3 + 108 * r * sigma * hi4 +
      36 * b * r ^ 2 * f3 * hsigma
  have hgclear :
      108 * b * r * sigma * g2 +
        rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
          a1 a0 aOne b b4 b5 c2 c3 c4 c5 f1 f2 g1 g0 gm2 epsilon +
        216 * r * sigma *
          rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
            b b4 b5 b6 c2 c3 c4 f1 f2 g0 gm2 epsilon = 0 := by
    dsimp only [rhoOne_boundaryG_signedRayLinearI3ThreeReduced68,
      rhoOne_boundaryG_signedRayLinearI3ThreeRest68,
      rhoOne_boundaryG_signedRayLinearI4FourBase68] at *
    linear_combination hi3 + 216 * r * sigma * hi4 +
      72 * b * r ^ 2 * f3 * hsigma
  constructor
  · apply (eq_div_iff hdenF).2
    linear_combination hfclear
  · apply (eq_div_iff hdenG).2
    linear_combination hgclear

omit [IsAlgClosed k] in
/-- On the zero coefficient cell the terminal row uniquely solves
`F[2]`, using only `G[-2] ≠ 0`. -/
theorem rhoOne_boundaryG_signedRayLinear_terminal_f2_solve68
    (sigma r a1 a0 b b4 c2 f2 gm2 : k)
    (hgm2 : gm2 ≠ 0)
    (hterminal : rhoOne_boundaryG_signedRayLinearTerminalResidual68 sigma r
      a1 a0 b b4 c2 f2 gm2 = 0) :
    f2 = rhoOne_boundaryG_signedRayLinearTerminalBase68
      sigma r a1 a0 b b4 c2 gm2 / (6561 * gm2 ^ 2) := by
  have hden : (6561 : k) * gm2 ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hgm2)
  apply (eq_div_iff hden).2
  dsimp only [rhoOne_boundaryG_signedRayLinearTerminalResidual68,
    rhoOne_boundaryG_signedRayLinearTerminalBase68] at hterminal ⊢
  linear_combination -hterminal

/-- Final explicit determinant packet.  The zero `D` cell additionally
solves `F[2]`; the nonzero cell retains its exact resultant transport. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    let R0 := rhoOne_boundaryG_signedRayLinearI3ThreeRest68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
      (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
      (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 2)
      (G.coeff 1) (G.coeff 0) (G.coeff (-2)) T.source.epsilon
    let S0 := rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
      (B.coeff 2) (B.coeff 4) (B.coeff 5) (B.coeff 6)
      (C.coeff 2) (C.coeff 3) (C.coeff 4) (F.coeff 1) (F.coeff 2)
      (G.coeff 0) (G.coeff (-2)) T.source.epsilon
    F.coeff 3 = -(R0 + 108 * r * sigma * S0) / (36 * B.coeff 2 * r ^ 2) ∧
    G.coeff 2 = -(R0 + 216 * r * sigma * S0) /
      (108 * B.coeff 2 * r * sigma) ∧
    (((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 = 0) ∧
        rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
          (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
          (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
          (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 3)
          (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
          T.source.epsilon = 0 ∧
        F.coeff 2 = rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
          (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
          (C.coeff 2) (G.coeff (-2)) / (6561 * G.coeff (-2) ^ 2)) ∨
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

/-- Rebuild the coefficient split on the exact terminal witness, invert the
top determinant, and solve `F[2]` on the zero cell. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_determinantSolved68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68 T := by
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
    hfneg, hgm2, hb1, hS0, hscalar, hi4base⟩
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearCoefficientSplit68] at Rc
  rcases Rc with ⟨Rred, oldWitness⟩
  have Rredc := Rred
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearI3ThreeReduction68] at Rredc
  rcases Rredc with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf,
    hlinear, hb3, hterminal, hi3source, hred, helim⟩
  have hsplit := rhoOne_boundaryG_signedRayLinear_coefficient_split68 sigma r
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
    T.source.epsilon hred helim
  have hi4source := T.rhoOne_boundaryG_i4four_source68 Q
  have hi4c := hi4source
  dsimp only [rhoOne_boundaryG_i4fourSourceRow68] at hi4c
  have hgmEq :
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hf0 :
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 0 =
      r ^ 2 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgmEq]
    linear_combination
      (r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) * hsigma
  have hc1 :
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 =
      -(sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  rw [hb3, hgmEq, hc1, hf0] at hi4c
  have hi4red :
      (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 2 -
        (sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) *
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 3 +
        rhoOne_boundaryG_signedRayLinearI4FourBase68 sigma r
          ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 4)
          ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
          ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
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
          T.source.epsilon = 0 := by
    dsimp only [rhoOne_boundaryG_signedRayLinearI4FourBase68]
    linear_combination hi4c
  have hsolve := rhoOne_boundaryG_signedRayLinear_determinant_solve68 sigma r
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
    ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
    ((ratFuncAtHahn46 T.root T.source.A).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 5)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
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
    T.source.epsilon hsigma hr0 hb hred hi4red
  have hfinalSplit :
      ((3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0) ∧
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
          T.source.epsilon = 0 ∧
        (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 2 =
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
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) /
            (6561 * (rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ^ 2)) ∨
      (3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 ≠ 0 ∧
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
    · exact Or.inl ⟨hzero.1, hzero.2,
        rhoOne_boundaryG_signedRayLinear_terminal_f2_solve68 sigma r
          ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
          ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
          ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
          ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
          hgm2 hterminal⟩
    · exact Or.inr hnon
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68]
  exact ⟨R, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hsolve.1, hsolve.2, hfinalSplit⟩

/-- Outer selector: only the signed linear child is refined. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_determinantSolved_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_coefficientSplit_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hlinear | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_determinantSolved68
          hsigned.1 hlinear)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDeterminantSolve68

end Max11DegreeRoutes
