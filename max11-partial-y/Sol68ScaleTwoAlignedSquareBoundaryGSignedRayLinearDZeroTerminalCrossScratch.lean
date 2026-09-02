import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalNegTwoScratch

/-! # Exact terminal-minus-two / I3(4) cross on the zero cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalCross68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- After all determinant-zero substitutions, terminal coefficient `-2`
has this compact numerator apart from its nonzero scalar factor. -/
def rhoOne_boundaryG_signedRayLinearDZeroTerminalNegTwoBase68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 f2 gm2 g0 d2 d1 epsilon : k) : k :=
  -243 * a0 * b * d2 * gm2 + 18 * a1 ^ 2 * b ^ 2 * r ^ 3 * sigma -
    18 * a1 * b ^ 2 * d2 * r ^ 3 * sigma - 486 * a1 * b * d1 * gm2 -
    243 * a1 * b * epsilon * r ^ 2 - 324 * a1 * b * g0 * r ^ 2 -
    162 * a1 * b4 * gm2 * r ^ 2 - 162 * aOne * b * gm2 * r ^ 2 -
    3 * b ^ 2 * d1 * r ^ 5 * sigma + 2 * b * b4 * r ^ 7 * sigma +
    9 * b * c2 * d2 * r ^ 4 + 6 * b * c3 * r ^ 6 -
    36 * b * f2 * r ^ 5 * sigma + 81 * b4 * d2 * gm2 * r ^ 2 +
    54 * b5 * gm2 * r ^ 4 - 729 * d2 * f2 * gm2

omit [IsAlgClosed k] in
/-- The exact cancellation in terminal coefficient `-2`: after inserting
the signed-ray and zero-cell values, `dA[0]` and `G[1]` disappear and the
row is linear in `F[3]`. -/
theorem rhoOne_boundaryG_signedRayLinear_dZero_terminalNegTwo_transport68
    (sigma r a1 a0 aOne b b4 b5 c2 c3 f2 f3 gm2 g0 g1
      d2 d1 d0 epsilon : k)
    (hraw : rhoOne_boundaryG_terminalNegTwoRaw68 epsilon
      (-(r ^ 2 / 3)) a1 a0 aOne b 0 b4 b5
      (-(sigma * r * b / 3)) c2 c3
      (r ^ 2 * b / 9) (a1 * b / 3) f2 f3
      gm2 (sigma * r ^ 3 * b / 27) g0 g1
      (2 * r ^ 2 / 3) d2 d1 d0 = 0) :
    486 * gm2 * r ^ 2 * f3 =
      rhoOne_boundaryG_signedRayLinearDZeroTerminalNegTwoBase68
        sigma r a1 a0 aOne b b4 b5 c2 c3 f2 gm2 g0 d2 d1 epsilon := by
  dsimp only [rhoOne_boundaryG_terminalNegTwoRaw68,
    rhoOne_boundaryG_signedRayLinearDZeroTerminalNegTwoBase68] at hraw ⊢
  linear_combination (-(6561 / 4 : k)) * hraw

/-- The already-solved `F[2]` value on the determinant-zero cell. -/
def rhoOne_boundaryG_signedRayLinearDZeroF2Value68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
    (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
    (C.coeff 2) (G.coeff (-2)) / (6561 * G.coeff (-2) ^ 2)

/-- The already-solved `F[3]` value from the two-by-two determinant. -/
def rhoOne_boundaryG_signedRayLinearDZeroF3Value68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : k :=
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
    (B.coeff 2) (B.coeff 4) (B.coeff 5) (B.coeff 6)
    (C.coeff 2) (C.coeff 3) (C.coeff 4) f1z f2z
    (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let f3z := -(R0 + 108 * r * sigma * S0) / (36 * B.coeff 2 * r ^ 2)
  f3z

/-- The compact terminal transport after substituting every solved zero-cell
value.  Its coefficient of the solved `F[3]` value is nonzero. -/
def rhoOne_boundaryG_signedRayLinearDZeroTerminalTransportResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let dA := ratFuncAtHahn46 T.root (Differential.deriv T.source.A)
  let f2z := rhoOne_boundaryG_signedRayLinearDZeroF2Value68 T sigma r
  let f3z := rhoOne_boundaryG_signedRayLinearDZeroF3Value68 T sigma r
  486 * G.coeff (-2) * r ^ 2 * f3z -
    rhoOne_boundaryG_signedRayLinearDZeroTerminalNegTwoBase68 sigma r
      (A.coeff (-1)) (A.coeff 0) (A.coeff 1)
      (B.coeff 2) (B.coeff 4) (B.coeff 5)
      (C.coeff 2) (C.coeff 3) f2z (G.coeff (-2)) (G.coeff 0)
      (dA.coeff (-2)) (dA.coeff (-1)) T.source.epsilon

/-- `I3(4)` after its two `F[3]` contributions cancel.  Thus the joint
system is triangular: terminal `-2` fixes the determinant `F[3]` transport,
whereas this row retains only the genuinely new fourth-jet coordinates. -/
def rhoOne_boundaryG_signedRayLinearDZeroI3FourCrossResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : k :=
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
    (B.coeff 4) (B.coeff 5) (B.coeff 6) (C.coeff 2) (C.coeff 3)
    (C.coeff 4) f1z f2z (G.coeff 0) (G.coeff (-2)) T.source.epsilon
  let g2z := -(R0 + 216 * r * sigma * S0) / (108 * b * r * sigma)
  (-(8 / 9 : k)) *
      ((-(r ^ 2 / 3)) * b * F.coeff 4 +
        ((-(r ^ 2 / 3)) * B.coeff 4 + A.coeff 0 * b) * f2z +
        ((-(r ^ 2 / 3)) * B.coeff 5 + A.coeff (-1) * B.coeff 4 +
          A.coeff 1 * b) * f1z +
        ((-(r ^ 2 / 3)) * B.coeff 6 + A.coeff (-1) * B.coeff 5 +
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
theorem rhoOne_boundaryG_signedRayLinear_dZero_i3four_cancel68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) :
    rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68 T sigma r =
      rhoOne_boundaryG_signedRayLinearDZeroI3FourCrossResidual68 T sigma r := by
  dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68,
    rhoOne_boundaryG_signedRayLinearDZeroI3FourCrossResidual68,
    rhoOne_boundaryG_signedRayLinearDZeroF2Value68]
  ring

/-- The cleared source coordinate supplies the one derivative value needed
to reduce terminal coefficient `-2`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_dA_negThree_source68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-3) =
      (-2 : k) * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) := by
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
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * T.source.A at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff 1)
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
  convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
    T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num

/-- The fully simplified joint packet.  The zero cell is now a triangular
pair: an `F[3]` transport from terminal `-2` and an `F[3]`-free `I3(4)` row.
Every outer sibling remains in the predecessor conjunct. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegTwo68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    (((3 * F.coeff 1 - A.coeff (-1) * B.coeff 2 = 0) ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3FourCrossResidual68
          T sigma r = 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroTerminalTransportResidual68
          T sigma r = 0) ∨
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

/-- Substitute the exact determinant-zero witness into both rows and reduce
the joint system to its triangular normal form. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_cross68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68 T := by
  have Rkeep := T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negTwo68
    hp hH hp6 hp5 hp4 Q R
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68] at Rc
  rcases Rc with ⟨Rprev, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hF3, hG2, hsplit⟩
  have hi3row := T.rhoOne_boundaryG_i3four_source68 Q
  have hi3c := hi3row
  dsimp only [rhoOne_boundaryG_i3fourSourceRow68,
    rhoOne_boundaryG_i3fourHahnRow68] at hi3c
  have hterm := T.rhoOne_boundaryG_terminal_negTwo_source68
    hp hH hp6 hp5 hp4 Q
  have htermc := hterm
  dsimp only [rhoOne_boundaryG_terminalNegTwoSourceRow68] at htermc
  have hd3 := T.rhoOne_boundaryG_dA_negThree_source68
    hp hH hp6 hp5 hp4 Q
  have ha : (ratFuncAtHahn46 T.root T.source.A).coeff (-2) =
      -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgm1 :
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
    rw [hrf, hgm1]
    linear_combination
      (r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 9) * hsigma
  have hc1 :
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 =
      -(sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hd3z :
      (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-3) =
        2 * r ^ 2 / 3 := by
    rw [hd3, ha]
    ring
  have hfinal :
      ((3 * (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 -
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 = 0) ∧
        rhoOne_boundaryG_signedRayLinearDZeroI3FourCrossResidual68
          T sigma r = 0 ∧
        rhoOne_boundaryG_signedRayLinearDZeroTerminalTransportResidual68
          T sigma r = 0) ∨
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
      have hf1 : (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1 =
          (ratFuncAtHahn46 T.root T.source.A).coeff (-1) *
            (ratFuncAtHahn46 T.root T.source.B).coeff 2 / 3 := by
        linear_combination (1 / 3 : k) * hzero.1
      have hf2raw := hzero.2.2
      have hf3raw := hF3
      have hg2raw := hG2
      rw [hf1, hf2raw] at hf3raw hg2raw
      have hf2 : (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 2 =
          rhoOne_boundaryG_signedRayLinearDZeroF2Value68 T sigma r := by
        simpa only [rhoOne_boundaryG_signedRayLinearDZeroF2Value68] using hf2raw
      have hf3' : (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 3 =
          rhoOne_boundaryG_signedRayLinearDZeroF3Value68 T sigma r := by
        simpa only [rhoOne_boundaryG_signedRayLinearDZeroF3Value68,
          rhoOne_boundaryG_signedRayLinearDZeroF2Value68] using hf3raw
      have hi3old :
          rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68 T sigma r = 0 := by
        rw [ha, hb3, hc1, hf0, hgm1, hf1, hf2raw, hf3raw, hg2raw] at hi3c
        dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3FourResidual68]
        linear_combination hi3c
      rw [rhoOne_boundaryG_signedRayLinear_dZero_i3four_cancel68] at hi3old
      rw [ha, hb3, hc1, hf0, hgm1, hf1, hf2, hf3', hd3z] at htermc
      have ht := rhoOne_boundaryG_signedRayLinear_dZero_terminalNegTwo_transport68
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
        (rhoOne_boundaryG_signedRayLinearDZeroF2Value68 T sigma r)
        (rhoOne_boundaryG_signedRayLinearDZeroF3Value68 T sigma r)
        ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
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
        ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-2))
        ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-1))
        ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff 0)
        T.source.epsilon htermc
      have htransport :
          rhoOne_boundaryG_signedRayLinearDZeroTerminalTransportResidual68
            T sigma r = 0 := by
        dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalTransportResidual68]
        linear_combination ht
      exact ⟨hzero.1, hi3old, htransport⟩
    · exact Or.inr hnon
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68]
  exact ⟨Rkeep, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hfinal⟩

/-- Outer selector with the exact zero cell replaced by the compact joint
system and all other leaves carried literally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_cross_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalCross68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_determinantSolved_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hlinear | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_cross68
          hp hH hp6 hp5 hp4 hsigned.1 hlinear)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalCross68

end Max11DegreeRoutes
