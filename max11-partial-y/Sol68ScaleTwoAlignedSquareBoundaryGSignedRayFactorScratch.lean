import Sol68ScaleTwoAlignedSquareBoundaryGCoordinateEndpointScratch

/-! # Factoring the signed-ray determinant on the `G[-2]` boundary -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayFactor68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The reduced `Q0,R0` determinant factors uniformly on both signed
square-root rays. -/
theorem rhoOne_boundaryG_signedRay_determinant_factor68
    (sigma r a b gm c q s : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0) (hb : b ≠ 0)
    (hr : r ^ 2 = -3 * a)
    (hray : 27 * gm = sigma * r ^ 3 * b)
    (hred : 9 * q * a * b * c - 27 * q * b * gm +
      8 * s * a ^ 2 * b ^ 2 + 72 * s * c * gm = 0) :
    3 * c + sigma * r * b = 0 ∨ -9 * q + 8 * sigma * r * s = 0 := by
  have haeq : a = -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgmeq : gm = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hid : 9 *
      (9 * q * a * b * c - 27 * q * b * gm +
        8 * s * a ^ 2 * b ^ 2 + 72 * s * c * gm) =
      r ^ 2 * b * (3 * c + sigma * r * b) *
        (-9 * q + 8 * sigma * r * s) := by
    rw [haeq, hgmeq]
    linear_combination (-8 * s * b ^ 2 * r ^ 4) * hsigma
  have hz : r ^ 2 * b * (3 * c + sigma * r * b) *
      (-9 * q + 8 * sigma * r * s) = 0 := by
    rw [← hid, hred]
    ring
  have hpre : r ^ 2 * b ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr0) hb
  have hpair : (3 * c + sigma * r * b) *
      (-9 * q + 8 * sigma * r * s) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hpre
    simpa only [mul_assoc] using hz
  exact mul_eq_zero.mp hpair

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRay_wall68
    (sigma r a b gm : k) (hsigma : sigma ^ 2 = 1)
    (hr : r ^ 2 = -3 * a)
    (hray : 27 * gm = sigma * r ^ 3 * b) :
    a ^ 3 * b ^ 2 + 27 * gm ^ 2 = 0 := by
  have haeq : a = -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgmeq : gm = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  rw [haeq, hgmeq]
  linear_combination (r ^ 6 * b ^ 2 / 27) * hsigma

def RhoOneAlignedSquareGNegTwoSignedRayFactored68
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
    (3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∨
      -9 * Q0 + 8 * sigma * r * R0 = 0)

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRayFactor68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        RhoOneAlignedSquareGNegTwoSignedRayFactored68 T) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_coordinateEndpoint68 R with hcoord | hray | hnon
  · exact Or.inl hcoord
  · right; left
    refine ⟨R, ?_⟩
    rcases hray with ⟨_, hray⟩
    dsimp only [RhoOneAlignedSquareGNegTwoSignedRayWitness68] at hray
    rcases hray with ⟨hb, hgm, r, hr0, hr, hsign⟩
    have Rc := R
    dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Rc
    rcases Rc with ⟨Rm, hsplit⟩
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
    have hwallray : A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 +
        27 * G.coeff (-1) ^ 2 = 0 := by
      rcases hsign with hpos | hneg
      · exact rhoOne_boundaryG_signedRay_wall68 (1 : k) r
          (A.coeff (-2)) (B.coeff 2) (G.coeff (-1))
          (by norm_num) hr (by simpa using hpos.1)
      · exact rhoOne_boundaryG_signedRay_wall68 (-1 : k) r
          (A.coeff (-2)) (B.coeff 2) (G.coeff (-1))
          (by norm_num) hr (by linear_combination hneg.1)
    have hred : 9 * Q0 * A.coeff (-2) * B.coeff 2 * C.coeff 1 -
        27 * Q0 * B.coeff 2 * G.coeff (-1) +
        8 * R0 * A.coeff (-2) ^ 2 * B.coeff 2 ^ 2 +
        72 * R0 * C.coeff 1 * G.coeff (-1) = 0 := by
      rcases hsplit with hw | hn
      · dsimp only [A, B, C, F, G, Q0, R0] at hw ⊢
        exact hw.2.1
      · exfalso
        exact hn.1 hwallray
    rcases hsign with hpos | hneg
    · have hfac := rhoOne_boundaryG_signedRay_determinant_factor68
        (1 : k) r (A.coeff (-2)) (B.coeff 2) (G.coeff (-1))
        (C.coeff 1) Q0 R0 (by norm_num) hr0 hb hr
        (by simpa using hpos.1) hred
      dsimp only [RhoOneAlignedSquareGNegTwoSignedRayFactored68]
      refine ⟨1, r, by norm_num, hr0, hb, hgm, hr, ?_, ?_, hfac⟩
      · simpa using hpos.1
      · simpa using hpos.2
    · have hfac := rhoOne_boundaryG_signedRay_determinant_factor68
        (-1 : k) r (A.coeff (-2)) (B.coeff 2) (G.coeff (-1))
        (C.coeff 1) Q0 R0 (by norm_num) hr0 hb hr
        (by linear_combination hneg.1) hred
      dsimp only [RhoOneAlignedSquareGNegTwoSignedRayFactored68]
      refine ⟨-1, r, by norm_num, hr0, hb, hgm, hr, ?_, ?_, ?_⟩
      · linear_combination hneg.1
      · linear_combination hneg.2
      · dsimp only [A, B, C, F, G, Q0, R0] at hfac
        simpa only [one_mul, neg_mul, neg_neg] using hfac
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayFactor68

end Max11DegreeRoutes
