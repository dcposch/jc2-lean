import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayTerminalScratch

/-! # The linear determinant factor on the signed `G[-2]` rays -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearFactor68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- On the linear determinant factor, `I4(1)` loses its two signed-ray
terms and forces `B[3]=0`. -/
theorem rhoOne_boundaryG_signedRay_linearFactor_b3_zero68
    (sigma r b b3 c1 f g gm : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0) (hg : g ≠ 0)
    (hray : 27 * gm = sigma * r ^ 3 * b)
    (hrf : r * f = 3 * sigma * gm)
    (hlinear : 3 * c1 + sigma * r * b = 0)
    (hi4one : b * gm + b3 * g + c1 * f = 0) :
    b3 = 0 := by
  have hgmeq : gm = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hfeq : f = r ^ 2 * b / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgmeq]
    linear_combination (r ^ 3 * b / 9) * hsigma
  have hc1eq : c1 = -(sigma * r * b / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hz : b3 * g = 0 := by
    rw [hgmeq, hfeq, hc1eq] at hi4one
    linear_combination hi4one
  exact (mul_eq_zero.mp hz).resolve_right hg

omit [IsAlgClosed k] in
/-- Terminal `-3` after the linear factor, cleared of its harmless
denominator three. -/
def rhoOne_boundaryG_signedRayLinearTerminalResidual68
    (sigma r a1 a0 b b4 c2 f2 g : k) : k :=
  -2187 * a0 * b * g ^ 2 +
    162 * a1 * b ^ 2 * g * r ^ 3 * sigma +
    2 * b ^ 3 * r ^ 8 +
    81 * b * c2 * g * r ^ 4 +
    729 * b4 * g ^ 2 * r ^ 2 -
    6561 * f2 * g ^ 2

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_signedRay_linearFactor_terminal_reduce68
    (sigma r a1 a0 b b4 c1 c2 f2 g : k)
    (hsigma : sigma ^ 2 = 1)
    (hlinear : 3 * c1 + sigma * r * b = 0)
    (hterminal : rhoOne_boundaryG_signedRayTerminalResidual68
      sigma r a1 a0 b b4 c1 c2 f2 g = 0) :
    rhoOne_boundaryG_signedRayLinearTerminalResidual68
      sigma r a1 a0 b b4 c2 f2 g = 0 := by
  have hc1eq : c1 = -(sigma * r * b / 3) := by
    linear_combination (1 / 3 : k) * hlinear
  have hid : 3 * rhoOne_boundaryG_signedRayTerminalResidual68
        sigma r a1 a0 b b4 c1 c2 f2 g =
      rhoOne_boundaryG_signedRayLinearTerminalResidual68
        sigma r a1 a0 b b4 c2 f2 g := by
    rw [hc1eq]
    dsimp only [rhoOne_boundaryG_signedRayTerminalResidual68,
      rhoOne_boundaryG_signedRayLinearTerminalResidual68]
    linear_combination 2 * b ^ 3 * r ^ 8 * hsigma
  rw [← hid, hterminal]
  ring

/-- Exact signed-ray factor audit.  The linear factor survives, but only
with `B[3]=0` and the displayed cleared terminal scalar.  The `Q0/R0`
factor retains the preceding terminal scalar literally. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearRefined68
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
    ((3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧
        B.coeff 3 = 0 ∧
        rhoOne_boundaryG_signedRayLinearTerminalResidual68 sigma r
          (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
          (C.coeff 2) (F.coeff 2) (G.coeff (-2)) = 0) ∨
      (-9 * Q0 + 8 * sigma * r * R0 = 0 ∧
        rhoOne_boundaryG_signedRayTerminalResidual68 sigma r
          (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
          (C.coeff 1) (C.coeff 2) (F.coeff 2) (G.coeff (-2)) = 0))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linearRefined68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (S : RhoOneAlignedSquareGNegTwoSignedRayTerminal68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearRefined68 T := by
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
  have Sc := S
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayTerminal68] at Sc
  rcases Sc with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf,
    hfactor, hterminal⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearRefined68]
  refine ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, ?_⟩
  rcases hfactor with hlinear | hqr
  · left
    refine ⟨hlinear, ?_, ?_⟩
    · exact rhoOne_boundaryG_signedRay_linearFactor_b3_zero68
        sigma r
        ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
        ((ratFuncAtHahn46 T.root T.source.B).coeff 3)
        ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
        hsigma hr0 hgneg hray hrf hlinear hi4one
    · exact rhoOne_boundaryG_signedRay_linearFactor_terminal_reduce68
        sigma r
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
        ((ratFuncAtHahn46 T.root T.source.A).coeff 0)
        ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
        ((ratFuncAtHahn46 T.root T.source.B).coeff 4)
        ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
        ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
        hsigma hlinear hterminal
  · exact Or.inr ⟨hqr, hterminal⟩

/-- Source-facing refinement with the coordinate and nonsingular siblings
preserved exactly. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        RhoOneAlignedSquareGNegTwoSignedRayLinearRefined68 T) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_terminal_selector68
      hp hH hp6 hp5 hp4 R with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · exact Or.inr (Or.inl ⟨hsigned.1,
      T.rhoOne_boundaryG_signedRay_linearRefined68 hsigned.1 hsigned.2⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearFactor68

end Max11DegreeRoutes
