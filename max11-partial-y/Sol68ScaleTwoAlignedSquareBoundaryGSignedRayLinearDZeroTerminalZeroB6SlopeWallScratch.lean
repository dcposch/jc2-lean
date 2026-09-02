import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeSplitScratch

/-! # The explicit leading-jet wall on the zero terminal slope cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroB6SlopeWall68
    (A G dA : LaurentSeries k) : k :=
  G.coeff (-2) * dA.coeff (-2) -
    2 * A.coeff (-2) * G.coeff (-1) -
    2 * A.coeff (-1) * G.coeff (-2)

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Slope_factor68
    (A G dA : LaurentSeries k)
    (hdA : dA.coeff (-3) = (-2 : k) * A.coeff (-2)) :
    rhoOne_boundaryG_terminalZeroB6Slope68 A G dA =
      (-(4 / 27 : k)) * A.coeff (-2) *
        rhoOne_boundaryG_terminalZeroB6SlopeWall68 A G dA := by
  dsimp only [rhoOne_boundaryG_terminalZeroB6Slope68,
    laurentFourLowerFiveYSlope68,
    rhoOne_boundaryG_terminalZeroB6SlopeWall68]
  norm_num
  rw [hdA]
  ring

def rhoOne_boundaryG_terminalZeroB6SlopeWallSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroB6SlopeWall68
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root G)
    (ratFuncAtLaurent46 T.root (Differential.deriv A))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_B6_slope_factor_source68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_terminalZeroB6SlopeSource68 T =
      (-(4 / 27 : k)) *
        (ratFuncAtLaurent46 T.root T.source.A).coeff (-2) *
          rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T := by
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
  have hdAH :
      (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-3) =
        (-2 : k) * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) := by
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
  have hdAL :
      (ratFuncAtLaurent46 T.root (Differential.deriv T.source.A)).coeff (-3) =
        (-2 : k) * (ratFuncAtLaurent46 T.root T.source.A).coeff (-2) := by
    have hd := ratFuncAtHahn46_coeff_int68 T.root
      (Differential.deriv T.source.A) (-3)
    have ha := ratFuncAtHahn46_coeff_int68 T.root T.source.A (-2)
    norm_num at hd ha
    rw [← hd, ← ha]
    exact hdAH
  have hfactor := rhoOne_boundaryG_terminalZeroB6Slope_factor68
    (ratFuncAtLaurent46 T.root T.source.A)
    (ratFuncAtLaurent46 T.root
      (T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3 -
        RatFunc.C (1 / 3 : k) * T.source.A *
          (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)))
    (ratFuncAtLaurent46 T.root (Differential.deriv T.source.A)) hdAL
  simpa only [rhoOne_boundaryG_terminalZeroB6SlopeSource68,
    rhoOne_boundaryG_terminalZeroB6SlopeWallSource68] using hfactor

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Slope_wall_of_zero68
    (a Slope Wall : k) (ha : a ≠ 0)
    (hfactor : Slope = (-(4 / 27 : k)) * a * Wall)
    (hzero : Slope = 0) : Wall = 0 := by
  have hcoef : (-(4 / 27 : k)) ≠ 0 := by norm_num
  have hp : (-(4 / 27 : k)) * (a * Wall) = 0 := by
    calc
      _ = (-(4 / 27 : k)) * a * Wall := by ring
      _ = Slope := hfactor.symm
      _ = 0 := hzero
  have haw : a * Wall = 0 := (mul_eq_zero.mp hp).resolve_left hcoef
  exact (mul_eq_zero.mp haw).resolve_left ha

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  let J80 := rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0
  let N8 := rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r
  let V0 := rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0
  let G2 := G.coeff 2
  let Base := rhoOne_boundaryG_terminalZeroB6BaseSource68 T
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let Wall := rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T
  rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68 T sigma r ∧
  ((M = 0 ∧
      ((Slope = 0 ∧ Base = 0 ∧ Wall = 0) ∨
       (Slope ≠ 0 ∧ B.coeff 6 = -Base / Slope ∧
        J80 = N8 * Base / Slope ∧ V0 = G2 * Base / Slope))) ∨
   (M ≠ 0 ∧
      ((Slope = 0 ∧ Base = 0 ∧ Wall = 0) ∨
       (Slope ≠ 0 ∧ B.coeff 6 = -Base / Slope ∧
        K0 = M * Base / Slope))))

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68 T ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68 T := by
  have hfactor := T.rhoOne_boundaryG_terminal_zero_B6_slope_factor_source68
    hp hH hp6 hp5 hp4 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68] at Rc
  rcases Rc with ⟨Rold, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have haH : (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ≠ 0 := by
    intro ha
    have hrz : r ^ 2 = 0 := by rw [hr, ha]; ring
    exact (pow_ne_zero 2 hr0) hrz
  have haL : (ratFuncAtLaurent46 T.root T.source.A).coeff (-2) ≠ 0 := by
    have hcs := ratFuncAtHahn46_coeff_int68 T.root T.source.A (-2)
    norm_num at hcs
    rw [← hcs]
    exact haH
  have hwall (hslope : rhoOne_boundaryG_terminalZeroB6SlopeSource68 T = 0) :
      rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T = 0 :=
    rhoOne_boundaryG_terminalZeroB6Slope_wall_of_zero68
      ((ratFuncAtLaurent46 T.root T.source.A).coeff (-2))
      (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
      (rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T)
      haL hfactor hslope
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallCells68]
    intro hD
    have hold := hcellsOld hD
    have hs := hold.2
    have hsc := hs
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68] at hsc
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68
        T sigma r := by
      rcases hsc.2 with hm | hm
      · rcases hm.2 with hz | hn
        · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68]
          exact ⟨hs, Or.inl ⟨hm.1, Or.inl ⟨hz.1, hz.2, hwall hz.1⟩⟩⟩
        · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68]
          exact ⟨hs, Or.inl ⟨hm.1, Or.inr hn⟩⟩
      · rcases hm.2 with hz | hn
        · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68]
          exact ⟨hs, Or.inr ⟨hm.1, Or.inl ⟨hz.1, hz.2, hwall hz.1⟩⟩⟩
        · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeWallMSplit68]
          exact ⟨hs, Or.inr ⟨hm.1, Or.inr hn⟩⟩
    exact ⟨hcellsOld, hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68]
  exact ⟨R, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWall68

end Max11DegreeRoutes
