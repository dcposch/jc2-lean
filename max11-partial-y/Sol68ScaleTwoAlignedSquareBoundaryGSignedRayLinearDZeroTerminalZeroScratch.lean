import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI4EightCrossScratch

/-! # Exact source terminal coefficient zero on the frozen `K/M` cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_terminalZeroLeft68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  (rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon)
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
    (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
    (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))
    (ratFuncAtHahn46 T.root (Differential.deriv B))
    (ratFuncAtHahn46 T.root (Differential.deriv C))
    (ratFuncAtHahn46 T.root (Differential.deriv F))
    (ratFuncAtHahn46 T.root (Differential.deriv G))).coeff 0

def rhoOne_boundaryG_terminalZeroRight68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  (ratFuncAtHahn46 T.root
    (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff 0

def rhoOne_boundaryG_terminalZeroSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  rhoOne_boundaryG_terminalZeroLeft68 T -
    rhoOne_boundaryG_terminalZeroRight68 T

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_terminalZeroSourceRow68 T = 0 := by
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
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (Polynomial.C x)
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
      T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  rw [hbeta, hdelta, hzeta] at hlow
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) A B C F G
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR : rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G
      (ratFuncDerivation68 A) (ratFuncDerivation68 B)
      (ratFuncDerivation68 C) (ratFuncDerivation68 F)
      (ratFuncDerivation68 G) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hsparseH := congrArg (ratFuncAtHahn46 T.root) hsparseR
  have hsparseH' :
      rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.epsilon)
        (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
        (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
        (ratFuncAtHahn46 T.root G)
        (ratFuncAtHahn46 T.root (Differential.deriv A))
        (ratFuncAtHahn46 T.root (Differential.deriv B))
        (ratFuncAtHahn46 T.root (Differential.deriv C))
        (ratFuncAtHahn46 T.root (Differential.deriv F))
        (ratFuncAtHahn46 T.root (Differential.deriv G)) =
      ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow,
      ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one]
      using hsparseH
  have hcoeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (0 : ℚ)) hsparseH'
  dsimp only [rhoOne_boundaryG_terminalZeroSourceRow68,
    rhoOne_boundaryG_terminalZeroLeft68, rhoOne_boundaryG_terminalZeroRight68]
  linear_combination hcoeff

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68 T sigma r ∧
  rhoOne_boundaryG_terminalZeroSourceRow68 T = 0 ∧
  ((M = 0 ∧ rhoOne_boundaryG_terminalZeroLeft68 T =
      rhoOne_boundaryG_terminalZeroRight68 T) ∨
   (M ≠ 0 ∧ rhoOne_boundaryG_terminalZeroLeft68 T =
      rhoOne_boundaryG_terminalZeroRight68 T))

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4EightCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4EightCross68 T ∧
  rhoOne_boundaryG_terminalZeroSourceRow68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4EightCross68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZero68 T := by
  have hrow := T.rhoOne_boundaryG_terminal_zero_source68 Q
  have hlr : rhoOne_boundaryG_terminalZeroLeft68 T =
      rhoOne_boundaryG_terminalZeroRight68 T := by
    dsimp only [rhoOne_boundaryG_terminalZeroSourceRow68] at hrow
    linear_combination hrow
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4EightCross68] at Rc
  rcases Rc with ⟨Rold, hi4eight, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroCells68]
    intro hD
    have hold := hcellsOld hD
    have hsplit := hold.2
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68
        T sigma r := by
      have hc := hsplit
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4EightMSplit68] at hc
      rcases hc.2.2 with hm | hm
      · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68]
        exact ⟨hsplit, hrow, Or.inl ⟨hm.1, hlr⟩⟩
      · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68]
        exact ⟨hsplit, hrow, Or.inr ⟨hm.1, hlr⟩⟩
    exact ⟨hcellsOld, hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZero68]
  exact ⟨R, hrow, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZero68

end Max11DegreeRoutes
