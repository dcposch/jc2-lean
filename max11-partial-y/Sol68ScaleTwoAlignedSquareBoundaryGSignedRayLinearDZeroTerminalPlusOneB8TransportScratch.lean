import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneBaseReductionScratch

/-! # The coefficient-plus-one row is an invertible `B[8]` transport

The literal product expansion has a nonzero `B[8]` slope on the signed-ray
source packet.  Thus this row preserves, rather than contradicts, both old
base-affine cells.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneB8Transport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_terminalPlusOneB8BaseSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalPlusOneB8Base68 T.source.gamma T.source.epsilon
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
    (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
    (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))
    (ratFuncAtHahn46 T.root (Differential.deriv B))
    (ratFuncAtHahn46 T.root (Differential.deriv C))
    (ratFuncAtHahn46 T.root (Differential.deriv F))
    (ratFuncAtHahn46 T.root (Differential.deriv G))

def rhoOne_boundaryG_terminalPlusOneB8SlopeSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalPlusOneB8Slope68
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))

def rhoOne_boundaryG_terminalPlusOneB8Transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T ≠ 0 ∧
  (ratFuncAtHahn46 T.root T.source.B).coeff 8 =
    -rhoOne_boundaryG_terminalPlusOneB8BaseSource68 T /
      rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T

def rhoOne_boundaryG_terminalPlusOneB8AffineCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let CoeffX := rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68 T
  let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T
  let DeltaA := rhoOne_boundaryG_terminalZeroB6DeltaASource68 T
  (CoeffX = 0 -> Const = 0 ->
    CoeffX = 0 ∧ Const = 0 ∧ rhoOne_boundaryG_terminalPlusOneB8Transport68 T) ∧
  (CoeffX ≠ 0 -> Const ≠ 0 -> DeltaA = -Const / CoeffX ->
    CoeffX ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / CoeffX ∧
      rhoOne_boundaryG_terminalPlusOneB8Transport68 T)

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB8Transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68 T ∧
  rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T =
    rhoOne_boundaryG_terminalPlusOneB8BaseSource68 T +
      rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T *
        (ratFuncAtHahn46 T.root T.source.B).coeff 8 ∧
  rhoOne_boundaryG_terminalPlusOneB8Transport68 T ∧
  rhoOne_boundaryG_terminalPlusOneB8AffineCells68 T

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_plus_one_B8_transport68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB8Transport68 T := by
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
    rw [map_sub, map_mul, hEmap, map_mul, ratFuncAtHahn46_C, hCmap]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  have hdAH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv A)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 A T.scale_order hAH
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root F hFH
  have hdGH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 G T.scale_order hGH
  have haff0 := rhoOne_boundaryG_terminalPlusOne_B8_affine68
    T.source.gamma T.source.epsilon
    ((ratFuncAtHahn46 T.root B).coeff 8)
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
    (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
    (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))
    (ratFuncAtHahn46 T.root (Differential.deriv B))
    (ratFuncAtHahn46 T.root (Differential.deriv C))
    (ratFuncAtHahn46 T.root (Differential.deriv F))
    (ratFuncAtHahn46 T.root (Differential.deriv G))
    hAH hBH hCH hFH hdAH hdBH hdFH hdGH
  rw [rhoOne_boundaryG_replaceB8_self68] at haff0
  have haff : rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T =
      rhoOne_boundaryG_terminalPlusOneB8BaseSource68 T +
        rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T *
          (ratFuncAtHahn46 T.root T.source.B).coeff 8 := by
    simpa only [rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68,
      rhoOne_boundaryG_terminalPlusOneB8BaseSource68,
      rhoOne_boundaryG_terminalPlusOneB8SlopeSource68, A, B, C, F, E, G]
      using haff0
  have hdA3 := T.rhoOne_boundaryG_dA_negThree_source68
    hp hH hp6 hp5 hp4 Q
  have hTransport := R.1.1.1.1.1
  rcases hTransport.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hcells⟩
  have ha : (ratFuncAtHahn46 T.root A).coeff (-2) ≠ 0 := by
    intro haz
    have : rCell ^ 2 = 0 := by
      rw [hrCell]
      rw [show (ratFuncAtHahn46 T.root T.source.A).coeff (-2) = 0 by
        simpa only [A] using haz]
      ring
    exact (pow_ne_zero 2 hrCell0) this
  have hlead : (ratFuncAtHahn46 T.root (A * G * Differential.deriv A)).coeff (-7) =
      (ratFuncAtHahn46 T.root A).coeff (-2) *
        (ratFuncAtHahn46 T.root G).coeff (-2) *
          (ratFuncAtHahn46 T.root (Differential.deriv A)).coeff (-3) := by
    let AL := ratFuncAtLaurent46 T.root A
    let GLa := ratFuncAtLaurent46 T.root G
    let dAL := ratFuncAtLaurent46 T.root (Differential.deriv A)
    have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root A (-2) hAH
    have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-2) hGH
    have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
      (Differential.deriv A) (-3) hdAH
    have hL := laurent_coeff_mul_three_lower_terminal68 AL GLa dAL (-2) (-2) (-3)
      hAL hGL hdAL
    norm_num at hL
    have hp := (ratFuncAtHahn46_coeff_int68 T.root
      (A * G * Differential.deriv A) (-7)).symm
    simp only [map_mul] at hp
    norm_num at hp
    have hcsA := ratFuncAtHahn46_coeff_int68 T.root A (-2)
    have hcsG := ratFuncAtHahn46_coeff_int68 T.root G (-2)
    have hcsdA := ratFuncAtHahn46_coeff_int68 T.root
      (Differential.deriv A) (-3)
    norm_num at hcsA hcsG hcsdA
    simp only [map_mul]
    rw [← hp, hL, hcsA, hcsG, hcsdA]
  have hslopeFormula : rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T =
      (-(4 / 27 : k)) * (ratFuncAtHahn46 T.root A).coeff (-2) *
        (ratFuncAtHahn46 T.root G).coeff (-2) *
          (ratFuncAtHahn46 T.root (Differential.deriv A)).coeff (-3) := by
    dsimp only [rhoOne_boundaryG_terminalPlusOneB8SlopeSource68,
      rhoOne_boundaryG_terminalPlusOneB8Slope68]
    rw [← map_mul, ← map_mul, hlead]
    ring
  have hslope : rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T ≠ 0 := by
    rw [hslopeFormula]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) ha
      · simpa only [hGmap] using hgm2
    · rw [show (ratFuncAtHahn46 T.root (Differential.deriv A)).coeff (-3) =
          (-2 : k) * (ratFuncAtHahn46 T.root A).coeff (-2) by
        simpa only [A] using hdA3]
      exact mul_ne_zero (by norm_num) ha
  have hsolve : (ratFuncAtHahn46 T.root T.source.B).coeff 8 =
      -rhoOne_boundaryG_terminalPlusOneB8BaseSource68 T /
        rhoOne_boundaryG_terminalPlusOneB8SlopeSource68 T := by
    apply (eq_div_iff hslope).2
    have hrow := R.1.2
    linear_combination hrow - haff
  have htransport : rhoOne_boundaryG_terminalPlusOneB8Transport68 T :=
    ⟨hslope, hsolve⟩
  refine ⟨R, haff, htransport, ?_⟩
  dsimp only [rhoOne_boundaryG_terminalPlusOneB8AffineCells68]
  constructor
  · intro hcoeff hconst
    exact ⟨hcoeff, hconst, htransport⟩
  · intro hcoeff hconst hdelta
    exact ⟨hcoeff, hconst, hdelta, htransport⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneB8Transport68

end Max11DegreeRoutes
