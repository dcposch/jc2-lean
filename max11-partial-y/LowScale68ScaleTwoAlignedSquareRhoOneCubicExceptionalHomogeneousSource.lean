import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalHomogeneousNext

/-! # Source assembly for the homogeneous exceptional compatibility -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalHomogeneousSource68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalHomogeneousSourceHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The abstract rational-function compatibility instantiated on the actual
five source coordinates and their main-tangent defects. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_homogeneous_compatibility
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hmain :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) = 3 * D.coeff (-4 : ℚ) ∧
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ))
    (hb :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (-2 : ℚ) = 0)
    (hc :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0)
    (hbeta : T.source.beta = 0)
    (hdisc :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let F := rhoOneTangentDDefectHahn68 A B D
      let G := rhoOneTangentEDefectHahn68 A C ER
      rhoOneZeroLCubicExceptionalDiscriminant68
        (A.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ))
        (G.coeff (-4 : ℚ)) = 0)
    (hdelta : T.source.delta = 0)
    (hdisc1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let C := rhoOneCDefectHahn68 A C0
      rhoOneZeroLCubicExceptionalSecondDiscriminant68
        (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
        (C.coeff (-2 : ℚ)) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicExceptionalHomogeneousCompatibility68
      (A.coeff (-2 : ℚ)) (A.coeff (-1 : ℚ))
      (B.coeff (-1 : ℚ)) (B.coeff (0 : ℚ))
      (C.coeff (-2 : ℚ)) (C.coeff (-1 : ℚ))
      (F.coeff (-2 : ℚ)) (G.coeff (-3 : ℚ)) = 0 := by
  have hBC := T.rhoOne_mainTangent_exceptional_orders
    hp hH hp6 hp5 hp4 P hb hc
  have hFG := T.rhoOne_mainTangent_exceptional_discriminant_orders
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  dsimp only at hb hc hBC hFG hdisc1 ⊢
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let C0H := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let E0H := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let FRH := ratFuncAtHahn46 T.root FR
  let GRH := ratFuncAtHahn46 T.root GR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH C0H := by
    dsimp only [CRH, CR, AH, C0H, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH E0H := by
    dsimp only [ERH, ER, AH, E0H, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : FRH = rhoOneTangentDDefectHahn68 AH BH DH := by
    dsimp only [FRH, FR, AH, BH, DH, AR, BR, DR,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤ AH.orderTop := by
    simpa only [AH, AR] using hbounds.1
  have hBH : (↑(-1 : ℚ) : WithTop ℚ) ≤ BH.orderTop := by
    simpa only [BH, BR] using hBC.1
  have hCRH : (↑(-2 : ℚ) : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    exact hBC.2
  have hFRH : (↑(-2 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    exact hFG.1
  have hGRH : (↑(-3 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap, hCRmap, hERmap]
    exact hFG.2
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta] at hi4 hi3
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR, AR, C0R]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR, AR, BR, DR]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR, AR, C0R, E0R]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hi4T :
      firstIntegralFour68 0 AR BR (AR ^ 2 / 3 + CR) (AR * BR / 3 + FR)
        (AR ^ 3 / 27 + AR * CR / 3 + GR) (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta) =
          RatFunc.C i4 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R,
      RatFunc.algebraMap_eq_C, map_zero] using hi4
  have hi3T :
      firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR) (AR * BR / 3 + FR)
        (AR ^ 3 / 27 + AR * CR / 3 + GR) (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta) =
          RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R,
      RatFunc.algebraMap_eq_C, map_zero] using hi3
  have hdiscR : rhoOneZeroLCubicExceptionalSecondDiscriminant68
      (AH.coeff (-2 : ℚ)) (BH.coeff (-1 : ℚ))
      (CRH.coeff (-2 : ℚ)) = 0 := by
    rw [hCRmap]
    simpa only [AH, BH, C0H, AR, BR, C0R] using hdisc1
  have hcompat := ratFunc_exceptional_homogeneous_compatibility68
    T.root AR BR CR FR GR T.source.gamma T.source.epsilon T.source.zeta
      i4 i3 hAH hBH hCRH hFRH hGRH hi4T hi3T hdiscR
  have hA2 := ratFuncAtHahn46_coeff_int68 T.root AR (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 T.root AR (-1)
  have hB1 := ratFuncAtHahn46_coeff_int68 T.root BR (-1)
  have hB0 := ratFuncAtHahn46_coeff_int68 T.root BR 0
  have hC2 := ratFuncAtHahn46_coeff_int68 T.root CR (-2)
  have hC1 := ratFuncAtHahn46_coeff_int68 T.root CR (-1)
  have hF2 := ratFuncAtHahn46_coeff_int68 T.root FR (-2)
  have hG3 := ratFuncAtHahn46_coeff_int68 T.root GR (-3)
  norm_num at hA2 hA1 hB1 hB0 hC2 hC1 hF2 hG3
  rw [← hA2, ← hA1, ← hB1, ← hB0, ← hC2, ← hC1,
    ← hF2, ← hG3] at hcompat
  have hCRmap' : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root C0R) := by
    simpa only [CRH, AH, C0H] using hCRmap
  have hERmap' : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root E0R) := by
    simpa only [ERH, AH, E0H] using hERmap
  have hFRmap' : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root DR) := by
    simpa only [FRH, AH, BH, DH] using hFRmap
  have hGRmap' : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root C0R))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root E0R)) := by
    simpa only [GRH, AH, CRH, ERH, hCRmap', hERmap'] using hGRmap
  rw [hCRmap', hFRmap', hGRmap'] at hcompat
  simpa only [AH, BH, C0H, DH, E0H, AR, BR, C0R, DR, E0R] using hcompat

def rhoOneZeroLCubicExceptionalHomogeneousReduced68
    (a a1 b1 b2 c1 c2 f1 : k) : k :=
  4 * b1 ^ 3 * c1 + 12 * a * b1 * b2 * f1 +
    6 * a1 * b1 ^ 2 * f1 + 36 * c1 * c2 * f1 - 9 * b1 * f1 ^ 2

/-- Combining the old homogeneous I4 equation, the singular second
determinant, and the new compatibility gives an exact two-component packet:
either both old boundary coefficients vanish, or a smaller seven-variable
polynomial vanishes. -/
theorem rhoOneZeroLCubicExceptional_homogeneous_singular_reduction68
    (a a1 b1 b2 c1 c2 f1 g1 : k) (ha : a ≠ 0)
    (h4 : rhoOneZeroLCubicExceptionalDegenerateFour68
      0 a b1 c1 f1 g1 = 0)
    (hdisc : rhoOneZeroLCubicExceptionalSecondDiscriminant68 a b1 c1 = 0)
    (hcompat : rhoOneZeroLCubicExceptionalHomogeneousCompatibility68
      a a1 b1 b2 c1 c2 f1 g1 = 0) :
    (b1 = 0 ∧ c1 = 0) ∨
      (c1 ≠ 0 ∧ rhoOneZeroLCubicExceptionalHomogeneousReduced68
        a a1 b1 b2 c1 c2 f1 = 0) := by
  have hE : b1 * g1 + c1 * f1 = 0 := by
    simp only [rhoOneZeroLCubicExceptionalDegenerateFour68, zero_mul,
      add_zero] at h4
    linear_combination (3 / 8 : k) * h4
  have hprod : c1 * rhoOneZeroLCubicExceptionalHomogeneousReduced68
      a a1 b1 b2 c1 c2 f1 = 0 := by
    simp only [rhoOneZeroLCubicExceptionalHomogeneousReduced68]
    simp only [rhoOneZeroLCubicExceptionalHomogeneousCompatibility68]
      at hcompat
    simp only [rhoOneZeroLCubicExceptionalSecondDiscriminant68] at hdisc
    linear_combination
      (-b1 / 3 : k) * hcompat + 6 * a * b1 * b2 * hE +
        18 * c1 * c2 * hE - (2 / 3 : k) * b1 ^ 3 * hdisc +
        6 * c2 * f1 * hdisc
  by_cases hc1 : c1 = 0
  · left
    refine ⟨?_, hc1⟩
    have hdisc' : a * b1 ^ 2 + 3 * c1 ^ 2 = 0 := by
      simpa only [rhoOneZeroLCubicExceptionalSecondDiscriminant68] using hdisc
    rw [hc1] at hdisc'
    norm_num at hdisc'
    exact hdisc'.resolve_left ha
  · right
    exact ⟨hc1, (mul_eq_zero.mp hprod).resolve_left hc1⟩

end AlignedSquareRhoOneCubicExceptionalHomogeneousSource68

end Max11DegreeRoutes
