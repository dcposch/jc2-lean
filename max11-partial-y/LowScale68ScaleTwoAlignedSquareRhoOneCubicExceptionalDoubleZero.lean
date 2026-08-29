import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalHomogeneousSource

/-! # The double-zero exceptional component -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZero68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalDoubleZeroHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The rational-function transport before eliminating the two next faces.
Unlike the compatibility theorem, this retains both equations. -/
theorem ratFunc_exceptional_homogeneous_next_faces68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon zeta i4 i3 : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (RatFunc.C (0 : k))
      (RatFunc.C gamma) (RatFunc.C (0 : k)) (RatFunc.C epsilon)
      (RatFunc.C zeta) = RatFunc.C i4)
    (hi3 : firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (RatFunc.C (0 : k))
      (RatFunc.C gamma) (RatFunc.C (0 : k)) (RatFunc.C epsilon)
      (RatFunc.C zeta) = RatFunc.C i3) :
    let aL := ratFuncAtLaurent46 root A
    let bL := ratFuncAtLaurent46 root B
    let cL := ratFuncAtLaurent46 root C
    let fL := ratFuncAtLaurent46 root F
    let gL := ratFuncAtLaurent46 root G
    rhoOneZeroLCubicExceptionalHomogeneousNextFour68
      (bL.coeff (-1)) (bL.coeff 0) (cL.coeff (-2)) (cL.coeff (-1))
      (fL.coeff (-2)) (fL.coeff (-1)) (gL.coeff (-3)) (gL.coeff (-2)) = 0 ∧
    rhoOneZeroLCubicExceptionalHomogeneousNextThree68
      (aL.coeff (-2)) (aL.coeff (-1)) (bL.coeff (-1)) (bL.coeff 0)
      (cL.coeff (-2)) (cL.coeff (-1)) (fL.coeff (-2)) (fL.coeff (-1))
      (gL.coeff (-3)) (gL.coeff (-2)) = 0 := by
  let aL := ratFuncAtLaurent46 root A
  let bL := ratFuncAtLaurent46 root B
  let cL := ratFuncAtLaurent46 root C
  let fL := ratFuncAtLaurent46 root F
  let gL := ratFuncAtLaurent46 root G
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B (-1) hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C (-2) hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F (-2) hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-3) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi3L := congrArg (ratFuncAtLaurent46 root) hi3
  have hi4L' :
      firstIntegralFour68 0 aL bL (aL ^ 2 / 3 + cL) (aL * bL / 3 + fL)
        (aL ^ 3 / 27 + aL * cL / 3 + gL) (HahnSeries.C (0 : k))
        (HahnSeries.C gamma) (HahnSeries.C (0 : k))
        (HahnSeries.C epsilon) (HahnSeries.C zeta) = HahnSeries.C i4 := by
    dsimp only [aL, bL, cL, fL, gL]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hi4L
  have hi3L' :
      firstIntegralThree68 0 aL bL (aL ^ 2 / 3 + cL) (aL * bL / 3 + fL)
        (aL ^ 3 / 27 + aL * cL / 3 + gL) (HahnSeries.C (0 : k))
        (HahnSeries.C gamma) (HahnSeries.C (0 : k))
        (HahnSeries.C epsilon) (HahnSeries.C zeta) = HahnSeries.C i3 := by
    dsimp only [aL, bL, cL, fL, gL]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hi3L
  have hface := firstIntegral_mainTangent_exceptional_homogeneous_next_laurent68
    gamma epsilon zeta aL bL cL fL gL hAL hBL hCL hFL hGL
  have h4coeff := congrArg (fun X : LaurentSeries k => X.coeff (-3 : ℤ)) hi4L'
  have h3coeff := congrArg (fun X : LaurentSeries k => X.coeff (-4 : ℤ)) hi3L'
  have h4const : (HahnSeries.C i4 : LaurentSeries k).coeff (-3 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : LaurentSeries k).coeff (-4 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hface.1, h4const] at h4coeff
  rw [hface.2, h3const] at h3coeff
  constructor
  · linear_combination (27 / 8 : k) * h4coeff
  · linear_combination (9 / 4 : k) * h3coeff

/-- The two retained faces specialize sharply on `b1 = c1 = 0`. -/
theorem rhoOneZeroLCubicExceptional_doubleZero_next_split68
    (a a1 b2 c2 f1 f2 g1 g2 : k)
    (h4 : rhoOneZeroLCubicExceptionalHomogeneousNextFour68
      0 b2 0 c2 f1 f2 g1 g2 = 0)
    (h3 : rhoOneZeroLCubicExceptionalHomogeneousNextThree68
      a a1 0 b2 0 c2 f1 f2 g1 g2 = 0) :
    b2 * g1 + c2 * f1 = 0 ∧
      (f1 = 0 ∨ 3 * b2 * f1 = 2 * a * b2 ^ 2 + 6 * c2 ^ 2) := by
  simp only [rhoOneZeroLCubicExceptionalHomogeneousNextFour68,
    rhoOneZeroLCubicExceptionalHomogeneousNextThree68] at h4 h3
  constructor
  · linear_combination (1 / 9 : k) * h4
  · have hf : f1 *
        (3 * b2 * f1 - 2 * a * b2 ^ 2 - 6 * c2 ^ 2) = 0 := by
      linear_combination b2 * h3 - (2 / 3 : k) * c2 * h4
    rcases mul_eq_zero.mp hf with hf | hf
    · exact Or.inl hf
    · right
      linear_combination hf

/-- Source-facing next packet on the double-zero component.  In particular,
this does not merely assume two abstract face equations: both are rebuilt
from the actual integrated source identities. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_doubleZero_next
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
    (hb1 :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (-1 : ℚ) = 0)
    (hc1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    B.coeff (0 : ℚ) * G.coeff (-3 : ℚ) +
        C.coeff (-1 : ℚ) * F.coeff (-2 : ℚ) = 0 ∧
      (F.coeff (-2 : ℚ) = 0 ∨
        3 * B.coeff (0 : ℚ) * F.coeff (-2 : ℚ) =
          2 * A.coeff (-2 : ℚ) * B.coeff (0 : ℚ) ^ 2 +
            6 * C.coeff (-1 : ℚ) ^ 2) := by
  have hBC := T.rhoOne_mainTangent_exceptional_orders
    hp hH hp6 hp5 hp4 P hb hc
  have hFG := T.rhoOne_mainTangent_exceptional_discriminant_orders
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  dsimp only at hb hc hBC hFG hb1 hc1 ⊢
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
    simpa only [AR, BR, C0R, DR, E0R, RatFunc.algebraMap_eq_C,
      map_zero] using hi4
  have hi3T :
      firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR) (AR * BR / 3 + FR)
        (AR ^ 3 / 27 + AR * CR / 3 + GR) (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta) =
          RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R, RatFunc.algebraMap_eq_C,
      map_zero] using hi3
  have hfaces := ratFunc_exceptional_homogeneous_next_faces68
    T.root AR BR CR FR GR T.source.gamma T.source.epsilon T.source.zeta
      i4 i3 hAH hBH hCRH hFRH hGRH hi4T hi3T
  dsimp only at hfaces
  have hB1c := ratFuncAtHahn46_coeff_int68 T.root BR (-1)
  have hC2c := ratFuncAtHahn46_coeff_int68 T.root CR (-2)
  norm_num at hB1c hC2c
  have hbL : (ratFuncAtLaurent46 T.root BR).coeff (-1) = 0 := by
    rw [← hB1c]
    simpa only [BH, BR] using hb1
  have hcL : (ratFuncAtLaurent46 T.root CR).coeff (-2) = 0 := by
    rw [← hC2c]
    change CRH.coeff (-2 : ℚ) = 0
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hc1
  rw [hbL, hcL] at hfaces
  have hsplit := rhoOneZeroLCubicExceptional_doubleZero_next_split68
    ((ratFuncAtLaurent46 T.root AR).coeff (-2))
    ((ratFuncAtLaurent46 T.root AR).coeff (-1))
    ((ratFuncAtLaurent46 T.root BR).coeff 0)
    ((ratFuncAtLaurent46 T.root CR).coeff (-1))
    ((ratFuncAtLaurent46 T.root FR).coeff (-2))
    ((ratFuncAtLaurent46 T.root FR).coeff (-1))
    ((ratFuncAtLaurent46 T.root GR).coeff (-3))
    ((ratFuncAtLaurent46 T.root GR).coeff (-2)) hfaces.1 hfaces.2
  have hA2 := ratFuncAtHahn46_coeff_int68 T.root AR (-2)
  have hB0 := ratFuncAtHahn46_coeff_int68 T.root BR 0
  have hC1 := ratFuncAtHahn46_coeff_int68 T.root CR (-1)
  have hF2 := ratFuncAtHahn46_coeff_int68 T.root FR (-2)
  have hG3 := ratFuncAtHahn46_coeff_int68 T.root GR (-3)
  norm_num at hA2 hB0 hC1 hF2 hG3
  rw [← hA2, ← hB0, ← hC1, ← hF2, ← hG3] at hsplit
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
  rw [hCRmap', hFRmap', hGRmap'] at hsplit
  simpa only [AH, BH, C0H, DH, E0H, AR, BR, C0R, DR, E0R] using hsplit

/-- The double zero is also a genuine discrete source descent: `B` and the
cubic defect each gain one full integral order. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_doubleZero_orders
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hb :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (-2 : ℚ) = 0)
    (hc :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0)
    (hb1 :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (-1 : ℚ) = 0)
    (hc1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let C := rhoOneCDefectHahn68 A C0
    ((0 : WithTop ℚ) ≤ B.orderTop) ∧
      ((↑(-1 : ℚ) : WithTop ℚ) ≤ C.orderTop) := by
  have hBC := T.rhoOne_mainTangent_exceptional_orders
    hp hH hp6 hp5 hp4 P hb hc
  dsimp only at hb1 hc1 hBC ⊢
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let C0H := ratFuncAtHahn46 T.root C0R
  let CRH := ratFuncAtHahn46 T.root CR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH C0H := by
    dsimp only [CRH, CR, AH, C0H, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hBbase : (↑(-1 : ℚ) : WithTop ℚ) ≤ BH.orderTop := by
    simpa only [BH, BR] using hBC.1
  have hCbase : (↑(-2 : ℚ) : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    exact hBC.2
  have hBzero : BH.coeff (-1 : ℚ) = 0 := by
    simpa only [BH, BR] using hb1
  have hCzero : CRH.coeff (-2 : ℚ) = 0 := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hc1
  have hBi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root BR (-1) hBbase hBzero
  have hCi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root CR (-2) hCbase hCzero
  norm_num at hBi hCi
  constructor
  · simpa only [BH, BR] using hBi
  · rw [← hCRmap]
    exact hCi

end AlignedSquareRhoOneCubicExceptionalDoubleZero68

end Max11DegreeRoutes
