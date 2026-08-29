import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedGZero

/-! # The `F`-gain subbox after the second `G` gain -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedGZeroFNext68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalDoubleZeroRefinedGZeroFNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def rhoOneZeroLCubicDoubleZeroGZeroFNextFour68
    (gamma epsilon b c f g : k) : k :=
  4 * b * g + 2 * f * (2 * c + 3 * gamma) + 3 * epsilon * b

/-- In the `F`-gain box the constant coefficient of `I₄` vanishes, and its
coefficient at exponent one is the displayed sparse face. -/
theorem firstIntegral_mainTangent_doubleZero_gZero_fNext_four68
    (gamma epsilon : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C (0 : k))).coeff (0 : ℚ) = 0 ∧
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C (0 : k))).coeff (1 : ℚ) =
        (2 / 3 : k) * rhoOneZeroLCubicDoubleZeroGZeroFNextFour68
          gamma epsilon (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
          (F.coeff (1 : ℚ)) (G.coeff (0 : ℚ)) := by
  have hz (r : ℚ) (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : r < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5 n1 n2 n3 n4 n5).coeff r = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 r h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have hdec := firstIntegralFour_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C (0 : k))
      A B C F G
  have hdecH :
      firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C (0 : k))
          (HahnSeries.C epsilon) (HahnSeries.C (0 : k)) =
        firstIntegralFourMainTangentTopHahn68 0 A B C F G +
          firstIntegralFourMainTangentLowerHahn68 0 gamma 0 epsilon 0
            A B C F G := by
    rw [hdec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68,
      firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68, weightedMonomial68,
      map_mul, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h0t1 := hz 0 (-8 / 27 : k) B A C F G 3 0 0 0 0
    1 (-2) 0 1 0 hB hA hC hF hG (by norm_num)
  have h0t3 := hz 0 (8 / 3 : k) B G A C F 1 1 0 0 0
    1 0 (-2) 0 1 hB hG hA hC hF (by norm_num)
  have h0t4 := hz 0 (8 / 3 : k) C F A B G 1 1 0 0 0
    0 1 (-2) 1 0 hC hF hA hB hG (by norm_num)
  have h0l6 := hz 0 (4 * gamma) F A B C G 1 0 0 0 0
    1 (-2) 1 0 0 hF hA hB hC hG (by norm_num)
  have h0l8 := hz 0 (2 * epsilon) B A C F G 1 0 0 0 0
    1 (-2) 0 1 0 hB hA hC hF hG (by norm_num)
  have h1t1 := hz 1 (-8 / 27 : k) B A C F G 3 0 0 0 0
    1 (-2) 0 1 0 hB hA hC hF hG (by norm_num)
  have h1t3 := lead (8 / 3 : k) B G A C F 1 1 0 0 0
    1 0 (-2) 0 1 hB hG hA hC hF
  have h1t4 := lead (8 / 3 : k) C F A B G 1 1 0 0 0
    0 1 (-2) 1 0 hC hF hA hB hG
  have h1l6 := lead (4 * gamma) F A B C G 1 0 0 0 0
    1 (-2) 1 0 0 hF hA hB hC hG
  have h1l8 := lead (2 * epsilon) B A C F G 1 0 0 0 0
    1 (-2) 0 1 0 hB hA hC hF hG
  norm_num at h1t3 h1t4 h1l6 h1l8
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  constructor
  · rw [hdecH]
    simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68]
    rw [h0t1, h0t3, h0t4, h0l6, h0l8]
    simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
      HahnSeries.coeff_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero, add_zero]
  · rw [hdecH]
    simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68]
    rw [h1t1, h1t3, h1t4, h1l6, h1l8]
    simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
      HahnSeries.coeff_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero, add_zero,
      rhoOneZeroLCubicDoubleZeroGZeroFNextFour68]
    ring

/-- Rational transport: the ground-field `I₄` load vanishes and the next
positive coefficient gives a load-free face. -/
theorem ratFunc_doubleZero_gZero_fNext_four68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon i4 : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C gamma) (RatFunc.C (0 : k))
      (RatFunc.C epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4) :
    i4 = 0 ∧
    rhoOneZeroLCubicDoubleZeroGZeroFNextFour68 gamma epsilon
      ((ratFuncAtHahn46 root B).coeff (1 : ℚ))
      ((ratFuncAtHahn46 root C).coeff (0 : ℚ))
      ((ratFuncAtHahn46 root F).coeff (1 : ℚ))
      ((ratFuncAtHahn46 root G).coeff (0 : ℚ)) = 0 := by
  have hi4H := congrArg (ratFuncAtHahn46 root) hi4
  have hi4H' :
      firstIntegralFour68 0 (ratFuncAtHahn46 root A)
          (ratFuncAtHahn46 root B)
          ((ratFuncAtHahn46 root A) ^ 2 / 3 + ratFuncAtHahn46 root C)
          ((ratFuncAtHahn46 root A) * (ratFuncAtHahn46 root B) / 3 +
            ratFuncAtHahn46 root F)
          ((ratFuncAtHahn46 root A) ^ 3 / 27 +
            (ratFuncAtHahn46 root A) * (ratFuncAtHahn46 root C) / 3 +
              ratFuncAtHahn46 root G)
          (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
          (HahnSeries.C (0 : k)) (HahnSeries.C epsilon)
          (HahnSeries.C (0 : k)) = HahnSeries.C i4 := by
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtHahn46_C] using hi4H
  have hface := firstIntegral_mainTangent_doubleZero_gZero_fNext_four68
    gamma epsilon (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) hA hB hC hF hG
  have h0coeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (0 : ℚ)) hi4H'
  have h1coeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ)) hi4H'
  have h0const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (0 : ℚ) = i4 := by
    simp [HahnSeries.C_apply]
  have h1const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (1 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hface.1, h0const] at h0coeff
  rw [hface.2, h1const] at h1coeff
  constructor
  · exact h0coeff.symm
  · linear_combination (3 / 2 : k) * h1coeff

/-- On `B[1] = 0`, the load-free face splits into another `F` gain or the
affine residual. -/
theorem rhoOneZeroLCubicDoubleZero_gZero_fNext_split68
    (gamma epsilon b c f g : k)
    (hface : rhoOneZeroLCubicDoubleZeroGZeroFNextFour68
      gamma epsilon b c f g = 0) (hb : b = 0) :
    f = 0 ∨ 2 * c + 3 * gamma = 0 := by
  simp only [rhoOneZeroLCubicDoubleZeroGZeroFNextFour68] at hface
  subst b
  norm_num at hface
  exact hface

/-- Source-facing load vanishing, next face, and order-gain split. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gZero_fNext
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      let B := ratFuncAtHahn46 T.root T.source.B
      (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (0 : WithTop ℚ) ≤ (rhoOneCDefectHahn68 A C0).orderTop)
    (hF :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (↑(1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68 A B D).orderTop)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      (0 : WithTop ℚ) ≤ (rhoOneTangentEDefectHahn68 A C ER).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
    (0 : WithTop ℚ) ≤ C.orderTop ∧
    (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
    (0 : WithTop ℚ) ≤ G.orderTop ∧
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C (0 : k) ∧
    rhoOneZeroLCubicDoubleZeroGZeroFNextFour68 T.source.gamma
      T.source.epsilon (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
      (F.coeff (1 : ℚ)) (G.coeff (0 : ℚ)) = 0 ∧
    (B.coeff (1 : ℚ) ≠ 0 ∨
      (B.coeff (1 : ℚ) = 0 ∧
       (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
       (((↑(2 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧ F.coeff (1 : ℚ) = 0) ∨
        2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0))) := by
  dsimp only at hB hC hF hG ⊢
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
  have hGRmap' : GRH = rhoOneTangentEDefectHahn68 AH
      (rhoOneCDefectHahn68 AH C0H) (rhoOneEDefectHahn68 AH E0H) := by
    rw [hGRmap, hCRmap, hERmap]
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤ AH.orderTop := by
    simpa only [AH, AR] using hbounds.1
  have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤ BH.orderTop := by
    simpa only [BH, BR] using hB
  have hCRH : (0 : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hC
  have hFRH : (↑(1 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hF
  have hGRH : (0 : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hG
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta, hzeta] at hi4 hi3
  have hi4source :
      firstIntegralFour68 0 T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 := by
    simpa only [RatFunc.algebraMap_eq_C, map_zero] using hi4
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
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R] using hi4source
  have hfaces := ratFunc_doubleZero_gZero_fNext_four68 T.root AR BR CR FR GR
    T.source.gamma T.source.epsilon i4 hAH hBH hCRH hFRH hGRH hi4T
  have hCRraw : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root C0R) := by
    simpa only [CRH, AH, C0H] using hCRmap
  have hERraw : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root E0R) := by
    simpa only [ERH, AH, E0H] using hERmap
  have hFRraw : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root DR) := by
    simpa only [FRH, AH, BH, DH] using hFRmap
  have hGRraw : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root C0R))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root E0R)) := by
    simpa only [GRH, AH, CRH, ERH, hCRraw, hERraw] using hGRmap
  rw [hCRraw, hFRraw, hGRraw] at hfaces
  simp only [AR, BR, C0R, DR, E0R] at hfaces
  have hi4zero :
      firstIntegralFour68 0 T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C (0 : k) := by
    rw [hi4source, hfaces.1]
  refine ⟨hB, hC, hF, hG, hi4zero, hfaces.2, ?_⟩
  by_cases hb1 : (ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ) = 0
  · right
    have hb1z : BH.coeff ((1 : ℤ) : ℚ) = 0 := by
      norm_num
      simpa only [BH, BR] using hb1
    have hB2 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root BR 1 hBH hb1z
    norm_num at hB2
    have hB2out : (↑(2 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop := by
      change (↑((2 : ℤ) : ℚ) : WithTop ℚ) ≤ BH.orderTop
      exact hB2
    refine ⟨hb1, hB2out, ?_⟩
    have hsplit := rhoOneZeroLCubicDoubleZero_gZero_fNext_split68
      T.source.gamma T.source.epsilon
        ((ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ))
        ((rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ))
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff (1 : ℚ))
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (0 : ℚ))
        hfaces.2 hb1
    rcases hsplit with hf1 | hS
    · left
      have hf1z : FRH.coeff ((1 : ℤ) : ℚ) = 0 := by
        norm_num
        rw [hFRmap]
        simpa only [AH, BH, DH, AR, BR, DR] using hf1
      have hF2 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root FR 1 hFRH hf1z
      norm_num at hF2
      have hF2out : (↑(2 : ℚ) : WithTop ℚ) ≤
          (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
        rw [← hFRraw]
        exact hF2
      exact ⟨hF2out, hf1⟩
    · exact Or.inr hS
  · exact Or.inl hb1

end AlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedGZeroFNext68

end Max11DegreeRoutes
