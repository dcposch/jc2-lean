import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZero

/-! # Next invariant face in the `B`-gain double-zero box -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroBNext68

variable {k : Type*} [Field k] [CharZero k]

/-- When `b₁ = b₂ = c₁ = f₁ = 0`, the retained `I₃(-4)` face is exactly
the product `c₂ g₁`. -/
theorem rhoOneZeroLCubicExceptional_doubleZero_bZero_next68
    (a a1 c2 f2 g1 g2 : k)
    (h3 : rhoOneZeroLCubicExceptionalHomogeneousNextThree68
      a a1 0 0 0 c2 0 f2 g1 g2 = 0) :
    c2 * g1 = 0 := by
  simp only [rhoOneZeroLCubicExceptionalHomogeneousNextThree68] at h3
  linear_combination (1 / 6 : k) * h3

/-- A vanishing boundary coefficient raises the actual cubic defect from
order `-1` to order `0`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_cZero_order_afterB
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hC :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let C := rhoOneCDefectHahn68 A C0
      (↑(-1 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hc :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let C := rhoOneCDefectHahn68 A C0
      C.coeff (-1 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let C := rhoOneCDefectHahn68 A C0
    (0 : WithTop ℚ) ≤ C.orderTop := by
  dsimp only at hC hc ⊢
  let AR : RatFunc k := T.source.A
  let C0R : RatFunc k := T.source.C0
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let AH := ratFuncAtHahn46 T.root AR
  let C0H := ratFuncAtHahn46 T.root C0R
  let CRH := ratFuncAtHahn46 T.root CR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH C0H := by
    dsimp only [CRH, CR, AH, C0H, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hbase : (↑(-1 : ℚ) : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hC
  have hzero : CRH.coeff (-1 : ℚ) = 0 := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hc
  have hi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root CR (-1) hbase hzero
  norm_num at hi
  change (0 : WithTop ℚ) ≤ CRH.orderTop at hi
  rw [hCRmap] at hi
  simpa only [AH, C0H, AR, C0R] using hi

/-- A vanishing boundary coefficient raises the actual tangent `G` defect
from order `-3` to order `-2`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_gZero_order_afterB
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let G := rhoOneTangentEDefectHahn68 A C ER
      (↑(-3 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hg :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let G := rhoOneTangentEDefectHahn68 A C ER
      G.coeff (-3 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let G := rhoOneTangentEDefectHahn68 A C ER
    (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop := by
  dsimp only at hG hg ⊢
  let AR : RatFunc k := T.source.A
  let C0R : RatFunc k := T.source.C0
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let AH := ratFuncAtHahn46 T.root AR
  let C0H := ratFuncAtHahn46 T.root C0R
  let E0H := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let GRH := ratFuncAtHahn46 T.root GR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH C0H := by
    dsimp only [CRH, CR, AH, C0H, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH E0H := by
    dsimp only [ERH, ER, AH, E0H, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap' : GRH = rhoOneTangentEDefectHahn68 AH
      (rhoOneCDefectHahn68 AH C0H) (rhoOneEDefectHahn68 AH E0H) := by
    rw [hGRmap, hCRmap, hERmap]
  have hbase : (↑(-3 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hG
  have hzero : GRH.coeff (-3 : ℚ) = 0 := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hg
  have hi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root GR (-3) hbase hzero
  norm_num at hi
  change (↑(-2 : ℚ) : WithTop ℚ) ≤ GRH.orderTop at hi
  rw [hGRmap'] at hi
  simpa only [AH, C0H, E0H, AR, C0R, E0R] using hi

/-- Source-facing `I₃(-4)` extraction in the improved `ord(B) ≥ 1` box.
It refines that box into an `ord(C) ≥ 0` box or an `ord(G) ≥ -2` box. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_bBox_next
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
      (rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ) = 0)
    (hf1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (rhoOneTangentDDefectHahn68 A B D).coeff (-2 : ℚ) = 0)
    (hb2 :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (0 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let G := rhoOneTangentEDefectHahn68 A C ER
    C.coeff (-1 : ℚ) * G.coeff (-3 : ℚ) = 0 ∧
      (((0 : WithTop ℚ) ≤ C.orderTop ∧ C.coeff (-1 : ℚ) = 0) ∨
       ((↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧ G.coeff (-3 : ℚ) = 0)) := by
  have hBC := T.rhoOne_mainTangent_exceptional_doubleZero_orders
    hp hH hp6 hp5 hp4 P hb hc hb1 hc1
  have hFG := T.rhoOne_mainTangent_exceptional_discriminant_orders
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  dsimp only at hb hc hBC hFG hb1 hc1 hf1 hb2 ⊢
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
    simpa only [BH, BR] using T.rhoOne_mainTangent_exceptional_orders
      hp hH hp6 hp5 hp4 P hb hc |>.1
  have hCRH : (↑(-2 : ℚ) : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using
      (T.rhoOne_mainTangent_exceptional_orders
        hp hH hp6 hp5 hp4 P hb hc).2
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
  have hB0c := ratFuncAtHahn46_coeff_int68 T.root BR 0
  have hC2c := ratFuncAtHahn46_coeff_int68 T.root CR (-2)
  have hC1c := ratFuncAtHahn46_coeff_int68 T.root CR (-1)
  have hF2c := ratFuncAtHahn46_coeff_int68 T.root FR (-2)
  have hG3c := ratFuncAtHahn46_coeff_int68 T.root GR (-3)
  norm_num at hB1c hB0c hC2c hC1c hF2c hG3c
  have hb1L : (ratFuncAtLaurent46 T.root BR).coeff (-1) = 0 := by
    rw [← hB1c]
    simpa only [BH, BR] using hb1
  have hb2L : (ratFuncAtLaurent46 T.root BR).coeff 0 = 0 := by
    rw [← hB0c]
    simpa only [BH, BR] using hb2
  have hc1L : (ratFuncAtLaurent46 T.root CR).coeff (-2) = 0 := by
    rw [← hC2c]
    change CRH.coeff (-2 : ℚ) = 0
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hc1
  have hf1L : (ratFuncAtLaurent46 T.root FR).coeff (-2) = 0 := by
    rw [← hF2c]
    change FRH.coeff (-2 : ℚ) = 0
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hf1
  rw [hb1L, hb2L, hc1L, hf1L] at hfaces
  have hprodL := rhoOneZeroLCubicExceptional_doubleZero_bZero_next68
    ((ratFuncAtLaurent46 T.root AR).coeff (-2))
    ((ratFuncAtLaurent46 T.root AR).coeff (-1))
    ((ratFuncAtLaurent46 T.root CR).coeff (-1))
    ((ratFuncAtLaurent46 T.root FR).coeff (-1))
    ((ratFuncAtLaurent46 T.root GR).coeff (-3))
    ((ratFuncAtLaurent46 T.root GR).coeff (-2)) hfaces.2
  rw [← hC1c, ← hG3c] at hprodL
  have hCRmap' : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root C0R) := by
    simpa only [CRH, AH, C0H] using hCRmap
  have hERmap' : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root E0R) := by
    simpa only [ERH, AH, E0H] using hERmap
  have hGRmap' : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root C0R))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root E0R)) := by
    simpa only [GRH, AH, CRH, ERH, hCRmap', hERmap'] using hGRmap
  rw [hCRmap', hGRmap'] at hprodL
  have hprod :
      (rhoOneCDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff (-1 : ℚ) *
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-3 : ℚ) = 0 := by
    simpa only [AR, C0R, E0R] using hprodL
  constructor
  · exact hprod
  · rcases mul_eq_zero.mp hprod with hc2 | hg1
    · left
      exact ⟨T.rhoOne_exceptional_cZero_order_afterB hBC.2 hc2, hc2⟩
    · right
      exact ⟨T.rhoOne_exceptional_gZero_order_afterB hFG.2 hg1, hg1⟩

end AlignedSquareRhoOneCubicExceptionalDoubleZeroBNext68

end Max11DegreeRoutes
