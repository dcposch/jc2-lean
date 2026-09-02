import Sol68ScaleTwoAlignedSquareTerminalGRaysTerminalMinusFourScratch

/-! # Source deletion of both nonzero quadratic rays -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGRaysElimination68

variable {k : Type*} [Field k] [CharZero k]

local instance terminalGRaysEliminationLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

theorem rhoOneDoubleZero_gRay_terminal_of_signed68
    (sigma r b s f g : k) (hsigma : sigma ^ 2 = 1)
    (hray : 3 * s = 2 * sigma * r * b)
    (hlinear : r * f + 3 * sigma * g = 0) :
    s * f + 2 * b * g = 0 := by
  have hsigma0 : sigma ≠ 0 := by
    intro hs
    subst sigma
    norm_num at hsigma
  have hmul : 3 * sigma * (s * f + 2 * b * g) = 0 := by
    calc
      3 * sigma * (s * f + 2 * b * g) =
          2 * b * (r * f + 3 * sigma * g) := by
        linear_combination sigma * f * hray + 2 * r * b * f * hsigma
      _ = 0 := by rw [hlinear]; ring
  exact (mul_eq_zero.mp hmul).resolve_left
    (mul_ne_zero (by norm_num) hsigma0)

theorem rhoOneDoubleZero_gRay_i4one_of_signed68
    (sigma r b s f g b2 g0 c1 f1 epsilon : k)
    (hsigma : sigma ^ 2 = 1)
    (hray : 3 * s = 2 * sigma * r * b)
    (hlinear : r * f + 3 * sigma * g = 0)
    (hsigned : 12 * b * g0 - 4 * sigma * r * b2 * f +
      4 * sigma * r * b * f1 + 12 * c1 * f + 9 * epsilon * b = 0) :
    4 * (b * g0 + b2 * g) + 2 * (s * f1 + 2 * c1 * f) +
      3 * epsilon * b = 0 := by
  linear_combination (1 / 3 : k) *
    (hsigned + 4 * b2 * sigma * hlinear + 2 * f1 * hray -
      12 * b2 * g * hsigma)

/-- Literal source terminal `-4` contradiction for either signed ray. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gRay_terminal_negFour_impossible
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hGne : (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) ≠ 0)
    (sigma r : k) (hsigma : sigma ^ 2 = 1)
    (hray : 3 * (2 * (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 +
        3 * T.source.gamma) =
      2 * sigma * r * (ratFuncAtHahn46 T.root T.source.B).coeff 1)
    (hlinear : r * (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0 +
      3 * sigma * (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) = 0)
    (hi4one : 4 * ((ratFuncAtHahn46 T.root T.source.B).coeff 1 *
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
        (ratFuncAtHahn46 T.root T.source.B).coeff 2 *
          (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1)) +
      2 * ((2 * (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 +
          3 * T.source.gamma) *
            (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 1 +
        2 * (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 1 *
            (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 0) +
      3 * T.source.epsilon *
        (ratFuncAtHahn46 T.root T.source.B).coeff 1 = 0)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) : False := by
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * AR at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
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
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR, AR, C0R]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR, AR, BR, DR]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR, AR, C0R, E0R]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) AR BR CR FR GR
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR :
      rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) AR BR CR FR GR
        (ratFuncDerivation68 AR) (ratFuncDerivation68 BR)
        (ratFuncDerivation68 CR) (ratFuncDerivation68 FR)
        (ratFuncDerivation68 GR) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root AR).orderTop := by
    simpa only [AR] using hbounds.1
  have hCRmap : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [CR, C0R, AR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [FR, DR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [ER, E0R, AR, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGRmap : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [GR, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hERmap, hCRmap, map_mul, ratFuncAtHahn46_C]
  have hBR : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root CR).orderTop := by
    rw [hCRmap]; exact hC
  have hFR : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root FR).orderTop := by
    rw [hFRmap]; exact hF
  have hGR : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop := by rw [hGRmap]; exact hG
  have hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).orderTop := by
    dsimp only [AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAcoH :
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ) =
        (-2 : k) * (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) := by
    dsimp only [AR]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
  have hdB : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv BR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root BR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBR)
  have hdC : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv CR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root CR hCR
  have hdF : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv FR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR hFR
  have hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 GR T.scale_order hGR
  let AL : LaurentSeries k := ratFuncAtLaurent46 T.root AR
  let BL : LaurentSeries k := ratFuncAtLaurent46 T.root BR
  let CL : LaurentSeries k := ratFuncAtLaurent46 T.root CR
  let FL : LaurentSeries k := ratFuncAtLaurent46 T.root FR
  let GSL : LaurentSeries k := ratFuncAtLaurent46 T.root GR
  let dAL : LaurentSeries k := ratFuncAtLaurent46 T.root (Differential.deriv AR)
  let dBL : LaurentSeries k := ratFuncAtLaurent46 T.root (Differential.deriv BR)
  let dCL : LaurentSeries k := ratFuncAtLaurent46 T.root (Differential.deriv CR)
  let dFL : LaurentSeries k := ratFuncAtLaurent46 T.root (Differential.deriv FR)
  let dGSL : LaurentSeries k := ratFuncAtLaurent46 T.root (Differential.deriv GR)
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root AR (-2) hAH
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root BR 1 hBR
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root CR 0 hCR
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root FR 0 hFR
  have hGSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root GR (-1) hGR
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68
    T.root (Differential.deriv AR) (-3) hdA
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68
    T.root (Differential.deriv BR) 0 hdB
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68
    T.root (Differential.deriv CR) 0 hdC
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68
    T.root (Differential.deriv FR) 0 hdF
  have hdGSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68
    T.root (Differential.deriv GR) (-2) hdG
  have hdAcoL : dAL.coeff (-3 : ℤ) = (-2 : k) * AL.coeff (-2 : ℤ) := by
    have hda := ratFuncAtHahn46_coeff_int68 T.root (Differential.deriv AR) (-3)
    have ha := ratFuncAtHahn46_coeff_int68 T.root AR (-2)
    norm_num at hda ha
    dsimp only [dAL, AL]
    rw [← hda, ← ha]
    exact hdAcoH
  have hcoeff := rhoOneMainTangentTerminal_coeff_negFour_gRay68
    T.source.gamma T.source.epsilon AL BL CL FL GSL dAL dBL dCL dFL dGSL
    hAL hBL hCL hFL hGSL hdAL hdBL hdCL hdFL hdGSL hdAcoL
  have hsparseL := congrArg (ratFuncAtLaurent46 T.root) hsparseR
  have hsparseL' :
      rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.epsilon) AL BL CL FL GSL
        dAL dBL dCL dFL dGSL =
      ratFuncAtLaurent46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, AL, BL, CL, FL, GSL, dAL, dBL, dCL, dFL,
      dGSL,
      map_add, map_mul, map_pow, ratFuncAtLaurent46_C68, map_div₀,
      map_neg, map_ofNat, map_one] using hsparseL
  have hterminalH : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).orderTop := by
    rw [T.terminal_order]
  have hrightOrder := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) (-1) hterminalH
  have hright : (ratFuncAtLaurent46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-4 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hrightOrder)
  have hleft : (rhoOneMainTangentTerminal68
      (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
      AL BL CL FL GSL dAL dBL dCL dFL dGSL).coeff (-4 : ℤ) = 0 := by
    rw [hsparseL']
    exact hright
  have hminus4 := hcoeff.symm.trans hleft
  have hA2 := ratFuncAtHahn46_coeff_int68 T.root AR (-2)
  have hA1 := ratFuncAtHahn46_coeff_int68 T.root AR (-1)
  have hdA2 := ratFuncAtHahn46_coeff_int68 T.root (Differential.deriv AR) (-2)
  have hB1 := ratFuncAtHahn46_coeff_int68 T.root BR 1
  have hB2 := ratFuncAtHahn46_coeff_int68 T.root BR 2
  have hC0 := ratFuncAtHahn46_coeff_int68 T.root CR 0
  have hC1 := ratFuncAtHahn46_coeff_int68 T.root CR 1
  have hF0 := ratFuncAtHahn46_coeff_int68 T.root FR 0
  have hF1 := ratFuncAtHahn46_coeff_int68 T.root FR 1
  have hGm1 := ratFuncAtHahn46_coeff_int68 T.root GR (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 T.root GR 0
  norm_num at hA2 hA1 hdA2 hB1 hB2 hC0 hC1 hF0 hF1 hGm1 hG0
  dsimp only [AL, BL, CL, FL, GSL, dAL] at hminus4
  rw [← hA2, ← hA1, ← hdA2, ← hB1, ← hB2, ← hC0, ← hC1,
    ← hF0, ← hF1, ← hGm1, ← hG0] at hminus4
  rw [hCRmap, hFRmap, hGRmap] at hminus4
  have hterminal := rhoOneDoubleZero_gRay_terminal_of_signed68
    sigma r
    ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
    (2 * (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 + 3 * T.source.gamma)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    hsigma hray hlinear
  apply rhoOneDoubleZero_gRay_terminal_negFour_impossible68
    sigma r
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1))
    ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-2))
    ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 0)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    T.source.gamma T.source.epsilon
  · simpa only [AR] using P.2.2.1
  · exact hGne
  · exact hsigma
  · exact hray
  · exact hlinear
  · exact hterminal
  · exact hi4one
  · simpa only [AR] using hminus4

/-- With both nonzero rays deleted, only the already-developed boundary cap
or the independently active `G[-1]=0` selector remains. -/
def RhoOneDoubleZeroTerminalGRaysEliminatedResidual68
    (root j gamma epsilon : k)
    (h A0 B0 C00 D0 : k[X])
    (hR AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  (RhoOneDoubleZeroTerminalGBoundaryCapKSourceOrderResidual68
      root j gamma epsilon h A0 B0 C00 D0 hR AR BR CR FR GR A B C F G ∧
    B.coeff 1 = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0 ∧
    B.coeff 2 * G.coeff (-1) + C.coeff 1 * F.coeff 0 = 0) ∨
  (G.coeff (-1) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
    (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 gamma B C F ∨
     RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 gamma B C F))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGRaysEliminatedResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    let A0 := localClearedA68RhoOne g u
    let B0 := localClearedB68RhoOne g u (p.coeff 3)
    let C00 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
      (p.coeff 1)
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGRaysEliminatedResidual68
      T.root j T.source.gamma T.source.epsilon h0 A0 B0 C00 D0
      (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G := by
  dsimp only [RhoOneDoubleZeroTerminalGRaysEliminatedResidual68]
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGRaysSecondJetResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprev with ⟨hcap, _, hpacket⟩ | hzero
  · rcases hpacket with ⟨⟨hb, hS⟩, hboundary⟩ | hray
    · exact Or.inl ⟨hcap, hb, hS, hboundary⟩
    · rcases hray with ⟨hb, hS, r, sigma, hr0, hr2, hsigma, hray,
        hlinear, hi4one, hi4two⟩
      have hselector := T.rhoOne_exceptional_doubleZero_refined_gZero
        P hB hC hF hG hbeta hdelta hzeta
      dsimp only at hselector
      rcases hselector with ⟨_, _, _, _, _, _, hsplit⟩
      rcases hsplit with hGne | hzero
      · have hi4raw := rhoOneDoubleZero_gRay_i4one_of_signed68
          sigma r
          ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
          (2 * (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 +
              3 * T.source.gamma)
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
          ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
          T.source.epsilon hsigma hray hlinear hi4one
        exact (T.rhoOne_exceptional_doubleZero_gRay_terminal_negFour_impossible
          hp hH hp6 hp5 hp4 P hB hC hF hG hGne sigma r hsigma hray
          hlinear hi4raw hbeta hdelta hzeta).elim
      · rcases hzero with ⟨hGzero, hG0, _⟩
        have hres :=
          T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
            hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
        dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
        rcases hres with hbad | ⟨_, _, htail⟩
        · exact (hbad hGzero).elim
        · exact Or.inr ⟨hGzero, hG0, htail⟩
  · exact Or.inr hzero

end AlignedSquareTerminalGRaysElimination68

end Max11DegreeRoutes
