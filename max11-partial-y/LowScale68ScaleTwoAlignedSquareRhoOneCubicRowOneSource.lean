import LowScale68ScaleTwoAlignedSquareRhoOneCubicRowOneRemainder

/-! # Source transport of the zero-septic cubic lower row one -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicRowOneSource68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicRowOneSourceHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Source transport of the exact weight-eleven lower-row-one face. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_cubicBranch_nextOne_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hnext : RhoOneZeroLCubicNextSourcePacket68 T g u) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    rhoOneZeroLCubicNextOne68 (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
      ((rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ))
      (D.coeff (-4 : ℚ))
      ((rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)) = 0 := by
  dsimp only
  have hbranch := hnext.1
  obtain ⟨cs, t, v, z, hcs, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ :=
    hbranch
  have hv' : v = z ^ 2 / 3 := by
    have h := (div_eq_iff (pow_ne_zero 2 hz)).mp hvcore
    calc
      v = (1 / 3 : k) * z ^ 2 := h
      _ = z ^ 2 / 3 := by ring
  have ht' : t = z ^ 3 / 27 := by
    have h := (div_eq_iff (pow_ne_zero 3 hz)).mp htcore
    calc
      t = (1 / 27 : k) * z ^ 3 := h
      _ = z ^ 3 / 27 := by ring
  have hgval : g.eval T.root = cs * z := by
    rw [hzdef]
    field_simp [hcs]
  have huval : u.eval T.root = cs ^ 2 * v := by
    rw [hv]
    field_simp [hcs]
  have hp3val : (p.coeff 3).eval T.root = cs ^ 3 * t := by
    rw [ht]
    field_simp [hcs]
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let CH := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let EH := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let dAH := ratFuncAtHahn46 T.root (Differential.deriv AR)
  let dBH := ratFuncAtHahn46 T.root (Differential.deriv BR)
  let dCRH := ratFuncAtHahn46 T.root (Differential.deriv CR)
  let dDH := ratFuncAtHahn46 T.root (Differential.deriv DR)
  let dERH := ratFuncAtHahn46 T.root (Differential.deriv ER)
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let E0 := localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  let Cdef0 : k[X] := C0 - C (1 / 3 : k) * A0 ^ 2
  let Edef0 : k[X] := E0 - C (1 / 27 : k) * A0 ^ 3
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  change algebraMap k[X] (RatFunc k) A0 = _ at hAclear
  change algebraMap k[X] (RatFunc k) B0 = _ at hBclear
  change algebraMap k[X] (RatFunc k) C0 = _ at hCclear
  change algebraMap k[X] (RatFunc k) D0 = _ at hDclear
  change algebraMap k[X] (RatFunc k) E0 = _ at hEclear
  have hB0root : B0.eval T.root = 0 := by
    simp [B0, localClearedB68RhoOne, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]
    ring
  have hD0root : D0.eval T.root = 0 := by
    simp [D0, localClearedD68RhoOne, T.root_eq, hgval, huval, hp3val,
      hv', ht']
    field_simp [hcs]
    ring
  have hCdef0root : Cdef0.eval T.root = 0 := by
    simp [Cdef0, C0, A0, localClearedC68RhoOne,
      localClearedA68RhoOne, T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]
    ring
  have hEdef0root : Edef0.eval T.root = 0 := by
    simp [Edef0, E0, A0, localClearedE68RhoOne,
      localClearedA68RhoOne, T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]
    ring
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR, C0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]
    ring
  have hEdefclear : algebraMap k[X] (RatFunc k) Edef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * ER := by
    dsimp only [Edef0, ER, E0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hEclear, hAclear]
    ring
  obtain ⟨cs', hcs', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcseq : cs' = cs := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst cs'
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at hnext
  rcases hnext with ⟨_, ⟨hAord, hBord, hCord, hCdeford, hDord,
    hEord, hEdeford⟩, hAne, htaut, h4, h3, hsplit⟩
  have hCRmap : CRH = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CRH, CR, AH, CH, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH EH := by
    dsimp only [ERH, ER, AH, EH, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hdAord : (↑(-3 : ℚ) : WithTop ℚ) ≤ dAH.orderTop := by
    dsimp only [dAH, AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAco : dAH.coeff (-3 : ℚ) = (-2 : k) * AH.coeff (-2 : ℚ) := by
    dsimp only [dAH, AH, AR]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root cs h0 A0
      T.source.A 2 hcs hsingle hderiv' hAclear using 1 <;> norm_num
  obtain ⟨hdBord, hdBco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 B0 T.source.B 3 (by omega) T.scale_ne_zero T.scale_degree
    T.root_eq hsingle T.scale_order hderiv' hcs hBclear hB0root
  obtain ⟨hdCRord, hdCRco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 Cdef0 CR 4 (by omega) T.scale_ne_zero T.scale_degree
    T.root_eq hsingle T.scale_order hderiv' hcs hCdefclear hCdef0root
  obtain ⟨hdDord, hdDco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 D0 T.source.D 5 (by omega) T.scale_ne_zero T.scale_degree
    T.root_eq hsingle T.scale_order hderiv' hcs hDclear hD0root
  obtain ⟨hdERord, hdERco⟩ := localHahn_deriv_improved_of_cleared_root_zero
    T.root cs h0 Edef0 ER 6 (by omega) T.scale_ne_zero T.scale_degree
    T.root_eq hsingle T.scale_order hderiv' hcs hEdefclear hEdef0root
  norm_num at hdBord hdBco hdCRord hdCRco hdDord hdDco hdERord hdERco
  change (↑(-3 : ℚ) : WithTop ℚ) ≤ dBH.orderTop at hdBord
  change (↑(-4 : ℚ) : WithTop ℚ) ≤ dCRH.orderTop at hdCRord
  change (↑(-5 : ℚ) : WithTop ℚ) ≤ dDH.orderTop at hdDord
  change (↑(-6 : ℚ) : WithTop ℚ) ≤ dERH.orderTop at hdERord
  have hdBco' : dBH.coeff (-3 : ℚ) = (-2 : k) * BH.coeff (-2 : ℚ) := by
    simpa only [dBH, BH, BR, neg_mul] using hdBco
  have hdCRco' : dCRH.coeff (-4 : ℚ) =
      (-3 : k) * CRH.coeff (-3 : ℚ) := by
    simpa only [dCRH, CRH, neg_mul] using hdCRco
  have hdDco' : dDH.coeff (-5 : ℚ) = (-4 : k) * DH.coeff (-4 : ℚ) := by
    simpa only [dDH, DH, DR, neg_mul] using hdDco
  have hdERco' : dERH.coeff (-6 : ℚ) =
      (-5 : k) * ERH.coeff (-5 : ℚ) := by
    simpa only [dERH, ERH, neg_mul] using hdERco
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hdecR := lowerRowOneCubic_decomposition68 (k := k)
    ratFuncDerivation68 AR BR CR DR ER
      (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
      (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta)
      (RatFunc.C T.source.eta)
      (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta)
  dsimp only at hdecR
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR]
    simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  have hErec : AR ^ 3 / 27 + ER = E0R := by
    dsimp only [ER]
    simp only [div_eq_mul_inv]
    rw [show (27 : RatFunc k) = RatFunc.C (27 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 27).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  rw [hCrec, hErec] at hdecR
  simp only [ratFuncDerivation46_apply] at hdecR
  have hdecH := congrArg (ratFuncAtHahn46 T.root) hdecR
  simp only [map_add, map_sub, map_mul, map_ofNat] at hdecH
  have hdecH' :
      let TT := ratFuncAtHahn46 T.root
        (integratedT68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon))
      let U := ratFuncAtHahn46 T.root
        (integratedU68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.zeta))
      let V := ratFuncAtHahn46 T.root
        (integratedV68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.epsilon) (RatFunc.C T.source.eta))
      let dD := ratFuncAtHahn46 T.root (Differential.deriv DR)
      let dE0 := ratFuncAtHahn46 T.root (Differential.deriv E0R)
      let dU := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedU68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.zeta)))
      let dV := ratFuncAtHahn46 T.root (Differential.deriv
        (integratedV68 0 AR BR C0R DR E0R
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
          (RatFunc.C T.source.epsilon) (RatFunc.C T.source.eta)))
      U * dD + 2 * TT * dE0 - 2 * CH * dV - DH * dU =
        lowerRowOneCubicWeightElevenHahn68 AH BH CRH DH ERH
          dAH dBH dCRH dDH dERH +
        lowerRowOneCubicLowerHahn68 T.source.beta T.source.gamma
          T.source.delta T.source.epsilon T.source.zeta
          AH BH CRH DH ERH dAH dBH dCRH dDH dERH := by
    dsimp only
    rw [hdecH]
    simp only [AR, BR, C0R, DR, E0R, AH, BH, CH, DH, CRH, ERH,
      dAH, dBH, dCRH, dDH, dERH, lowerRowOneCubicWeightElevenHahn68,
      lowerRowOneCubicLowerHahn68, lowerRowOneCubicWeightElevenAlg68,
      lowerRowOneCubicLowerAlg68, weightedMonomial68, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      ratFuncAtHahn46_C]
    ring
  have hlower := lowerRowOneCubicLowerHahn68_coeff_neg11
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CRH DH ERH dAH dBH dCRH dDH dERH
      hAord hBord (by rw [hCRmap]; exact hCdeford) hDord
      (by rw [hERmap]; exact hEdeford) hdAord hdBord hdCRord hdDord hdERord
  have hactual := T.lowerRowOne_actual_coeff_neg11_zero
  dsimp only at hactual hdecH'
  simp only [map_zero] at hactual
  have hcoeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-11 : ℚ))
    hdecH'
  rw [hactual, HahnSeries.coeff_add, hlower, add_zero] at hcoeff
  have hface := lowerRowOneCubicWeightElevenHahn68_coeff_neg11
    AH BH CRH DH ERH dAH dBH dCRH dDH dERH
      hAord hBord (by rw [hCRmap]; exact hCdeford) hDord
      (by rw [hERmap]; exact hEdeford) hdAord hdBord hdCRord hdDord hdERord
      hdAco hdBco' hdCRco' hdDco' hdERco'
  rw [hface] at hcoeff
  have hscalar : (8 / 81 : k) ≠ 0 := by norm_num
  have hout := (mul_eq_zero.mp hcoeff.symm).resolve_left hscalar
  rw [hCRmap, hERmap] at hout
  simpa only [AH, BH, CH, DH, EH, AR, BR, C0R, DR, E0R] using hout

/-- Component one after the source-valid row-one face.  The exceptional
locus is sharpened all the way to zero in the five defect coordinates. -/
def RhoOneZeroLCubicFirstRowOneComponent68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    ((a * b = 3 * d ∧ 3 * e = a * c) ∨
      (b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0))

theorem RhoOneZeroLCubicFirstI3RefinedComponent68.refine_with_rowOne
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    (P : RhoOneZeroLCubicFirstI3RefinedComponent68 T g u)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    RhoOneZeroLCubicFirstRowOneComponent68 T g u := by
  dsimp only [RhoOneZeroLCubicFirstI3RefinedComponent68,
    RhoOneZeroLCubicFirstRowOneComponent68] at P ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  rcases P with ⟨P0, hmain | hex⟩
  · exact ⟨P0, Or.inl hmain⟩
  · have h1 : rhoOneZeroLCubicNextOne68 a b c d e = 0 := by
      simpa only [A, B, C0, D, E, a, b, c, d, e] using
        T.rhoOne_cubicBranch_nextOne_zero hp hH hp6 hp5 hp4 P0
    have he := rhoOneZeroLCubic_firstComponent_exceptional_rowOne68
      a b c d e hex.1 hex.2.1 hex.2.2 h1
    exact ⟨P0, Or.inr ⟨hex.1, hex.2.1, hex.2.2, he⟩⟩

end AlignedSquareRhoOneCubicRowOneSource68

end Max11DegreeRoutes
