import LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangentInvariants

/-! # Exporting the improved main-tangent defect orders -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicMainTangentOrderBridge68

variable {k : Type*} [Field k] [CharZero k]

/-- The two improved orders used by the next I4/I3 faces.  This packages the
root-factor argument previously internal to `rhoOne_mainTangent_nextOne_zero`.
-/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_defect_orders
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
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ)) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    ((↑(-3 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68 A B D).orderTop) ∧
      ((↑(-4 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68 A C ER).orderTop) := by
  dsimp only at hmain ⊢
  have hbranch := P.1
  obtain ⟨cs, t, v, z, hcs, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ :=
    hbranch
  have hv' : v = z ^ 2 / 3 := by
    have h := (div_eq_iff (pow_ne_zero 2 hz)).mp hvcore
    calc v = (1 / 3 : k) * z ^ 2 := h
         _ = z ^ 2 / 3 := by ring
  have ht' : t = z ^ 3 / 27 := by
    have h := (div_eq_iff (pow_ne_zero 3 hz)).mp htcore
    calc t = (1 / 27 : k) * z ^ 3 := h
         _ = z ^ 3 / 27 := by ring
  have hgval : g.eval T.root = cs * z := by rw [hzdef]; field_simp [hcs]
  have huval : u.eval T.root = cs ^ 2 * v := by rw [hv]; field_simp [hcs]
  have hp3val : (p.coeff 3).eval T.root = cs ^ 3 * t := by
    rw [ht]; field_simp [hcs]
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
  let CH := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let EH := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let FRH := ratFuncAtHahn46 T.root FR
  let GRH := ratFuncAtHahn46 T.root GR
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
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
    field_simp [hcs]; ring
  have hD0root : D0.eval T.root = 0 := by
    simp [D0, localClearedD68RhoOne, T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hCdef0root : Cdef0.eval T.root = 0 := by
    simp [Cdef0, C0, A0, localClearedC68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hEdef0root : Edef0.eval T.root = 0 := by
    simp [Edef0, E0, A0, localClearedE68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  obtain ⟨B1, hB1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 B0 T.root T.scale_degree T.root_eq hB0root
  obtain ⟨C1, hC1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Cdef0 T.root T.scale_degree T.root_eq hCdef0root
  obtain ⟨D1, hD1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 D0 T.root T.scale_degree T.root_eq hD0root
  obtain ⟨E1, hE1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Edef0 T.root T.scale_degree T.root_eq hEdef0root
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR, C0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]; ring
  have hEdefclear : algebraMap k[X] (RatFunc k) Edef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * ER := by
    dsimp only [Edef0, ER, E0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hEclear, hAclear]; ring
  have hBclear1 : algebraMap k[X] (RatFunc k) B1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * BR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 B0 B1 BR 1 2 1 T.scale_ne_zero (by simpa using hB1) (by
        simpa only [Nat.mul_one, show 2 + 1 = 3 by omega] using hBclear)
    simpa only [Nat.mul_one] using hc
  have hCclear1 : algebraMap k[X] (RatFunc k) C1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * CR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 Cdef0 C1 CR 1 3 1 T.scale_ne_zero (by simpa using hC1) (by
        simpa only [Nat.mul_one, show 3 + 1 = 4 by omega] using hCdefclear)
    simpa only [Nat.mul_one] using hc
  have hDclear1 : algebraMap k[X] (RatFunc k) D1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * DR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 D0 D1 DR 1 4 1 T.scale_ne_zero (by simpa using hD1) (by
        simpa only [Nat.mul_one, show 4 + 1 = 5 by omega] using hDclear)
    simpa only [Nat.mul_one] using hc
  have hEclear1 : algebraMap k[X] (RatFunc k) E1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * ER := by
    have hc := algebraMap_cancel_factoredClearing
      h0 Edef0 E1 ER 1 5 1 T.scale_ne_zero (by simpa using hE1) (by
        simpa only [Nat.mul_one, show 5 + 1 = 6 by omega] using hEdefclear)
    simpa only [Nat.mul_one] using hc
  let F0 : k[X] := D1 - C (1 / 3 : k) * A0 * B1
  let G0 : k[X] := E1 - C (1 / 3 : k) * A0 * C1
  have hFclear : algebraMap k[X] (RatFunc k) F0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * FR := by
    dsimp only [F0, FR]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C]
    rw [hDclear1, hAclear, hBclear1]; ring
  have hGclear : algebraMap k[X] (RatFunc k) G0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * GR := by
    dsimp only [G0, GR]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C]
    rw [hEclear1, hAclear, hCclear1]; ring
  obtain ⟨cs', hcs', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 T.root T.scale_degree T.root_eq
  have hcseq : cs' = cs := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst cs'
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at P
  rcases P with ⟨_, ⟨hAord, hBord, hCord, hCRord0, hDord, hEord,
    hERord0⟩, hAne, htaut, h4, h3, hsplit⟩
  have hCRmap : CRH = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CRH, CR, AH, CH, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH EH := by
    dsimp only [ERH, ER, AH, EH, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : FRH = rhoOneTangentDDefectHahn68 AH BH DH := by
    dsimp only [FRH, FR, AH, BH, DH, AR, BR, DR,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hABco := weightedMonomial68_coeff_at_general_lower_next
    (1 / 3 : k) AH BH AH BH CH 1 1 0 0 0
      (-2) (-2) (-2) (-2) (-4) hAord hBord hAord hBord hCord
  have hACco := weightedMonomial68_coeff_at_general_lower_next
    (1 / 3 : k) AH CRH AH BH CH 1 1 0 0 0
      (-2) (-3) (-2) (-2) (-4) hAord
      (by rw [hCRmap]; exact hCRord0) hAord hBord hCord
  norm_num at hABco hACco
  have hABco' : (HahnSeries.C (1 / 3 : k) * AH * BH).coeff (-4 : ℚ) =
      (1 / 3 : k) * AH.coeff (-2 : ℚ) * BH.coeff (-2 : ℚ) := by
    simpa [weightedMonomial68] using hABco
  have hACco' : (HahnSeries.C (1 / 3 : k) * AH * CRH).coeff (-5 : ℚ) =
      (1 / 3 : k) * AH.coeff (-2 : ℚ) * CRH.coeff (-3 : ℚ) := by
    simpa [weightedMonomial68] using hACco
  have hFRlead : FRH.coeff (-4 : ℚ) = 0 := by
    rw [hFRmap]
    simp only [rhoOneTangentDDefectHahn68, HahnSeries.coeff_sub]
    change DH.coeff (-4 : ℚ) - (HahnSeries.C (1 / 3 : k) * AH * BH).coeff
      (-4 : ℚ) = 0
    rw [hABco']
    linear_combination (-1 / 3 : k) * hmain.1
  have hGRlead : GRH.coeff (-5 : ℚ) = 0 := by
    rw [hGRmap]
    simp only [rhoOneTangentEDefectHahn68, HahnSeries.coeff_sub]
    change ERH.coeff (-5 : ℚ) - (HahnSeries.C (1 / 3 : k) * AH * CRH).coeff
      (-5 : ℚ) = 0
    rw [hACco']
    rw [hCRmap, hERmap]
    linear_combination (1 / 3 : k) * hmain.2
  have hFco := localHahn_coeff_neg_of_cleared T.root cs h0 F0 FR 4
    hcs hsingle hFclear
  have hGco := localHahn_coeff_neg_of_cleared T.root cs h0 G0 GR 5
    hcs hsingle hGclear
  norm_num at hFco hGco
  have hF0root : F0.eval T.root = 0 := by
    change FRH.coeff (-4 : ℚ) = _ at hFco
    rw [hFRlead] at hFco
    exact (mul_eq_zero.mp hFco.symm).resolve_left
      (inv_ne_zero (pow_ne_zero 4 hcs))
  have hG0root : G0.eval T.root = 0 := by
    change GRH.coeff (-5 : ℚ) = _ at hGco
    rw [hGRlead] at hGco
    exact (mul_eq_zero.mp hGco.symm).resolve_left
      (inv_ne_zero (pow_ne_zero 5 hcs))
  have hFRord := localHahn_orderTop_ge_one_better_of_cleared_root_zero
    T.root h0 F0 FR 4 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      T.scale_order hFclear hF0root
  have hGRord := localHahn_orderTop_ge_one_better_of_cleared_root_zero
    T.root h0 G0 GR 5 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      T.scale_order hGclear hG0root
  norm_num at hFRord hGRord
  change ((↑(-3 : ℚ) : WithTop ℚ) ≤ FRH.orderTop) at hFRord
  change ((↑(-4 : ℚ) : WithTop ℚ) ≤ GRH.orderTop) at hGRord
  constructor
  · rw [← hFRmap]
    exact hFRord
  · rw [← hCRmap, ← hERmap, ← hGRmap]
    exact hGRord

/-- The next I4/I3 tangent invariants for the actual normalized source, with
the improved defect orders discharged by
`rhoOne_mainTangent_defect_orders`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_invariants
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
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ)) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicMainTangentFour68 T.source.beta
      (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ)) (C.coeff (-3 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
    rhoOneZeroLCubicMainTangentThree68
      (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ)) (C.coeff (-3 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 := by
  have hord := T.rhoOne_mainTangent_defect_orders hp hH hp6 hp5 hp4 P hmain
  exact T.rhoOne_mainTangent_invariants_of_orders P hord.1 hord.2

/-- The exact finite residual left by row one and the next two invariant
faces. -/
def RhoOneZeroLCubicMainTangentInvariantResidual68
    (beta a b c f g : k) : Prop :=
  (c = 0 ∧
    ((b = 0 ∧ beta = 0) ∨
     (b ≠ 0 ∧ f = 0 ∧
      -64 * b ^ 3 + 15 * beta * a ^ 3 + 576 * b * g = 0))) ∨
  (c ≠ 0 ∧ b ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
    rhoOneZeroLCubicMainTangentFour68 beta a b c f g = 0 ∧
    rhoOneZeroLCubicMainTangentThree68 a b c f g = 0)

/-- On the nonzero component, I3 solves the `g` direction and I4 reduces to
one smaller scalar after using `c² = a b²`. -/
theorem rhoOneZeroLCubicMainTangent_nonzero_reduced68
    (beta a b c f g : k) (hc0 : c ≠ 0)
    (hc : c ^ 2 = a * b ^ 2)
    (h4 : rhoOneZeroLCubicMainTangentFour68 beta a b c f g = 0)
    (h3 : rhoOneZeroLCubicMainTangentThree68 a b c f g = 0) :
    3 * c * g = a * b * f + b ^ 2 * c ∧
    128 * b ^ 3 + 15 * beta * a ^ 3 + 768 * c * f = 0 := by
  simp only [rhoOneZeroLCubicMainTangentFour68] at h4
  simp only [rhoOneZeroLCubicMainTangentThree68] at h3
  constructor
  · linear_combination h3
  · have hc' : c ^ 2 - a * b ^ 2 = 0 := by linear_combination hc
    have hfac : c *
        (128 * b ^ 3 + 15 * beta * a ^ 3 + 768 * c * f) = 0 := by
      linear_combination c * h4 - 192 * b * h3 + 192 * f * hc'
    exact (mul_eq_zero.mp hfac).resolve_left hc0

/-- Source-facing form of the complete residual split after combining the
old differential row with the two newly unconditional invariant rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_residual
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
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ)) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    RhoOneZeroLCubicMainTangentInvariantResidual68 T.source.beta
      (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ)) (C.coeff (-3 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) := by
  have ha :
      let A := ratFuncAtHahn46 T.root T.source.A
      A.coeff (-2 : ℚ) ≠ 0 := by
    exact P.2.2.1
  have h1 := T.rhoOne_mainTangent_nextOne_zero hp hH hp6 hp5 hp4 P hmain
  have hinv := T.rhoOne_mainTangent_invariants hp hH hp6 hp5 hp4 P hmain
  dsimp only at ha h1 hinv ⊢
  exact rhoOneZeroLCubicMainTangent_exact_split68 _ _ _ _ _ _
    ha h1 hinv.1 hinv.2

end AlignedSquareRhoOneCubicMainTangentOrderBridge68

end Max11DegreeRoutes
