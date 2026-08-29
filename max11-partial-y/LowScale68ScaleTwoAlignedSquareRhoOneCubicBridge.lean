import LowScale68ScaleTwoAlignedSquareRhoOneCubicNext

/-! # Source bridge for the aligned zero-septic rho-one cubic component -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicBridge68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicBridgeHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The improved local box obtained by removing the four cubic leading
terms. -/
def RhoOneZeroLCubicImprovedHahnBounds68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop ∧
  (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
  (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop ∧
  (↑(-3 : ℚ) : WithTop ℚ) ≤ (rhoOneCDefectHahn68 A C0).orderTop ∧
  (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop ∧
  (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop ∧
  (↑(-5 : ℚ) : WithTop ℚ) ≤ (rhoOneEDefectHahn68 A E).orderTop

/-- The exact source-facing packet after the first two informative
zero-septic cubic rows. -/
def RhoOneZeroLCubicNextSourcePacket68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  RhoOneZeroLCubicSourcePacket68 T g u ∧
  RhoOneZeroLCubicImprovedHahnBounds68 T ∧
  A.coeff (-2 : ℚ) ≠ 0 ∧
  (firstIntegralFour68 (HahnSeries.C 0) A B C0 D E
    (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
    (HahnSeries.C T.source.zeta)).coeff (-8 : ℚ) = 0 ∧
  rhoOneZeroLCubicNextFour68 (A.coeff (-2 : ℚ))
    (B.coeff (-2 : ℚ)) c (D.coeff (-4 : ℚ)) e = 0 ∧
  rhoOneZeroLCubicNextThree68 (A.coeff (-2 : ℚ))
    (B.coeff (-2 : ℚ)) c (D.coeff (-4 : ℚ)) e = 0 ∧
  (A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) =
      3 * D.coeff (-4 : ℚ) ∨
    A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) ^ 2 -
      B.coeff (-2 : ℚ) * D.coeff (-4 : ℚ) + 2 * c ^ 2 = 0)

/-- The two next rows have only two algebraic components after eliminating
the improved `E`-defect coefficient. -/
theorem rhoOneZeroLCubicNext_rows_component_split68
    (a b c d e : k)
    (h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0)
    (h3 : rhoOneZeroLCubicNextThree68 a b c d e = 0) :
    a * b = 3 * d ∨ a * b ^ 2 - b * d + 2 * c ^ 2 = 0 := by
  have h4' : -2 * a * b * c + 3 * c * d + 3 * b * e = 0 := by
    simp only [rhoOneZeroLCubicNextFour68] at h4
    linear_combination (9 / 8 : k) * h4
  have h3' :
      3 * d ^ 2 - 4 * a * b * d + a ^ 2 * b ^ 2 - 2 * a * c ^ 2 +
        6 * c * e = 0 := by
    simp only [rhoOneZeroLCubicNextThree68] at h3
    linear_combination (9 / 4 : k) * h3
  have hfactor :
      (a * b - 3 * d) * (a * b ^ 2 - b * d + 2 * c ^ 2) = 0 := by
    calc
      (a * b - 3 * d) * (a * b ^ 2 - b * d + 2 * c ^ 2) =
          b * (3 * d ^ 2 - 4 * a * b * d + a ^ 2 * b ^ 2 -
            2 * a * c ^ 2 + 6 * c * e) -
          2 * c * (-2 * a * b * c + 3 * c * d + 3 * b * e) := by ring
      _ = 0 := by rw [h4', h3']; ring
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · left; linear_combination hleft
  · exact Or.inr hright

/-- Transport of the rational cubic component to the improved Hahn box and
the two first informative zero-septic equations. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_cubicBranch_nextPacket
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbranch : RhoOneZeroLCubicSourcePacket68 T g u) :
    RhoOneZeroLCubicNextSourcePacket68 T g u := by
  have hbranch0 := hbranch
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ :=
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
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let E0 := localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2
  let ER : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3
  let Cdef0 : k[X] := C0 - C (1 / 3 : k) * A0 ^ 2
  let Edef0 : k[X] := E0 - C (1 / 27 : k) * A0 ^ 3
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  change algebraMap k[X] (RatFunc k) A0 = _ at hAclear
  change algebraMap k[X] (RatFunc k) B0 = _ at hBclear
  change algebraMap k[X] (RatFunc k) C0 = _ at hCclear
  change algebraMap k[X] (RatFunc k) D0 = _ at hDclear
  change algebraMap k[X] (RatFunc k) E0 = _ at hEclear
  have hAco := localHahn_coeff_neg_of_cleared T.root c h0 A0 T.source.A 2
    hc hsingle hAclear
  have hBco := localHahn_coeff_neg_of_cleared T.root c h0 B0 T.source.B 3
    hc hsingle hBclear
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0 C0 T.source.C0 4
    hc hsingle hCclear
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0 D0 T.source.D 5
    hc hsingle hDclear
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0 E0 T.source.E 6
    hc hsingle hEclear
  norm_num at hAco hBco hCco hDco hEco
  have hAroot : A0.eval T.root =
      u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [A0, localClearedA68RhoOne]
  have hBroot : B0.eval T.root =
      (p.coeff 3).eval T.root - (2 / 3 : k) * u.eval T.root *
        g.eval T.root + (5 / 27 : k) * g.eval T.root ^ 3 := by
    simp [B0, localClearedB68RhoOne]
  have hCroot : C0.eval T.root =
      -(1 / 2 : k) * (p.coeff 3).eval T.root * g.eval T.root +
        (1 / 6 : k) * u.eval T.root * g.eval T.root ^ 2 -
        (5 / 144 : k) * g.eval T.root ^ 4 := by
    simp [C0, localClearedC68RhoOne, T.root_eq]
  have hDroot : D0.eval T.root =
      (1 / 12 : k) * (p.coeff 3).eval T.root * g.eval T.root ^ 2 -
        (1 / 54 : k) * u.eval T.root * g.eval T.root ^ 3 +
        (1 / 324 : k) * g.eval T.root ^ 5 := by
    simp [D0, localClearedD68RhoOne, T.root_eq]
  have hEroot : E0.eval T.root =
      -(1 / 216 : k) * (p.coeff 3).eval T.root * g.eval T.root ^ 3 +
        (1 / 1296 : k) * u.eval T.root * g.eval T.root ^ 4 -
        (5 / 46656 : k) * g.eval T.root ^ 6 := by
    simp [E0, localClearedE68RhoOne, T.root_eq]
  have hAform : AH.coeff (-2 : ℚ) = rhoOneInitialA68 v z := by
    dsimp only [AH]
    rw [hAco, hAroot, hv, hzdef]
    simp only [rhoOneInitialA68]
    field_simp [hc]
  have hBform : BH.coeff (-3 : ℚ) = rhoOneInitialB68 t v z := by
    dsimp only [BH]
    rw [hBco, hBroot, ht, hv, hzdef]
    simp only [rhoOneInitialB68]
    field_simp [hc]
  have hCform : CH.coeff (-4 : ℚ) = rhoOneInitialC68 t v z := by
    dsimp only [CH]
    rw [hCco, hCroot, ht, hv, hzdef]
    simp only [rhoOneInitialC68]
    field_simp [hc]
  have hDform : DH.coeff (-5 : ℚ) = rhoOneInitialD68 t v z := by
    dsimp only [DH]
    rw [hDco, hDroot, ht, hv, hzdef]
    simp only [rhoOneInitialD68]
    field_simp [hc]
  have hEform : EH.coeff (-6 : ℚ) = rhoOneInitialE68 t v z := by
    dsimp only [EH]
    rw [hEco, hEroot, ht, hv, hzdef]
    simp only [rhoOneInitialE68]
    field_simp [hc]
  have hBlead : BH.coeff (-3 : ℚ) = 0 := by
    rw [hBform, hv', ht']
    simp only [rhoOneInitialB68]
    ring
  have hDlead : DH.coeff (-5 : ℚ) = 0 := by
    rw [hDform, hv', ht']
    simp only [rhoOneInitialD68]
    ring
  have hClead : CH.coeff (-4 : ℚ) = (AH.coeff (-2 : ℚ)) ^ 2 / 3 := by
    rw [hAform, hCform, hv', ht']
    simp only [rhoOneInitialA68, rhoOneInitialC68]
    ring
  have hElead : EH.coeff (-6 : ℚ) = (AH.coeff (-2 : ℚ)) ^ 3 / 27 := by
    rw [hAform, hEform, hv', ht']
    simp only [rhoOneInitialA68, rhoOneInitialE68]
    ring
  have hAlead : AH.coeff (-2 : ℚ) = -(z ^ 2) / 12 := by
    rw [hAform, hv']
    simp only [rhoOneInitialA68]
    ring
  have hAne : AH.coeff (-2 : ℚ) ≠ 0 := by
    rw [hAlead]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hz)) (by norm_num)
  have hB0root : B0.eval T.root = 0 := by
    dsimp only [BH] at hBlead
    rw [hBco] at hBlead
    exact (mul_eq_zero.mp hBlead).resolve_left
      (inv_ne_zero (pow_ne_zero 3 hc))
  have hD0root : D0.eval T.root = 0 := by
    dsimp only [DH] at hDlead
    rw [hDco] at hDlead
    exact (mul_eq_zero.mp hDlead).resolve_left
      (inv_ne_zero (pow_ne_zero 5 hc))
  have hCdef0root : Cdef0.eval T.root = 0 := by
    dsimp only [AH, CH] at hClead
    rw [hAco, hCco] at hClead
    simp only [Cdef0, eval_sub, eval_mul, eval_C, eval_pow]
    field_simp [hc] at hClead ⊢
    linear_combination hClead
  have hEdef0root : Edef0.eval T.root = 0 := by
    dsimp only [AH, EH] at hElead
    rw [hAco, hEco] at hElead
    simp only [Edef0, eval_sub, eval_mul, eval_C, eval_pow]
    field_simp [hc] at hElead ⊢
    linear_combination hElead
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]
    ring
  have hEdefclear : algebraMap k[X] (RatFunc k) Edef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * ER := by
    dsimp only [Edef0, ER]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hEclear, hAclear]
    ring
  obtain ⟨hAord, hBord0, hCord, hDord0, hEord⟩ :=
    T.coordinateOrderBoundsRhoOne hp hH hp6 hp5 hp4
  have hBord : (↑(-2 : ℚ) : WithTop ℚ) ≤ BH.orderTop := by
    dsimp only [BH]
    exact localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 B0 T.source.B 3 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hBclear hB0root
  have hDord : (↑(-4 : ℚ) : WithTop ℚ) ≤ DH.orderTop := by
    dsimp only [DH]
    exact localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 D0 T.source.D 5 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hDclear hD0root
  have hCRord : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop :=
    localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 Cdef0 CR 4 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hCdefclear hCdef0root
  have hERord : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root ER).orderTop :=
    localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 Edef0 ER 6 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hEdefclear hEdef0root
  have hCRmap : ratFuncAtHahn46 T.root CR = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CR, AH, CH, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ER = rhoOneEDefectHahn68 AH EH := by
    dsimp only [ER, AH, EH, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hCdeford : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 AH CH).orderTop := by
    rw [← hCRmap]
    exact hCRord
  have hEdeford : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 AH EH).orderTop := by
    rw [← hERmap]
    exact hERord
  have hbounds : RhoOneZeroLCubicImprovedHahnBounds68 T := by
    dsimp only [RhoOneZeroLCubicImprovedHahnBounds68, AH, BH, CH, DH, EH]
    exact ⟨hAord, hBord, hCord, hCdeford, hDord, hEord, hEdeford⟩
  have htaut := firstIntegralFour68_coeff_neg8_zero_of_zeroL_cubicBounds
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hAord hBord hCord hCdeford hDord hEord
      hEdeford hClead hElead
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have h4coeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-7 : ℚ)) hi4H'
  have h4const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-7 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [h4const] at h4coeff
  have h4formula := firstIntegralFour68_coeff_neg7_of_zeroL_cubicBounds
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hAord hBord hCord hCdeford hDord hEord
      hEdeford
  rw [h4formula] at h4coeff
  have h3coeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-8 : ℚ)) hi3H'
  have h3const : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-8 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [h3const] at h3coeff
  have h3formula := firstIntegralThree68_coeff_neg8_of_zeroL_cubicBounds
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hAord hBord hCord hCdeford hDord hEord
      hEdeford
  rw [h3formula] at h3coeff
  have hsplit := rhoOneZeroLCubicNext_rows_component_split68
    (AH.coeff (-2 : ℚ)) (BH.coeff (-2 : ℚ))
    ((rhoOneCDefectHahn68 AH CH).coeff (-3 : ℚ))
    (DH.coeff (-4 : ℚ))
    ((rhoOneEDefectHahn68 AH EH).coeff (-5 : ℚ)) h4coeff h3coeff
  dsimp only [RhoOneZeroLCubicNextSourcePacket68, AH, BH, CH, DH, EH]
  exact ⟨hbranch0, hbounds, hAne, htaut, h4coeff, h3coeff, hsplit⟩

/-- The exhaustive rho-one split with its cubic component upgraded to the
first informative zero-septic packet. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_component_split_with_cubic_next
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
      RhoOneZeroLCubicNextSourcePacket68 T g u ∨
      RhoOneZeroLNoncubicSourcePacket68 T g u := by
  rcases T.rhoOne_component_split hp hH hp6 hp5 hp4 with hdesc | hcubic | hnon
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl
      (T.rhoOne_cubicBranch_nextPacket hp hH hp6 hp5 hp4 hcubic))
  · exact Or.inr (Or.inr hnon)

end AlignedSquareRhoOneCubicBridge68

end Max11DegreeRoutes
