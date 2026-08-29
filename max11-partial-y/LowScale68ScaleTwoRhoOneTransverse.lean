import LowScale68ScaleTwoLocalRhoOne

/-! # The first transverse coefficient at the `rho = 1` cubic core

The scalar top rows vanish on the cubic-core family.  Their first variation
vanishes there as well.  Consequently the coefficient one step above the
weight-nine face of the fourth first integral is independent of all unknown
next coordinate coefficients: it is `(35/1728) * L * a⁴`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RhoOneTransverse68

variable {k : Type*} [Field k] [CharZero k]

local instance rhoOneTransverseHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def rhoOneCDefectHahn68 (A C0 : HahnSeries ℚ k) : HahnSeries ℚ k :=
  C0 - HahnSeries.C (1 / 3 : k) * A ^ 2

def rhoOneEDefectHahn68 (A E : HahnSeries ℚ k) : HahnSeries ℚ k :=
  E - HahnSeries.C (1 / 27 : k) * A ^ 3

theorem firstIntegralFourTopFaceHahn68_cubicDefects
    (A B C0 D E : HahnSeries ℚ k) :
    firstIntegralFourTopFaceHahn68 A B C0 D E =
      weightedMonomial68 (-8 / 27 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 0 3 0 0 0 +
      weightedMonomial68 (-16 / 9 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 1 1 1 0 0 +
      weightedMonomial68 (8 / 3 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 0 0 1 1 0 +
      weightedMonomial68 (8 / 3 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 0 1 0 0 1 := by
  simp only [firstIntegralFourTopFaceHahn68, weightedMonomial68,
    rhoOneCDefectHahn68, rhoOneEDefectHahn68]
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_ofNat,
    map_one]
  ring

theorem firstIntegralFourTopFaceHahn68_coeff_neg8_of_cubicBounds
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hCdef : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hEdef : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    (firstIntegralFourTopFaceHahn68 A B C0 D E).coeff (-8 : ℚ) = 0 := by
  let Cdef := rhoOneCDefectHahn68 A C0
  let Edef := rhoOneEDefectHahn68 A E
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-8 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-3) + (aD : ℚ) * (-4) + (aE : ℚ) * (-5)) :
      (weightedMonomial68 c A B Cdef D Edef aA aB aC aD aE).coeff
          (-8 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B Cdef D Edef
      aA aB aC aD aE (-2) (-2) (-3) (-4) (-5) (-8)
      hA hB (by simpa only [Cdef] using hCdef) hD
      (by simpa only [Edef] using hEdef) hlt
  have h1 := hzero (-8 / 27 : k) 0 3 0 0 0 (by norm_num)
  have h2 := hzero (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have h3 := hzero (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have h4 := hzero (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  rw [firstIntegralFourTopFaceHahn68_cubicDefects]
  simp only [HahnSeries.coeff_add]
  change _ + _ + _ + _ = 0
  rw [show rhoOneCDefectHahn68 A C0 = Cdef by rfl,
    show rhoOneEDefectHahn68 A E = Edef by rfl, h1, h2, h3, h4]
  ring

theorem firstIntegralFourHigherHahn68_coeff_neg8_of_cubicBounds
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hCcoeff : C0.coeff (-4 : ℚ) = (A.coeff (-2 : ℚ)) ^ 2 / 3)
    (hEcoeff : E.coeff (-6 : ℚ) = (A.coeff (-2 : ℚ)) ^ 3 / 27) :
    (firstIntegralFourHigherHahn68 L beta gamma delta epsilon zeta
      A B C0 D E).coeff (-8 : ℚ) =
        (35 / 1728 : k) * L * (A.coeff (-2 : ℚ)) ^ 4 := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-8 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-4) + (aD : ℚ) * (-4) + (aE : ℚ) * (-6)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-8 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-2) (-2) (-4) (-4) (-6) (-8)
      hA hB hC hD hE hlt
  have hz1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have hz2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hz3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have hz4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hz5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have hz6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hz7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hz9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hz11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have hz13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hz14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have hz16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  have hBstd : (↑(-3 : ℚ) : WithTop ℚ) ≤ B.orderTop :=
    (WithTop.coe_le_coe.mpr (by norm_num : (-3 : ℚ) ≤ -2)).trans hB
  have hDstd : (↑(-5 : ℚ) : WithTop ℚ) ≤ D.orderTop :=
    (WithTop.coe_le_coe.mpr (by norm_num : (-5 : ℚ) ≤ -4)).trans hD
  have hA1 : (↑(-2 * (1 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB1 : (↑(-3 * (1 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hBstd
  have hC1 : (↑(-4 * (1 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD1 : (↑(-5 * (1 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hDstd
  have hE1 : (↑(-6 * (1 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have hc8 := weightedMonomial68_coeff_at_weight
    ((7 / 12 : k) * L) A B C0 D E 0 0 2 0 0 1
      hA1 hB1 hC1 hD1 hE1
  have hc10 := weightedMonomial68_coeff_at_weight
    ((385 / 5184 : k) * L) A B C0 D E 4 0 0 0 0 1
      hA1 hB1 hC1 hD1 hE1
  have hc12 := weightedMonomial68_coeff_at_weight
    (-(35 / 72 : k) * L) A B C0 D E 2 0 1 0 0 1
      hA1 hB1 hC1 hD1 hE1
  have hc15 := weightedMonomial68_coeff_at_weight
    ((7 / 6 : k) * L) A B C0 D E 1 0 0 0 1 1
      hA1 hB1 hC1 hD1 hE1
  have h8 :
      (weightedMonomial68 ((7 / 12 : k) * L) A B C0 D E 0 0 2 0 0).coeff
          (-8 : ℚ) = ((7 / 12 : k) * L) * (C0.coeff (-4 : ℚ)) ^ 2 := by
    convert hc8 using 1 <;> norm_num
  have h10 :
      (weightedMonomial68 ((385 / 5184 : k) * L) A B C0 D E 4 0 0 0 0).coeff
          (-8 : ℚ) = ((385 / 5184 : k) * L) *
            (A.coeff (-2 : ℚ)) ^ 4 := by
    convert hc10 using 1 <;> norm_num
  have h12 :
      (weightedMonomial68 (-(35 / 72 : k) * L) A B C0 D E 2 0 1 0 0).coeff
          (-8 : ℚ) = (-(35 / 72 : k) * L) *
            (A.coeff (-2 : ℚ)) ^ 2 * C0.coeff (-4 : ℚ) := by
    convert hc12 using 1 <;> norm_num
  have h15 :
      (weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 1 0 0 0 1).coeff
          (-8 : ℚ) = ((7 / 6 : k) * L) * A.coeff (-2 : ℚ) *
            E.coeff (-6 : ℚ) := by
    convert hc15 using 1 <;> norm_num
  simp only [firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
  rw [hz1, hz2, hz3, hz4, hz5, hz6, hz7, h8, hz9, h10, hz11,
    h12, hz13, hz14, h15, hz16, hCcoeff, hEcoeff]
  ring

theorem firstIntegralFour68_coeff_neg8_of_cubicBounds
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop)
    (hCcoeff : C0.coeff (-4 : ℚ) = (A.coeff (-2 : ℚ)) ^ 2 / 3)
    (hEcoeff : E.coeff (-6 : ℚ) = (A.coeff (-2 : ℚ)) ^ 3 / 27) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-8 : ℚ) =
        (35 / 1728 : k) * L * (A.coeff (-2 : ℚ)) ^ 4 := by
  rw [firstIntegralFour68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_coeff_neg8_of_cubicBounds
      A B C0 D E hA hB hCdef hD hEdef,
    firstIntegralFourHigherHahn68_coeff_neg8_of_cubicBounds
      L beta gamma delta epsilon zeta A B C0 D E
      hA hB hC hD hE hCcoeff hEcoeff, zero_add]

/-! ## Source specialization -/

theorem localHahn_orderTop_ge_one_better_of_cleared_root_zero
    (a : k) (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ) (hn : 0 < n)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hscale :
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ))
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A)
    (hA0root : A0.eval a = 0) :
    (↑(-((n - 1 : ℕ) : ℚ)) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a A).orderTop := by
  obtain ⟨A1, hA1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 A0 a hdegree hroot hA0root
  have hclear1 : algebraMap k[X] (RatFunc k) A1 =
      (algebraMap k[X] (RatFunc k) h0) ^ (n - 1) * A := by
    have hcancel := algebraMap_cancel_factoredClearing
      h0 A0 A1 A 1 (n - 1) 1 hh0 (by simpa using hA1) (by
        simpa only [Nat.mul_one, show n - 1 + 1 = n by omega] using hclear)
    simpa only [Nat.mul_one] using hcancel
  exact localHahn_orderTop_ge_of_cleared a h0 A1 A (n - 1) hscale hclear1

def RhoOneSourceCubicBranch68
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (g u : k[X]) : Prop :=
  ∃ c : k, c ≠ 0 ∧
    ratFuncAtHahn46 T.root (algebraMap k[X] (RatFunc k) h0) =
      HahnSeries.single (1 : ℚ) c ∧
    (c ^ 2)⁻¹ * u.eval T.root = (c⁻¹ * g.eval T.root) ^ 2 / 3 ∧
    (c ^ 3)⁻¹ * (p.coeff 3).eval T.root =
      (c⁻¹ * g.eval T.root) ^ 3 / 27

theorem SquareConstantLIntegratedLocalRootData68.rhoOne_cubicBranch_transverse_zero
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbranch : RhoOneSourceCubicBranch68 T g u) :
    h0 ∣ g ∧ h0 ∣ u ∧ h0 ∣ p.coeff 3 := by
  obtain ⟨c, hc, hsingle, hv, ht⟩ := hbranch
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
    SquareConstantLIntegratedSourceData68.clearedCoordinatesRhoOne
      T.source hp T.scale_ne_zero hH hp6 hp5 hp4
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
  let t : k := (c ^ 3)⁻¹ * (p.coeff 3).eval T.root
  let v : k := (c ^ 2)⁻¹ * u.eval T.root
  let z : k := c⁻¹ * g.eval T.root
  have hv' : v = z ^ 2 / 3 := by simpa only [v, z] using hv
  have ht' : t = z ^ 3 / 27 := by simpa only [t, z] using ht
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
    rw [hAco, hAroot]
    simp only [rhoOneInitialA68, v, z]
    field_simp [hc]
  have hBform : BH.coeff (-3 : ℚ) = rhoOneInitialB68 t v z := by
    dsimp only [BH]
    rw [hBco, hBroot]
    simp only [rhoOneInitialB68, t, v, z]
    field_simp [hc]
  have hCform : CH.coeff (-4 : ℚ) = rhoOneInitialC68 t v z := by
    dsimp only [CH]
    rw [hCco, hCroot]
    simp only [rhoOneInitialC68, t, v, z]
    field_simp [hc]
  have hDform : DH.coeff (-5 : ℚ) = rhoOneInitialD68 t v z := by
    dsimp only [DH]
    rw [hDco, hDroot]
    simp only [rhoOneInitialD68, t, v, z]
    field_simp [hc]
  have hEform : EH.coeff (-6 : ℚ) = rhoOneInitialE68 t v z := by
    dsimp only [EH]
    rw [hEco, hEroot]
    simp only [rhoOneInitialE68, t, v, z]
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
      (rhoOneCDefectHahn68 AH CH).orderTop := by rw [← hCRmap]; exact hCRord
  have hEdeford : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 AH EH).orderTop := by rw [← hERmap]; exact hERord
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-8 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-8 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have htrans := firstIntegralFour68_coeff_neg8_of_cubicBounds
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hAord) hBord (by simpa only [CH] using hCord)
      hCdeford hDord (by simpa only [EH] using hEord) hEdeford hClead hElead
  rw [htrans] at hcoeff
  have hscalar : (35 / 1728 : k) * l ≠ 0 :=
    mul_ne_zero (by norm_num) T.septic_ne_zero
  have hApow : (AH.coeff (-2 : ℚ)) ^ 4 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hscalar
    simpa only [mul_assoc] using hcoeff
  have hAzero : AH.coeff (-2 : ℚ) = 0 := eq_zero_of_pow_eq_zero hApow
  have hzpow : z ^ 2 = 0 := by
    rw [hAform, hv'] at hAzero
    simp only [rhoOneInitialA68] at hAzero
    linear_combination (-12 : k) * hAzero
  have hz : z = 0 := eq_zero_of_pow_eq_zero hzpow
  have hgroot : g.eval T.root = 0 := by
    dsimp only [z] at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hc)
  have hvzero : v = 0 := by rw [hv', hz]; norm_num
  have htzero : t = 0 := by rw [ht', hz]; norm_num
  have huroot : u.eval T.root = 0 := by
    dsimp only [v] at hvzero
    exact (mul_eq_zero.mp hvzero).resolve_left
      (inv_ne_zero (pow_ne_zero 2 hc))
  have hp3root : (p.coeff 3).eval T.root = 0 := by
    dsimp only [t] at htzero
    exact (mul_eq_zero.mp htzero).resolve_left
      (inv_ne_zero (pow_ne_zero 3 hc))
  exact ⟨
    linearPolynomial_dvd_of_eval_eq_zero h0 g T.root T.scale_degree
      T.root_eq hgroot,
    linearPolynomial_dvd_of_eval_eq_zero h0 u T.root T.scale_degree
      T.root_eq huroot,
    linearPolynomial_dvd_of_eval_eq_zero h0 (p.coeff 3) T.root T.scale_degree
      T.root_eq hp3root⟩

theorem SquareConstantLIntegratedLocalRootData68.rhoOne_cubicBranch_next_divisibilities
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbranch : RhoOneSourceCubicBranch68 T g u) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3 := by
  obtain ⟨⟨g1, hg1⟩, ⟨u1, hu1⟩, hp3⟩ :=
    T.rhoOne_cubicBranch_transverse_zero hp hH hp6 hp5 hp4 hbranch
  refine ⟨⟨g1, ?_⟩, ⟨u1, ?_⟩, hp3⟩
  · rw [hp5, hg1]
    ring
  · rw [hp4, hu1]
    ring

end RhoOneTransverse68

#print axioms firstIntegralFour68_coeff_neg8_of_cubicBounds
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOne_cubicBranch_transverse_zero
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOne_cubicBranch_next_divisibilities

end Max11DegreeRoutes
