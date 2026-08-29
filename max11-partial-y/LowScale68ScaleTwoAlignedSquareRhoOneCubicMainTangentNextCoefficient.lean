import LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangentOrderBridge

/-! # The next invariant coefficients on the exceptional main tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicMainTangentNextCoefficient68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicMainTangentNextCoefficientHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def rhoOneZeroLCubicExceptionalFour68 (b1 c1 f g : k) : k :=
  b1 * g + c1 * f

def rhoOneZeroLCubicExceptionalThree68
    (a b1 c1 f g : k) : k :=
  -2 * a * b1 * f + 6 * c1 * g + 3 * f ^ 2

/-- After `b = c = beta = 0`, the next I4/I3 coefficients occur at
exponents `-5` and `-6`. -/
theorem firstIntegral_mainTangent_exceptional_coeff68
    (gamma delta epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-4 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-5 : ℚ) =
        (8 / 3 : k) * rhoOneZeroLCubicExceptionalFour68
          (B.coeff (-1 : ℚ)) (C.coeff (-2 : ℚ))
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) ∧
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-6 : ℚ) =
        (4 / 9 : k) * rhoOneZeroLCubicExceptionalThree68
          (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
          (C.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ))
          (G.coeff (-4 : ℚ)) := by
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
  have lead (r : ℚ) (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have h4dec := firstIntegralFour_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h3dec := firstIntegralThree_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h4decH :
      firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
          (HahnSeries.C zeta) =
        firstIntegralFourMainTangentTopHahn68 0 A B C F G +
          firstIntegralFourMainTangentLowerHahn68 0 gamma delta epsilon zeta
            A B C F G := by
    rw [h4dec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68, weightedMonomial68, map_mul,
      map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h3decH :
      firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
          (HahnSeries.C zeta) =
        firstIntegralThreeMainTangentTopHahn68 A B C F G +
          firstIntegralThreeMainTangentLowerHahn68 0 gamma delta epsilon zeta
            A B C F G := by
    rw [h3dec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68, firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68, weightedMonomial68, map_mul,
      map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h4t1 := hz (-5) (-8 / 27 : k) B A C F G 3 0 0 0 0
    (-1) (-2) (-2) (-3) (-4) hB hA hC hF hG (by norm_num)
  have h4t3 := lead (-5) (8 / 3 : k) B G A C F 1 1 0 0 0
    (-1) (-4) (-2) (-2) (-3) hB hG hA hC hF
  have h4t4 := lead (-5) (8 / 3 : k) C F A B G 1 1 0 0 0
    (-2) (-3) (-2) (-1) (-4) hC hF hA hB hG
  norm_num at h4t3 h4t4
  have h4l3 := hz (-5) ((1 / 4 : k) * delta) A B C F G 2 0 0 0 0
    (-2) (-1) (-2) (-3) (-4) hA hB hC hF hG (by norm_num)
  have h4l5 := hz (-5) (3 * delta) C A B F G 1 0 0 0 0
    (-2) (-2) (-1) (-3) (-4) hC hA hB hF hG (by norm_num)
  have h4l6 := hz (-5) (4 * gamma) F A B C G 1 0 0 0 0
    (-3) (-2) (-1) (-2) (-4) hF hA hB hC hG (by norm_num)
  have h4l7 := hz (-5) zeta A B C F G 1 0 0 0 0
    (-2) (-1) (-2) (-3) (-4) hA hB hC hF hG (by norm_num)
  have h4l8 := hz (-5) (2 * epsilon) B A C F G 1 0 0 0 0
    (-1) (-2) (-2) (-3) (-4) hB hA hC hF hG (by norm_num)
  have h3t1 := lead (-6) (-8 / 9 : k) A B F C G 1 1 1 0 0
    (-2) (-1) (-3) (-2) (-4) hA hB hF hC hG
  have h3t2 := hz (-6) (-8 / 9 : k) B C A F G 2 1 0 0 0
    (-1) (-2) (-2) (-3) (-4) hB hC hA hF hG (by norm_num)
  have h3t3 := lead (-6) (8 / 3 : k) C G A B F 1 1 0 0 0
    (-2) (-4) (-2) (-1) (-3) hC hG hA hB hF
  have h3l2 := lead (-6) (4 / 3 : k) F A B C G 2 0 0 0 0
    (-3) (-2) (-1) (-2) (-4) hF hA hB hC hG
  have h3l5 := hz (-6) (-(1 / 2 : k) * delta) A B C F G 1 1 0 0 0
    (-2) (-1) (-2) (-3) (-4) hA hB hC hF hG (by norm_num)
  have h3l6 := hz (-6) (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0
    (-1) (-2) (-2) (-3) (-4) hB hA hC hF hG (by norm_num)
  have h3l7 := hz (-6) (4 * gamma) G A B C F 1 0 0 0 0
    (-4) (-2) (-1) (-2) (-3) hG hA hB hC hF (by norm_num)
  have h3l8 := hz (-6) (2 * epsilon) C A B F G 1 0 0 0 0
    (-2) (-2) (-1) (-3) (-4) hC hA hB hF hG (by norm_num)
  have h3l9 := hz (-6) (3 * delta) F A B C G 1 0 0 0 0
    (-3) (-2) (-1) (-2) (-4) hF hA hB hC hG (by norm_num)
  have h3l10 := hz (-6) zeta B A C F G 1 0 0 0 0
    (-1) (-2) (-2) (-3) (-4) hB hA hC hF hG (by norm_num)
  norm_num at h3t1 h3t3 h3l2
  have h3t1' :
      (weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0).coeff
          (-6 : ℚ) =
        (-8 / 9 : k) * A.coeff (-2 : ℚ) * B.coeff (-1 : ℚ) *
          F.coeff (-3 : ℚ) := by
    convert h3t1 using 1 <;> ring
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  constructor
  · rw [h4decH]
    simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68]
    rw [h4t1, h4t3, h4t4, h4l3, h4l5, h4l6, h4l7, h4l8]
    simp only [weightedMonomial68]
    simp only [mul_zero, zero_mul, neg_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero]
    simp only [rhoOneZeroLCubicExceptionalFour68]
    ring
  · rw [h3decH]
    simp only [HahnSeries.coeff_add, firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68]
    rw [h3t1', h3t2, h3t3, h3l2, h3l5, h3l6, h3l7, h3l8, h3l9,
      h3l10]
    simp only [weightedMonomial68]
    simp only [mul_zero, zero_mul, neg_zero]
    rw [hCzero]
    simp only [zero_mul, neg_zero, HahnSeries.coeff_zero]
    simp only [rhoOneZeroLCubicExceptionalThree68]
    ring

/-- Vanishing of the old `b,c` leading coefficients gives one additional
root factor in each of the cleared `B` and cubic-defect `C` coordinates. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_orders
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
      (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let C := rhoOneCDefectHahn68 A C0
    ((↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop) ∧
      ((↑(-2 : ℚ) : WithTop ℚ) ≤ C.orderTop) := by
  dsimp only at hb hc ⊢
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
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let CH := ratFuncAtHahn46 T.root C0R
  let CRH := ratFuncAtHahn46 T.root CR
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let Cdef0 : k[X] := C0 - C (1 / 3 : k) * A0 ^ 2
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  change algebraMap k[X] (RatFunc k) A0 = _ at hAclear
  change algebraMap k[X] (RatFunc k) B0 = _ at hBclear
  change algebraMap k[X] (RatFunc k) C0 = _ at hCclear
  have hB0root : B0.eval T.root = 0 := by
    simp [B0, localClearedB68RhoOne, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hCdef0root : Cdef0.eval T.root = 0 := by
    simp [Cdef0, C0, A0, localClearedC68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  obtain ⟨B1, hB1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 B0 T.root T.scale_degree T.root_eq hB0root
  obtain ⟨C1, hC1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Cdef0 T.root T.scale_degree T.root_eq hCdef0root
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR, C0R, AR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]; ring
  have hBclear1 : algebraMap k[X] (RatFunc k) B1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * BR := by
    have hcancel := algebraMap_cancel_factoredClearing
      h0 B0 B1 BR 1 2 1 T.scale_ne_zero (by simpa using hB1) (by
        simpa only [Nat.mul_one, show 2 + 1 = 3 by omega] using hBclear)
    simpa only [Nat.mul_one] using hcancel
  have hCclear1 : algebraMap k[X] (RatFunc k) C1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * CR := by
    have hcancel := algebraMap_cancel_factoredClearing
      h0 Cdef0 C1 CR 1 3 1 T.scale_ne_zero (by simpa using hC1) (by
        simpa only [Nat.mul_one, show 3 + 1 = 4 by omega] using hCdefclear)
    simpa only [Nat.mul_one] using hcancel
  have hCRmap : CRH = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CRH, CR, AH, CH, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hBco := localHahn_coeff_neg_of_cleared T.root cs h0 B1 BR 2
    hcs hsingle hBclear1
  have hCco := localHahn_coeff_neg_of_cleared T.root cs h0 C1 CR 3
    hcs hsingle hCclear1
  norm_num at hBco hCco
  have hB1root : B1.eval T.root = 0 := by
    change BH.coeff (-2 : ℚ) = _ at hBco
    rw [hb] at hBco
    exact (mul_eq_zero.mp hBco.symm).resolve_left
      (inv_ne_zero (pow_ne_zero 2 hcs))
  have hC1root : C1.eval T.root = 0 := by
    change CRH.coeff (-3 : ℚ) = _ at hCco
    rw [hCRmap, hc] at hCco
    exact (mul_eq_zero.mp hCco.symm).resolve_left
      (inv_ne_zero (pow_ne_zero 3 hcs))
  have hBorder := localHahn_orderTop_ge_one_better_of_cleared_root_zero
    T.root h0 B1 BR 2 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      T.scale_order hBclear1 hB1root
  have hCorder := localHahn_orderTop_ge_one_better_of_cleared_root_zero
    T.root h0 C1 CR 3 (by omega) T.scale_ne_zero T.scale_degree T.root_eq
      T.scale_order hCclear1 hC1root
  norm_num at hBorder hCorder
  change ((↑(-1 : ℚ) : WithTop ℚ) ≤ BH.orderTop) at hBorder
  change ((↑(-2 : ℚ) : WithTop ℚ) ≤ CRH.orderTop) at hCorder
  exact ⟨hBorder, by rw [← hCRmap]; exact hCorder⟩

/-- The first genuinely new invariant packet on the source component
`b = c = beta = 0`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_next
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
    (hbeta : T.source.beta = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicExceptionalFour68
      (B.coeff (-1 : ℚ)) (C.coeff (-2 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
    rhoOneZeroLCubicExceptionalThree68
      (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
      (C.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ))
      (G.coeff (-4 : ℚ)) = 0 := by
  have hBC := T.rhoOne_mainTangent_exceptional_orders
    hp hH hp6 hp5 hp4 P hb hc
  have hFG := T.rhoOne_mainTangent_defect_orders
    hp hH hp6 hp5 hp4 P hmain
  dsimp only at hb hc hBC hFG ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hA := hbounds.1
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 0 A B C0 D E
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [A, B, C0, D, E]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 0 A B C0 D E
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [A, B, C0, D, E]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  rw [hbeta] at hi4H' hi3H'
  have hthird : HahnSeries.C (1 / 3 : k) =
      (1 / 3 : HahnSeries ℚ k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_one]
    simp only [map_ofNat]
  have hCrec : A ^ 2 / 3 + C = C0 := by
    dsimp only [C, rhoOneCDefectHahn68]
    rw [hthird]
    ring
  have hDrec : A * B / 3 + F = D := by
    dsimp only [F, rhoOneTangentDDefectHahn68]
    simp only [map_mul, map_div₀, map_ofNat, map_one]
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = E := by
    dsimp only [G, ER, rhoOneTangentEDefectHahn68,
      rhoOneEDefectHahn68]
    simp only [map_mul, map_div₀, map_ofNat, map_one]
    ring
  have hformula := firstIntegral_mainTangent_exceptional_coeff68
    T.source.gamma T.source.delta T.source.epsilon T.source.zeta
      A B C F G hA hBC.1 hBC.2 hFG.1 hFG.2
  have h4coeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-5 : ℚ))
    hi4H'
  have h3coeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-6 : ℚ))
    hi3H'
  have h4const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-5 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-6 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [← hCrec, ← hDrec, ← hErec, hformula.1, h4const] at h4coeff
  rw [← hCrec, ← hDrec, ← hErec, hformula.2, h3const] at h3coeff
  constructor
  · exact (mul_eq_zero.mp h4coeff).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp h3coeff).resolve_left (by norm_num)

theorem rhoOneZeroLCubicExceptionalThree_forces_f_zero68
    (a b1 c1 f g : k)
    (hb1 : b1 = 0) (hc1 : c1 = 0)
    (h3 : rhoOneZeroLCubicExceptionalThree68 a b1 c1 f g = 0) :
    f = 0 := by
  have hf2 : f ^ 2 = 0 := by
    simp only [rhoOneZeroLCubicExceptionalThree68, hb1, hc1, mul_zero,
      zero_mul, neg_zero, add_zero] at h3
    linear_combination (1 / 3 : k) * h3
  exact eq_zero_of_pow_eq_zero hf2

/-- Eliminating the newly exposed `c1` and `b1` directions respectively. -/
theorem rhoOneZeroLCubicExceptional_next_elimination68
    (a b1 c1 f g : k)
    (h4 : rhoOneZeroLCubicExceptionalFour68 b1 c1 f g = 0)
    (h3 : rhoOneZeroLCubicExceptionalThree68 a b1 c1 f g = 0) :
    b1 * (2 * a * f ^ 2 + 6 * g ^ 2) = 3 * f ^ 3 ∧
    c1 * (2 * a * f ^ 2 + 6 * g ^ 2) = -3 * f ^ 2 * g := by
  simp only [rhoOneZeroLCubicExceptionalFour68] at h4
  simp only [rhoOneZeroLCubicExceptionalThree68] at h3
  constructor
  · linear_combination -(f * h3 - 6 * g * h4)
  · linear_combination g * h3 + 2 * a * f * h4

/-- A concrete descent inside the exceptional component: if both newly
exposed `B,C` coefficients vanish, then the leading tangent defect `f`
vanishes as well. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_f_zero
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
    let C := rhoOneCDefectHahn68 A C0
    let F := rhoOneTangentDDefectHahn68 A B D
    F.coeff (-3 : ℚ) = 0 := by
  have hnext := T.rhoOne_mainTangent_exceptional_next
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta
  dsimp only at hb1 hc1 hnext ⊢
  exact rhoOneZeroLCubicExceptionalThree_forces_f_zero68 _ _ _ _ _
    hb1 hc1 hnext.2

end AlignedSquareRhoOneCubicMainTangentNextCoefficient68

end Max11DegreeRoutes
