import LowScale68ScaleTwoAfterRhoOneImprovedDefectRowOne

/-! # The box after `h⁴ ∣ p₄`

Writing `p₅=h⁵g`, `p₄=h⁴u`, and `p₃=h²v` changes the depressed
box to `(0,1,2,2,2)`.  Three exact faces first force `h ∣ p₂`; the
resulting `(0,1,1,1,1)` box then has a unique `B³` face and forces
`h³ ∣ p₃`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneAfterP468

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneAfterP4HahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedA68AfterP4 (g u : k[X]) : k[X] :=
  u - C (5 / 12 : k) * g ^ 2

def localClearedB68AfterP4 (h g u v : k[X]) : k[X] :=
  v - C (2 / 3 : k) * h * u * g + C (5 / 27 : k) * h * g ^ 3

def localClearedC68AfterP4 (h g u v a2 : k[X]) : k[X] :=
  a2 - C (1 / 2 : k) * h * v * g + C (1 / 6 : k) * h ^ 2 * u * g ^ 2 -
    C (5 / 144 : k) * h ^ 2 * g ^ 4

def localClearedD68AfterP4 (h g u v a2 a1 : k[X]) : k[X] :=
  a1 * h - C (1 / 3 : k) * a2 * g + C (1 / 12 : k) * h * v * g ^ 2 -
    C (1 / 54 : k) * h ^ 2 * u * g ^ 3 + C (1 / 324 : k) * h ^ 2 * g ^ 5

def localClearedE68AfterP4
    (h g u v a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 2 - C (1 / 6 : k) * a1 * g * h +
    C (1 / 36 : k) * a2 * g ^ 2 - C (1 / 216 : k) * h * v * g ^ 3 +
    C (1 / 1296 : k) * h ^ 2 * u * g ^ 4 -
    C (5 / 46656 : k) * h ^ 2 * g ^ 6

set_option maxHeartbeats 800000 in
theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterP4
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k) (localClearedA68AfterP4 g u) = S.A ∧
    algebraMap k[X] (RatFunc k) (localClearedB68AfterP4 h0 g u v) = h * S.B ∧
    algebraMap k[X] (RatFunc k)
      (localClearedC68AfterP4 h0 g u v (p.coeff 2)) = h ^ 2 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
      (localClearedD68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1)) =
        h ^ 2 * S.D ∧
    algebraMap k[X] (RatFunc k)
      (localClearedE68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1)
        (p.coeff 0)) = h ^ 2 * S.E := by
  dsimp only
  have hp4' : p.coeff 4 = h0 ^ 3 * (h0 * u) := by rw [hp4]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ := S.clearedCoordinatesAfterRhoOneNext
    hp hh0 hH hp6 hp5 hp4' hp3
  let A0 := localClearedA68AfterP4 g u
  have hfA : localClearedA68AfterRhoOne h0 g (h0 * u) = h0 * A0 := by
    simp only [localClearedA68AfterRhoOne, A0, localClearedA68AfterP4]
    ring
  change algebraMap k[X] (RatFunc k)
    (localClearedA68AfterRhoOne h0 g (h0 * u)) = _ at hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hcancel := algebraMap_cancel_factoredClearing h0 _ A0 S.A
      1 0 1 hh0 (by simpa using hfA) hA
    simpa only [A0, Nat.zero_mul, pow_zero, one_mul] using hcancel
  · simpa only [localClearedB68AfterP4,
      localClearedB68AfterRhoOneNext, pow_one, mul_assoc] using hB
  · convert hC using 1 <;>
      simp only [localClearedC68AfterP4,
        localClearedC68AfterRhoOneNext] <;> ring
  · convert hD using 1 <;>
      simp only [localClearedD68AfterP4,
        localClearedD68AfterRhoOneNext] <;> ring
  · convert hE using 1 <;>
      simp only [localClearedE68AfterP4,
        localClearedE68AfterRhoOneNext] <;> ring

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterP4
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP4
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterP4 g u) T.source.A 0 T.scale_order (by simpa using hA),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterP4 h0 g u v) T.source.B 1 T.scale_order (by simpa using hB),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterP4 h0 g u v (p.coeff 2)) T.source.C0 2
      T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1)) T.source.D 2
      T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1) (p.coeff 0))
      T.source.E 2 T.scale_order hE⟩

theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialPacketAfterP4
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-1 : ℚ) =
        c⁻¹ * v.eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (p.coeff 2).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * (-(1 / 3 : k) * (p.coeff 2).eval T.root *
          g.eval T.root) ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-2 : ℚ) =
        (c ^ 2)⁻¹ * ((1 / 36 : k) * (p.coeff 2).eval T.root *
          g.eval T.root ^ 2) := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP4
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3
  have hBco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedB68AfterP4 h0 g u v) T.source.B 1 hc hsingle (by simpa using hB)
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedC68AfterP4 h0 g u v (p.coeff 2)) T.source.C0 2 hc hsingle hC
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedD68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1)) T.source.D 2
      hc hsingle hD
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedE68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1) (p.coeff 0))
      T.source.E 2 hc hsingle hE
  norm_num at hBco hCco hDco hEco
  refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
  · rw [hBco]
    simp [localClearedB68AfterP4, T.root_eq]
  · rw [hCco]
    simp [localClearedC68AfterP4, T.root_eq]
  · rw [hDco]
    simp [localClearedD68AfterP4, T.root_eq]
  · rw [hEco]
    simp [localClearedE68AfterP4, T.root_eq]

/-- Once the fourth coefficient has gained its fourth scale factor, the
row-one face of the preceding box has only its cubic `C₀` term left. -/
theorem SquareConstantLIntegratedLocalRootData68.afterP4_forces_p2
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    h0 ∣ p.coeff 2 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let CH := ratFuncAtHahn46 T.root T.source.C0
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterP4 hp hH hp6 hp5 hp4 hp3
  have hAco : AH.coeff (-1 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have hA' : (↑(0 : ℚ) : WithTop ℚ) ≤ AH.orderTop := by
      dsimp only [AH]
      convert hA using 1 <;> norm_num
    exact (WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℚ) < 0)).trans_le hA'
  have hp4' : p.coeff 4 = h0 ^ 3 * (h0 * u) := by rw [hp4]; ring
  have hrow := T.afterRhoOneNext_rowOneFace
    hp hH hp6 hp5 hp4' hp3
  dsimp only at hrow
  change afterRhoOneNextRowOneFace68 (AH.coeff (-1 : ℚ))
    (CH.coeff (-2 : ℚ)) = 0 at hrow
  rw [hAco, afterRhoOneNextRowOneFace68] at hrow
  have hCzero : CH.coeff (-2 : ℚ) = 0 := by
    have hcubed : CH.coeff (-2 : ℚ) ^ 3 = 0 := by
      linear_combination (9 / 2 : k) * hrow
    exact eq_zero_of_pow_eq_zero hcubed
  obtain ⟨c, hc, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterP4 hp hH hp6 hp5 hp4 hp3
  change (ratFuncAtHahn46 T.root T.source.C0).coeff (-2 : ℚ) = 0 at hCzero
  rw [hCco] at hCzero
  have hp2root : (p.coeff 2).eval T.root = 0 :=
    (mul_eq_zero.mp hCzero).resolve_left (inv_ne_zero (pow_ne_zero 2 hc))
  exact linearPolynomial_dvd_of_eval_eq_zero h0 (p.coeff 2) T.root
    T.scale_degree T.root_eq hp2root

def localClearedC68AfterP4P2 (h g u v w : k[X]) : k[X] :=
  w - C (1 / 2 : k) * v * g + C (1 / 6 : k) * h * u * g ^ 2 -
    C (5 / 144 : k) * h * g ^ 4

def localClearedD68AfterP4P2
    (h g u v w a1 : k[X]) : k[X] :=
  a1 - C (1 / 3 : k) * w * g + C (1 / 12 : k) * v * g ^ 2 -
    C (1 / 54 : k) * h * u * g ^ 3 + C (1 / 324 : k) * h * g ^ 5

def localClearedE68AfterP4P2
    (h g u v w a1 a0 : k[X]) : k[X] :=
  a0 * h - C (1 / 6 : k) * a1 * g + C (1 / 36 : k) * w * g ^ 2 -
    C (1 / 216 : k) * v * g ^ 3 + C (1 / 1296 : k) * h * u * g ^ 4 -
    C (5 / 46656 : k) * h * g ^ 6

set_option maxHeartbeats 800000 in
theorem SquareConstantLIntegratedSourceData68.clearedCoordinatesAfterP4P2
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k) (localClearedA68AfterP4 g u) = S.A ∧
    algebraMap k[X] (RatFunc k) (localClearedB68AfterP4 h0 g u v) = h * S.B ∧
    algebraMap k[X] (RatFunc k) (localClearedC68AfterP4P2 h0 g u v w) =
        h * S.C0 ∧
    algebraMap k[X] (RatFunc k)
      (localClearedD68AfterP4P2 h0 g u v w (p.coeff 1)) = h * S.D ∧
    algebraMap k[X] (RatFunc k)
      (localClearedE68AfterP4P2 h0 g u v w (p.coeff 1) (p.coeff 0)) =
        h * S.E := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ := S.clearedCoordinatesAfterP4
    hp hh0 hH hp6 hp5 hp4 hp3
  let C1 := localClearedC68AfterP4P2 h0 g u v w
  let D1 := localClearedD68AfterP4P2 h0 g u v w (p.coeff 1)
  let E1 := localClearedE68AfterP4P2 h0 g u v w (p.coeff 1) (p.coeff 0)
  have hfC : localClearedC68AfterP4 h0 g u v (p.coeff 2) = h0 * C1 := by
    rw [hp2]
    simp only [localClearedC68AfterP4, C1, localClearedC68AfterP4P2]
    ring
  have hfD : localClearedD68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1) =
      h0 * D1 := by
    rw [hp2]
    simp only [localClearedD68AfterP4, D1, localClearedD68AfterP4P2]
    ring
  have hfE : localClearedE68AfterP4 h0 g u v (p.coeff 2) (p.coeff 1)
      (p.coeff 0) = h0 * E1 := by
    rw [hp2]
    simp only [localClearedE68AfterP4, E1, localClearedE68AfterP4P2]
    ring
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · have hc := algebraMap_cancel_factoredClearing h0 _ C1 S.C0
      1 1 1 hh0 (by simpa using hfC) hC
    simpa only [C1, Nat.mul_one, pow_one] using hc
  · have hd := algebraMap_cancel_factoredClearing h0 _ D1 S.D
      1 1 1 hh0 (by simpa using hfD) hD
    simpa only [D1, Nat.mul_one, pow_one] using hd
  · have he := algebraMap_cancel_factoredClearing h0 _ E1 S.E
      1 1 1 hh0 (by simpa using hfE) hE
    simpa only [E1, Nat.mul_one, pow_one] using he

theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBoundsAfterP4P2
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.A).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.C0).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.D).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root T.source.E).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP4P2
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3 hp2
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68AfterP4 g u) T.source.A 0 T.scale_order
        (by simpa using hA),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68AfterP4 h0 g u v) T.source.B 1 T.scale_order
        (by simpa only [pow_one] using hB),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68AfterP4P2 h0 g u v w) T.source.C0 1 T.scale_order
        (by simpa only [pow_one] using hC),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68AfterP4P2 h0 g u v w (p.coeff 1)) T.source.D 1
        T.scale_order (by simpa only [pow_one] using hD),
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68AfterP4P2 h0 g u v w (p.coeff 1) (p.coeff 0))
        T.source.E 1 T.scale_order (by simpa only [pow_one] using hE)⟩

/-- At the `(0,1,1,1,1)` box, the coefficient at weight `-3` of the
fourth exact integral is the single monomial `-(8/27)B³`. -/
theorem firstIntegralFour68_coeff_neg3_afterP4P2
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-1 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-1 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-1 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-3 : ℚ) =
      (-8 / 27 : k) * (B.coeff (-1 : ℚ)) ^ 3 := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-3 : ℚ) < (aA : ℚ) * 0 + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-1) + (aD : ℚ) * (-1) + (aE : ℚ) * (-1)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-3 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE 0 (-1) (-1) (-1) (-1) (-3)
      hA hB hC hD hE hlt
  have hlead := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A B C0 D E 0 3 0 0 0 0 (-1) (-1) (-1) (-1)
      hA hB hC hD hE
  have ht1 :
      (weightedMonomial68 (-8 / 27 : k) A B C0 D E 0 3 0 0 0).coeff
          (-3 : ℚ) = (-8 / 27 : k) * (B.coeff (-1 : ℚ)) ^ 3 := by
    convert hlead using 1 <;> norm_num
  have ht2 := hzero (-8 / 9 : k) 2 0 0 1 0 (by norm_num)
  have ht3 := hzero (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have ht4 := hzero (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht5 := hzero (40 / 81 : k) 3 1 0 0 0 (by norm_num)
  have ht6 := hzero (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have hh1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have hh6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hh7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh8 := hzero ((7 / 12 : k) * L) 0 0 2 0 0 (by norm_num)
  have hh9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hh10 := hzero ((385 / 5184 : k) * L) 4 0 0 0 0 (by norm_num)
  have hh11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have hh12 := hzero (-(35 / 72 : k) * L) 2 0 1 0 0 (by norm_num)
  have hh13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hh14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have hh15 := hzero ((7 / 6 : k) * L) 1 0 0 0 1 (by norm_num)
  have hh16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  rw [firstIntegralFour68_eq_localFaces]
  simp only [firstIntegralFourTopFaceHahn68,
    firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
  rw [ht1, ht2, ht3, ht4, ht5, ht6, hh1, hh2, hh3, hh4, hh5, hh6,
    hh7, hh8, hh9, hh10, hh11, hh12, hh13, hh14, hh15, hh16]
  norm_num

theorem SquareConstantLIntegratedLocalRootData68.afterP4P2_B_zero
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    (ratFuncAtHahn46 T.root T.source.B).coeff (-1 : ℚ) = 0 := by
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterP4P2 hp hH hp6 hp5 hp4 hp3 hp2
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
  have hcoeff := congrArg
    (fun z : HahnSeries ℚ k => z.coeff (-3 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-3 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_neg3_afterP4P2
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
  rw [hface] at hcoeff
  have hcube : BH.coeff (-1 : ℚ) ^ 3 = 0 := by
    apply (mul_eq_zero.mp hcoeff).resolve_left
    norm_num
  simpa only [BH] using (eq_zero_of_pow_eq_zero hcube)

theorem SquareConstantLIntegratedLocalRootData68.afterP4P2_forces_p3
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    h0 ^ 3 ∣ p.coeff 3 := by
  have hBzero := T.afterP4P2_B_zero hp hH hp6 hp5 hp4 hp3 hp2
  obtain ⟨c, hc, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterP4 hp hH hp6 hp5 hp4 hp3
  rw [hBco] at hBzero
  have hvroot : v.eval T.root = 0 :=
    (mul_eq_zero.mp hBzero).resolve_left (inv_ne_zero hc)
  obtain ⟨t, hvt⟩ := linearPolynomial_dvd_of_eval_eq_zero h0 v T.root
    T.scale_degree T.root_eq hvroot
  refine ⟨t, ?_⟩
  rw [hp3, hvt]
  ring

/-- Original-data checkpoint: the post-`p₄` box forces one more scale
factor into `p₃` (and, en route, one scale factor into `p₂`). -/
theorem SquareConstantLIntegratedLocalRootData68.afterP4_global_descend
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ p.coeff 4 ∧
      h0 ^ 3 ∣ p.coeff 3 := by
  rcases T.afterRhoOne_rowOne_global_descend hp hH hp6 with
    ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ⟨v, hp3⟩⟩
  obtain ⟨w, hp2⟩ := T.afterP4_forces_p2 hp hH hp6 hp5 hp4 hp3
  have hp3' := T.afterP4P2_forces_p3 hp hH hp6 hp5 hp4 hp3 hp2
  exact ⟨⟨g, hp5⟩, ⟨u, hp4⟩, hp3'⟩

end AfterRhoOneAfterP468

end Max11DegreeRoutes
