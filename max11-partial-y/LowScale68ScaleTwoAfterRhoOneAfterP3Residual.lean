import LowScale68ScaleTwoAfterRhoOneAfterP3
import LowScale68Expansion

/-! # Eliminating the divisible branch after the `(0,0,1,1,1)` box

If the first branch has `h² ∣ p₂`, then `C` becomes regular.  The preceding
third-integral face consequently has the unique term `(4/3)D₋₁²`, forcing
`h ∣ p₁`.  At that point all five depressed coordinates have polynomial
representatives, contradicting the simple pole of the Keller terminal in the
row-zero identity.  Thus only the explicit nonzero residual survives.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterP3Residual68

variable {k : Type*} [Field k] [CharZero k]

local instance afterP3ResidualHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def localClearedC68AfterP2Two (g u v s : k[X]) : k[X] :=
  s - C (1 / 2 : k) * v * g + C (1 / 6 : k) * u * g ^ 2 -
    C (5 / 144 : k) * g ^ 4

theorem SquareConstantLIntegratedLocalRootData68.coordinateCOrderAfterP2Two
    {p q : k[X][X]} {j l : k} {h0 H g u v s : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 ^ 2 * s) :
    (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.C0).orderTop := by
  have hp2' : p.coeff 2 = h0 * (h0 * s) := by rw [hp2]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesAfterP3
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3 hp2'
  let C0 := localClearedC68AfterP2Two g u v s
  have hfC : localClearedC68AfterP3 h0 g u v (h0 * s) = h0 * C0 := by
    simp only [localClearedC68AfterP3, C0, localClearedC68AfterP2Two]
    ring
  have hclear : algebraMap k[X] (RatFunc k) C0 = T.source.C0 := by
    have hc := algebraMap_cancel_factoredClearing h0 _ C0 T.source.C0
      1 0 1 T.scale_ne_zero (by simpa using hfC)
        (by convert hC using 1 <;> norm_num)
    simpa only [C0, Nat.zero_mul, pow_zero, one_mul] using hc
  exact localHahn_orderTop_ge_of_cleared T.root h0 C0 T.source.C0 0
    T.scale_order (by simpa using hclear)

theorem SquareConstantLIntegratedLocalRootData68.afterP2Two_forces_p1
    {p q : k[X][X]} {j l : k} {h0 H g u v s : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 ^ 2 * s) :
    h0 ∣ p.coeff 1 := by
  have hp2' : p.coeff 2 = h0 * (h0 * s) := by rw [hp2]; ring
  obtain ⟨hfour, hthree⟩ := T.afterP3_integralFaces
    hp hH hp6 hp5 hp4 hp3 hp2'
  have hC := T.coordinateCOrderAfterP2Two hp hH hp6 hp5 hp4 hp3 hp2
  have hCco : (ratFuncAtHahn46 T.root T.source.C0).coeff (-1 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have hC' : (↑(0 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.C0).orderTop := by
      convert hC using 1 <;> norm_num
    exact (WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℚ) < 0)).trans_le hC'
  obtain ⟨c, hc, hAco, hCcoOld, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterP3 hp hH hp6 hp5 hp4 hp3 hp2'
  rw [hCco] at hthree
  simp only [afterP3ThreeFace68] at hthree
  have hDzero : (ratFuncAtHahn46 T.root T.source.D).coeff (-1 : ℚ) = 0 := by
    have hsq : (ratFuncAtHahn46 T.root T.source.D).coeff (-1 : ℚ) ^ 2 = 0 := by
      linear_combination (3 / 4 : k) * hthree
    exact eq_zero_of_pow_eq_zero hsq
  rw [hDco] at hDzero
  simp only [eval_mul, T.root_eq, zero_mul, mul_zero, sub_zero, zero_add] at hDzero
  have hp1root : (p.coeff 1).eval T.root = 0 :=
    (mul_eq_zero.mp hDzero).resolve_left (inv_ne_zero hc)
  exact linearPolynomial_dvd_of_eval_eq_zero h0 (p.coeff 1) T.root
    T.scale_degree T.root_eq hp1root

def localClearedD68AfterP2P1 (g u v s t : k[X]) : k[X] :=
  t - C (1 / 3 : k) * s * g + C (1 / 12 : k) * v * g ^ 2 -
    C (1 / 54 : k) * u * g ^ 3 + C (1 / 324 : k) * g ^ 5

def localClearedE68AfterP2P1
    (g u v s t a0 : k[X]) : k[X] :=
  a0 - C (1 / 6 : k) * t * g + C (1 / 36 : k) * s * g ^ 2 -
    C (1 / 216 : k) * v * g ^ 3 + C (1 / 1296 : k) * u * g ^ 4 -
    C (5 / 46656 : k) * g ^ 6

set_option maxHeartbeats 800000 in
theorem SquareConstantLIntegratedSourceData68.polynomialCoordinatesAfterP2P1
    {p q : k[X][X]} {j l : k} {h0 H g u v s t : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 ^ 2 * s) (hp1 : p.coeff 1 = h0 * t) :
    algebraMap k[X] (RatFunc k) (localClearedA68AfterP4 g u) = S.A ∧
    algebraMap k[X] (RatFunc k) (localClearedB68AfterP3 g u v) = S.B ∧
    algebraMap k[X] (RatFunc k) (localClearedC68AfterP2Two g u v s) = S.C0 ∧
    algebraMap k[X] (RatFunc k) (localClearedD68AfterP2P1 g u v s t) = S.D ∧
    algebraMap k[X] (RatFunc k)
      (localClearedE68AfterP2P1 g u v s t (p.coeff 0)) = S.E := by
  have hp2' : p.coeff 2 = h0 * (h0 * s) := by rw [hp2]; ring
  obtain ⟨hA, hB, hC, hD, hE⟩ := S.clearedCoordinatesAfterP3
    hp hh0 hH hp6 hp5 hp4 hp3 hp2'
  let C0 := localClearedC68AfterP2Two g u v s
  let D0 := localClearedD68AfterP2P1 g u v s t
  let E0 := localClearedE68AfterP2P1 g u v s t (p.coeff 0)
  have hfC : localClearedC68AfterP3 h0 g u v (h0 * s) = h0 * C0 := by
    simp only [localClearedC68AfterP3, C0, localClearedC68AfterP2Two]
    ring
  have hfD : localClearedD68AfterP3 h0 g u v (h0 * s) (p.coeff 1) =
      h0 * D0 := by
    rw [hp1]
    simp only [localClearedD68AfterP3, D0, localClearedD68AfterP2P1]
    ring
  have hfE : localClearedE68AfterP3 h0 g u v (h0 * s) (p.coeff 1)
      (p.coeff 0) = h0 * E0 := by
    rw [hp1]
    simp only [localClearedE68AfterP3, E0, localClearedE68AfterP2P1]
    ring
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · have hc := algebraMap_cancel_factoredClearing h0 _ C0 S.C0
      1 0 1 hh0 (by simpa using hfC) (by convert hC using 1 <;> norm_num)
    simpa only [C0, Nat.zero_mul, pow_zero, one_mul] using hc
  · have hd := algebraMap_cancel_factoredClearing h0 _ D0 S.D
      1 0 1 hh0 (by simpa using hfD) (by convert hD using 1 <;> norm_num)
    simpa only [D0, Nat.zero_mul, pow_zero, one_mul] using hd
  · have he := algebraMap_cancel_factoredClearing h0 _ E0 S.E
      1 0 1 hh0 (by simpa using hfE) (by convert hE using 1 <;> norm_num)
    simpa only [E0, Nat.zero_mul, pow_zero, one_mul] using he

/-- A fully regular depressed coordinate tuple cannot have the row-zero
Keller terminal `j/h`, whose local order is exactly `-1`. -/
theorem SquareConstantLIntegratedLocalRootData68.afterP2P1_impossible
    {p q : k[X][X]} {j l : k} {h0 H g u v s t : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 ^ 2 * s) (hp1 : p.coeff 1 = h0 * t) : False := by
  let A0 := localClearedA68AfterP4 g u
  let B0 := localClearedB68AfterP3 g u v
  let C0 := localClearedC68AfterP2Two g u v s
  let D0 := localClearedD68AfterP2P1 g u v s t
  let E0 := localClearedE68AfterP2P1 g u v s t (p.coeff 0)
  obtain ⟨hA0, hB0, hC0, hD0, hE0⟩ := T.source.polynomialCoordinatesAfterP2P1
    hp T.scale_ne_zero hH hp6 hp5 hp4 hp3 hp2 hp1
  let U0 := integratedUPolynomial68 l T.source.alpha T.source.beta
    T.source.gamma T.source.delta T.source.zeta A0 B0 C0 D0 E0
  let V0 := integratedVPolynomial68 l T.source.alpha T.source.beta
    T.source.gamma T.source.delta T.source.epsilon T.source.eta
      A0 B0 C0 D0 E0
  have hUmap : algebraMap k[X] (RatFunc k) U0 =
      integratedU68 (RatFunc.C l) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta) := by
    dsimp only [U0]
    rw [algebraMap_integratedUPolynomial68, hA0, hB0, hC0, hD0, hE0]
  have hVmap : algebraMap k[X] (RatFunc k) V0 =
      integratedV68 (RatFunc.C l) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
        (RatFunc.C T.source.eta) := by
    dsimp only [V0]
    rw [algebraMap_integratedVPolynomial68, hA0, hB0, hC0, hD0, hE0]
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C l) T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst l) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  have hrowR := hlow.2.2.2.2
  let R0 := lowerRowZeroPolynomial68 U0 V0 D0 E0
  have hRmap : algebraMap k[X] (RatFunc k) R0 =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    dsimp only [R0]
    rw [algebraMap_lowerRowZeroPolynomial68, hUmap, hVmap, hD0, hE0]
    exact hrowR
  have hrowH := congrArg (ratFuncAtHahn46 T.root) hRmap
  have horder := congrArg HahnSeries.orderTop hrowH
  have hnonneg := ratFuncAtHahn46_polynomial_orderTop_nonneg T.root R0
  rw [horder, T.terminal_order] at hnonneg
  have hbad : (↑(0 : ℚ) : WithTop ℚ) ≤ ↑(-1 : ℚ) := by
    convert hnonneg using 1 <;> norm_num
  exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℚ) < 0))) hbad

/-- The divisible face is impossible, so the explicit nonzero residual is
the only survivor of the post-`p₃` box. -/
theorem SquareConstantLIntegratedLocalRootData68.afterP3_residual_forced
    {p q : k[X][X]} {j l : k} {h0 H g u v w : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 4 * u) (hp3 : p.coeff 3 = h0 ^ 3 * v)
    (hp2 : p.coeff 2 = h0 * w) :
    AfterP3NonzeroResidual68 T g u w := by
  rcases T.afterP3_face_dichotomy hp hH hp6 hp5 hp4 hp3 hp2 with hdiv | hres
  · obtain ⟨s, hp2two⟩ := hdiv
    obtain ⟨t, hp1⟩ := T.afterP2Two_forces_p1
      hp hH hp6 hp5 hp4 hp3 hp2two
    exact (T.afterP2P1_impossible hp hH hp6 hp5 hp4 hp3 hp2two hp1).elim
  · exact hres

/-- Original-data residual packet after eliminating the fully divisible
branch. -/
theorem SquareConstantLIntegratedLocalRootData68.afterP3_global_residual
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u v w : k[X],
      p.coeff 5 = h0 ^ 5 * g ∧ p.coeff 4 = h0 ^ 4 * u ∧
      p.coeff 3 = h0 ^ 3 * v ∧ p.coeff 2 = h0 * w ∧
      AfterP3NonzeroResidual68 T g u w := by
  rcases T.afterP3_global_packet hp hH hp6 with
    ⟨g, u, v, w, hp5, hp4, hp3, hp2, hpacket⟩
  refine ⟨g, u, v, w, hp5, hp4, hp3, hp2, ?_⟩
  exact T.afterP3_residual_forced hp hH hp6 hp5 hp4 hp3 hp2

end AfterP3Residual68

end Max11DegreeRoutes
