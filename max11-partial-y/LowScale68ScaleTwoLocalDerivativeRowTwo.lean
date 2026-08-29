import LowScale68ScaleTwoLocalRowThree

/-! # Derivative bridge and the third local face for `(6,8)`

The first new ingredient is an exact coefficient-level compatibility of
the finite-place embedding with rational differentiation, specialized only
by an explicit polynomial denominator clearing.  This is the generality
needed by all five depressed sextic coordinates.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalDerivative68

variable {k : Type*} [Field k] [CharZero k]

local instance localDerivativeHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Exact finite-place derivative coefficient bridge.  If `h` is the
local monomial `c t` and `h^n A` is polynomial, then the coefficient of
`A'` one exponent below the boundary is the formal derivative of the
boundary monomial. -/
theorem localHahn_deriv_coeff_neg_succ_of_cleared
    (a c : k) (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ) (hc : c ≠ 0)
    (hsingle :
      ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c)
    (hderiv :
      ratFuncAtHahn46 a
          (Differential.deriv (algebraMap k[X] (RatFunc k) h0)) =
        HahnSeries.C c)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A) :
    (ratFuncAtHahn46 a (Differential.deriv A)).coeff
        (-(n : ℚ) - 1) =
      -(n : k) * (ratFuncAtHahn46 a A).coeff (-(n : ℚ)) := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a A
  let dAH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (Differential.deriv A)
  have hdclear := congrArg Differential.deriv hclear
  rw [GCD369RatFuncDerivative] at hdclear
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hdclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hdclear
  have hmapped' :
      ratFuncAtHahn46 a
          (algebraMap k[X] (RatFunc k) A0.derivative) =
        (HahnSeries.single (1 : ℚ) c) ^ n * dAH +
          AH * ((n : HahnSeries ℚ k) *
            ((HahnSeries.single (1 : ℚ) c) ^ (n - 1) * HahnSeries.C c)) := by
    dsimp only [h, AH, dAH]
    simpa only [map_add, map_mul, map_pow, map_natCast, hsingle, hderiv]
      using hmapped
  have hmapped'' :
      ratFuncAtHahn46 a
          (algebraMap k[X] (RatFunc k) A0.derivative) =
        (HahnSeries.single (1 : ℚ) c) ^ n * dAH +
          (HahnSeries.single (1 : ℚ) c) ^ (n - 1) *
            (HahnSeries.C ((n : k) * c) * AH) := by
    rw [hmapped']
    simp only [map_mul, map_natCast]
    ring
  have hleftOrder : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a
        (algebraMap k[X] (RatFunc k) A0.derivative)).orderTop :=
    ratFuncAtHahn46_polynomial_orderTop_nonneg a A0.derivative
  have hleftCoeff :
      (ratFuncAtHahn46 a
        (algebraMap k[X] (RatFunc k) A0.derivative)).coeff (-1 : ℚ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr (by norm_num)).trans_le hleftOrder)
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-1 : ℚ)) hmapped''
  rw [hleftCoeff, HahnSeries.coeff_add] at hcoeff
  simp only [HahnSeries.single_pow, HahnSeries.coeff_single_mul,
    HahnSeries.C_apply, nsmul_eq_mul] at hcoeff
  cases n with
  | zero =>
      norm_num at hcoeff ⊢
      exact hcoeff.symm
  | succ m =>
      have hpow : c ^ (m + 1) ≠ 0 := pow_ne_zero (m + 1) hc
      have hcoeff' : 0 =
          c ^ (m + 1) * dAH.coeff (-(m + 1 : ℕ) - 1) +
            c ^ (m + 1) * (m + 1 : k) *
              AH.coeff (-(m + 1 : ℕ)) := by
        convert hcoeff using 1 <;>
          norm_num [Nat.cast_succ, pow_succ] <;> ring
      have hfac : c ^ (m + 1) *
          (dAH.coeff (-(m + 1 : ℕ) - 1) +
            (m + 1 : k) * AH.coeff (-(m + 1 : ℕ))) = 0 := by
        calc
          c ^ (m + 1) *
              (dAH.coeff (-(m + 1 : ℕ) - 1) +
                (m + 1 : k) * AH.coeff (-(m + 1 : ℕ))) =
              c ^ (m + 1) * dAH.coeff (-(m + 1 : ℕ) - 1) +
                c ^ (m + 1) * (m + 1 : k) *
                  AH.coeff (-(m + 1 : ℕ)) := by ring
          _ = 0 := hcoeff'.symm
      have hsum := (mul_eq_zero.mp hfac).resolve_left hpow
      have heq : dAH.coeff (-(m + 1 : ℕ) - 1) =
          -(m + 1 : k) * AH.coeff (-(m + 1 : ℕ)) := by
        linear_combination hsum
      simpa only [AH, dAH, Nat.cast_succ] using heq

/-- A linear local scale and its rational derivative map respectively to
`c t` and the constant `c`. -/
theorem ratFuncAtHahn68_linearRoot_single_deriv
    (h0 : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) :
    ∃ c : k, c ≠ 0 ∧
      ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c ∧
      ratFuncAtHahn46 a
          (Differential.deriv (algebraMap k[X] (RatFunc k) h0)) =
        HahnSeries.C c := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by
    simpa [← hlinear] using hroot
  have hcomp : h0.comp (X + C a) = C c * X := by
    apply Polynomial.funext
    intro x
    rw [← hlinear]
    simp only [Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hca
  refine ⟨c, hc, ?_, ?_⟩
  · rw [ratFuncAtHahn46_algebraMap, hcomp, map_mul]
    simp [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
  · rw [GCD369RatFuncDerivative, ← hlinear]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X, mul_one, mul_zero,
      add_zero]
    simp [ratFuncAtHahn46_C, RatFunc.algebraMap_C]

/-- The five exact derivative boundary coefficients of a square-source
local package. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateDerivativeInitialCoeffs
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff
        (-11 : ℚ) =
      (-10 : k) * (ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.B)).coeff
        (-16 : ℚ) =
      (-15 : k) * (ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.C0)).coeff
        (-21 : ℚ) =
      (-20 : k) * (ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.D)).coeff
        (-26 : ℚ) =
      (-25 : k) * (ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ) ∧
    (ratFuncAtHahn46 T.root (Differential.deriv T.source.E)).coeff
        (-31 : ℚ) =
      (-30 : k) * (ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ) := by
  obtain ⟨c, hc, hsingle, hderiv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0 (localClearedA68 h0 (p.coeff 5) (p.coeff 4))
      T.source.A 10 hc hsingle hderiv hA using 1 <;> norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 hc hsingle hderiv hB using 1 <;> norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 hc hsingle hderiv hC using 1 <;> norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 hc hsingle hderiv hD using 1 <;>
      norm_num
  · convert localHahn_deriv_coeff_neg_succ_of_cleared
      T.root c h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30 hc
        hsingle hderiv hE using 1 <;> norm_num

/-- Differentiating an `h^n` denominator clearing produces an
`h^(n+1)` clearing for the derivative. -/
theorem algebraMap_localDerivativeCleared
    (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A) :
    algebraMap k[X] (RatFunc k)
        (h0 * A0.derivative - C (n : k) * h0.derivative * A0) =
      (algebraMap k[X] (RatFunc k) h0) ^ (n + 1) *
        Differential.deriv A := by
  have hdclear := congrArg Differential.deriv hclear
  rw [GCD369RatFuncDerivative] at hdclear
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hdclear
  simp only [map_sub, map_mul, RatFunc.algebraMap_C,
    GCD369RatFuncDerivative]
  rw [← GCD369RatFuncDerivative h0]
  have hnC : RatFunc.C (n : k) = (n : RatFunc k) := by
    simp only [← map_natCast (RatFunc.C : k →+* RatFunc k)]
  rw [hclear, hdclear]
  rw [hnC]
  cases n with
  | zero => simp
  | succ m =>
      simp only [Nat.cast_succ, Nat.add_sub_cancel, Nat.one_add,
        Nat.succ_sub_one]
      ring

/-- A cleared rational coordinate has derivative order at least one below
its original cleared boundary. -/
theorem localHahn_deriv_orderTop_ge_of_cleared
    (a : k) (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ)
    (hscale :
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ))
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A) :
    (↑(-((n + 1 : ℕ) : ℚ)) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv A)).orderTop := by
  let dA0 : k[X] :=
    h0 * A0.derivative - C (n : k) * h0.derivative * A0
  apply localHahn_orderTop_ge_of_cleared a h0 dA0
    (Differential.deriv A) (n + 1) hscale
  dsimp only [dA0]
  exact algebraMap_localDerivativeCleared h0 A0 A n hclear

/-- The exact derivative Newton box for the five depressed coordinates. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateDerivativeOrderBounds
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    (↑(-11 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.A)).orderTop ∧
    (↑(-16 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.B)).orderTop ∧
    (↑(-21 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.C0)).orderTop ∧
    (↑(-26 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.D)).orderTop ∧
    (↑(-31 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root
          (Differential.deriv T.source.E)).orderTop := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) T.source.A 10
      T.scale_order hA using 1 <;> norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 T.scale_order hB using 1 <;> norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 T.scale_order hC using 1 <;> norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 T.scale_order hD using 1 <;>
      norm_num
  · convert localHahn_deriv_orderTop_ge_of_cleared T.root h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30
      T.scale_order hE using 1 <;> norm_num

/-! ## Abstract extraction of the third lower row -/

/-- The local coefficient analogue of
`lowerRowTwoPolynomial68_topCoeff`.  The sign is reversed from the
positive-degree boundary because a local derivative multiplies the
coefficient at exponent `-5w` by `-5w`. -/
theorem lowerRowTwoHahn68_coeff_neg56
    (A B C0 D E S T U V dC dD dE dT dU dV : HahnSeries ℚ k)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hSord : (↑(-25 : ℚ) : WithTop ℚ) ≤ S.orderTop)
    (hTord : (↑(-30 : ℚ) : WithTop ℚ) ≤ T.orderTop)
    (hUord : (↑(-35 : ℚ) : WithTop ℚ) ≤ U.orderTop)
    (hVord : (↑(-40 : ℚ) : WithTop ℚ) ≤ V.orderTop)
    (hdC : (↑(-21 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdD : (↑(-26 : ℚ) : WithTop ℚ) ≤ dD.orderTop)
    (hdE : (↑(-31 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdT : (↑(-31 : ℚ) : WithTop ℚ) ≤ dT.orderTop)
    (hdU : (↑(-36 : ℚ) : WithTop ℚ) ≤ dU.orderTop)
    (hdV : (↑(-41 : ℚ) : WithTop ℚ) ≤ dV.orderTop)
    (hSco : S.coeff (-25 : ℚ) =
      (4 / 3 : k) * D.coeff (-25 : ℚ) +
        (4 / 9 : k) * A.coeff (-10 : ℚ) * B.coeff (-15 : ℚ))
    (hTco : T.coeff (-30 : ℚ) =
      (4 / 3 : k) * E.coeff (-30 : ℚ) +
      (2 / 9 : k) * B.coeff (-15 : ℚ) ^ 2 +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * C0.coeff (-20 : ℚ) -
      (4 / 81 : k) * A.coeff (-10 : ℚ) ^ 3)
    (hUco : U.coeff (-35 : ℚ) =
      (4 / 9 : k) * B.coeff (-15 : ℚ) * C0.coeff (-20 : ℚ) +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * D.coeff (-25 : ℚ) -
      (4 / 27 : k) * A.coeff (-10 : ℚ) ^ 2 * B.coeff (-15 : ℚ))
    (hVco : V.coeff (-40 : ℚ) =
      (2 / 9 : k) * C0.coeff (-20 : ℚ) ^ 2 +
      (4 / 9 : k) * B.coeff (-15 : ℚ) * D.coeff (-25 : ℚ) +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * E.coeff (-30 : ℚ) -
      (4 / 27 : k) * A.coeff (-10 : ℚ) * B.coeff (-15 : ℚ) ^ 2 -
      (4 / 27 : k) * A.coeff (-10 : ℚ) ^ 2 * C0.coeff (-20 : ℚ) +
      (5 / 243 : k) * A.coeff (-10 : ℚ) ^ 4)
    (hdCco : dC.coeff (-21 : ℚ) =
      (-20 : k) * C0.coeff (-20 : ℚ))
    (hdDco : dD.coeff (-26 : ℚ) =
      (-25 : k) * D.coeff (-25 : ℚ))
    (hdEco : dE.coeff (-31 : ℚ) =
      (-30 : k) * E.coeff (-30 : ℚ))
    (hdTco : dT.coeff (-31 : ℚ) =
      (-30 : k) * T.coeff (-30 : ℚ))
    (hdUco : dU.coeff (-36 : ℚ) =
      (-35 : k) * U.coeff (-35 : ℚ))
    (hdVco : dV.coeff (-41 : ℚ) =
      (-40 : k) * V.coeff (-40 : ℚ)) :
    (U * dC + 2 * T * dD + 3 * S * dE - 3 * B * dV -
      2 * C0 * dU - D * dT).coeff (-56 : ℚ) =
      (40 / 81 : k) * topRowTwo68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  have hUC := hahnCoeff_mul_at_lower46 U dC (-35) (-21) hUord hdC
  have hTD := hahnCoeff_mul_at_lower46 T dD (-30) (-26) hTord hdD
  have hSE := hahnCoeff_mul_at_lower46 S dE (-25) (-31) hSord hdE
  have hBV := hahnCoeff_mul_at_lower46 B dV (-15) (-41) hB hdV
  have hCU := hahnCoeff_mul_at_lower46 C0 dU (-20) (-36) hC hdU
  have hDT := hahnCoeff_mul_at_lower46 D dT (-25) (-31) hD hdT
  norm_num at hUC hTD hSE hBV hCU hDT
  have hrewrite :
      U * dC + 2 * T * dD + 3 * S * dE - 3 * B * dV -
          2 * C0 * dU - D * dT =
        U * dC + (T * dD + T * dD) +
          (S * dE + S * dE + S * dE) -
          (B * dV + B * dV + B * dV) -
          (C0 * dU + C0 * dU) - D * dT := by ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub,
    hUC, hTD, hSE, hBV, hCU, hDT]
  rw [hdCco, hdDco, hdEco, hdTco, hdUco, hdVco,
    hSco, hTco, hUco, hVco]
  simp only [topRowTwo68]
  ring

/-- Exact integrated boundary information still needed for the actual
third local row.  This is a structure of propositions, not an axiom. -/
structure IntegratedLocalRowTwoBoundaryData68
    (A B C0 D E S T U V dT dU dV : HahnSeries ℚ k) : Prop where
  s_order : (↑(-25 : ℚ) : WithTop ℚ) ≤ S.orderTop
  t_order : (↑(-30 : ℚ) : WithTop ℚ) ≤ T.orderTop
  u_order : (↑(-35 : ℚ) : WithTop ℚ) ≤ U.orderTop
  v_order : (↑(-40 : ℚ) : WithTop ℚ) ≤ V.orderTop
  dt_order : (↑(-31 : ℚ) : WithTop ℚ) ≤ dT.orderTop
  du_order : (↑(-36 : ℚ) : WithTop ℚ) ≤ dU.orderTop
  dv_order : (↑(-41 : ℚ) : WithTop ℚ) ≤ dV.orderTop
  s_coeff : S.coeff (-25 : ℚ) =
    (4 / 3 : k) * D.coeff (-25 : ℚ) +
      (4 / 9 : k) * A.coeff (-10 : ℚ) * B.coeff (-15 : ℚ)
  t_coeff : T.coeff (-30 : ℚ) =
    (4 / 3 : k) * E.coeff (-30 : ℚ) +
    (2 / 9 : k) * B.coeff (-15 : ℚ) ^ 2 +
    (4 / 9 : k) * A.coeff (-10 : ℚ) * C0.coeff (-20 : ℚ) -
    (4 / 81 : k) * A.coeff (-10 : ℚ) ^ 3
  u_coeff : U.coeff (-35 : ℚ) =
    (4 / 9 : k) * B.coeff (-15 : ℚ) * C0.coeff (-20 : ℚ) +
    (4 / 9 : k) * A.coeff (-10 : ℚ) * D.coeff (-25 : ℚ) -
    (4 / 27 : k) * A.coeff (-10 : ℚ) ^ 2 * B.coeff (-15 : ℚ)
  v_coeff : V.coeff (-40 : ℚ) =
    (2 / 9 : k) * C0.coeff (-20 : ℚ) ^ 2 +
    (4 / 9 : k) * B.coeff (-15 : ℚ) * D.coeff (-25 : ℚ) +
    (4 / 9 : k) * A.coeff (-10 : ℚ) * E.coeff (-30 : ℚ) -
    (4 / 27 : k) * A.coeff (-10 : ℚ) * B.coeff (-15 : ℚ) ^ 2 -
    (4 / 27 : k) * A.coeff (-10 : ℚ) ^ 2 * C0.coeff (-20 : ℚ) +
    (5 / 243 : k) * A.coeff (-10 : ℚ) ^ 4
  dt_coeff : dT.coeff (-31 : ℚ) =
    (-30 : k) * T.coeff (-30 : ℚ)
  du_coeff : dU.coeff (-36 : ℚ) =
    (-35 : k) * U.coeff (-35 : ℚ)
  dv_coeff : dV.coeff (-41 : ℚ) =
    (-40 : k) * V.coeff (-40 : ℚ)

/-- Once the explicit integrated boundary package above is supplied, the
literal source bracket forces the third scalar top row to vanish. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowTwo_zero_of_integratedBoundary
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T0 : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hboundary :
      let AH := ratFuncAtHahn46 T0.root T0.source.A
      let BH := ratFuncAtHahn46 T0.root T0.source.B
      let CH := ratFuncAtHahn46 T0.root T0.source.C0
      let DH := ratFuncAtHahn46 T0.root T0.source.D
      let EH := ratFuncAtHahn46 T0.root T0.source.E
      let SR := integratedS68 (RatFunc.C l) T0.source.A T0.source.B
        T0.source.C0 T0.source.D (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.delta)
      let TR := integratedT68 (RatFunc.C l) T0.source.A T0.source.B
        T0.source.C0 T0.source.D T0.source.E
        (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
        (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.epsilon)
      let UR := integratedU68 (RatFunc.C l) T0.source.A T0.source.B
        T0.source.C0 T0.source.D T0.source.E
        (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
        (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
        (RatFunc.C T0.source.zeta)
      let VR := integratedV68 (RatFunc.C l) T0.source.A T0.source.B
        T0.source.C0 T0.source.D T0.source.E
        (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
        (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
        (RatFunc.C T0.source.epsilon) (RatFunc.C T0.source.eta)
      let SH := ratFuncAtHahn46 T0.root SR
      let TH := ratFuncAtHahn46 T0.root TR
      let UH := ratFuncAtHahn46 T0.root UR
      let VH := ratFuncAtHahn46 T0.root VR
      let dTH := ratFuncAtHahn46 T0.root (Differential.deriv TR)
      let dUH := ratFuncAtHahn46 T0.root (Differential.deriv UR)
      let dVH := ratFuncAtHahn46 T0.root (Differential.deriv VR)
      IntegratedLocalRowTwoBoundaryData68
        AH BH CH DH EH SH TH UH VH dTH dUH dVH) :
    topRowTwo68
        ((ratFuncAtHahn46 T0.root T0.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T0.root T0.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH := ratFuncAtHahn46 T0.root T0.source.A
  let BH := ratFuncAtHahn46 T0.root T0.source.B
  let CH := ratFuncAtHahn46 T0.root T0.source.C0
  let DH := ratFuncAtHahn46 T0.root T0.source.D
  let EH := ratFuncAtHahn46 T0.root T0.source.E
  let SR := integratedS68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D (RatFunc.C T0.source.alpha)
    (RatFunc.C T0.source.beta) (RatFunc.C T0.source.delta)
  let TR := integratedT68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.epsilon)
  let UR := integratedU68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
    (RatFunc.C T0.source.zeta)
  let VR := integratedV68 (RatFunc.C l) T0.source.A T0.source.B
    T0.source.C0 T0.source.D T0.source.E
    (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
    (RatFunc.C T0.source.gamma) (RatFunc.C T0.source.delta)
    (RatFunc.C T0.source.epsilon) (RatFunc.C T0.source.eta)
  let SH := ratFuncAtHahn46 T0.root SR
  let TH := ratFuncAtHahn46 T0.root TR
  let UH := ratFuncAtHahn46 T0.root UR
  let VH := ratFuncAtHahn46 T0.root VR
  let dCH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.C0)
  let dDH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.D)
  let dEH := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
  let dTH := ratFuncAtHahn46 T0.root (Differential.deriv TR)
  let dUH := ratFuncAtHahn46 T0.root (Differential.deriv UR)
  let dVH := ratFuncAtHahn46 T0.root (Differential.deriv VR)
  dsimp only at hboundary
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T0.coordinateOrderBounds hp hH hp6
  obtain ⟨hdA, hdB, hdC, hdD, hdE⟩ :=
    T0.coordinateDerivativeOrderBounds hp hH hp6
  obtain ⟨hdAco, hdBco, hdCco, hdDco, hdEco⟩ :=
    T0.coordinateDerivativeInitialCoeffs hp hH hp6
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hx := GCD369RatFuncDerivative (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C l) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst l) (hconst T0.source.alpha) (hconst T0.source.beta)
      (hconst T0.source.gamma) (hconst T0.source.delta)
      (hconst T0.source.epsilon) (hconst T0.source.zeta)
      (hconst T0.source.eta) T0.source.bracket_eq
  have hrowR := hlow.2.2.1
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hrowR
  have hrowH' :
      UH * dCH + 2 * TH * dDH + 3 * SH * dEH - 3 * BH * dVH -
        2 * CH * dUH - DH * dTH = 0 := by
    dsimp only [AH, BH, CH, DH, EH, SR, TR, UR, VR, SH, TH, UH, VH,
      dCH, dDH, dEH, dTH, dUH, dVH]
    simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
      map_ofNat, map_zero] using hrowH
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-56 : ℚ)) hrowH'
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hface := lowerRowTwoHahn68_coeff_neg56
    AH BH CH DH EH SH TH UH VH dCH dDH dEH dTH dUH dVH
      hB hC hD hE hboundary.s_order hboundary.t_order hboundary.u_order
      hboundary.v_order hdC hdD hdE hboundary.dt_order hboundary.du_order
      hboundary.dv_order hboundary.s_coeff hboundary.t_coeff
      hboundary.u_coeff hboundary.v_coeff hdCco hdDco hdEco
      hboundary.dt_coeff hboundary.du_coeff hboundary.dv_coeff
  rw [hface] at hcoeff
  have hfactor : (40 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

end LocalDerivative68

#print axioms localHahn_deriv_coeff_neg_succ_of_cleared
#print axioms ratFuncAtHahn68_linearRoot_single_deriv
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateDerivativeInitialCoeffs
#print axioms algebraMap_localDerivativeCleared
#print axioms localHahn_deriv_orderTop_ge_of_cleared
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateDerivativeOrderBounds
#print axioms lowerRowTwoHahn68_coeff_neg56
#print axioms SquareConstantLIntegratedLocalRootData68.topRowTwo_zero_of_integratedBoundary

end Max11DegreeRoutes
