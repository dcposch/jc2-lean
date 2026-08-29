import LowScale68ScaleTwoAlignedSquareRhoOneCubicBridge

/-! # The next differential face on the two zero-septic cubic components -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicComponents68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicComponentsHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Scalar form of the weight-ten row-two coefficient. -/
def rhoOneZeroLCubicNextTwo68 (a b c d e : k) : k :=
  a ^ 2 * b * c + 3 * a * c * d + 3 * a * b * e - 27 * d * e

/-- The exact weight-ten portion of the differentiated row two after
writing `C=A²/3+CΔ` and `E=A³/27+EΔ`. -/
def lowerRowTwoCubicWeightTenHahn68
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 (8 / 27 : k) A B C dA dE 1 1 1 1 0 +
  weightedMonomial68 (8 / 3 : k) E dD A B C 1 1 0 0 0 +
  weightedMonomial68 (8 / 3 : k) D dE A B C 1 1 0 0 0 +
  weightedMonomial68 (-4 / 3 : k) B E dA A C 1 1 1 0 0 +
  weightedMonomial68 (-8 / 27 : k) A C dB D E 2 1 1 0 0 +
  weightedMonomial68 (-8 / 27 : k) A B dC D E 2 1 1 0 0 +
  weightedMonomial68 (-4 / 3 : k) C D dA A B 1 1 1 0 0

/-- Literal extraction of the weight-ten Hahn coefficient.  The five
derivative coefficients are the formal derivatives of the corresponding
boundary monomials. -/
theorem lowerRowTwoCubicWeightTenHahn68_coeff_neg10
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-5 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (↑(-3 : ℚ) : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (↑(-4 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdD : (↑(-5 : ℚ) : WithTop ℚ) ≤ dD.orderTop)
    (hdE : (↑(-6 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hdBco : dB.coeff (-3 : ℚ) = (-2 : k) * B.coeff (-2 : ℚ))
    (hdCco : dC.coeff (-4 : ℚ) = (-3 : k) * C.coeff (-3 : ℚ))
    (hdDco : dD.coeff (-5 : ℚ) = (-4 : k) * D.coeff (-4 : ℚ))
    (hdEco : dE.coeff (-6 : ℚ) = (-5 : k) * E.coeff (-5 : ℚ)) :
    (lowerRowTwoCubicWeightTenHahn68 A B C D E dA dB dC dD dE).coeff
        (-10 : ℚ) =
      (8 / 9 : k) * rhoOneZeroLCubicNextTwo68
        (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
        (C.coeff (-3 : ℚ)) (D.coeff (-4 : ℚ))
        (E.coeff (-5 : ℚ)) := by
  have h1 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 27 : k) A B C dA dE 1 1 1 1 0
      (-2) (-2) (-3) (-3) (-6) hA hB hC hdA hdE
  have h2 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 3 : k) E dD A B C 1 1 0 0 0
      (-5) (-5) (-2) (-2) (-3) hE hdD hA hB hC
  have h3 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 3 : k) D dE A B C 1 1 0 0 0
      (-4) (-6) (-2) (-2) (-3) hD hdE hA hB hC
  have h4 := weightedMonomial68_coeff_at_general_lower_next
    (-4 / 3 : k) B E dA A C 1 1 1 0 0
      (-2) (-5) (-3) (-2) (-3) hB hE hdA hA hC
  have h5 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A C dB D E 2 1 1 0 0
      (-2) (-3) (-3) (-4) (-5) hA hC hdB hD hE
  have h6 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A B dC D E 2 1 1 0 0
      (-2) (-2) (-4) (-4) (-5) hA hB hdC hD hE
  have h7 := weightedMonomial68_coeff_at_general_lower_next
    (-4 / 3 : k) C D dA A B 1 1 1 0 0
      (-3) (-4) (-3) (-2) (-2) hC hD hdA hA hB
  norm_num at h1 h2 h3 h4 h5 h6 h7
  simp only [lowerRowTwoCubicWeightTenHahn68, HahnSeries.coeff_add]
  norm_num only
  rw [h1, h2, h3, h4, h5, h6, h7, hdAco, hdBco, hdCco, hdDco,
    hdEco]
  simp only [rhoOneZeroLCubicNextTwo68]
  ring

/-- Combining I4 with the new differential row eliminates the improved
`E` coefficient from one equation. -/
theorem rhoOneZeroLCubic_nextFour_nextTwo_force68
    (a b c d e : k)
    (h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0)
    (h2 : rhoOneZeroLCubicNextTwo68 a b c d e = 0) :
    a ^ 2 * b * c = 9 * d * e := by
  have h4' : -2 * a * b * c + 3 * c * d + 3 * b * e = 0 := by
    simp only [rhoOneZeroLCubicNextFour68] at h4
    linear_combination (9 / 8 : k) * h4
  simp only [rhoOneZeroLCubicNextTwo68] at h2
  linear_combination (1 / 3 : k) * (h2 - a * h4')

/-- On the first component, I4 splits it into the `b=0` face and the
linear defect relation `3e=ac`. -/
theorem rhoOneZeroLCubic_firstComponent_split68
    (a b c d e : k)
    (h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0)
    (hd : a * b = 3 * d) : b = 0 ∨ 3 * e = a * c := by
  have h4' : -2 * a * b * c + 3 * c * d + 3 * b * e = 0 := by
    simp only [rhoOneZeroLCubicNextFour68] at h4
    linear_combination (9 / 8 : k) * h4
  have hfac : b * (3 * e - a * c) = 0 := by
    calc
      b * (3 * e - a * c) =
          (-2 * a * b * c + 3 * c * d + 3 * b * e) +
            c * (a * b - 3 * d) := by ring
      _ = 0 := by rw [h4']; rw [hd]; ring
  rcases mul_eq_zero.mp hfac with hb | he
  · exact Or.inl hb
  · right; linear_combination he

/-- The two exact components already present in the source packet. -/
def RhoOneZeroLCubicFirstNextComponent68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let D := ratFuncAtHahn46 T.root T.source.D
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) = 3 * D.coeff (-4 : ℚ)

def RhoOneZeroLCubicSecondNextComponent68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) ^ 2 -
      B.coeff (-2 : ℚ) * D.coeff (-4 : ℚ) + 2 * c ^ 2 = 0

theorem RhoOneZeroLCubicNextSourcePacket68.component_split
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    {g u : k[X]} (P : RhoOneZeroLCubicNextSourcePacket68 T g u) :
    RhoOneZeroLCubicFirstNextComponent68 T g u ∨
      RhoOneZeroLCubicSecondNextComponent68 T g u := by
  rcases P.2.2.2.2.2.2 with hfirst | hsecond
  · exact Or.inl ⟨P, hfirst⟩
  · exact Or.inr ⟨P, hsecond⟩

/-- The actual differentiated lower row has zero coefficient at every
negative exponent, in particular at the new exponent `-10`. -/
theorem SquareZeroLIntegratedLocalRootData68.lowerRowTwo_actual_coeff_neg10_zero
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    let B := ratFuncAtHahn46 T0.root T0.source.B
    let C0 := ratFuncAtHahn46 T0.root T0.source.C0
    let D := ratFuncAtHahn46 T0.root T0.source.D
    let S := ratFuncAtHahn46 T0.root
      (integratedS68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D (RatFunc.C T0.source.alpha) (RatFunc.C T0.source.beta)
        (RatFunc.C T0.source.delta))
    let TT := ratFuncAtHahn46 T0.root
      (integratedT68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.epsilon))
    let U := ratFuncAtHahn46 T0.root
      (integratedU68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.zeta))
    let V := ratFuncAtHahn46 T0.root
      (integratedV68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
        (RatFunc.C T0.source.eta))
    let dC := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.C0)
    let dD := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.D)
    let dE := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
    let dT := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedT68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.epsilon)))
    let dU := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedU68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.zeta)))
    let dV := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedV68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
        (RatFunc.C T0.source.eta)))
    (U * dC + 2 * TT * dD + 3 * S * dE - 3 * B * dV -
      2 * C0 * dU - D * dT).coeff (-10 : ℚ) = 0 := by
  dsimp only
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T0.source.alpha) (hconst T0.source.beta)
      (hconst T0.source.gamma) (hconst T0.source.delta)
      (hconst T0.source.epsilon) (hconst T0.source.zeta)
      (hconst T0.source.eta) T0.source.bracket_eq
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hlow.2.2.1
  have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-10 : ℚ)) hrowH
  simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
    map_ofNat, map_zero, HahnSeries.coeff_zero] using hcoeff

end AlignedSquareRhoOneCubicComponents68

end Max11DegreeRoutes
