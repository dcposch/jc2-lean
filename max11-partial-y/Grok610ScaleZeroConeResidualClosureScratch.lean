import Grok610ScaleZeroConeResidualClosurePart101Scratch
import Grok610ScaleZeroConeResidualClosurePart102Scratch
import Grok610ScaleZeroConeResidualClosurePart40Scratch
import Grok610ScaleZeroConeResidualClosurePart48Scratch
import Grok610ScaleZeroConeResidualClosurePart49Scratch
import Grok610ScaleZeroConeResidualClosurePart50Scratch
import Grok610ScaleZeroConeResidualClosurePart51Scratch
import Grok610ScaleZeroConeResidualClosurePart52Scratch

/-! # Scale-zero cone residual closure for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeCascadeScratch` on the constant core
`H = (C t)²`.  That file closed a constant core, the unique-`A` cone
except the leftover chambers `L = 0` with `B` constant (and `β = 0` if
`B = 0`), the extreme unique-`B` cone `3 deg A < 2 deg B`, a unique
nonconstant `B` or `D₀`, and a unique nonconstant `E₀` with `β ≠ 0`.

This file continues the same Newton-degree / unique-face comparison of
the weight-fifteen primitive against derivative `C (j / t) ≠ 0`.  CAS
enumeration of the leftover cones (`derive_610_scale_zero_cone_residual.py`)
identifies the following unique faces, which this file closes.

* Unique-`A`, `L = 0`, `deg B = 0`, combined `A⁶` coefficient
  `(-(62720/2239488)) B + C (2695/559872 β)` nonzero: the face `A⁶`
  has degree `6 deg A ≥ 6`.  This includes the subchamber `β = 0`
  with `B` a nonzero constant.
* Unique-`A`, `L = 0`, `B = 0`, `β = 0`, `D₀` nonconstant: the face
  `A⁵ D₀` has degree `5 deg A + deg D₀ ≥ 6`.
* Unique-`A`, `L = 0`, `B = 0`, `β = 0`, `D₀` constant, combined `A⁵`
  coefficient `(92160/2239488) D₀ + C (49/5184 δ)` nonzero: the face
  `A⁵` has degree `5 deg A ≥ 5`.
* Unique-`A`, `L = 0`, `B = 0`, `β = 0`, `D₀ = 0`, `δ = 0`: the
  remaining primitive is `ζ` times a quartic in `(A, C₀)` plus `θ`
  times a cubic in `(A, C₀, E₀)`.  Nonzero `ζ` makes `A⁴` unique of
  degree `≥ 4`; vanishing `ζ` and nonzero `θ` makes `A³` unique of
  degree `≥ 3`; vanishing both makes the primitive constant.
* Unique nonconstant `C₀` with cubic coefficient
  `(419904/2239488 L) A + (414720/2239488) B - C (36288/559872 β)`
  nonzero: the face `C₀³` has degree `3 deg C₀ ≥ 3`.
* Unique nonconstant `E₀` with `β = 0` and `deg E₀ ≥ 2`: the primitive
  is affine in `E₀`, so either the linear coefficient is a nonzero
  constant and the degree equals `deg E₀ ≥ 2`, or the linear
  coefficient vanishes and the primitive is constant.
* Unique-`B` with `2 deg B < 3 deg A`: the face `A⁶ B` has degree
  `6 deg A + deg B > 5 deg B`.  Combined with the parent extreme cone
  `3 deg A < 2 deg B` (which forces `7 deg A < 5 deg B` over
  `ℕ`), the only leftover unique-`B` chamber is the tie `3 deg A = 2 deg B`.
* `A, B, C₀` constant, `β = 0`, `D₀` nonconstant, `deg E₀ < 2 deg D₀`:
  the face `D₀³` has degree `3 deg D₀`, strictly above `D₀²`, `D₀ E₀`,
  and `E₀`.

The leaf is not closed.  Named remaining cones are recorded by
`normalized610ScaleZero_coneResidualClosureResidual`.  No total-degree
or twice-prime theorem is used.  No finite-root shortcut is used.
-/
/-! ## Additional cones -/

namespace Max11DegreeRoutes

#print axioms UniqueHighC0Cone610
#print axioms UniqueHighD0Cone610
#print axioms UniqueHighE0Cone610
#print axioms A6BLeadsHighBCone610
#print axioms highA_l0_constB_A6Coefficient610
#print axioms highA_l0_B0_beta0_A5Coefficient610
#print axioms uniqueC0_cubicCoefficient610
#print axioms uniqueHighA_impossible_of_l_zero_B_const_A6_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_D0_pos
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_D0_zero_delta_zero
#print axioms uniqueNonconstantC0_impossible_of_cubic_ne
#print axioms uniqueNonconstantE0_impossible_of_beta_zero_deg_ge_two
#print axioms uniqueHighB_impossible_of_A6B_leads
#print axioms mixedConstABC_beta0_D0_leads_impossible
#print axioms normalized610ScaleZero_coneResidualClosureResidual

end Max11DegreeRoutes
