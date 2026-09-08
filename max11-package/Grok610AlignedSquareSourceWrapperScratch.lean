import Grok610AlignedSquareSourceWrapperPart01Scratch
import Grok610AlignedSquareSourceWrapperPart02Scratch
import Grok610AlignedSquareSourceWrapperPart03Scratch
import Grok610AlignedSquareSourceWrapperPart04Scratch
import Grok610AlignedSquareSourceWrapperPart05Scratch
import Grok610AlignedSquareSourceWrapperPart06Scratch
import Grok610AlignedSquareSourceWrapperPart07Scratch
import Grok610AlignedSquareSourceWrapperPart08Scratch
import Grok610AlignedSquareSourceWrapperPart09Scratch
import Grok610AlignedSquareSourceWrapperPart10Scratch
import Grok610AlignedSquareSourceWrapperPart11Scratch
import Grok610AlignedSquareSourceWrapperPart12Scratch
import Grok610AlignedSquareSourceWrapperPart13Scratch
import Grok610AlignedSquareSourceWrapperPart14Scratch
import Grok610AlignedSquareSourceWrapperPart15Scratch
import Grok610AlignedSquareSourceWrapperPart16Scratch
import Grok610AlignedSquareSourceWrapperPart17Scratch
import Grok610AlignedSquareSourceWrapperPart18Scratch
import Grok610AlignedSquareSourceWrapperPart19Scratch
import Grok610AlignedSquareSourceWrapperPart20Scratch
import Grok610AlignedSquareSourceWrapperPart21Scratch
import Grok610AlignedSquareSourceWrapperPart22Scratch
import Grok610AlignedSquareSourceWrapperPart23Scratch
import Grok610AlignedSquareSourceWrapperPart24Scratch
import Grok610AlignedSquareSourceWrapperPart25Scratch
import Grok610AlignedSquareSourceWrapperPart26Scratch
import Grok610AlignedSquareSourceWrapperPart27Scratch
import Grok610AlignedSquareSourceWrapperPart28Scratch
import Grok610AlignedSquareSourceWrapperPart29Scratch
import Grok610AlignedSquareSourceWrapperPart30Scratch
import Grok610AlignedSquareSourceWrapperPart31Scratch
import Grok610AlignedSquareSourceWrapperPart32Scratch
import Grok610AlignedSquareSourceWrapperPart33Scratch
import Grok610AlignedSquareSourceWrapperPart34Scratch
import Grok610AlignedSquareSourceWrapperPart35Scratch
import Grok610AlignedSquareSourceWrapperPart36Scratch
import Grok610AlignedSquareSourceWrapperPart37Scratch
import Grok610AlignedSquareSourceWrapperPart38Scratch
import Grok610AlignedSquareSourceWrapperPart39Scratch
import Grok610AlignedSquareSourceWrapperPart40Scratch
import Grok610AlignedSquareSourceWrapperPart41Scratch
import Grok610AlignedSquareSourceWrapperPart42Scratch
import Grok610AlignedSquareSourceWrapperPart43Scratch
import Grok610AlignedSquareSourceWrapperPart44Scratch
import Grok610AlignedSquareSourceWrapperPart45Scratch
import Grok610AlignedSquareSourceWrapperPart46Scratch
import Grok610AlignedSquareSourceWrapperPart47Scratch
import Grok610AlignedSquareSourceWrapperPart48Scratch
import Grok610AlignedSquareSourceWrapperPart49Scratch
import Grok610AlignedSquareSourceWrapperPart50Scratch
import Grok610AlignedSquareSourceWrapperPart51Scratch

/-! # Aligned-square source wrapper for the `(6,10)` weight-fifteen primitive

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareM1M2Scratch` reduced both live MixedPair limbs and
did not close the square chamber.  This file is route M3: the analog of
`Grok610DegreeZeroSourceWrapperScratch` together with the pole/clearing
bookkeeping of the linear-root sibling, instantiated on the committed
aligned peel rather than copied from Backwire.

The affine source Jacobian still divides by exactly one power of `h`
(`differentialJacobian_affineDepress_sourceToRatFunc68`).  On the aligned
face `N = 0` the depressed `z⁹` coefficient is the constant `L = 0`, so
the weight-fifteen primitive satisfies the ordinary simple-pole equation
`ρ' = C(j)/h₀`.  This is not assumed, and it is not the linear-root
remaining pole `6`.

Under the MixedPair peel `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
`3 f₂ - w₁² = h₀ e₁`, `27 p₃ - w₁³ = h₀² e₃`, `λ = 0`:

* `pole(A) = 2`, `pole(B) = 2`, `pole(C) = 4`, `pole(P) = 8`
  (the last because MixedPair does not peel `q₈`);
* native homogeneous clearing of the same weight-fifteen primitive is
  still `5 · 15 = 75`;
* the cleared compact numerator has base order `54` (not `69`) and
  remaining pole `21` (not `6`);
* the base-order head is the single monomial `67814496 b₈ w₁¹³`.

On the live `μ = 0` limb `w₁(a) ≠ 0`, the order-`21` pole obstruction
therefore forces `q₈(a) = 0`, which is a new `q`-side peel, not
`0 = j`.  The `w₁(a) = 0` child kills this MixedPair head automatically
and has a strictly later base order `61` (remaining pole `14`).  The
square chamber is not claimed empty.

CAS: `derive_610_aligned_square_source_wrapper.py` (job
`20260902T022625Z-aligned-square-source-wrapper-789`).  No `sorry`, no
new axioms, no finite-root shortcut, no closure overclaim.
-/
/-! ## Bookkeeping: weight, native clearing, computed remaining pole -/

namespace Max11DegreeRoutes

#print axioms alignedSquareSourceClearingPower610_eq_mul
#print axioms alignedSquareRemainingPole610_eq_sub
#print axioms alignedSquareBaseOrder610_ne_sixtyNine
#print axioms alignedSquareRemainingPole610_ne_six
#print axioms alignedSquareABar610_eq_generic
#print axioms alignedSquareBBar610_eq_generic
#print axioms alignedSquarePBar610_eq_generic
#print axioms alignedSquareDepressedA_eq_peeled
#print axioms alignedSquareA_pole_two610
#print axioms alignedSquareB_pole_two610
#print axioms alignedSquareP_pole_eight610
#print axioms alignedSquareL_eq_zero610
#print axioms alignedSquarePrimitive610_independent_of_X0
#print axioms alignedSquarePrimitive610_deriv_eq_simplePole_of_source
#print axioms alignedSquareJetQuotient610_head
#print axioms alignedSquareBaseHead610_q8_of_w1_ne_zero
#print axioms alignedSquare_localLinearPole_head_eval_zero610
#print axioms alignedSquare_poleTwentyOne_head_eval_zero610
#print axioms alignedSquare_poleTwentyOne_baseHead_eval_zero610
#print axioms alignedSquare_poleTwentyOne_q8_eval_zero610

end Max11DegreeRoutes
