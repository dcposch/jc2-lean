import Fable610ScaleTwoKappaIntegralBridgeCompatPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart05Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart06Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart102Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart19Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart20Scratch

/-! # Compatible kappa integral bridge for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h₀²` and `N = 5 p₅ H² - 3 q₉ = λ h₀⁹`
with `h₀.natDegree = 1`, the terminal integral closure spent the
degree-`5` first integral `ι`; the next genuinely unused integral row
is the degree-`4` first integral `κ`, whose construction needs the
degree-`6` `θ` tower.  The scale-zero eighth/ninth/tenth defect
scratches state that tower and the `κ` clearing, but they collide with
canonical scale-two declarations, so nothing is imported from them:
this file restates on the compatible scale-two chain, with
`terminal`/`_bridge` names, exactly the missing pieces — the depressed
decic `z¹` coordinate and its ninth-power clearing, the degree-`6` and
degree-`4` depressed differential rows, the degree-`6` integral `θ`
with `d θ = 0`, and the degree-`4` integral `κ` with `d κ = 0` — and
rederives the weight-`55` power relation
`bridgeClearedKappaDefect610 = C kappaMu · h₀⁵⁵` directly from the
source differential rows already in the canonical ancestry (rows `13`
through `7`, the bridge row `5`, and the two rows restated here).  The
spent `ι` packet is reused opaquely; its weight-`50` numerator is never
re-expanded.

On the fifteenth-face jet `p₅ = h₀⁵ w₁`, `p₄ = h₀³ a₄₁`,
`p₃ = h₀ p₃₁`, `q₈ = h₀⁷ s₁`, `q₇ = h₀⁵ u₁`, `q₆ = h₀⁴ b₆₂`,
`q₅ = h₀² q₅₂` the numerator factors exactly through `h₀⁴⁸`, seven
orders below the defect weight, with fully factored first head
`4837294080 p₃₁ (264 p₃₁² s₁ + 693 a₄₁ p₃₁ u₁ - 935 a₄₁ p₃₁²
- 432 a₄₁ q₄ - 270 p₃₁ q₅₂)`; the peel is
`head + h₀ · tail = C kappaMu · h₀⁷`, so the head vanishes at the
root, and modulo the tenth-face root laws alone it reduces,
chamber-free, to `a₄₁(a) p₃₁(a)³ = 0` — the honest split
`a₄₁(a) = 0 ∨ p₃₁(a) = 0`, a relation the `ι` heads never reached.

Combined with the four exact terminal-closure children: the two
`p₃₁(a) = 0` sibling children and the pinned `p₃₁(a) = 0` complement
child absorb the head through its overall `p₃₁` factor and are
retained unchanged.  On the `p₃₁(a) ≠ 0` child the split forces
`a₄₁(a) = 0`, the retained core `5 a₄₁² + 2 p₃₁ w₁ = 0` forces
`w₁(a) = 0`, and the remaining ground relations collapse to the pins
`80 p₂(a) = 9 λ p₃₁(a)`, `16 b₆₂(a) = -5 λ p₃₁(a)`, which subsume all
three original relations; the retained `ψ₂` value collapses to
`ψ₂(a) = -209952 λ p₁(a)`, under which the retained boundary
elimination reproduces exactly the inhomogeneous degree-`0` Keller row
`p₀'(a) q₁(a) - p₁(a) q₀'(a) = j`, the sole inhomogeneous constraint
left on that child.

No child is closed, because none is contradicted — the Keller boundary
relation lives on the fresh coordinates `p₀, p₁, q₀, q₁`.  The honest
residual is that single boundary relation with the preserved ground
constants `ζ, η, iotaK, kappaMu` and the open aligned face `N = 0`.
The next unused integral row is the degree-`3` first integral; the
next unused aligned row on `N = 0` is the degree-`10` row.

No total-degree or twice-prime theorem is used.
-/
/-! ## Depressed decic `z¹` coordinate and the `θ`/`κ` residuals -/

namespace Max11DegreeRoutes

#print axioms nonzeroFace610_linearRoot_kappaIntegralBridge
#print axioms normalized610ScaleTwo_nonzeroFace_kappaIntegralBridge
#print axioms nonzeroFace610_bridgeKappaPowerRelation

end Max11DegreeRoutes
