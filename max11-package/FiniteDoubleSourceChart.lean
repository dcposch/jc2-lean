import FiniteDoubleSource

/-! # Moving-root chart identities at the source double root

Two commutative-ring identities for the cubic value and the transverse
quadratic after translating the double root by `w`.  The first identity
uses the residual root relation `3 * e + 2 * d * r = 0`.  Neither proof
uses valuation theory.
-/

noncomputable section

/-- Three times the cubic value at `r + w`, after the residual relation
`3 * e + 2 * d * r = 0`, equals the cubic remainder plus the displayed
linear `H`-correction. -/
theorem GCD369CubeDoubleSourceChart_cubic
    {R : Type*} [CommRing R] (r w H d e : R)
    (hre : 3 * e + 2 * d * r = 0) :
    3 * ((r + w) ^ 3 + (-3 * r ^ 2 + H * d) * (r + w) +
        (2 * r ^ 3 + H * e)) =
      3 * w ^ 2 * (3 * r + w) + H * (3 * d * w + d * r) := by
  linear_combination H * hre

/-- The transverse quadratic at `r + w` with first-order deviation
`(M * B, -M * r * B)` and second-order correction `(H * B2, H * C2)`
equals the displayed chart form. -/
theorem GCD369CubeDoubleSourceChart_transverse
    {R : Type*} [CommRing R] (r w H M A B B2 C2 : R) :
    A * (r + w) ^ 2 + (r * A + M * B + H * B2) * (r + w) +
        (-2 * r ^ 2 * A - M * r * B + H * C2) =
      A * w * (3 * r + w) + M * B * w +
        H * (B2 * (r + w) + C2) := by
  ring

#print axioms GCD369CubeDoubleSourceChart_cubic
#print axioms GCD369CubeDoubleSourceChart_transverse
