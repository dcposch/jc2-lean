# Exact partial-`y` degree closure through eleven

This Lean 4 project formalizes the finite degree-routing certificate underlying
the campaign's maximum-partial-degree-eleven composition.  Once the standard
zero-degree, gcd-at-most-two, equal-degree, and divisibility reduction rules
are supplied, closing the single primitive pair `(6,9)` closes every ordered
pair `(m,n)` with `m,n ≤ 11`.

The original abstract routing certificate remains available, and
`Max11PlaneKellerGeneration` instantiates it with actual bivariate polynomials.
The strengthened headline
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithElementaryRoutes` proves the
zero-partial-degree, equal-degree, and divisibility routes in characteristic
zero.  It defines the two-variable Jacobian using `MvPolynomial.pderiv`, uses
`degreeOf 1` for the actual partial `y`-degree, and concludes the concrete
coordinate-ring equality `K[P,Q] = K[x,y]` via `Algebra.adjoin`.  Its only
remaining premises are the gcd-at-most-two theorem and the global `(6,9)`
leaf, so this remains a formal composition theorem rather than an
unconditional standalone proof of maximum eleven.

The further source-facing headline
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithNormalized69Routes` replaces
the single opaque `(6,9)` premise by two exhaustive premises: closure of the
normalized cube-core branch and closure of the normalized noncube-core branch.
Thus its remaining mathematical inputs are exactly gcd-at-most-two and those
two branch closures.
The equivalent exclusion-form headline
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithNormalized69Exclusions`
matches the output shape of the trajectory projects: if each normalized
branch is impossible, its generation route follows immediately.

## Compared declarations

- `Max11RouteClassification` proves that every unordered pair through eleven
  takes one of the four standard routes or is `(6,9)`.
- `Max11UniquePrimitive` states the same fact in fail-closed form: if none of
  the standard routes applies, the pair is exactly `(6,9)`.
- `MaxPartialDegreeElevenClosure` proves the recursive closure theorem for an
  arbitrary symmetric predicate `Good`.  Its induction follows the strict
  sum decrease of every equal-degree or divisibility child.
- `Max11PlaneKellerGeneration` specializes that recursion to actual bivariate
  Keller pairs and concludes that the two coordinates generate the full
  polynomial ring.  Target-coordinate symmetry is proved internally.
- `Max11ClassicalRoutes.Max11PlaneKellerGenerationWithZeroRoute` proves the
  zero-degree route from the Jacobian equation and removes it from the
  premises of the characteristic-zero composition theorem.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithElementaryRoutes` proves
  the equal-degree and divisibility routes by deriving the weighted Wronskian
  equation for the leading `y`-coefficients, identifying the required leading
  power, and applying a degree-lowering triangular target shear.  Only the
  gcd-at-most-two theorem and global `(6,9)` leaf remain as premises.
- `Max11DegreeRoutes.planeKellerPair_69_commonCore` starts that remaining
  exceptional leaf from a genuine Keller pair: the top Jacobian row and UFD
  factorization produce nonzero `alpha`, `beta`, and `h` with leading
  coefficients `alpha*h^2` and `beta*h^3`.  No cube/noncube landing is
  assumed in this theorem.
- `Max11DegreeRoutes.planeKellerPair_69_normalize` removes those two nonzero
  scalar factors by independent target rescalings.  The normalized pair has
  literal leading coefficients `h^2` and `h^3`, the same partial degrees,
  remains Keller, and generates the full ring exactly when the original pair
  does.
- `Max11DegreeRoutes.planeKellerAutomorphicAtDegrees_69_of_normalized_routes`
  performs the exhaustive literal cube/noncube split on that normalized core
  and transports generation back to the original pair.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithNormalized69Routes`
  composes that split with the elementary degree routes.  It is the current
  source-honest top of the formal tower: gcd at most two and the two normalized
  branch closures remain explicit premises.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithNormalized69Exclusions`
  gives the same composition using branch-impossibility premises, the exact
  output interface expected from the cube and noncube exclusions.
- `Max12FirstPrimitives` verifies the frontier checksum: at maximum twelve,
  the same direct routes first leave `(8,12)` and `(9,12)`.

## Scope and relationship to the source

The frozen source and independent hostile review prove a larger mathematical
composition: after the full `(6,9), 3 | H` leaf is excluded and the cited
classical degree reductions are applied, every characteristic-zero Keller pair
with maximum actual partial `y`-degree at most eleven is an automorphism.  This
Lean extraction checks the complete finite recursion and frontier arithmetic,
then instantiates the result for actual bivariate polynomials, their Jacobian,
partial `y`-degree, and coordinate-ring generation.  It does not prove
scalar-extension descent, the gcd-at-most-two theorem, or the global `(6,9)`
leaf (including the cube-core trajectory closure).

The source files are copied byte-for-byte under `sources/`:

- composition: `7eda0a469585247479d46c8f5f2ce95d2643ae8541f0d7f9c80e1c8537fffb0c`
- review: `d9522acbb35c5097cb3d3c947be12c10868f109af4d30c9713870f5ec6e9a33f`

No claim of novelty or priority is made beyond the included source.  The
hostile review is campaign-internal, not external human peer review.

## Verification

```sh
lake build
./scripts/check_axioms.sh
```

`Solution.lean`, `ClassicalRoutes.lean`, and `DegreeRoutes.lean` contain no
`sorry`, custom axioms, or trust escapes.  The permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`.
