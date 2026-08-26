# Exact partial-`y` degree closure through eleven

This Lean 4 project formalizes the finite degree-routing certificate underlying
the campaign's maximum-partial-degree-eleven composition.  Once the standard
zero-degree, gcd-at-most-two, equal-degree, and divisibility reduction rules
are supplied, closing the single primitive pair `(6,9)` closes every ordered
pair `(m,n)` with `m,n ≤ 11`.

The original abstract routing certificate remains available, and the headline
`Max11PlaneKellerGeneration` now instantiates it with actual bivariate
polynomials.  It defines the two-variable Jacobian using `MvPolynomial.pderiv`,
uses `degreeOf 1` for the actual partial `y`-degree, and concludes the concrete
coordinate-ring equality `K[P,Q] = K[x,y]` via `Algebra.adjoin`.  The theorem's
premises are the cited zero, gcd-at-most-two, divisibility, equal-degree, and
`(6,9)` route theorems at this concrete predicate.  Those deep premises are
not reproved here, so this remains a formal composition theorem rather than an
unconditional standalone proof of maximum eleven.

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
scalar-extension descent, the classical degree-route premises, or the global
`(6,9)` leaf (including the cube-core trajectory closure).

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

`Solution.lean` contains no `sorry`, custom axioms, or trust escapes.  The
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
