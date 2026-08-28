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

The source-honest headline
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithHistoryAndDivisible69Exclusions`
matches the finer reviewed history split.  It routes `3 ∤ deg h` through an
explicit large-source-shear/history premise and asks the deep cube and
noncube projects only to exclude the residue `3 ∣ deg h`.  A constant core
has degree zero and therefore remains in the divisible cube residue.

`Max11Assembly.lean` now imports the exhaustive source-facing divisible-core
theorem and discharges both of those deep exclusion premises.  Its theorem
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithImportedDivisible69Exclusion`
leaves exactly the gcd-at-most-two theorem and the nondivisible-core history
route as inputs.

`HistoryRoute.lean` and `HistoryDegree.lean` now prove every local step of that
history route: the triangular source automorphism, generation and Keller
invariance, both chain rules, exact large-shear total degrees
`2(H+3L),3(H+3L)`, and the Dirichlet choice making `H+3L` prime.  The stronger
headline
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithPrimeTotalDegreeGCDRoute`
therefore replaces the opaque history premise by the canonical published
theorem for Keller pairs whose total-degree gcd is prime.

`CoprimeDegreeRoute.lean` now substantially narrows its other premise.  The
top weighted-Wronskian row gives
`n * natDegree(A) = m * natDegree(B)` for the two leading coefficients.  For
coprime positive partial degrees this yields an integral common scale, and a
large source shear makes the total-degree gcd prime.  At partial-degree gcd
two, the same proof closes the odd common-scale case.  A sharper finite
classifier shows that equal and divisibility recursion leave only five such
unordered pairs through eleven: `(4,6)`, `(4,10)`, `(6,8)`, `(6,10)`, and
`(8,10)`.  Consequently
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithFiveEvenScaleGCDTwoLeaves`
is the current narrowest honest headline: besides the published prime-gcd
theorem, only the even common-leading-scale subcase of those five pairs
remains.  A checked adapter shows that the strong arbitrary-pair twice-prime
total-degree interface would close all five, but that interface is not treated
as an established theorem.

## Compared declarations

- `Max11RouteClassification` proves that every unordered pair through eleven
  takes one of the four standard routes or is `(6,9)`.
- `Max11UniquePrimitive` states the same fact in fail-closed form: if none of
  the standard routes applies, the pair is exactly `(6,9)`.
- `Max11PrimeRouteClassification` replaces the broad gcd-at-most-two branch
  by coprimality and enumerates exactly five remaining gcd-two primitives.
- `MaxPartialDegreeElevenClosureWithFiveGCDTwoLeaves` proves the corresponding
  recursive closure theorem with those five concrete leaves.
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
- `Max11DegreeRoutes.planeKellerPair_69_alignmentDiscriminator_constant`
  extracts the next actual Jacobian coefficient row.  In cube-root weights
  for the first two source coefficients it proves `(3*A-2*B)'=0`, hence
  `3*A-2*B` is constant—the source discriminator preceding the aligned and
  cube-mismatch branches.
- `Max11DegreeRoutes.planeKellerPair_69_cubeDiscriminatorNumerator_eq_zero`
  gives the stronger denominator-cleared cube-core row directly from an
  actual Keller pair with leading coefficients `s^6,s^9`; it makes no prior
  divisibility assumption on the next coefficients.
- `Max11DegreeRoutes.planeKellerPair_69_sourceDichotomy` packages the genuine
  source handoff: after normalization, every pair has either a noncube core or
  a nonzero cube root `s` with leading rows `s^6,s^9` and the first
  denominator-cleared cube-discriminator row.  Generation is transported
  equivalently back to the original pair.
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
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithHistoryAndDivisible69Exclusions`
  refines that interface to the actual historical residue: a nondivisible
  core is generated by the source-shear route, while the divisible core is
  exhausted by its cube and noncube exclusions.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithImportedDivisible69Exclusion`
  imports the kernel-checked exhaustive divisible-core source theorem and
  removes both divisible exclusions from the max-eleven interface.
- `Max11DegreeRoutes.planeKeller69SourceShearExactTotalDegree` proves that a
  sufficiently large source shear of a normalized `(6,9)` pair has total
  degrees exactly `2(H+3L)` and `3(H+3L)` by isolating the unique maximal
  shear-weight monomials.
- `Max11DegreeRoutes.imported_planeKeller69NondivisibleCoreRoute_of_primeTotalDegreeGCD`
  combines that degree calculation, source-shear invariance, and Mathlib's
  Dirichlet theorem to reduce `3 ∤ H` to the classical prime-total-degree-gcd
  result.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithPrimeTotalDegreeGCDRoute`
  reduces the historical `(6,9)` branch to the prime-total-degree-gcd theorem.
- `Max11DegreeRoutes.planeKellerAutomorphicAtDegrees_of_coprime_and_primeTotalDegreeGCD`
  proves every positive coprime partial-degree pair from that prime theorem,
  using only numerical leading-degree proportionality and an exact source
  shear.
- `Max11DegreeRoutes.planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScale`
  additionally proves every partial-degree gcd-two pair whose reduced common
  leading-degree scale is odd; only the even-scale interface remains.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithEvenLeadingScaleGCDTwoRoute`
  packages the uniform even-scale residue.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithFiveEvenScaleGCDTwoLeaves`
  is the current narrowest source-honest top of the tower: its inputs are the
  published prime-total-degree-gcd theorem and the even-scale subcase at only
  the five enumerated gcd-two degree pairs.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithPrimeAndTwicePrimeTotalDegreeGCDRoutes`
  records the fully assembled implication from prime and strong arbitrary-pair
  twice-prime total-degree routes.  The implication is checked; availability
  of the twice-prime premise is deliberately not asserted.
- `Max12FirstPrimitives` verifies the frontier checksum: at maximum twelve,
  the same direct routes first leave `(8,12)` and `(9,12)`.

## Scope and relationship to the source

The frozen source and independent hostile review prove a larger mathematical
composition: after the full `(6,9), 3 | H` leaf is excluded and the cited
classical degree reductions are applied, every characteristic-zero Keller pair
with maximum actual partial `y`-degree at most eleven is an automorphism.  This
Lean extraction checks the complete finite recursion and frontier arithmetic,
then instantiates the result for actual bivariate polynomials, their Jacobian,
partial `y`-degree, and coordinate-ring generation.  The divisible `(6,9)`
leaf is now discharged by imported kernel-checked source theorems.  This
project also proves the complete local nondivisible-core source-shear and
Dirichlet reduction.  It now proves the coprime partial-degree route and the
odd-common-scale half of partial-degree gcd two from the classical
prime-total-degree-gcd theorem.  It still does not prove scalar-extension
descent, the prime theorem itself, or the even-common-scale subcases of those
five gcd-two pairs.  Those last residues follow from an arbitrary-pair
twice-prime total-degree result.  A primary-source re-audit found that GGV
2017 proves only the
corresponding restriction on the globally minimal counterexample gcd `B`; it
explicitly records a gap in the earlier arbitrary-pair proof.
Thus the strong twice-prime interface in `TotalDegreeRoutes.lean` is retained
only as a precisely typed open premise, not described here as a proved
classical input.

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

`Max11Core.lean`, `ClassicalRoutes.lean`, `DegreeRoutes.lean`,
`HistoryRoute.lean`, `HistoryDegree.lean`, `TotalDegreeRoutes.lean`,
`CoprimeDegreeRoute.lean`, and `Max11Assembly.lean` contain no
`sorry`, custom axioms, or trust escapes.  The permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`.
