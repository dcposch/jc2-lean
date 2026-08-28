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
`(8,10)`.  `EndpointGCDRoute.lean` then gives a source-shear adapter to the
reliable standard-pair endpoint obstruction of
Guccione--Guccione--Valqui: its normalized endpoint has coordinate gcd
strictly greater than two.  This eliminates every even common-leading scale
`H > 2`.  Consequently
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves`
leaves only the scales `H = 0` and `H = 2` at those five pairs.  Finally,
`LowScaleCore.lean` derives the exact common-power leading rows and removes
their scalar units for every one of the five pairs.  The current narrowest
honest headline,
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes`,
therefore asks only for the published prime-gcd theorem, the literal numerical
standard-endpoint obstruction, and the five uniform normalized `H = 0/2`
routes.  A separate checked adapter shows that the strong arbitrary-pair
twice-prime total-degree interface would close all five, but that interface is
not treated as an established theorem.

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
  reduces the inputs to the published prime-total-degree-gcd theorem and the
  even-scale subcase at only the five enumerated gcd-two degree pairs.
- `Max11DegreeRoutes.planeKellerLeadingScaleAtDegrees_of_gcd_two_of_two_lt_scale`
  proves that the classical standard-pair endpoint obstruction closes every
  one of those leaves at an even common scale `H > 2`.  The proof checks the
  exact source-shear degree, leading-coefficient preservation, normalized
  endpoint `(2,H)`, and transport of Keller and generation predicates.
- `Max11DegreeRoutes.planeKellerStandardEndpointGCDRoute_of_obstruction`
  derives the older generation-form compatibility interface from the
  literature's exact numerical conclusion `2 < gcd(u,v)` by contradiction.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves`
  reduces the top of the tower to the
  prime-total-degree-gcd theorem, the literal standard-pair endpoint gcd
  obstruction, and only the scales `H = 0` and `H = 2` at the five enumerated
  pairs.
- `Max11DegreeRoutes.planeKellerPair_46_normalizeAtScale`, together with its
  `(4,10)`, `(6,8)`, `(6,10)`, and `(8,10)` analogues, proves from the top
  Jacobian row that every residual pair has exact leading coefficients
  `alpha*h^r,beta*h^s`, removes both scalar units by target rescaling, and
  identifies `deg h = H`.  The nonconsecutive `(2,5)` and `(3,5)` UFD cases
  are reduced internally to the square/cube lemma.
- `Max11DegreeRoutes.Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes`
  is the current narrowest source-honest headline: the ten remaining literal
  cases now share one exact normalized form, with reduced weights `(2,3)`,
  `(2,5)`, `(3,4)`, `(3,5)`, and `(4,5)` and common-core degree zero or two.
- `Max11DegreeRoutes.planeKellerPair_46_imprimitiveDiscriminatorDichotomy`
  begins the genuine `(4,6)` closure from an actual normalized Keller pair.
  Its next Jacobian row gives `N² = κH⁵`; over an algebraically closed field
  this splits exactly into `N = 0` or `H = h², N = λh⁵` with `λ ≠ 0`.
- `Max11DegreeRoutes.differentialJacobian_integrated46_eq` works over an
  arbitrary characteristic-zero differential field extension.  It verifies
  all eight depressed quartic/sextic Jacobian rows, the five integrated upper
  coefficients, and the two first integrals `I₂,I₁`; only the constant last
  row remains in that normal form.
- `Max11DegreeRoutes.differentialJacobian_integratedDiscriminant46_eq`
  changes to `U=A²-4C` and identifies the entire remaining Jacobian with the
  two exact coefficient-curve rows `dJ₂,dJ₁` and the reviewed one-form `η`.
  The same module derives both translated-origin boundary equations by exact
  polynomial evaluation and proves that the four weighted-leading forms have
  unique weighted-projective common zero `[1:0:0:0]`.
- `LowScale46LocalChart.lean` verifies all four full cleared equations in the
  weighted chart at that point, with no truncation, and proves the terminal
  mismatch leading system inconsistent.  `LowScale46AlignedChart.lean`
  verifies the aligned Newton polynomials, the shifted plane curve
  `Φ(A)²=X²R(A,X)`, the component equations and restricted one-form, and both
  monic boundary eliminants.  `LowScale46DegreeCones.lean` replaces the
  report's finite integer scans by exact proofs of the unique positive cones
  `(4,5,7)`, `(4,3,5)`, and `(4,1,3)` and their one-form degree gaps.  It also
  proves the generic polynomial leading-term principle that four nonzero
  displayed terms summing with a strictly lower-degree remainder must have a
  tied maximum degree.  `LowScale46PolynomialEndgame.lean` instantiates that
  principle on the exact two coefficient-curve equations and closes the
  complete mismatch polynomial endgame: all eight constant/nonconstant
  patterns of `(A,B,U)` are incompatible with a nonzero constant last row.
  `LowScale46FinitePoles.lean` instantiates all four full local-chart rows on
  rational-exponent Hahn series and closes the mismatch finite-pole chart
  exhaustively, allowing each of `Q,Y,Z` either to vanish identically or to
  have finite positive order.  The nonzero case forces
  `(v(Q),v(Y),v(Z))=(1/4,1/2,1/2)` and the terminal boundary contradiction;
  `Y=0` or `Z=0` is killed by the isolated order-one `J₂` term, while `Q=0`
  is killed by the exact `J₂,F,J₁` leading system.
  `LowScale46AlignedFinitePoles.lean` performs the corresponding full-row
  Hahn-series instantiation in the aligned chart.  It applies the exhaustive
  Newton tables to the literal higher remainders and excludes both
  `beta ≠ 0` and `beta=0, delta ≠ 0`, including the identically-zero `Q` and
  `Y` loci.  Thus every aligned finite-pole branch reaches
  `beta=delta=0`.
  `LowScale46AlignedPolynomialEndgame.lean` handles the complementary
  no-finite-pole branch over `F[x]`.  It proves the exact shifted curve and
  one-form identities, derives the actual beta and delta degree cones and
  leading relations, and excludes a nonzero constant last row in both strata
  for all eight constant/nonconstant patterns of the shifted variables.  This
  includes the exceptional line `A=V=delta=0`, where the last row has degree
  `3 deg(X)-1`.  The certified all-nonconstant terminal degrees are `12n-1`
  in the beta stratum and `8n-1` in the delta stratum; the final theorems are
  transported back to the literal original coefficient rows.  The terminal
  `beta=delta=0` stratum is also exhaustive: `k2!=0` freezes all coefficient
  functions, while `k2=0` splits into `B=0` and `V=0`, the latter closing by
  the square unit-product theorem.  Thus every aligned polynomial trajectory
  has now been excluded.
  `LowScale46AlignedZeroFinitePoles.lean` begins the remaining final-stratum
  finite-pole calculation.  It verifies the exact cleared equations for
  `W=s^4(U-8gamma/3)` and proves directly from the literal local `J2,J1`
  rows that `k2!=0` forces `v(Y)=v(W)=7/2`.  It then exhausts the three
  possibilities for `2v(Q)` against `7/2`: the lower case violates the first
  boundary, the higher case gives incompatible leading coefficients, and the
  tie makes `Q^3` uniquely lowest in the exact second boundary.  Hence every
  final aligned finite-pole branch reaches `k2=0`.
  `LowScale46AlignedComponentEndgame.lean` closes the resulting component
  algebra.  Over the square working field it starts from the literal curve,
  boundary, and last-row equations, splits `BV=0`, uses the monic octic on
  `A=0` and the monic quartic when `theta!=0`, recovers polynomial
  representatives, and reaches the square unit-product contradiction.  Its
  quadratic-descent endpoint differentiates `K=B²`, transports the last row
  to `(-3/8) M K'`, and applies `M²=HK` to obtain the nonsquare contradiction.
  `LowScale46SourceBridge.lean` now carries the genuine-source handoff through
  the coefficient curve.  It exposes the standard quotient-rule differential
  on `K(x)` as a `K`-derivation, maps the literal coefficient-polynomial
  Jacobian into the differential bracket, proves that `y=(z-r)/h` divides that
  bracket exactly by `h`, identifies mapped degree-four and degree-six sources
  with the raw coefficient forms, and constructs the full depressed `L=0`
  package from any literal square-core aligned source.  It then extracts the
  five upper rows, successively integrates them, proves that all five
  integration parameters descend to `K`, and extracts ground-field values
  `k2,k1` for the two coefficient-curve equations together with the exact
  terminal `eta` row.
  `LowScale46Depression.lean` performs the exact source substitution
  `y=(z-r)/h` on the quartic and sextic and proves that the normalized quintic
  coefficient is zero in the aligned branch and `-lambda/2` in the mismatch
  branch.  `LowScale46Integrality.lean` turns both monic boundary eliminants
  into exact rational-function-to-polynomial results, reconstructs `K=B²`
  and `B`, and proves both square and nonsquare last-row unit-product
  contradictions (including the linear-`K` edge case).
  `LowScale46NewtonFaces.lean` proves the underlying three- and four-term
  Hahn-series tied-minimum principle and the complete rational Newton-face
  tables for the aligned `beta ≠ 0` and `delta ≠ 0` strata.
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
descent, the prime theorem itself, the standard-pair endpoint theorem itself,
or the literal normalized common-core `H = 0` and `H = 2` subcases of those
five gcd-two pairs.  It does prove the common-power UFD factorization, exact
core degree, scalar normalization, and generation transport for all five.
The endpoint theorem is the first assertion of Guccione--Guccione--
Valqui's Corollary 7.9 and applies to every standard pair.  By contrast, the
same corollary's `B \ne 2p` assertion concerns only the globally minimal
counterexample gcd `B`; a primary-source re-audit confirmed that it does not
supply an arbitrary-pair twice-prime theorem and records a gap in the earlier
proof.
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
`CoprimeDegreeRoute.lean`, `EndpointGCDRoute.lean`, `LowScaleCore.lean`, and
`LowScale46Rows.lean`, `LowScale46NormalForm.lean`, `LowScale46Curve.lean`,
`LowScale46LocalChart.lean`, `LowScale46AlignedChart.lean`,
`LowScale46DegreeCones.lean`, `LowScale46Depression.lean`,
`LowScale46Integrality.lean`, `LowScale46NewtonFaces.lean`,
`LowScale46PolynomialEndgame.lean`, `LowScale46FinitePoles.lean`,
`LowScale46AlignedFinitePoles.lean`,
`LowScale46AlignedPolynomialEndgame.lean`,
`LowScale46AlignedZeroFinitePoles.lean`,
`LowScale46AlignedComponentEndgame.lean`, `LowScale46SourceBridge.lean`, and
`Max11Assembly.lean`
contain no `sorry`, custom axioms, or trust escapes.  The
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
