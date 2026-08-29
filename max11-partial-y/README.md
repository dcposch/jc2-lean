# Exact partial-`y` degree closure through eleven

This Lean 4 project formalizes the finite degree-routing certificate underlying
the campaign's maximum-partial-degree-eleven composition.  Once the standard
zero-degree, gcd-at-most-two, equal-degree, and divisibility reduction rules
are supplied, closing the single primitive pair `(6,9)` closes every ordered
pair `(m,n)` with `m,n ≤ 11`.

For Palomar verification, the already-verified `(6,9)` proof trees in the
three sibling directories are exposed as source libraries of this Lake
package.  This keeps all generated objects under this project's `.lake`
directory while preserving the exact in-repository theorem dependencies.

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
their scalar units for every one of the five pairs.  Both normalized `(4,6)`
sources, at scales zero and two, are now excluded outright; the other eight
normalized cases remain.  The current narrowest honest headline,
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithFourLowScaleLeaves`,
therefore asks for the published prime-gcd theorem, the literal numerical
standard-endpoint obstruction, and the two low-scale cases at each of the
other four leaves.  A separate checked adapter
shows that the strong arbitrary-pair
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
  is the common normalized handoff from which the low-scale campaign began:
  its ten literal cases share one exact normalized form, with reduced weights `(2,3)`,
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
  terminal `eta` row.  Evaluation at the depression center identifies both
  reviewed boundaries with explicit polynomials in `K[x]`; the resulting
  source package feeds the final component theorem directly and rules out
  `beta=delta=k2=0`.  Thus an actual aligned square-core source can remain
  only in the `beta != 0`, `beta=0, delta != 0`, or
  `beta=delta=0, k2 != 0` strata, whose local closures are already checked.
  `LowScale46GeneralSourceBridge.lean` proves the corresponding integration
  and coefficient-curve package for every ground-field quintic coefficient
  `L`, including the mismatch value `L=-lambda/2`.
  `LowScale46ScaleZero.lean` then closes the complete literal source when the
  common-core degree is zero.  The genuine discriminator dichotomy covers
  both aligned and mismatch branches; in either case the square root is a
  nonzero scalar, the depressed rational coefficients have exact polynomial
  representatives, and an exhaustive polynomial endgame contradicts the
  nonzero constant Jacobian row.
  `LowScale46PoleBridge.lean` starts the scale-two globalization with an
  injective translated finite-place embedding
  `K(x) -> K((t)) -> K((t^Q))`.  It preserves ground-field constants and
  polynomial equations, proves that literal polynomial boundary loads have
  nonnegative local order, and supplies an injective positive rescaling of
  rational exponents that normalizes any selected finite pole order to one.
  `LowScale46RegularLoads.lean` proves that the complete mismatch finite-pole
  exclusion is unchanged when the two scalar boundary terms are replaced by
  arbitrary Hahn-series loads of nonnegative order.  These are exactly the
  translated polynomial loads produced by the finite-place bridge.
  `LowScale46WeightedInfinity.lean` begins the remaining weighted-projective
  step with exact Hahn boundary-coefficient rules for products and powers.
  The pole bridge now also proves regularity of rational derivatives and
  uses the nonzero final Jacobian row to force a genuine curve-coordinate
  pole over every zero of the common core.
  `LowScale46Depression.lean` performs the exact source substitution
  `y=(z-r)/h` on the quartic and sextic and proves that the normalized quintic
  coefficient is zero in the aligned branch and `-lambda/2` in the mismatch
  branch.  `LowScale46Integrality.lean` turns both monic boundary eliminants
  into exact rational-function-to-polynomial results, reconstructs `K=B²`
  and `B`, and proves both square and nonsquare last-row unit-product
  contradictions (including the linear-`K` edge case).
  `LowScale46QuadraticField.lean` constructs the irreducible quadratic
  extension `K(x)(√H)` for a nonsquare core, its deck involution and fixed
  field, and the uniquely extended differential.  It also proves that the
  extension introduces no new differential constants.
  `LowScale46QuadraticSourceBridge.lean` maps a literal nonsquare aligned
  source into that field, proves the affine depression is deck-equivariant,
  forces the expected even/odd coefficient parities, and packages the exact
  curve, boundary, and last-row equations with `beta=delta=k2=0`.
  `LowScale46QuadraticEndgame.lean` descends the invariant quantities
  `q`, `B²`, `rB`, and `√H B` to `K(x)`, uses the monic boundary quartic to
  recover polynomial representatives, and applies `M²=HK` to close the
  nonsquare final row.
  Finally, `LowScale46ScaleTwo.lean` combines this nonsquare closure with the
  square aligned and mismatch weighted-infinity theorems.  Its theorem
  `normalized46ScaleTwo_impossible` is exhaustive, and
  `proved_planeKellerNormalized46LowScaleRoute` closes the entire `(4,6)`
  low-scale interface used by Max-11.
  `LowScale68NormalForm.lean` and `LowScale68Integrated.lean` begin the next
  `(6,8)` leaf.  They verify the complete twelve-row depressed sextic/octic
  differential Jacobian, integrate the seven triangular upper rows into the
  exact Faber coefficient reconstruction, extract the five remaining rows,
  and prove that the first two of those rows are the derivatives of explicit
  coefficient invariants.  The resulting lower-system theorem leaves exactly
  three literal one-form constraints, the last equal to the Keller constant;
  `LowScale68Depression.lean` additionally verifies the exact common affine
  depression of raw leading forms `h⁶y⁶,h⁸y⁸` and identifies the surviving
  septic coefficient with the first sextic/octic alignment discriminator;
  `LowScale68SourceBridge.lean` now transports the literal polynomial Keller
  bracket to `k(x)`, reconstructs both raw sources, and proves the common
  depressed bracket.  Its omitted top row forces the septic coefficient to be
  constant; that coefficient and all seven Faber residuals are then descended
  to the ground field, and the octic is reconstructed in integrated form.
  `LowScale68ScaleZero.lean` proves that scalar common scale makes the affine
  depression literal over `k[x]`, supplies polynomial representatives for all
  thirteen depressed coefficients, and descends both exact lower-row
  invariants to the ground field.  Thus the scale-zero branch is reduced to
  the polynomial-degree contradiction for the final three one-form rows.
  `LowScale68Infinity.lean` proves the first weighted-infinity elimination:
  the five top lower rows have only the depressed cubic-core solution
  `B=D=0`, `C=A²/3`, `E=A³/27`.  Extracting that scalar system from arbitrary
  polynomial loads is now completed in
  `LowScale68PolynomialBoundary.lean`: it defines literal polynomial versions
  of the four integrated octic coefficients, both exact invariants, and the
  final three one-form rows; proves their weighted boundary coefficients;
  pulls the rational-function system back through the injective
  `k[x] -> k(x)` map; and obtains the same cubic-core boundary for every
  positive integral weighted radius.  `LowScale68WeightedRadius.lean` now
  constructs the required attained radius canonically: the common expansion
  `x -> x^60` clears all five weight denominators, and the maximum of the five
  scaled degrees supplies the bounds together with a proof that at least one
  boundary coefficient is nonzero.  It also proves that a nonzero terminal row
  forces at least one original load to be nonconstant.
  `LowScale68Expansion.lean` now packages the exact five-row polynomial lower
  system, pulls it directly from the rational source bracket, proves that both
  invariants commute with expansion and that all three one-form rows acquire
  the common chain-rule factor, and applies the maximal-radius theorem.  Thus
  the canonical expanded boundary is nontrivial and has
  `B=D=0`, `C=A²/3`, `E=A³/27`, with the top `A` coefficient nonzero.
  `LowScale68CubicDescent.lean` translates the two exact invariants into the
  four transverse cubic coordinates, proves their strict degree drop, and
  rules out remaining identically on the exact cubic locus: the quartic first
  integral forces the relevant loads to vanish, after which the terminal
  one-form contradicts its nonzero Keller constant.
  `LowScale68SecondaryRadius.lean` then takes the minimum of the four actual
  degree deficits, without assuming that they are equal.  A sentinel removes
  zero defects; the exact-cubic contradiction proves that the positive gap is
  attained by a genuine nonzero defect and supplies all four sharpened degree
  bounds.  `LowScale68SecondaryFace.lean` gives the exact algebraic solver for
  the first chamber `2g<n`: the two invariant and three one-form face equations
  force `e=0` and `a*b=3*d`, so only `(b,c,d,e)=(3d,c,d,0)` survives.
  `LowScale68SecondaryExtraction.lean` and
  `LowScale68SecondaryOneForms.lean` derive both invariant equations and all
  three one-form equations from the literal polynomial system.  They prove
  arbitrary-bound coefficient and derivative rules, split the four integrated
  coefficients into load-free and strictly lower-weight pieces, and
  kernel-check the exact coefficients `F4`, `F3`, `F2`, `F1`, and `F0`.
  `LowScale68SecondarySmallGap.lean` applies those equations to the canonical
  expanded lower system: in the chamber `2g<n`, it proves `e=0`, `a*b=3*d`,
  and reduces the attained residual boundary to the `B` or translated-`C`
  direction.  `LowScale68SecondaryResidualFace.lean` introduces the translated
  defect `d=D-A*B/3` and kernel-checks the exact field-algebra solvers for the
  next prospective faces in the stricter chamber `3g<n`: the two one-sided
  endpoints are impossible, the tied endpoint forces the contradictory
  relation `g=4n`, and the middle face forces
  `a*b²+3*c²=0` with both residual directions nonzero.  Extracting those
  equations from the actual polynomial rows is now completed in
  `LowScale68SecondaryResidualExtraction.lean`: it proves strict degree drop
  for `d=D-A*B/3` and `e`, all five exact residual-coordinate identities,
  the invariant load cutoffs, and both middle-face coefficients.
  `LowScale68SecondaryResidualMiddle.lean` applies those results back to the
  canonical expanded lower system and proves the full middle classifier from
  explicit degree-gap data `g<h<2g`.
  `LowScale68SecondaryResidualDouble.lean` extracts the two double-gap
  invariant coefficients and the terminal two one-form coefficients, proves
  the sharper load cutoffs, transports all four equations to the canonical
  expanded system, and eliminates the strict-`D`, strict-`E`, and tied
  endpoints uniformly in `3g<n`.  `LowScale68SecondaryResidualSelector.lean`
  selects the minimum actual residual gap, proves it lies strictly between
  `g` and `2g`, eliminates its double-face alternative, and upgrades the
  surviving middle face to nonzero `A,B,c,d,e` satisfying
  `A*B²+3*c²=0`.  `LowScale68SecondaryResidualDescent.lean` packages the
  exact polynomial discriminant, incidence, and cubic defects, proves their
  invariant syzygies and strict degree cutoffs, and classifies the next
  comparison completely.  If `2h<3g`, the discriminant gap is exactly `g+h`;
  if `3g<2h`, it is exactly `4g-h`; on `2h=3g`, its boundary coefficient obeys
  the exact three-term cubic-face equation.  The row-two residual modules
  then split the literal lower system into residual and load terms, prove the
  load cutoff, eliminate both strict chambers, and force `2h=3g`.  On that
  balanced face they extract the exact relation
  `4*b*c^2-9*d*e=0`.  The canonical balanced wrapper derives both required
  cutoffs directly from the lower system, so its only extra chamber premise
  is `3g<n`.  The companion row-one modules split the literal second
  one-form, prove its load cutoff, and calculate its surviving coefficient as
  `(-64/9)*(4n-g)*c_top^3`, which is nonzero.  Thus the complete canonical
  `3g<n` residual chamber is impossible.  The complementary gap chambers and
  scale-two analysis remain open.
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
prime-total-degree-gcd theorem.  The exact external source for that premise is
Masayoshi Nagata, *Two-dimensional Jacobian Conjecture*, 1989 symposium
record, pp. 153--172, Theorem 7.3 on pp. 169--170.  It proves that a complex
Keller pair whose total-degree gcd is prime generates the full polynomial
ring; the corresponding Lean premise is
`PlaneKellerPrimeTotalDegreeGCDRoute`.  This project proves the exact
source-shear and Dirichlet reduction to that premise, not Nagata's
Newton-polygon proof.

The source-shear, UFD common-core normalization, target-rescaling transport,
complete normalized `(4,6)` low-scale closure, and the current `(6,8)`
development are first presented in this formalization; they are not claimed
as translations of Nagata or Guccione--Guccione--Valqui.  They refine the
included finite-composition report: the source-shear connects partial degree
to the two published total-degree interfaces, the normalization produces the
five literal low-scale leaves, and the low-scale modules begin discharging
those leaves internally.  The related proof trees are the registered
[source-facing `(6,9)` noncube exclusion](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-25-000002&version=2),
the sibling `gcd3-69-cube` project, and the sibling
`gcd3-69-noncube-v2` cube/noncube composition.

The project still does not prove scalar-extension descent, the prime theorem
itself, or the standard-pair endpoint theorem itself.  Among the eight cases
left after `(4,6)`, the `(6,8)` scale-zero case is now proved through its
canonical nontrivial expanded cubic-core top boundary, strict transverse
degree drop, exact-cubic contradiction, and an attained positive secondary
  defect radius.  All five small-gap face equations are extracted from the
  literal polynomial rows and applied to the canonical expanded system,
  forcing `e=0`, `a*b=3*d`, with attained support reduced to `B` or translated
  `C`.  In `3g<n`, the exact residual identities and degree drops select the
  balanced wall `2h=3g`; row two fixes its scalar relation and the next row-one
  coefficient is nonzero, closing that whole chamber.  In the complementary
  strict loaded chamber `n<2g`, the degree-`8n` quartic invariant now forces
  the old-weight load `l=0`; deeper in `3n<2g`, its degree-`6n` coefficient
  then forces `beta=0`.  After `l=0`, a relaxed extraction now recovers the
  complete five-equation first secondary face throughout `g<n`, and throughout
  `2g<3n` after the additional vanishing `alpha=0`; without row one, it also
  classifies the exact three surviving scalar families.  These statements are
  transported to the canonical expanded source system with the terminal
  `60*X^59` row handled explicitly.  On the equality wall `g=n`, the apparent
  `alpha` row-one cores cancel identically, so the ordinary fifth equation
  survives and again forces `e=0`, `a*b=3*d`, while leaving `alpha` free.
  This equality-wall classification is transported to the canonical expanded
  source system with the terminal row coefficient handled explicitly.  In the
  medium complement, the selected residual gap
  still satisfies `g<h`: on `g+h<n` the two ordinary residual middle-face
  equations survive, while the strict overshoot `n<g+h`, `n<3g` again forces
  `l=0`.  Once `l=0` is known in the strip `2g<n<3g`, the residual selector,
  balanced wall, and row-one contradiction replay without side conditions.
  On `n=3g`, five exact boundary modules cover every comparison of `2h`
  with `n` and of `h` with `2g`; their exhaustive selector closes the wall.
  Together with the original `3g<n` endgame, every chamber `2g<n` is now
  impossible.  The five abstract mixed equations on the equality wall `2g=n` are
  also classified exactly: they force `l=0`, `e=0`, and `a*b=3*d`.  Both
  invariant scalars, the homogeneous row-two/row-zero scalars, the load-free
  row-one scalar, and the cancellation-sensitive pure `l*A^5` cores are now
  checked literally.  The full row-two and row-zero loads are now split into
  those cores plus termwise lower remainders, completing the generic
  polynomial-system wall face and forcing `l=0`, `e=0`, `a*b=3*d`.
  The same classification is now transported to the canonical expanded
  source system, with the terminal row coefficient handled explicitly.
  Its strict residual drops select `h>g`; the middle/double invariant faces,
  row-two trichotomy, and nonzero balanced row-one coefficient then exclude
  every residual chamber, closing `2g=n` as well.  In `n<2g`, `g<n`, the
  load-zero classification now also supplies strict residual drops, an
  attained gap, sharp load cutoffs, and both residual invariant faces.  Its
  exact row-one alpha cores cancel identically after `l=0`; every surviving
  alpha-rest term has degree at most `10n-g-1`, strictly below the residual
  cubic face `12n-3g-1` whenever `g<n`.  Feeding that sharp cutoff into the
  complete one-form endgame closes the entire chamber `n<2g`, `g<n`, including
  the formerly separate `2n≤3g` region.  In the first deeper window
  `n<g<3n/2`, the same alpha-core cancellation now recovers the ordinary
  five-equation first face and its two strict residual degree drops without
  assuming `alpha=0`.  Its selected residual gap now carries the exact
  load-free I3 face and the complete `beta*A^3`-loaded I4 trichotomy,
  including both mixed walls and the cases where the I4 load first forces
  `beta=0`.  On the equality wall `g=n`, the canonical system now
  supplies `l=0`, strict residual drops, an attained gap, both ordinary
  middle invariant faces, and the exact mixed double I4 face where
  `beta*A^3` survives.  The four apparent alpha terms on its residual
  row-one face also cancel exactly, leaving the ordinary residual row-one
  coefficient.  Its six row-two load terms are now also computed exactly:
  every alpha core cancels and the unique survivor is
  `(5n/18) beta*a^4`.  Exact mixed row-zero faces now eliminate both the
  balanced face `2h=3g` and the residual double face `h≥2g`; consequently
  the entire alpha wall `g=n` is impossible.  The entire first-deep chamber
  `n<g<3n/2` is now impossible as well.  Exact row-two, row-one, row-zero,
  I4, and I3 faces eliminate its double and load-above branches; the wall
  `2h=3n` and left middle window fall to the next residual coefficients.
  Finally, after `beta=0`, the right window `3g<2h<4g` has a nonzero cubic
  row-two core, while the balanced wall `2h=3g` feeds a nonzero residual
  row-one scalar.  In the later `g≥3n/2` chamber, the fourth invariant now gives
  the complete `beta`/`delta` load cascade through `2g<8n`: it records both
  mixed walls, forces `beta=delta=0` between them and beyond, recovers the
  ordinary secondary face through `2g≤6n`, and then extracts the clamped-`B`
  face through `2g<8n`.  At `8n≤2g`, the exact cubic degree-`4n` and quartic
  degree-`2n` faces now force the clamped coefficient `B=0` and load
  `zeta=0`; the resulting constant-`c` scalar split and exact lower rows close
  that entire clamped chamber.  In the upper preclamped window, `7n<2g<8n`
  is also impossible; below it, the route now forces `B=0` for `6n<2g`,
  and the strict `6n<2g<7n` chamber is now impossible: the surviving
  `c_top` branch forces successive degree drops in `D` and `e`, then kills
  `D`, `zeta`, and finally the nonzero terminal row.  The exact wall
  `2g=7n` is also impossible after extracting its tied terminal-row face.
  The remaining `5n<2g≤6n` window is reduced by its I4, I3, terminal, and
  row-one faces to the single top family `e=0, a*b=3*d`; the other two
  apparent families are impossible.  Gap attainment further splits it into
  `b≠0,d≠0` or `b=d=0,c≠0`.  All five top-face equations vanish on this
  family, but the first lower residual coefficient is now exact: after the
  translated defects drop, its two incidence equations force either a second
  simultaneous degree drop, or the nonzero branch
  `b*c*d1*e1≠0` with `a*b^2+3*c^2=0`.  Expansion-lattice support now rules out
  the nonzero branches at both the `g+1` and `g+2` edges: any active translated
  discriminant edge must have displacement divisible by `60`.  The full
  support descent now forces every translated-defect coefficient at
  displacement `1≤s<60` to vanish and drops both defects by sixty degrees,
  except for the unique earliest load wall `n=30, g=90`.  On that wall the
  offset-30 I4 coefficient ties the `zeta*A` load and remains to be resolved.
  The lower
  `3n≤2g≤5n` window is reduced to three
  exact packets: the two endpoint load walls and an open branch with
  `beta=0`, vanishing `e_top`, and `a*b=3*d`.  On the open branch both
  translated defects now drop strictly and its attained residual gap satisfies
  `h>g`; I4 is classified across `g+h ? 5n`.  On the `2g=3n` wall, the next
  mixed row-zero face combines with I4 and row two through an explicit
  polynomial certificate to force `beta=0`; the ordinary five-face
  classification then gives `e_top=0` and `a*b=3d`.  Thus this endpoint can
  enter the same residual descent rather than remain a separate beta packet.
  The `2g=5n` mixed-delta face and the subsequent residual packets remain.
  Lower coefficients remain to exclude them.  The remaining literal normalized low-scale subcases
  remain open.  Source-level scale-zero assembly is now
  complete: every literal normalized source produces a nonzero-terminal
  `IntegratedPolynomialLowerSystem68`, so only the intrinsic global
  exclusion of that system remains.  For the `(6,8)` scale-two source, the
  next literal Jacobian row now classifies the complete first face: its
  discriminator is
  either zero or the seventh power of a degree-one polynomial times a nonzero
  scalar, while the common quadratic core is its square.  The latter branch
  therefore has an
  explicit finite root.  At that root, exact Hahn extraction now forces the
  five cubic top rows to vanish and yields the first Newton-box descent
  `h0 ∣ p.coeff 5`.  The improved `rho=4` box then strengthens this to
  `h0^2 ∣ p.coeff 5`, the `rho=3` box gives `h0^3 ∣ p.coeff 5`, and the
  two mixed rows at `rho=2` have an explicit Bezout certificate that gives
  `h0^4 ∣ p.coeff 5`.  Two consecutive nonuniform boxes then force
  `h0^2 ∣ p.coeff 4`.  The next `rho=1` box is a coupled packet involving
  the `p3`, `p4/h0^2`, and `p5/h0^4` quotients.  Its scalar top rows have a
  genuine cubic-core branch `v=z^2/3`, `t=z^3/27`.  On that branch the first
  transverse coefficient forces `z=0`, hence simultaneously
  `h0^5∣p5`, `h0^3∣p4`, and `h0∣p3`.  An exact elimination certificate now
  splits the full two-row residual into that cubic point and one disjoint
  degree-ten component `P10(v/z^2)=0`.  The next literal differential/Hahn
  row is now extracted too, refining the non-cubic branch to the finite affine
  packet `P10(V)=F4(T,V)=F3(T,V)=F2(T,V)=0`.  A staged quadratic-resultant
  and univariate Bezout certificate eliminates this packet: the three rows
  force `V=1/3`, while `P10(1/3)=-90`.  Thus every rho-one component gives
  the simultaneous descent `h0^5∣p5`, `h0^3∣p4`, and `h0∣p3`.  In the next
  sharp local box, the unique pole-six face is `-(8/27)B^3`, which strengthens
  the last divisibility to `h0^2∣p3`.  Substituting that descent gives the
  sharp box `(1,1,2,2,2)`; its pole-five face factors as
  `a(3x-a^2)(9x-2a^2)`.  Hence either `h0^4∣p4`, or one of those two exact
  algebraic branches remains.  The next I4 coefficient further forces
  `512b+119*l*a=0` on `3x=a^2`, and
  `4608d-1536ab+77*l*a^2=0` on `9x=2a^2`; the next I3 row must track the
  improved-order defect on each branch.  Those two defect cancellations and
  their exact I3 rows are now formalized; each remaining branch determines
  its transverse defect coefficient together with `d` or `e`, so one further
  Hahn/differential coefficient is required.
  For all six
  `(4,10)`, `(6,10)`, and `(8,10)` leaves, an exact large source-shear
  calculation gives total-degree gcd `H+2L`; prime selection reduces them
  uniformly to the deliberately open arbitrary-pair twice-prime interface,
  but does not assert that interface.  Independently, the `(4,10)` scale-two
  source now has its exact first discriminator face: if
  `N=5*p3*H^3-2*q9`, then `N^2=C κ*H^9`.  Thus either `N=0`, or the
  quadratic core is a square and the nonzero face is a ninth power of a
  degree-one polynomial with a concrete finite root.  The `(6,10)` scale-two
  source has the parallel exact packet with `N=5*p5*H^2-3*q9`, again giving
  `N^2=C κ*H^9` and a finite linear root on the nonzero face.  The `(8,10)`
  source likewise has `N=5*p7*H-4*q9` with the same square/ninth-power
  dichotomy and finite-root packet.  The direct `(4,10)`
  route now has an exact decic differential normal form: nine upper rows are
  integrated explicitly, leaving precisely three terminal lower rows.  It does
  more: the first two terminal rows are exact derivatives of explicit
  polynomial first integrals, so the direct endgame is reduced to two constant
  invariant equations and the single genuinely non-exact row
  `W*C₀' - B*Z' = terminal`.  Discriminant coordinates now exclude every
  zero-load constant fiber.  The zero first-invariant fiber reduces to
  `U³-B⁴ = constant` and `8(B³U)' = nonzero constant`; on a nonzero fiber,
  the shifted primitive `8B³U-c₂A` has degree one, contradicting the even
  degree forced on `A`.  Only the nonzero-load cascade remains open in this
  direct branch.  The load correction is now sharply bounded and the terminal
  row depends on exactly seven effective loads (`l`, `beta`, `gamma`, `delta`,
  `zeta`, `eta`, `theta`).  On the first `l≠0` Newton wall, discriminant
  coordinates now exclude the low-`U` chamber
  `(deg A,deg B,deg U)=(3n,4n,<5n)` by incompatible leading-coefficient
  equations.  At `deg U=5n` only the scalar wall
  `7 lc(A)lc(U)=9 lc(B)^2` is eliminated by the exact terminal face; above
  it every chamber is impossible except `2 deg U=11n`, whose two scalar
  relations are also incompatible with its terminal face.  The rest of the
  closed Newton sector is now eliminated as well: its strict intermediate
  cone gives incompatible constant-invariant faces, and the aligned
  `(deg A,deg B,deg U)=(2n,3n,4n)` endpoint contradicts the terminal row.
  The arithmetic fan split leaves no cone inside that sector.  Exact exposed-
  vertex exclusions now supply the source-level Newton-support connector, and
  the zero-degree boundary classification closes every remaining mixed case.
  Hence every source trajectory on the `l≠0` wall is impossible, with no
  degree or coordinate-nonzero assumptions.  The other six effective load
  walls remain.
The low-scale core proves the common-power UFD factorization, exact
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

The first-presentation statement above records provenance, not an external
priority determination.  The hostile review is campaign-internal, not
external human peer review.

## Verification

```sh
lake build
./scripts/check_axioms.sh
# On the dedicated box, sync and verify selected modules in one command:
./scripts/box_lean_verify.sh LowScale410LoadCascade
# Scratch and untracked canonical imports are rebuilt transitively:
./scripts/box_lean_verify.sh --file Sol410ScaleZeroLWallBoundaryScratch.lean
# Returned lanes can share one isolated sync and dependency walk:
./scripts/box_lean_verify.sh --file LaneOneScratch.lean --file LaneTwoScratch.lean
```

`Max11Core.lean`, `ClassicalRoutes.lean`, `DegreeRoutes.lean`,
`HistoryRoute.lean`, `HistoryDegree.lean`, `TotalDegreeRoutes.lean`,
`CoprimeDegreeRoute.lean`, `EndpointGCDRoute.lean`, `LowScaleCore.lean`, and
`LowScale46Rows.lean`, `LowScale46NormalForm.lean`, `LowScale46Curve.lean`,
`LowScale46LocalChart.lean`, `LowScale46AlignedChart.lean`,
`LowScale46DegreeCones.lean`, `LowScale46Depression.lean`,
`LowScale46Integrality.lean`, `LowScale46QuadraticField.lean`,
`LowScale46QuadraticSourceBridge.lean`, `LowScale46QuadraticEndgame.lean`,
`LowScale46NewtonFaces.lean`,
`LowScale46PolynomialEndgame.lean`, `LowScale46FinitePoles.lean`,
`LowScale46AlignedFinitePoles.lean`,
`LowScale46AlignedPolynomialEndgame.lean`,
`LowScale46AlignedZeroFinitePoles.lean`,
`LowScale46AlignedComponentEndgame.lean`, `LowScale46SourceBridge.lean`,
`LowScale46GeneralSourceBridge.lean`, `LowScale46ScaleZero.lean`,
`LowScale46PoleBridge.lean`, `LowScale46RegularLoads.lean`,
`LowScale46AlignedRegularLoads.lean`, `LowScale46WeightedInfinity.lean`,
`LowScale46ScaleTwo.lean`, `LowScaleOtherLeaves.lean`,
`LowScale410NormalForm.lean`,
`LowScale410FirstIntegrals.lean`,
`LowScale410ZeroLoadTrajectory.lean`,
`LowScale410ZeroLoadShiftedFiber.lean`,
`LowScale410LoadCascade.lean`, `LowScale410LWall.lean`,
`LowScale410LWallBoundary.lean`, `LowScale410LWallResidual.lean`,
`LowScale410LWallOtherCones.lean`,
`LowScale410LWallFanConnector.lean`,
`LowScale410LWallUnconditional.lean`, `LowScale410GammaWall.lean`,
`LowScale410DeltaWall.lean`, `LowScale410DeltaWallElimination.lean`,
`LowScale410ThetaWallElimination.lean`,
`LowScale410ZetaEtaWalls.lean`,
`LowScale410MixedEffectiveWalls.lean`,
`LowScale410EtaThetaAndDegenerate.lean`,
`LowScale410ScaleZeroAssembly.lean`,
`LowScale410ScaleZeroSourceBridge.lean`,
`LowScale410ScaleZeroEarlyLoadElimination.lean`,
`LowScale410ScaleZeroGroundIntegration.lean`,
`LowScale410ScaleZeroNonzeroBetaCone.lean`,
`LowScale410ScaleZeroBetaCubicWall.lean`,
`LowScale410ScaleZeroBetaCubicTie.lean`,
`LowScale410ScaleZeroBetaCubicNonzeroCTie.lean`,
`LowScale410BetaWall.lean`,
`LowScale410ScaleTwoSourceFace.lean`, `LowScale410ScaleTwoSecondFace.lean`,
`LowScale410ScaleTwoThirdFace.lean`,
`LowScale410ScaleTwoFourthFace.lean`,
`LowScale410ScaleTwoFifthFace.lean`,
`LowScale610ScaleTwoSourceFace.lean`,
`LowScale610ScaleTwoSecondFace.lean`, `LowScale610ScaleTwoThirdFace.lean`,
`LowScale610ScaleTwoFourthFace.lean`, `LowScale610ScaleTwoFifthFace.lean`,
`LowScale610ScaleTwoSixthFace.lean`,
`LowScale810ScaleTwoSourceFace.lean`,
`LowScale810ScaleTwoSecondFace.lean`, `LowScale810ScaleTwoThirdFace.lean`,
`LowScale810ScaleTwoFourthFace.lean`, `LowScale810ScaleTwoFifthFace.lean`,
`LowScale68NormalForm.lean`,
`LowScale68Integrated.lean`, `LowScale68Depression.lean`,
`LowScale68SourceBridge.lean`, `LowScale68ScaleZero.lean`,
`LowScale68ScaleZeroAssembly.lean`,
`LowScale68ScaleTwoSourceFace.lean`,
`LowScale68ScaleTwoNonalignedInfinity.lean`,
`LowScale68ScaleTwoLocalInitialForms.lean`,
`LowScale68ScaleTwoLocalRowThree.lean`,
`LowScale68ScaleTwoLocalDerivativeRowTwo.lean`,
`LowScale68ScaleTwoIntegratedBoundary.lean`,
`LowScale68ScaleTwoLocalRowOneZero.lean`,
`LowScale68ScaleTwoAfterRhoOne.lean`,
`LowScale68ScaleTwoAfterRhoOneNextBox.lean`,
`LowScale68ScaleTwoAfterRhoOneBranchRows.lean`,
`LowScale68ScaleTwoAfterRhoOneImprovedDefect.lean`,
`LowScale68ScaleTwoAfterRhoOneImprovedDefectNextRow.lean`,
`LowScale68ScaleTwoAfterRhoOneImprovedDefectRowOne.lean`,
`LowScale68ScaleTwoAfterRhoOneAfterP4.lean`,
`LowScale68ScaleTwoAfterRhoOneAfterP3.lean`,
`LowScale68ScaleTwoAfterRhoOneAfterP3Residual.lean`,
`LowScale68ScaleTwoAfterRhoOneAfterP3Closure.lean`,
`LowScale68ScaleTwoClosureBridge.lean`,
`LowScale68ScaleTwoAlignedFace.lean`,
`LowScale68ScaleTwoAlignedSecondDefect.lean`,
`LowScale68ScaleTwoAlignedNonsquareBridge.lean`,
`LowScale68ScaleTwoAlignedNonsquareEndgame.lean`,
`LowScale68ScaleTwoAlignedNonsquareRepresentatives.lean`,
`LowScale68ScaleTwoAlignedNonsquarePolynomialEndgame.lean`,
`LowScale68ScaleTwoAlignedSquareDescent.lean`,
`LowScale68ScaleTwoAlignedSquareRowTwo.lean`,
`LowScale68ScaleTwoAlignedSquareLowerRows.lean`,
`LowScale68ScaleTwoAlignedSquareRhoFour.lean`,
`LowScale68ScaleTwoAlignedSquareRhoThree.lean`,
`LowScale68ScaleTwoAlignedSquareRhoTwo.lean`,
`LowScale68ScaleTwoAlignedSquareP4First.lean`,
`LowScale68ScaleTwoAlignedSquareP4Second.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOne.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicNext.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicBridge.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicComponents.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicRemainder.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicComponentOne.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicRowOneRemainder.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicRowOneSource.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangent.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangentInvariants.lean`,
`LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangentOrderBridge.lean`,
`LowScale68ScaleTwoLocalRhoFour.lean`,
`LowScale68ScaleTwoLocalRhoThree.lean`,
`LowScale68ScaleTwoLocalRhoTwo.lean`,
`LowScale68ScaleTwoAfterRhoTwo.lean`,
`LowScale68ScaleTwoLocalRhoOne.lean`,
`LowScale68ScaleTwoRhoOneTransverse.lean`,
`LowScale68ScaleTwoRhoOneComponentSplit.lean`,
`LowScale68ScaleTwoRhoOneNoncubicNext.lean`,
`LowScale68ScaleTwoRhoOneNoncubicElimination.lean`, `LowScaleRemainingShear.lean`,
`LowScale68Infinity.lean`, `LowScale68PolynomialBoundary.lean`,
`LowScale68WeightedRadius.lean`, `LowScale68Expansion.lean`,
`LowScale68CubicDescent.lean`, `LowScale68SecondaryRadius.lean`,
`LowScale68SecondaryFace.lean`, `LowScale68SecondaryExtraction.lean`,
`LowScale68SecondaryOneForms.lean`, `LowScale68SecondarySmallGap.lean`,
`LowScale68SecondaryResidualFace.lean`,
`LowScale68SecondaryResidualExtraction.lean`,
`LowScale68SecondaryLargeGapLoads.lean`,
`LowScale68SecondaryRelaxedFirstFace.lean`,
`LowScale68SecondaryRelaxedCanonical.lean`,
`LowScale68SecondaryAlphaWall.lean`,
`LowScale68SecondaryLargeGapAlphaCancellation.lean`,
`LowScale68SecondaryLargeGapTransport.lean`,
`LowScale68SecondaryLargeGapClosure.lean`,
`LowScale68SecondaryAlphaWallCanonical.lean`,
`LowScale68SecondaryAlphaWallEndgame.lean`,
`LowScale68SecondaryAlphaWallRowOneLoad.lean`,
`LowScale68SecondaryAlphaWallRowTwoLoad.lean`,
`LowScale68SecondaryAlphaWallMixedEndgame.lean`,
`LowScale68SecondaryAlphaWallBalancedRowZero.lean`,
`LowScale68SecondaryFirstLoadWallFace.lean`,
`LowScale68SecondaryFirstLoadWallCore.lean`,
`LowScale68SecondaryFirstLoadWallRemainder.lean`,
`LowScale68SecondaryFirstLoadWallCanonical.lean`,
`LowScale68SecondaryFirstGapBoundaryFace.lean`,
`LowScale68SecondaryFirstGapBoundary.lean`,
`LowScale68SecondaryLargeGapResidual.lean`,
`LowScale68SecondaryLargeGapLoadZeroFace.lean`,
`LowScale68SecondaryLargeGapSubcritical.lean`,
`LowScale68SecondaryDeepGapCascade.lean`,
`LowScale68SecondaryDeepGapResidualOneForms.lean`,
`LowScale68SecondaryDeepGapResidualEndgame.lean`,
`LowScale68SecondaryDeepGapMiddleBetaEndgame.lean`,
`LowScale68SecondaryDeepGapMiddleBetaNextOrder.lean`,
`LowScale68SecondaryDeepGapMiddleRightEndgame.lean`,
`LowScale68SecondaryLaterDeepLoadCascade.lean`,
`LowScale68SecondaryLaterDeepLowerEndgame.lean`,
`LowScale68SecondaryLaterDeepLowerResidual.lean`,
`LowScale68SecondaryLaterDeepThreeRadiusWallNext.lean`,
`LowScale68SecondaryLaterDeepThreeRadiusWallElimination.lean`,
`LowScale68SecondaryLaterDeepThreeRadiusResidualEntry.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusWallElimination.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusResidualDescent.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusResidualEndgame.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusScalarFaces.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusExactWalls.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusZeroResidual.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalResiduals.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalLeafAlgebra.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalLeafAssembly.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalEqualityFaceAlgebra.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalEqualityAssembly.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalRowZeroAlgebra.lean`,
`LowScale68SecondaryLaterDeepFiveRadiusTerminalEndgame.lean`,
`LowScale68SecondaryLaterDeepLowerParentAssembly.lean`,
`LowScale68SecondaryLaterDeepThreeRadiusResidualFaces.lean`,
`LowScale68SecondaryLaterDeepThreeRadiusResidualSelector.lean`,
`LowScale68SecondaryLaterDeepMixedTwoNFace.lean`,
`LowScale68SecondaryLaterDeepClampedEndgame.lean`,
`LowScale68SecondaryLaterDeepPreclampedEndgame.lean`,
`LowScale68SecondaryLaterDeepPreclampedLowerEndgame.lean`,
`LowScale68SecondaryLaterDeepSixToSevenLowerCoefficient.lean`,
`LowScale68SecondaryLaterDeepSevenBoundaryEndgame.lean`,
`LowScale68SecondaryLaterDeepFiveToSixEndgame.lean`,
`LowScale68SecondaryLaterDeepFiveToSixRowOne.lean`,
`LowScale68SecondaryLaterDeepFiveToSixLowerCoefficient.lean`,
`LowScale68SecondaryLaterDeepFiveToSixResidualNext.lean`,
`LowScale68SecondaryLaterDeepFiveToSixNonzeroEdge.lean`,
`LowScale68SecondaryLaterDeepFiveToSixStrideDescent.lean`,
`LowScale68SecondaryLaterDeepFiveToSixEarliestWall.lean`,
`LowScale68SecondaryResidualMiddle.lean`,
`LowScale68SecondaryResidualDouble.lean`,
`LowScale68SecondaryResidualDoubleLoadWall.lean`,
`LowScale68SecondaryResidualDoubleLoadWallCanonical.lean`,
`LowScale68SecondaryResidualSumLoadWall.lean`,
`LowScale68SecondaryResidualHalfRadiusLoadWall.lean`,
`LowScale68SecondaryResidualHalfRadiusI4Wall.lean`,
`LowScale68SecondaryResidualHalfRadiusBoundary.lean`,
`LowScale68SecondaryResidualLeftLoadWindow.lean`,
`LowScale68SecondaryResidualLeftBoundary.lean`,
`LowScale68SecondaryResidualRowTwoLoadDominance.lean`,
`LowScale68SecondaryResidualOvershootCanonical.lean`,
`LowScale68SecondaryResidualOvershootBoundary.lean`,
`LowScale68SecondaryResidualThreeGapBoundaryMiddle.lean`,
`LowScale68SecondaryResidualThreeGapBoundarySelector.lean`,
`LowScale68SecondaryResidualStripSelector.lean`,
`LowScale68SecondaryResidualSelector.lean`,
`LowScale68SecondaryResidualDescent.lean`,
`LowScale68SecondaryResidualRowTwoSystem.lean`,
`LowScale68SecondaryResidualRowTwoFaces.lean`,
`LowScale68SecondaryResidualRowTwoBalanced.lean`,
`LowScale68SecondaryResidualBalancedSelector.lean`,
`LowScale68SecondaryResidualCanonicalBalanced.lean`,
`LowScale68SecondaryResidualCanonicalBalancedData.lean`,
`LowScale68SecondaryResidualRowOneFaces.lean`,
`LowScale68SecondaryResidualRowOneSystem.lean`,
`LowScale68SecondaryResidualBalancedEndgame.lean`,
`LowScale68SecondaryResidualLoadZeroEndgame.lean`, and
`Max11Assembly.lean`
contain no `sorry`, custom axioms, or trust escapes.  The
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
