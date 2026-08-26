# Aligned noncube exclusion at partial degrees `(6,9)`

This Lean 4 project proves the full noncube gate for the aligned
nontrivial cubic-Kummer branch at actual partial degrees `(6,9)`.  Starting
from a general simultaneously depressed Keller bracket, it first integrates
the eight high rows to the reviewed five-coefficient-plus-`kappa` normal form,
modulo constant target shear and translation.  It then extracts the four lower
coefficient rows, derives the Kummer first integrals and two-sheet
invariant-fibre split, and rules out every resulting sheet.  The common-power
sheet has zero bracket;
the nonzero elliptic fibres are excluded for both constant and nonconstant
rational trajectories; and the special elliptic fibre reduces to the shifted
Davenport–Stothers valuation contradiction.

The headline theorem is `GCD369AlignedNoncubeExclusion`.  Its hypotheses make
explicit the cubic-Kummer weights, the constant-field descent, the polynomial
core `h=H(x)`, reduced rational presentations for the elliptic coordinate and
the shifted parameter, and the noncube condition on `H`.  It does not assert
the cube-core branch, a general `(6,9)` theorem, maximum partial degree eleven,
or the plane Jacobian conjecture.

The source-facing prelude now also formalizes the first alignment step:
`GCD369AlignmentDiscriminatorDerivative` turns the denominator-cleared first
Keller row into differential constancy of `3a/s⁵-2b/s⁸`, and
`GCD369KummerAlignmentFromFirstRow` proves that a nontrivial cubic Kummer
action forces this weight-one discriminator to vanish.
`GCD369NoncubeCubicKummerExtension` constructs the required irreducible
adjoin-root extension and nontrivial deck action from a noncube field element;
these are no longer merely assumed abstract objects.
`GCD369PolynomialNoncubeInRatFunc` proves that polynomial noncubeness survives
passage to `k(x)`, and `GCD369PolynomialNoncubeKummerExtension` composes both
steps into the Kummer data used by the normalized noncube route.
`GCD369KummerRootDerivative` differentiates the cubic root equation in the
canonical extension, while `GCD369KummerDeckCommutesWithDerivative` proves
that its deck action respects this differential structure.
`GCD369RatFuncConstantsOfPolynomialDerivative` proves directly from reduced
numerator/denominator coprimality that standard differentiation on `k(x)` has
constant field exactly `k`.
`GCD369RatFuncStandardDifferential` constructs that quotient-rule differential
structure and packages the derivative and constant-field conclusions without
an existence hypothesis.  `GCD369RatFuncDerivative` and
`GCD369RatFuncConstants` expose those properties through the selected standard
instance used by the later Kummer construction.
`GCD369AlgebraicDifferentialConstantsDescend` proves that an algebraic
differential extension does not enlarge an algebraically closed constant
field, and `GCD369BaseFixingAutomorphismFixesConstants` consequently removes
the need to assume separately that a base-fixing deck action fixes constants.
`GCD369KummerAlignmentFromBaseConstants` then feeds that result directly into
the first-row alignment argument.
`GCD369PolynomialNoncubeDifferentialKummerPackage` composes the entire bridge:
from a noncube polynomial it constructs the differential cubic Kummer field,
deck action, extension constants, and the resulting first-row alignment.
`GCD369KummerHighRowsNormalize` then proves the formerly assumed triangular
integration step: for a general depressed degree-nine member, the eight high
bracket rows produce eight differential constants; the Kummer action kills the
five nonzero-weight constants, leaving exactly target shear, `kappa`, and
target translation.

The result is aimed at researchers studying polynomial automorphisms, the
Jacobian conjecture, and exact algebraic decompositions arising in formal or
computer-assisted proofs.  No claim of novelty or priority is made beyond the
included campaign source and its review.

## Compared declaration

- `GCD369KummerHighRowsNormalize` integrates all eight high rows of the
  general depressed bracket and derives `GCD369AlignedG` modulo the two
  inessential constant target gauges.
- `GCD369AlignmentDiscriminatorDerivative` proves the exact quotient-rule
  form of the first denominator-cleared source row.
- `GCD369KummerAlignmentFromFirstRow` derives the aligned condition from that
  row and the explicit cubic Kummer action.
- `GCD369NoncubeCubicKummerExtension` constructs the cubic root, its
  irreducible extension, and the base-fixing deck action from noncubeness.
- `GCD369PolynomialNoncubeInRatFunc` is the exact reduced-fraction
  polynomial-to-function-field noncube bridge.
- `GCD369PolynomialNoncubeKummerExtension` supplies the concrete Kummer data
  directly from a noncube polynomial core.
- `GCD369KummerRootDerivative` and
  `GCD369KummerDeckCommutesWithDerivative` connect that algebraic extension
  to the differential-field structure used by the alignment theorem.
- `GCD369RatFuncConstantsOfPolynomialDerivative` proves the rational base
  constant-field theorem from the standard derivative of embedded
  polynomials.
- `GCD369RatFuncStandardDifferential` constructs the quotient-rule derivation
  on `k(x)` and packages its polynomial derivative and constant field.
- `GCD369RatFuncDerivative` and `GCD369RatFuncConstants` expose the two
  properties of the selected standard differential instance.
- `GCD369AlgebraicDifferentialConstantsDescend` and
  `GCD369BaseFixingAutomorphismFixesConstants` supply constant-field descent
  through the algebraic Kummer extension and show that its base-fixing deck
  action fixes every differential constant.
- `GCD369KummerAlignmentFromBaseConstants` composes this descent with the
  first denominator-cleared source row to prove alignment without a separate
  constant-fixing hypothesis.
- `GCD369PolynomialNoncubeDifferentialKummerPackage` packages polynomial
  noncubeness, the standard differential on `k(x)`, the cubic extension and
  deck action, extension constant descent, and first-row alignment in one
  theorem.
- `GCD369AlignedNoncubeExclusion` proves that the displayed aligned Keller,
  Kummer, constant-field, and reduced function-field hypotheses are
  inconsistent with a noncube polynomial core.
- `GCD369AlignedF` and `GCD369AlignedG` are compared definitions for the
  degree-six and degree-nine aligned normal forms used in the theorem.
- `GCD369DepressedG` is the compared general degree-nine input before the
  eight-row integration.

## Proof architecture

The proof is assembled entirely inside Lean:

1. `GCD369KummerHighRowsNormalize` extracts the `z¹²,…,z⁵` bracket
   coefficients, integrates their triangular differential system, and uses
   the deck weights to descend to the aligned normal form.
2. `GCD369AlignedKellerRow4` through `GCD369AlignedKellerRow1` extract the
   four nonconstant lower coefficients from the single polynomial Keller
   identity.
3. `GCD369LowerFirstIntegrals` and
   `GCD369AlignedKellerFibreDichotomy` turn those rows into the four Kummer
   invariants and the two-sheet split.
4. `GCD369ZeroSheetTerminalExclusion` proves that the first sheet has zero
   source bracket and cannot support the nonzero Keller constant.
5. On the second sheet, `GCD369EllipticTerminalRow` connects the actual
   bracket to the elliptic terminal form.  Constant elliptic coordinates are
   excluded directly; nonconstant reduced rational coordinates are excluded
   at the two forbidden finite values after exact denominator clearing.
6. On the special fibre, the zero-`X` branch returns to the first sheet.  The
   nonzero-`X` branch is the shifted Davenport–Stothers family; terminal
   descent gives its reduced rational ODE, whose finite-place classification,
   one-point support, and cube conclusion contradict the noncube hypothesis.

The source report used symbolic computation to discover and review several
identities.  The submitted proofs invoke no external computer algebra system:
all identities and case splits are checked by Lean's kernel.

## Exact scope

The theorem works over an algebraically closed characteristic-zero constant
field `k` and a differential field extension `L` with injective evaluation
at a differential indeterminate.  Constant-field descent is stated explicitly.
The two rational presentations are pointwise reduced over `k`.  The theorem
assumes the standard Kummer relation `s³=h`, the shifted descent relation
`a₄/4=s²q`, and divisibility `3 | deg(H)`.

Those are the exact inputs needed for the noncube branch.  The high-row theorem
starts one step earlier than the headline exclusion, with a general
simultaneously depressed coefficient path, but the formalization still does
not derive that Kummer-weighted depression from every arbitrary Keller pair.
It does not address the cube-core branch and makes no claim about larger
degree gates.

## Relationship to earlier literature

Common-power leading forms and degree reductions are standard themes in the
plane Jacobian literature; broad antecedents include Moh's root-configuration
analysis (*J. Reine Angew. Math.* 340 (1983), 140–212) and
Guccione–Guccione–Valqui's Newton-polygon treatment
([*J. Algebra* 471 (2017), 13–74](https://doi.org/10.1016/j.jalgebra.2016.08.039)).
Those works concern global or total-degree reductions.  This package checks a
specific lower-Pfaffian implication at actual partial degrees `(6,9)`.

The shifted degree-`(6,9)` family belongs to classical Davenport–Stothers
theory.  Shioda records the order-three Birch example and `St(3)=1`
([*Comment. Math. Univ. St. Pauli* 54 (2005), 49–68](https://doi.org/10.14992/00008689)),
while Zannier studies equality cases of Davenport's bound
([*Acta Arith.* 71 (1995), 107–137](https://doi.org/10.4064/AA-71-2-107-137)).
Shioda's order-three family is the literature input adapted here; Zannier's
work supplies broader equality-case context.  The explicit family is not
claimed as new.

The two source reports and campaign-internal hostile reviews are copied under
`sources/`; their SHA-256 digests agree with the frozen originals:

- high-row producer: `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8`
- high-row review: `5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503`
- lower-Pfaffian producer: `7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043`
- lower-Pfaffian review: `a000619d8b5597add21716d525856c459ff57d5a2b2ab75b85de5d9d08970b27`

The hostile review concerns the informal mathematics, not the Lean code and
not external human peer review.  AI assistance and human responsibility are
reported in `formalization.yaml`.

## Verification

```sh
lake build
./scripts/check_axioms.sh
```

`Solution.lean` has no `sorry`, custom axioms, or trust escapes.  The
permitted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The project uses the Apache-2.0 licence at the repository root.
