# Aligned noncube exclusion at partial degrees `(6,9)`

This Lean 4 project proves the full noncube gate for the aligned
nontrivial cubic-Kummer branch at actual partial degrees `(6,9)`.  Starting
from the actual aligned Keller bracket, it extracts the four lower coefficient
rows, derives the Kummer first integrals and two-sheet invariant-fibre split,
and rules out every resulting sheet.  The common-power sheet has zero bracket;
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

The result is aimed at researchers studying polynomial automorphisms, the
Jacobian conjecture, and exact algebraic decompositions arising in formal or
computer-assisted proofs.  No claim of novelty or priority is made beyond the
included campaign source and its review.

## Compared declaration

- `GCD369AlignmentDiscriminatorDerivative` proves the exact quotient-rule
  form of the first denominator-cleared source row.
- `GCD369KummerAlignmentFromFirstRow` derives the aligned condition from that
  row and the explicit cubic Kummer action.
- `GCD369NoncubeCubicKummerExtension` constructs the cubic root, its
  irreducible extension, and the base-fixing deck action from noncubeness.
- `GCD369AlignedNoncubeExclusion` proves that the displayed aligned Keller,
  Kummer, constant-field, and reduced function-field hypotheses are
  inconsistent with a noncube polynomial core.
- `GCD369AlignedF` and `GCD369AlignedG` are compared definitions for the
  degree-six and degree-nine aligned normal forms used in the theorem.

## Proof architecture

The proof is assembled entirely inside Lean:

1. `GCD369AlignedKellerRow4` through `GCD369AlignedKellerRow1` extract the
   four nonconstant lower coefficients from the single polynomial Keller
   identity.
2. `GCD369LowerFirstIntegrals` and
   `GCD369AlignedKellerFibreDichotomy` turn those rows into the four Kummer
   invariants and the two-sheet split.
3. `GCD369ZeroSheetTerminalExclusion` proves that the first sheet has zero
   source bracket and cannot support the nonzero Keller constant.
4. On the second sheet, `GCD369EllipticTerminalRow` connects the actual
   bracket to the elliptic terminal form.  Constant elliptic coordinates are
   excluded directly; nonconstant reduced rational coordinates are excluded
   at the two forbidden finite values after exact denominator clearing.
5. On the special fibre, the zero-`X` branch returns to the first sheet.  The
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

Those are the exact inputs needed for the noncube branch.  The formalization
does not prove that every arbitrary Keller pair admits this aligned/Kummer
presentation, does not address the cube-core branch, and makes no claim about
larger degree gates.

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

The source report and campaign-internal hostile review are copied under
`sources/`; their SHA-256 digests agree with the frozen originals:

- producer: `7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043`
- review: `a000619d8b5597add21716d525856c459ff57d5a2b2ab75b85de5d9d08970b27`

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
