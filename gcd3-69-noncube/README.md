# Two-sheet reduction and noncube closure at partial degrees `(6,9)`

This Lean 4 project formalizes an algebraic reduction in the lower-Pfaffian
analysis of the plane Jacobian conjecture at actual partial degrees `(6,9)`.
It proves that every field-valued solution of four Kummer-forced invariant
equations lies on at least one of two displayed sheets: a common-power sheet
with identically zero source bracket or an elliptic sheet.  It does not prove
the converse inclusions or existence of either sheet.  The formalization also
excludes nonconstant reduced rational trajectories on the nonsingular
(`C ≠ 0`) elliptic sheet when they satisfy its terminal Keller equation, and
certifies the special-fibre factorization and shifted Davenport–Stothers
endgame identities.  Version 2 additionally derives the complete finite-place
valuation classification from the reduced rational ODE itself, proves that
the support consists of one point, and excludes the shifted
Davenport–Stothers sheet in the noncube Kummer branch.

The result is aimed at researchers studying polynomial automorphisms, the
Jacobian conjecture, and exact algebraic decompositions arising in formal or
computer-assisted proofs.  No claim of novelty or priority is made beyond the
included campaign source and its review.

## Compared declarations

- `GCD369InvariantFibreDichotomy` is the central result.  Over any
  characteristic-zero field, the four displayed invariant equations imply
  either the three equations defining the zero-bracket sheet `P_A`, or all
  four equations defining the elliptic sheet `P_B`.  This is the
  field-valued, reduced-point form of the source's universal radical
  decomposition in the implication direction used here; the compared theorem
  does not prove either converse inclusion or existence of points on the
  sheets.  Its Lean proof uses explicit ideal-membership certificates and
  field case splits; it does not call a computer algebra system.
- `GCD369ZeroBracketSheet` proves that every differential path of the form
  `f=K₀²+d`, `g=K₀³+(κ+3d/2)K₀`, with `d` and `κ` constant, has zero source
  bracket.
- `GCD369EllipticSheetEquation` derives
  `Y²=3X³+4096C` from the `P_B` equation.
- `GCD369EllipticTerminalForm` proves the exact polynomial terminal one-form
  identity on tangent vectors to that elliptic curve.
- `GCD369ForbiddenNumerator` proves that one of the two forbidden-value
  numerators of a nonconstant polynomial numerator/denominator pair is
  nonconstant.
- `GCD369EllipticNonzeroExclusion` combines algebraic closedness, a reduced
  rational presentation, nonconstancy, and the cleared terminal equation to
  exclude nonconstant reduced rational trajectories on the `C ≠ 0` elliptic
  sheet.  At a finite preimage of one of the two forbidden values, the left
  side vanishes and the right side is nonzero.  This also covers ramified
  preimages; constant trajectories are not excluded by this declaration.
- `GCD369SpecialFibreDichotomy` proves, without division, that `C=0` factors
  as `X=0` or `X=3a₄²`.
- `GCD369ShiftedDSBracket` proves the shifted Davenport–Stothers bracket in a
  denominator-free normalization (the degree-nine polynomial is doubled).
- `GCD369ShiftedDSTerminalDescent` proves the exact chain-rule descent from
  `s³=h`, `λ=s²q` to the weighted rational ODE.
- `GCD369WeightedWronskianLocal` proves the cancellation-sensitive local
  order formula for `2H'B-3HB'`, including the resonant case.
- `GCD369ShiftedDSFinitePlace` derives, at every finite support point, the
  exact orders `ord(H)=3+7k`, `ord(B)=2+5k`, with `k>0`, directly from the
  cleared ODE.
- `GCD369WeightedWronskianDegree` proves the corresponding exact degree at
  infinity when the explicit leading resonance is absent.
- `GCD369ShiftedDSPolynomialCube` sums the local orders, proves that the
  support is a singleton, gives the exact one-root forms for `H` and `B`, and
  concludes that `H` is a cube when `3 | deg(H)`.
- `GCD369ShiftedDSNumeratorConstant` proves that the numerator in a reduced
  presentation `q=N/B` with `B ≠ 0` is constant.
- `GCD369ShiftedDSRationalCube` combines those steps into the full rational
  valuation closure, including explicit numerator, support, and exponent data.
- `GCD369ShiftedDSNoncubeExclusion` is the headline v2 result: the cleared
  shifted Davenport–Stothers ODE has no reduced rational trajectory satisfying
  the noncube Kummer and `3 | deg(H)` hypotheses.
- `GCD369DSInfinitySupport` formalizes the degree arithmetic that forces the
  valuation-classified Davenport–Stothers path to have one finite support
  point.
- `GCD369DSOneRootCube` proves the terminal cube conclusion: an algebraically
  closed-field polynomial `c(X-a)^(3+7k)` is a cube when `3 | (3+7k)`.

## Proof architecture and exact scope

The first theorem implements the reduced two-sheet calculation constructively.
In the branch `A=4a₂-a₄²=0`, an explicit consequence of the first invariant is
`24B²=0`, after which the remaining `P_A` equation follows.  In the branch
`A≠0`, a Gröbner-derived but Lean-verified identity gives `a₃A⁴=0`; two shorter
certificates then force `a₃=a₁=0`, the linear `P_B` equation, and `E_B=0`.
The subsequent theorems verify the source bracket, elliptic coordinates,
terminal form, forbidden-value contradiction, special fibre, and shifted
Davenport–Stothers identities directly in Mathlib.  For v2, a reduced
presentation `q=N/B` is substituted into the descended ODE.  Reducedness first
forces `N` to be constant.  Root multiplicities of the weighted Wronskian then
give the exact finite orders, with the resonant cancellation separately ruled
out.  Summing over the algebraically closed field and comparing the exact
leading degree forces a single support point; `3 | deg(H)` makes its exponent
and leading scalar cubic.

This closes the shifted Davenport–Stothers sheet of the aligned nontrivial-
Kummer branch, conditional on the displayed reduced rational ODE obtained by
the preceding formalized terminal descent.  Still out of scope are the
landing from an arbitrary Keller pair into the invariant fibre and its
shifted-DS parametrization, the cube-core branch, a general `(6,9)` exclusion,
the maximum-partial-degree-eleven theorem, and the plane Jacobian conjecture.

## Relationship to earlier literature

Common-power leading forms and degree reductions are standard themes in the
plane Jacobian literature; the nearest broad antecedents are Moh's
root-configuration analysis (*J. Reine Angew. Math.* 340 (1983), 140–212)
and Guccione–Guccione–Valqui's Newton-polygon treatment
([*J. Algebra* 471 (2017), 13–74](https://doi.org/10.1016/j.jalgebra.2016.09.020)).
Those works concern global or total-degree reductions.  This package instead
checks a selected lower-Pfaffian implication at actual partial degrees `(6,9)`;
it neither reproduces nor strengthens their global theorems, and no such
theorem is imported into the Lean proofs.

The displayed degree-`(6,9)` polynomial family belongs to the classical
Davenport–Stothers theory.  Shioda records the order-three Birch example and
`St(3)=1` ([*Comment. Math. Univ. St. Pauli* 54 (2005), 49–68](https://doi.org/10.14992/00008689)),
while Zannier studies equality cases of Davenport's bound
([*Acta Arith.* 71 (1995), 107–137](https://doi.org/10.4064/AA-71-2-107-137)).
The explicit family is therefore not claimed as new.  The selected result here
adapts it to the shifted rational ODE produced by the campaign's invariant
fibre and proves, in Lean, the finite-place classification, one-point support,
and noncube contradiction; it does not reprove the classical classification
of Davenport–Stothers triples.

The source report and its campaign-internal hostile review are copied exactly
under `sources/`; their SHA-256 digests agree with the frozen originals:

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

`Solution.lean` has no `sorry`, custom axioms, or trust escapes.  The permitted
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.  The project
uses the Apache-2.0 licence at the repository root.
