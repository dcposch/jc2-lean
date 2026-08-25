# Two-sheet reduction of the nontrivial cubic–Kummer `(6,9)` branch

This Lean 4 project formalizes an algebraic reduction in the lower-Pfaffian
analysis of the plane Jacobian conjecture at actual partial degrees `(6,9)`.
It proves that every field-valued solution of four Kummer-forced invariant
equations lies on at least one of two displayed sheets: a common-power sheet
with identically zero source bracket or an elliptic sheet.  It does not prove
the converse inclusions or existence of either sheet.  The formalization also
excludes nonconstant reduced rational trajectories on the nonsingular
(`C ≠ 0`) elliptic sheet when they satisfy its terminal Keller equation, and
certifies the special-fibre factorization and shifted Davenport–Stothers
endgame identities.

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
Davenport–Stothers identities directly in Mathlib.

This project does **not** yet prove that the full aligned nontrivial-Kummer
`(6,9)` branch is empty.  The remaining mathematical bridge is the finite-place
valuation classification of the shifted Davenport–Stothers rational ODE: from
that ODE one must derive the common one-point factorization with exponents
`ord(h)=3+7k` and `-ord(q)=2+5k`, including the cancelled leading case.  The
last two Lean theorems check the infinity and cube conclusions once that
classification is available.  Also out of scope are the preceding landing
from an arbitrary Keller pair, the cube-core branch, a general `(6,9)`
exclusion, the maximum-partial-degree-eleven theorem, and the plane Jacobian
conjecture.

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
