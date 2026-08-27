# Exhaustive divisible-core common-cubic exclusion at `(6,9)`

This Lean 4 project proves that a literal normalized bivariate source at
outer degrees `(6,9)` cannot have a common leading core `H` with
`3 ∣ H.natDegree`.  The leading coefficients are exactly `H²` and `H³`,
and the coefficientwise-inner Jacobian is assumed to be a nonzero scalar.
The headline theorem,
`GCD369PolynomialCommonCubicSourceExclusionV2`, makes no cube/noncube
assumption: it performs that exhaustive split internally.

The noncube branch is supplied by the registered
[PALOMAR-2026-08-25-000002 v2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-25-000002&version=2).
The cube branch uses the locally strengthened complete cube-source exclusion,
including its constant-core case, from the sibling `gcd3-69-cube` project.
That strengthened cube result has not yet been registered with Palomar.

## Compared declaration

- `GCD369PolynomialCommonCubicSourceExclusionV2` rules out the entire
  divisible-core normalized `(6,9)` source.  Its proof splits on whether
  `H = s³`; the cube branch rewrites `H²,H³` as `s⁶,s⁹`, while the
  complementary branch invokes the registered noncube theorem.
- `GCD369SourceXDeriv` is the compared coefficientwise inner derivative used
  to state the source Jacobian.

## Exact scope

The theorem works over an algebraically closed characteristic-zero field.  It
starts with already-normalized `p,q ∈ k[x][y]`, actual outer degrees six and
nine, leading coefficients `H²,H³`, a nonzero constant Keller bracket, and
`3 ∣ deg H`.  It proves that these assumptions are inconsistent.

This project does not derive the normalized common core from an arbitrary
plane Keller pair, handle the nondivisible-core history route, prove the
gcd-at-most-two reduction, establish the maximum-partial-degree-eleven
theorem, remove algebraic closedness by scalar descent, or prove the plane
Jacobian conjecture.

## Verification

The project uses Lean `v4.34.0-rc1` and the same pinned Mathlib revision as
both dependency projects.

```sh
lake build
lake env lean GCD369DivisibleChallenge.lean
./scripts/check_axioms.sh
```

The solution theorem contains no `sorry`, custom axiom, or trusted external
certificate.  Its permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

## AI disclosure

An OpenAI Codex agent composed and kernel-checked the formalization under Dan
Clemens Posch's mathematical direction.  The two imported branch proofs were
developed and audited in their respective projects; no external human review
of this composition has yet occurred.
