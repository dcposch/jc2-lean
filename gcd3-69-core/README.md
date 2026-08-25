# jc2-gcd3-69-core

Lean 4 / Mathlib formalization of six reusable algebraic statements from the
first common-cubic gate at actual partial degrees `(6,9)` in the plane
Jacobian campaign.  This is deliberately a formalization of the first-gate
foundation, **not** of the later coverage composition or the maximum-eleven
automorphism theorem.

The formalized results are:

- `GCD369TopRowIdentity`: exact cancellation in the `y^13` Jacobian row after
  the cubic-Kummer normalization;
- `GCD369KummerAlignment`: the top row, fixed differential constants, and
  common nontrivial Kummer weight force `3*A - 2*B = 0`;
- `GCD369SimultaneousDepression`: the translation `r=A/6` then kills the
  degree-five and degree-eight coefficients simultaneously;
- `GCD369CubeFactorNeutral`: multiplication of a simple field generator by a
  nonzero base-field scalar does not change the generated intermediate field;
- `GCD369DavenportStothersCertificate`: the two explicit polynomial identities
  for the order-three Davenport--Stothers family, in the denominator-free
  parameter `lambda = 2*mu`;
- `GCD369DavenportStothersDerivativeIdentity`: the general identity relating
  the weighted Wronskian to `H=f^3-g^2`.

All characteristic-dependent cancellation is explicit: the alignment and
depression theorems assume characteristic zero.  The top-row and differential
identities hold over arbitrary commutative rings.

## Layout and checks

| File | Role |
| --- | --- |
| `Challenge.lean` | human-auditable statements, with proofs replaced by `sorry` |
| `Solution.lean` | the same declarations with complete proofs |
| `comparator.json` | Palomar Comparator declaration list |
| `formalization.yaml` | structured provenance, scope, and fidelity metadata |
| `scripts/check_axioms.sh` | rejects `sorryAx`, compiler trust, and custom axioms |

Toolchain: Lean `v4.34.0-rc1`, Mathlib revision
`20bc12820422504f9e52ee6caebf8182a9015336`.

```sh
lake exe cache get
lake build
./scripts/check_axioms.sh
```

The Solution theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The proofs use ordinary Mathlib tactics and no custom axioms,
`native_decide`, or trusted external certificates.

## Scope boundary

The source campaign later composes this gate with lower-Pfaffian,
cube-mismatch, and cube-trajectory arguments to exclude the `(6,9), 3|H`
residue and then invokes a separately reviewed partial-degree history to reach
maximum actual `y`-degree eleven.  None of those handoffs or conclusions is
asserted here.  In particular, this project does not formalize a Keller-pair
exclusion, a maximum-degree theorem, or the Jacobian conjecture.

## AI disclosure

An OpenAI Codex agent drafted and checked this formalization under Dan Clemens
Posch's campaign direction.  The Lean kernel checks every Solution proof; the
mathematical statements still require human source-fidelity and publication
review.
