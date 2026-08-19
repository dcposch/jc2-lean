# jc2-vertex-gap

Lean 4 / Mathlib formalization of the **vertex-gap obstruction at
`(k,d₂) = (2,2)`** (label `thm:22`, Theorem 3.4 in the current compilation)
from *A Vertex-Gap Obstruction for Low-Degree Strip Pairs in the Plane
Jacobian Conjecture* — archived with its reproduction artifact at
[doi:10.5281/zenodo.21894922](https://doi.org/10.5281/zenodo.21894922) —
prepared for the [Palomar registry](https://palomar-registry.org).
Sibling project of `theorem-a/` (Theorem A, ODE rigidity), pinned to the
same Lean/Mathlib toolchain.

**Vertex-gap obstruction, `(2,2)`.** Let `K` be a field of characteristic
not in `{2,3,5}` and `P, Q ∈ K[x,y]` a normalized type-`(2,2)` strip pair:
writing `w(i,j) = 2i − j`,

    supp P ⊆ { 0 ≤ w ≤ 2 },   supp Q ⊆ { 0 ≤ w ≤ 3 } ∩ { i ≤ 2j },
    [P,Q] := Pₓ·Q_y − P_y·Qₓ = x².

Then the block coefficients of `P` satisfy `a₃ = a_{(1,2)} = 0` and
`a₂²·a₆ = a_{(1,1)}²·a_{(2,4)} = 0` — the generic chart `a₂a₆ ≠ 0` of the
strip family is empty. This is the mechanism that discards the generic
chart of the `(8,28)` strip subcase (Guccione–Guccione–Horruitiner–Valqui,
arXiv:2204.14178v1, Proposition 4.3, subcase (2)) at Newton-degree pair
`(72,108)`.

Four theorems (all in `Challenge.lean`, proved in `Solution.lean`):

| Lean name | Source |
| --- | --- |
| `CornerEnumeration` | Lemma 2.2 (`lem:enum`): under the vertex normalization, `{p₀,q₀} = {(1,0),(k,1)}` |
| `GapConditionSideSymm` | hypothesis (ii) side-symmetrically, per the erratum of Section 8: `k ≥ 2 ↔ max((p₀)ₓ,(q₀)ₓ) ≥ 2` |
| `VertexGap22` | Theorem 3.4 (`thm:22`), normalized labels (corner `(1,0)` on the `P` side) |
| `VertexGap22_swapped` | Theorem 3.4, mirrored labels — the side-symmetric companion; its proof is the paper's normalization `(P,Q) ↦ (Q,−P)` |

## Layout (Palomar conventions)

| File | Role |
| --- | --- |
| `Challenge.lean` | the statements, human-auditable, proofs are `sorry` |
| `Solution.lean` | the same statements with complete proofs |
| `comparator.json` | declarations Palomar's Comparator compares |
| `formalization.yaml` | structured metadata (sources, automation, review) |
| `scripts/check_axioms.sh` | axiom audit for the Solution theorems |

Toolchain: Lean `v4.32.2`, Mathlib tag `v4.32.2` (pinned in
`lake-manifest.json`, identical to `theorem-a/`).

## Build and check

```sh
lake exe cache get   # fetch Mathlib build cache
lake build           # builds Challenge and Solution
./scripts/check_axioms.sh
```

The axiom script confirms all four theorems depend only on `propext`,
`Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool` /
`native_decide`, no custom axioms).

## Proof sketch (`Solution.lean`)

1. `coeff_bracket`: the coefficient of `x^{n₀}y^{n₁}` in the Jacobian
   bracket as an explicit double sum over exponent pairs — the paper's key
   formula `E_m = ∑_{p+q=m} det(p,q)·a_p·b_q` (equation (1)), with the two
   bracket products kept separate.
2. Key extraction: instantiating `coeff_bracket` at the twelve relevant
   Minkowski points and discharging every out-of-strip coefficient by the
   support hypotheses yields the vertex equation `a₁b₃ = 1` (coefficient
   of `x²`), the two gap keys, and the nine block keys of the `(2,2)` cell
   — exactly the display in the proof of Theorem 3.4.
3. `cascade`: the elimination cascade as `linear_combination`
   certificates — gap kill, unit-pivot solves, cancellations C1/C2, the
   radical step `(a₃b₃)² = 0 ⇒ a₃ = 0` (the rigidity event at key
   `(3,5)`; cf. Remark 3.5), and the pinning surplus at `(4,7)` giving
   `a₂²a₆ = 0`.

## What is / is not formalized (fidelity scope)

**Formalized.** Theorem 3.4 at polynomial level, both label assignments
(`VertexGap22`, `VertexGap22_swapped`); Lemma 2.2 (`CornerEnumeration`);
the side-symmetric gap condition (`GapConditionSideSymm`). The vertex
equation and the gap kill are *derived* from the bracket rather than
assumed.

**Not formalized.** The general-cell counting propositions 3.2/3.3, the
gap-kill lemma at general `(k,d₂)` (only its `(2,2)` instances appear,
inside the proof), the radical-membership refinement of Remark 3.5, the
`(2,3)`/`(2,4)` variants and `k ≥ 3` certificates (Section 4), the
`(8,28)` worked example (Section 5), the log-residue functional and the
block-variety theorem (Section 6), and the GGHV chart reduction with the
`(72,108)` application (Sections 7–8; Theorem A of that story lives in
the sibling project `theorem-a/`).

**Divergences from the print** (details in `formalization.yaml`):

* Newton-polygon language becomes explicit lattice-support inequalities.
  The near-origin bottom-edge condition on the wide member (`i ≤ 2j`,
  support on or above the line through `(0,0)` and `(2,1)`) is carried in
  the paper by the polygon shape (gap-column points lie *strictly above
  the bottom edge* of `N(Q)`); it is load-bearing for the gap kill and is
  made explicit here.
* The saturation clause of (S2) and the uniqueness clause of (i) are
  consequences under these hypotheses (the bracket forces `a₁b₃ = 1`), so
  they are not assumed — the formal statement is harmlessly stronger.
* `char K ∉ {2,3,5}` is rendered as `(2:K) ≠ 0 ∧ (3:K) ≠ 0 ∧ (5:K) ≠ 0`
  (equivalent for fields). The formalized cascade keeps the factor `5` on
  the `b₉`-pivot instead of dividing by it, so it only consumes the
  invertibility of `2` and `3`; `(5:K) ≠ 0` is retained in the statement
  for fidelity with the print but is unused by the proof (consistent with
  Remark 3.7, which claims sharpness of `{2,3,5}` only for the paper's
  own pivot derivation and observes, without claim, persistence mod `5`).
* The conclusion is the variety-level statement (`a₃ = 0` and
  `a₂²a₆ = 0` for every solution), not the scheme-level radical statement.
* `CornerEnumeration` is stated for all `k : ℕ` (the paper's context has
  `k ≥ 1`; the statement also holds at `k = 0`).

## Provenance and AI disclosure

Proofs drafted by a Claude (Fable, Anthropic) agent in a human-directed
campaign; the key equations and cascade were re-verified during
formalization with an independent exact-arithmetic enumeration over a
large prime field; statements audited by the human author; everything
machine-checked by the Lean kernel. See `formalization.yaml` for the full
disclosure.
