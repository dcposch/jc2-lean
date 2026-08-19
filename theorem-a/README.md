# jc72108-theorem-a

Lean 4 / Mathlib formalization of **Theorem A** (ODE rigidity, all weights;
label `thm:ode`, Theorem 6.1 in the current compilation) from Section 6 of the
(72,108) plane-Jacobian campaign paper — stated and proved as Theorem A in
`MATHIEU.md` §5.1 of the archived campaign theory bundle
([doi:10.5281/zenodo.22002825](https://doi.org/10.5281/zenodo.22002825)) —
prepared for the [Palomar registry](https://palomar-registry.org).

**Theorem A.** Let `F` be an integral domain of characteristic zero,
`ν ≥ 1` an integer, and `A, C ∈ F[y]` polynomials with

    A·C′ − ν·A′·C = c,   c ∈ F a nonzero constant.

Then `deg A ≤ 1`.

**Theorem A, characteristic p** (`TheoremA_charP`): the same conclusion over
an integral domain of characteristic `p`, provided `ν·deg A < p` and
`deg C < p` — a standalone strengthening extracted from the source's Section 6
proof and characteristic remark (`MATHIEU.md` §5.4); the source records only
the conservative bound `p > (k+1)·d₂`, which implies both hypotheses in its
application.  Some bound is necessary (`A = y^p + y`, `C = 1`, `ν = 1`).

In the campaign, Theorem A is the rigidity engine that closes the depth-two
block of the strip reduction at Newton-degree pair (72,108): through the
block-to-ODE bridge it forces the edge polynomial of a hypothetical Keller
counterexample to be binomial.  (The block-variety theorem `thm:R` —
Theorem 6.5 in the current compilation — is **not** formalized here.)
Prior art: Żołądek, Topology 47 (2008), Appendix Lemma A.7, yields the case
where `A` has at least two distinct roots (via `(C/A^ν)′ = c/A^{ν+1}`;
perfect powers need a separate evaluation), and Theorem 4 of Hermoso–Alcázar,
arXiv:2410.18867, forces both polynomials of a nonzero-constant-Wronskian
pair (`ν = 1`) to be affine.  The proof formalized here is the campaign's
independent one: pure degree bookkeeping inside `F[y]`.

## Layout (Palomar conventions)

| File | Role |
| --- | --- |
| `Challenge.lean` | the statements, human-auditable, proofs are `sorry` |
| `Solution.lean` | the same statements with complete proofs |
| `comparator.json` | declarations Palomar's Comparator compares |
| `formalization.yaml` | structured metadata (sources, automation, review) |
| `scripts/check_axioms.sh` | axiom audit for the Solution theorems |

Toolchain: Lean `v4.32.2`, Mathlib tag `v4.32.2` (pinned in
`lake-manifest.json`).

## Build and check

```sh
lake exe cache get   # fetch Mathlib build cache
lake build           # builds Challenge and Solution
./scripts/check_axioms.sh
```

The axiom script confirms both theorems depend only on `propext`,
`Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`, no
custom axioms).

## Proof sketch (`Solution.lean`)

Write `δ = deg A`, `α = lc A`, and suppose `δ ≥ 2`.

1. **Step 1** (`JC72108.coeff_bracket`): for `deg A ≤ a`, `deg D ≤ d`,
   `a + d = n + 1`, the `y^n`-coefficient of `A·D′ − ν·A′·D` is
   `(d − ν·a)·A_a·D_d` — and nothing of higher degree occurs.
2. **Step 2**: applied at `D = C`, the bracket is the constant `c`, so the
   top coefficient `(deg C − ν·δ)·α·lc C` at position `δ + deg C − 1 ≥ 1`
   must vanish; the characteristic hypothesis turns this into
   `deg C = ν·δ`.
3. **Steps 3–4**: `D := α^ν·C − lc(C)·A^ν` (denominators cleared — this is
   why a domain suffices) satisfies the same identity with constant `α^ν·c ≠ 0`
   and has `deg D < ν·δ`; `D = 0` is impossible, and `D ≠ 0` re-triggers
   Step 1 with `(deg D − ν·δ) ≠ 0` — contradiction.

The characteristic enters only through injectivity of `ℕ → F` on the degree
range, packaged as one hypothesis of `JC72108.core`; `TheoremA` and
`TheoremA_charP` are the two instantiations.

## Provenance and AI disclosure

Proofs drafted by Claude (Fable, Anthropic) agents in a human-directed
campaign; statements audited by the human author; everything machine-checked
by the Lean kernel.  See `formalization.yaml` for the full disclosure.
