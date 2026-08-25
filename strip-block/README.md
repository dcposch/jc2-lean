# jc2-strip-block-core

Lean 4 / Mathlib formalization of a **supporting algebraic core** for the
uniform depth-two log-residue theorem (`thm:R`, Theorem 6.5 in the current
compilation) in Section 6 of *A Vertex-Gap Obstruction for Low-Degree Strip
Pairs in the Plane Jacobian Conjecture*.

This package is intentionally narrower than the printed theorem.  It proves
four exact statements:

| Lean name | Kernel-checked scope |
| --- | --- |
| `BlockToODEBridge` | The finite coefficient encoding `innerBlockKeysVanish` is equivalent to the polynomial identity `A C' - k A' C = 1`, using the displayed support bounds. |
| `InnerBlockRigidity` | Over a characteristic-zero domain, that encoding forces `deg A <= 1`. |
| `OuterResidueIdentity` | The displayed functional `R_{k,d}` is exactly coefficient `k+2` of an explicit finite binomial transform. |
| `LogResidueBlockVariety` | Given explicit hypotheses identifying the actual inner and outer extra-key loci, their intersection is `deg A <= 1` and (`a = 0` or `R_{k,d} = 0`). |

The residue is represented denominator-free as

```text
R(k,d,a,beta) = sum_{0 <= j <= 2d}
  (-1)^j * choose(j,k+2) * a^(2d-j) * beta(j).
```

The terms with `j < k+2` vanish automatically.  The package includes a local
copy of the already published weighted-ODE rigidity proof, so it has no
dependency on the sibling `theorem-a/` package.

## Exact fidelity boundary

This is **not yet a full formalization of `thm:R`**.  In particular, it does
not formalize:

* the Newton-strip/lattice-support reduction from a pair `P,Q` to the block
  columns;
* the triangular solve showing that the paper's `d-1` inner extras are
  equivalent to existence of the polynomial `C` used here;
* the converse construction on the normalized binomial locus; or
* Lemma `lem:outer`, which derives the surviving outer extra and its precise
  nonzero scalar from the solved outer column.

Those two decisive identifications are fields `inner_iff` and `outer_iff` of
`DepthTwoBlockData`; `LogResidueBlockVariety` proves only the final logical
assembly from them.  Accordingly, this package is useful scaffolding and an
auditable statement boundary, but the four declarations should not be
advertised as a formal proof of the paper's full block-variety theorem.

## Layout

| File | Role |
| --- | --- |
| `Challenge.lean` | Public declarations with `sorry`, for statement comparison. |
| `Solution.lean` | The same declarations with complete proofs. |
| `Rigidity.lean` | Local, standalone weighted-ODE rigidity proof. |
| `comparator.json` | Declarations for Palomar's Comparator. |
| `formalization.yaml` | Source, scope, automation, and fidelity metadata. |
| `scripts/check_axioms.sh` | Axiom audit for the four Solution theorems. |

Toolchain: Lean `v4.34.0-rc1`, Mathlib revision
`20bc12820422504f9e52ee6caebf8182a9015336`, matching `theorem-a/` and
`vertex-gap/`.

## Build and audit

```sh
lake exe cache get
lake build
./scripts/check_axioms.sh
```

The Solution proofs depend only on Mathlib's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`, custom
axiom, or native-code trust escape in `Solution.lean` or `Rigidity.lean`.

## Source

The source theorem appears in Section 6 of the campaign paper and in the
archived campaign theory bundle
([doi:10.5281/zenodo.22002825](https://doi.org/10.5281/zenodo.22002825)).
The earlier reproduction artifact for the surrounding strip-pair work is
[doi:10.5281/zenodo.21894922](https://doi.org/10.5281/zenodo.21894922).

Proofs and package metadata were drafted with OpenAI Codex in a
human-directed campaign.  The statement boundary above is deliberate and is
the main fidelity caveat for any later submission.
