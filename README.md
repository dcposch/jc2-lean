# jc2-lean

Lean 4 formalizations from the JC2 campaign (plane Jacobian Conjecture
program of Dan Clemens Posch, in collaboration with Claude, GPT, and Grok),
structured for the [Palomar registry](https://palomar-registry.org).

Each subdirectory is a self-contained lake project with its own
`Challenge.lean` (statements), `Solution.lean` (sorry-free proofs),
`comparator.json`, and `formalization.yaml`.

| Project | Contents | Status |
|---|---|---|
| [`theorem-a/`](theorem-a/) | Theorem A: polynomial ODE rigidity (if AC' − νA'C is a nonzero constant then deg A ≤ 1), char 0 over any integral domain, plus a characteristic-p strengthening | **registered: [PALOMAR-2026-08-19-000005 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-08-19-000005&version=1)** |
| [`vertex-gap/`](vertex-gap/) | Vertex-gap obstruction at type (2,2): Theorem 3.4 + side-symmetric companion, corner enumeration, side-symmetric gap condition | built green; axioms = the 3 standard |

Campaign artifacts: [paper + verification](https://doi.org/10.5281/zenodo.21894922),
[theory bundle](https://doi.org/10.5281/zenodo.22002825).
