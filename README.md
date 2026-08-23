# jc2-lean

Lean 4 formalizations from the JC2 campaign.

The campaign's goal: either prove that every polynomial map ℂ² → ℂ² with
constant nonzero Jacobian is invertible, or find a counterexample. After the
July 2026 counterexample in dimension 3, the plane case is the last one
standing. The campaign runs frontier AI models (Claude, GPT, Grok) as peer
co-researchers under a common protocol, with no result promoted until it
survives hostile review by a model other than the one that produced it. Every
mathematical claim ships with replayable artifacts, and key results are
machine-verified in Lean 4 and registered; this repository holds those
formalizations, structured for the
[Palomar registry](https://palomar-registry.org).

## Public progress

- **2026-08-20** · [PALOMAR-2026-08-20-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-08-20-000001&version=1):
  vertex-gap obstruction for low-degree strip pairs (Lean 4, kernel-checked)
- **2026-08-19** · [PALOMAR-2026-08-19-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-08-19-000005&version=1):
  Theorem A, the strip rigidity lemma (Lean 4, kernel-checked)

Campaign artifacts: [paper + verification](https://doi.org/10.5281/zenodo.21894922),
[theory bundle](https://doi.org/10.5281/zenodo.22002825).

## Layout

Each subdirectory is a self-contained lake project with its own
`Challenge.lean` (statements), `Solution.lean` (sorry-free proofs),
`comparator.json`, and `formalization.yaml`.

| Project | Contents | Status |
|---|---|---|
| [`theorem-a/`](theorem-a/) | Theorem A: polynomial ODE rigidity (if AC' − νA'C is a nonzero constant then deg A ≤ 1), char 0 over any integral domain, plus a characteristic-p strengthening | **registered: [PALOMAR-2026-08-19-000005 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-08-19-000005&version=1)** |
| [`vertex-gap/`](vertex-gap/) | Vertex-gap obstruction at type (2,2): Theorem 3.4 + side-symmetric companion, corner enumeration, side-symmetric gap condition | **registered: [PALOMAR-2026-08-20-000001 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-08-20-000001&version=1)** |
