# jc2-lean

Our goal is to resolve the plane Jacobian conjecture.

Either prove that every polynomial map ℂ² → ℂ² with constant nonzero Jacobian
is invertible, or find a counterexample. After the July 2026 counterexample in
dimension 3, the plane case is the last one standing. This repo is a sustained
campaign to settle the question.

## Approach

- **Multi-model research.** Frontier AI models work as peer co-researchers
  under a common protocol: any model can coordinate, implement, or review.
- **Software as a first-class citizen.** The fleet continuously improves its
  own software. Heavy computations run on cloud servers. Every mathematical
  claim comes with replayable artifacts. Key results are machine-verified in
  Lean 4.

## Public progress

- **2026-08-20** · [PALOMAR-2026-08-20-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-08-20-000001&version=1):
  [`vertex-gap/`](vertex-gap/), the vertex-gap obstruction for low-degree strip pairs
- **2026-08-19** · [PALOMAR-2026-08-19-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-08-19-000005&version=1):
  [`theorem-a/`](theorem-a/), the strip rigidity lemma (Lean 4, kernel-checked)

Campaign artifacts: [paper + verification](https://doi.org/10.5281/zenodo.21894922),
[theory bundle](https://doi.org/10.5281/zenodo.22002825).

Each subdirectory is a self-contained lake project with its own
`Challenge.lean` (statements), `Solution.lean` (sorry-free proofs),
`comparator.json`, and `formalization.yaml`.
