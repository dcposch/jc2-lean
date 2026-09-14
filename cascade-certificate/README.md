# Cascade certificate: the `(8,28)` worked example

This is the original small Lean project from the campaign's `lean/` directory,
consolidated here so formal proofs have one home. It checks two polynomial
identities used in Paper 1, Section 5. The more general polynomial-level
obstruction is in [vertex-gap](../vertex-gap/README.md).

`Jc/Culprit.lean` proves:

- `eq3_at_b3_zero`: substituting `b3 = 0` into the vertex equation's left
  side `a1*b3 - 1` gives `-1`, over any commutative ring.
- `culprit_key36_reduction`: ten recorded substitutions reduce the key
  `(3,6)` bracket coefficient to `(-1/5)*a2^2*a6*b3*ia1^2`, over a field
  of characteristic zero. The proof uses `subst` and `ring`.

The second theorem assumes the recorded substitutions. It does not prove
that they follow from the original ideal, that the chart reductions preserve
solutions, or that the supplied polynomials are the original bracket
coefficients. It is not a formal proof of the full `(72,108)` exclusion.

## Build

From this directory:

```sh
lake exe cache get
lake build
```

The original Lean `v4.32.2` and Mathlib pins are unchanged. `Jc.lean` imports
`Jc.Culprit`; this historical project uses that layout instead of the
registry's `Challenge.lean` / `Solution.lean` convention.

## Provenance

The proof, project configuration, and dependency manifest are byte-identical
to the originals in `jc72108-paper1-artifact-v1.tar.gz`, retained in the
campaign's `dist/` directory. That release also preserves the old Python
generator and replay machinery. The source no longer needs a live generator.
