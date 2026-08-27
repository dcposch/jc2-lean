# Source-facing polynomial-cube exclusion at partial degrees `(6,9)`

This Lean 4 project proves the cube-core companion to the registered
noncube exclusion.  Its headline theorem,
`GCD369PolynomialCubeSourceExclusion`, directly quantifies over literal
`p,q ∈ k[x][y]` and `s ∈ k[x]` over an algebraically closed
characteristic-zero field, with
outer degrees six and nine, leading coefficients `s^6,s^9`, and nonzero
constant coefficientwise-inner Jacobian.  It proves that the common
polynomial cube root `s` cannot be nonconstant.

The Mathlib-only statement contains no project-specific structure, chosen
pole, Hahn-series scale, Faber
decomposition, root chart, or trajectory data.  The proof constructs those
objects internally.

## Proof architecture

1. Nonconstant `s` supplies a finite pole among the five normalized sextic
   coefficients.
2. The three exact transverse normals have a first positive Hahn scale.  If
   they all vanished, the sextic would be a literal cubic square, contradicting
   the nonzero Jacobian.
3. Source-facing simple- and double-root analyses cover every relative timing
   of the successive Faber loads
   `d,c7,c5,c4,c2,c1,rho1,rho2`.  Triangular composition forces all eight to
   vanish.
4. After the legal first-target translation, the remaining `rho3,rho4`
   fibres are exhausted: elliptic and cusp trajectories are impossible, and
   the zero-invariant Davenport–Stothers sheet is excluded by a second finite
   pole of the original polynomial source.

The many intermediate files make each valuation, coefficient extraction,
root split, and endpoint residue independently kernel-checkable.  The public
Comparator surface is the single source-facing theorem in `Challenge.lean`.

## Verification

Toolchain: Lean `v4.34.0-rc1`, Mathlib revision
`20bc12820422504f9e52ee6caebf8182a9015336`.

```sh
lake build
./scripts/check_axioms.sh
```

The solution contains no `sorry`, custom axiom, opaque proof escape, or
external trusted certificate.  The headline theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact scope

This proves the normalized polynomial-cube branch at actual partial degrees
`(6,9)`.  It does not by itself derive that normalization from an arbitrary
Keller pair, combine the cube and noncube branches, prove the gcd-at-most-two
degree reduction, establish maximum partial degree eleven, or settle the
plane Jacobian conjecture.

The complementary source-facing noncube branch is registered as
[PALOMAR-2026-08-25-000002 v2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-25-000002&version=2).

## Frozen informal sources

The four campaign sources used for the cube branch are included byte-for-byte
under `sources/`:

- mismatch gate: `6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20`
- mismatch hostile review: `2648eef3b8091970655a94743c6c181343a94534b6454f43c579b310331ba7d7`
- trajectory gate: `069f6280332b44d93dcad17801dc7136d4a79fb06ace101c2dce8a4e746b5e7b`
- trajectory hostile review: `7bcf18d69344acc2277a0184ca1aeeb717ebad35c3aacf91421874b7e59f5cc9`

## AI disclosure

An OpenAI Codex agent developed and checked the Lean formalization under Dan
Clemens Posch's mathematical direction, with selected mechanical ports
delegated to Grok.  The informal cube-trajectory source had a separate
campaign-internal hostile Grok review; no external human peer review of this
Lean project has yet occurred.
