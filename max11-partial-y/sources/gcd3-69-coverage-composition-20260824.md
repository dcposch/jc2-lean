# GCD3 `(6,9)` coverage composition

## Fail-closed branch routing and the exact partial-`y` degree theorem through eleven

**Producer verdict: `THE REVIEWED NONCUBE AND POLYNOMIAL-CUBE ROUTES ARE
DISJOINT AND EXHAUSTIVE.  THERE IS NO CHARACTERISTIC-ZERO KELLER PAIR OF
ACTUAL y-DEGREES (6,9) WITH 3|H.  CONSEQUENTLY EVERY CHARACTERISTIC-ZERO
KELLER PAIR WITH MAXIMUM ACTUAL y-DEGREE AT MOST ELEVEN IS A POLYNOMIAL
AUTOMORPHISM.`**

- Snapshot: `2026-08-24`
- Status: producer-complete, frozen, and ready for a fresh different-model
  review of the composition
- Cube-core trajectory review: **CONFIRMED**, SHA-256
  `7bcf18d69344acc2277a0184ca1aeeb717ebad35c3aacf91421874b7e59f5cc9`
- Field: arbitrary characteristic-zero field, by algebraic-closure base
  change and descent
- Degrees: actual partial degrees `deg_y`, not total degrees and not support
  caps
- Generic coefficient search, AWS, and canonical-file edits: none
- JC2: not claimed

The mathematical work in the leaves is not reproved here.  It is supplied by
the hash-pinned producer/review pairs in Section 7.  The new content is the
theorem-level composition: every successor premise is named, the two branch
partitions are explicit, two hostile typing controls are run, and all degree
pairs through eleven are recursively enumerated.

## 1. Exact theorem and field passage

Let `k` be a field of characteristic zero and let `P,Q in k[x,y]` satisfy

```text
det J(P,Q)=j in k*.
```

Write `m=deg_y(P)`, `n=deg_y(Q)`.  The composed result is:

```text
(A)  If (m,n)=(6,9), and the primitive common leading core h has
     3 | H=deg(h), then no such Keller pair exists.

(B)  If max(m,n)<=11, then k[P,Q]=k[x,y].
```

It is enough to prove the leaf exclusions after extending `k` to its
algebraic closure.  The Jacobian constant, actual `y`-degrees, the leading
identities, and both original polynomial boundary values survive this
extension.  Statement (A) over the algebraic closure forbids the original
pair.  For the classical leaves in (B), automorphy after scalar extension
descends: a polynomial inverse is unique and therefore fixed by descent
(equivalently, use faithful flatness).  Thus no algebraic-closure hypothesis
remains in the displayed theorem.

The statement is deliberately not that every arbitrary `(6,9)` pair is
empty.  If `3` does not divide `H`, the reviewed history theorem makes the
pair automorphic by a large source shear and the prime-total-gcd theorem.
The empty residue proved here is exactly `(6,9),3|H`.

## 2. Charged landing shared by both branches

After swapping targets and constant target scalings as in the reviewed
history and first common-cubic gate, an actual `(6,9)` residue has

```text
a6=alpha h^2,             b9=beta h^3,
s^3=h,                    delta=3A-2B in k,
```

over `L=k(x)(s)`.  The original Taylor polynomiality conditions for
`P(x,0)` and `Q(x,0)` and all required jets remain charged.  The depression
`z=sy+r` is an identity over the coefficient extension, not a polynomial
source automorphism.

Exactly one of the following holds in `k(x)`:

```text
N: h is not a cube;                 C: h is a cube.
```

This is the first exhaustive partition.  The cube route later has the second
exhaustive partition `d=-delta/2=0` or `d!=0`.

## 3. Noncube route

If `h` is not a cube in `k(x)`, then `T^3-h` gives the reviewed nontrivial
cubic Kummer branch.  With a primitive cube root `omega`, `delta` is both a
base-field constant and a weight-one quantity.  Hence

```text
delta=omega delta,
(omega-1)delta=0,
(omega-1)^(-1)=-(omega+2)/3,
delta=0.                                                (3.1)
```

The inverse identity is exact modulo `omega^2+omega+1`; no division by a
possibly vanishing coefficient occurs.  The same Kummer action forces
exactly the reviewed nonzero-weight constants

```text
c7=c5=c4=c2=c1=0,
```

while `c6,c0` are removed by the reviewed target gauges and the `c3`
coordinate is handled covariantly under the reviewed first-target
translation.  The resulting five-coefficient invariant fibre, with the
terminal Jacobian row and original Taylor boundaries still present, is
precisely the input of the reviewed aligned lower-Pfaffian exclusion.  That
theorem makes the noncube leaf empty.

No full-cubic boundary factor, orbit-degree-three hypothesis, or polynomial
source depression is used.

## 4. Polynomial-cube route

If `h` is a cube in `k(x)`, Gauss's lemma and algebraic closedness of the
constant field give, after absorbing a constant,

```text
h=s^3,                  s in k[x].                    (4.1)
```

There is no nontrivial Kummer action on this route.  In particular none of
`c7,c5,c4,c2,c1` is weight-forced to vanish.  The reviewed cube Faber landing
is consumed with all constants retained:

```text
g=[H(f^(1/6))]_+,
r1'=r2'=r3'=r4'=0,
6 r5'=j/s,                                          (4.2)
```

together with both original polynomial Taylor boundaries.  Its finite-pole
theorem is exhaustive:

```text
s in k*                         or
s=C(x-a)^m,  m>=2.                               (4.3)
```

Only after the full landing do we split `d=-delta/2`.

| Cube leaf | Target data retained | Reviewed terminal theorem | Result |
|---|---|---|---|
| `d!=0` | the complete `d!=0` invariant quotient and every later target load | constant-`s` and monomial-`s` trajectory closure, including mixed and unmixed fibres | empty |
| `d=0` | the separate quotient, with `c7,c5,c4,c2,c1` retained after legal gauges | constant-`s` and monomial-`s` trajectory closure, including all high-constant and target-load strata | empty |

The trajectory review explicitly confirms the mixed `rho3,rho4` case: after
`rho1=rho2=0`, put `mu=6rho3`, `nu=6rho4`; it splits `nu!=0` from `nu=0`
without setting `rho4=0` when `rho3!=0`.  Thus no later target constant is
lost in this handoff.  The same review separately reconstructs `d!=0` and
`d=0` through the original coefficient equations and boundaries.

This closes both cube leaves.  Together with Section 3 and the two binary
partitions, it proves (A).

## 5. Mandatory branch-typing controls

The portable replay runs two controls before issuing the composition bit.

### 5.1 Noncube control

For

```text
h=x(x-1)(x-2),
```

`h(0)=0` and `h'(0)=2`, so its divisor at zero has valuation one and `h` is
not a cube in `k(x)`.  A formal `delta` is not initialized to zero.  It is
routed through the Kummer fixed/weight-one relation and (3.1), which derives
`delta=0`, before the aligned theorem may be consumed.

### 5.2 Cube `d=0` control

For

```text
s=x^2+1,             h=s^3,
d=0,                 c7=1,
c5=c4=c2=c1=0,
```

the replay reconstructs

```text
h=x^6+3x^4+3x^2+1,
```

so `H=6` and `3|H`.  The nonzero `c7` survives the cube split and enters the
separate `d=0` five-constant Faber quotient.  The replay aborts if the
aligned Kummer-vanishing fact appears on this route.  This is a routing
control, not a claim that the displayed constants themselves solve the
Faber equations.

## 6. Exact degree coverage through eleven

Assume `0<=m<=n` after swapping the two target coordinates.  Use the reviewed
history routes:

- `Z`: `m=0`;
- `G`: `gcd(m,n)<=2`, closed for every common-core degree by the large
  triangular source shear and the reviewed prime/`2p` total-gcd theorems;
- `D`: `m<n` and `m|n`, where a target shear replaces the larger coordinate
  by one of degree `r<n`;
- `E`: `m=n`, where constant target `GL_2` replaces one coordinate by one of
  degree `r<n`;
- `X`: `(m,n)=(6,9)`, with `3 not| H` routed by the prime-gcd shear and
  `3|H` routed by Sections 2--4.

For `D`, every possible child is `sort(m,r)`, `0<=r<n`.  For `E`, every
possible child is `(r,n)`, `0<=r<n`.  Both decrease the lexicographic measure

```text
(max(m,n),m+n),
```

so recursion cannot cycle.  The following is the complete unordered table;
each entry lists the smaller degrees `m` assigned to each route at fixed
maximum `n`.

| `n` | `Z` | `G` | `D` | `E` | `X` |
|---:|---|---|---|---|---|
| 0 | `0` | — | — | — | — |
| 1 | `0` | `1` | — | — | — |
| 2 | `0` | `1,2` | — | — | — |
| 3 | `0` | `1,2` | — | `3` | — |
| 4 | `0` | `1,2,3` | — | `4` | — |
| 5 | `0` | `1,2,3,4` | — | `5` | — |
| 6 | `0` | `1,2,4,5` | `3` | `6` | — |
| 7 | `0` | `1,2,3,4,5,6` | — | `7` | — |
| 8 | `0` | `1,2,3,5,6,7` | `4` | `8` | — |
| 9 | `0` | `1,2,4,5,7,8` | `3` | `9` | `6` |
| 10 | `0` | `1,2,3,4,6,7,8,9` | `5` | `10` | — |
| 11 | `0` | `1,2,3,4,5,6,7,8,9,10` | — | `11` | — |

The priority convention labels `(1,1)` and `(2,2)` by `G`; they could also
be treated by `E`.  Every `D/E` child is recursively checked, not merely the
displayed first reduction.  Before the new composition the unique terminal
nonclassical primitive in all `78` unordered pairs is

```text
(6,9), 3|H.
```

After composition there is none.  Swap symmetry then covers all
`12^2=144` ordered pairs.  This proves (B).

As a frontier checksum only, the same classifier at maximum twelve finds
exactly two new primitive pairs:

```text
(8,12), (9,12).
```

No maximum-twelve theorem is claimed.

## 7. Reviewed dependency ledger

The replay refuses to run if any of these exact bytes changes.

```text
6994dd6bc1642122ba549be474d2465203faf554d93da5146ecb212dbaaf89fe  xmodel/as109-partial-y-history-stop-20260824.md
f9d547f0f17dc3557ed8edce19912b4930dc2125542c7f9b3e4782c554a03afd  xmodel/as109-partial-y-history-review-grok-20260824.md
f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8  xmodel/gcd3-69-common-cubic-first-gate-20260824.md
5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503  xmodel/gcd3-69-common-cubic-first-gate-review-grok-20260824.md
7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043  xmodel/gcd3-69-lower-pfaffian-successor-20260824.md
a000619d8b5597add21716d525856c459ff57d5a2b2ab75b85de5d9d08970b27  xmodel/gcd3-69-lower-pfaffian-successor-review-grok-20260824.md
43fa36968bb90414748330c1b4a5d5169a0eaa21b1925623764e96204e049c78  xmodel/gcd3-69-target-translation-erratum-20260824.md
f4cb57ca765138ed2decab01b12a7f884c37f9a847d80e90162ee751bb3df837  xmodel/gcd3-69-target-translation-erratum-review-grok-20260824.md
6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20  xmodel/gcd3-69-cube-mismatch-gate-20260824.md
2648eef3b8091970655a94743c6c181343a94534b6454f43c579b310331ba7d7  xmodel/gcd3-69-cube-mismatch-review-grok-20260824.md
069f6280332b44d93dcad17801dc7136d4a79fb06ace101c2dce8a4e746b5e7b  xmodel/gcd3-69-cube-trajectory-kuranishi-20260824.md
7bcf18d69344acc2277a0184ca1aeeb717ebad35c3aacf91421874b7e59f5cc9  xmodel/gcd3-69-cube-trajectory-kuranishi-review-grok-20260824.md
```

The handoff graph is exactly:

```text
reviewed history stop
  -> actual (6,9), 3|H, leading h^2/h^3
  -> reviewed first common-cubic split
       -> h noncube
            -> exact delta=0 + reviewed Kummer high form
            -> reviewed aligned lower-Pfaffian exclusion
       -> h cube
            -> reviewed full cube Faber--Laurent landing
            -> d!=0 / d=0
            -> confirmed cube trajectory closure in each leaf
  -> degree recursion through maximum eleven.
```

## 8. Replay, failure semantics, and scope

Run from the repository root:

```sh
python3 cases/gcd3_69_coverage_composition_20260824/replay.py
```

The successful terminal markers are:

```text
PASS-GCD3-69-COVERAGE-COMPOSITION
stress_noncube=formal-delta-derived-zero
stress_cube_d0=c7-retained-full-weight-unforced-Faber
primitive_before_composition=(6,9),3|H
max_actual_y_degree_le_11=ALL_144_ORDERED_PAIRS_COVERED
max12_first_primitives=(8,12),(9,12)
payload_sha256=d7e030685c84e7c7366524e4b28f8516a5bf9d5060c3ebdba3990ca2e243ecd4
```

The route state throws `UNCLAIMED` on a missing successor premise, an input
hash mismatch, a lost `c7`, an aligned Kummer vanishing on the cube route, an
extra primitive through eleven, or a changed maximum-twelve frontier.  PASS
strings are regression markers only; the reviewed reports are the
mathematical evidence.

No conclusion here uses a full-cubic boundary reduction, treats `z=sy+r` as
a polynomial source automorphism, or imports nontrivial-Kummer weight
vanishing into the polynomial cube core.  No arbitrary-support theorem,
total-degree bound, maximum-twelve theorem, polynomial counterexample, or
JC2 decision follows.
