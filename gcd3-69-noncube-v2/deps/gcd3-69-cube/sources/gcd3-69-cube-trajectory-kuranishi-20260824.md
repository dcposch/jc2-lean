# GCD3 `(6,9)` cube-core rational trajectory gate

## Weighted pole balances, ramified common strata, and reconstruction through the original boundaries

**Producer verdict: `CONDITIONAL ON THE CONFIRMED CUBE-CORE
FABER--LAURENT REDUCTION, BOTH TERMINAL FINITE-POLE BRANCHES ARE EMPTY.
THIS CLOSES d!=0 AND THE SEPARATE d=0 POLYNOMIAL CUBE CORE.  IT DOES NOT BY
ITSELF CLOSE AN ARBITRARY (6,9) PAIR OR JC2.`**

- Snapshot: `2026-08-24`
- Field: algebraically closed characteristic-zero constant field `k`
- Exact engines: SymPy `1.14.0`, Singular `4.4.1`
- Producer lane: Codex/Sol, independent of the external Claude successor;
  no Claude output was read or consumed
- Lifecycle: producer-complete and review-ready; provisional until hostile
  different-model review
- Generic coefficient rectangle, random search, AWS: none
- Polynomial Keller pair found: none

This is the rational-trajectory successor to the confirmed cube-mismatch
gate.  It starts with its exact Faber form and five Laurent invariants, not
with the aligned nontrivial-Kummer normal form.  In particular, no Kummer
weight vanishing is imported.  The `d=0` quotient is made first and retains
all five constants allowed there.

The conclusion is an exclusion at the exact polynomial cube-core scope:

```text
h=s^3,  s in k[x],
z=s y+r,
g=[H(f^(1/6))]_+,
r1'=r2'=r3'=r4'=0,  6r5'=j/s,
all original Taylor boundary jets polynomial.
```

The predecessor proves that a rational trajectory has only two possible
cores, `s in k*` or `s=C(x-a)^m`, `m>=2`.  Sections 3--8 below exclude both.

## 1. Charged identities and target quotient

Write

```text
f=z^6+a4 z^4+a3 z^3+a2 z^2+a1 z+a0,

H(T)=T^9+dT^8+c7T^7+c5T^5+c4T^4+c3T^3+c2T^2+c1T
```

after removing `c6` and `c0`.  The exact high-row solution is

```text
g=[H(f^(1/6))]_+.
```

If `H(w)-g=sum_(n>=1) r_n w^-n`, the five lower rows are exactly

```text
r1'=r2'=r3'=r4'=0,              6r5'=j/s.            (1.1)
```

For `d!=0`, use the target-translation-invariant quotient from the confirmed
erratum.  For `d=0`, set `c3=0`; the retained constants are

```text
c7,c5,c4,c2,c1,                                      (1.2)
```

where `c1` means the invariant barred value `nu0/9`.  Translation changes
`a0` only by a constant and preserves every pole, degree, and boundary
condition used below.

The weights are

```text
wt(a0,a1,a2,a3,a4)=(6,5,4,3,2),
wt(d,c7,c5,c4,c3,c2,c1)=(1,2,4,5,6,7,8),
wt(r_n)=9+n.                                          (1.3)
```

The replay derives the `r_n` again from the Faber polynomial and verifies
(1.3), rather than importing their 239 printed monomials.

## 2. Exhaustive weighted leading components

At a pole choose `L=t^-p`, `p>0`, so

```text
a_i=L^(6-i)(A_i+lower),
```

with at least one nonzero `A_i`.  Constants of weight `q` enter the scaled
equations at `epsilon^q`, where `epsilon=L^-1`.

The leading four equations are `r1^0=...=r4^0=0`, where the superscript
means all high constants zero.  Weighted Euler and the invertible `6^5`
lower-row matrix identify this scheme with the confirmed constant-W scheme.
Its reduced projective support has exactly two components.

### 2.1 Uniform terminal exponent and exact source boundaries

Let `k` be the first scaled weight at which the terminal invariant is
nonzero.  Thus `k=0` on DS, `k=1` on the `d!=0` common row, and on a forced
common row `k` is the weight of its first high constant or target load.  In
every row to which this notation is applied below, the exact replay proves
that the coefficient `gamma` is nonzero and

```text
r5=gamma L^(14-k)+lower.                              (2.1)
```

This gives one pole formula for both terminal branches.  If `s` is constant,
then `6r5'=j/s` makes `r5=alpha x+beta`, `alpha!=0`.  At infinity take
`L=x^p`; differentiating (2.1), or just comparing its pole order with the
simple pole of an affine function, gives

```text
(14-k)p=1.                                           (2.2)
```

If `s=Ct^m`, `t=x-a`, then

```text
r5=c+j t^(1-m)/(6C(1-m)).
```

Now `L=t^-p`, and differentiation of the leading term in (2.1) has order
`t^(-(14-k)p-1)`.  Comparison with `j/(6Ct^m)` gives

```text
(14-k)p=m-1.                                         (2.3)
```

This explicitly reconciles the two constant-core exponents used below:
DS has `k=0` and hence `p=1/14`; the `d!=0` common-cubic row is forced one
weight later, `k=1`, and hence has `p=1/13`.  They are different leading
components, not competing values for the same balance.

Here are the exact original-boundary identities behind every finite-pole
test.  Write `P_l=[y^l]P` and `Q_l=[y^l]Q`.  Since
`P(x,y)=f(x,sy+r)` and `Q(x,y)=g(x,sy+r)`, Taylor expansion and its inverse
give

```text
P_l=s^l f^(l)(r)/l!,       f(x,z)=sum_(l=0)^6 P_l s^-l(z-r)^l,
Q_l=s^l g^(l)(r)/l!,       g(x,z)=sum_(l=0)^9 Q_l s^-l(z-r)^l.   (2.4)
```

In particular `P_5=6s^5r`.  For constant `s`, this makes `r` and all
depressed coefficients polynomial.  For `s=Ct^m`, it gives

```text
r=P_5/(6C^5t^(5m)),       a_i,b_i in k[t,t^-1].       (2.5)
```

The value rows are not replaced by a normal-form boundary.  Define exactly

```text
Fbar(t,xi)=L^-6 f(t,L xi),   Gbar(t,xi)=L^-9 g(t,L xi),
R(t)=r(t)/L.
```

Then

```text
P_0=f(t,r)=L^6 Fbar(t,R),   Q_0=g(t,r)=L^9 Gbar(t,R). (2.6)
```

For a forced common row `h=epsilon^(k/2)`, `epsilon=L^-1`, regularity of
these two original polynomials at `t=0` therefore requires

```text
ord_h Fbar(t,R)>=12/k,       ord_h Gbar(t,R)>=18/k.   (2.7)
```

Equations (2.4)--(2.7), rather than an aligned Kummer boundary, are used in
Sections 4--7.

### 2.2 DS component

For nonzero `lambda`,

```text
a4=4lambda,  a3=a1=0,  a2=10lambda^2,  a0=6lambda^3,
r1^0=...=r4^0=0,      r5^0=(27/2)lambda^7.           (2.8)
```

At infinity in the constant-`s` branch, (2.2) with `k=0` forces `p=1/14`.
But `a4` would then have polynomial degree `2p=1/7`.  Thus no polynomial
coefficient path is DS-leading.

At the finite pole of `s=Ct^m`, (2.3) forces

```text
14p=m-1.                                              (2.9)
```

Integral coefficient valuations require `2p in Z`, hence
`m=7 ell+1`.  This is the familiar pure-DS valuation.  It still fails the
original source: at `lambda=1`,

```text
Res_z(f_DS,g_DS)=3^9 7^2/2^5 !=0.                    (2.10)
```

No leading value of the boundary depression `r/L` can make both
`f_DS(r/L)` and `g_DS(r/L)` vanish.  One of `P(t,0)=f(r)` and
`Q(t,0)=g(r)` therefore has a pole.  Lower weighted terms cannot cancel a
nonzero leading resultant.  This excludes every DS-leading monomial core,
not only an exactly pure DS path.

### 2.3 Common-cubic component

Put

```text
K=z^3+u z+v,

(a4,a3,a2,a1,a0)=(2u,2v,u^2,2uv,v^2),               (2.11)
```

where `(u,v)!=(0,0)`.  A first transverse normal is

```text
phi=Xz^2+Yz+Z,

a2=u^2+hX,  a1=2uv+hY,  a0=v^2+hZ.                  (2.12)
```

All five invariants have zero linear term in `h`.  Their universal quadratic
terms are

```text
Q1=-(729uX^2-1458XZ-729Y^2)/1944,
Q2=(-2187vX^2-4374uXY+4374YZ)/5832,
Q3=(2u^2X^2-6vXY-4uXZ-2uY^2+3Z^2)/8,
Q4=(19683uvX^2+13122u^2XY-26244vXZ
    -13122vY^2-13122uYZ)/52488,
Q5=(-729u^3X^2+2187v^2X^2+4374uvXY+1458u^2XZ
    +729u^2Y^2-4374vYZ)/17496.                       (2.13)
```

At the original coefficient level,

```text
f=K^2+h phi+O(h^2),
g=K^3+(3/2)hK phi+O(h^2).                            (2.14)
```

This identity is the boundary reconstruction used below; it is not a
normal-form ansatz.

## 3. Rank and boundary strata of the common component

The unforced normal cone `Q1=...=Q4=0`, saturated away from
`X=Y=Z=0`, is supported exactly on

```text
Delta=4u^3+27v^2=0.                                  (3.1)
```

Thus a squarefree `K` has no field-valued unforced transverse first term.
The only nonzero projective normal occurs at a double-root cubic.  Normalize

```text
K=(z-1)^2(z+2),       (u,v)=(-3,2),
phi=(z-1)(z+2),       (X,Y,Z)=(1,1,-2).              (3.2)
```

Allow every next coefficient `p0,...,p4` at order `h^2` and put
`S=p0+...+p4`.  The complete cubic row is

```text
(r1,r2,r3,r4,r5)|_(h^3)
 =(3S/4, 3S/4, -1/16, -(4S+3)/16, (4S-3)/16).        (3.3)
```

In particular the `r3` obstruction is independent of all five next
coefficients.  Every high constant has zero `r3` load on the common surface.
Consequently no earlier `h=epsilon^(k/3)` double-root arc can bypass any of
the forced quadratic rows in Sections 4 or 5.  For a putative `rho3` load,
`r1=r2=0` forces `S=0`, while `r4=-3/16` remains.  No target-only or
terminal-only double arc survives either.

The triple point `(u,v)=(0,0)` is the affine intersection of the common and
DS components, but it is not a point of the weighted projective pole
boundary: it would make every leading `A_i` zero.  Rechoosing the maximal
pole scale returns one of the cases above.  It contributes no third pole
balance.

## 4. `d!=0`: the two exceptional orbits reconstruct and fail

Set `h=epsilon^(1/2)` and scale `d` to one.  Adding the `d` load to (2.13)
and eliminating `X,Y,Z` from the first four equations gives exactly

```text
P_d(u,v)=2u^6-90u^3v^2+135v^4=0.                    (4.1)
```

If `u=0` or `v=0`, (4.1) forces `(u,v)=(0,0)`, which is not projective.
For `v!=0`, its two weighted orbits are

```text
q=u^3/v^2=(45+3sqrt(195))/2,
q=u^3/v^2=(45-3sqrt(195))/2.                         (4.2)
```

Neither equals the double-root value `-27/4`; both are squarefree.

The reconstruction is exact.  Normalize `v=1` and adjoin

```text
2u^6-90u^3+135=0.
```

The four Kuranishi quadrics cut a zero-dimensional normal scheme of length
eight.  On this entire scheme,

```text
Res_z(K,phi) !=0,                   T_d !=0,          (4.3)
```

where `T_d` is the full `h^2` coefficient of `r5`, including its `d` load;
it is not merely the unforced quadratic `Q5` of (2.13).

The projection ideal is equal to `(P_d)`, not just contained in it.  No
division by `u` or `v` was used; the two axis charts are checked before the
legal normalization `v=1`.  Every displayed row multiplier is a nonzero
rational integer in characteristic zero.  The length-eight reconstruction
over `2u^6-90u^3+135` and the two unit-ideal certificates therefore make the
elimination reversible on every projective orbit.  Thus (4.2) is not being
discarded at a necessary-only row.

For `s` constant, (2.2) with `k=1` and (4.3) give `r5~L^13` and
`p=1/13`; both `u` and `v` are nonzero, so already `a4` has impossible
polynomial degree `2/13`.  This is the `1/13` row, distinct from the DS
`1/14` row of Section 2.2.

For `s=Ct^m`, (2.6), (2.7), (2.14), and the first assertion in (4.3)
retain the original boundary.  Put `q0=ord_h K(R)`, `R=r/L`.  If `K(R)`
tends to zero, `Res(K,phi)!=0` makes `phi(R)` a unit.  Away from
`2q0=1`, the scaled `f` has order at most one.  At `2q0=1`, the only
possible leading cancellation in `K^2+hphi` leaves

```text
K^3+(3/2)hKphi=(1/2)hKphi+...,
```

of exact order `3/2` in `g`.  Here `h=epsilon^(1/2)`, while (2.7) requires
scaled orders `12` and `18`.  Thus either the value row of `P` or that of
`Q` fails.  Lower terms cannot change the first nonzero order.  Hence no
original polynomial boundary lifts either exceptional orbit.

This proves:

> The confirmed `d!=0` cube-mismatch survivor has no rational trajectory in
> either terminal finite-pole branch.

## 5. `d=0` with a nonzero retained high constant

Use the correct quotient `c3=0`.  Let `theta` be the first nonzero constant
in the order `(c7,c5,c4,c2,c1)`, and let `k=wt(theta)`.  Balance
`h=epsilon^(k/2)`.  Exact elimination gives this complete first-row table.

| `theta` | `k` | projective Kuranishi support |
|---|---:|---|
| `c7` | 2 | `uv(u^3-6v^2)=0` |
| `c5` | 4 | `v(u^3-3v^2)=0` |
| `c4` | 5 | `u(u^3-18v^2)=0` |
| `c2` | 7 | `u^3-9v^2=0` |
| `c1` | 8 | `uv=0` |

Every nonzero point in the table is squarefree.  On every displayed orbit,

```text
Res_z(K,phi) !=0,                   T_theta !=0.      (5.1)
```

Here `T_theta` is the full forced `h^2` terminal coefficient, including the
first nonzero high-constant load.

The companion Singular replay checks both projective charts, so axes are not
lost to division by `u` or `v`.  Each displayed support is an equality of
elimination ideals after multiplication only by explicit nonzero rational
integers; the resultant and terminal assertions are projective unit-ideal
certificates on both charts.

For constant `s`, `T_theta!=0` gives

```text
(14-k)p=1.                                             (5.2)
```

The possible denominators are `12,10,9,7,6`.  At a nonzero projective
point, `u!=0` makes `2p` a polynomial degree and `v!=0` makes `3p` one.
The axes and mixed orbits give respectively the degree tests encoded in the
replay:

```text
c7: {2p},{3p},{2p,3p};   c5: {2p},{2p,3p};
c4: {3p},{2p,3p};        c2: {2p,3p};       c1: {2p},{3p}.
```

No listed support makes all of its nonzero leading degrees integral.  Thus
the constant-`s` branch is empty.

For `s=Ct^m`, the boundary argument of Section 4 applies with
`h=epsilon^(k/2)`.  Source regularity requires scaled orders `12/k` and
`18/k`.  By (2.14) and `Res(K,phi)!=0`, either `Fbar` has order at most
`1`, or cancellation at `ord_h K(R)=1/2` makes `Gbar` have exact order
`3/2`.  Since `k<=8`, both required inequalities are strict.  Thus the
monomial branch is empty as well.

## 6. `d=0` with all high constants zero: target balance

It remains to set

```text
d=c7=c5=c4=c3=c2=c1=0.                              (6.1)
```

Put `r_i=rho_i` for `1<=i<=4`.  If `rho_j` is the first nonzero target
constant, its scaled weight is `9+j`.  The forced quadratic rows give

| first nonzero target | weight | necessary common support |
|---|---:|---|
| `rho1` | 10 | `v=0` |
| `rho2` | 11 | `u=0` |
| `rho3` | 12 | dominant in `(u,v)` |
| `rho4` | 13 | empty as a first common quadratic row |

For `rho1` and `rho2`, both the common resultant and `Q5` are nonzero on the
displayed support.  A monomial core fails the same boundary inequality as
above (`12/k>1` and `18/k>3/2` for `k=10,11`).  The equality threshold
first occurs at `k=12`, so this argument intentionally does not discard the
`rho3` row.

For constant `s`, `rho1` would give `p=1/4` and the impossible degree
`deg(a4)=1/2`.  The `rho2` row gives `p=1/3` and leading `u=0`, but its
normal terms occur at `epsilon^(11/2)`:

```text
deg corrections to (a2,a1,a0)=(-1/2,-1/6,1/6).
```

Polynomiality would force `X=Y=Z=0`, contradicting the nonzero `rho2` load.

No quadratic normal can supply only the terminal row: adjoining `Q5=1` to
`Q1=...=Q4=0` gives the unit ideal.  The only unforced double normal is
already killed by (3.3).  These first-row statements prove exactly

```text
rho1=rho2=0,             rho3,rho4 arbitrary.        (6.2)
```

They do **not** set a later `rho4` to zero after a nonzero `rho3` row.  The
mixed `(rho3,rho4)` fiber is reconstructed next.  If `rho3=0` and `rho4`
is first, the empty entry in the table only rules out a common quadratic
landing; its possible DS-leading ends are likewise retained in Section 7.1.

## 7. Exact reconstruction of all last invariant fibers

In the zero-high-constant specialization, the four lower invariants from the
reviewed universal decomposition satisfy

```text
(I4,I3,I2,I1)=6(r1,r2,r3,r4).                        (7.1)
```

Put

```text
mu=I2=6rho3,                 nu=I1=6rho4.             (7.2)
```

The cases `nu!=0` and `nu=0` are genuinely different.  Both are retained.

### 7.1 Mixed later target: `nu!=0`

Use the invertible rational coordinates

```text
A=4a2-a4^2,       B=2a1-a3a4,       w=4a0-a3^2,
p=a3,             q=a4.
```

At `kappa=0`, the first two invariant numerators become exactly

```text
e4=-A^2q+4Aw+8B^2,
e3=-A^2p-4ABq+8Bw.                                  (7.3)
```

If `A=0`, (7.3) gives `B=0`, and then the exact `I1` numerator gives
`nu=0`.  Thus `nu!=0` licenses localization at `A`.  Define

```text
V=w+8B^2/A.
```

Solving (7.3), with no choice of branch, gives

```text
q=4w/A+8B^2/A^2,       p=-8Bw/A^2-32B^3/A^3.        (7.4)
```

Substitution into the other two invariants gives the complete mixed fiber

```text
A^2B=-256nu/9,
72V^2-3A^3-512mu=0.                                 (7.5)
```

Conversely, (7.4)--(7.5), followed by

```text
a4=q,  a3=p,  a2=(A+q^2)/4,
a1=(B+pq)/2,  a0=(w+p^2)/4,                         (7.6)
```

reconstructs every original coefficient and all four invariants.  The
Singular replay proves equality of the two localized ideals after adjoining
`TA-1`; all denominators are powers of the now-proved unit `A` and rational
integers.  This is an exact birational model, not a necessary projection.
Direct Faber substitution also gives

```text
r5=A^2V/1024-256nu^2/(27A^3).                        (7.7)
```

If `mu!=0`, (7.5) is a smooth projective genus-one curve.  A rational
coefficient path supplies `A,V in k(x)`, hence a rational map from `P1` to
that curve.  Properness and Riemann--Hurwitz make it constant; (7.4)--(7.7)
then make the coefficient path and `r5` constant, contradicting
`6r5'=j/s`.

If `mu=0`, the cusp has rational normalization

```text
A=24lambda^2,        V=24lambda^3,        lambda=V/A,
r5=(27/2)lambda^7-nu^2/(1458lambda^6).                (7.8)
```

Because `nu!=0`, the rational map on the right has two distinct pole
places: order six at `lambda=0` and order seven at `lambda=infinity`.
Every nonconstant rational `lambda(x)` is surjective on projective lines,
so the composition in (7.8) has nonempty, disjoint pole divisors above both
places.  It therefore has at least two pole points.  In contrast, an affine
`r5` for constant `s` has only its pole at `x=infinity`, while
`c+j t^(1-m)/(6C(1-m))` for a monomial core has only its pole at `t=0`.
A constant `lambda` makes `r5'=0`.  Thus the complete mixed target fiber is
empty in both terminal branches, including `rho3=0,rho4!=0`.

### 7.2 Unmixed target: `nu=0`

Now (7.1)--(7.2) are precisely the `kappa=0` universal fiber with
`I4=I3=I1=0`, `I2=mu`.  The different-model-reviewed Singular certificate
is rerun as part of this case.  Its reduced field-valued support has exactly
two sheets; the embedded component adds no third path.

#### 7.2.1 Zero-bracket sheet

For a constant `eta`,

```text
K=z^3+(a4/2)z+a3/2,
f=K^2+eta,
g=K^3+(3eta/2)K.                                    (7.9)
```

Direct reconstruction gives

```text
f_x g_z-f_z g_x=0
```

for every moving `K`.  It cannot satisfy the terminal row.

#### 7.2.2 Elliptic sheet

The second sheet has rational coordinates

```text
X=8a2-2a4^2,       Y=3a4X,
Y^2=3X^3+4096mu.                                    (7.10)
```

If `mu!=0`, its smooth projective closure has genus one.  A rational
coefficient path gives a rational map `P1 -> E_mu`; properness extends it
across the missing points, and Riemann--Hurwitz makes it constant.  The
terminal one-form then vanishes, contradicting `j/s!=0`.  This argument is
specific to the cube core, where `X,Y in k(x)`; it imports no Kummer descent.

If `mu=0`, the sheet is zero-bracket or the DS curve

```text
r5=(27/2)lambda^7.                                   (7.11)
```

For constant `s`, a nonconstant affine function is not a seventh power in
`k(x)` (its simple zero already forbids it).  For `s=Ct^m`, rationality in
(7.11) first forces the additive constant in `r5` to vanish and
`m=7ell+1`; otherwise the numerator has simple finite zeros.  The surviving
formal value is `lambda=A t^-ell`, and the nonzero DS resultant (2.10)
excludes both original polynomial boundaries.  Thus the special fiber also
has no rational trajectory.

## 8. Original polynomial coefficients and completeness

The pole analysis above is exhaustive at the source level.  The ordering is
machine-readable in the companion replays:

| source of first nonzero row | `k` | exact disposition |
|---|---:|---|
| DS principal value | 0 | constant degree; monomial resultant |
| `d!=0` | 1 | two reconstructed squarefree orbits; boundary split |
| `c7,c5,c4,c2,c1` | 2,4,5,7,8 | all projective supports; degree/boundary |
| `rho1,rho2` | 10,11 | exact supports; degree/boundary |
| `rho3,rho4` | 12,13 | mixed elliptic/cusp model or unmixed two-sheet model |
| terminal-only quadratic row | 14 | unit ideal |

There is no omitted equal-weight collision: when `d!=0`, weight one is
strictly first; when `d=0`, the legal high weights are the distinct values
`2,4,5,7,8`; after all five vanish, the target weights are the distinct
values `10,11,12,13`.  The normal-cone replay also covers each of
`X!=0`, `Y!=0`, and `Z!=0`, and the projective common boundary is covered by
`u!=0` and `v!=0`.

- If `s in k*`, then (2.4) gives `r=P_5/(6s^5)` polynomial.  Its inverse
  reconstructs `f` from its expansion at polynomial `r`, so every `a_i` is
  polynomial.  Since `r5` is nonconstant affine, some `a_i` has a pole at
  infinity, where Sections 2--7 apply.
- If `s=Ct^m`, then (2.4)--(2.5) make `r` and every depressed coefficient
  Laurent polynomials with their only possible finite pole at `t=0`.  The prescribed
  `r5=c+j t^(1-m)/(6C(1-m))` has a pole there, so some `a_i` does too.
  Sections 2--7 apply at that pole.  Boundary exclusions always use the exact
  original values `f(r)=P_0` and `g(r)=Q_0` from (2.6); the stronger remaining
  Taylor jets cannot restore a failed value row.

No rational pole is omitted, and no analytic local trajectory is promoted
to a rational one.  The predecessor's regular local `d=1` survivor is a
useful negative control: this gate excludes it only after the global
degree/boundary conditions are imposed.

## 9. Exact outcome and scope

The strongest exact conclusion is:

> Assume the confirmed polynomial cube-core Faber--Laurent reduction for an
> actual-degree `(6,9)` Keller pair.  Then neither `s in k*` nor
> `s=C(x-a)^m`, `m>=2`, admits a rational coefficient trajectory satisfying
> the original polynomial source boundaries.  Hence the complete polynomial
> cube core is empty, separately for `d!=0` and `d=0`.

This closes the survivor frozen by the cube-mismatch gate.  It does **not**
silently import the aligned nontrivial-Kummer exclusion.  To state a theorem
about every `(6,9)` pair, one must additionally consume and correctly scope
the separately reviewed noncube/aligned branch and the first common-cubic
landing split.  To state anything about JC2, one still needs the surrounding
bounded-degree reduction and its global hypotheses.  Those implications are
not promoted here.

## 10. Deterministic replay

Run from the repository root:

```text
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_cube_trajectory_kuranishi_20260824/replay.py

Singular -q \
  cases/gcd3_69_cube_trajectory_kuranishi_20260824/verify_kuranishi.sing

Singular -q \
  cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing
```

Expected markers:

```text
PASS-GCD3-69-CUBE-TRAJECTORY-SYMBOLICS
PASS-GCD3-69-CUBE-KURANISHI-ELIMINATION
PASS-GCD3-69-D-EXCEPTIONAL-RECONSTRUCTION
PASS-GCD3-69-MIXED-TARGET-FIBER
PASS-GCD3-69-LOWER-INVARIANT-DECOMPOSITION
```

The PASS strings are regression markers.  The mathematical evidence is the
weighted Faber reconstruction, exact quadrics, eliminations and projective
unit certificates, double-root cubic obstruction, original-boundary
valuation, reversible mixed-target elliptic/cusp model, and universal
unmixed two-sheet decomposition above.
