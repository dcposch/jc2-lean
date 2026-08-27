# GCD3 `(6,9)` cube-core mismatch gate

## Complete high-row Faber form, Laurent first integrals, and the single-root core reduction

**Producer verdict: `THE CUBE-CORE HIGH AND LOWER ROWS INTEGRATE EXACTLY TO
A FIVE-INVARIANT FABER--LAURENT SYSTEM; THE TERMINAL ROW FORCES THE POLYNOMIAL
CUBE ROOT s TO BE CONSTANT OR A SINGLE-ROOT POWER; d!=0 REMAINS LIVE ON AN
EXACT ALGEBRAIC-CURVE/ODE/BOUNDARY SURVIVOR; RAMIFIED COMMON STRATA AND THE
d=0 CUBE CORE REMAIN OPEN`.**

- Snapshot: `2026-08-24`
- Checkout HEAD at materialization:
  `1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a`
- Charged confirmed first gate:
  `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8`
- Charged independent review:
  `5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503`
- Field: algebraically closed characteristic-zero constant field `k`
- Exact engine: SymPy `1.14.0` over `Q`
- Generic coefficient rectangle, random search, AWS: none
- Actual polynomial Keller pair, `(6,9)` exclusion, JC2 inference: none

This is the bounded independent successor for the cube-core mismatch branch.
It consumes the confirmed split but does not import any nontrivial-Kummer
weight vanishing. It also records a target-translation normalization erratum:
unless a target value is explicitly pinned, the first-coordinate translation
`P -> P+q` is legal and removes one more high-row constant.

There are four positive conclusions, at deliberately narrow scopes.

1. Every cube-core high-row solution, including `d=-delta/2`, has one exact
   closed Faber form retaining all nine constants before target quotient.
2. The five lower rows integrate exactly: four Laurent coefficients are
   constant and the fifth has derivative `j/(6s)`.
3. Since `s` is a polynomial in the cube core, rational exactness of the
   terminal row forces either constant `s` or
   `s=C(x-a)^m`, `m>=2`.
4. The coefficient system is not empty: an exact regular local formal survivor
   exists. Polynomiality and the full source boundary jets remain load-bearing.

The gate does **not** close `d!=0`. It does not close the cube core, because the
cube core also contains the separate `d=0` specialization with all constants
unrestricted by Kummer weights. It does not classify rational components of
the invariant fibres or ramified arcs from the nonreduced common component.

## 1. Source-honest cube-core normalization

Use the notation of the confirmed first gate. A genuine actual-degree `(6,9)`
pair has, after constant target scalings,

```text
a_6=h^2,                 b_9=h^3.
```

In the cube core, `h=s^3` with `s in k[x]`. Put

```text
A=a_5/s^5,       B=b_8/s^8,       delta=3A-2B in k,
r=A/6,           z=s y+r,          d=-delta/2.
```

The identity `z=s y+r` is used only in `k(x)[y]`; it is not declared a
polynomial source automorphism. In the depressed variable,

```text
f=z^6+a_4z^4+a_3z^3+a_2z^2+a_1z+a_0,
g=z^9+d z^8+b_7z^7+...+b_0.                           (1.1)
```

The exact chain rule remains

```text
J_(x,y)(P,Q)=s J_(x,z)(f,g).                           (1.2)
```

All terms involving `z_x` cancel. Source polynomiality retains the complete
boundary-jet conditions

```text
s^ell f^(ell)(r)/ell! in k[x],     0<=ell<=6,
s^ell g^(ell)(r)/ell! in k[x],     0<=ell<=9.          (1.3)
```

In particular, retaining only `f(r),g(r)` would be a weakening, and setting
them to zero would be incorrect.

The live mismatch branch is `d!=0`. Constant source/target scalings can
normalize `d=1` over the charged algebraically closed field, but formulas
below retain `d` so that the `d=0` cube-core stratum remains visible.

## 2. Complete high-row normal form

Let

```text
w=f^(1/6)=z+O(z^-1)
```

be the unique formal branch at `z=infinity`, and write

```text
F_j=[w^j]_+
```

for its polynomial part in `z`. Define the constant polynomial

```text
H(T)=T^9+dT^8+c_7T^7+c_6T^6+c_5T^5+c_4T^4
              +c_3T^3+c_2T^2+c_1T+c_0.              (2.1)
```

Then the complete solution of the eight source rows `z^12,...,z^5` is

```text
g=[H(w)]_+
 =F_9+dF_8+c_7F_7+c_6F_6+c_5F_5+c_4F_4
             +c_3F_3+c_2F_2+c_1F_1+c_0.             (2.2)
```

Here every `c_j` is an independent element of `k`. There is no Kummer action
in the cube core, so none may be discarded by weight. The registered replay
derives (2.2) twice: by formal polynomial parts and by integrating each
triangular one-form. The first coefficients are

```text
b_7=3a_4/2+c_7,

b_6=3a_3/2+4d a_4/3+c_6,

b_5=3a_2/2+4d a_3/3+3a_4^2/8+7c_7a_4/6+c_5,

b_4=3a_1/2+4d a_2/3+3a_3a_4/4+7c_7a_3/6
    +2d a_4^2/9+c_6a_4+c_4.                          (2.3)
```

Formula (2.2) is the exact compact form of all four remaining `b`-rows as
well; it is not an ansatz or a truncation in the coefficient variables.

To see generality without computation, the monic polynomials `F_j` are
triangular in `z`. Since `w^j` is a function of `f`, its bracket with `f`
vanishes. Removing its negative Laurent tail can contribute only to the five
rows `z^4,...,z^0`. Thus every right side of (2.2) kills the eight high rows.
Conversely, solving them from `b_7` down through `b_0` supplies exactly one
constant at each step, hence exactly (2.2).

## 3. Authoritative target-translation quotient

Two familiar target operations give

```text
Q -> Q-c_6P             removes c_6,
Q -> Q-c_0              removes c_0.                 (3.1)
```

The first-coordinate target translation is also legal when no target value
has been pinned. If

```text
P_new=P+q,               a_0,new=a_0+q,
```

then the same polynomial `Q` has Faber constants

```text
c_3,new=c_3-3q/2,
c_2,new=c_2-4dq/3,
c_1,new=c_1-7c_7q/6,
c_0,new=c_0-c_6q,                                      (3.2)
```

with `d,c_7,c_6,c_5,c_4` unchanged. The replay verifies (3.2) as a full
polynomial identity, not merely coefficientwise to one order.

### 3.1 The `d!=0` quotient

Set `c_2,new=0` using `q=3c_2/(4d)`. The target-invariant data are

```text
bar(a_0)=a_0+3c_2/(4d),
mu=8d c_3-9c_2,          bar(c_3)=mu/(8d),
nu=8d c_1-7c_7c_2,       bar(c_1)=nu/(8d),             (3.3)
```

together with `d,c_7,c_5,c_4`. All mismatch invariants below mean the
Laurent invariants computed in this unique `c_2=0` gauge. Thus they are
global target-translation invariants, not pinned-coordinate artifacts.

### 3.2 The `d=0` quotient and the normalization erratum

Division by `d` is forbidden on this stratum. Instead set `c_3,new=0` using
`q=2c_3/3`; retain

```text
c_2,          nu_0=9c_1-7c_7c_3,
bar(c_1)=nu_0/9,                                      (3.4)
```

and `c_7,c_5,c_4`. This is valid even when `c_7=0`.

In the nontrivial-Kummer aligned branch, weights additionally force

```text
c_7=c_5=c_4=c_2=c_1=0.
```

Equation (3.2) then removes `c_3` as well. Therefore the prior description
of `kappa=c_3` as “essential” was a **normalization error** unless the first
target value was explicitly pinned. This changes the parameter count, not
the target-invariant mathematical exclusion in the subsequent lower gate.
The cube-core `d=0` stratum is much larger than the nontrivial-Kummer branch
because its constants receive no weight vanishings; it remains open.

## 4. Exact integration of all five lower rows

Expand the negative Laurent tail in the formal coordinate `w`:

```text
H(w)-g(z(w))=r_1w^-1+r_2w^-2+r_3w^-3+r_4w^-4+r_5w^-5+... . (4.1)
```

Every `r_n` is a polynomial with rational coefficients in
`a_0,...,a_4,d,c_7,...,c_1`; `c_6,c_0` disappear after (3.1). The first five
have respectively `31,36,48,55,69` monomials in the pinned coordinates. The
coefficient definition (4.1), followed by the canonical quotient in Section
3, is smaller and less error-prone than printing those 239 terms.

At fixed `w`, `f=w^6` and `g=H(w)-sum r_nw^-n`. Therefore

```text
J_(x,z)(f,g)=f_z partial_x(H(w)-g)|_w.                 (4.2)
```

Only `n<=5` can contribute a nonnegative power of `z`. Direct binomial
expansion gives

```text
A_1=[f_z w^-1]_+
   =6z^4+3a_4z^2+2a_3z+a_2-a_4^2/12,
A_2=[f_z w^-2]_+=6z^3+2a_4z+a_3,
A_3=[f_z w^-3]_+=6z^2+a_4,
A_4=[f_z w^-4]_+=6z,
A_5=[f_z w^-5]_+=6.                                  (4.3)
```

The coefficient matrix from `(A_1,...,A_5)` to the rows
`(z^4,...,z^0)` is triangular with determinant `6^5`. Hence the complete
remaining Keller equation is exactly

```text
r_1'=r_2'=r_3'=r_4'=0,
6r_5'=j/s.                                             (4.4)
```

This is an equivalence, not a necessary-only projection. The replay also
integrates the row one-forms directly and verifies that their gradients are
the five Laurent coefficients of (4.1).

Thus a normalized trajectory lies on one algebraic fibre

```text
r_1=rho_1, ..., r_4=rho_4                            (4.5)
```

in five coefficient variables, and `r_5` supplies the time coordinate.
Generically (4.5) is a curve. A global polynomial Keller pair requires a
rational trajectory on one of its components satisfying (1.3); a local
analytic integral curve is not enough.

## 5. Exact terminal finite-pole reduction

This is the cheapest actual obstruction in the gate. In the cube core,
`s in k[x]`, all `a_i in k(x)`, and therefore `r_5 in k(x)`. Equation (4.4)
says that the rational differential

```text
(j/6) dx/s
```

is exact.

Suppose `s` is nonconstant of degree `m`, with `r` distinct finite roots of
multiplicities `e_1,...,e_r`. Rational differentiation raises every finite
pole order by one. Consequently:

- a simple root `e_i=1` is impossible;
- at a root of multiplicity `e_i>=2`, `r_5` has pole order exactly `e_i-1`;
- `r_5` has no other finite pole.

Therefore the pole degree of `r_5-c` is

```text
sum_i(e_i-1)=m-r.                                     (5.1)
```

At infinity, for `m>=2`, integration of the leading term of `1/s` gives

```text
r_5-c = j/[6 lc(s)(1-m)] x^(1-m)+lower powers.        (5.2)
```

Thus `r_5-c` has a zero of exact order `m-1` at infinity. The zero degree of
a nonzero rational function equals its pole degree, so

```text
m-1 <= m-r.
```

Since `r>=1`, necessarily `r=1`. Degree `m=1` would require a logarithm and
is impossible. We have proved the exact dichotomy

```text
s in k*;

or

s=C(x-a)^m,       m>=2,                               (5.3)
r_5=c+j/[6C(1-m)](x-a)^(1-m).                         (5.4)
```

This proof is independent of `d`; it applies verbatim to the open `d=0`
cube-core specialization. It does not apply directly to the nontrivial
Kummer branch, where `s` is not in `k(x)`.

When `s` is constant, (4.4) makes `r_5` affine in `x`. When (5.3) is
nonconstant, all normalized coefficients have possible finite poles only at
`x=a`, hence are Laurent polynomials in `x-a`; (1.3) remains to be imposed.
The gate does not claim that the monomial repeated cores are empty.

## 6. Exact controls and exceptional strata

### 6.1 Primitive cube-core rejection control

Take `s=x`, `r=0`, `f=z^6`, `g=z^9+d z^8`. Then

```text
P=x^6y^6,
Q=x^9y^9+d x^8y^8,
delta=-2d.
```

This is a primitive polynomial cube-core control with both polynomial
boundaries and all high rows. Its Jacobian is identically zero because both
coordinates are functions of `z=xy`. It is not a Keller pair. The terminal
theorem separately shows why no Keller trajectory can have this squarefree
core: `dx/x` is not rationally exact.

### 6.2 Regular local formal survivor

Normalize `d=1`, take all `c_j=0`, and evaluate at

```text
(a_0,a_1,a_2,a_3,a_4)=(0,0,0,0,1).
```

The Laurent values are exactly

```text
(r_1,...,r_5)=(-3/256,-8/729,5/1024,20/6561,-5/6144).
```

The determinant of the five lower Pfaffian rows is

```text
92286875/25048249270272 !=0.                           (6.1)
```

For terminal RHS `1`, the exact coefficient velocity is

```text
(128/3,
 131072/729,
 194683904/177147,
 1221232033792/4485142125,
 1689034934081536/1089889536375).                     (6.2)
```

Thus the mismatch coefficient equations admit a unique local formal/analytic
trajectory through this point. It is not asserted to be rational or
polynomial, and no source boundary is promoted. This control forbids an
algebraic “all rows inconsistent” verdict.

### 6.3 Weighted landing controls

At a pole, `d` and the `c_j` are lower-weight data. Setting `c_j=0`, the
ordinary first `d`-deformation of the four invariant equations gives these
exact rank pairs `(rank linear, rank augmented)`:

```text
DS point                         (4,4),
squarefree common point          (0,1),
double common point              (0,1),
triple common point              (0,0).                (6.3)
```

With `a_4` fixed on the DS slice, the first correction is

```text
(delta a_0,delta a_1,delta a_2,delta a_3,delta a_4)
 =(0,-660128/531441,0,-50176/531441,0).                (6.4)
```

So the DS infinity branch survives first order and must be treated as a
deformed DS trajectory. The common-component failures in (6.3) exclude only
ordinary first-order arcs. The common residual scheme is nonreduced; a
deviation of order `sqrt(d)` can contribute quadratically at the same order.
Ramified/Puiseux arcs are therefore explicitly open. The triple point is
exceptional already at first order.

### 6.4 `d=0` regression and open cube-core stratum

All formulas (2.2) and (4.1)--(4.4) are polynomial in `d` and specialize
without division. The quotient, however, must change from (3.3) to (3.4).
This `d=0` cube core retains `c_7,c_5,c_4,c_2` and the invariant combination
`nu_0`; it is not the nontrivial-Kummer aligned branch and is not closed by
the confirmed first gate.

## 7. Smallest exact survivor

After global target quotient, a live `d!=0` candidate consists exactly of:

1. constants
   ```text
   d!=0, c_7,c_5,c_4, mu=8dc_3-9c_2, nu=8dc_1-7c_7c_2,
   rho_1,...,rho_4;
   ```
2. a rational coefficient path on an irreducible component of
   ```text
   r_i=rho_i, 1<=i<=4;
   ```
3. either constant `s` and affine `r_5`, or the monomial core (5.3)--(5.4);
4. the complete boundary jets (1.3), actual degrees `(6,9)`, and the inverse
   depression provenance.

This is the frozen survivor. It is an algebraic-curve/rational-trajectory
problem with a prescribed time function and source jets, not a generic
coefficient rectangle.

The immediate independent successor is the same division-free invariant
system at `d=0`, with the quotient (3.4). It must not be silently included in
any future claim that “the mismatch branch” is closed.

## 8. Outcome and next licensed gates

The strongest licensed promotion is:

> In the polynomial cube core, all twelve nonterminal Jacobian rows at
> actual degrees `(6,9)` integrate exactly to constant Faber/Laurent data.
> The terminal row makes `dx/s` rationally exact and forces `s` to be constant
> or a single-root power. The remaining mismatch problem is the exact
> survivor in Section 7.

Do not promote this to emptiness of `d!=0`, emptiness of the cube core,
closure of `(6,9)`, a polynomial Keller pair, or JC2.

The next bounded gates, in order, are:

1. classify rational components of the invariant fibres that can carry the
   prescribed `r_5`; begin with `s=C(x-a)^m` and constant `s`;
2. compute the first nonzero ramified Kuranishi row at squarefree, double, and
   triple common landings, retaining the chosen boundary minimal factor;
3. continue the deformed DS branch from (6.4) and test both polynomial
   boundaries before any global claim; and
4. run the `d=0` cube core with its separate target quotient.

No generic coefficient enumeration or AWS job is licensed by this gate.

## 9. Deterministic replay

Run from the repository root, without network:

```text
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_cube_mismatch_gate_20260824/replay.py
```

Expected terminal output:

```text
PASS-GCD3-69-CUBE-MISMATCH-GATE
high_row_normal_form=g=[H(f^(1/6))]_+
pinned_constants=d,c7,c6,c5,c4,c3,c2,c1,c0
global_target_gauges=REMOVE-c6,c0-AND-QUOTIENT-P-TRANSLATION
d_nonzero_invariants=8d*c3-9c2,8d*c1-7c7*c2
d_zero_cube_core=OPEN-SEPARATE-STRATUM
lower_rows=r1'=r2'=r3'=r4'=0,6r5'=j/s
cube_core_terminal=s-CONSTANT-OR-SINGLE-ROOT-POWER
regular_local_formal_survivor=true
common_ramified_puiseux_strata=OPEN
cube_mismatch_closed=false
degree_69_closed=false
keller_pair_found=false
jc2_inference=false
```

The PASS string is a regression marker. The mathematical evidence is the
exact Faber triangularity, direct one-form integration, target-gauge identity,
Laurent coefficient decomposition, divisor argument, and exact controls above.
