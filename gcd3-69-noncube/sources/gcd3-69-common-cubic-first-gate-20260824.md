# GCD3 `(6,9)` first common-cubic gate

## Source-honest normalization, boundary provenance, and the exact constant-W scheme

**Producer verdict: `KUMMER NORMALIZATION SPLITS; FULL-CUBIC BOUNDARY
REDUCTION TYPE-FAILS WITHOUT ORBIT DEGREE THREE; THE NORMALIZED CONSTANT-W
SCHEME IS EXACTLY COMMON-CUBIC UNION ONE DAVENPORT--STOTHERS CURVE; THE PURE
DS SOURCE PATH IS ODE/BOUNDARY-EMPTY, BUT ENTRY FROM THE FULL (6,9) SYSTEM IS
NOT YET DERIVED`.**

- Snapshot: `2026-08-24`
- Charged bank: `6f2e49e63d74493910fa357a8adc82f0e40d219a`
- Field: an algebraically closed characteristic-zero constant field `k`,
  with the explicitly named rational/Kummer coefficient fields below
- Frozen input: the differently reviewed partial-`y` history stop
- Exact engines: SymPy `1.14.0` over `Q`; Singular `4.4.1` over `Q`
- Generic exponent rectangle, AWS, protected jobs: none
- Actual `(6,9)` Keller pair, nonlinear exclusion, JC2 inference: none

This gate corrects the first execution of Card 4 and supplies the first exact
calculation on all three common-cubic strata.

There are four conclusions, with deliberately different scopes.

1. A genuine `(6,9)` pair has an exact cubic-Kummer normalization, but it
   splits into an aligned branch and a cube-core constant-mismatch branch.
2. A chosen polynomial boundary root kills only its minimal-polynomial
   component.  Reducing both boundaries modulo the full squarefree cubic is
   invalid without a degree-three orbit hypothesis.
3. The complete normalized binary equation

   ```text
   2 f g_z-3 f_z g = constant,       deg(f,g)=(6,9)
   ```

   has exactly two reduced components: the common-cubic surface and the
   unique order-three Davenport--Stothers curve.  They meet only at the
   triple cubic.  Thus the linear cokernel obstruction is tangent-only, but
   its only nonlinear constant-W bypass is completely identified.
4. If the *full source coefficient path* lies purely on that DS curve, the
   Keller equation becomes `(lambda^7)'=j/(81s)`.  Exact valuations exclude
   the noncube Kummer case, and both polynomial boundaries exclude the
   remaining cube case.  This is a closed conditional branch, not yet a
   closure of `(6,9)`.  The eight top source rows do reduce exactly to five
   moving coefficients plus one essential constant `kappa`; the missing
   load-bearing step is solving the four lower Pfaffian rows and the terminal
   Keller row, including their boundary provenance.

No statement below treats a zero-Jacobian common-power family or an
Artinian jet as a Keller pair.

## 1. Exact top rows and the Kummer normalization split

Let a genuine pair have actual `y`-degrees `(6,9)`:

```text
P=a_6 y^6+a_5 y^5+...,       Q=b_9 y^9+b_8 y^8+...,
J(P,Q)=j in k*.
```

The reviewed top-row UFD statement, after nonzero constant target scalings,
is

```text
a_6=h^2,                     b_9=h^3,                  (1.1)
```

with `h in k[x]` nonzero.  Put `s^3=h` and work temporarily in

```text
L=k(x)(s).
```

Then write

```text
a_6=s^6,  b_9=s^9,  a_5=s^5 A,  b_8=s^8 B.            (1.2)
```

The coefficient of `y^13` in the Jacobian is exactly

```text
8a_6'b_8+9a_5'b_9-6a_6b_8'-5a_5b_9'
       =s^14(9A'-6B').                                 (1.3)
```

Thus

```text
delta=3A-2B in k.                                      (1.4)
```

Here the constant field of the finite algebraic extension `L/k(x)` is `k`.
Starting with `z_0=s y`, translate `z=z_0+r` with `r=A/6`.  The `z^5`
coefficient of `P` vanishes, while the `z^8` coefficient of `Q` becomes

```text
B-9r=B-3A/2=-delta/2.                                  (1.5)
```

There are two source-honest cases.

1. **Noncube core.**  If `h` is not a cube in `k(x)`, the cubic Kummer
   extension is nontrivial.  For `sigma(s)=omega s`, both `A=a_5/s^5` and
   `B=b_8/s^8` have weight one.  Hence `sigma(delta)=omega delta`.  But
   (1.4) puts `delta` in `k`, fixed by `sigma`; therefore `delta=0` and the
   two depressions align.
2. **Cube core.**  If `h` is a cube in `k(x)`, UFD makes it a constant times
   a polynomial cube, so `s` may be taken in `k[x]`.  There is no nontrivial
   Kummer action and (1.3) permits `delta!=0`.  This is a separate live
   normal-form branch.  The historical condition `3 | deg(h)` does not
   imply that `h` is a cube and does not eliminate the split.

Even in the aligned case, `z=s y+r` is an identity over `L`, not a polynomial
source automorphism.  Its exact boundary provenance is

```text
z|_(y=0)=r,       F(x,r)=P(x,0),       G(x,r)=Q(x,0).  (1.6)
```

The right sides are polynomials; they are not identically zero.

### 1.1 The eight top source rows integrate exactly

Continue only in the aligned nontrivial-Kummer branch.  Write the depressed
coefficient path as

```text
f=z^6+a_4z^4+a_3z^3+a_2z^2+a_1z+a_0,
g=z^9+b_7z^7+b_6z^6+...+b_1z+b_0.                    (1.7)
```

The chain rule gives

```text
J_(x,y)(P,Q)=s(f_xg_z-f_zg_x);                       (1.8)
```

all terms involving the `x`-derivative of `z=sy+r` cancelling in the
determinant.  The `z^12,...,z^5` rows of the source equation therefore
vanish.  They form a triangular first-order system.  Exact integration gives
eight constants `c_j in k`; for example

```text
b_7=3a_4/2+c_7,                 b_6=3a_3/2+c_6,
b_5=3(4a_2+a_4^2)/8+(7/6)a_4c_7+c_5,
b_4=3(2a_1+a_3a_4)/4+(7/6)a_3c_7+a_4c_6+c_4,         (1.9)
```

and the replay integrates and differentiates all four remaining formulas.
Under `sigma(s)=omega s`, a coefficient of `z^j` has weight `-j mod 3`;
the same is true of `c_j`.  Nontrivial Kummer descent consequently forces

```text
c_7=c_5=c_4=c_2=c_1=0.                               (1.10)
```

The weight-zero constant `c_6` multiplies all of `f` inside `g`, so the
constant target shear `g -> g-c_6f` removes it.  The target translation
removes `c_0`.  The only essential constant is `kappa=c_3`, and the complete
high-row normal form is

```text
g=g_0(a_0,...,a_4)
  +kappa(z^3+(a_4/2)z+a_3/2),                         (1.11)
```

where `g_0` is the eight-row zero-constant solution displayed in the replay
(and used in Section 5).  Thus the high source rows reduce to five moving
`a`-coefficients plus one constant `kappa`.  Four lower Pfaffian rows
(`z^4,...,z`) and the terminal row (`z^0=j/s`) remain.

This also shows exactly why Section 5 is an entry condition rather than an
automatic consequence of normalization.  On the common-cubic component

```text
f=K^2,                    g=K^3+kappa K.               (1.12)
```

The `kappa K` deformation is a genuine source integration constant and does
not belong to the pure constant-W classification unless the remaining rows
force `kappa=0` (or otherwise absorb it).  No such conclusion is asserted
here.  If the *complete source path* nevertheless stays on (1.12), both
coordinates are polynomials in the same moving `K`, so its source Jacobian
is identically zero.  Hence that persistent common-component path cannot be
Keller.  What is not licensed is promoting one associated-graded
common-cubic point to persistence of (1.12) through the lower filtration.

## 2. Binary common-cubic structure and exact discriminant strata

Suppose a separately licensed weighted leading calculation produces monic
homogeneous binary forms `F_0,G_0` of degrees six and nine with zero binary
Jacobian.  Euler gives

```text
t J_(t,z)(F_0,G_0)=6F_0 (G_0)_z-9G_0(F_0)_z=0.
```

Unique factorization, monicity, and `gcd(6,9)=3` give

```text
F_0=K^2,                    G_0=K^3                    (2.1)
```

for a monic homogeneous cubic `K`.  If the aligned form has no `z^5` or
`z^8` row, the `z^2t` coefficient of `K` vanishes.  Thus, without dividing
by the discriminant,

```text
K=z^3+u t^2 z+v t^3,          Delta=-4u^3-27v^2.       (2.2)
```

The exact geometric split is

```text
Delta != 0                         three distinct roots;
Delta = 0, (u,v)!=(0,0)            (z-a t)^2(z+2a t),
                                    u=-3a^2, v=2a^3;
u=v=0                              z^3.                (2.3)
```

Equation (2.1) is a binary-leading identity.  It is not a claim that the
global polynomial pair is `(K^2,K^3)`, whose Jacobian is zero.

## 3. Boundary provenance: the full-cubic reduction type-fails

Let `K_0` be the coefficient field of `K(1,z)` and let a boundary root `rho`
lie in an algebraic extension.  For `H in K_0[z]`,

```text
H(rho)=0  iff  m_rho divides H,                         (3.1)
```

where `m_rho` is the minimal polynomial of `rho` over `K_0`.  Therefore two
chosen-root boundary equations imply reduction modulo `m_rho`, not
automatically modulo `K`.

Full reduction modulo `K` is valid if `m_rho=K`, for example when `K` is
irreducible of degree three or a separate field-of-definition theorem makes
the root orbit have degree three.  It is not implied by `Delta!=0`:

| squarefree factorization over `K_0` | possible orbit degree of `rho` |
|---|---:|
| irreducible cubic | `3` |
| linear times irreducible quadratic | `1` or `2` |
| three linear factors | `1` |

After passing to a splitting field the etale cubic algebra has three
idempotents, but a boundary section already defined over `K_0` occupies one
idempotent.  Descent does not manufacture the other two vanishings.

The exact depressed split control is

```text
K=z(z-t)(z+t)=z^3-t^2z,       rho=0,
phi=z t^5,                    psi=(3/2)K phi.           (3.2)
```

For `F_epsilon=K^2+epsilon phi` and
`G_epsilon=K^3+epsilon psi`, both first-order boundaries vanish at `rho=0`.
At the three roots `(0,1,-1)` of `K(1,z)`, however,

```text
phi=(0,1,-1).                                          (3.3)
```

Thus `phi` is divisible by the selected linear factor, not by `K`.  This is
an exact `TYPE-FAIL` of a full-cubic *boundary* reduction.  It does not
refute a full-cubic conclusion derived from extra Jacobian rows.

## 4. Linear and quadratic component controls

Use the binary/source orientation

```text
{A,B}=A_t B_z-A_z B_t.
```

For normalized perturbations `phi,psi` of degrees six and nine,

```text
F_epsilon=K^2+epsilon phi,
G_epsilon=K^3+epsilon psi,
```

the coefficient of `epsilon` is

```text
L_K(phi,psi)
 = {phi,K^3}+{K^2,psi}
 = K {K,2psi-3Kphi}.                                   (4.1)
```

Every linearized bracket is zero in `K_0[z]/(K)`.  A requested nonzero
constant `c` has residues `(c,c,c)`, with

```text
Res_z(K(1,z),c)=c^3.                                   (4.2)
```

Thus the constant row is a nonzero first-order cokernel class.  Quotienting
source/target/`(u,v)` gauges cannot enlarge the image.  This is only a
tangent obstruction; Section 5 gives its nonlinear bypass.

For a zero first-order bracket, the normalized tangent conditions give

```text
psi=(3/2)K phi.                                        (4.3)
```

The quadratic bracket is

```text
q_2={phi,psi}=(3/2)phi{phi,K}
             =9phi^2K_z                    modulo K.  (4.4)
```

On `Delta!=0`, `K_0[z]/(K)` is reduced and `K_z` is a unit.  Therefore, if
the right-hand-side constant and both boundary values are still absent at
this filtration order,

```text
q_2=0 modulo K  iff  K divides phi.                    (4.5)
```

For

```text
phi=p_4z^4+p_3z^3+p_2z^2+p_1z+p_0,
K=z^3+uz+v,
```

this is the exact linear system

```text
p_2-u p_4=0,
p_1-v p_4-u p_3=0,
p_0-v p_3=0.                                           (4.6)
```

It leaves only the two common-cubic tangent directions.  On the split
control (3.2), the quadratic residues are `(0,18,18)`.

This conclusion is explicitly RHS-filtration-sensitive.  If the constant
row first appears at this order, the equation is `9phi^2K_z=c mod K`; if a
boundary polynomial contributes at this order, `phi(rho)` need not vanish.
The Davenport--Stothers curve below shows exactly such delayed behavior:
its first boundary term appears at order `lambda^3` and its constant bracket
at order `lambda^7`.

The singular quotient is nonreduced, so (4.4) only forces
`rad(K)|phi`.  The replay freezes exact non-common-cubic two-jets:

```text
K=(z-t)^2(z+2t),  rho=-2t,
phi=(z-t)(z+2t)t^4,
psi_1=(3/2)Kphi,  psi_2=(3/8)t^8(z+2t),
{K^2+e phi,K^3+e psi_1+e^2 psi_2}
   =-(9/8)e^3t^11(z+2t)(5t+4z);                       (4.7)

K=z^3,  rho=0,
phi=z^2t^4,
psi_1=(3/2)Kphi,  psi_2=(3/8)zt^8,
{K^2+e phi,K^3+e psi_1+e^2 psi_2}
   =-(9/2)e^3t^11z^2.                                 (4.8)
```

They survive over `k[e]/(e^3)` and satisfy the selected-root boundaries.
They are Artinian controls, not characteristic-zero Keller pairs.

## 5. Complete normalized constant-W scheme

Now solve the nonlinear binary equation exactly.  Put

```text
f=z^6+a_4z^4+a_3z^3+a_2z^2+a_1z+a_0,
g=z^9+b_7z^7+b_6z^6+...+b_1z+b_0,                     (5.1)
W=2fg_z-3f_zg.
```

The `z^12,...,z^5` rows of `W=constant` solve `b_7,...,b_0`
uniquely.  The first four are

```text
b_7=3a_4/2,
b_6=3a_3/2,
b_5=3(4a_2+a_4^2)/8,
b_4=3(2a_1+a_3a_4)/4,                                 (5.2)
```

and the replay derives the remaining four rather than importing them.  The
`z^4,z^3,z^2,z` rows give four exact residual equations in
`a_0,...,a_4`.  Independent Singular primary decomposition gives

```text
rad(I_residual)=P_common intersect P_DS,               (5.3)

P_common=(4a_2-a_4^2, 2a_1-a_3a_4, 4a_0-a_3^2),

P_DS=(a_3,a_1,8a_2-5a_4^2,20a_0-3a_2a_4).             (5.4)
```

There are exactly two prime radicals.  The common component has dimension
two and is

```text
f=(z^3+uz+v)^2,          g=(z^3+uz+v)^3,
a_4=2u, a_3=2v.                                         (5.5)
```

The DS component has dimension one.  The two components meet only at

```text
a_0=a_1=a_2=a_3=a_4=0,       K=z^3.                    (5.6)
```

In particular, no nonlinear constant-W branch meets a squarefree or
double-root point of the common-cubic surface.  The common component is
nonreduced in the original residual ideal, consistent with the tangent and
two-jet controls of Section 4; (5.3) is a set-theoretic classification, not a
claim that its scheme is reduced.

Parameterize the second component by `a_4=4lambda`.  Then

```text
f_lambda=z^6+4lambda z^4+10lambda^2z^2+6lambda^3,

g_lambda=z^9+6lambda z^7+21lambda^2z^5+35lambda^3z^3
         +(63/2)lambda^4z,                             (5.7)

f_lambda^3-g_lambda^2
 =(27/4)lambda^7(4z^4+13lambda z^2+32lambda^2),

2f_lambda(g_lambda)_z-3(f_lambda)_zg_lambda
 =378lambda^7.                                         (5.8)
```

At `lambda=1` this is the order-three example of Birch reproduced by
Shioda.  For `lambda!=0`,

```text
Res_z(f_lambda,g_lambda)
  =(3^9 7^2/2^5)lambda^27 !=0.                         (5.9)
```

Thus the nonlinear bypass is coprime and has no persistent common boundary
root.  It approaches only the triple cubic.  Under the natural scaling
`lambda=epsilon^2`, its constant bracket first appears at order
`epsilon^14`.

### 5.1 Davenport--Stothers identity and primary-source check

For `H=f^3-g^2`, direct differentiation gives

```text
fH'-3f'H=-(2fg'-3f'g)g.                               (5.10)
```

Hence a nonzero constant Wronskian at degrees `(6,9)` is exactly an extremal
order-three Davenport--Stothers pair with `deg(H)=4`; conversely an extremal
pair has nonzero constant Wronskian.  This is the equality case of the
Davenport lower bound.

Primary sources inspected:

- Tetsuji Shioda, *Elliptic Surfaces and Davenport--Stothers Triples*,
  `Comment. Math. Univ. St. Pauli` 54 (2005), 49--68,
  [DOI 10.14992/00008689](https://doi.org/10.14992/00008689).  Section 1
  records `St(3)=1`; Section 5 gives exactly
  (5.7) at `lambda=1`.  Official Rikkyo PDF SHA-256:
  `467701925109586976ca8f89ec614ee95c5ad740084b969a93ba3795b0cdb740`.
- Umberto Zannier, *On Davenport's bound for the degree of f^3-g^2 and
  Riemann's Existence Theorem*, `Acta Arith.` 71 (1995), 107--137,
  [DOI 10.4064/AA-71-2-107-137](https://doi.org/10.4064/AA-71-2-107-137).
  The paper proves existence of extremal examples
  in every order.  EuDML-linked ICM journal-archive PDF SHA-256:
  `b629733a8c7c64007110e06e5ffc73212eb4b87bcbd6dbcf5416cac485c51a2d`.
- Shioda attributes existence, finiteness, and enumeration to W. W. Stothers,
  *Polynomial Identities and Hauptmoduln*, `Q. J. Math.` 32 (1981), 349--370,
  [DOI 10.1093/qmath/32.3.349](https://doi.org/10.1093/qmath/32.3.349).
  That paywalled paper is not consumed for the
  new algebra: (5.3)--(5.9) are independently exact.

The literature supplies history and the explicit control.  It is not used
as evidence for the primary decomposition.

## 6. The source boundary persists only at leading order

The DS degeneration is the exact negative control against treating the
leading common root as a full filtered root.  At `rho=0`,

```text
f_lambda(0)=6lambda^3,       g_lambda(0)=0,             (6.1)
```

while the constant Wronskian begins at `lambda^7`.  Thus both leading forms
vanish at the triple root when `lambda=0`, but one boundary turns on four
orders before the constant row.

This matches the source provenance (1.6): at a finite pole or polynomial
infinity, multiplying by the leading weight makes a regular polynomial
boundary vanish in the associated graded, but its first regular term is
allowed later.  Therefore the source supplies a common root at the leading
binary layer only.  It does **not** supply a common root through the whole
filtered deformation without an additional order statement.

At a fixed nonzero `lambda`, a persistent common boundary root is impossible
also directly: evaluating `W` at `f(rho)=g(rho)=0` gives `W(rho)=0`, contrary
to (5.8), and (5.9) gives the symmetric certificate.

## 7. Conditional closure of a pure DS source path

This section has one explicit load-bearing hypothesis:

> after the aligned Kummer depression, the complete normalized coefficient
> path is exactly `(f_lambda(x),g_lambda(x))` of (5.7), with all lower-weight
> integration constants absent.

That entry hypothesis is not derived in this gate.  Conditional on it, the
branch closes exactly.

Give `z` weight one and `lambda` weight two.  Weighted Euler gives

```text
2lambda J_(lambda,z)(f_lambda,g_lambda)
 =3(2f_lambda(g_lambda)_z-3(f_lambda)_zg_lambda),

J_(lambda,z)=567lambda^6.                              (7.1)
```

For `z=s y+r`, the chain rule, including the `x`-dependence of `s,r`, is

```text
J_(x,y)=s J_(x,z).                                     (7.2)
```

The terms containing `z_x` cancel in the determinant.  Therefore a pure DS
path satisfies the Keller equation only if

```text
567s lambda^6 lambda'=j,
(lambda^7)'=j/(81s).                                  (7.3)
```

The parameter `lambda` has Kummer weight two.  Write

```text
lambda=s^2q,                 q in k(x),  s^3=h.
```

Equation (7.3) is equivalent to

```text
189h^4q^6(2h'q+3hq')=j.                               (7.4)
```

### 7.1 Exact valuation classification

At a finite point put `e=v(h)>=0`, `n=v(q)`.  If `e=0`, (7.4) forces
`n=0`.  If `e>0` and `2e+3n!=0`, constant valuation forces

```text
5e+7n-1=0,
e=3+7k,       n=-2-5k,       2e+3n=-k,                (7.5)
```

with `k>=1`.  The cancelled case `2e+3n=0` has strictly positive valuation
and is impossible.  Hence the divisor of `q` is supported exactly on the
zeros of `h`.

If `h` has no zero, it is constant.  The finite-place calculation then makes
`q` a nonzero constant, and the left side of (7.4) is zero, a contradiction.
Thus `h` has `r>=1` distinct zeros.  Summing (7.5) gives at infinity

```text
deg( h^4q^6(2h'q+3hq') )=r-1,                         (7.6)
```

and its leading coefficient is nonzero because it contains
`-sum k_i`.  Constancy forces `r=1`.  Thus

```text
h=C(x-a)^(3+7k).                                       (7.7)
```

The reviewed historical branch has `3 | deg(h)`, so `3|k`.  Write
`k=3ell`, `ell>=1`.  Then

```text
h=C(x-a)^(3+21ell),
q=D(x-a)^(-2-15ell),
lambda=A(x-a)^(-ell).                                 (7.8)
```

In particular, every rational solution of the pure-DS ODE lies in the
**cube** core case.  There is no noncube/Kummer solution.  The smallest
control is `h=x^24,s=x^8,q=x^-17,lambda=x^-1`, for which the source Jacobian
factor is the nonzero constant `-567` after scalar choice.

### 7.2 Both polynomial boundaries kill the cube controls

Let `t=x-a`; then `v(lambda)=-ell<0`.  For a boundary value
`z=r(x)` with integer valuation `nu`, the four valuations in
`f_lambda(r)` are

```text
6nu,  -ell+4nu,  -2ell+2nu,  -3ell.                   (7.9)
```

If `2nu!=-ell`, the minimum is unique, so `f_lambda(r)` has a pole.  If
`2nu=-ell`, all terms balance.  After extracting the common power, regularity
of the first boundary forces the leading scaled value `xi` to satisfy
`f_1(xi)=0`.  The same calculation for `g_lambda(r)` forces
`g_1(xi)=0`.  This contradicts the nonzero resultant (5.9).

Therefore no rational pure-DS solution of (7.3) has both source boundary
values in `k[x]`.  Under the stated entry hypothesis, the DS branch is empty.

This does not close the cube-mismatch branch `delta!=0`, nor a trajectory
with lower-weight integration constants that is not purely (5.7).

## 8. Exact outcome and next licensed gate

The following are established at their stated scopes:

1. exact Kummer-aligned versus cube-mismatch normalization;
2. binary common-cubic structure and squarefree/double/triple split;
3. `TYPE-FAIL` of full-cubic boundary reduction without orbit degree three;
4. tangent cokernel and filtration-sensitive quadratic residues;
5. complete reduced classification of the normalized constant-W scheme;
6. the unique nonlinear DS bypass, meeting the common surface only at the
   triple cubic and turning on at order `lambda^7`; and
7. exact integration of the eight high source rows to five moving
   coefficients plus the essential constant `kappa`, with
   `f=K^2,g=K^3+kappa K` and zero source bracket on any path persisting in
   the common component; and
8. conditional exclusion of a pure DS source path by the exact Kummer ODE
   plus both polynomial boundaries.

The gate does **not** establish that an arbitrary aligned `(6,9)` trajectory
lies on the pure DS curve.  It does not solve the four lower Pfaffian rows
and terminal Keller row, prove that the rational depression data are
polynomial, close `delta!=0`, construct or exclude a Keller pair, or decide
JC2.

The smallest source-honest successor is now sharply defined:

1. solve the four lower Pfaffian rows and terminal row of the exact
   five-variable-plus-`kappa` normal form (1.11), testing first whether they
   force `kappa=0` or admit a smaller differential invariant;
2. at a finite pole, retain the chosen minimal factor `m_rho`, not the full
   cubic, and compute whether the associated graded arc lands on the common
   primary component, the DS prime, or an integration-constant deformation;
3. if it lands on the DS prime, apply Section 7; if it lands on the common
   primary component, compute the first nonzero Kuranishi row separately on
   the squarefree/double strata; and
4. run the cube mismatch `delta!=0` as an independent branch.

A generic coefficient rectangle and AWS are not licensed.

## 9. Deterministic replay

Run, without network:

```text
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_common_cubic_first_gate_20260824/replay.py

Singular -q \
  cases/gcd3_69_common_cubic_first_gate_20260824/verify_constant_w_scheme.sing
```

Expected terminal lines include

```text
PASS-GCD3-69-FIRST-COMMON-CUBIC-GATE
normalization=KUMMER-ALIGNED-OR-CUBE-MISMATCH
high_row_reduction=FIVE-COEFFICIENTS-PLUS-KAPPA
full_cubic_boundary_reduction=TYPE-FAIL-WITHOUT-ORBIT-DEGREE-3
linear_constant_row=TANGENT-ONLY-NONZERO-COKERNEL-CLASS
nonlinear_constant_w_bypass=UNIQUE-ORDER3-DS-CURVE
ds_first_constant_order=lambda^7=epsilon^14
pure_ds_source_ode=(lambda^7)'=j/(81s)
pure_ds_noncube_branch=VALUATION-EMPTY
pure_ds_cube_branch=POLYNOMIAL-BOUNDARY-EMPTY
nonlinear_69_closure=false
keller_pair_found=false
jc2_inference=false

PASS-GCD3-69-CONSTANT-W-SCHEME
radical_components=COMMON-CUBIC-SURFACE,UNIQUE-DS-CURVE
component_intersection=TRIPLE-CUBIC-ORIGIN-ONLY
ds_constant_w=(189/8192)*a4^7
ds_persistent_common_root=false
```

The Python replay independently integrates and differentiates the eight high
source rows, derives the high Wronskian rows, verifies the Kummer mismatch
and discriminant split, constructs the orbit-degree and jet controls, checks
Birch/DS, weighted Euler, the source ODE, and its local valuation arithmetic.
The Singular replay reconstructs the exact residual
ideal, computes its primary decomposition, checks both prime radicals and
their intersection, and independently verifies the DS difference,
Wronskian, and resultant.  PASS strings are regression markers, not theorem
substitutes.

The accompanying manifest freezes every payload against the charged bank.
