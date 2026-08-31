# GCD3 (6,9) lower-Pfaffian successor gate

## Exact invariant sheets and terminal-row exclusion in the aligned nontrivial-Kummer branch

**Producer verdict: PROVISIONALLY, THE FOUR LOWER ZERO ROWS INTEGRATE TO
FOUR EXACT INVARIANTS WHOSE REDUCED FIBER HAS ONLY A ZERO-BRACKET SHEET AND
AN ELLIPTIC SHEET. THE TERMINAL KELLER ROW EXCLUDES BOTH SHEETS IN THE
ALIGNED NONTRIVIAL-KUMMER BRANCH. THIS DOES NOT CLOSE THE CUBE-MISMATCH
BRANCH, ALL (6,9), OR JC2.**

- Snapshot: 2026-08-24
- Charged bank: 1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a
- Input: frozen first common-cubic gate, treated provisionally
- Field: algebraically closed characteristic-zero k
- Exact engines: SymPy 1.14.0 and Singular 4.4.1 over Q
- Boundary equations, generic rectangles, AWS, protected jobs: none
- Cube-core mismatch, general (6,9), JC2 inference: open

The calculation solves exactly the successor requested in Section 8 of the
first gate. Its scope is deliberately one branch:

~~~text
F=k(x),       L=F(s),       s^3=h in k[x],
L/F nontrivial cubic Kummer,       3 | deg(h),
~~~

after the aligned depression and the reviewed eight-high-row reduction.
The coefficient path is

~~~text
f=z^6+a4 z^4+a3 z^3+a2 z^2+a1 z+a0,
g=g0(a)+kappa(z^3+(a4/2)z+a3/2),                    (1)
~~~

where kappa is constant and g0 is reproduced exactly in the replay. If a
dot denotes x differentiation in L, define

~~~text
D=f_dot g_z-f_z g_dot.
~~~

The chain rule for z=s y+r gives J_(x,y)=sD. Thus the four lower zero rows
are [z^4]D=...=[z]D=0 and the terminal row is

~~~text
[z^0]D=j/s,             j in k*.                     (2)
~~~

No polynomial boundary value or common root is used below.

## 1. Four exact triangular first integrals

Let alpha_r be the coefficient one-form [z^r]D in
(da0,...,da4). Direct expansion gives the exact triangular corrections

~~~text
alpha4                                  =dI4,
alpha3                                  =dI3,
alpha2-(a4/2)alpha4                     =dI2,
alpha1-(a3/3)alpha4-(a4/3)alpha3       =dI1.          (3)
~~~

The replay checks every mixed partial and differentiates the recovered
potentials back to (3). For compact formulas put

~~~text
A=4a2-a4^2,                 B=2a1-a3a4,

e4=64a0a2-16a0a4^2+32a1^2-32a1a3a4-16a2^2a4
   -16a2a3^2+8a2a4^3+12a3^2a4^2-a4^5,

e3=64a0a1-32a0a3a4-32a1a2a4-16a1a3^2+8a1a4^3
   -16a2^2a3+24a2a3a4^2+8a3^3a4-5a3a4^4.
~~~

Then

~~~text
I4=9e4/128+3kappa A/4,       I3=9e3/128+3kappa B/2,
I2=N2/512,                   I1=-N1/128,              (4)
~~~

where

~~~text
N2=1152a0^2-768a0a2a4-576a0a3^2+192a0a4^3+1536a0kappa
   -384a1^2a4-1152a1a2a3+672a1a3a4^2-192a2^3
   +336a2^2a4^2+768a2a3^2a4-132a2a4^4-512a2a4kappa
   +72a3^4-288a3^2a4^3-384a3^2kappa+15a4^6
   +128a4^3kappa,

N1=96a0a1a4+192a0a2a3-96a0a3a4^2+96a1^2a3+144a1a2^2
   -120a1a2a4^2-120a1a3^2a4+21a1a4^4+64a1a4kappa
   -144a2^2a3a4-48a2a3^3+96a2a3a4^3+128a2a3kappa
   +48a3^3a4^2-15a3a4^5-64a3a4^2kappa.
~~~

The Kummer weights of (a0,a1,a2,a3,a4,kappa) are
(0,2,1,0,2,0) modulo 3, while

~~~text
wt(I4,I3,I2,I1)=(1,2,0,1).
~~~

All four I's are x-constants and the constant field of L is k. Nonzero
weights therefore force the exact invariant fiber

~~~text
I4=I3=I1=0,                 I2=mu in k.               (5)
~~~

## 2. Complete reduced invariant fiber

Singular computes the primary decomposition of (5) universally over
Q[a0,...,a4,kappa,mu]. Its radical is the intersection of exactly two
minimal primes PA and PB.

For

~~~text
w=4a0-a3^2,                 C=kappa^2+mu,

EB=384a2^3-432a2^2a4^2+144a2a4^4-15a4^6+1024C,
~~~

they are

~~~text
PA=(A, B, 9w^2+48kappa w-64mu),                      (6)

PB=(a3, a1, EB,
    48a0-12a2a4+3a4^3+32kappa).                      (7)
~~~

There is one associated prime

~~~text
PE=(C,A,B,12a0-3a3^2+8kappa),
~~~

and PA is contained in PE ideal-wise, so V(PE) is embedded inside V(PA).
It is not a third reduced or field-valued branch. The replay verifies

~~~text
rad(5)=PA intersect PB
~~~

rather than inferring completeness from sampled points.

A coefficient path gives a homomorphism to the field L, so its kernel is
prime and radical. A prime containing PA intersect PB contains PA or PB.
Consequently an irreducible generic source path lies on one reduced sheet;
it cannot switch between them by passing through their intersection.

## 3. Sheet PA: common powers and integration-constant deformations

Put d=w/4. Equation (6) makes d algebraic over k, hence d lies in k, and

~~~text
mu=9d^2/4+3kappa d.
~~~

With

~~~text
K=z^3+(a4/2)z+a3/2,
~~~

the entire sheet is

~~~text
f=K^2+d,              g=K^3+(kappa+3d/2)K.            (8)
~~~

For every moving K and constant d,kappa, direct differentiation gives
D=0. Thus (2) is impossible.

This keeps three notions distinct. The point d=kappa=0 is the pure
common-power family. The kappa K term is the essential high-row integration
constant. Nonzero d is a further lower-row constant deformation. They all
belong to the same reduced zero-bracket sheet, but none is silently
identified with the DS sheet.

## 4. Sheet PB: elliptic coordinate and terminal form

On PB,

~~~text
a3=a1=0,
a0=a2a4/4-a4^3/16-2kappa/3.
~~~

Define the Kummer-homogeneous coordinates

~~~text
X=8a2-2a4^2,            Y=3a4X,            C=kappa^2+mu.
~~~

They have weights wt(X)=1 and wt(Y)=wt(C)=0 and satisfy

~~~text
Y^2=3X^3+4096C.                                      (9)
~~~

Thus X=sR with R in k(x), whereas Y belongs to k(x). Pulling the terminal
row alpha0 back to PB before any division gives

~~~text
beta_a4=3(4a2-3a4^2)(4a2-a4^2)(4a2+a4^2)/2048,
beta_a2=3a4(4a2-a4^2)(4a2+a4^2)/512.                 (10)
~~~

In the function field of (9), (10) becomes

~~~text
beta=(7Y^2-12288C)dY/(147456X).                       (11)
~~~

The terminal Keller equation beta=j/s is therefore, for nonconstant Y,

~~~text
(7Y^2-12288C)Y'=147456jR,
3hR^3=Y^2-4096C.                                     (12)
~~~

Cubing and eliminating R is useful only after the constant-map case:

~~~text
3h(7Y^2-12288C)^3(Y')^3
 =(147456j)^3(Y^2-4096C).                             (13)
~~~

### 4.1 Constant Y

Before (13), if Y is constant, (10)--(11) give beta=0. If X is identically
zero this follows directly from the polynomial factors in (10); otherwise
it follows in the function field from dY=0. Both contradict j/s != 0.
No constant solution is introduced or lost by the cleared equation.

### 4.2 C nonzero: finite forbidden-value valuation

Assume C != 0 and Y is nonconstant. Let

~~~text
y_plus^2=y_minus^2=12288C/7,       y_plus=-y_minus.
~~~

A nonconstant rational map Y:P1 to P1 is surjective. The single source
point at infinity can map to at most one of these two finite values, so at
least one has a finite preimage p. At p, if
ord_p(Y-y_plus)=e >= 1, then

~~~text
ord_p(7Y^2-12288C)=e,        ord_p(Y')=e-1.
~~~

This includes every ramified preimage; Y'=0 only increases e. Moreover,

~~~text
Y(p)^2-4096C=-16384C/7 !=0,
X(p)^3=-16384C/21 !=0.                                (14)
~~~

Thus the chosen point is not a denominator, pole, or affine-chart escape.
Taking valuations in (13) forces

~~~text
ord_p(h)+3e+3(e-1)=0,
ord_p(h)=3-6e<0.                                      (15)
~~~

But h is a polynomial and p is finite. This contradiction excludes the
entire C != 0 sheet, including ramified/Y'=0 points.

## 5. Special fiber C=0

The polynomial equation, without division, factors exactly as

~~~text
EB=(3/4)X^2(X-3a4^2).                                 (16)
~~~

Because the source target is a field, (16) has two cases.

If X=0, then

~~~text
f=K0^2-2kappa/3,        g=K0^3,
K0=z^3+(a4/2)z,
~~~

which is already on PA and has zero bracket.

If X=3a4^2, put a4=4lambda. Then

~~~text
a2=10lambda^2,       a3=a1=0,
a0=6lambda^3-2kappa/3,       mu=-kappa^2,

f=f_lambda-2kappa/3,         g=g_lambda,              (17)
~~~

where

~~~text
f_lambda=z^6+4lambda z^4+10lambda^2 z^2+6lambda^3,

g_lambda=z^9+6lambda z^7+21lambda^2 z^5
         +35lambda^3 z^3+(63/2)lambda^4 z.
~~~

The constant subtraction in f has zero lambda and z derivatives. Exact
replay therefore gives, with the same orientation as D,

~~~text
(f_lambda-2kappa/3)_lambda (g_lambda)_z
 -(f_lambda-2kappa/3)_z (g_lambda)_lambda
 =567lambda^6.                                        (18)
~~~

The five-row determinant on (17) is

~~~text
det M=(3^18 7/32)lambda^20.                           (19)
~~~

For lambda != 0 there is no rank loss, and the terminal equation is exactly

~~~text
567s lambda^6 lambda'=j.                              (20)
~~~

The weight of lambda is two, so lambda=s^2q with q in k(x). Equation (20)
descends to

~~~text
189h^4q^6(2h'q+3hq')=j.                              (21)
~~~

The predecessor's exact finite-place and infinity classification, whose
arithmetic is rechecked here, says that every zero of h has

~~~text
e=ord(h)=3+7k,       ord(q)=-2-5k,       k>=1,
~~~

that h has exactly one distinct zero, and that the reviewed condition
3 | deg(h) forces k=3ell. Therefore e=3+21ell and h is a cube. This
contradicts the nontrivial Kummer hypothesis. The shifted DS sheet is empty
in the branch under review.

At lambda=0, (18) has zero bracket. If lambda is not identically zero, its
isolated zeros remain governed by the rational identity (20) and the same
valuation classification. Hence the rank-zero point in (19) is not an
unexamined source trajectory.

As a negative control, the unshifted static DS substitution has

~~~text
det M=(81/32)lambda^5(4kappa+63lambda^3)
      (8kappa^2-72kappa lambda^3+729lambda^6)^2,

I4=18kappa lambda^2.                                  (22)
~~~

On the Kummer invariant fiber and lambda != 0, (22) first forces kappa=0,
after which both extra determinant factors are nonzero. At lambda=0 the
bracket is zero. Thus none of the apparent extra rank factors discarded by
a generic matrix solve is a surviving invariant-fiber path. The correct
C=0 path is the shifted curve (17), not the unshifted ansatz.

## 6. Seven explicit no-loss dispatches

1. **Constant Y.** It is tested against beta=j/s before clearing or cubing;
   beta=0.
2. **Finite forbidden value.** A nonconstant Y attains at least one of the
   two forbidden finite values at a finite source point, and (14) makes X
   nonzero there.
3. **Ramification.** A ramification index e gives ord(Y')=e-1 and the
   stronger negative polynomial valuation (15); Y'=0 is no escape.
4. **Component switching.** The generic source map lands in the field L;
   its prime kernel selects PA or PB and cannot switch reduced components
   through their intersection.
5. **Embedded C=0 component.** PE contains PA ideal-wise, so its variety is
   inside the zero-bracket sheet and nilpotent structure cannot map
   nontrivially to a field.
6. **Denominator and rank loci.** The proof never inverts M. It derives
   (10) polynomially, handles X=0 in (16), uses the cleared identity only
   after constant Y, chooses a contradiction point with X != 0, treats
   lambda=0 separately, and checks every factor in (22).
7. **Shifted DS subtraction.** The constant -2kappa/3 changes neither (18)
   nor (20)--(21), so it cannot alter the nontrivial-Kummer valuation
   contradiction.

These dispatches are part of the claim, not genericity conventions.

## 7. Scope and next gate

Conditional on the frozen high-row normal form and reviewed history input,
the aligned nontrivial-Kummer (6,9) branch is provisionally empty. This
advances the first gate by deriving pure-component entry from all four lower
zero rows rather than assuming it.

The result uses no boundary reduction at all. In particular, it neither
repairs nor invokes the predecessor's chosen-root/full-cubic TYPE-FAIL.
It says nothing about:

- the cube-core constant mismatch delta != 0;
- an aligned cube branch for which nontrivial Kummer weights do not kill the
  other high-row integration constants;
- arbitrary degree-(6,9) Keller pairs outside the frozen normal-form
  hypotheses; or
- the plane Jacobian conjecture.

The smallest licensed successor is the cube-core high-row system, retaining
delta and every weight-unforced integration constant. A separate hostile
review should first attack the universal primary decomposition, the
terminal one-form orientation, the C != 0 forbidden-value valuation, and
the transfer of the predecessor's DS valuation lemma to (17).

## 8. Deterministic replay

Run without network:

~~~text
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_lower_pfaffian_successor_20260824/replay.py

Singular -q \
  cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing
~~~

Expected markers include:

~~~text
PASS-GCD3-69-LOWER-PFAFFIAN-SUCCESSOR
lower_zero_rows=FOUR-TRIANGULAR-FIRST-INTEGRALS
kummer_constants=I4=I3=I1=0,I2=mu
reduced_invariant_strata=ZERO-BRACKET-SHEET,ELLIPTIC-SHEET
constant_Y=TERMINAL-FAILS-BEFORE-CLEARING
forbidden_finite_value=X-NONZERO-NO-CHART-ESCAPE
ramified_preimage=h-order=3-6e<0
component_switching=PRIME-GENERIC-PATH-CANNOT-SWITCH
embedded_C_zero=NO-EXTRA-FIELD-VALUED-BRANCH
denominator_rank_strata=DISPATCHED-WITHOUT-MATRIX-INVERSION
shifted_ds_constant_subtraction=BRACKET-AND-VALUATIONS-UNCHANGED
aligned_noncube_69_branch=PROVISIONAL-EMPTY
cube_mismatch_branch=OPEN
jc2_inference=false

PASS-GCD3-69-LOWER-INVARIANT-DECOMPOSITION
minimal_reduced_components=ZERO-BRACKET-SHEET,ELLIPTIC-SHEET
embedded_C_zero_component=CONTAINED-IN-ZERO-BRACKET-SHEET
special_C_zero=ZERO-BRACKET-OR-SHIFTED-DS
~~~

The SymPy replay reconstructs g0, derives all five lower rows from the source
bracket, integrates and checks (3)--(5), verifies both sheets and the
terminal pullback, checks the DS bracket/determinants, and replays the local
valuation arithmetic. The independent Singular script computes the
universal primary decomposition and radical equality over Q. PASS strings
are regression markers, not theorem substitutes.
