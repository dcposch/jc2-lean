#!/usr/bin/env python3
"""Exact symbolic residual of the `(6,8)` cubic face `e=0, 3D=A*B`."""

import os
import platform
import socket
import sympy as s

job_tag = os.environ.get("JC2_JOB_TAG", "")
if platform.system() != "Linux":
    raise SystemExit("refusing non-Linux CAS run")
if not job_tag:
    raise SystemExit("JC2_JOB_TAG is required")
print(f"host={socket.gethostname()} job_tag={job_tag}")

A, B, c, d, e = s.symbols("A B c d e")
Ap, Bp, cp, dp, ep = s.symbols("Ap Bp cp dp ep")
N, G = s.symbols("N G")

D = A * B / 3 + d
Dp = (Ap * B + A * Bp) / 3 + dp

I4 = -s.Rational(8, 27) * B**3 - s.Rational(8, 9) * A * B * c
I4 += s.Rational(8, 3) * B * e + s.Rational(8, 3) * D * c

I3 = s.Rational(4, 9) * A**2 * B**2
I3 -= s.Rational(16, 9) * A * B * D
I3 -= s.Rational(8, 9) * B**2 * c
I3 += s.Rational(4, 3) * D**2 + s.Rational(8, 3) * c * e

row2 = -s.Rational(4, 27) * (
    2 * A**2 * B * cp + 2 * A**2 * Bp * c + A * Ap * B * c
    - 6 * A * B**2 * Bp - 6 * A * D * cp - 6 * A * Dp * c
    - 3 * Ap * B**3 + 9 * Ap * B * e + 3 * Ap * D * c
    + 6 * B**2 * Dp + 12 * B * Bp * D + 12 * B * c * cp
    + 6 * Bp * c**2 - 18 * D * ep - 18 * Dp * e
)

row1 = -s.Rational(4, 81) * (
    -4 * A**3 * B * Bp - 3 * A**2 * Ap * B**2
    + 6 * A**2 * B * Dp + 6 * A**2 * Bp * D
    - 3 * A * B**2 * cp - 12 * A * B * Bp * c
    - 18 * A * c * ep - 18 * A * cp * e - 9 * Ap * B**2 * c
    + 9 * Ap * D**2 - 9 * B**2 * ep + 9 * B * D * cp
    + 9 * B * Dp * c + 27 * Bp * D * c + 18 * c**2 * cp
    - 54 * e * ep
)

row0 = s.Rational(4, 81) * (
    A**2 * Ap * B * c - 3 * A * Ap * D * c
    + 6 * A * B * Bp * D + 3 * A * B * c * cp
    + 3 * Ap * B**2 * D + 3 * Ap * B * c**2 - 9 * Ap * D * e
    - 9 * B * D * Dp + 9 * B * c * ep - 9 * Bp * D**2
    - 9 * D * c * cp
)

for name, expr in (("I4", I4), ("I3", I3), ("row2", row2),
                   ("row1", row1), ("row0", row0)):
    print(f"{name} residual =")
    print(s.factor(s.expand(expr)))
    print()

# Verify the first-face formulas vanish identically on d=e=0.
F4 = A * B * c - 3 * B * e - 3 * c * D
F3 = A**2 * B**2 - 4 * A * B * D + 6 * c * e + 3 * D**2
F2 = 2*A**2*B*c*G - 8*A**2*B*c*N - 9*A*B*e*N
F2 += -6*A*c*D*G + 24*A*c*D*N - 18*D*e*G + 99*D*e*N
F1 = 2*A**3*B**2*G - 9*A**3*B**2*N - 6*A**2*B*D*G
F1 += 24*A**2*B*D*N + 18*A*c*e*G - 90*A*c*e*N
F1 += 9*A*D**2*N + 27*e**2*G - 162*e**2*N
F0 = A**2*B*c - 3*A*c*D - 9*D*e
for name, expr in (("F4", F4), ("F3", F3), ("F2", F2),
                   ("F1", F1), ("F0", F0)):
    assert s.expand(expr.subs({d: 0, e: 0})) == 0, name


def gap_support(expr):
    """Gap linear forms for a residual homogeneous equation."""
    generators = (A, B, c, d, e, Ap, Bp, cp, dp, ep)
    forms = set()
    for monomial, coefficient in s.Poly(s.expand(expr), *generators).terms():
        if coefficient == 0:
            continue
        _, b, cc, dd, ee, _, bp, cpp, ddp, eep = monomial
        forms.add((b + bp, cc + cpp, dd + ddp, ee + eep))
    return sorted(forms)


supports = [gap_support(expr) for expr in (I4, I3, row2, row1, row0)]
print("residual gap supports:")
for name, forms in zip(("I4", "I3", "row2", "row1", "row0"), supports):
    print(name, forms)


def deficit(form, gaps):
    return sum(a * b for a, b in zip(form, gaps))


print("\nNECESSARY TROPICAL PATTERNS IN 3g<n")
for g in range(1, 6):
    cap = 6 * g + 2
    survivors = set()
    for u in range(g, cap + 1):
        for v in range(g, cap + 1):
            if min(u, v) != g:
                continue
            for w in range(g + 1, cap + 1):
                for z in range(g + 1, cap + 1):
                    gaps = (u, v, w, z)
                    if all(sum(deficit(form, gaps) == min(
                            deficit(other, gaps) for other in forms)
                               for form in forms) >= 2
                           for forms in supports):
                        survivors.add(gaps)
    normalized = sorted(tuple(s.Rational(x, g) for x in item)
                        for item in survivors)
    print(f"g={g}: {len(normalized)} patterns")
    print(normalized[:80])


H, Z = s.symbols("H Z")


def leading(expr, numeric_gaps, symbolic_gaps):
    """Leading coefficient at a representative tropical point."""
    generators = (A, B, c, d, e, Ap, Bp, cp, dp, ep)
    terms = s.Poly(s.expand(expr), *generators).terms()
    weighted = []
    for monomial, coefficient in terms:
        _, b, cc, dd, ee, _, bp, cpp, ddp, eep = monomial
        form = (b + bp, cc + cpp, dd + ddp, ee + eep)
        weighted.append((deficit(form, numeric_gaps), monomial, coefficient))
    floor = min(item[0] for item in weighted)
    selected = sum(coefficient * s.prod(x**power for x, power in
        zip(generators, monomial))
        for value, monomial, coefficient in weighted if value == floor)
    u, v, w, z = symbolic_gaps
    derivative_values = {
        Ap: 2 * N * A,
        Bp: (3 * N - u) * B,
        cp: (4 * N - v) * c,
        dp: (5 * N - w) * d,
        ep: (6 * N - z) * e,
    }
    return floor, s.factor(s.expand(selected.subs(derivative_values)))


cases = (
    ("g<h<2g", (3, 3, 4, 4), (G, G, H, H)),
    ("w=2g<z", (3, 3, 6, 7), (G, G, 2*G, Z)),
    ("w=z=2g", (3, 3, 6, 6), (G, G, 2*G, 2*G)),
    ("z=2g<w", (3, 3, 7, 6), (G, G, H, 2*G)),
)
for case_name, numeric_gaps, symbolic_gaps in cases:
    print(f"\nLEADING SYSTEM: {case_name}")
    for equation_name, expr in zip(
            ("I4", "I3", "row2", "row1", "row0"),
            (I4, I3, row2, row1, row0)):
        floor, result = leading(expr, numeric_gaps, symbolic_gaps)
        print(equation_name, "deficit", floor, ":", result)
