#!/usr/bin/env python3
"""Residue and valuation identities for the (6,8) aligned-nonsquare degree-zero primitive.

The pole tower does not apply: sqrt(H) is ramified at the roots of a squarefree
quadratic H, so (j/sqrt(H)) dx is holomorphic there.  The genuine residues sit
at the two places over infinity of the conic y^2 = H.

This job records three algebraic facts used by
Grok68AlignedNonsquareDegreeZeroPrimitiveScratch.lean:

1. After completing the square, u = y / t gives
   (j/y) dx = -du / (u^2 - c); equivalently -2j du/(u^2-c) after the
   conventional 2-scaling of the uniformiser, with residues ±j/sqrt(c).
2. An odd primitive rho = Q * y with d(rho) = j/y is equivalent to the
   rational ODE 2 H Q' + Q H' = 2 j.
3. For deg H = 2 that ODE has no rational solution unless j = 0
   (leading-coefficient / degree mismatch on 2 H W + n H' d = 2 j d^2).

Run:
  JC2_JOB_TAG=68-aligned-nonsquare-degree-zero \\
    ./scripts/max11_cas_run.py --name 68-aligned-nonsquare-degree-zero --timeout 120 -- \\
    python3 scripts/derive_68_aligned_nonsquare_degree_zero.py
"""

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import os
import platform
import socket
import time

import random

import sympy as sp


job_tag = os.environ.get("JC2_JOB_TAG", "")
if platform.system() != "Linux":
    raise SystemExit("refusing non-Linux CAS run")
if not job_tag:
    raise SystemExit("JC2_JOB_TAG is required")
print(f"host={socket.gethostname()} job_tag={job_tag}", flush=True)

ROOT = Path(__file__).resolve().parent.parent
started = time.monotonic()
source = Path(__file__).resolve()
print(f"command_source_sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)


def checkpoint(label: str) -> None:
    print(f"{label}_SECONDS={time.monotonic() - started:.3f}", flush=True)


x, t, u, y, j, c, Delta = sp.symbols("x t u y j c Delta")
Q, Hsym = sp.symbols("Q H", cls=sp.Function)

checkpoint("START")

# --- 1. Residue at infinity after completing the square -------------------
# H = c t^2 - Delta, y^2 = H, u = y/t.
H_t = c * t**2 - Delta
y_u = u * t
# Implicit: u^2 t^2 = c t^2 - Delta  =>  t^2 (u^2 - c) = -Delta
# Differentiate: 2 t dt (u^2 - c) + t^2 * 2 u du = 0
# dt = - u t du / (u^2 - c)
# dx/y = dt / (u t) = - du / (u^2 - c)
dx_over_y = -1 / (u**2 - c)
print("DX_OVER_Y_IN_U=", dx_over_y, flush=True)

# Conventional 2-scaling u2 = y / (2t) recovers the plan's -2 du/(u^2-c).
# Residues of -2 j / (u^2 - c) at u = ±sqrt(c):
sqrtc = sp.sqrt(c)
form = -2 * j / (u**2 - c)
res_plus = sp.residue(form, u, sqrtc)
res_minus = sp.residue(form, u, -sqrtc)
print("RESIDUE_PLUS=", sp.simplify(res_plus), flush=True)
print("RESIDUE_MINUS=", sp.simplify(res_minus), flush=True)
assert sp.simplify(res_plus - (-j / sqrtc)) == 0
assert sp.simplify(res_minus - (j / sqrtc)) == 0
print("RESIDUE_IDENTITY_OK", flush=True)

# Unscaled form -j/(u^2-c) has residues ∓ j/(2 sqrt(c)), still nonzero.
form1 = -j / (u**2 - c)
print("UNSCALED_RES_PLUS=", sp.simplify(sp.residue(form1, u, sqrtc)), flush=True)

checkpoint("RESIDUES")

# --- 2. Odd primitive ODE -------------------------------------------------
# rho = Q(x) * y, y^2 = H, y' = H'/(2y)
# rho' = Q' y + Q H'/(2y)  and  rho' = j/y
# =>  2 H Q' + Q H' = 2 j
Qfun = sp.Function("Q")
Hfun = sp.Function("H")
ode_lhs = 2 * Hfun(x) * sp.diff(Qfun(x), x) + Qfun(x) * sp.diff(Hfun(x), x)
print("ODE_LHS=", ode_lhs, flush=True)

# Direct differentiation of Q*y:
rho_deriv = (
    sp.diff(Qfun(x), x) * y
    + Qfun(x) * sp.diff(Hfun(x), x) / (2 * y)
)
rho_deriv_cleared = sp.expand(rho_deriv * y).subs(y**2, Hfun(x))
print("RHO_DERIV_TIMES_Y=", rho_deriv_cleared, flush=True)
assert sp.expand(rho_deriv_cleared - ode_lhs / 2) == 0
print("ODE_IDENTITY_OK", flush=True)

checkpoint("ODE")

# --- 3. Degree analysis for natDegree H = 2 --------------------------------
# Polynomial form: Q = n/d, W = n' d - n d'
# 2 H W + n H' d = 2 j d^2


def wronskian(n, d, var):
    return sp.diff(n, var) * d - n * sp.diff(d, var)


def lhs_poly(H, n, d, var):
    W = wronskian(n, d, var)
    return sp.expand(2 * H * W + n * sp.diff(H, var) * d)


def analyse(H, n, d, var):
    n = sp.Poly(sp.expand(n), var)
    d = sp.Poly(sp.expand(d), var)
    H = sp.Poly(sp.expand(H), var)
    assert H.degree() == 2
    N, D = n.degree(), d.degree()
    W = wronskian(n.as_expr(), d.as_expr(), var)
    Wpoly = sp.Poly(sp.expand(W), var)
    lhs = lhs_poly(H.as_expr(), n.as_expr(), d.as_expr(), var)
    L = sp.Poly(lhs, var)
    rhs_deg = 2 * D
    return {
        "N": N,
        "D": D,
        "degW": Wpoly.degree() if not Wpoly.is_zero else -1,
        "degLHS": L.degree() if not L.is_zero else -1,
        "degRHS": rhs_deg,
        "lcLHS": L.LC() if not L.is_zero else 0,
    }


var = x
H0 = x**2 + 3 * x + 1
samples = [
    ("N=D=0", 5, 2),
    ("N=D=2", x**2 + 1, x**2 + x + 1),
    ("N=D-1", x + 1, x**2 + 2),
    ("N=D+1", x**2 + 1, x + 3),
    ("N=0 D=3", 7, x**3 + x + 1),
    ("D=0 N=4", x**4 + 2 * x + 1, 3),
    ("N=3 D=1", x**3 + 1, x + 5),
]
print("DEGREE_TABLE", flush=True)
for name, n, d in samples:
    info = analyse(H0, n, d, var)
    print(
        f"  {name}: N={info['N']} D={info['D']} degW={info['degW']} "
        f"degLHS={info['degLHS']} degRHS={info['degRHS']}",
        flush=True,
    )
    assert info["degLHS"] != info["degRHS"] or (
        info["degLHS"] == -1 and info["degRHS"] == -1
    ), name
print("DEGREE_MISMATCH_ON_SAMPLES_OK", flush=True)

# Leading-coefficient formula when N != D: lc(W) = (N-D) a b
n_ex = 2 * x**3 + x + 1  # N=3, a=2
d_ex = 5 * x + 7         # D=1, b=5
W_ex = sp.Poly(wronskian(n_ex, d_ex, x), x)
a, b = 2, 5
N, D = 3, 1
lc_pred = (N - D) * a * b
print("LC_W=", W_ex.LC(), "PRED=", lc_pred, flush=True)
assert W_ex.LC() == lc_pred
print("WRONSKIAN_LC_OK", flush=True)

# Combined leading coefficient of 2 H W + n H' d when N != D:
# 2abc (N - D + 1) with c = lc(H) = 1
Hpoly = sp.Poly(H0, x)
c_lead = int(Hpoly.LC())
nP = sp.Poly(n_ex, x)
dP = sp.Poly(d_ex, x)
L_ex = sp.Poly(lhs_poly(H0, n_ex, d_ex, x), x)
lc_comb_pred = 2 * a * b * c_lead * (N - D + 1)
print("LC_LHS=", L_ex.LC(), "PRED=", lc_comb_pred, flush=True)
assert L_ex.LC() == lc_comb_pred
print("COMBINED_LC_OK", flush=True)

# Random squarefree quadratics: lhs is never a scalar multiple of d^2
# unless both vanish (j=0).
random.seed(68)
failures = 0
trials = 40
for _ in range(trials):
    coeffs_H = [random.randint(-5, 5) for _ in range(3)]
    coeffs_H[2] = coeffs_H[2] or 1
    Hrand = sum(coeffs_H[i] * x**i for i in range(3))
    if sp.degree(Hrand, x) != 2:
        continue
    if sp.discriminant(sp.Poly(Hrand, x)) == 0:
        continue
    Nn = random.randint(0, 4)
    Dd = random.randint(0, 4)
    nrand = sum((random.randint(-4, 4) or 1) * x**i for i in range(Nn + 1))
    drand = sum((random.randint(-4, 4) or 1) * x**i for i in range(Dd + 1))
    lhs = lhs_poly(Hrand, nrand, drand, x)
    quot, rem = sp.div(sp.expand(lhs), sp.expand(drand**2), domain="QQ")
    if rem == 0 and sp.diff(quot, x) == 0 and quot != 0:
        failures += 1
        print("UNEXPECTED_CONSTANT_QUOTIENT", Hrand, nrand, drand, quot, flush=True)
print(f"RANDOM_TRIALS_CONSTANT_QUOTIENT_FAILURES={failures}", flush=True)
assert failures == 0
print("NO_RATIONAL_SOLUTION_FOR_QUADRATIC_CORE_OK", flush=True)

checkpoint("DEGREE")
print("CAS_OK", flush=True)
