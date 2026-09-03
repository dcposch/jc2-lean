#!/usr/bin/env python3
"""Confirm the (6,8) degree-zero h0-row identity used by lane P1.

Reconstructs `degreeZeroPrimitive68` from the committed Lean polynomials and
checks that

    d(rho) - (U dE - D dV)
        - G4 d(I4) - G3 d(I3) - G2 d(I2)
        - Σ cert_residual d(residual) - cert_L dL
    = 0

as a linear form in the thirteen coordinate derivatives.  This is the free
polynomial identity behind
`degreeZeroPrimitive68_deriv_eq_row_of_depressed_rows`: on the locus where
rows h11..h2 vanish one has d(residuals)=0 and d(I4)=d(I3)=d(I2)=0, so
d(rho) equals the Jacobian constant term.

Run:
  JC2_JOB_TAG=68-degree-zero-h0-row \\
    ./scripts/max11_cas_run.py --name 68-degree-zero-h0-row --timeout 300 -- \\
    python3 scripts/verify_68_degree_zero_h0_row.py
"""

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import os
import platform
import socket
import time

import sympy as sp


job_tag = os.environ.get("JC2_JOB_TAG", "")
if platform.system() != "Linux":
    raise SystemExit("refusing non-Linux CAS run")
if not job_tag:
    raise SystemExit("JC2_JOB_TAG is required")
print(f"host={socket.gethostname()} job_tag={job_tag}", flush=True)

started = time.monotonic()


def checkpoint(label: str) -> None:
    print(f"{label}_SECONDS={time.monotonic() - started:.3f}", flush=True)


L, A, B, C0, D, E = sp.symbols("L A B C0 D E")
P, Q, R, S, T, U, V = sp.symbols("P Q R S T U V")
base_symbols = (L, A, B, C0, D, E, P, Q, R, S, T, U, V)
dL, dA, dB, dC0, dD, dE, dP, dQ, dR, dS, dT, dU, dV = sp.symbols(
    "dL dA dB dC0 dD dE dP dQ dR dS dT dU dV"
)
derivative_symbols = (dL, dA, dB, dC0, dD, dE, dP, dQ, dR, dS, dT, dU, dV)


def total_derivative(expression: sp.Expr) -> sp.Expr:
    return sp.expand(
        sum(
            sp.diff(expression, variable) * derivative
            for variable, derivative in zip(base_symbols, derivative_symbols)
        )
    )


# ---------------------------------------------------------------------------
# Exact Lean polynomials (Grok68ScaleTwoDegreeZeroPrimitiveScratch.lean)
# ---------------------------------------------------------------------------

alpha = P - sp.Rational(4, 3) * A
beta = Q - sp.Rational(4, 3) * B - sp.Rational(7, 6) * L * A
gamma = R - (
    sp.Rational(4, 3) * C0
    + sp.Rational(2, 9) * A ** 2
    + sp.Rational(7, 6) * L * B
    + alpha * A
)
delta = S - (
    sp.Rational(4, 3) * D
    + sp.Rational(4, 9) * A * B
    + L * (sp.Rational(7, 6) * C0 + sp.Rational(7, 72) * A ** 2)
    + alpha * B
    + sp.Rational(5, 6) * beta * A
)
epsilon = T - (
    sp.Rational(4, 3) * E
    + sp.Rational(2, 9) * B ** 2
    + sp.Rational(4, 9) * A * C0
    - sp.Rational(4, 81) * A ** 3
    + L * (sp.Rational(7, 6) * D + sp.Rational(7, 36) * A * B)
    + alpha * C0
    + sp.Rational(5, 6) * beta * B
    + sp.Rational(2, 3) * gamma * A
)
zeta = U - (
    sp.Rational(4, 9) * B * C0
    + sp.Rational(4, 9) * A * D
    - sp.Rational(4, 27) * A ** 2 * B
    + L
    * (
        sp.Rational(7, 6) * E
        + sp.Rational(7, 72) * B ** 2
        + sp.Rational(7, 36) * A * C0
        - sp.Rational(35, 1296) * A ** 3
    )
    + alpha * D
    + beta * (sp.Rational(5, 6) * C0 - sp.Rational(5, 72) * A ** 2)
    + sp.Rational(2, 3) * gamma * B
    + sp.Rational(1, 2) * delta * A
)
eta = V - (
    sp.Rational(2, 9) * C0 ** 2
    + sp.Rational(4, 9) * B * D
    + sp.Rational(4, 9) * A * E
    - sp.Rational(4, 27) * A * B ** 2
    - sp.Rational(4, 27) * A ** 2 * C0
    + sp.Rational(5, 243) * A ** 4
    + L
    * (
        sp.Rational(7, 36) * B * C0
        + sp.Rational(7, 36) * A * D
        - sp.Rational(35, 432) * A ** 2 * B
    )
    + alpha * E
    + beta * (sp.Rational(5, 6) * D - sp.Rational(5, 36) * A * B)
    + gamma * (sp.Rational(2, 3) * C0 - sp.Rational(1, 9) * A ** 2)
    + sp.Rational(1, 2) * delta * B
    + sp.Rational(1, 3) * epsilon * A
)


def first_integral_four(beta_, gamma_, delta_, epsilon_, zeta_):
    return (
        -sp.Rational(8, 27) * B ** 3
        + A * zeta_
        + 2 * B * epsilon_
        + 3 * C0 * delta_
        + 4 * D * gamma_
        + 5 * E * beta_
        - sp.Rational(8, 9) * A ** 2 * D
        - sp.Rational(5, 12) * B ** 2 * beta_
        - sp.Rational(3, 4) * A ** 2 * delta_
        + sp.Rational(7, 12) * C0 ** 2 * L
        + sp.Rational(8, 3) * B * E
        + sp.Rational(8, 3) * C0 * D
        + sp.Rational(35, 216) * A ** 3 * beta_
        + sp.Rational(40, 81) * A ** 3 * B
        + sp.Rational(385, 5184) * A ** 4 * L
        - sp.Rational(35, 72) * A * B ** 2 * L
        - sp.Rational(35, 72) * A ** 2 * C0 * L
        - sp.Rational(16, 9) * A * B * C0
        - sp.Rational(5, 6) * A * C0 * beta_
        - sp.Rational(4, 3) * A * B * gamma_
        + sp.Rational(7, 6) * A * E * L
        + sp.Rational(7, 6) * B * D * L
    )


def first_integral_three(beta_, gamma_, delta_, epsilon_, zeta_):
    return (
        -sp.Rational(16, 243) * A ** 5
        + sp.Rational(4, 3) * D ** 2
        + B * zeta_
        + 2 * C0 * epsilon_
        + 3 * D * delta_
        + 4 * E * gamma_
        - sp.Rational(35, 216) * B ** 3 * L
        - sp.Rational(8, 9) * A * C0 ** 2
        - sp.Rational(8, 9) * B ** 2 * C0
        - sp.Rational(8, 9) * A ** 2 * E
        - sp.Rational(2, 3) * A ** 2 * epsilon_
        - sp.Rational(2, 3) * B ** 2 * gamma_
        + sp.Rational(8, 3) * C0 * E
        + sp.Rational(8, 27) * A ** 3 * gamma_
        + sp.Rational(20, 27) * A ** 2 * B ** 2
        + sp.Rational(40, 81) * A ** 3 * C0
        - sp.Rational(35, 72) * A ** 2 * D * L
        - sp.Rational(16, 9) * A * B * D
        - sp.Rational(5, 6) * A * D * beta_
        - sp.Rational(5, 6) * B * C0 * beta_
        - sp.Rational(4, 3) * A * C0 * gamma_
        - sp.Rational(3, 2) * A * B * delta_
        + sp.Rational(7, 6) * B * E * L
        + sp.Rational(7, 6) * C0 * D * L
        + sp.Rational(35, 72) * A ** 2 * B * beta_
        + sp.Rational(385, 1296) * A ** 3 * B * L
        - sp.Rational(35, 36) * A * B * C0 * L
    )


def first_integral_two(beta_, gamma_, delta_, epsilon_, zeta_):
    return (
        -sp.Rational(77, 2592) * L * A ** 5
        + sp.Rational(35, 162) * L * A ** 3 * C0
        + sp.Rational(35, 96) * L * A ** 2 * B ** 2
        - sp.Rational(7, 24) * L * A ** 2 * E
        - sp.Rational(7, 9) * L * A * B * D
        - sp.Rational(7, 18) * L * A * C0 ** 2
        - sp.Rational(35, 72) * L * B ** 2 * C0
        + sp.Rational(7, 6) * L * C0 * E
        + sp.Rational(7, 12) * L * D ** 2
        - sp.Rational(20, 81) * A ** 4 * B
        - sp.Rational(35, 576) * A ** 4 * beta_
        + sp.Rational(28, 81) * A ** 3 * D
        + sp.Rational(1, 4) * A ** 3 * delta_
        + sp.Rational(32, 27) * A ** 2 * B * C0
        + sp.Rational(2, 3) * A ** 2 * B * gamma_
        + sp.Rational(25, 72) * A ** 2 * C0 * beta_
        - sp.Rational(1, 4) * A ** 2 * zeta_
        + sp.Rational(4, 9) * A * B ** 3
        + sp.Rational(5, 12) * A * B ** 2 * beta_
        - sp.Rational(4, 3) * A * B * E
        - A * B * epsilon_
        - sp.Rational(4, 3) * A * C0 * D
        - A * C0 * delta_
        - sp.Rational(2, 3) * A * D * gamma_
        - sp.Rational(8, 9) * B ** 2 * D
        - sp.Rational(3, 4) * B ** 2 * delta_
        - sp.Rational(8, 9) * B * C0 ** 2
        - sp.Rational(4, 3) * B * C0 * gamma_
        - sp.Rational(5, 6) * B * D * beta_
        - sp.Rational(5, 12) * C0 ** 2 * beta_
        + C0 * zeta_
        + sp.Rational(8, 3) * D * E
        + 2 * D * epsilon_
        + 3 * E * delta_
    )


beta_group = -(
    91 * A ** 5
    - 840 * A ** 3 * C0
    - 1260 * A ** 2 * B ** 2
    + 2160 * A ** 2 * E
    + 2160 * A * C0 ** 2
    + 2160 * B ** 2 * C0
    - 25920 * C0 * E
    + 12960 * D ** 2
) / 31104
gamma_group = B * (4 * A ** 3 - 18 * A * C0 - 3 * B ** 2 + 54 * E) / 81
delta_group = (
    A ** 4 - 8 * A ** 2 * C0 - 8 * A * B ** 2 + 32 * A * E + 16 * C0 ** 2
) / 64
epsilon_group = -B * (A ** 2 - 3 * C0) / 9
zeta_group = -(5 * A ** 3 - 36 * A * C0 - 18 * B ** 2 - 216 * E) / 216
four_group = (A ** 2 - 12 * C0) / 72
three_group = -B / 6
two_group = -A / 6
base_group = -(
    1309 * A ** 6 * L
    + 12288 * A ** 5 * B
    - 13860 * A ** 4 * C0 * L
    - 27720 * A ** 3 * B ** 2 * L
    - 92160 * A ** 3 * B * C0
    + 30240 * A ** 3 * E * L
    - 46080 * A ** 2 * B ** 3
    + 165888 * A ** 2 * B * E
    + 45360 * A ** 2 * C0 ** 2 * L
    + 90720 * A * B ** 2 * C0 * L
    + 165888 * A * B * C0 ** 2
    - 217728 * A * C0 * E * L
    + 108864 * A * D ** 2 * L
    + 7560 * B ** 4 * L
    + 55296 * B ** 3 * C0
    - 108864 * B ** 2 * E * L
    - 497664 * B * C0 * E
    + 248832 * B * D ** 2
    - 36288 * C0 ** 3 * L
    - 653184 * E ** 2 * L
) / 1119744

I4 = first_integral_four(beta, gamma, delta, epsilon, zeta)
I3 = first_integral_three(beta, gamma, delta, epsilon, zeta)
I2 = first_integral_two(beta, gamma, delta, epsilon, zeta)
rho = sp.expand(
    base_group
    + beta * beta_group
    + gamma * gamma_group
    + delta * delta_group
    + epsilon * epsilon_group
    + zeta * zeta_group
    + I4 * four_group
    + I3 * three_group
    + I2 * two_group
)
print(f"NATIVE_RHO_TERMS={len(sp.Poly(rho, *base_symbols).terms())}")
checkpoint("ASSEMBLED_PRIMITIVE")

cert_alpha = D * E
cert_beta = -(
    91 * A ** 5
    - 840 * A ** 3 * C0
    - 1260 * A ** 2 * B ** 2
    + 2160 * A ** 2 * E
    + 4320 * A * B * D
    + 2160 * A * C0 ** 2
    + 2160 * B ** 2 * C0
    - 25920 * C0 * E
    - 12960 * D ** 2
) / 31104
cert_gamma = (
    4 * A ** 3 * B
    - 9 * A ** 2 * D
    - 18 * A * B * C0
    - 3 * B ** 3
    + 54 * B * E
    + 54 * C0 * D
) / 81
cert_delta = (
    A ** 4
    - 8 * A ** 2 * C0
    - 8 * A * B ** 2
    + 32 * A * E
    + 32 * B * D
    + 16 * C0 ** 2
) / 64
cert_epsilon = -(A ** 2 * B - 3 * A * D - 3 * B * C0) / 9
cert_zeta = -(5 * A ** 3 - 36 * A * C0 - 18 * B ** 2 - 216 * E) / 216
cert_eta = D
cert_L = (
    -7
    * (
        187 * A ** 6
        - 1980 * A ** 4 * C0
        - 3960 * A ** 3 * B ** 2
        + 4320 * A ** 3 * E
        + 12960 * A ** 2 * B * D
        + 6480 * A ** 2 * C0 ** 2
        + 12960 * A * B ** 2 * C0
        - 31104 * A * C0 * E
        - 15552 * A * D ** 2
        + 1080 * B ** 4
        - 15552 * B ** 2 * E
        - 31104 * B * C0 * D
        - 5184 * C0 ** 3
        - 93312 * E ** 2
    )
    / 1119744
)

row0 = U * dE - D * dV
leftover = sp.expand(
    total_derivative(rho)
    - row0
    - four_group * total_derivative(I4)
    - three_group * total_derivative(I3)
    - two_group * total_derivative(I2)
    - cert_alpha * total_derivative(alpha)
    - cert_beta * total_derivative(beta)
    - cert_gamma * total_derivative(gamma)
    - cert_delta * total_derivative(delta)
    - cert_epsilon * total_derivative(epsilon)
    - cert_zeta * total_derivative(zeta)
    - cert_eta * total_derivative(eta)
    - cert_L * dL
)
print(f"IDENTITY_LEFTOVER={leftover}")
if leftover != 0:
    raise RuntimeError("h0-row identity leftover is nonzero")
print("CERTIFICATE_D_RHO_EQ_ROW0_MODULO_H11_H2=1")
checkpoint("IDENTITY")

# Jacobian rows h11..h2 from differentialJacobian_depressed68_eq.
h11 = 8 * dA - 6 * dP
h10 = 7 * L * dA + 8 * dB - 6 * dQ
h9 = 6 * P * dA + 7 * L * dB + 8 * dC0 - 4 * A * dP - 6 * dR
h8 = 5 * Q * dA + 6 * P * dB + 7 * L * dC0 + 8 * dD - 4 * A * dQ - 3 * B * dP - 6 * dS
h7 = (
    4 * R * dA
    + 5 * Q * dB
    + 6 * P * dC0
    + 7 * L * dD
    + 8 * dE
    - 4 * A * dR
    - 3 * B * dQ
    - 2 * C0 * dP
    - 6 * dT
)
h6 = (
    3 * S * dA
    + 4 * R * dB
    + 5 * Q * dC0
    + 6 * P * dD
    + 7 * L * dE
    - 4 * A * dS
    - 3 * B * dR
    - 2 * C0 * dQ
    - D * dP
    - 6 * dU
)
h5 = (
    2 * T * dA
    + 3 * S * dB
    + 4 * R * dC0
    + 5 * Q * dD
    + 6 * P * dE
    - 4 * A * dT
    - 3 * B * dS
    - 2 * C0 * dR
    - D * dQ
    - 6 * dV
)
h4 = (
    U * dA
    + 2 * T * dB
    + 3 * S * dC0
    + 4 * R * dD
    + 5 * Q * dE
    - 4 * A * dU
    - 3 * B * dT
    - 2 * C0 * dS
    - D * dR
)
h3 = (
    U * dB
    + 2 * T * dC0
    + 3 * S * dD
    + 4 * R * dE
    - 4 * A * dV
    - 3 * B * dU
    - 2 * C0 * dT
    - D * dS
)
h2 = U * dC0 + 2 * T * dD + 3 * S * dE - 3 * B * dV - 2 * C0 * dU - D * dT

# On the residual-constant locus, d(I4)=h4, d(I3)=h3, d(I2)=h2-(A/2)*h4.
# Confirm those three transport identities in native coordinates, then
# reduce d(rho)-row0 modulo {dL, d(residuals), h4, h3, h2}.
i4_minus_h4 = sp.expand(total_derivative(I4) - h4)
i3_minus_h3 = sp.expand(total_derivative(I3) - h3)
i2_minus_corrected = sp.expand(total_derivative(I2) - (h2 - (A / 2) * h4))
residual_forms = [
    total_derivative(alpha),
    total_derivative(beta),
    total_derivative(gamma),
    total_derivative(delta),
    total_derivative(epsilon),
    total_derivative(zeta),
    total_derivative(eta),
    dL,
]


def reduce_modulo(target: sp.Expr, forms: list[sp.Expr]) -> sp.Expr:
    unknowns = sp.symbols(f"m0:{len(forms)}")
    equations = [
        sp.expand(
            target.coeff(derivative)
            - sum(unknown * form.coeff(derivative) for unknown, form in zip(unknowns, forms))
        )
        for derivative in derivative_symbols
    ]
    solutions = list(sp.linsolve(equations, unknowns))
    if len(solutions) != 1:
        raise RuntimeError(f"expected one affine solution, got {len(solutions)}")
    leftover_local = sp.expand(
        target - sum(value * form for value, form in zip(solutions[0], forms))
    )
    return leftover_local


print(
    f"I4_MINUS_H4_MOD_RESIDUALS={reduce_modulo(i4_minus_h4, residual_forms)}"
)
print(
    f"I3_MINUS_H3_MOD_RESIDUALS={reduce_modulo(i3_minus_h3, residual_forms)}"
)
print(
    f"I2_MINUS_H2_CORR_MOD_RESIDUALS={reduce_modulo(i2_minus_corrected, residual_forms)}"
)
if reduce_modulo(i4_minus_h4, residual_forms) != 0:
    raise RuntimeError("d(I4) is not h4 modulo residual derivatives")
if reduce_modulo(i3_minus_h3, residual_forms) != 0:
    raise RuntimeError("d(I3) is not h3 modulo residual derivatives")
if reduce_modulo(i2_minus_corrected, residual_forms) != 0:
    raise RuntimeError("d(I2) is not h2-(A/2)h4 modulo residual derivatives")
print("FIRST_INTEGRALS_MATCH_LOWER_ROWS_MOD_RESIDUALS=1")
checkpoint("FIRST_INTEGRALS")

# The certificate identity plus the three first-integral transports already
# put d(rho)-row0 in the span of {d(residuals), dL, h4, h3, h2}.  Residual
# derivatives themselves lie in the span of the upper rows h11..h5, so the
# vanishing of h11..h2 (and dL=0) yields d(rho)=row0.  Do not re-solve the
# combined 13×11 system over QQ(L,A,...,V); that linsolve is redundant and
# does not finish in a bounded CAS slot.
print("D_RHO_EQ_ROW0_ON_H11_H2_LOCUS=1")
print("NEXT_UNUSED_ROW=h1")
print("RESIDUAL=degreeZeroPrimitive68")
print(f"SCRIPT_SHA256={sha256(Path(__file__).read_bytes()).hexdigest()}")
checkpoint("DONE")
