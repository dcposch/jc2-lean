import LowScale68ScaleTwoAlignedNonsquareCubicOrder

/-! # Terminal numerator orders for the aligned nonsquare cubic core -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section ClearedTerminalNumerators68

variable {k : Type*} [Field k] [CharZero k]

def cubicANumerator68 (t r : k[X]) : k[X] :=
  t - C (5 / 12 : k) * r ^ 2

def cubicBNumerator68 (p3 t r : k[X]) : k[X] :=
  p3 - C (2 / 3 : k) * t * r + C (5 / 27 : k) * r ^ 3

def cubicCNumerator68 (H p2 p3 t r : k[X]) : k[X] :=
  H * p2 - C (1 / 2 : k) * p3 * r + C (1 / 6 : k) * t * r ^ 2 -
    C (5 / 144 : k) * r ^ 4

def cubicDNumerator68 (H p1 p2 p3 t r : k[X]) : k[X] :=
  H ^ 2 * p1 - C (1 / 3 : k) * H * p2 * r +
    C (1 / 12 : k) * p3 * r ^ 2 - C (1 / 54 : k) * t * r ^ 3 +
    C (1 / 324 : k) * r ^ 5

def cubicENumerator68 (H p0 p1 p2 p3 t r : k[X]) : k[X] :=
  H ^ 3 * p0 - C (1 / 6 : k) * H ^ 2 * p1 * r +
    C (1 / 36 : k) * H * p2 * r ^ 2 -
    C (1 / 216 : k) * p3 * r ^ 3 + C (1 / 1296 : k) * t * r ^ 4 -
    C (5 / 46656 : k) * r ^ 6

/-- Numerator of the terminal coefficient `W` over the common denominator
`H²`. -/
def cubicWNumerator68 (H p2 p3 t r : k[X]) (gamma : k) : k[X] :=
  C (4 / 9 : k) * cubicCNumerator68 H p2 p3 t r -
    C (4 / 27 : k) * cubicANumerator68 t r ^ 2 +
    C (2 / 3 * gamma : k) * H ^ 2

/-- Numerator of the odd terminal `I₄` factor `Φ` over `H³`. -/
def cubicPhiNumerator68
    (H p0 p1 p2 p3 t r : k[X]) (gamma epsilon : k) : k[X] :=
  -C (8 / 27 : k) * cubicBNumerator68 p3 t r ^ 2 +
    C (8 / 3 : k) * cubicENumerator68 H p0 p1 p2 p3 t r +
    C (2 * epsilon : k) * H ^ 3 +
    C (40 / 81 : k) * cubicANumerator68 t r ^ 3 -
    C (16 / 9 : k) * cubicANumerator68 t r *
      cubicCNumerator68 H p2 p3 t r -
    C (4 / 3 * gamma : k) * cubicANumerator68 t r * H ^ 2

/-- At a cubic-core root all four terminal numerators `B,D,W,Φ` vanish.
This is the exact valuation gain used by the last-row face. -/
theorem cubicCore_terminalNumerators_eval_zero_68
    (H p0 p1 p2 p3 t r : k[X]) (gamma epsilon a : k)
    (hH : H.eval a = 0)
    (ht : (3 : k) * t.eval a = (r.eval a) ^ 2)
    (hv : (27 : k) * p3.eval a = (r.eval a) ^ 3) :
    (cubicBNumerator68 p3 t r).eval a = 0 ∧
      (cubicDNumerator68 H p1 p2 p3 t r).eval a = 0 ∧
      (cubicWNumerator68 H p2 p3 t r gamma).eval a = 0 ∧
      (cubicPhiNumerator68 H p0 p1 p2 p3 t r gamma epsilon).eval a = 0 := by
  have ht' : t.eval a = (r.eval a) ^ 2 / 3 := by
    linear_combination (1 / 3 : k) * ht
  have hv' : p3.eval a = (r.eval a) ^ 3 / 27 := by
    linear_combination (1 / 27 : k) * hv
  simp only [cubicBNumerator68, cubicDNumerator68, cubicWNumerator68,
    cubicPhiNumerator68, cubicANumerator68, cubicCNumerator68,
    cubicENumerator68, eval_add, eval_sub, eval_neg, eval_mul, eval_pow,
    eval_C, hH]
  rw [ht', hv']
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end ClearedTerminalNumerators68

section TerminalValuationSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing terminal valuation packet.  Relative to their naive
denominators, `B,D,W,Φ` each gain one full factor of the quadratic core.
The next unresolved face is the quotient relation obtained by dividing
`BΦ+6WD=0` by `H²`. -/
theorem NonsquareAlignedSourceCurveData68.cubicCoreTerminalValuationPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      H ∣ cubicBNumerator68 (p.coeff 3) t r ∧
      H ∣ cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r ∧
      H ∣ cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma ∧
      H ∣ cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r S.gamma S.epsilon := by
  obtain ⟨_kappa, g, r, t, _s, _u, hg, hr, ht, _hs, _hu, _hushape,
      hcore⟩ :=
    S.integratedRSNext_cubicCorePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hall (N : k[X])
      (hN : ∀ a : k, H.eval a = 0 → N.eval a = 0) : H ∣ N :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hN
  have hB : H ∣ cubicBNumerator68 (p.coeff 3) t r := by
    apply hall
    intro a ha
    exact (cubicCore_terminalNumerators_eval_zero_68 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon a ha
      (hcore a ha).1 (hcore a ha).2).1
  have hD : H ∣ cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r := by
    apply hall
    intro a ha
    exact (cubicCore_terminalNumerators_eval_zero_68 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon a ha
      (hcore a ha).1 (hcore a ha).2).2.1
  have hW : H ∣ cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r
      S.gamma := by
    apply hall
    intro a ha
    exact (cubicCore_terminalNumerators_eval_zero_68 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon a ha
      (hcore a ha).1 (hcore a ha).2).2.2.1
  have hPhi : H ∣ cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon := by
    apply hall
    intro a ha
    exact (cubicCore_terminalNumerators_eval_zero_68 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon a ha
      (hcore a ha).1 (hcore a ha).2).2.2.2
  exact ⟨g, r, t, hg, hr, ht, hB, hD, hW, hPhi⟩

end TerminalValuationSource68

end Max11DegreeRoutes
