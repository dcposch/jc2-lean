import Fable410ScaleTwoIotaSourceBridgeScratch

/-! # Zero-`p₁` polar branch of the normalized `(4,10)` iota bridge

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the iota source bridge proved that at the root `a`
of the degree-one scale the order-`-3` polar coefficient of the cleared
tenth-face residual `ι` vanishes, splitting the nonzero face into
`p₁(a) = 0` or `λ + 4 t₂(a) = 0`.  This file opens the branch
`p₁(a) = 0`; the complementary branch is not touched.

First, on `p₁(a) = 0` the thirteenth-face jet equations collapse at the
root: `(q₇/h⁶)(a) = (q₆/h⁵)(a) = (q₄/h²)(a) = (q₅/h⁴)(a) =
(q₃/h)(a) = q₂(a) = 0`.

Second, the exact order-two residual of the bridge forces the
`h`-cofactor `w₁` of the order-`-3` block to vanish at the root, so the
order-`-3` numerator gains a second factor of `h` and the order-`-2`
numerator gains its first: `D₃ = h² w₂` and `D₂ = h u₂`.  Cancelling
`h²` in the power relation `D₃ + h (D₂ + h (D₁ + h D₀)) = c h³` leaves
the exact peeled identity `w₂ + u₂ + D₁ + h D₀ = c h`.  At the root the
collapsed jet kills every term of `D₁` except the `q₁` term, giving the
order-`-1` relation `w₂(a) + u₂(a) = 2 q₁(a) t₂(a)`.

Third, the last unused Keller coefficient — the degree-`0` Jacobian row
`p₀' q₁ - p₁ q₀' = j` of `thirteenthCoefficientJacobianRow_410` — is
consumed at the root on this branch: `p₁(a) = 0` reduces it to
`p₀'(a) q₁(a) = j`.  Combined with the peeled identity this yields the
terminal branch relation `p₀'(a) (w₂(a) + u₂(a)) = 2 j t₂(a)`, and for
a nonzero Keller constant both `p₀'(a)` and `q₁(a)` are nonzero.

The branch is not closed: no contradiction is derived, the cofactors
`w₂, u₂` are retained exactly and are not individually determined, and
`q₁(a)` is pinned only through `p₀'(a) q₁(a) = j`.  The complementary
branch `λ + 4 t₂(a) = 0` is untouched, the ground constants
`α, β, γ, δ` are not touched, and on this branch the Jacobian
coefficient tower is exhausted: there is no unused row below the
consumed degree-`0` row.

No total-degree or twice-prime theorem is used.  The aligned face
`N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Jet collapse at the root on the zero-`p₁` branch -/

section IotaZeroBranchScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- On the `p₁ = 0` branch every thirteenth-face jet value collapses:
the six jet equations force `vis, w₇₃, b₄₂, q₅₄, b₃₁, b₂` to vanish
with `p₁`. -/
theorem iotaZeroBranch_jetCollapse410 (a1 t2 a22 s22 vis w73 q54 b42
    b31 b2 lam : F) (ha1 : a1 = 0)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hW : (8 : F) * b42 = (15 : F) * a1 ^ 2)
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 = 0)
    (hX : (64 : F) * b31 =
      (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam))
    (hY : (256 : F) * b2 =
      a1 ^ 2 *
        ((256 : F) * s22 - (400 : F) * a22 + (243 : F) * lam * t2 -
          (540 : F) * t2 ^ 2)) :
    vis = 0 ∧ w73 = 0 ∧ b42 = 0 ∧ q54 = 0 ∧ b31 = 0 ∧ b2 = 0 := by
  subst ha1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 64 : F) * hT
  · linear_combination (1 / 8 : F) * hU
  · linear_combination (1 / 8 : F) * hW
  · linear_combination (1 / 32 : F) * hV
  · linear_combination (1 / 64 : F) * hX
  · linear_combination (1 / 256 : F) * hY

end IotaZeroBranchScalars410

/-! ## Polar-block evaluations on the collapsed jet -/

section IotaZeroBranchLocal410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 1600000 in
/-- On the collapsed jet the order-`-2` numerator block vanishes at the
root: every monomial carries `p₁`, `b₄₂`, `b₃₁`, or `b₂`. -/
theorem iotaZeroBranch_polarTwoEval410 (t2 a22 s22 vis w73 q54 a1 a0
    b42 b31 b2 : k[X]) (lambda a : k)
    (ha1 : a1.eval a = 0) (hb42 : b42.eval a = 0)
    (hb31 : b31.eval a = 0) (hb2 : b2.eval a = 0) :
    (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
        lambda).eval a = 0 := by
  simp only [iotaPolarTwoNumerator410, eval_add, eval_sub, eval_mul,
    eval_pow, eval_neg, eval_ofNat, eval_C, ha1, hb42, hb31, hb2]
  ring

set_option maxHeartbeats 1600000 in
/-- On the collapsed jet only the `q₁` term of the order-`-1` numerator
block survives at the root. -/
theorem iotaZeroBranch_polarOneEval410 (t2 a22 s22 vis w73 q54 a1 a0
    b1 : k[X]) (lambda a : k)
    (ha1 : a1.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0) :
    (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
        lambda).eval a =
      -((2 : k) * b1.eval a * t2.eval a) := by
  simp only [iotaPolarOneNumerator410, eval_add, eval_sub, eval_mul,
    eval_pow, eval_neg, eval_ofNat, eval_C, ha1, hvis, hw73, hq54]
  ring

set_option maxHeartbeats 1600000 in
/-- Successor packet of the zero-`p₁` polar branch: the order-`-3`
block carries `h²`, the order-`-2` block carries `h`, the `h²`-peeled
power relation is exact, and its root evaluation ties the two retained
cofactors to `q₁ t₂`.  The cofactors `w₂, u₂` are not individually
determined and the branch is not closed. -/
theorem iotaZeroBranch_successorPacket410 (h t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hdegree : h.natDegree = 1) (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (ha1 : a1.eval a = 0)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2)
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * (a1.eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * b2.eval a =
      (a1.eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2)) :
    ∃ w2 u2 : k[X],
      iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
          h ^ 2 * w2 ∧
        iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
            b2 lambda =
          h * u2 ∧
        w2 + u2 +
            iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
              lambda +
            h * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda =
          Polynomial.C c * h ∧
        w2.eval a + u2.eval a = (2 : k) * b1.eval a * t2.eval a := by
  obtain ⟨hvisa, hw73a, hb42a, hq54a, hb31a, hb2a⟩ :=
    iotaZeroBranch_jetCollapse410 (a1.eval a) (t2.eval a) (a22.eval a)
      (s22.eval a) (vis.eval a) (w73.eval a) (q54.eval a) (b42.eval a)
      (b31.eval a) (b2.eval a) lambda ha1 hT hU hW hV hX hY
  obtain ⟨w1, hw1, hres⟩ := iotaBridge_orderTwoResidual410 h t2 a22 s22
    vis w73 q54 a1 a0 b42 b31 b2 b1 b0 lambda a c hroot hpow hT hU hW
    hV hX hY
  have hw1a : w1.eval a = 0 := by
    rw [ha1] at hres
    linear_combination (1 / 128 : k) * hres
  obtain ⟨w2, hw2⟩ := linearPolynomial_dvd_of_eval_eq_zero_410 h w1 a
    hdegree hroot hw1a
  have hP2a :
      (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
          b2 lambda).eval a = 0 :=
    iotaZeroBranch_polarTwoEval410 t2 a22 s22 vis w73 q54 a1 a0 b42
      b31 b2 lambda a ha1 hb42a hb31a hb2a
  obtain ⟨u2, hu2⟩ := linearPolynomial_dvd_of_eval_eq_zero_410 h
    (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
      lambda) a hdegree hroot hP2a
  have hne : h ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdegree
    exact zero_ne_one hdegree
  have hpow' := hpow
  simp only [localClearedIotaResidual410] at hpow'
  have hcube :
      h ^ 2 *
          (w2 + u2 +
            iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
              lambda +
            h * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda) =
        h ^ 2 * (Polynomial.C c * h) := by
    linear_combination hpow' - hw1 - h * hw2 - h * hu2
  have hexact := mul_left_cancel₀ (pow_ne_zero 2 hne) hcube
  have hevalx := congrArg (fun r : k[X] => r.eval a) hexact
  simp only [eval_add, eval_mul, eval_C, hroot, zero_mul, mul_zero,
    add_zero] at hevalx
  have hP1a := iotaZeroBranch_polarOneEval410 t2 a22 s22 vis w73 q54
    a1 a0 b1 lambda a ha1 hvisa hw73a hq54a
  have hsum : w2.eval a + u2.eval a =
      (2 : k) * b1.eval a * t2.eval a := by
    linear_combination hevalx - hP1a
  refine ⟨w2, u2, ?_, hu2, hexact, hsum⟩
  rw [hw1, hw2]
  ring

/-! ## The last unused Keller coefficient at the root -/

/-- On the zero-`p₁` branch the degree-`0` Jacobian row — the last
unused Keller coefficient — evaluates at the root to
`p₀'(a) q₁(a) = j`. -/
theorem iotaZeroBranch_kellerRowZero410 (p q : k[X][X]) (j : k) (a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ha1 : (p.coeff 1).eval a = 0) :
    ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j := by
  have hjac : bivariateJacobian p q =
      Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := thirteenthCoefficientJacobianRow_410 hp hq hjac
  have heval := congrArg (fun r : k[X] => r.eval a) hrow
  simp only [eval_sub, eval_mul, eval_C] at heval
  linear_combination heval + ((q.coeff 0).derivative).eval a * ha1

/-- If the Keller constant is nonzero, both factors of the evaluated
degree-`0` row are nonzero on the zero-`p₁` branch. -/
theorem iotaZeroBranch_kellerUnits410 (u v j : k) (hj : j ≠ 0)
    (hrow : u * v = j) : u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · rintro rfl
    rw [zero_mul] at hrow
    exact hj hrow.symm
  · rintro rfl
    rw [mul_zero] at hrow
    exact hj hrow.symm

/-! ## Source-facing packet -/

set_option maxHeartbeats 1600000 in
/-- Zero-`p₁` polar branch packet on the literal depressed source: the
power relation, the exact order-two residual, the collapsed
thirteenth-face jet, and the previously unused degree-`0` Keller row
combine into `D₃ = h₀² w₂`, `D₂ = h₀ u₂`, the exact peeled identity
`w₂ + u₂ + D₁ + h₀ D₀ = c h₀`, the root relations
`w₂(a) + u₂(a) = 2 q₁(a) t₂(a)` and `p₀'(a) q₁(a) = j`, and the
terminal branch relation `p₀'(a) (w₂(a) + u₂(a)) = 2 j t₂(a)`.  The
cofactors `w₂, u₂` are retained exactly; the branch is not closed and
the complementary branch `λ + 4 t₂(a) = 0` is untouched. -/
theorem nonzeroFace410_iotaZeroPolarBranchPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X]) (a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) (hq7 : q.coeff 7 = h0 ^ 6 * vis)
    (hq6 : q.coeff 6 = h0 ^ 5 * w73) (hq5 : q.coeff 5 = h0 ^ 4 * q54)
    (hq4 : q.coeff 4 = h0 ^ 2 * b42) (hq3 : q.coeff 3 = h0 * b31)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (ha1 : (p.coeff 1).eval a = 0)
    (hT : (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0)
    (hU : (8 : k) * w73.eval a =
      (p.coeff 1).eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * ((p.coeff 1).eval a) ^ 2)
    (hV : (32 : k) * q54.eval a +
        (40 : k) * (p.coeff 1).eval a * a22.eval a -
        (64 : k) * (p.coeff 1).eval a * s22.eval a -
        (27 : k) * (p.coeff 1).eval a * lambda * t2.eval a +
        (90 : k) * (p.coeff 1).eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * ((p.coeff 1).eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * (q.coeff 2).eval a =
      ((p.coeff 1).eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2)) :
    ∃ (c : k) (w2 u2 : k[X]),
      iotaPolarThreeNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda =
        h0 ^ 2 * w2 ∧
      iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) lambda =
        h0 * u2 ∧
      w2 + u2 +
          iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
            (p.coeff 0) (q.coeff 1) lambda +
          h0 * iotaRegularNumerator410 t2 a22 s22 (p.coeff 0)
            (q.coeff 0) lambda =
        Polynomial.C c * h0 ∧
      w2.eval a + u2.eval a =
        (2 : k) * (q.coeff 1).eval a * t2.eval a ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j ∧
      ((p.coeff 0).derivative).eval a * (w2.eval a + u2.eval a) =
        (2 : k) * j * t2.eval a := by
  have hh0 : h0 ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdegree
    exact zero_ne_one hdegree
  obtain ⟨c, hc⟩ := nonzeroFace410_iotaResidualPowerRelation p q H h0 j
    lambda t2 a22 s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN hD
    hp3 hp2 hq8 hq7 hq6 hq5 hq4 hq3
  obtain ⟨w2, u2, hw2, hu2, hexact, hsum⟩ :=
    iotaZeroBranch_successorPacket410 h0 t2 a22 s22 vis w73 q54
      (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
      (q.coeff 0) lambda a c hdegree hroot hc ha1 hT hU hW hV hX hY
  have hrow := iotaZeroBranch_kellerRowZero410 p q j a hp hq hD ha1
  refine ⟨c, w2, u2, hw2, hu2, hexact, hsum, hrow, ?_⟩
  linear_combination ((p.coeff 0).derivative).eval a * hsum +
    (2 : k) * t2.eval a * hrow

end IotaZeroBranchLocal410

#print axioms iotaZeroBranch_jetCollapse410
#print axioms iotaZeroBranch_polarTwoEval410
#print axioms iotaZeroBranch_polarOneEval410
#print axioms iotaZeroBranch_successorPacket410
#print axioms iotaZeroBranch_kellerRowZero410
#print axioms iotaZeroBranch_kellerUnits410
#print axioms nonzeroFace410_iotaZeroPolarBranchPacket

end Max11DegreeRoutes
