import Sol410ScaleTwoNonzeroSuppliedSourcePacketScratch
import Fable410ScaleTwoFollowingGroundBridgeScratch
import Fable410ScaleTwoThetaZeroBranchClosureScratch

/-!
# Supplied-witness double-root promotion on the nonzero square `(4,10)` face

This successor keeps the caller's exact linear square root `h₀` and root `a`.
The exhausted ground packet kills both the value and the first derivative of
the last three residual coefficients, so their `h₀`-orders rise by two.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- A double zero at the root of a degree-one polynomial gives divisibility by
the square of that exact supplied polynomial. -/
theorem linearPolynomial_sq_dvd_of_eval_derivative_zero_410
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : f.eval a = 0)
    (hf' : f.derivative.eval a = 0) :
    h ^ 2 ∣ f := by
  have hx : (X - C a) ^ 2 ∣ f := by
    have hlin : X - C a ∣ f := by
      rw [dvd_iff_isRoot]
      exact hf
    obtain ⟨f1, hf1⟩ := hlin
    have hf1root : f1.eval a = 0 := by
      have hder := congrArg (fun P : k[X] => P.derivative.eval a) hf1
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
        eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_C, sub_self,
        zero_mul, add_zero] at hder
      simpa using hder.symm.trans hf'
    have hlin1 : X - C a ∣ f1 := by
      rw [dvd_iff_isRoot]
      exact hf1root
    obtain ⟨f2, hf2⟩ := hlin1
    refine ⟨f2, ?_⟩
    rw [hf1, hf2]
    ring
  have hh : h ∣ X - C a :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h (X - C a) a hdegree
      hroot (by simp)
  obtain ⟨u, hu⟩ := hh
  obtain ⟨g, hg⟩ := hx
  refine ⟨u ^ 2 * g, ?_⟩
  rw [hg, hu]
  ring

set_option maxHeartbeats 64000000 in
/-- The supplied nonzero square face gains the exact terminal factorization
`q₄ = h₀⁴ b₄₄`, `q₃ = h₀³ b₃₃`, and `q₂ = h₀² q₂₂` after consuming the
complete ground bridge. -/
theorem nonzeroFace410_linearRoot_suppliedGroundDoubleRoot
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ t2 a22 s22 vis w73 q54 b44 b33 q22 : k[X],
      p.coeff 3 = h0 ^ 3 * t2 ∧
      p.coeff 2 = h0 ^ 2 * a22 ∧
      q.coeff 8 = h0 ^ 8 * s22 ∧
      q.coeff 7 = h0 ^ 6 * vis ∧
      q.coeff 6 = h0 ^ 5 * w73 ∧
      q.coeff 5 = h0 ^ 4 * q54 ∧
      q.coeff 4 = h0 ^ 4 * b44 ∧
      q.coeff 3 = h0 ^ 3 * b33 ∧
      q.coeff 2 = h0 ^ 2 * q22 := by
  obtain ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8,
      hq7, hq6, hq5, hq4, hq3, hT, hU, hW, hV, hX, hY⟩ :=
    nonzeroFace410_linearRoot_suppliedThetaInputs p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  obtain ⟨_, _, _, _, _, _, ha1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    nonzeroFace410_thetaZeroBranchClosurePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4 hq3 hdegree hroot hT hU hW hV hX hY
  have hvis0 : vis.eval a = 0 := by
    linear_combination ((1 : k) / 64) * hT + ((5 : k) / 2) * ha1
  have hw730 : w73.eval a = 0 := by
    rw [ha1, zero_mul] at hU
    linear_combination ((1 : k) / 8) * hU
  have hb420 : b42.eval a = 0 := by
    rw [ha1] at hW
    norm_num at hW
    exact hW
  have hq540 : q54.eval a = 0 := by
    rw [ha1] at hV
    norm_num at hV
    exact hV
  have hb310 : b31.eval a = 0 := by
    rw [ha1] at hX
    norm_num at hX
    exact hX
  have hb20 : (q.coeff 2).eval a = 0 := by
    rw [ha1] at hY
    norm_num at hY
    exact hY
  obtain ⟨cepsilon, hepin⟩ :=
    nonzeroFace410_epsilonResidualPowerRelation p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4
  obtain ⟨czeta, hzpin⟩ :=
    nonzeroFace410_zetaResidualPowerRelation p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3
  obtain ⟨ceta, hnpin⟩ :=
    nonzeroFace410_etaResidualPowerRelation p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3
  have hb42kill := epsilonPin_rootDerivativeKill410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 lambda cepsilon a hepin hroot
    hvis0 hw730 hq540 ha1
  have hb31kill := zetaPin_rootDerivativeKillFull410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 lambda cepsilon czeta a
    hepin hzpin hroot hvis0 hw730 hq540 ha1
  have hq2kill := etaPin_rootDerivativeKillFull410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) lambda
    cepsilon czeta ceta a hepin hzpin hnpin hroot hvis0 hw730 hq540 ha1
  have hb42div : h0 ^ 2 ∣ b42 :=
    linearPolynomial_sq_dvd_of_eval_derivative_zero_410 h0 b42 a hdegree
      hroot hb420 hb42kill
  have hb31div : h0 ^ 2 ∣ b31 :=
    linearPolynomial_sq_dvd_of_eval_derivative_zero_410 h0 b31 a hdegree
      hroot hb310 hb31kill
  have hq2div : h0 ^ 2 ∣ q.coeff 2 :=
    linearPolynomial_sq_dvd_of_eval_derivative_zero_410 h0 (q.coeff 2) a
      hdegree hroot hb20 hq2kill
  obtain ⟨b44, hb44⟩ := hb42div
  obtain ⟨b33, hb33⟩ := hb31div
  obtain ⟨q22, hq22⟩ := hq2div
  refine ⟨t2, a22, s22, vis, w73, q54, b44, b33, q22, hp3, hp2,
    hq8, hq7, hq6, hq5, ?_, ?_, hq22⟩
  · rw [hq4, hb44]
    ring
  · rw [hq3, hb33]
    ring

end Max11DegreeRoutes
