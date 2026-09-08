import Grok410ScaleTwoFaceCascadeScratch
import Sol410ScaleTwoNonzeroSuppliedFinalContradictionScratch

/-! # Endgame of the `(4,10)` scale-two nonzero cascade

Untracked working note.  No tracked file was edited.

The cascade twelfth packet
`normalized410ScaleTwo_nonzeroFace_twelfthInitialPacket` records the
jet `h³ ∣ p₃`, `h² ∣ p₂`, `h⁸ ∣ q₈`, `h⁶ ∣ q₇`, `h⁵ ∣ q₆`,
`h⁴ ∣ q₅`, `h² ∣ q₄`, `h ∣ q₃` together with the root vanishings of
`p₂, q₅, q₄, q₃`.  The thirteenth face isolated the last Keller
coefficient — the degree-`0` row `p₀' q₁ - p₁ q₀' = C j` — but did
not back-wire a source-facing packet.  This file promotes that row to
`normalized410ScaleTwo_nonzeroFace_thirteenthInitialPacket`.  There is
no unused Jacobian coefficient below degree `0`.

The tenth-face residual `ι` is an exact first integral on the
thirteenth-face jet, and its order-`-3` polar coefficient is
`15 p₁³ (λ + 4 t₂) / 256`.  The degree-`4` first integral `θ` has no
branch factor: its order-`-3` block is `-5242880 p₁³`, so `p₁(a) = 0`
unconditionally.  The iota polar split therefore collapses, every
thirteenth-face jet letter vanishes at the root, and the degree-`0`
row reduces to `p₀'(a) q₁(a) = j`.

The remaining overdetermined system is closed by the supplied
valuation exhaustion already landed on this jet
(`nonzeroFace410_linearRoot_suppliedFinalContradiction`): extra
powers of the linear scale on `p₁, p₂, p₃, q₂, q₃, q₄, q₅` force
`h⁴ ∣ (h⁴)'`, which is impossible.  The nonzero face is empty.

No vanishing of the aligned face `N = 0` is claimed.  No total-degree
or twice-prime theorem is used.  No new axiom is introduced.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Local thirteenth packet (twelfth jet plus the last Keller row) -/

section NonzeroThirteenthCascade410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 32000000 in
/-- Finite local thirteenth-face packet: the twelfth-face jet together
with the degree-`0` Keller identity, the last unused Jacobian
coefficient on this cascade. -/
theorem nonzeroFace410_linearRoot_thirteenthInitialPacket
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
    ∃ t2 a22 s22 vis w73 q54 b42 b31 : k[X],
      p.coeff 3 = h0 ^ 3 * t2 ∧
      p.coeff 2 = h0 ^ 2 * a22 ∧
      q.coeff 8 = h0 ^ 8 * s22 ∧
      q.coeff 7 = h0 ^ 6 * vis ∧
      q.coeff 6 = h0 ^ 5 * w73 ∧
      q.coeff 5 = h0 ^ 4 * q54 ∧
      q.coeff 4 = h0 ^ 2 * b42 ∧
      q.coeff 3 = h0 * b31 ∧
      (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0 ∧
      (8 : k) * w73.eval a =
        (p.coeff 1).eval a *
          ((30 : k) * t2.eval a - (9 : k) * lambda) ∧
      (8 : k) * b42.eval a = (15 : k) * ((p.coeff 1).eval a) ^ 2 ∧
      (32 : k) * q54.eval a +
          (40 : k) * (p.coeff 1).eval a * a22.eval a -
          (64 : k) * (p.coeff 1).eval a * s22.eval a -
          (27 : k) * (p.coeff 1).eval a * lambda * t2.eval a +
          (90 : k) * (p.coeff 1).eval a * (t2.eval a) ^ 2 =
        0 ∧
      (64 : k) * b31.eval a =
        (15 : k) * ((p.coeff 1).eval a) ^ 2 *
          ((4 : k) * t2.eval a - (3 : k) * lambda) ∧
      (256 : k) * (q.coeff 2).eval a =
        ((p.coeff 1).eval a) ^ 2 *
          ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
            (243 : k) * lambda * t2.eval a -
            (540 : k) * (t2.eval a) ^ 2) ∧
      (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative =
        Polynomial.C j := by
  obtain ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8, hq7, hq6,
      hq5, hq4, hq3, hT, hU, hW, hV, hX, hY⟩ :=
    nonzeroFace410_linearRoot_twelfthInitialPacket p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  refine ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8, hq7, hq6,
    hq5, hq4, hq3, hT, hU, hW, hV, hX, hY, ?_⟩
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  exact thirteenthCoefficientJacobianRow_410 hp hq hjac

end NonzeroThirteenthCascade410

/-! ## Source-facing thirteenth packet -/

section SourceThirteenthCascade410

/-- Source-facing thirteenth-face packet of a normalized scale-two
`(4,10)` nonzero face: the twelfth-face jet together with the last
Keller coefficient.  No unused Jacobian row remains. -/
theorem normalized410ScaleTwo_nonzeroFace_thirteenthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a j : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ j ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 3 ∣ p.coeff 3 ∧ h0 ^ 2 ∣ p.coeff 2 ∧
        h0 ^ 8 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 5 ∣ q.coeff 6 ∧ h0 ^ 4 ∣ q.coeff 5 ∧
        h0 ^ 2 ∣ q.coeff 4 ∧ h0 ∣ q.coeff 3 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        (p.coeff 2).eval a = 0 ∧ (q.coeff 5).eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative =
          Polynomial.C j := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized410ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨_t2, _a21, _s21, _vis, _w72, _q52, _hp3t, _hp2t, _hq8t, _hq7t,
      _hq6t, _hq5t, _hsrel, _hq52z, _hq4z, _hwrel, _ha21z, _hp3_3,
      _hp2_2, _hq8_8, _hq7_6, _hq6_5, _hq5_3, _hq4_2, hq9, _hT⟩ :=
    nonzeroFace410_linearRoot_tenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot hlambda
  obtain ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8, hq7, hq6,
      hq5, hq4, hq3, _hT', _hU, _hW, _hV, _hX, _hY, hrow⟩ :=
    nonzeroFace410_linearRoot_thirteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot hlambda
  have hp3div : h0 ^ 3 ∣ p.coeff 3 := ⟨t2, hp3⟩
  have hp2div : h0 ^ 2 ∣ p.coeff 2 := ⟨a22, hp2⟩
  have hq8div : h0 ^ 8 ∣ q.coeff 8 := ⟨s22, hq8⟩
  have hq7div : h0 ^ 6 ∣ q.coeff 7 := ⟨vis, hq7⟩
  have hq6div : h0 ^ 5 ∣ q.coeff 6 := ⟨w73, hq6⟩
  have hq5div : h0 ^ 4 ∣ q.coeff 5 := ⟨q54, hq5⟩
  have hq4div : h0 ^ 2 ∣ q.coeff 4 := ⟨b42, hq4⟩
  have hq3div : h0 ∣ q.coeff 3 := ⟨b31, hq3⟩
  have ha2z : (p.coeff 2).eval a = 0 := by
    have : (p.coeff 2).eval a = (h0.eval a) ^ 2 * a22.eval a := by
      simpa [eval_mul, eval_pow] using
        congrArg (fun r : K[X] => r.eval a) hp2
    simpa [hroot] using this
  have hb5z : (q.coeff 5).eval a = 0 := by
    have : (q.coeff 5).eval a = (h0.eval a) ^ 4 * q54.eval a := by
      simpa [eval_mul, eval_pow] using
        congrArg (fun r : K[X] => r.eval a) hq5
    simpa [hroot] using this
  have hq4z : (q.coeff 4).eval a = 0 := by
    have : (q.coeff 4).eval a = (h0.eval a) ^ 2 * b42.eval a := by
      simpa [eval_mul, eval_pow] using
        congrArg (fun r : K[X] => r.eval a) hq4
    simpa [hroot] using this
  have hq3z : (q.coeff 3).eval a = 0 := by
    have : (q.coeff 3).eval a = h0.eval a * b31.eval a := by
      simpa [eval_mul] using congrArg (fun r : K[X] => r.eval a) hq3
    simpa [hroot] using this
  exact ⟨h0, lambda, a, j, hh0, hlambda, hj, hh0degree, hH, hroot, hp3div,
    hp2div, hq8div, hq7div, hq6div, hq5div, hq4div, hq3div, hq9, ha2z,
    hb5z, hq4z, hq3z, hN', hrow⟩

end SourceThirteenthCascade410

/-! ## Iota polar collapse: `θ` forces `p₁(a) = 0` -/

section IotaPolarCollapse410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 80000000 in
/-- On the thirteenth-face jet the degree-`4` first integral `θ` forces
`p₁(a) = 0`.  The iota polar split `p₁(a) = 0 ∨ λ + 4 t₂(a) = 0`
therefore collapses, every thirteenth-face jet letter vanishes at the
root, and the last Keller row reduces to `p₀'(a) q₁(a) = j`.  The
letters `t₂(a), a₂₂(a), s₂₂(a), p₀(a), q₁(a)` remain live. -/
theorem nonzeroFace410_linearRoot_iotaPolarCollapse
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
    ∃ t2 a22 s22 vis w73 q54 b42 b31 : k[X],
      p.coeff 3 = h0 ^ 3 * t2 ∧
      p.coeff 2 = h0 ^ 2 * a22 ∧
      q.coeff 8 = h0 ^ 8 * s22 ∧
      q.coeff 7 = h0 ^ 6 * vis ∧
      q.coeff 6 = h0 ^ 5 * w73 ∧
      q.coeff 5 = h0 ^ 4 * q54 ∧
      q.coeff 4 = h0 ^ 2 * b42 ∧
      q.coeff 3 = h0 * b31 ∧
      (p.coeff 1).eval a = 0 ∧
      vis.eval a = 0 ∧
      w73.eval a = 0 ∧
      q54.eval a = 0 ∧
      b42.eval a = 0 ∧
      b31.eval a = 0 ∧
      (q.coeff 2).eval a = 0 ∧
      (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative =
        Polynomial.C j ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j := by
  obtain ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8, hq7, hq6,
      hq5, hq4, hq3, hT, hU, hW, hV, hX, hY, hrow⟩ :=
    nonzeroFace410_linearRoot_thirteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  obtain ⟨ctheta, hpowT⟩ :=
    nonzeroFace410_thetaResidualPowerRelation p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4 hq3
  have ha1 : (p.coeff 1).eval a = 0 :=
    thetaBridge_pOneVanishes410 h0 t2 a22 s22 vis w73 q54 (p.coeff 1)
      (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1) lambda a ctheta
      hroot hpowT hT hW
  have hvis : vis.eval a = 0 := by
    linear_combination (1 / 64 : k) * hT + (5 / 2 : k) * ha1
  have hw73 : w73.eval a = 0 := by
    linear_combination (1 / 8 : k) * hU +
      (((30 : k) * t2.eval a - (9 : k) * lambda) / 8) * ha1
  have hb42 : b42.eval a = 0 := by
    linear_combination (1 / 8 : k) * hW +
      (15 / 8 : k) * (p.coeff 1).eval a * ha1
  have hq54 : q54.eval a = 0 := by
    linear_combination (1 / 32 : k) * hV -
      (1 / 32 : k) *
        ((40 : k) * a22.eval a - (64 : k) * s22.eval a -
          (27 : k) * lambda * t2.eval a +
          (90 : k) * (t2.eval a) ^ 2) * ha1
  have hb31 : b31.eval a = 0 := by
    linear_combination (1 / 64 : k) * hX +
      (15 / 64 : k) * (p.coeff 1).eval a *
        ((4 : k) * t2.eval a - (3 : k) * lambda) * ha1
  have hq2 : (q.coeff 2).eval a = 0 := by
    linear_combination (1 / 256 : k) * hY +
      (1 / 256 : k) * (p.coeff 1).eval a *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2) * ha1
  have hkel := kellerRowConstant_eval410 hp hq hD a
  have hkelP :
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j := by
    rw [ha1, zero_mul, sub_zero] at hkel
    exact hkel
  exact ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8, hq7, hq6,
    hq5, hq4, hq3, ha1, hvis, hw73, hq54, hb42, hb31, hq2, hrow, hkelP⟩

end IotaPolarCollapse410

/-! ## Valuation exhaustion of the nonzero face -/

section NonzeroEndgame410

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 64000000 in
/-- The thirteenth-face jet, the collapsed iota/theta polar tower, and
the last Keller row form an overdetermined system.  The supplied
valuation exhaustion produces `h⁴ ∣ (h⁴)'` on the linear scale, which
is impossible. -/
theorem nonzeroFace410_linearRoot_endgameContradiction
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) (hj : j ≠ 0) :
    False :=
  nonzeroFace410_linearRoot_suppliedFinalContradiction p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj

/-- Source-facing exclusion of a normalized scale-two `(4,10)` nonzero
face.  The aligned face `N = 0` is not opened. -/
theorem normalized410ScaleTwo_nonzeroFace_false
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    False := by
  dsimp only at hnonzero
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized410ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact nonzeroFace410_linearRoot_endgameContradiction p q H h0 j
    lambda a hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot hlambda hj

end NonzeroEndgame410

#print axioms nonzeroFace410_linearRoot_thirteenthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_thirteenthInitialPacket
#print axioms nonzeroFace410_linearRoot_iotaPolarCollapse
#print axioms nonzeroFace410_linearRoot_endgameContradiction
#print axioms normalized410ScaleTwo_nonzeroFace_false

end Max11DegreeRoutes
