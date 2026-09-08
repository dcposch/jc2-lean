import Sol410ScaleTwoNonzeroSuppliedSourcePacketScratch

/-! # Source-facing twelfth packet on the `(4,10)` scale-two nonzero cascade

Untracked working note.  No tracked file was edited.

The committed nonzero cascade stops at
`normalized410ScaleTwo_nonzeroFace_eighthInitialPacket`.  Untracked
ninth and tenth faces already supply source-facing packets; the
eleventh and twelfth faces isolated the next Jacobian rows and the
upgraded jet, but did not back-wire a `Normalized410LeadingCoreSource`
packet.  The supplied twelfth-face jet
`nonzeroFace410_linearRoot_suppliedThetaInputs` is that missing
composition: `h³ ∣ p₃`, `h² ∣ p₂`, `h⁸ ∣ q₈`, `h⁶ ∣ q₇`, `h⁵ ∣ q₆`,
`h⁴ ∣ q₅`, `h² ∣ q₄`, `h ∣ q₃`.  This file records the same jet under
the cascade packet names and the source-facing wrapper.

No vanishing of `p₁, p₀, t₂, a₂₂, s₂₂, q₂` is claimed.  The residual
`ι` is not claimed to vanish.  The aligned face `N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Local twelfth packet (same jet as the supplied theta-input wrapper) -/

section NonzeroTwelfthCascade410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 32000000 in
/-- Finite local twelfth-face packet: the tenth-face collapsed jet after
the eleventh- and twelfth-face next-order identities. -/
theorem nonzeroFace410_linearRoot_twelfthInitialPacket
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
            (540 : k) * (t2.eval a) ^ 2) :=
  nonzeroFace410_linearRoot_suppliedThetaInputs p q H h0 j lambda a
    hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda

end NonzeroTwelfthCascade410

/-! ## Source-facing twelfth packet -/

section SourceTwelfthCascade410

/-- Source-facing twelfth-face packet of a normalized scale-two `(4,10)`
nonzero face: the tenth-face jet upgrades by one further power of `h`
on `q₅` and a linear factor on `q₃`. -/
theorem normalized410ScaleTwo_nonzeroFace_twelfthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 3 ∣ p.coeff 3 ∧ h0 ^ 2 ∣ p.coeff 2 ∧
        h0 ^ 8 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 5 ∣ q.coeff 6 ∧ h0 ^ 4 ∣ q.coeff 5 ∧
        h0 ^ 2 ∣ q.coeff 4 ∧ h0 ∣ q.coeff 3 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        (p.coeff 2).eval a = 0 ∧ (q.coeff 5).eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
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
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
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
      hq5, hq4, hq3, _hT', _hU, _hW, _hV, _hX, _hY⟩ :=
    nonzeroFace410_linearRoot_twelfthInitialPacket p q H h0 j lambda a
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
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3div, hp2div,
    hq8div, hq7div, hq6div, hq5div, hq4div, hq3div, hq9, ha2z, hb5z, hq4z,
    hq3z, hN'⟩

end SourceTwelfthCascade410

#print axioms nonzeroFace410_linearRoot_twelfthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_twelfthInitialPacket

end Max11DegreeRoutes
