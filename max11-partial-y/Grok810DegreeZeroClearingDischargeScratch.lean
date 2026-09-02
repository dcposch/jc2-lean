import Grok810DegreeZeroCompactBridgeScratch

/-! # Clearing discharge of the `(8,10)` degree-zero Z-track

Lane Z7.  The parent `Grok810DegreeZeroCompactBridgeScratch` lands
`compact = 2^{28} ρ` and the integer-cleared coordinates
`h^{7d} · depressed`.  This file discharges the simple-pole derivative
on the scaled left jet from a literal `(8,10)` source.

**Landed.** `sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source`:
`ρ_left' = C(2^{62} j)/h0` from the source Jacobian, with the six
unsolved valuations.  Consequently
`degreeZeroSourceJetHead810_zero_of_source_of_clearing` and
`degreeZeroFace810_linearRoot_headVanishing_of_clearing` need only the
remaining-`17` clearing, not a derivative hypothesis.

**Named gap.** The algebraic identity
`degreeZeroClearedSource810 = 2^{62} · h^{119} · sourceRhoResidual810`
on the ninth-power face (CAS job `810-dz-clearing`; analog of
`piSourceClearingBridge810`).  One-shot `field_simp; ring` after
unfolding the nested residuals did not finish in two hours, nor did
substituting the cleared rationals into the 215-term compact.  That
identity is the exact remaining datum for
`degreeZeroFace810_linearRoot_headVanishing` with no clearing
hypothesis.

Constants are `119 / 17 / 102`.  No chamber is closed.  After degree
`0` there is no unused Keller row.  The next unused compact-numerator
order on this jet is `103`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Named gap: source `= 2^{62} h^{119} ρ`

The one-shot ring identity
`degreeZeroClearedSource810 = 2^{62} · h^{119} · sourceRhoResidual810`
(the `(8,10)` analog of `piSourceClearingBridge810`) did not finish
inside a two-hour isolated compile, nor did the companion compact
substitution `2^{34} · compact(cleared rationals)`.  CAS job
`810-dz-clearing` confirms both identities.  The nested residual
expansion `compact = 2^{28} ρ` is landed in the parent.  The missing
datum is exactly that algebraic source-clearing ring.

The simple-pole derivative on the scaled left jet *is* discharged
below, so the numerator's remaining hypotheses reduce to clearing
alone.
-/

/-! ## Left-jet identification -/

section DegreeZeroLeftJetClearing810

variable {F : Type*} [Field F] [CharZero F]

theorem sourceRhoResidualLeftJet810_eq_source
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : F) :
    sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5
        b4 b3 b2 b1 lambda =
      sourceRhoResidual810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4
        a3 a2 a1 a0
        ((5 * (h ^ 6 * t0) * h ^ 2 - lambda * h ^ 9) / 4)
        (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 :=
  rfl

theorem degreeZeroLeftJet_ninthPower810
    (h t0 lambda : F) :
    5 * (h ^ 6 * t0) * h ^ 2 -
        4 * ((5 * (h ^ 6 * t0) * h ^ 2 - lambda * h ^ 9) / 4) =
      lambda * h ^ 9 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  field_simp [h4]
  ring

#print axioms sourceRhoResidualLeftJet810_eq_source
#print axioms degreeZeroLeftJet_ninthPower810

end DegreeZeroLeftJetClearing810

/-! ## Scaled simple pole on the left jet -/

section DegreeZeroLeftJetDeriv810

variable {k : Type*} [Field k] [CharZero k]

theorem ninthPower_coeff9_ratFunc810
    (h0 a7 q9 : k[X]) (lambda : k)
    (hN : (5 : k[X]) * a7 * h0 ^ 2 - (4 : k[X]) * q9 =
      Polynomial.C lambda * h0 ^ 9) :
    algebraMap k[X] (RatFunc k) q9 =
      ((5 : RatFunc k) * algebraMap k[X] (RatFunc k) a7 *
            (algebraMap k[X] (RatFunc k) h0) ^ 2 -
          RatFunc.C lambda * (algebraMap k[X] (RatFunc k) h0) ^ 9) /
        4 := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have h4 : (4 : RatFunc k) ≠ 0 := by norm_num
  have hmapped := congrArg phi hN
  have hNrat :
      (5 : RatFunc k) * phi a7 * (phi h0) ^ 2 - 4 * phi q9 =
        RatFunc.C lambda * (phi h0) ^ 9 := by
    simpa [phi, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hsum :
      5 * phi a7 * (phi h0) ^ 2 =
        RatFunc.C lambda * (phi h0) ^ 9 + 4 * phi q9 :=
    (sub_eq_iff_eq_add.mp hNrat)
  have hmul4 :
      4 * phi q9 =
        5 * phi a7 * (phi h0) ^ 2 -
          RatFunc.C lambda * (phi h0) ^ 9 := by
    rw [hsum]
    ring
  rw [eq_div_iff h4, mul_comm]
  exact hmul4

set_option maxHeartbeats 800000000 in
/-- The scaled left-jet primitive has the ordinary simple-pole
derivative supplied by the affine source Jacobian.  The residue is
`2^{62} j`.  No clearing identity is used. -/
theorem sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    Differential.deriv
        ((degreeZeroClearedIntegerScale810 : RatFunc k) *
          sourceRhoResidualLeftJet810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) t0)
            (algebraMap k[X] (RatFunc k) v1)
            (algebraMap k[X] (RatFunc k) u1)
            (algebraMap k[X] (RatFunc k) (p.coeff 4))
            (algebraMap k[X] (RatFunc k) (p.coeff 3))
            (algebraMap k[X] (RatFunc k) (p.coeff 2))
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
            (algebraMap k[X] (RatFunc k) (p.coeff 0))
            (algebraMap k[X] (RatFunc k) s1)
            (algebraMap k[X] (RatFunc k) w1)
            (algebraMap k[X] (RatFunc k) b62)
            (algebraMap k[X] (RatFunc k) (q.coeff 5))
            (algebraMap k[X] (RatFunc k) (q.coeff 4))
            (algebraMap k[X] (RatFunc k) (q.coeff 3))
            (algebraMap k[X] (RatFunc k) (q.coeff 2))
            (algebraMap k[X] (RatFunc k) (q.coeff 1)) (RatFunc.C lambda)) =
      RatFunc.C ((degreeZeroClearedIntegerScale810 : k) * j) /
        algebraMap k[X] (RatFunc k) h0 := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hprim := sourceRhoResidual810_deriv_eq_simplePole_of_source p q
    H h0 j lambda hp hq hh0 hH hp8 hq10 hN hD
  have hNsubst :
      (5 : k[X]) * (h0 ^ 6 * t0) * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0] using hN
  have hHsubst :
      (5 : k[X]) * (h0 ^ 6 * t0) * h0 ^ 2 - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [hH] using hNsubst
  have hb9 := ninthPower_coeff9_ratFunc810 h0 (h0 ^ 6 * t0)
    (q.coeff 9) lambda hHsubst
  have hident :
      sourceRhoResidualLeftJet810 (phi h0) (phi t0) (phi v1) (phi u1)
          (phi (p.coeff 4)) (phi (p.coeff 3)) (phi (p.coeff 2))
          (phi (p.coeff 1)) (phi (p.coeff 0)) (phi s1) (phi w1)
          (phi b62) (phi (q.coeff 5)) (phi (q.coeff 4))
          (phi (q.coeff 3)) (phi (q.coeff 2)) (phi (q.coeff 1))
          (RatFunc.C lambda) =
        sourceRhoResidual810 (phi h0) (phi (p.coeff 7))
          (phi (p.coeff 6)) (phi (p.coeff 5)) (phi (p.coeff 4))
          (phi (p.coeff 3)) (phi (p.coeff 2)) (phi (p.coeff 1))
          (phi (p.coeff 0)) (phi (q.coeff 9)) (phi (q.coeff 8))
          (phi (q.coeff 7)) (phi (q.coeff 6)) (phi (q.coeff 5))
          (phi (q.coeff 4)) (phi (q.coeff 3)) (phi (q.coeff 2))
          (phi (q.coeff 1)) := by
    dsimp only [sourceRhoResidualLeftJet810]
    simp only [ht0, hv1, hu1, hs1, hw1, hb62, phi, map_mul, map_pow]
    have hb9' :
        phi (q.coeff 9) =
          ((5 : RatFunc k) * (phi h0 ^ 6 * phi t0) * phi h0 ^ 2 -
              RatFunc.C lambda * phi h0 ^ 9) / 4 := by
      simpa [phi, map_mul, map_pow] using hb9
    rw [hb9']
  rw [hident]
  have hnum : (degreeZeroClearedIntegerScale810 : RatFunc k) =
      RatFunc.C (degreeZeroClearedIntegerScale810 : k) :=
    (map_natCast (RatFunc.C : k →+* RatFunc k)
      degreeZeroClearedIntegerScale810).symm
  let prim : RatFunc k :=
    sourceRhoResidual810 (phi h0) (phi (p.coeff 7)) (phi (p.coeff 6))
      (phi (p.coeff 5)) (phi (p.coeff 4)) (phi (p.coeff 3))
      (phi (p.coeff 2)) (phi (p.coeff 1)) (phi (p.coeff 0))
      (phi (q.coeff 9)) (phi (q.coeff 8)) (phi (q.coeff 7))
      (phi (q.coeff 6)) (phi (q.coeff 5)) (phi (q.coeff 4))
      (phi (q.coeff 3)) (phi (q.coeff 2)) (phi (q.coeff 1))
  have hleib :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) * prim) =
        (degreeZeroClearedIntegerScale810 : RatFunc k) *
          (RatFunc.C j / phi h0) := by
    have hmul :
        Differential.deriv
            (RatFunc.C (degreeZeroClearedIntegerScale810 : k) * prim) =
          RatFunc.C (degreeZeroClearedIntegerScale810 : k) *
            Differential.deriv prim := by
      simpa [ratFuncDerivation46_apply, Algebra.smul_def] using
        ratFuncDerivation46.map_smul
          (degreeZeroClearedIntegerScale810 : k) prim
    rw [hnum, hmul]
    dsimp [prim, phi]
    rw [hprim]
  have hscale :
      (degreeZeroClearedIntegerScale810 : RatFunc k) *
          (RatFunc.C j / phi h0) =
        RatFunc.C ((degreeZeroClearedIntegerScale810 : k) * j) /
          phi h0 := by
    rw [hnum, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← map_mul]
  rw [hleib, hscale]

#print axioms ninthPower_coeff9_ratFunc810
#print axioms sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source

end DegreeZeroLeftJetDeriv810

/-! ## Head vanishing with clearing, without a derivative hypothesis -/

section DegreeZeroSourceHeadDischarge810

variable {k : Type*} [Field k] [CharZero k]

/-- The order-`102` head vanishes at a linear root of `h0` once the
remaining-`17` clearing is supplied.  The simple-pole derivative is
obtained from the source Jacobian, not assumed. -/
theorem degreeZeroSourceJetHead810_zero_of_source_of_clearing
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) (p.coeff 4))
              (algebraMap k[X] (RatFunc k) (p.coeff 3))
              (algebraMap k[X] (RatFunc k) (p.coeff 2))
              (algebraMap k[X] (RatFunc k) (p.coeff 1))
              (algebraMap k[X] (RatFunc k) (p.coeff 0))
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) (q.coeff 5))
              (algebraMap k[X] (RatFunc k) (q.coeff 4))
              (algebraMap k[X] (RatFunc k) (q.coeff 3))
              (algebraMap k[X] (RatFunc k) (q.coeff 2))
              (algebraMap k[X] (RatFunc k) (q.coeff 1))
              (RatFunc.C lambda))) :
    degreeZeroSourceJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
        ((p.coeff 4).eval a) ((p.coeff 3).eval a) ((p.coeff 2).eval a)
        ((p.coeff 1).eval a) ((p.coeff 0).eval a) (s1.eval a)
        (w1.eval a) (b62.eval a) ((q.coeff 5).eval a)
        ((q.coeff 4).eval a) ((q.coeff 3).eval a) ((q.coeff 2).eval a)
        ((q.coeff 1).eval a) lambda = 0 :=
  degreeZeroSourceJetHead810_zero_of_deriv_eq_simplePole h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda ((degreeZeroClearedIntegerScale810 : k) * j) a hh0 hdegree
    hroot hclear
    (sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source p q H
      h0 j lambda t0 v1 u1 s1 w1 b62 hp hq hh0 hH hp8 hq10 hN hD ht0
      hv1 hu1 hs1 hw1 hb62)

/-- Source-facing head vanishing at a linear root, with the remaining-`17`
clearing still hypothesized.  The six unsolved valuations come from the
fifteenth-face packet.  The simple-pole derivative is not assumed. -/
theorem degreeZeroFace810_linearRoot_headVanishing_of_clearing
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hclear :
      ∀ (t0 v1 u1 s1 w1 b62 : k[X]),
        p.coeff 7 = h0 ^ 6 * t0 →
          p.coeff 6 = h0 ^ 4 * v1 →
            p.coeff 5 = h0 ^ 2 * u1 →
              q.coeff 8 = h0 ^ 6 * s1 →
                q.coeff 7 = h0 ^ 4 * w1 →
                  q.coeff 6 = h0 ^ 2 * b62 →
                    algebraMap k[X] (RatFunc k)
                        (degreeZeroSourceJetQuotient810 h0 t0 v1 u1
                          (p.coeff 4) (p.coeff 3) (p.coeff 2)
                          (p.coeff 1) (p.coeff 0) s1 w1 b62
                          (q.coeff 5) (q.coeff 4) (q.coeff 3)
                          (q.coeff 2) (q.coeff 1)
                          (Polynomial.C lambda)) =
                      (algebraMap k[X] (RatFunc k) h0) ^
                          degreeZeroEffectiveTowerLength810 *
                        ((degreeZeroClearedIntegerScale810 : RatFunc k) *
                          sourceRhoResidualLeftJet810
                            (algebraMap k[X] (RatFunc k) h0)
                            (algebraMap k[X] (RatFunc k) t0)
                            (algebraMap k[X] (RatFunc k) v1)
                            (algebraMap k[X] (RatFunc k) u1)
                            (algebraMap k[X] (RatFunc k) (p.coeff 4))
                            (algebraMap k[X] (RatFunc k) (p.coeff 3))
                            (algebraMap k[X] (RatFunc k) (p.coeff 2))
                            (algebraMap k[X] (RatFunc k) (p.coeff 1))
                            (algebraMap k[X] (RatFunc k) (p.coeff 0))
                            (algebraMap k[X] (RatFunc k) s1)
                            (algebraMap k[X] (RatFunc k) w1)
                            (algebraMap k[X] (RatFunc k) b62)
                            (algebraMap k[X] (RatFunc k) (q.coeff 5))
                            (algebraMap k[X] (RatFunc k) (q.coeff 4))
                            (algebraMap k[X] (RatFunc k) (q.coeff 3))
                            (algebraMap k[X] (RatFunc k) (q.coeff 2))
                            (algebraMap k[X] (RatFunc k) (q.coeff 1))
                            (RatFunc.C lambda))) :
    ∃ (t0 v1 u1 s1 w1 b62 : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧
      p.coeff 6 = h0 ^ 4 * v1 ∧
      p.coeff 5 = h0 ^ 2 * u1 ∧
      q.coeff 8 = h0 ^ 6 * s1 ∧
      q.coeff 7 = h0 ^ 4 * w1 ∧
      q.coeff 6 = h0 ^ 2 * b62 ∧
      degreeZeroSourceJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
          ((p.coeff 4).eval a) ((p.coeff 3).eval a)
          ((p.coeff 2).eval a) ((p.coeff 1).eval a)
          ((p.coeff 0).eval a) (s1.eval a) (w1.eval a) (b62.eval a)
          ((q.coeff 5).eval a) ((q.coeff 4).eval a)
          ((q.coeff 3).eval a) ((q.coeff 2).eval a)
          ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, _hq9d, _hq6, _hsplit⟩ :=
    nonzeroFace810_linearRoot_fifteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have ha6 : p.coeff 6 = h0 ^ 4 * v1 := by
    rw [hv0, hv1]
    ring
  have ha5 : p.coeff 5 = h0 ^ 2 * u1 := by
    rw [hu0, hu1]
    ring
  have hb8 : q.coeff 8 = h0 ^ 6 * s1 := by
    rw [hs0, hs1]
    ring
  have hb7 : q.coeff 7 = h0 ^ 4 * w1 := by
    rw [hw0, hw1]
    ring
  have hhead := degreeZeroSourceJetHead810_zero_of_source_of_clearing
    p q H h0 j lambda a t0 v1 u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8
    hq10 hN hD hroot ht0 ha6 ha5 hb8 hb7 hb62
    (hclear t0 v1 u1 s1 w1 b62 ht0 ha6 ha5 hb8 hb7 hb62)
  exact ⟨t0, v1, u1, s1, w1, b62, ht0, ha6, ha5, hb8, hb7, hb62, hhead⟩

#print axioms degreeZeroSourceJetHead810_zero_of_source_of_clearing
#print axioms degreeZeroFace810_linearRoot_headVanishing_of_clearing

end DegreeZeroSourceHeadDischarge810

end Max11DegreeRoutes
