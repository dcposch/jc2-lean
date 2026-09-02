import Sol68ScaleTwoAlignedNonsquareSourceFixedMixedFourthScratch
import Fable68ScaleTwoAlignedNonsquareMixedFollowingScratch

/-! # Same-witness fifth-row mixed reduction

The two divisor limbs of the fixed fourth-row packet consume their first
unused once-divided terminal coefficient.  The transverse `E2` limb is
preserved verbatim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000

section FixedMixedFifth68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Exact same-witness fifth packet.  The first divisor limb carries the
first coefficient of its divided terminal row.  The simultaneous `B,D`
divisor limb carries the quotient values at the other root and the exact
zeroth-coefficient product split.  The transverse limb is unchanged. -/
def terminalFixedMixedFifth68
    (H r phi1 B D w eDot k1 : k[X]) (j : k) : Prop :=
  ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
    r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
    r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
    B.eval a = 0 ∧ k1.eval a = 0 ∧ D.eval a = 0 ∧
    B.derivative.eval a = 0 ∧ D.derivative.eval a = 0 ∧
    B.eval b * phi1.derivative.eval b +
      6 * H.derivative.eval b * w.eval b * D.eval b = 0 ∧
    H.derivative.eval b * B.eval b * w.eval b * eDot.eval b -
      (D.derivative.eval b * k1.eval b +
        D.eval b * k1.derivative.eval b) = 0 ∧
    (r.eval b ^ 2 * B.eval b + 36 * D.eval b) *
      (6 * phi1.derivative.eval b -
        r.eval b ^ 2 * w.eval b * H.derivative.eval b) = 0 ∧
    15552 * eDot.eval b = H.derivative.eval b * r.eval b ^ 6 ∧
    ((k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
        B * w * eDot - D * k2 = C j * H ^ 3 ∧
        B.derivative.eval b * w.eval b * eDot.eval b +
            B.eval b * w.derivative.eval b * eDot.eval b +
            B.eval b * w.eval b * eDot.derivative.eval b -
          (D.derivative.eval b * k2.eval b +
            D.eval b * k2.derivative.eval b) = 0) ∨
      (D.eval b = 0 ∧ B.eval b = 0 ∧ ∃ B3 E1 : k[X],
        B = H * B3 ∧ D = H * E1 ∧
        B3 * phi1 + C 6 * H * w * E1 = 0 ∧
        E1 * k1 = H * B3 * w * eDot - C j * H ^ 3 ∧
        B3.eval a = 0 ∧ E1.eval a = 0 ∧
        ((E1.eval b = 0 ∧ ∃ E2 : k[X], E1 = H * E2 ∧
            D = H ^ 2 * E2 ∧
            B3 * phi1 + C 6 * H ^ 2 * w * E2 = 0 ∧
            E2 * k1 = B3 * w * eDot - C j * H ^ 2) ∨
          (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
            E1 * k2 = B3 * w * eDot - C j * H ^ 2))) ∨
      (D.eval b = 0 ∧ k1.eval b ≠ 0 ∧ B.eval b ≠ 0 ∧
        phi1.derivative.eval b = 0 ∧ w.eval b = 0 ∧
        D.derivative.eval b = 0 ∧
        ∃ E2 : k[X], D = H ^ 2 * E2 ∧
          B * phi1 + C 6 * H ^ 3 * w * E2 = 0 ∧
          B * w * eDot - H * E2 * k1 = C j * H ^ 3 ∧
          B.eval b * w.derivative.eval b * eDot.eval b =
            H.derivative.eval b * E2.eval b * k1.eval b))

/-- The first unused divided terminal coefficient refines both divisor limbs
of the fixed fourth packet, without changing roots or quotient witnesses. -/
theorem terminalFixedMixed_fifth_68
    (hdeg : H.natDegree = 2)
    {r phi1 B D w eDot k1 : k[X]} {j : k}
    (hfourth : terminalFixedMixedFourth68 H r phi1 B D w eDot k1 j) :
    terminalFixedMixedFifth68 H r phi1 B D w eDot k1 j := by
  obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hBa, hk1a, hDa,
    hBda, hDda, hfaceIb, hfaceRb, hfaceB, heDotPin, htri⟩ := hfourth
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  refine ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hBa, hk1a, hDa,
    hBda, hDda, hfaceIb, hfaceRb, hfaceB, heDotPin, ?_⟩
  rcases htri with ⟨hk1b, k2, hk2, hk2row⟩ |
      ⟨hDb, hBb, B3, E1, hB3, hE1, hI4red, hE1row⟩ |
      ⟨hDb, hk1b, hBb, hphidb, hwb, hDdb, E2, hDsq, hI4red,
        hrowRed, hface3⟩
  · exact Or.inl ⟨hk1b, k2, hk2, hk2row,
      mixedReducedTerminalFirstCoefficient_68 H B w eDot D k2 j b hb
        hk2row⟩
  · have hB3a : B3.eval a = 0 :=
      quotientEvalZero_of_derivativeZero_68 H B B3 a ha
        (hsimple a ha) hB3 hBda
    have hE1a : E1.eval a = 0 :=
      quotientEvalZero_of_derivativeZero_68 H D E1 a ha
        (hsimple a ha) hE1 hDda
    have hsplit := mixedReducedTerminalZeroCoefficient_68 H B3 w eDot
      E1 k1 j b hb hE1row
    refine Or.inr (Or.inl ⟨hDb, hBb, B3, E1, hB3, hE1, hI4red,
      hE1row, hB3a, hE1a, ?_⟩)
    rcases mul_eq_zero.mp hsplit with hE1b | hk1b
    · obtain ⟨E2, hE2⟩ := dvd_of_two_simple_root_evals_68 H E1 hdeg
        hsimple a b hab ha hb hE1a hE1b
      refine Or.inl ⟨hE1b, E2, hE2, ?_, ?_, ?_⟩
      · rw [hE1, hE2]
        ring
      · have hc := hI4red
        rw [hE2] at hc
        linear_combination hc
      · apply mul_left_cancel₀ hH
        have hc := hE1row
        rw [hE2] at hc
        linear_combination hc
    · obtain ⟨k2, hk2⟩ := dvd_of_two_simple_root_evals_68 H k1 hdeg
        hsimple a b hab ha hb hk1a hk1b
      refine Or.inr ⟨hk1b, k2, hk2, ?_⟩
      apply mul_left_cancel₀ hH
      have hc := hE1row
      rw [hk2] at hc
      linear_combination hc
  · exact Or.inr (Or.inr ⟨hDb, hk1b, hBb, hphidb, hwb, hDdb,
      E2, hDsq, hI4red, hrowRed, hface3⟩)

def terminalFixedMixedFifthAssemblyResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  H ∣ r ∨
    terminalFixedMixedFifth68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 j ∨
    terminalFixedPhiFinalAssembly68 H S r t X0 Yd B D w phi1 k1

/-- Source-facing same-witness fifth packet. -/
theorem NonsquareAlignedSourceCurveData68.fixedMixedFifthAssemblyPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      terminalFixedMixedLowerTransport68 H S r t X0 Yd B D w phi1 k1 ∧
      terminalFixedMixedFifthAssemblyResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1, hLower, hres⟩ :=
    S.fixedMixedFourthAssemblyPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1, hLower, ?_⟩
  rcases hres with hr | hfourth | hphi
  · exact Or.inl hr
  · exact Or.inr (Or.inl (terminalFixedMixed_fifth_68 H hdeg hfourth))
  · exact Or.inr (Or.inr hphi)

end FixedMixedFifth68

section NormalizedFixedMixedFifth68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Normalized `(6,8), H=2` same-witness fifth-row assembly. -/
theorem normalized68ScaleTwo_alignedNonsquare_fixedMixedFifthAssembly
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
    ∃ (j : k) (S : NonsquareAlignedSourceCurveData68 H p q j),
      j ≠ 0 ∧
      ∃ r t X0 Yd B D w phi1 k1 : k[X],
        terminalFixedMixedLowerTransport68 H S r t X0 Yd B D w phi1 k1 ∧
        terminalFixedMixedFifthAssemblyResidual68 H S
          r t X0 Yd B D w phi1 k1 := by
  dsimp only
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hDsrc
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1, hLower, hres⟩ :=
    S.fixedMixedFifthAssemblyPacket (H := H) hHdegree hp hq hp6' hq8'
      haligned' hjac hj
  exact ⟨j, S, hj, r, t, X0, Yd, B, D, w, phi1, k1, hLower, hres⟩

end NormalizedFixedMixedFifth68

end Max11DegreeRoutes
