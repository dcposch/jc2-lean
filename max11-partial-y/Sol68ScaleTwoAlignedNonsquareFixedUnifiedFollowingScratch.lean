import Sol68ScaleTwoAlignedNonsquareFixedUnifiedInventoryScratch

/-! # First common divided coefficient in the unified fixed inventory -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000

section FixedUnifiedFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The first derivative coefficient of the once-divided terminal row at
every core root. -/
def terminalFixedDividedFirstCoefficient68
    (H B D w eDot K : k[X]) : Prop :=
  ∀ z : k, H.eval z = 0 →
    B.derivative.eval z * w.eval z * eDot.eval z +
        B.eval z * w.derivative.eval z * eDot.eval z +
        B.eval z * w.eval z * eDot.derivative.eval z -
      (D.derivative.eval z * K.eval z +
        D.eval z * K.derivative.eval z) = 0

/-- Named R-divisor leaf with the common divided coefficient attached to
the exact quotient witnesses already carried by its phi transport. -/
def terminalFixedUnifiedRFollowing68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedRDivisorLowerZeroRefined68 H S
      r t X0 Yd B D w phi1 k1 ∧
    terminalFixedPhiEarlyGeometricAssembly68 H S
      r t X0 Yd B D w phi1 k1 ∧
    ∃ phi K : k[X],
      terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 phi K ∧
      terminalFixedDividedFirstCoefficient68 H B D w
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) K

/-- Named mixed fifth leaf.  Any exact `H`-quotient witness for `k1`
inherits the same first coefficient at every core root; nondivisor and
transverse children remain inside the fifth packet unchanged. -/
def terminalFixedUnifiedMixedFollowing68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedMixedFifth68 H r phi1 B D w eDot k1 j ∧
    ∀ K : k[X], k1 = H * K →
      B * w * eDot - D * K = C j * H ^ 3 →
      terminalFixedDividedFirstCoefficient68 H B D w eDot K

/-- The early-geometric leaf is deliberately opaque to this coefficient. -/
def terminalFixedUnifiedEarlyGeometryResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedPhiEarlyGeometricAssembly68 H S
    r t X0 Yd B D w phi1 k1

/-- Finite normalized list after consuming the common divided coefficient. -/
def terminalFixedUnifiedFollowingResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRFollowing68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedFollowing68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

/-- Pure same-witness refinement of the unified inventory. -/
theorem terminalFixedUnifiedFollowing_of_inventory68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : terminalFixedUnifiedInventory68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedFollowingResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  rcases h with ⟨href, hearly⟩ | hmixed | hearly
  · left
    have hfinal := terminalFixedRDivisorLowerZeroRefined68_phiAssembly
      H S r t X0 Yd B D w phi1 k1 href
    obtain ⟨phi, K, T, _hgeom, _hconsume⟩ := hfinal
    refine ⟨href, hearly, phi, K, T, ?_⟩
    obtain ⟨_hp4, _hX, _hY, _hW, _hPhi, _hwitness, _hI4,
      hrow, _hlower⟩ := T
    intro z hz
    exact mixedReducedTerminalFirstCoefficient_68 H B w _ D K j z hz
      hrow
  · right
    left
    dsimp only [terminalFixedUnifiedMixedFollowing68]
    refine ⟨hmixed, ?_⟩
    intro K _hk hrow
    intro z hz
    exact mixedReducedTerminalFirstCoefficient_68 H B w _ D K j z hz
      hrow
  · exact Or.inr (Or.inr hearly)

/-- Source-facing packet with all old coordinate equations and lower
transport retained. -/
theorem NonsquareAlignedSourceCurveData68.fixedUnifiedFollowingPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      terminalFixedUnifiedFollowingResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedInventoryPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedFollowing_of_inventory68 H S
      r t X0 Yd B D w phi1 k1 hres⟩

end FixedUnifiedFollowing68

section NormalizedFixedUnifiedFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized68ScaleTwo_alignedNonsquare_fixedUnifiedFollowing
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
        p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
        C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
        B * phi1 + C 6 * H * w * D = 0 ∧
        H * B * w * terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
        H ∣ r * phi1 ∧
        terminalFixedMixedLowerTransport68 H S r t X0 Yd
          B D w phi1 k1 ∧
        terminalFixedUnifiedFollowingResidual68 H S
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
  refine ⟨j, S, hj, ?_⟩
  exact S.fixedUnifiedFollowingPacket (H := H)
    hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedFixedUnifiedFollowing68

end Max11DegreeRoutes
