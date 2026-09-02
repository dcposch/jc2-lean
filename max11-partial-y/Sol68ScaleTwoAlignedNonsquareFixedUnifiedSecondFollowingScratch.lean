import Sol68ScaleTwoAlignedNonsquareFixedUnifiedFollowingScratch

/-! # Second common coefficient in the unified fixed inventory -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000

section FixedUnifiedSecondFollowingAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Second coefficient of a row loaded only at the third core power. -/
def terminalFixedCubeLoadedSecondCoefficient68
    (H F : k[X]) : Prop :=
  ∀ z : k, H.eval z = 0 → F.derivative.derivative.eval z = 0

/-- First coefficient of a difference loaded only at the second core power. -/
def terminalFixedSquareLoadedFirstCoefficient68
    (H F G : k[X]) : Prop :=
  ∀ z : k, H.eval z = 0 → (F - G).derivative.eval z = 0

/-- First coefficient of the twice-divided I4 row. -/
def terminalFixedSquareI4FirstCoefficient68
    (H B3 phi : k[X]) : Prop :=
  ∀ z : k, H.eval z = 0 → (B3 * phi).derivative.eval z = 0

theorem cubeLoaded_secondCoefficient_68
    (H F : k[X]) (j : k) (hrow : F = C j * H ^ 3) :
    terminalFixedCubeLoadedSecondCoefficient68 H F := by
  intro z hz
  rw [hrow]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_pow, Nat.cast_ofNat, eval_mul, eval_add, eval_pow,
    eval_C, hz, zero_pow, mul_zero, zero_add, add_zero]
  norm_num

theorem squareLoaded_firstCoefficient_68
    (H F G : k[X]) (j : k) (hrow : G = F - C j * H ^ 2) :
    terminalFixedSquareLoadedFirstCoefficient68 H F G := by
  intro z hz
  have hdiff : F - G = C j * H ^ 2 := by
    rw [hrow]
    ring
  rw [hdiff]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_pow, Nat.cast_ofNat, eval_mul, eval_pow, eval_C, hz,
    zero_mul]
  norm_num

theorem squareI4_firstCoefficient_68
    (H B3 phi w E2 : k[X])
    (hrow : B3 * phi + C 6 * H ^ 2 * w * E2 = 0) :
    terminalFixedSquareI4FirstCoefficient68 H B3 phi := by
  intro z hz
  have hder := congrArg (fun P : k[X] => P.derivative.eval z) hrow
  simp only [derivative_add, derivative_mul, derivative_C, derivative_pow,
    Nat.cast_ofNat, eval_add, eval_mul, eval_pow, eval_C, eval_zero,
    derivative_zero, hz, zero_pow, zero_mul, mul_zero, zero_add, add_zero]
    at hder
  norm_num at hder
  simpa only [derivative_mul, eval_add, eval_mul] using hder

end FixedUnifiedSecondFollowingAlgebra68

section FixedUnifiedSecondFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- R-refined named leaf after the common second coefficient. -/
def terminalFixedUnifiedRSecondFollowing68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRFollowing68 H S r t X0 Yd B D w phi1 k1 ∧
    ∃ phi K : k[X],
      terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 phi K ∧
      terminalFixedCubeLoadedSecondCoefficient68 H
        (B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * K)

/-- Mixed fifth named leaf after the common second coefficient and the first
coefficients of every exact twice-divided B/D child row. -/
def terminalFixedUnifiedMixedSecondFollowing68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedFollowing68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    (∀ K : k[X], k1 = H * K →
      B * w * eDot - D * K = C j * H ^ 3 →
      terminalFixedCubeLoadedSecondCoefficient68 H
        (B * w * eDot - D * K)) ∧
    (∀ B3 E2 : k[X],
      E2 * k1 = B3 * w * eDot - C j * H ^ 2 →
      terminalFixedSquareLoadedFirstCoefficient68 H
        (B3 * w * eDot) (E2 * k1)) ∧
    (∀ B3 E1 K : k[X],
      E1 * K = B3 * w * eDot - C j * H ^ 2 →
      terminalFixedSquareLoadedFirstCoefficient68 H
        (B3 * w * eDot) (E1 * K)) ∧
    ∀ B3 E2 : k[X],
      B3 * phi1 + C 6 * H ^ 2 * w * E2 = 0 →
      terminalFixedSquareI4FirstCoefficient68 H B3 phi1

def terminalFixedUnifiedSecondFollowingResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRSecondFollowing68 H S
      r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedSecondFollowing68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem terminalFixedUnifiedSecondFollowing_of_following68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : terminalFixedUnifiedFollowingResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedSecondFollowingResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  rcases h with hR | hM | hG
  · left
    obtain ⟨href, hearly, phi, K, T, hfirst⟩ := hR
    refine ⟨⟨href, hearly, phi, K, T, hfirst⟩, phi, K, T, ?_⟩
    obtain ⟨_hp4, _hX, _hY, _hW, _hPhi, _hwitness, _hI4,
      hrow, _hlower⟩ := T
    exact cubeLoaded_secondCoefficient_68 H _ j hrow
  · right
    left
    dsimp only [terminalFixedUnifiedMixedSecondFollowing68]
    refine ⟨hM, ?_, ?_, ?_, ?_⟩
    · intro K _hk hrow
      exact cubeLoaded_secondCoefficient_68 H _ j hrow
    · intro B3 E2 hrow
      exact squareLoaded_firstCoefficient_68 H _ _ j hrow
    · intro B3 E1 K hrow
      exact squareLoaded_firstCoefficient_68 H _ _ j hrow
    · intro B3 E2 hrow
      exact squareI4_firstCoefficient_68 H B3 phi1 w E2 hrow
  · exact Or.inr (Or.inr hG)

theorem NonsquareAlignedSourceCurveData68.fixedUnifiedSecondFollowingPacket
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
      terminalFixedUnifiedSecondFollowingResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedFollowingPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedSecondFollowing_of_following68 H S
      r t X0 Yd B D w phi1 k1 hres⟩

end FixedUnifiedSecondFollowing68

section NormalizedFixedUnifiedSecondFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized68ScaleTwo_alignedNonsquare_fixedUnifiedSecondFollowing
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
        terminalFixedUnifiedSecondFollowingResidual68 H S
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
  exact S.fixedUnifiedSecondFollowingPacket (H := H)
    hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedFixedUnifiedSecondFollowing68

end Max11DegreeRoutes
