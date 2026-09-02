import Sol68ScaleTwoAlignedNonsquareFixedUnifiedSecondFollowingScratch

/-! # First loaded coefficients in the unified fixed inventory -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section FixedUnifiedLoadedAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The first loaded coefficient of a cube-loaded row, together with its
nonvanishing consequence. -/
def terminalFixedCubeLoadedThird68
    (H F : k[X]) (j : k) : Prop :=
  ∀ z : k, H.eval z = 0 → H.derivative.eval z ≠ 0 → j ≠ 0 →
    F.derivative.derivative.derivative.eval z =
        6 * j * H.derivative.eval z ^ 3 ∧
      F.derivative.derivative.derivative.eval z ≠ 0

/-- The first loaded coefficient of a square-loaded difference, including
the exact nonzero scalar. -/
def terminalFixedSquareLoadedSecond68
    (H F G : k[X]) (j : k) : Prop :=
  ∀ z : k, H.eval z = 0 → H.derivative.eval z ≠ 0 → j ≠ 0 →
    (F - G).derivative.derivative.eval z =
        2 * j * H.derivative.eval z ^ 2 ∧
      (F - G).derivative.derivative.eval z ≠ 0

/-- The simultaneously loaded second coefficient of the twice-divided I4
row.  No nonvanishing is claimed without a unit hypothesis on `w*E2`. -/
def terminalFixedSquareI4Second68
    (H B3 phi w E2 : k[X]) : Prop :=
  ∀ z : k, H.eval z = 0 →
    (B3 * phi).derivative.derivative.eval z =
      -12 * H.derivative.eval z ^ 2 * w.eval z * E2.eval z

theorem cubeLoaded_third_68
    (H F : k[X]) (j : k) (hrow : F = C j * H ^ 3) :
    terminalFixedCubeLoadedThird68 H F j := by
  intro z hz hHz hj
  have hH2d : (H ^ 2).derivative.eval z = 0 := by
    rw [derivative_pow]
    simp [hz]
  have heq : F.derivative.derivative.derivative.eval z =
      6 * j * H.derivative.eval z ^ 3 := by
    rw [hrow]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_pow, Nat.cast_ofNat, eval_mul, eval_add, eval_pow,
      eval_C, hz, zero_pow, mul_zero, zero_add, add_zero]
    norm_num
    rw [hH2d]
    simp only [hz, zero_mul, mul_zero, zero_pow, add_zero, zero_add]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 3 hHz)

theorem squareLoaded_second_68
    (H F G : k[X]) (j : k) (hrow : G = F - C j * H ^ 2) :
    terminalFixedSquareLoadedSecond68 H F G j := by
  intro z hz hHz hj
  have hdiff : F - G = C j * H ^ 2 := by
    rw [hrow]
    ring
  have heq : (F - G).derivative.derivative.eval z =
      2 * j * H.derivative.eval z ^ 2 := by
    rw [hdiff]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_pow, Nat.cast_ofNat, eval_mul, eval_add, eval_pow,
      eval_C, hz, zero_pow, mul_zero, zero_add, add_zero]
    norm_num
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 2 hHz)

theorem squareI4_second_68
    (H B3 phi w E2 : k[X])
    (hrow : B3 * phi + C 6 * H ^ 2 * w * E2 = 0) :
    terminalFixedSquareI4Second68 H B3 phi w E2 := by
  have hprod : B3 * phi = -(C 6 * H ^ 2 * w * E2) := by
    linear_combination hrow
  intro z hz
  have hH2d : (H ^ 2).derivative.eval z = 0 := by
    rw [derivative_pow]
    simp [hz]
  rw [hprod]
  simp only [derivative_neg, derivative_mul, derivative_C,
    derivative_pow, Nat.cast_ofNat, eval_neg, eval_add, eval_mul,
    eval_pow, eval_C, hz, zero_pow, zero_mul, mul_zero, zero_add, add_zero]
  norm_num
  rw [hH2d]
  simp only [hz, zero_mul, mul_zero, zero_pow, add_zero, zero_add]
  ring

end FixedUnifiedLoadedAlgebra68

section FixedUnifiedLoaded68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

def terminalFixedUnifiedRLoaded68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRSecondFollowing68 H S
      r t X0 Yd B D w phi1 k1 ∧
    ∃ phi K : k[X],
      terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 phi K ∧
      terminalFixedCubeLoadedThird68 H
        (B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * K) j

def terminalFixedUnifiedMixedLoaded68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedSecondFollowing68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    (∀ K : k[X], k1 = H * K →
      B * w * eDot - D * K = C j * H ^ 3 →
      terminalFixedCubeLoadedThird68 H (B * w * eDot - D * K) j) ∧
    (∀ B3 E2 : k[X],
      E2 * k1 = B3 * w * eDot - C j * H ^ 2 →
      terminalFixedSquareLoadedSecond68 H
        (B3 * w * eDot) (E2 * k1) j) ∧
    (∀ B3 E1 K : k[X],
      E1 * K = B3 * w * eDot - C j * H ^ 2 →
      terminalFixedSquareLoadedSecond68 H
        (B3 * w * eDot) (E1 * K) j) ∧
    ∀ B3 E2 : k[X],
      B3 * phi1 + C 6 * H ^ 2 * w * E2 = 0 →
      terminalFixedSquareI4Second68 H B3 phi1 w E2

def terminalFixedUnifiedLoadedResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoaded68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoaded68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem terminalFixedUnifiedLoaded_of_secondFollowing68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : terminalFixedUnifiedSecondFollowingResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedLoadedResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  have hsimple : ∀ z : k, H.eval z = 0 → H.derivative.eval z ≠ 0 :=
    fun z hz => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hz
  rcases h with hR | hM | hG
  · left
    obtain ⟨hRprev, phi, K, T, _hsecond⟩ := hR
    refine ⟨⟨hRprev, phi, K, T, _hsecond⟩, phi, K, T, ?_⟩
    obtain ⟨_hp4, _hX, _hY, _hW, _hPhi, _hwitness, _hI4,
      hrow, _hlower⟩ := T
    exact cubeLoaded_third_68 H _ j hrow
  · right
    left
    dsimp only [terminalFixedUnifiedMixedLoaded68]
    refine ⟨hM, ?_, ?_, ?_, ?_⟩
    · intro K _hk hrow
      exact cubeLoaded_third_68 H _ j hrow
    · intro B3 E2 hrow
      exact squareLoaded_second_68 H _ _ j hrow
    · intro B3 E1 K hrow
      exact squareLoaded_second_68 H _ _ j hrow
    · intro B3 E2 hrow
      exact squareI4_second_68 H B3 phi1 w E2 hrow
  · exact Or.inr (Or.inr hG)

theorem NonsquareAlignedSourceCurveData68.fixedUnifiedLoadedPacket
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
      terminalFixedUnifiedLoadedResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedSecondFollowingPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedLoaded_of_secondFollowing68 H S hdeg hj
      r t X0 Yd B D w phi1 k1 hres⟩

end FixedUnifiedLoaded68

section NormalizedFixedUnifiedLoaded68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized68ScaleTwo_alignedNonsquare_fixedUnifiedLoaded
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
        terminalFixedUnifiedLoadedResidual68 H S
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
  exact S.fixedUnifiedLoadedPacket (H := H)
    hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedFixedUnifiedLoaded68

end Max11DegreeRoutes
