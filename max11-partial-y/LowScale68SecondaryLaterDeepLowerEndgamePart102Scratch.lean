import LowScale68SecondaryLaterDeepLowerEndgamePart16Scratch

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_laterDeepLower
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl hwindow hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
        alpha gamma delta epsilon zeta eta A B c D e n g
        hn hg hgt hopen hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

theorem laterDeepLower_radius_lt_gap
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    n < g := by
  omega

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryFace68_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha 0 delta A B C0 D)
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    FirstSecondaryFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hgt : n < g := laterDeepLower_radius_lt_gap n g hn hwindow
  have hI4c : cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c D e = C i4 := by
    rw [← hI4, hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates]
  have hI3c : cubicFirstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c D e = C i3 := by
    rw [← hI3, hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates]
  have hfour :=
    cubicFirstIntegralFourPolynomial68_laterSecondary_forces_face
      gamma delta epsilon zeta i4 A B c D e n g hn hg hopen
      hA hB hc hD he hI4c
  have hthree :=
    cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
      0 0 gamma delta epsilon zeta i3 A B c D e n g hn hg rfl hwindow
      hA hB hc hD he hI3c
  have h2 := hrowTwo
  rw [hC0, hE0] at h2
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) h2
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower_open
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hopen hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h1 := hrowOne
  rw [hC0, hE0] at h1
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) h1
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    0 alpha 0 gamma delta epsilon zeta eta A B c D e n g
    hn hg rfl hwindow hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have h0 := hrowZero
  rw [hC0, hE0] at h0
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower_open
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hopen hA hB hc hD he] at h0
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hfactor
  exact ⟨hfour, hthree, htwo0, hone0, hzero0⟩

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

theorem polynomialSecondaryClassified68_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha 0 delta A B C0 D)
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  exact firstSecondaryFace68_classify (n : k) (g : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha
    (laterDeepLower_gap_ne_six_radius n g hn hwindow)
    (polynomialSecondaryFace68_of_laterDeepLower_open
      alpha gamma delta epsilon zeta eta i4 i3
      A B C0 c D E e n g hn hg hopen hA hB hc hD he ha hC0 hE0
      hI4 hI3 hrowTwo hrowOne hrowZero)

theorem secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n := by omega
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by
    rw [← Nat.add_sub_assoc hg3]
    omega
  have hdegree : (secondaryDDefectPolynomial68 A B D).natDegree ≤
      5 * n - g := by
    simp only [secondaryDDefectPolynomial68]
    refine (natDegree_sub_le _ _).trans ?_
    rw [sup_le_iff]
    constructor
    · exact hD
    · have hmul := (natDegree_mul_le (p := A) (q := B)).trans
        (Nat.add_le_add hA hB)
      have hsmul := (natDegree_smul_le (1 / 3 : k) (A * B)).trans hmul
      rwa [hindex] at hsmul
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  rw [hindex] at hAB
  have hcoeff : (secondaryDDefectPolynomial68 A B D).coeff
      (5 * n - g) = 0 := by
    simp only [secondaryDDefectPolynomial68, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hAB]
    linear_combination (-1 / 3 : k) * hface
  exact natDegree_lt_of_le_of_coeff_eq_zero68 _
    (5 * n - g) (laterDeepLower_index_pos_five n g hn hwindow)
    hdegree hcoeff

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

/-! ## Canonical expanded endpoints -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  change l = 0 ∧ firstSecondaryThree68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt : n < 2 * g := by
    have hn : 0 < n := data.hn
    omega
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates, hl]
    at hi3e
  exact ⟨hl,
    cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
      0 beta gamma delta epsilon zeta i3 Ae Be ce De ee n g
      data.hn data.hg rfl hwindow data.hA data.hB data.hc data.hD data.he
      hi3e⟩

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

/-! ## Canonical expanded endpoints -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  change l = 0 ∧ firstSecondaryOne68 (n : k) (g : k)
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt : n < 2 * g := by
    have hn : 0 < n := data.hn
    omega
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hErec] at h1e
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) h1e
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    data.hn data.hg hl hwindow data.hA data.hB data.hc data.hD data.he]
    at hone
  simp only [coeff_zero] at hone
  exact ⟨hl, (mul_eq_zero.mp hone).resolve_left (by norm_num)⟩

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

/-! ## Canonical expanded endpoints -/

set_option maxHeartbeats 10000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen.1)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hl, hbeta] at hi4e hi3e
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E
      (by simpa only [n] using data.hn)
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 2 * g - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (laterDeepLower_rowZeroIndex_gt_fiftyNine n g hnlarge hwindow)
  rw [hl, hbeta] at h2e h1e h0target
  have hclass :=
    polynomialSecondaryClassified68_of_laterDeepLower_open
      alpha gamma delta epsilon zeta eta i4 i3
      Ae Be Ce ce De Ee ee n g data.hn data.hg hopen
      data.hA data.hB data.hc data.hD data.he data.ha
      hCrec hErec hi4e hi3e h2e h1e h0target
  exact ⟨hl, hbeta, hclass.1, hclass.2⟩

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

/-! ## Canonical expanded endpoints -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ((2 * g = 3 * n ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (5 / 72 * beta : k) * Ae.coeff (2 * n) ^ 3 = 0) ∨
        (3 * n < 2 * g ∧ 2 * g < 5 * n ∧ beta = 0 ∧
          ee.coeff (6 * n - g) = 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
            3 * De.coeff (5 * n - g)) ∨
        (2 * g = 5 * n ∧ beta = 0 ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have hI3 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hF1 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hl : l = 0 := hI3.1
  refine ⟨hl, hI3.2, hF1.2, ?_⟩
  have hgt : n < 2 * g := by
    have hn : 0 < n := by
      have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
      simpa only [n] using hcore.1
    omega
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro hgt hwindow.1)
  change l = 0 ∧ _ at hsplit
  rcases hsplit.2 with hwall3 | hopen | hwall5 | hdeep
  · exact Or.inl hwall3
  · refine Or.inr (Or.inl ?_)
    have hclass :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            And.intro hopen.1 hopen.2.1)
    exact ⟨hopen.1, hopen.2.1, hclass.2.1, hclass.2.2.1, hclass.2.2.2⟩
  · exact Or.inr (Or.inr hwall5)
  · have : 5 * n < 2 * g ∧ 2 * g ≤ 5 * n := ⟨hdeep.1, hwindow.2⟩
    omega

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
