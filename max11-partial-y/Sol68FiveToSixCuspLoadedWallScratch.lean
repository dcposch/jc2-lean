import Sol68FiveToSixCuspConvolutionScratch

/-! # Classification of the first loaded cusp wall

The finite convolution reaches one of three exact scalar walls.  The
all-nonzero cusp packet makes the `d^2`-first wall rigidly nonzero, detects
the zero discriminant jet on the `zeta*A`-first wall exactly by `zeta=0`,
and isolates the unique cancellation scalar on the simultaneous wall.
No contradiction follows from these scalars alone.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Strongest algebraic classification of the exact first loaded rung. -/
def FiveToSixCuspLoadedWallClassification68
    (zeta : k) (A B c d : k[X]) (N G S : ℕ) : Prop :=
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let a := A.coeff (2 * N)
  let b := B.coeff (3 * N - G)
  let c0 := c.coeff (4 * N - G)
  let ds := d.coeff V
  let deltaMu := (Delta.reflect U).coeff mu
  (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧
    ((S < R - S ∧ mu = S ∧
        deltaMu = (3 / 2 : k) * b * ds ∧ deltaMu ≠ 0) ∨
      (R - S < S ∧ mu = R - S ∧
        deltaMu * ds + (9 / 8 : k) * zeta * a * c0 = 0 ∧
        (deltaMu = 0 ↔ zeta = 0)) ∨
      (S = R - S ∧ mu = S ∧ mu = R - S ∧
        deltaMu * ds + (9 / 8 : k) * zeta * a * c0 -
            (3 / 2 : k) * b * ds ^ 2 = 0 ∧
        (deltaMu = 0 ↔
          4 * b * ds ^ 2 = 3 * zeta * a * c0)))

theorem fiveToSix_cuspLoadedWall_classify68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hfactor : FiveToSixCuspFirstLoadFactor68 zeta A B c d N G S) :
    FiveToSixCuspLoadedWallClassification68 zeta A B c d N G S := by
  rcases hpacket with
    ⟨_hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, ha,
      hcusp, _hsource⟩
  rcases hcusp with ⟨hb, hc0, hds, _hes, _hcusp0⟩
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let a := A.coeff (2 * N)
  let b := B.coeff (3 * N - G)
  let c0 := c.coeff (4 * N - G)
  let ds := d.coeff V
  let deltaMu := (Delta.reflect U).coeff mu
  change (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧ _ at hfactor
  change (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧ _
  refine ⟨hfactor.1, ?_⟩
  rcases hfactor.2 with
      ⟨hlt, hmu, hwall⟩ | ⟨hlt, hmu, hwall⟩ |
        ⟨heq, hmuS, hmuZ, hwall⟩
  · left
    refine ⟨hlt, hmu, ?_, ?_⟩
    · have hmul : (deltaMu - (3 / 2 : k) * b * ds) * ds = 0 := by
        linear_combination hwall
      have hz := (mul_eq_zero.mp hmul).resolve_right (by
        simpa only [ds, V] using hds)
      linear_combination hz
    · have hscalar : (3 / 2 : k) * b * ds ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (by simpa only [b] using hb))
          (by simpa only [ds, V] using hds)
      intro hz
      have heq : deltaMu = (3 / 2 : k) * b * ds := by
        have hmul : (deltaMu - (3 / 2 : k) * b * ds) * ds = 0 := by
          linear_combination hwall
        have hzero := (mul_eq_zero.mp hmul).resolve_right (by
          simpa only [ds, V] using hds)
        linear_combination hzero
      exact hscalar (heq ▸ hz)
  · right; left
    refine ⟨hlt, hmu, hwall, ?_⟩
    constructor
    · intro hdelta
      rw [hdelta, zero_mul, zero_add] at hwall
      have hza : (9 / 8 : k) * zeta * a = 0 :=
        (mul_eq_zero.mp hwall).resolve_right (by
          simpa only [c0] using hc0)
      have hz : (9 / 8 : k) * zeta = 0 :=
        (mul_eq_zero.mp hza).resolve_right (by
          simpa only [a] using ha)
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
    · intro hzeta
      rw [hzeta] at hwall
      simp only [mul_zero, zero_mul, add_zero] at hwall
      exact (mul_eq_zero.mp hwall).resolve_right (by
        simpa only [ds, V] using hds)
  · right; right
    refine ⟨heq, hmuS, hmuZ, hwall, ?_⟩
    constructor
    · intro hdelta
      rw [hdelta, zero_mul, zero_add] at hwall
      linear_combination (-8 / 3 : k) * hwall
    · intro hcancel
      have hmul : deltaMu * ds = 0 := by
        linear_combination hwall + (3 / 8 : k) * hcancel
      exact (mul_eq_zero.mp hmul).resolve_right (by
        simpa only [ds, V] using hds)

/-- Earlier source packet upgraded to the rigid loaded-wall split. -/
def FiveToSixContractedEarlierLoadedWallAssembly68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ) : Prop :=
  FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g ∧
    ∃ N G S, n = 60 * N ∧ g = 60 * G ∧
      FiveToSixCuspLoadedWallClassification68 zeta A B c d N G S

theorem fiveToSix_contractedEarlier_loadedWall68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ)
    (hfinite : FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g) :
    FiveToSixContractedEarlierLoadedWallAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g := by
  refine ⟨hfinite, ?_⟩
  rcases hfinite.1 with
    ⟨_s, N, G, S, hn, hg, _hs, _hN, hS, hSR,
      hdSharp, heSharp, hpacket, _hsecond⟩
  have hfactor := fiveToSix_contractedCusp_firstLoad_convolution68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
    hS hSR hdSharp heSharp
  exact ⟨N, G, S, hn, hg,
    fiveToSix_cuspLoadedWall_classify68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hpacket hfactor⟩

/-- Full source split.  The terminal all-nonzero cusp remains a separate,
honest residual. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_loadedWall_assembly68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
      FiveToSixContractedEarlierLoadedWallAssembly68
        alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E)
        Ae Be ce d ee n g ∨
      (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
        d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) := by
  dsimp only
  rcases integratedPolynomialLowerSystem68_fiveToSix_finiteStop_assembly68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys with hzero | hearlier | hterminalCusp
  · exact Or.inl hzero
  · exact Or.inr (Or.inl
      (fiveToSix_contractedEarlier_loadedWall68 (hfinite := hearlier)))
  · exact Or.inr (Or.inr hterminalCusp)

#print axioms fiveToSix_cuspLoadedWall_classify68
#print axioms fiveToSix_contractedEarlier_loadedWall68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_loadedWall_assembly68

end FiveToSixCuspLoadedWall68

end Max11DegreeRoutes
