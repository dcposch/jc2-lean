import Sol68FiveToSixLargeCuspSupportAssemblyScratch

/-! # Finite stopping architecture for the five-to-six cusp jets

For a contracted earlier cusp put `R = 7N-2G`.  The two genuinely first
loads in the I4/I3 ladder occur at jet depths `R-S` (`zeta*A`) and `S`
(`d^2`).  Thus `mu = min S (R-S)` is positive and every coefficient with
depth strictly below `mu` is homogeneous.  All other literal terms in the
two first integrals remain below the extracted coefficient until after
this first wall.

This file proves only that arithmetic and the abstract finite induction
which a symbolic homogeneous recurrence may instantiate.  It assumes no
unproved coefficient recurrence.  The existing terminal-zero and terminal
all-nonzero branches are retained verbatim in the source-facing wrapper.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspFiniteStopping68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Exact arithmetic inventory for the first loaded contracted cusp jet.

The seven strict inequalities below respectively keep out `d^2`, `zeta*A`,
the common `gamma*d/gamma*e` wall, `B^3/B^2*c`, the epsilon loads,
`gamma*B^2`, and `zeta*B`.  The final trichotomy records whether the first
loaded rung contains only `d^2`, only `zeta*A`, or both. -/
def FiveToSixCuspJetFiniteStop68 (N G S : ℕ) : Prop :=
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  0 < mu ∧
    (∀ q, q < mu →
      q < S ∧ q < R - S ∧ q < 4 * N - G ∧ q < G - S ∧
        q < 6 * N - G - S ∧ q < 4 * N - S ∧
        q < 7 * N - G - S) ∧
    (∀ q, q ≤ mu →
      9 * N - 2 * G - S - q = 2 * N + (R - S - q) ∧
        10 * N - 2 * G - S - q = 3 * N + (R - S - q)) ∧
    ((S < R - S ∧ mu = S) ∨
      (R - S < S ∧ mu = R - S) ∨
      (S = R - S ∧ mu = S ∧ mu = R - S))

/-- In the five-to-six chamber the first cusp load is finite and is exactly
`d^2`, `zeta*A`, or their simultaneous wall. -/
theorem fiveToSix_cuspJet_finiteStop_arithmetic68
    (N G S : ℕ) (hN : 0 < N)
    (hwindow : 5 * N < 2 * G ∧ 2 * G ≤ 6 * N)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G) :
    FiveToSixCuspJetFiniteStop68 N G S := by
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  have hR : R = 7 * N - 2 * G := rfl
  have hRS : 0 < R - S := by omega
  have hmuS : mu ≤ S := Nat.min_le_left _ _
  have hmuRS : mu ≤ R - S := Nat.min_le_right _ _
  have hmu : 0 < mu := by
    change 0 < min S (R - S)
    rcases le_total S (R - S) with hleft | hright
    · rw [Nat.min_eq_left hleft]
      exact hS
    · rw [Nat.min_eq_right hright]
      exact hRS
  have hRG : R < G := by omega
  have hGN : N < G := by omega
  have hR4 : R < 4 * N := by omega
  have hRgamma : R < 2 * (4 * N - G) := by omega
  change 0 < mu ∧ _ ∧ _ ∧ _
  refine ⟨hmu, ?_, ?_, ?_⟩
  · intro q hq
    have hqS : q < S := lt_of_lt_of_le hq hmuS
    have hqRS : q < R - S := lt_of_lt_of_le hq hmuRS
    have hqGamma : q < 4 * N - G := by
      rcases le_total S (R - S) with hleft | hright
      · have htwice : 2 * S ≤ R := by omega
        omega
      · have htwice : 2 * (R - S) ≤ R := by omega
        omega
    refine ⟨hqS, hqRS, hqGamma, ?_, ?_, ?_, ?_⟩ <;> omega
  · intro q hq
    have hqRS : q ≤ R - S := le_trans hq hmuRS
    constructor <;> omega
  · rcases lt_trichotomy S (R - S) with hlt | heq | hgt
    · exact Or.inl ⟨hlt, Nat.min_eq_left (Nat.le_of_lt hlt)⟩
    · exact Or.inr (Or.inr ⟨heq,
        Nat.min_eq_left (by omega), Nat.min_eq_right (by omega)⟩)
    · exact Or.inr (Or.inl ⟨hgt,
        Nat.min_eq_right (Nat.le_of_lt hgt)⟩)

/-- Predicate-valued finite induction through every homogeneous rung.  The
step is required only when the next depth is still strictly before the
first load; no assertion is made at the loaded rung itself. -/
theorem fiveToSix_cuspJet_induction_before_firstLoad68
    (mu : ℕ) (P : ℕ → Prop) (hP0 : P 0)
    (hstep : ∀ q, q + 1 < mu → P q → P (q + 1)) :
    ∀ q, q < mu → P q := by
  intro q hq
  induction q with
  | zero => exact hP0
  | succ q ih =>
      exact hstep q (by simpa [Nat.succ_eq_add_one] using hq)
        (ih (by omega))

/-- The form needed for the discriminant invariant: a symbolic recurrence
which kills the next jet modulo all previous jets yields vanishing of every
jet strictly before the first load. -/
theorem fiveToSix_cuspJet_zero_before_firstLoad68
    {K : Type*} [Zero K] (mu : ℕ) (jet : ℕ → K)
    (hzero : jet 0 = 0)
    (hstep : ∀ q, q + 1 < mu →
      (∀ j, j ≤ q → jet j = 0) → jet (q + 1) = 0) :
    ∀ q, q < mu → ∀ j, j ≤ q → jet j = 0 := by
  apply fiveToSix_cuspJet_induction_before_firstLoad68 mu
      (fun q => ∀ j, j ≤ q → jet j = 0)
  · intro j hj
    have : j = 0 := by omega
    simpa [this] using hzero
  · intro q hq hprev j hj
    by_cases hjq : j ≤ q
    · exact hprev j hjq
    · have hj1 : j = q + 1 := by omega
      rw [hj1]
      exact hstep q hq hprev

/-- Existing supported second-jet data plus the exact finite stopping
arithmetic at its same contracted witness. -/
def FiveToSixContractedEarlierFiniteStopAssembly68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ) : Prop :=
  FiveToSixContractedEarlierSecondJetAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g ∧
    ∃ N G S, n = 60 * N ∧ g = 60 * G ∧ 2 < N ∧
      0 < S ∧ S < 7 * N - 2 * G ∧
      FiveToSixCuspJetFiniteStop68 N G S

theorem fiveToSix_contractedEarlierSecondJet_finiteStop68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ)
    (hassembly : FiveToSixContractedEarlierSecondJetAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g) :
    FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g := by
  refine ⟨hassembly, ?_⟩
  rcases hassembly with
    ⟨_s, N, G, S, hn, hg, _hs, hN, hS, hSR, _hd, _he, hpacket, _hjet⟩
  rcases hpacket with
    ⟨hN0, hgt5, hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp, _hsource⟩
  exact ⟨N, G, S, hn, hg, hN, hS, hSR,
    fiveToSix_cuspJet_finiteStop_arithmetic68 N G S hN0
      ⟨hgt5, hle6⟩ hS hSR⟩

/-- Source-facing refinement.  Only the earlier cusp receives new finite
stopping data; both terminal alternatives are unchanged. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_finiteStop_assembly68
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
      FiveToSixContractedEarlierFiniteStopAssembly68
        alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E)
        Ae Be ce d ee n g ∨
      (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
        d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) := by
  dsimp only
  rcases integratedPolynomialLowerSystem68_fiveToSix_support_secondJet_assembly68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys with hzero | hearlier | hterminalCusp
  · exact Or.inl hzero
  · exact Or.inr (Or.inl
      (fiveToSix_contractedEarlierSecondJet_finiteStop68
        (hassembly := hearlier)))
  · exact Or.inr (Or.inr hterminalCusp)

#print axioms fiveToSix_cuspJet_finiteStop_arithmetic68
#print axioms fiveToSix_cuspJet_induction_before_firstLoad68
#print axioms fiveToSix_cuspJet_zero_before_firstLoad68
#print axioms fiveToSix_contractedEarlierSecondJet_finiteStop68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_finiteStop_assembly68

end FiveToSixCuspFiniteStopping68

end Max11DegreeRoutes
