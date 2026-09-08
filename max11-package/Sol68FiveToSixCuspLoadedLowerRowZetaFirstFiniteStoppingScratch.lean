import Sol68FiveToSixCuspLoadedLowerRowZetaFirstDepthFiveScratch

/-! # Finite stopping of the zeta-first successor ladder

Rather than unrolling further fixed depths, choose the least arithmetic load
between `mu+1` and `S`.  Strong induction and the generic source-backed
I3/I4 successor lemma kill every earlier reflected discriminant coefficient.
The exact least load, its full lower-zero provenance, and the verified first
five layers are all retained.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstFiniteStopping68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The four literal load thresholds for the common I3/I4 successor row. -/
def FiveToSixCuspZetaFirstLoadAt68 (N G S q : ℕ) : Prop :=
  S ≤ q ∨ G-S ≤ q ∨ 4*N-G ≤ q ∨ 4*N-S ≤ q

/-- Finite source-honest induction to the least exact load.  The witness is
at most `S`, because the first threshold necessarily fires there. -/
theorem fiveToSix_zetaFirst_reaches_least_load68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    let mu := min S (7*N-2*G-S)
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    let U := 8*N-2*G
    ∃ q, mu < q ∧ q ≤ S ∧
      (∀ j, j < q → (Delta.reflect U).coeff j = 0) ∧
      (∀ j, mu < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q := by
  classical
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let Load := FiveToSixCuspZetaFirstLoadAt68 N G S
  have h0 := hs
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ R-S < S ∧ mu = R-S ∧ _ ∧
    (∀ j, j ≤ mu → (Delta.reflect U).coeff j = 0) ∧ _ at h0
  have hmuS : mu < S := by omega
  have hbase := h0.2.2.2.2.2.2.2.2.1
  let Q : ℕ → Prop := fun q => mu < q ∧ q ≤ S ∧ Load q
  have hQS : Q S := by
    refine ⟨hmuS,le_rfl,?_⟩
    exact Or.inl le_rfl
  have hex : ∃ q, Q q := ⟨S,hQS⟩
  let q0 := Nat.find hex
  have hq0 : Q q0 := Nat.find_spec hex
  have hnoLoad (j : ℕ) (hmuj : mu < j) (hjq : j < q0) : ¬ Load j := by
    intro hload
    have hjS : j ≤ S := le_trans (Nat.le_of_lt hjq) hq0.2.1
    have hQj : Q j := ⟨hmuj,hjS,hload⟩
    have hq0j : q0 ≤ j := Nat.find_min' hex hQj
    omega
  have hall : ∀ j, j < q0 → (Delta.reflect U).coeff j = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hjq
        by_cases hjmu : j ≤ mu
        · exact hbase j hjmu
        · have hmuj : mu < j := by omega
          have hnload := hnoLoad j hmuj hjq
          have hjS : j < S := by
            by_contra h
            apply hnload
            exact Or.inl (by omega)
          have hjBc : j < G-S := by
            by_contra h
            apply hnload
            exact Or.inr (Or.inl (by omega))
          have hjGamma : j < 4*N-G := by
            by_contra h
            apply hnload
            exact Or.inr (Or.inr (Or.inl (by omega)))
          have hjB3 : j < 4*N-S := by
            by_contra h
            apply hnload
            exact Or.inr (Or.inr (Or.inr (by omega)))
          exact fiveToSix_zetaFirst_discriminant_zero_of_prior68
            alpha gamma epsilon zeta eta terminal A B c d e N G S j hs
            hjS hjBc hjGamma hjB3 (by
              intro i hij
              exact ih i hij (lt_trans hij hjq))
  exact ⟨q0,hq0.1,hq0.2.1,hall,hnoLoad,hq0.2.2⟩

/-- Full handoff: retain every verified fixed-depth branch and attach the
least-load witness supplied by the finite induction. -/
def FiveToSixCuspZetaFirstFiniteStoppingResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let mu := min S (7*N-2*G-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, mu < q ∧ q ≤ S ∧
      (∀ j, j < q → (Delta.reflect U).coeff j = 0) ∧
      (∀ j, mu < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q

theorem fiveToSix_zetaFirst_finiteStopping_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hfive : FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hfive,?_⟩
  have hfour := hfive
  change FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hfour
  have hthree := hfour.1
  change FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hthree
  have hthree' := hthree.1
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hthree'
  exact fiveToSix_zetaFirst_reaches_least_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hthree'.1

#print axioms fiveToSix_zetaFirst_reaches_least_load68
#print axioms fiveToSix_zetaFirst_finiteStopping_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstFiniteStopping68

end Max11DegreeRoutes
