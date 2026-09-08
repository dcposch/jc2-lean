import Sol68FiveToSixCuspConvolutionPart02Scratch

/-! # Finite discriminant convolution at an arbitrary cusp depth

The exact first-integral combination from the third-jet file works at every
contracted depth.  Reflection turns its leading term `Delta*d` into an
ordinary coefficient convolution.  Since the edge coefficient of `d` is
nonzero, strong induction kills every `Delta` jet strictly before the first
load `mu = min(S, 7N-2G-S)`.  At `mu` the same convolution leaves exactly
the `d^2`, `zeta*A`, or simultaneous loaded scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspConvolution68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Existing earlier-cusp source data upgraded with its complete finite
convolution and exact first loaded scalar. -/
def FiveToSixContractedEarlierConvolutionAssembly68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ) : Prop :=
  FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g ∧
    ∃ N G S, n = 60 * N ∧ g = 60 * G ∧
      FiveToSixCuspFirstLoadFactor68 zeta A B c d N G S

theorem fiveToSix_contractedEarlierFiniteStop_convolution68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ)
    (hfinite : FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g) :
    FiveToSixContractedEarlierConvolutionAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g := by
  refine ⟨hfinite, ?_⟩
  rcases hfinite.1 with
    ⟨_s, N, G, S, hn, hg, _hs, _hN, hS, hSR,
      hdSharp, heSharp, hpacket, _hsecond⟩
  exact ⟨N, G, S, hn, hg,
    fiveToSix_contractedCusp_firstLoad_convolution68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
      hS hSR hdSharp heSharp⟩

/-- Full source assembly, with both terminal alternatives unchanged. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_convolution_assembly68
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
      FiveToSixContractedEarlierConvolutionAssembly68
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
      (fiveToSix_contractedEarlierFiniteStop_convolution68
        (hfinite := hearlier)))
  · exact Or.inr (Or.inr hterminalCusp)

end FiveToSixCuspConvolution68
end Max11DegreeRoutes
