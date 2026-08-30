import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLargeReductionScratch

/-! # The top compensated-I4 resultant on the `q=0` wall

Although the formerly selected coefficient is the constant coefficient when
`q=0`, the compensated `I4` polynomial is itself constant.  Its genuine top
coefficient therefore gives `B_D e_E + c_C d_V = 0`.  Together with the cusp
equation and the already-verified leading scalar this yields the same quadratic
resultant that was previously available only on the positive-`q` branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroTopResultant68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The constant compensated `I4` identity supplies the missing top-product
sum, and hence the quadratic cusp resultant, on the exact `q=0` wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0 ∧
      (4:k)*B.coeff D^2*c.coeff Cc+(9:k)*d.coeff V^2=0:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let K:=D+E
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have hEq:9*N=7*S:=hnxt.1.1
  have hD:0<D:=by dsimp only [D];omega
  have hC:0<Cc:=by dsimp only [Cc];omega
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hK:0<K:=by dsimp only [K];omega
  have hB3deg:(B^3).natDegree≤3*D:=by compute_degree;omega
  have hB3low:(B^3).natDegree<K:=by dsimp only [D,E,K] at *;omega
  have hdLow:d.natDegree<K:=by dsimp only [D,E,K,V] at *;omega
  have hBLow:B.natDegree<K:=by dsimp only [D,E,K] at *;omega
  have hBe: (B*e).coeff K=B.coeff D*e.coeff E:=by
    have h:=coeff_mul_at_bounds68 B e D E hB' he'
    simpa only [K] using h
  have hcd: (c*d).coeff K=c.coeff Cc*d.coeff V:=by
    have h:=coeff_mul_at_bounds68 c d Cc V hc' hd'
    rw [show Cc+V=K by dsimp only [D,Cc,V,E,K];omega] at h
    exact h
  have hFK:Fce.coeff K=0:=by
    dsimp only [Fce]
    rw [hFce,coeff_smul,coeff_C]
    split_ifs with h
    · omega
    · simp only [smul_zero]
  have hsum:B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0:=by
    dsimp only [Fce] at hFK
    simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hBe,hcd,
      coeff_eq_zero_of_natDegree_lt hB3low,
      coeff_eq_zero_of_natDegree_lt hdLow,
      coeff_eq_zero_of_natDegree_lt hBLow,mul_zero,sub_zero,add_zero]
      at hFK
    exact hFK
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hctop':c.coeff Cc≠0:=by simpa [Cc,hGS] using hctop
  have hcuspEq':A.coeff (2*N)*B.coeff D^2+
      (3:k)*c.coeff Cc^2=0:=by simpa [D,Cc,hGS] using hcuspEq
  have hlead:=fiveToSix_zetaFirst_B3_equality_support_leading_scalar68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  dsimp only [D,V,E] at hlead
  refine ⟨hsum,?_⟩
  exact fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
    (A.coeff (2*N)) (B.coeff D) (c.coeff Cc) (d.coeff V)
      (e.coeff E) hctop' hcuspEq' hsum hlead

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroTopResultant68

end Max11DegreeRoutes
