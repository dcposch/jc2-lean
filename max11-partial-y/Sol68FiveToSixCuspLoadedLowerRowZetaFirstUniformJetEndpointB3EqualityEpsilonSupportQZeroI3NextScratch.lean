import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroDiscriminantNextScratch

/-! # The first coefficient below the compensated-I3 top on `q=0`

The compensated `I3` polynomial has degree at most `2D`.  Its two genuine
top summands have common degree `p+D+V=C+E`, which is strictly larger than
`2D` on the exact `q=0` wall.  One coefficient below that top therefore
gives a further first-jet incidence equation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI3Next68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The first-jet equation furnished by the compensated `I3` degree drop. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_I3_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    A.coeff (p-1)*B.coeff D*d.coeff V+
      A.coeff p*B.coeff (D-1)*d.coeff V+
      A.coeff p*B.coeff D*d.coeff (V-1)-
      (3:k)*(c.coeff (Cc-1)*e.coeff E+
        c.coeff Cc*e.coeff (E-1))=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let K:=p+D+V
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rce:=R+(9/2*gamma:k)•e+(9/4*epsilon:k)•c
  change A.coeff (p-1)*B.coeff D*d.coeff V+
      A.coeff p*B.coeff (D-1)*d.coeff V+
      A.coeff p*B.coeff D*d.coeff (V-1)-
      (3:k)*(c.coeff (Cc-1)*e.coeff E+
        c.coeff Cc*e.coeff (E-1))=0
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hEq:9*N=7*S:=hnxt.1.1
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hA':A.natDegree≤p:=by simpa [p] using hA
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have hp:0<p:=by dsimp only [p];omega
  have hD:0<D:=by dsimp only [D];omega
  have hC:0<Cc:=by dsimp only [Cc];omega
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hRlow:Rce.coeff (K-1)=0:=by
    rw [coeff_eq_zero_of_natDegree_lt]
    exact hRceDeg.trans_lt (by dsimp only [D,p,V,K];omega)
  have hABd0:=coeff_mul_mul_one_below_bounds68 A B d p D V
    hp hD hV hA' hB' hd'
  have hABd:(A*B*d).coeff (K-1)=
      A.coeff (p-1)*B.coeff D*d.coeff V+
      A.coeff p*B.coeff (D-1)*d.coeff V+
      A.coeff p*B.coeff D*d.coeff (V-1):=by
    simpa only [K] using hABd0
  have hce0:=coeff_mul_one_below_bounds68 c e Cc E hC hE hc' he'
  have hce:(c*e).coeff (K-1)=
      c.coeff (Cc-1)*e.coeff E+c.coeff Cc*e.coeff (E-1):=by
    rw [show Cc+E=K by dsimp only [p,D,Cc,V,E,K];omega] at hce0
    exact hce0
  have hB2c:(B^2*c).natDegree<K-1:=by
    compute_degree
    dsimp only [D,Cc,p,V,K] at *
    omega
  have hd2:(d^2).natDegree<K-1:=by
    compute_degree
    dsimp only [D,p,V,K] at *
    omega
  have heLow:e.natDegree<K-1:=by
    dsimp only [D,p,V,E,K] at *
    omega
  have hcLow:c.natDegree<K-1:=by
    dsimp only [D,Cc,p,V,K] at *
    omega
  dsimp only [Rce,R] at hRlow
  simp only [coeff_add,coeff_sub,coeff_neg,coeff_smul,smul_eq_mul,hABd,hce,
    coeff_eq_zero_of_natDegree_lt hB2c,
    coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt heLow,
    coeff_eq_zero_of_natDegree_lt hcLow,mul_zero,add_zero,sub_zero] at hRlow
  linear_combination -hRlow

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_I3_next68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI3Next68

end Max11DegreeRoutes
