import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportWallScratch

/-! # Exact contraction of the post-epsilon support wall

This contracts only the six literal top-support products retained by the
support-wall module.  The sole algebraic reduction used on those products is
the cusp relation `A_top * B_top^2 + 3*c_top^2 = 0`.  In particular the
coincident wall `D=T` (where the compensated `Fce` edge is constant) is kept.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The two edge equations and their division-free resultant at the support
wall.  All natural-number factors are left in factored form so the arithmetic
provenance of the wall remains visible. -/
def FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let q:=9*N-7*S
  let p:=11*N-7*S
  let a:=4*N-3*S
  let A0:=A.coeff (2*N)
  let B0:=B.coeff D
  let c0:=c.coeff Cc
  let d0:=d.coeff V
  let e0:=e.coeff E
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  A0*((2*N:ℕ):k)*(A0*Fce.coeff q-J.coeff p)+
      ((a:ℕ):k)*A0*B0^2*d0-
        (3:k)*((E:ℕ):k)*B0*c0*e0=0 ∧
    A0*Fce.coeff q*(((N:ℕ):k)-((q:ℕ):k))+
        ((p:ℕ):k)*(J.coeff p+B0^2*d0)=0 ∧
      A0*((2*N:ℕ):k)*((3*N:ℕ):k)*(A0*Fce.coeff q)+
        ((p:ℕ):k)*((E:ℕ):k)*
          (A0*B0^2*d0-(3:k)*B0*c0*e0)=0

/-- Exact top-coefficient contraction.  The `q=0` proof is separate, so no
positive-index derivative formula is silently used on the coincident wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_contracted_scalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ)
    (hN:0<N) (hS:0<S) (hchamber:5*N<4*S) (hupper:4*S≤6*N)
    (hGamma:3*S<4*N) (hTD:S-2*(3*N-2*S)≤3*N-2*S)
    (hA:A.natDegree≤2*N)
    (hB:B.natDegree≤3*N-2*S)
    (hc:c.natDegree≤4*N-2*S)
    (hd:d.natDegree≤5*N-3*S)
    (he:e.natDegree≤6*N-3*S)
    (hcusp:A.coeff (2*N)*B.coeff (3*N-2*S)^2+
      (3:k)*c.coeff (4*N-2*S)^2=0)
    (hstate:
      let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
        (3/4*epsilon:k)•B
      let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
      Fce.natDegree≤9*N-7*S ∧ J.natDegree≤11*N-7*S)
    (hrows:FiveToSixCuspZetaFirstB3EqualitySupportRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoScalar68
        gamma epsilon A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68
      gamma epsilon A B c d e N S:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let q:=9*N-7*S
  let p:=11*N-7*S
  let a:=4*N-3*S
  let K0:=13*N-7*S-1
  let K2:=11*N-7*S-1
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  have hD:0<D:=by dsimp only [D];omega
  have hC:0<Cc:=by dsimp only [Cc];omega
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hq:q=0 ∨ 0<q:=by dsimp only [q];omega
  have hp:0<p:=by dsimp only [p,q];omega
  have hstate':Fce.natDegree≤q ∧ J.natDegree≤p:=by
    simpa only [Fce,J,q,p] using hstate
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hAAF:=coeff_mul_mul_derivative_at_bounds68 A Fce A
    (2*N) q (2*N) (by omega) hA hstate'.1 hA
  rw [show 2*N+q+2*N-1=K0 by dsimp only [q,K0];omega] at hAAF
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) p
    hdAsharp hstate'.2
  rw [show (2*N-1)+p=K0 by dsimp only [p,K0];omega] at hAJ
  have hAF:(A*derivative Fce).coeff K2=
      A.coeff (2*N)*Fce.coeff q*((q:ℕ):k):=by
    rcases hq with hq0|hqpos
    · have hFconst:Fce=C (Fce.coeff 0):=by
        apply eq_C_of_natDegree_le_zero
        simpa only [hq0] using hstate'.1
      rw [hFconst,derivative_C,mul_zero,coeff_zero]
      simp only [hq0,Nat.cast_zero,mul_zero]
    · have hh:=coeff_mul_derivative_at_bounds68 A Fce (2*N) q hqpos
          hA hstate'.1
      rw [show 2*N+q-1=K2 by dsimp only [q,K2];omega] at hh
      exact hh
  have hA'F:=coeff_mul_at_bounds68 (derivative A) Fce (2*N-1) q
    hdAsharp hstate'.1
  rw [show (2*N-1)+q=K2 by dsimp only [q,K2];omega] at hA'F
  have hJder:=coeff_derivative_at_bound68 J p hp
  rw [show p-1=K2 by rfl] at hJder
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hAB2d:=coeff_mul_mul_mul_derivative_at_bounds68 A B B d
    (2*N) D D V hV hA hB hB hd
  rw [show 2*N+D+D+V-1=K0 by dsimp only [D,V,K0];omega] at hAB2d
  have hABBd:=coeff_mul_mul_mul_derivative_at_bounds68 A B d B
    (2*N) D V D hD hA hB hd hB
  rw [show 2*N+D+V+D-1=K0 by dsimp only [D,V,K0];omega] at hABBd
  have hBce:=coeff_mul_mul_derivative_at_bounds68 B c e
    D Cc E hE hB hc he
  rw [show D+Cc+E-1=K0 by dsimp only [D,Cc,E,K0];omega] at hBce
  have hccd:=coeff_mul_mul_derivative_at_bounds68 c d c
    Cc V Cc hC hc hd hc
  rw [show Cc+V+Cc-1=K0 by dsimp only [Cc,V,K0];omega] at hccd
  have hB2d:=coeff_mul_mul_derivative_at_bounds68 B B d
    D D V hV hB hB hd
  rw [show D+D+V-1=K2 by dsimp only [D,V,K2];omega] at hB2d
  have hBBd:=coeff_mul_mul_derivative_at_bounds68 B d B
    D V D hD hB hd hB
  rw [show D+V+D-1=K2 by dsimp only [D,V,K2];omega] at hBBd
  have hfactor:=fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hrow0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowZeroScalar68] at hrow0
  rw [show 13*N-7*S-1=K0 by rfl] at hrow0
  rw [hfactor.1] at hrow0
  change (A*derivative A*Fce-derivative A*J+
    FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e).coeff
      K0=0 at hrow0
  have hrow2:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowTwoScalar68] at hrow2
  rw [show 11*N-7*S-1=K2 by rfl] at hrow2
  rw [hfactor.2] at hrow2
  change ((-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J)+
    FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d).coeff K2=0
      at hrow2
  have hAAF':(A*derivative A*Fce).coeff K0=
      A.coeff (2*N)^2*Fce.coeff q*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAF
  have hAJ':(derivative A*J).coeff K0=
      A.coeff (2*N)*((2*N:ℕ):k)*J.coeff p:=by rw [hAJ,hAtop]
  have hAB2d':(A*B^2*derivative d).coeff K0=
      A.coeff (2*N)*B.coeff D^2*d.coeff V*((V:ℕ):k):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hAB2d
  have hABBd':(A*B*derivative B*d).coeff K0=
      A.coeff (2*N)*B.coeff D^2*d.coeff V*((D:ℕ):k):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hABBd
  have hBce':(B*c*derivative e).coeff K0=
      B.coeff D*c.coeff Cc*e.coeff E*((E:ℕ):k):=hBce
  have hccd':(c*derivative c*d).coeff K0=
      c.coeff Cc^2*d.coeff V*((Cc:ℕ):k):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hccd
  have hB2d':(B^2*derivative d).coeff K2=
      B.coeff D^2*d.coeff V*((V:ℕ):k):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hB2d
  have hBBd':(B*derivative B*d).coeff K2=
      B.coeff D^2*d.coeff V*((D:ℕ):k):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hBBd
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68] at hrow0
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hAAF',hAJ',hAF,
    hA'F,hJder,hAtop,hAB2d',hABBd',hBce',hccd'] at hrow0
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68] at hrow2
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hAF,hA'F,hJder,
    hAtop,hB2d',hBBd'] at hrow2
  have hrow0simple:
      A.coeff (2*N)*((2*N:ℕ):k)*
          (A.coeff (2*N)*Fce.coeff q-J.coeff p)+
        ((a:ℕ):k)*A.coeff (2*N)*B.coeff D^2*d.coeff V-
          (3:k)*((E:ℕ):k)*B.coeff D*c.coeff Cc*e.coeff E=0:=by
    have hnat:V+D=Cc+a:=by dsimp only [V,D,Cc,a];omega
    have hcast:((V:ℕ):k)+((D:ℕ):k)-((Cc:ℕ):k)=((a:ℕ):k):=by
      have hh:=congrArg (fun n:ℕ↦(n:k)) hnat
      push_cast at hh
      linear_combination hh
    rw [←hcast]
    linear_combination hrow0-((Cc:ℕ):k)*d.coeff V*hcusp
  have hrow2simple:
      A.coeff (2*N)*Fce.coeff q*(((N:ℕ):k)-((q:ℕ):k))+
        ((p:ℕ):k)*(J.coeff p+B.coeff D^2*d.coeff V)=0:=by
    have hpNat:V+2*D=p:=by dsimp only [V,D,p];omega
    have hpcast:((V:ℕ):k)+(2:k)*((D:ℕ):k)=((p:ℕ):k):=by
      have hh:=congrArg (fun n:ℕ↦(n:k)) hpNat
      push_cast at hh
      exact hh
    have h2Ncast:((2*N:ℕ):k)=(2:k)*((N:ℕ):k):=by push_cast;rfl
    rw [h2Ncast] at hrow2
    linear_combination (1/6:k)*hrow2-
      (B.coeff D^2*d.coeff V)*hpcast
  have hsumcast:((N:ℕ):k)-((q:ℕ):k)+((p:ℕ):k)=((3*N:ℕ):k):=by
    have hn:N+p=q+3*N:=by dsimp only [q,p];omega
    have hh:=congrArg (fun n:ℕ↦(n:k)) hn
    push_cast at hh ⊢
    linear_combination hh
  have haENat:2*N+a=E:=by dsimp only [a,E];omega
  have haEcast:((2*N:ℕ):k)+((a:ℕ):k)=((E:ℕ):k):=by
    have hh:=congrArg (fun n:ℕ↦(n:k)) haENat
    push_cast at hh
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hresultRaw:
      A.coeff (2*N)*((2*N:ℕ):k)*((3*N:ℕ):k)*
          (A.coeff (2*N)*Fce.coeff q)+
        ((p:ℕ):k)*
          ((((2*N:ℕ):k)+((a:ℕ):k))*A.coeff (2*N)*
              B.coeff D^2*d.coeff V-
            (3:k)*((E:ℕ):k)*B.coeff D*c.coeff Cc*e.coeff E)=0:=by
    rw [←hsumcast]
    linear_combination
      A.coeff (2*N)*((2*N:ℕ):k)*hrow2simple+
        ((p:ℕ):k)*hrow0simple
  have hresult:
      A.coeff (2*N)*((2*N:ℕ):k)*((3*N:ℕ):k)*
          (A.coeff (2*N)*Fce.coeff q)+
        ((p:ℕ):k)*((E:ℕ):k)*
          (A.coeff (2*N)*B.coeff D^2*d.coeff V-
            (3:k)*B.coeff D*c.coeff Cc*e.coeff E)=0:=by
    rw [haEcast] at hresultRaw
    linear_combination hresultRaw
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68,
    D,Cc,V,E,q,p,a,Fce,J]
  exact ⟨hrow0simple,hrow2simple,hresult⟩

/-- Source-facing contraction of the retained support-loaded packet. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68
      gamma epsilon A B c d e N S:=by
  rcases hs with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  rcases hstop with ⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩
  let D:=3*N-2*S
  let w:=2*D
  let T:=S-w
  let t:=min D T
  have htT:t=T:=by dsimp only [t];exact Nat.min_eq_right hTD
  rcases hcur with ⟨hbase,hbaseDrop⟩
  rcases hbase with ⟨hterminal,hJold,hrowOld0,hrowOld2⟩
  rcases hterminal with ⟨hgamma,hY⟩
  rcases hgamma with ⟨hgammaStop,hcontract⟩
  rcases hgammaStop with ⟨hnext,ha,hjet,hgammaRow0,hgammaRow2⟩
  rcases hnext.1 with ⟨hGS,hcell,hprev⟩
  have hsource:=hcell.1.1.1.1
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hstate':=hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hfidx:3*N-2*S-(t-1)-1=9*N-7*S:=by
    dsimp only [D,w,T] at htT
    omega
  have hjidx:5*N-2*S-(t-1)-1=11*N-7*S:=by
    dsimp only [D,w,T] at htT
    omega
  rw [hfidx,hjidx] at hstate'
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hCusp⟩
  rw [hGS] at hgt hle hCusp hB hc hd he
  have hgt':5*N<4*S:=by omega
  have hle':4*S≤6*N:=by omega
  have hd':d.natDegree≤5*N-3*S:=by omega
  have he':e.natDegree≤6*N-3*S:=by omega
  apply fiveToSix_zetaFirst_B3_equality_support_contracted_scalar68
    gamma epsilon A B c d e N S hN hS
      hgt' hle'
      (by omega) (by dsimp only [D,w,T] at hTD;omega)
      hA hB hc hd' he' hCusp hstate' hrows

#print axioms fiveToSix_zetaFirst_B3_equality_support_contracted_scalar68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68

end Max11DegreeRoutes
