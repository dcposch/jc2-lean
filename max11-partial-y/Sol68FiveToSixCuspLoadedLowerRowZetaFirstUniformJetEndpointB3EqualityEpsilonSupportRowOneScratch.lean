import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContractionScratch

/-! # Row one at the post-epsilon support wall

The literal row-one coefficient has a nonzero coefficient on a new `Y` jet,
so it is a fresh-jet solve, not a new equation on the row-zero/row-two
resultant.  The first source identity that constrains an existing resultant
variable is instead the individual I4 identity: the fully compensated `Fce`
is constant.  This file records both facts without changing the source
witness or excluding the coincidence `D=T`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualitySupportRowOneLoad68
    (B c d e:k[X]):k[X]:=
  -(3:k)•(B^2*derivative e)+(3:k)•(B*c*derivative d)+
    (3:k)•(B*derivative c*d)+(9:k)•(derivative B*c*d)

def FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=12*N-7*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e-
      (9*gamma:k)•(A*derivative e)+
      (-(9/2*epsilon):k)•(A*derivative c)+
      FiveToSixCuspZetaFirstB3EqualitySupportRowOneLoad68 B c d e).coeff K=0

/-- The same frozen source packet and equality witness are recoverable from
the support-loaded branch. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    G=2*S ∧ S<4*N-G ∧
      FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S:=by
  rcases hs with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  rcases hstop with ⟨hcur,ht,hstate,hclass,hrow0,hrow2⟩
  rcases hcur with ⟨hbase,hbaseDrop⟩
  rcases hbase with ⟨hterminal,hJold,hrowOld0,hrowOld2⟩
  rcases hterminal with ⟨hgamma,hY⟩
  rcases hgamma with ⟨hgammaStop,hcontract⟩
  rcases hgammaStop with ⟨hnext,ha,hjet,hgammaRow0,hgammaRow2⟩
  rcases hnext.1 with ⟨hGS,hcell,hprev⟩
  exact ⟨hGS,hcell.1.1.1.2.2.1,hcell.1.1.1.1⟩

/-- Exact reduction of row one at `q+m=2*S`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_rowOne_literal68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hGamma:3*S<4*N)
    (hrow:FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
      gamma epsilon A B c d e N G S S S):
    FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68
      gamma epsilon A B c d e N S:=by
  let K:=12*N-7*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rw [heq] at hB hc hd he
  have hidx:12*N-2*G-S-(S+S)-1=K:=by rw [heq];dsimp only [K];omega
  have hcc:(c*derivative c).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hAB2:(derivative A*B^2).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hBd:(B*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hdB:(d*derivative B).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have he':(derivative e).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68] at hrow
  rw [hidx] at hrow
  simp only [secondaryResidualRowOnePolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hcc,
    coeff_eq_zero_of_natDegree_lt hAB2,
    coeff_eq_zero_of_natDegree_lt hBd,
    coeff_eq_zero_of_natDegree_lt hdB,
    coeff_eq_zero_of_natDegree_lt he',
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68
    gamma epsilon A B c d e N S
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68,
    FiveToSixCuspZetaFirstB3EndpointRowOneCore68,
    FiveToSixCuspZetaFirstB3EqualitySupportRowOneLoad68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination (-27/4:k)*hrow

/-- The four support products have this exact top coefficient. -/
theorem fiveToSix_zetaFirst_B3_equality_support_rowOne_load_top68
    (B c d e:k[X]) (N S:ℕ)
    (hD:0<3*N-2*S) (hC:0<4*N-2*S)
    (hV:0<5*N-3*S) (hE:0<6*N-3*S)
    (hB:B.natDegree≤3*N-2*S) (hc:c.natDegree≤4*N-2*S)
    (hd:d.natDegree≤5*N-3*S) (he:e.natDegree≤6*N-3*S):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    let H:=18*N-11*S
    let K:=12*N-7*S-1
    (FiveToSixCuspZetaFirstB3EqualitySupportRowOneLoad68 B c d e).coeff K=
      (3:k)*(((H:ℕ):k)*B.coeff D*c.coeff Cc*d.coeff V-
        ((E:ℕ):k)*B.coeff D^2*e.coeff E):=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let H:=18*N-11*S
  let K:=12*N-7*S-1
  have hB2e:=coeff_mul_mul_derivative_at_bounds68 B B e D D E hE hB hB he
  rw [show D+D+E-1=K by dsimp only [D,E,K];omega] at hB2e
  have hB2e':(B^2*derivative e).coeff K=
      B.coeff D^2*e.coeff E*((E:ℕ):k):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hB2e
  have hBcd:=coeff_mul_mul_derivative_at_bounds68 B c d D Cc V hV hB hc hd
  rw [show D+Cc+V-1=K by dsimp only [D,Cc,V,K];omega] at hBcd
  have hBc'd:=coeff_mul_mul_derivative_at_bounds68 B d c D V Cc hC hB hd hc
  rw [show D+V+Cc-1=K by dsimp only [D,Cc,V,K];omega] at hBc'd
  have hB'cd:=coeff_mul_mul_derivative_at_bounds68 c d B Cc V D hD hc hd hB
  rw [show Cc+V+D-1=K by dsimp only [D,Cc,V,K];omega] at hB'cd
  have hsumNat:V+Cc+3*D=H:=by dsimp only [D,Cc,V,H];omega
  have hsumCast:((V:ℕ):k)+((Cc:ℕ):k)+(3:k)*((D:ℕ):k)=((H:ℕ):k):=by
    have hh:=congrArg (fun n:ℕ↦(n:k)) hsumNat
    push_cast at hh
    exact hh
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowOneLoad68]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  rw [hB2e',hBcd]
  have hBc'd':(B*derivative c*d).coeff K=
      B.coeff D*c.coeff Cc*d.coeff V*((Cc:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hBc'd
  have hB'cd':(derivative B*c*d).coeff K=
      B.coeff D*c.coeff Cc*d.coeff V*((D:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hB'cd
  rw [hBc'd',hB'cd']
  linear_combination
    ((3:k)*B.coeff D*c.coeff Cc*d.coeff V)*hsumCast

def FiveToSixCuspZetaFirstB3EqualitySupportRowOneFreshJet68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let H:=18*N-11*S
  let K:=12*N-7*S-1
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rce:=R+(9/2*gamma:k)•e+(9/4*epsilon:k)•c
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  (((K+1:ℕ):k))*Y.coeff (K+1)=
      (2:k)*(A*derivative Rce).coeff K-
        (3:k)*(((H:ℕ):k)*B.coeff D*c.coeff Cc*d.coeff V-
          ((E:ℕ):k)*B.coeff D^2*e.coeff E) ∧
    (((K+1:ℕ):k))≠0

/-- Row one has nonzero transport slope on `Y.coeff (K+1)`, hence it only
solves a new jet at this wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_rowOne_freshJet68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ)
    (hN:0<N) (hTD:S-2*(3*N-2*S)≤3*N-2*S)
    (hD:0<3*N-2*S) (hC:0<4*N-2*S)
    (hV:0<5*N-3*S) (hE:0<6*N-3*S)
    (hB:B.natDegree≤3*N-2*S) (hc:c.natDegree≤4*N-2*S)
    (hd:d.natDegree≤5*N-3*S) (he:e.natDegree≤6*N-3*S)
    (hrow:FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68
      gamma epsilon A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualitySupportRowOneFreshJet68
      gamma epsilon A B c d e N S:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let H:=18*N-11*S
  let K:=12*N-7*S-1
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rce:=R+(9/2*gamma:k)•e+(9/4*epsilon:k)•c
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  have hload:=fiveToSix_zetaFirst_B3_equality_support_rowOne_load_top68
    (k:=k) B c d e N S hD hC hV hE hB hc hd he
  dsimp only [D,Cc,V,E,H,K] at hload
  have hbase:=fiveToSix_zetaFirst_B3_endpoint_rowOne_core_factor68
    (k:=k) A B c d e
  change FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e=
    -(2:k)•(A*derivative R)+derivative Y at hbase
  have hfactor:
      FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e-
          (9*gamma:k)•(A*derivative e)+
          (-(9/2*epsilon):k)•(A*derivative c)=
        -(2:k)•(A*derivative Rce)+derivative Y:=by
    rw [hbase]
    dsimp only [Rce]
    simp only [derivative_add,derivative_smul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_add,smul_sub,smul_smul]
    module
  have hr:=hrow
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68] at hr
  rw [hfactor] at hr
  simp only [coeff_add,coeff_smul,smul_eq_mul,coeff_derivative,hload] at hr
  have heq:
      (((K+1:ℕ):k))*Y.coeff (K+1)=
        (2:k)*(A*derivative Rce).coeff K-
          (3:k)*(((H:ℕ):k)*B.coeff D*c.coeff Cc*d.coeff V-
            ((E:ℕ):k)*B.coeff D^2*e.coeff E):=by
    push_cast at hr ⊢
    linear_combination hr
  have hKpos:0<K+1:=by dsimp only [K] at *;omega
  have hKcast:(((K+1:ℕ):k))≠0:=by exact_mod_cast (show K+1≠0 by omega)
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowOneFreshJet68,
    D,Cc,V,E,H,K,R,Rce,Y]
  exact ⟨heq,hKcast⟩

/-- The individual I4 identity is the first equation that constrains the
existing support resultant: off the coincidence `q=0`, it kills `Fce_q`
and leaves the displayed top-product relation. -/
theorem fiveToSix_zetaFirst_B3_equality_support_i4_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    let q:=9*N-7*S
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    q=0 ∨
      (0<q ∧ A.coeff (2*N)*B.coeff D^2*d.coeff V-
          (3:k)*B.coeff D*c.coeff Cc*e.coeff E=0 ∧
        B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0):=by
  let q:=9*N-7*S
  let p:=11*N-7*S
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hp0,hrest⟩
  rcases hp0 with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hctop' : c.coeff Cc ≠ 0 := by
    simpa [Cc, hGS] using hctop
  have hcuspEq' :
      A.coeff (2*N) * B.coeff D ^ 2 + (3:k) * c.coeff Cc ^ 2 = 0 := by
    simpa [D, Cc, hGS] using hcuspEq
  have hcontract:=fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68]
    at hcontract
  have hresult:=hcontract.2.2
  have hI4:=fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsource
  rcases hI4 with ⟨i4,hi4⟩
  have hFce:Fce=(3/8:k)•C i4:=by
    dsimp only [Fce]
    linear_combination hi4
  by_cases hq:q=0
  · exact Or.inl hq
  · right
    have hqpos:0<q:=by omega
    have hf:Fce.coeff q=0:=by
      rw [hFce,coeff_smul,coeff_C]
      simp only [if_neg (by omega),smul_zero]
    have hpNat:0<p:=by dsimp only [p,q];omega
    have hENat:0<E:=by dsimp only [E];omega
    have hpk:((p:ℕ):k)≠0:=by exact_mod_cast (show p≠0 by omega)
    have hEk:((E:ℕ):k)≠0:=by exact_mod_cast (show E≠0 by omega)
    have hprod:((p:ℕ):k)*((E:ℕ):k)*
        (A.coeff (2*N)*B.coeff D^2*d.coeff V-
          (3:k)*B.coeff D*c.coeff Cc*e.coeff E)=0:=by
      dsimp only [q,p,D,Cc,V,E,Fce] at hresult hf ⊢
      rw [hf,mul_zero,mul_zero,zero_add] at hresult
      exact hresult
    have hpe:((p:ℕ):k)*((E:ℕ):k)≠0:=mul_ne_zero hpk hEk
    have hrel:= (mul_eq_zero.mp hprod).resolve_left hpe
    have hsumProd:(3:k)*c.coeff Cc*
        (B.coeff D*e.coeff E+c.coeff Cc*d.coeff V)=0:=by
      linear_combination d.coeff V*hcuspEq'-hrel
    have h3c:(3:k)*c.coeff Cc≠0:=mul_ne_zero (by norm_num) hctop'
    exact ⟨hqpos,hrel,(mul_eq_zero.mp hsumProd).resolve_left h3c⟩

def FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EqualitySupportRowOneScalar68
      gamma epsilon A B c d e N S ∧
    FiveToSixCuspZetaFirstB3EqualitySupportRowOneFreshJet68
      gamma epsilon A B c d e N S ∧
    let q:=9*N-7*S
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    q=0 ∨
      (0<q ∧ A.coeff (2*N)*B.coeff D^2*d.coeff V-
          (3:k)*B.coeff D*c.coeff Cc*e.coeff E=0 ∧
        B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0)

/-- Full same-witness assembly of the literal row, its fresh-jet audit, and
the first genuinely constraining I4 split. -/
theorem fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S:=by
  have hsCopy:=hs
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
      ⟨hGS,hGamma0,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hraw:=fiveToSix_zetaFirst_loaded_uniform_rowOne68
    alpha gamma epsilon zeta eta terminal A B c d e N G S S S hsource
  have hGamma:3*S<4*N:=by omega
  have hlit:=fiveToSix_zetaFirst_B3_equality_support_rowOne_literal68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsource hGS
      hGamma hraw
  have hsupp:=hsCopy.1
  rcases hsupp with ⟨hstop,hTD⟩
  rw [hGS] at hB hc hd he
  have hD:0<3*N-2*S:=by omega
  have hC:0<4*N-2*S:=by omega
  have hV:0<5*N-3*S:=by omega
  have hE:0<6*N-3*S:=by omega
  have hd':d.natDegree≤5*N-3*S:=by omega
  have he':e.natDegree≤6*N-3*S:=by omega
  have hfresh:=fiveToSix_zetaFirst_B3_equality_support_rowOne_freshJet68
    gamma epsilon A B c d e N S hN
      (by simpa only using hTD) hD hC hV hE hB hc hd' he' hlit
  have hsplit:=fiveToSix_zetaFirst_B3_equality_support_i4_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsCopy
  exact ⟨hsCopy,hlit,hfresh,hsplit⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_rowOne_literal68
#print axioms fiveToSix_zetaFirst_B3_equality_support_rowOne_freshJet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_i4_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportRowOne68

end Max11DegreeRoutes
