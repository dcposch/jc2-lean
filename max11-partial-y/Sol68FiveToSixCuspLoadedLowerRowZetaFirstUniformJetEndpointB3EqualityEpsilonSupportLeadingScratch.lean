import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportRowOneScratch

/-! # The same-witness leading edge scalar after the support row

The retained `J` degree drop kills its actual top coefficient.  Together
with the cusp equation this is exactly `4*A_top*B_top^3+27*d_top*e_top=0`.
On the positive compensated-I4 branch, the row-one packet then gives the
additional division-free scalar `4*B_top^2*c_top+9*d_top^2=0`.  The
coefficient-zero coincidence `q=0` is kept verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The top coefficient of the already-retained `J` state, with no source
reselection and with the coincident support wall allowed. -/
theorem fiveToSix_zetaFirst_B3_equality_support_leading_scalar68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    let D:=3*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    4*A.coeff (2*N)*B.coeff D^3+27*d.coeff V*e.coeff E=0:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let p:=11*N-7*S
  let K:=11*N-6*S
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  have hloaded:=hs.1
  have hsourceData:=fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded
  rcases hsourceData with ⟨hGS,hGamma,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  rcases hloaded with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  rcases hstop with ⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩
  let w:=2*D
  let T:=S-w
  let t:=min D T
  have htT:t=T:=by dsimp only [t];exact Nat.min_eq_right hTD
  have hstate':=hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hjidx:5*N-2*S-(t-1)-1=p:=by
    dsimp only [D,w,T] at htT
    dsimp only [p]
    omega
  rw [hjidx] at hstate'
  have hJ:J.natDegree≤p:=by exact hstate'.2
  have hJzero:J.coeff K=0:=by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp only [p,K] at hJ ⊢
    omega
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by
    dsimp only [V]
    rw [hGS] at hd
    omega
  have he':e.natDegree≤E:=by
    dsimp only [E]
    rw [hGS] at he
    omega
  have hBc2: (B*c^2).coeff K=B.coeff D*c.coeff Cc^2:=by
    have h:=coeff_mul_mul_at_bounds68 B c c D Cc Cc hB' hc' hc'
    rw [show D+Cc+Cc=K by dsimp only [D,Cc,K];omega] at h
    simpa only [pow_two,mul_assoc] using h
  have hB3deg:(B^3).natDegree≤3*D:=by compute_degree;omega
  have hB3: (B^3).coeff (3*D)=B.coeff D^3:=by
    simpa only [Nat.mul_comm] using coeff_pow_at_bound68 B D 3 hB'
  have hAB3: (A*B^3).coeff K=A.coeff (2*N)*B.coeff D^3:=by
    have h:=coeff_mul_at_bounds68 A (B^3) (2*N) (3*D) hA hB3deg
    rw [show 2*N+3*D=K by dsimp only [D,K];omega,hB3] at h
    exact h
  have hde:(d*e).coeff K=d.coeff V*e.coeff E:=by
    have h:=coeff_mul_at_bounds68 d e V E hd' he'
    rw [show V+E=K by dsimp only [V,E,K];omega] at h
    exact h
  have hcuspEq':A.coeff (2*N)*B.coeff D^2+
      (3:k)*c.coeff Cc^2=0:=by
    simpa [D,Cc,hGS] using hcuspEq
  dsimp only [J] at hJzero
  simp only [coeff_sub,coeff_smul,smul_eq_mul,hBc2,hAB3,hde] at hJzero
  dsimp only [D,V,E]
  linear_combination (3:k)*B.coeff D*hcuspEq'-(9:k)*hJzero

/-- Small division-free elimination used after the positive `q` split. -/
theorem fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
    (A0 B0 c0 d0 e0:k) (hc0:c0≠0)
    (hcusp:A0*B0^2+3*c0^2=0)
    (hsum:B0*e0+c0*d0=0)
    (hlead:4*A0*B0^3+27*d0*e0=0):
    4*B0^2*c0+9*d0^2=0:=by
  have hprod:(-3*c0)*(4*B0^2*c0+9*d0^2)=0:=by
    linear_combination B0*hlead-(4*B0^2)*hcusp-(27*d0)*hsum
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) hc0)

/-- Same-witness source packet: the leading scalar is unconditional, while
the positive compensated-I4 branch carries the extra cusp resultant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_leading_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    let q:=9*N-7*S
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    (4*A.coeff (2*N)*B.coeff D^3+27*d.coeff V*e.coeff E=0) ∧
      (q=0 ∨ (0<q ∧
        A.coeff (2*N)*B.coeff D^2*d.coeff V-
          (3:k)*B.coeff D*c.coeff Cc*e.coeff E=0 ∧
        B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0 ∧
        4*B.coeff D^2*c.coeff Cc+9*d.coeff V^2=0)):=by
  let q:=9*N-7*S
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  have hlead:=fiveToSix_zetaFirst_B3_equality_support_leading_scalar68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
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
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hctop':c.coeff Cc≠0:=by simpa [Cc,hGS] using hctop
  have hcuspEq':A.coeff (2*N)*B.coeff D^2+
      (3:k)*c.coeff Cc^2=0:=by simpa [D,Cc,hGS] using hcuspEq
  have hsplit:=hs.2.2.2
  dsimp only [q,D,Cc,V,E] at hsplit hlead ⊢
  refine ⟨hlead,?_⟩
  rcases hsplit with hq0|hqpos
  · exact Or.inl hq0
  · right
    rcases hqpos with ⟨hq,hrel,hsum⟩
    exact ⟨hq,hrel,hsum,
      fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
        (A.coeff (2*N)) (B.coeff D) (c.coeff Cc) (d.coeff V)
          (e.coeff E) hctop' hcuspEq' hsum hlead⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_leading_scalar68
#print axioms fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_leading_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68

end Max11DegreeRoutes
