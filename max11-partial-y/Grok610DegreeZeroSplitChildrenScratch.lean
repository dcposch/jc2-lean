import Grok610DegreeZeroSourceWrapperScratch

/-! # Child analysis of the `(6,10)` degree-zero post-collapse split

The source wrapper supplies the order-`69` head
`7583143431241728 p32^3 q41` and the split `p32(a) = 0 ∨ q41(a) = 0`.
This file instantiates that split and consumes two already landed heads
rather than re-deriving them:

* the fourth-tail post-collapse head, specialized on each child as in
  `Sol610ScaleTwoDegreeZeroPostCollapseHeadSplitScratch`;
* the next coefficient of the *same* degree-zero compact numerator,
  which is the explicit order-`70` polynomial recorded below.

On `p32(a) = 0` the order-`69` monomial is divisible by `h0^3`, so the
simple-pole obstruction peels one more power of the linear scale and
forces the order-`70` head to vanish.  Combined with the fourth-tail
child `q41(a) = 0 ∨ p21(a) = 0` this is `p21(a) = 0 ∨ (q41(a) = 0 ∧
q3(a) = 0)`.  On `q41(a) = 0` the order-`70` head mixes `q41'(a)` and
is not used; the honest leftover is the landed five-term cofactor, or
the same `p32(a) = 0` grandchild already analysed.

Neither child is False.  The Jacobian coefficient tower is already
exhausted at the inhomogeneous degree-`0` row.  The next unused
compact-numerator order on the live `p32 = p21 = 0` grandchild is the
order-`71` coefficient of the same quotient.

No total-degree or twice-prime theorem is used, and no chamber is
closed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000

section LinearDvdAndPoleFive610

variable {k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem linearPolynomial_dvd_of_eval_eq_zero_610
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : f.eval a = 0) : h ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h = C c * (X - C a) := by
    calc
      h = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

omit [CharZero k] in
/-- Cancel one polynomial power of a linear clearing. -/
theorem algebraMap_cancel_one_clearing_610
    (h old new : k[X]) (A : RatFunc k) (r : ℕ) (hh : h ≠ 0)
    (hfact : old = h * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h) ^ (r + 1) * A) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h) ^ r * A := by
  let hR : RatFunc k := algebraMap k[X] (RatFunc k) h
  have hhR : hR ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hfact
  apply mul_left_cancel₀ hhR
  calc
    hR * algebraMap k[X] (RatFunc k) new =
        algebraMap k[X] (RatFunc k) old := by
      dsimp only [hR]
      simpa only [map_mul] using hmapped.symm
    _ = hR ^ (r + 1) * A := hclear
    _ = hR * (hR ^ r * A) := by
      rw [add_comm r 1, pow_add, pow_one]
      ring

local instance degreeZeroSplitChildrenHahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A rational function cleared by exactly five powers of a linear local
parameter cannot have a nonzero exponent-`-5` head when its derivative is a
simple pole. -/
theorem localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho 5 hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho 5 hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hminusSix :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff (-6 : ℚ) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-6 : ℚ)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle,
      HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne (by norm_num :
        (-6 : ℚ) ≠ -(1 : ℚ)), smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-5 : ℚ) = 0 := by
    norm_num at hderivBoundary
    rw [hminusSix] at hderivBoundary
    have hfive : (5 : k) ≠ 0 := by norm_num
    have hprod : (5 : k) * (ratFuncAtHahn46 a rho).coeff (-5 : ℚ) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hfive
  norm_num at hrhoBoundary
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ 5)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 5 hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

end LinearDvdAndPoleFive610

section DegreeZeroOrderOneHead610

set_option maxHeartbeats 800000000

variable {R : Type*} [CommRing R]

/-- The coefficient of `h` in the degree-zero post-collapse quotient. -/
def degreeZeroPostCollapseJetOrderOne610
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) : R :=
  45498860587450368*a42*p21*p32*q41 + 17062072720293888*a42*p32^2*q3 - 49290432303071232*a42*p32^2*q41*w1 - 38999023360671744*p1*p21*q41 - 29249267520503808*p1*p32*q3 + 45498860587450368*p1*p32*q41*w1 - 14624633760251904*p21^2*q3 + 22749430293725184*p21^2*q41*w1 + 28436787867156480*p21*p32^2*q53 + 34124145440587776*p21*p32*q3*w1 - 49290432303071232*p21*p32*q41*w1^2 + 6503598706655232*p32^5 - 7188188044197888*p32^4*u2 - 20537680126279680*p32^3*q53*w1 - 18483912113651712*p32^2*q3*w1^2 + 26014394826620928*p32^2*q41*w1^3

/-- The remaining factor after `Head0 + h · OrderOne` is removed. -/
def degreeZeroPostCollapseJetOrderTwoPlus610
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
  -1000057340805120*a42^7*h^4*lambda - 15556447523635200*a42^7*h^4*w1 + 21584570939043840*a42^6*h^4*lambda*w1^2 + 18667737028362240*a42^6*h^4*s2*w1 + 63954284263833600*a42^6*h^4*w1^3 + 23334671285452800*a42^6*h^3*p32 - 3161471593512960*a42^6*h^3*u2 - 16258996766638080*a42^5*b63*h^3*w1 - 77344712531573760*a42^5*h^4*lambda*w1^4 - 115117711674900480*a42^5*h^4*s2*w1^3 - 34375427791810560*a42^5*h^4*w1^5 + 8129498383319040*a42^5*h^3*lambda*p21 - 42002408313815040*a42^5*h^3*lambda*p32*w1 - 27098327944396800*a42^5*h^3*p1 + 99360535796121600*a42^5*h^3*p21*w1 - 21678662355517440*a42^5*h^3*p32*s2 - 221679377211801600*a42^5*h^3*p32*w1^2 + 49002809699450880*a42^5*h^3*u2*w1^2 + 3251799353327616*a42^5*h^2*q53 + 70004013856358400*a42^4*b63*h^3*w1^3 + 19510796119965696*a42^4*b63*h^2*p32 - 9755398059982848*a42^4*h^4*lambda*p0 + 105274747612419840*a42^4*h^4*lambda*w1^6 - 86714649422069760*a42^4*h^4*p0*w1 + 206252566750863360*a42^4*h^4*s2*w1^5 - 66841109595187200*a42^4*h^4*w1^7 + 40647491916595200*a42^4*h^3*lambda*p1*w1 - 105006020784537600*a42^4*h^3*lambda*p21*w1^2 + 215845709390438400*a42^4*h^3*lambda*p32*w1^3 + 26014394826620928*a42^4*h^3*p1*s2 + 146782609698816000*a42^4*h^3*p1*w1^2 - 108393311777587200*a42^4*h^3*p21*s2*w1 - 194455594045440000*a42^4*h^3*p21*w1^3 + 280016055425433600*a42^4*h^3*p32*s2*w1^2 + 209849995240704000*a42^4*h^3*p32*w1^4 - 125909997144422400*a42^4*h^3*u2*w1^4 + 20323745958297600*a42^4*h^2*lambda*p32^2 - 135491639721984000*a42^4*h^2*p21*p32 + 22762595473293312*a42^4*h^2*p21*u2 + 248401339490304000*a42^4*h^2*p32^2*w1 - 94844147805388800*a42^4*h^2*p32*u2*w1 - 33872909930496000*a42^4*h^2*q53*w1^2 - 3080652018941952*a42^4*h*q3 + 13007197413310464*a42^4*h*q41*w1 - 86338283756175360*a42^3*b63*h^3*w1^5 - 24645216151535616*a42^3*b63*h^2*p1 + 78043184479862784*a42^3*b63*h^2*p21*w1 - 162589967666380800*a42^3*b63*h^2*p32*w1^2 + 81294983833190400*a42^3*h^4*lambda*p0*w1^2 - 68929894270036800*a42^3*h^4*lambda*w1^8 + 104057579306483712*a42^3*h^4*p0*s2*w1 + 60218506543104000*a42^3*h^4*p0*w1^3 - 160418663028449280*a42^3*h^4*s2*w1^7 + 85098634901280000*a42^3*h^4*w1^9 - 140008027712716800*a42^3*h^3*lambda*p1*w1^3 + 215845709390438400*a42^3*h^3*lambda*p21*w1^4 - 309378850126295040*a42^3*h^3*lambda*p32*w1^5 + 130071974133104640*a42^3*h^3*p0*p32 - 28752752176791552*a42^3*h^3*p0*u2 - 216786623555174400*a42^3*h^3*p1*s2*w1^2 - 19445559404544000*a42^3*h^3*p1*w1^4 + 373354740567244800*a42^3*h^3*p21*s2*w1^3 - 47965713197875200*a42^3*h^3*p21*w1^5 - 575588558374502400*a42^3*h^3*p32*s2*w1^4 + 143230949132544000*a42^3*h^3*p32*w1^6 + 1895785857810432*a42^3*h^3*q1 + 120313997271336960*a42^3*h^3*u2*w1^6 - 39021592239931392*a42^3*h^2*lambda*p1*p32 - 19510796119965696*a42^3*h^2*lambda*p21^2 + 162589967666380800*a42^3*h^2*lambda*p21*p32*w1 - 210012041569075200*a42^3*h^2*lambda*p32^2*w1^2 + 130071974133104640*a42^3*h^2*p1*p21 - 346858597688279040*a42^3*h^2*p1*p32*w1 + 91050381893173248*a42^3*h^2*p1*u2*w1 - 173429298844139520*a42^3*h^2*p21^2*w1 + 104057579306483712*a42^3*h^2*p21*p32*s2 + 587130438795264000*a42^3*h^2*p21*p32*w1^2 - 189688295610777600*a42^3*h^2*p21*u2*w1^2 - 216786623555174400*a42^3*h^2*p32^2*s2*w1 - 388911188090880000*a42^3*h^2*p32^2*w1^3 + 326685397996339200*a42^3*h^2*p32*u2*w1^3 - 8215072050511872*a42^3*h^2*q2*w1 + 58336678213632000*a42^3*h^2*q53*w1^4 - 20537680126279680*a42^3*h*p21*q53 - 90327759814656000*a42^3*h*p32^3 + 45525190946586624*a42^3*h*p32^2*u2 + 65035987066552320*a42^3*h*p32*q53*w1 + 19510796119965696*a42^3*h*q3*w1^2 - 36131103925862400*a42^3*h*q41*w1^3 - 16430144101023744*a42^3*p32*q41 - 73935648454606848*a42^2*b63*h^3*p0*w1 + 44196978589470720*a42^2*b63*h^3*w1^7 + 117064776719794176*a42^2*b63*h^2*p1*w1^2 - 162589967666380800*a42^2*b63*h^2*p21*w1^3 + 210012041569075200*a42^2*b63*h^2*p32*w1^4 - 73935648454606848*a42^2*b63*h*p21*p32 + 117064776719794176*a42^2*b63*h*p32^2*w1 - 105006020784537600*a42^2*h^4*lambda*p0*w1^4 + 23359575280401360*a42^2*h^4*lambda*w1^10 - 216786623555174400*a42^2*h^4*p0*s2*w1^3 + 93338685141811200*a42^2*h^4*p0*w1^5 + 61271017128921600*a42^2*h^4*s2*w1^9 - 37752848938022400*a42^2*h^4*w1^11 + 36967824227303424*a42^2*h^3*lambda*p0*p21 - 117064776719794176*a42^2*h^3*lambda*p0*p32*w1 + 129507425634263040*a42^2*h^3*lambda*p1*w1^5 - 154689425063147520*a42^2*h^3*lambda*p21*w1^6 + 180470995907005440*a42^2*h^3*lambda*p32*w1^7 - 123226080757678080*a42^2*h^3*p0*p1 + 205376801262796800*a42^2*h^3*p0*p21*w1 - 98580864606142464*a42^2*h^3*p0*p32*s2 - 227625954732933120*a42^2*h^3*p0*p32*w1^2 + 136575572839759872*a42^2*h^3*p0*u2*w1^2 + 280016055425433600*a42^2*h^3*p1*s2*w1^4 - 131905711294156800*a42^2*h^3*p1*w1^6 - 345353135024701440*a42^2*h^3*p21*s2*w1^5 + 171877138959052800*a42^2*h^3*p21*w1^7 + 412505133501726720*a42^2*h^3*p32*s2*w1^6 - 213056036834659200*a42^2*h^3*p32*w1^8 - 6161304037883904*a42^2*h^3*q1*w1^2 - 52637373806209920*a42^2*h^3*u2*w1^8 + 18483912113651712*a42^2*h^2*lambda*p1^2 - 117064776719794176*a42^2*h^2*lambda*p1*p21*w1 + 243884951499571200*a42^2*h^2*lambda*p1*p32*w1^2 + 121942475749785600*a42^2*h^2*lambda*p21^2*w1^2 - 420024083138150400*a42^2*h^2*lambda*p21*p32*w1^3 + 323768564085657600*a42^2*h^2*lambda*p32^2*w1^4 + 28436787867156480*a42^2*h^2*p0*q53 + 102688400631398400*a42^2*h^2*p1^2*w1 - 98580864606142464*a42^2*h^2*p1*p21*s2 - 227625954732933120*a42^2*h^2*p1*p21*w1^2 + 312172737919451136*a42^2*h^2*p1*p32*s2*w1 + 180655519629312000*a42^2*h^2*p1*p32*w1^3 - 189688295610777600*a42^2*h^2*p1*u2*w1^3 + 156086368959725568*a42^2*h^2*p21^2*s2*w1 + 90327759814656000*a42^2*h^2*p21^2*w1^3 - 650359870665523200*a42^2*h^2*p21*p32*s2*w1^2 - 58336678213632000*a42^2*h^2*p21*p32*w1^4 + 245014048497254400*a42^2*h^2*p21*u2*w1^4 + 560032110850867200*a42^2*h^2*p32^2*s2*w1^3 - 71948569796812800*a42^2*h^2*p32^2*w1^5 - 302183993146613760*a42^2*h^2*p32*u2*w1^5 + 13007197413310464*a42^2*h^2*q2*w1^3 - 35974284898406400*a42^2*h^2*q53*w1^6 - 58532388359897088*a42^2*h*lambda*p21*p32^2 + 81294983833190400*a42^2*h*lambda*p32^3*w1 + 195107961199656960*a42^2*h*p1*p32^2 - 86258256530374656*a42^2*h*p1*p32*u2 - 61613040378839040*a42^2*h*p1*q53*w1 + 195107961199656960*a42^2*h*p21^2*p32 - 43129128265187328*a42^2*h*p21^2*u2 - 520287896532418560*a42^2*h*p21*p32^2*w1 + 273151145679519744*a42^2*h*p21*p32*u2*w1 + 97553980599828480*a42^2*h*p21*q53*w1^2 + 52028789653241856*a42^2*h*p32^3*s2 + 293565219397632000*a42^2*h*p32^3*w1^2 - 284532443416166400*a42^2*h*p32^2*u2*w1^2 + 11374715146862592*a42^2*h*p32*q2 - 135491639721984000*a42^2*h*p32*q53*w1^3 - 20323745958297600*a42^2*h*q3*w1^4 + 28001605542543360*a42^2*h*q41*w1^5 + 22749430293725184*a42^2*p1*q41 + 17062072720293888*a42^2*p21*q3 - 49290432303071232*a42^2*p21*q41*w1 - 30806520189419520*a42^2*p32^2*q53 - 36967824227303424*a42^2*p32*q3*w1 + 78043184479862784*a42^2*p32*q41*w1^2 + 78043184479862784*a42*b63*h^3*p0*w1^3 - 10026166439278080*a42*b63*h^3*w1^9 + 68248290881175552*a42*b63*h^2*p0*p32 - 81294983833190400*a42*b63*h^2*p1*w1^4 + 84004816627630080*a42*b63*h^2*p21*w1^5 - 86338283756175360*a42*b63*h^2*p32*w1^6 + 68248290881175552*a42*b63*h*p1*p21 - 147871296909213696*a42*b63*h*p1*p32*w1 - 73935648454606848*a42*b63*h*p21^2*w1 + 234129553439588352*a42*b63*h*p21*p32*w1^2 - 162589967666380800*a42*b63*h*p32^2*w1^3 - 24645216151535616*a42*b63*p32^3 - 17062072720293888*a42*h^4*lambda*p0^2 + 43169141878087680*a42*h^4*lambda*p0*w1^6 - 3952251373199220*a42*h^4*lambda*w1^12 - 37915717156208640*a42*h^4*p0^2*w1 + 112006422170173440*a42*h^4*p0*s2*w1^5 - 68522447425536000*a42*h^4*p0*w1^7 - 11325854681406720*a42*h^4*s2*w1^11 + 7431583778665200*a42*h^4*w1^13 + 73935648454606848*a42*h^3*lambda*p0*p1*w1 - 117064776719794176*a42*h^3*lambda*p0*p21*w1^2 + 162589967666380800*a42*h^3*lambda*p0*p32*w1^3 - 44196978589470720*a42*h^3*lambda*p1*w1^7 + 45117748976751360*a42*h^3*lambda*p21*w1^8 - 45953262846691200*a42*h^3*lambda*p32*w1^9 + 90997721174900736*a42*h^3*p0*p1*s2 + 20537680126279680*a42*h^3*p0*p1*w1^2 - 197161729212284928*a42*h^3*p0*p21*s2*w1 + 43357324711034880*a42*h^3*p0*p21*w1^3 + 312172737919451136*a42*h^3*p0*p32*s2*w1^2 - 112909699768320000*a42*h^3*p0*p32*w1^4 - 94844147805388800*a42*h^3*p0*u2*w1^4 - 115117711674900480*a42*h^3*p1*s2*w1^6 + 70592396358182400*a42*h^3*p1*w1^8 + 117858609571921920*a42*h^3*p21*s2*w1^7 - 72411202061452800*a42*h^3*p21*w1^9 - 120313997271336960*a42*h^3*p32*s2*w1^8 + 74035812364113600*a42*h^3*p32*w1^10 + 3251799353327616*a42*h^3*q1*w1^4 + 10722427997561280*a42*h^3*u2*w1^10 + 36967824227303424*a42*h^2*lambda*p0*p32^2 - 58532388359897088*a42*h^2*lambda*p1^2*w1^2 + 162589967666380800*a42*h^2*lambda*p1*p21*w1^3 - 210012041569075200*a42*h^2*lambda*p1*p32*w1^4 - 105006020784537600*a42*h^2*lambda*p21^2*w1^4 + 259014851268526080*a42*h^2*lambda*p21*p32*w1^5 - 154689425063147520*a42*h^2*lambda*p32^2*w1^6 - 246452161515356160*a42*h^2*p0*p21*p32 + 79623006028038144*a42*h^2*p0*p21*u2 + 205376801262796800*a42*h^2*p0*p32^2*w1 - 172516513060749312*a42*h^2*p0*p32*u2*w1 - 61613040378839040*a42*h^2*p0*q53*w1^2 - 98580864606142464*a42*h^2*p1^2*s2*w1 + 21678662355517440*a42*h^2*p1^2*w1^3 + 312172737919451136*a42*h^2*p1*p21*s2*w1^2 - 112909699768320000*a42*h^2*p1*p21*w1^4 - 433573247110348800*a42*h^2*p1*p32*s2*w1^3 + 186677370283622400*a42*h^2*p1*p32*w1^5 + 98005619398901760*a42*h^2*p1*u2*w1^5 - 216786623555174400*a42*h^2*p21^2*s2*w1^3 + 93338685141811200*a42*h^2*p21^2*w1^5 + 560032110850867200*a42*h^2*p21*p32*s2*w1^4 - 263811422588313600*a42*h^2*p21*p32*w1^6 - 9749755840167936*a42*h^2*p21*q1 - 100727997715537920*a42*h^2*p21*u2*w1^6 - 345353135024701440*a42*h^2*p32^2*s2*w1^5 + 171877138959052800*a42*h^2*p32^2*w1^7 + 11374715146862592*a42*h^2*p32*q1*w1 + 103126283375431680*a42*h^2*p32*u2*w1^7 - 5419665588879360*a42*h^2*q2*w1^5 + 9207703872806400*a42*h^2*q53*w1^8 + 73935648454606848*a42*h*lambda*p1*p21*p32 - 117064776719794176*a42*h*lambda*p1*p32^2*w1 + 12322608075767808*a42*h*lambda*p21^3 - 117064776719794176*a42*h*lambda*p21^2*p32*w1 + 243884951499571200*a42*h*lambda*p21*p32^2*w1^2 - 140008027712716800*a42*h*lambda*p32^3*w1^3 - 29249267520503808*a42*h*p0*q3 + 45498860587450368*a42*h*p0*q41*w1 - 123226080757678080*a42*h*p1^2*p32 + 39811503014019072*a42*h*p1^2*u2 - 123226080757678080*a42*h*p1*p21^2 + 410753602525593600*a42*h*p1*p21*p32*w1 - 172516513060749312*a42*h*p1*p21*u2*w1 - 98580864606142464*a42*h*p1*p32^2*s2 - 227625954732933120*a42*h*p1*p32^2*w1^2 + 273151145679519744*a42*h*p1*p32*u2*w1^2 - 19499511680335872*a42*h*p1*q2 + 65035987066552320*a42*h*p1*q53*w1^3 + 68458933754265600*a42*h*p21^3*w1 - 98580864606142464*a42*h*p21^2*p32*s2 - 227625954732933120*a42*h*p21^2*p32*w1^2 + 136575572839759872*a42*h*p21^2*u2*w1^2 + 312172737919451136*a42*h*p21*p32^2*s2*w1 + 180655519629312000*a42*h*p21*p32^2*w1^3 - 379376591221555200*a42*h*p21*p32*u2*w1^3 + 22749430293725184*a42*h*p21*q2*w1 - 67745819860992000*a42*h*p21*q53*w1^4 - 216786623555174400*a42*h*p32^3*s2*w1^2 - 19445559404544000*a42*h*p32^3*w1^4 + 245014048497254400*a42*h*p32^2*u2*w1^4 - 24645216151535616*a42*h*p32*q2*w1^2 + 70004013856358400*a42*h*p32*q53*w1^5 + 7000401385635840*a42*h*q3*w1^6 - 8222693691064320*a42*h*q41*w1^7 - 9755398059982848*a42*lambda*p32^4 + 56873575734312960*a42*p1*p32*q53 + 34124145440587776*a42*p1*q3*w1 - 49290432303071232*a42*p1*q41*w1^2 + 28436787867156480*a42*p21^2*q53 + 130071974133104640*a42*p21*p32^3 - 86258256530374656*a42*p21*p32^2*u2 - 123226080757678080*a42*p21*p32*q53*w1 - 36967824227303424*a42*p21*q3*w1^2 + 52028789653241856*a42*p21*q41*w1^3 - 86714649422069760*a42*p32^4*w1 + 91050381893173248*a42*p32^3*u2*w1 + 97553980599828480*a42*p32^2*q53*w1^2 + 39021592239931392*a42*p32*q3*w1^3 - 54196655888793600*a42*p32*q41*w1^4 - 16258996766638080*b63*h^3*p0*w1^5 + 835513869939840*b63*h^3*w1^11 - 58498535041007616*b63*h^2*p0*p1 + 68248290881175552*b63*h^2*p0*p21*w1 - 73935648454606848*b63*h^2*p0*p32*w1^2 + 14000802771271680*b63*h^2*p1*w1^6 - 12334040536596480*b63*h^2*p21*w1^7 + 11049244647367680*b63*h^2*p32*w1^8 + 34124145440587776*b63*h*p1^2*w1 - 73935648454606848*b63*h*p1*p21*w1^2 + 78043184479862784*b63*h*p1*p32*w1^3 + 39021592239931392*b63*h*p21^2*w1^3 - 81294983833190400*b63*h*p21*p32*w1^4 + 42002408313815040*b63*h*p32^2*w1^5 + 34124145440587776*b63*p1*p32^2 + 34124145440587776*b63*p21^2*p32 - 73935648454606848*b63*p21*p32^2*w1 + 39021592239931392*b63*p32^3*w1^2 + 18483912113651712*h^4*lambda*p0^2*w1^2 - 5524622323683840*h^4*lambda*p0*w1^8 + 264207280442805*h^4*lambda*w1^14 + 45498860587450368*h^4*p0^2*s2*w1 - 27383573501706240*h^4*p0^2*w1^3 - 16445387382128640*h^4*p0*s2*w1^7 + 10912834219622400*h^4*p0*w1^9 + 810718230399840*h^4*s2*w1^13 - 547985470548040*h^4*w1^15 - 39021592239931392*h^3*lambda*p0*p1*w1^3 + 40647491916595200*h^3*lambda*p0*p21*w1^4 - 42002408313815040*h^3*lambda*p0*p32*w1^5 + 5013083219639040*h^3*lambda*p1*w1^9 - 4595326284669120*h^3*lambda*p21*w1^10 + 4247195505527520*h^3*lambda*p32*w1^11 + 56873575734312960*h^3*p0^2*p32 - 34124145440587776*h^3*p0^2*u2 - 98580864606142464*h^3*p0*p1*s2*w1^2 + 59616321477672960*h^3*p0*p1*w1^4 + 104057579306483712*h^3*p0*p21*s2*w1^3 - 63229431870259200*h^3*p0*p21*w1^5 - 108393311777587200*h^3*p0*p32*s2*w1^4 + 66114901975449600*h^3*p0*p32*w1^6 + 58498535041007616*h^3*p0*q1 + 16334269899816960*h^3*p0*u2*w1^6 + 14732326196490240*h^3*p1*s2*w1^8 - 9747661815964800*h^3*p1*w1^10 - 13368221919037440*h^3*p21*s2*w1^9 + 8819313071587200*h^3*p21*w1^11 + 12254203425784320*h^3*p32*s2*w1^10 - 8061806283640200*h^3*p32*w1^12 - 451638799073280*h^3*q1*w1^6 - 825843570519240*h^3*u2*w1^12 - 34124145440587776*h^2*lambda*p0*p1*p32 - 17062072720293888*h^2*lambda*p0*p21^2 + 73935648454606848*h^2*lambda*p0*p21*p32*w1 - 58532388359897088*h^2*lambda*p0*p32^2*w1^2 + 20323745958297600*h^2*lambda*p1^2*w1^4 - 42002408313815040*h^2*lambda*p1*p21*w1^5 + 43169141878087680*h^2*lambda*p1*p32*w1^6 + 21584570939043840*h^2*lambda*p21^2*w1^6 - 44196978589470720*h^2*lambda*p21*p32*w1^7 + 22558874488375680*h^2*lambda*p32^2*w1^8 + 113747151468625920*h^2*p0*p1*p21 - 75831434312417280*h^2*p0*p1*p32*w1 + 79623006028038144*h^2*p0*p1*u2*w1 - 37915717156208640*h^2*p0*p21^2*w1 + 90997721174900736*h^2*p0*p21*p32*s2 + 20537680126279680*h^2*p0*p21*p32*w1^2 - 86258256530374656*h^2*p0*p21*u2*w1^2 - 98580864606142464*h^2*p0*p32^2*s2*w1 + 21678662355517440*h^2*p0*p32^2*w1^3 + 91050381893173248*h^2*p0*p32*u2*w1^3 - 19499511680335872*h^2*p0*q2*w1 + 16258996766638080*h^2*p0*q53*w1^4 + 52028789653241856*h^2*p1^2*s2*w1^3 - 31614715935129600*h^2*p1^2*w1^5 - 108393311777587200*h^2*p1*p21*s2*w1^4 + 66114901975449600*h^2*p1*p21*w1^6 + 112006422170173440*h^2*p1*p32*s2*w1^5 - 68522447425536000*h^2*p1*p32*w1^7 - 9749755840167936*h^2*p1*q1*w1 - 14389713959362560*h^2*p1*u2*w1^7 + 56003211085086720*h^2*p21^2*s2*w1^5 - 34261223712768000*h^2*p21^2*w1^7 - 115117711674900480*h^2*p21*p32*s2*w1^6 + 70592396358182400*h^2*p21*p32*w1^8 + 5687357573431296*h^2*p21*q1*w1^2 + 12890785421928960*h^2*p21*u2*w1^8 + 58929304785960960*h^2*p32^2*s2*w1^7 - 36205601030726400*h^2*p32^2*w1^9 - 4107536025255936*h^2*p32*q1*w1^3 - 11697194179157760*h^2*p32*u2*w1^9 + 666704893870080*h^2*q2*w1^7 - 835513869939840*h^2*q53*w1^10 - 17062072720293888*h*lambda*p1^2*p21 + 36967824227303424*h*lambda*p1^2*p32*w1 + 36967824227303424*h*lambda*p1*p21^2*w1 - 117064776719794176*h*lambda*p1*p21*p32*w1^2 + 81294983833190400*h*lambda*p1*p32^2*w1^3 - 19510796119965696*h*lambda*p21^3*w1^2 + 81294983833190400*h*lambda*p21^2*p32*w1^3 - 105006020784537600*h*lambda*p21*p32^2*w1^4 + 43169141878087680*h*lambda*p32^3*w1^5 - 48748779200839680*h*p0*p21*q53 - 41075360252559360*h*p0*p32^3 + 39811503014019072*h*p0*p32^2*u2 + 56873575734312960*h*p0*p32*q53*w1 + 17062072720293888*h*p0*q3*w1^2 - 16430144101023744*h*p0*q41*w1^3 + 18957858578104320*h*p1^3 - 37915717156208640*h*p1^2*p21*w1 + 45498860587450368*h*p1^2*p32*s2 + 10268840063139840*h*p1^2*p32*w1^2 - 43129128265187328*h*p1^2*u2*w1^2 + 45498860587450368*h*p1*p21^2*s2 + 10268840063139840*h*p1*p21^2*w1^2 - 197161729212284928*h*p1*p21*p32*s2*w1 + 43357324711034880*h*p1*p21*p32*w1^3 + 91050381893173248*h*p1*p21*u2*w1^3 + 156086368959725568*h*p1*p32^2*s2*w1^2 - 56454849884160000*h*p1*p32^2*w1^4 - 94844147805388800*h*p1*p32*u2*w1^4 + 11374715146862592*h*p1*q2*w1^2 - 13549163972198400*h*p1*q53*w1^5 - 32860288202047488*h*p21^3*s2*w1 + 7226220785172480*h*p21^3*w1^3 + 156086368959725568*h*p21^2*p32*s2*w1^2 - 56454849884160000*h*p21^2*p32*w1^4 - 47422073902694400*h*p21^2*u2*w1^4 - 216786623555174400*h*p21*p32^2*s2*w1^3 + 93338685141811200*h*p21*p32^2*w1^5 + 98005619398901760*h*p21*p32*u2*w1^5 - 8215072050511872*h*p21*q2*w1^3 + 11667335642726400*h*p21*q53*w1^6 + 93338685141811200*h*p32^3*s2*w1^4 - 43968570431385600*h*p32^3*w1^6 - 4874877920083968*h*p32^2*q1 - 50363998857768960*h*p32^2*u2*w1^6 + 6503598706655232*h*p32*q2*w1^4 - 10278367113830400*h*p32*q53*w1^7 - 770877533537280*h*q3*w1^8 + 818462566471680*h*q41*w1^9 + 12322608075767808*lambda*p1*p32^3 + 18483912113651712*lambda*p21^2*p32^2 - 39021592239931392*lambda*p21*p32^3*w1 + 20323745958297600*lambda*p32^4*w1^2 - 38999023360671744*p0*p32*q41 - 24374389600419840*p1^2*q53 - 123226080757678080*p1*p21*p32^2 + 79623006028038144*p1*p21*p32*u2 + 56873575734312960*p1*p21*q53*w1 + 68458933754265600*p1*p32^3*w1 - 86258256530374656*p1*p32^2*u2*w1 - 61613040378839040*p1*p32*q53*w1^2 - 12322608075767808*p1*q3*w1^3 + 13007197413310464*p1*q41*w1^4 - 41075360252559360*p21^3*p32 + 13270501004673024*p21^3*u2 + 102688400631398400*p21^2*p32^2*w1 - 86258256530374656*p21^2*p32*u2*w1 - 30806520189419520*p21^2*q53*w1^2 - 32860288202047488*p21*p32^3*s2 - 75875318244311040*p21*p32^3*w1^2 + 136575572839759872*p21*p32^2*u2*w1^2 - 19499511680335872*p21*p32*q2 + 65035987066552320*p21*p32*q53*w1^3 + 9755398059982848*p21*q3*w1^4 - 10839331177758720*p21*q41*w1^5 + 26014394826620928*p32^4*s2*w1 + 15054626635776000*p32^4*w1^3 - 63229431870259200*p32^3*u2*w1^3 + 11374715146862592*p32^2*q2*w1 - 33872909930496000*p32^2*q53*w1^4 - 8129498383319040*p32*q3*w1^5 + 9333868514181120*p32*q41*w1^6

/-- On `p32 = 0` the order-`70` head is `-1624959306694656 p21` times one
three-term cofactor. -/
def degreeZeroPostCollapseP32ZeroOrderOne610
    (w1 p21 p1 q41 q3 : R) : R :=
  -(38999023360671744 : R) * p1 * p21 * q41 -
    14624633760251904 * p21 ^ 2 * q3 +
    22749430293725184 * p21 ^ 2 * q41 * w1

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetQuotient610_orderExpansion
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseJetHead610 p32 q41 +
        h * degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53
          q41 q3 u2 +
        h ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32
          p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseJetHead610,
    degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseJetOrderTwoPlus610]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseJetOrderOne610_p32Zero
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) (hp32 : p32 = 0) :
    degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
        u2 =
      degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 := by
  simp only [degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseP32ZeroOrderOne610, hp32, mul_zero, zero_mul,
    add_zero, sub_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32ZeroOrderOne610_factor
    (w1 p21 p1 q41 q3 : R) :
    degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 =
      -(1624959306694656 : R) * p21 *
        (24 * p1 * q41 + 9 * p21 * q3 - 14 * p21 * q41 * w1) := by
  simp only [degreeZeroPostCollapseP32ZeroOrderOne610]
  ring

end DegreeZeroOrderOneHead610

section DegreeZeroOrderOneEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseJetOrderOne610_eval
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : k[X]) (a : k) :
    (degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
        u2).eval a =
      degreeZeroPostCollapseJetOrderOne610 (w1.eval a) (a42.eval a)
        (p32.eval a) (p21.eval a) (p1.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) (u2.eval a) := by
  simp only [degreeZeroPostCollapseJetOrderOne610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseP32ZeroOrderOne610_eval
    (w1 p21 p1 q41 q3 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3).eval a =
      degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
        (p1.eval a) (q41.eval a) (q3.eval a) := by
  simp only [degreeZeroPostCollapseP32ZeroOrderOne610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

end DegreeZeroOrderOneEval610

section DegreeZeroP32ZeroSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Honest scalar split of the `p32 = 0` order-`70` head. -/
theorem degreeZeroPostCollapseP32ZeroOrderOne610_split
    (w1 p21 p1 q41 q3 : F)
    (hhead :
      degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 = 0) :
    p21 = 0 ∨
      24 * p1 * q41 + 9 * p21 * q3 - 14 * p21 * q41 * w1 = 0 := by
  rw [degreeZeroPostCollapseP32ZeroOrderOne610_factor] at hhead
  rcases mul_eq_zero.mp hhead with hconstant | hcofactor
  · have hp21 : p21 = 0 :=
      (mul_eq_zero.mp hconstant).resolve_left (by norm_num)
    exact Or.inl hp21
  · exact Or.inr hcofactor

/-- Joint grandchild of the `p32 = 0` child, using the fourth-tail split
together with the order-`70` head. -/
theorem degreeZeroPostCollapseP32Zero_grandchildren610
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hp32 : p32 = 0)
    (hfourteenth :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 = 0)
    (horder :
      degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 = 0) :
    p21 = 0 ∨ (q41 = 0 ∧ q3 = 0) := by
  have hord :=
    degreeZeroPostCollapseP32ZeroOrderOne610_split w1 p21 p1 q41 q3
      horder
  rcases nonzeroFourteenthPostCollapseJetHead610_p32Zero_split w1 a42
      p32 q53 p21 p1 q41 q3 hfourteenth hp32 with hq41 | hp21
  · rcases hord with hp21 | hlin
    · exact Or.inl hp21
    · have hsimp : 9 * p21 * q3 = 0 := by
        simpa [hq41, mul_zero, zero_mul, sub_zero, add_zero] using hlin
      rcases mul_eq_zero.mp hsimp with hnine | hq3
      · exact Or.inl
          ((mul_eq_zero.mp hnine).resolve_left (by norm_num))
      · exact Or.inr ⟨hq41, hq3⟩
  · exact Or.inl hp21

/-- On the `q41 = 0` child, the fourth-tail split together with the
`p32 = 0` grandchild analysis. -/
theorem degreeZeroPostCollapseQ41Zero_grandchildren610
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hq41 : q41 = 0)
    (hfourteenth :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 = 0)
    (horder_of_p32 :
      p32 = 0 →
        degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 = 0) :
    (p32 = 0 ∧ (p21 = 0 ∨ q3 = 0)) ∨
      10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3 = 0 := by
  rcases nonzeroFourteenthPostCollapseJetHead610_q41Zero_split w1 a42
      p32 q53 p21 p1 q41 q3 hfourteenth hq41 with hp32 | hcof
  · have hord := horder_of_p32 hp32
    have hgrand :=
      degreeZeroPostCollapseP32Zero_grandchildren610 w1 a42 p32 q53 p21
        p1 q41 q3 hp32 hfourteenth hord
    refine Or.inl ⟨hp32, ?_⟩
    rcases hgrand with hp21 | hpair
    · exact Or.inl hp21
    · exact Or.inr hpair.2
  · exact Or.inr hcof

end DegreeZeroP32ZeroSplit610

section DegreeZeroOrderOneSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = 0` the simple-pole obstruction peels one more power of
`h0` and forces the order-`70` head to vanish. -/
theorem degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
      (p1.eval a) (q41.eval a) (q3.eval a) = 0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hquotientZero : quotient.eval a = 0 :=
    localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      quotient rho hdegree hroot hclear (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q1, hQeq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    quotient a hdegree hroot hquotientZero
  have hclear5 : algebraMap k[X] (RatFunc k) Q1 = hRF ^ 5 * rho :=
    algebraMap_cancel_one_clearing_610 h0 quotient Q1 rho 5 hh0 hQeq
      (by simpa [hRF] using hclear)
  have hQ1zero : Q1.eval a = 0 :=
    localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q1 rho hdegree hroot hclear5 (by simpa [rho, hRF] using hderiv)
  obtain ⟨p32', hp32eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    p32 a hdegree hroot hp32
  have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
    w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
    (Polynomial.C lambda)
  have hident :
      Q1 =
        (7583143431241728 : k[X]) * h0 ^ 2 * p32' ^ 3 * q41 +
          degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53
            q41 q3 u2 +
          h0 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
            p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
            (Polynomial.C lambda) := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * Q1 = quotient := hQeq.symm
      _ = degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 * degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
              q53 q41 q3 u2 +
            h0 ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
              p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
              (Polynomial.C lambda) := hform
      _ = h0 *
            ((7583143431241728 : k[X]) * h0 ^ 2 * p32' ^ 3 * q41 +
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 q41 q3 u2 +
              h0 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
                p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda)) := by
        simp only [degreeZeroPostCollapseJetHead610, hp32eq]
        ring
  have hQ1eval :
      Q1.eval a =
        (degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41
          q3 u2).eval a := by
    rw [hident]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, hroot]
    ring
  have horderEval :
      (degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
          u2).eval a =
        degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a)
          (p21.eval a) (p1.eval a) (q41.eval a) (q3.eval a) := by
    rw [degreeZeroPostCollapseJetOrderOne610_eval]
    exact degreeZeroPostCollapseJetOrderOne610_p32Zero (w1.eval a)
      (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
      (q41.eval a) (q3.eval a) (u2.eval a) hp32
  rw [← horderEval, ← hQ1eval]
  exact hQ1zero

theorem degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) :
    degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
      ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) = 0 :=
  degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_primitiveDeriv h0 w1
    a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41 (q.coeff 3)
    (q.coeff 2) (q.coeff 1) lambda (58498535041007616 * j) a hh0
    hh0degree hroot hp32
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)

end DegreeZeroOrderOneSource610

section DegreeZeroSplitChildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing `p32(a) = 0` child: `p21(a) = 0` or both `q41(a)` and
`q3(a)` vanish. -/
theorem degreeZeroFace610_linearRoot_p32ZeroChild
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      (p32.eval a = 0 →
        p21.eval a = 0 ∨
          (q41.eval a = 0 ∧ (q.coeff 3).eval a = 0)) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  intro hp32
  have horder := degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source
    p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
    hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
    hq8deep hq7deep hq6deep hq5deep hq4deep hp32
  exact degreeZeroPostCollapseP32Zero_grandchildren610 (w1.eval a)
    (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
    ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hp32
    hfourteenth horder

/-- Source-facing `q41(a) = 0` child: either the `p32(a) = 0` grandchild
with `p21(a) = 0 ∨ q3(a) = 0`, or the landed five-term cofactor. -/
theorem degreeZeroFace610_linearRoot_q41ZeroChild
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      (q41.eval a = 0 →
        (p32.eval a = 0 ∧
            (p21.eval a = 0 ∨ (q.coeff 3).eval a = 0)) ∨
          10 * (p32.eval a) ^ 2 * (q53.eval a) +
              (18 * (p32.eval a) * (w1.eval a) -
                27 * (p21.eval a)) * (q.coeff 3).eval a = 0) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  intro hq41
  refine degreeZeroPostCollapseQ41Zero_grandchildren610 (w1.eval a)
    (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
    ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hq41
    hfourteenth ?_
  intro hp32
  exact degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source p q H
    h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
    hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
    hq8deep hq7deep hq6deep hq5deep hq4deep hp32

/-- Source-facing joint grandchild packet.  This is not a closure:
each surviving arm retains a residual. -/
theorem degreeZeroFace610_linearRoot_splitChildren
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      ((p32.eval a = 0 ∧
          (p21.eval a = 0 ∨
            (q41.eval a = 0 ∧ (q.coeff 3).eval a = 0))) ∨
        (q41.eval a = 0 ∧
          10 * (p32.eval a) ^ 2 * (q53.eval a) +
              (18 * (p32.eval a) * (w1.eval a) -
                27 * (p21.eval a)) * (q.coeff 3).eval a = 0)) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hdegree := degreeZeroPostCollapseJetHead610_zero_of_source p q H
    h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree
    hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
    hq6deep hq5deep hq4deep
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  have horder_of_p32 (hp32 : p32.eval a = 0) :
      degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) = 0 :=
    degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source p q H h0 j
      lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree hH
      hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
      hq6deep hq5deep hq4deep hp32
  rcases degreeZeroPostCollapseJetHead610_split (p32.eval a)
      (q41.eval a) hdegree with hp32 | hq41
  · exact Or.inl ⟨hp32,
      degreeZeroPostCollapseP32Zero_grandchildren610 (w1.eval a)
        (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hp32
        hfourteenth (horder_of_p32 hp32)⟩
  · have hchild :=
      degreeZeroPostCollapseQ41Zero_grandchildren610 (w1.eval a)
        (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hq41
        hfourteenth horder_of_p32
    rcases hchild with ⟨hp32, hrest⟩ | hcof
    · refine Or.inl ⟨hp32, ?_⟩
      rcases hrest with hp21 | hq3
      · exact Or.inl hp21
      · exact Or.inr ⟨hq41, hq3⟩
    · exact Or.inr ⟨hq41, hcof⟩

#print axioms linearPolynomial_dvd_of_eval_eq_zero_610
#print axioms localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610
#print axioms degreeZeroPostCollapseJetQuotient610_orderExpansion
#print axioms degreeZeroPostCollapseP32ZeroOrderOne610_split
#print axioms degreeZeroPostCollapseP32Zero_grandchildren610
#print axioms degreeZeroPostCollapseQ41Zero_grandchildren610
#print axioms degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source
#print axioms degreeZeroFace610_linearRoot_p32ZeroChild
#print axioms degreeZeroFace610_linearRoot_q41ZeroChild
#print axioms degreeZeroFace610_linearRoot_splitChildren

end DegreeZeroSplitChildren610

end Max11DegreeRoutes
