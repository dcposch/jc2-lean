import Grok610DegreeZeroOrder71GrandchildScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderThreeHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 1 through 10. -/
private abbrev order72Part09SpeedT_chunk01
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  -1000057340805120*a42^7*h^2*lambda - 15556447523635200*a42^7*h^2*w1 + 21584570939043840*a42^6*h^2*lambda*w1^2 + 23334671285452800*a42^6*h^2*p32n + 18667737028362240*a42^6*h^2*s2*w1 + 63954284263833600*a42^6*h^2*w1^3 - 3161471593512960*a42^6*h*u2 - 16258996766638080*a42^5*b63*h*w1 - 42002408313815040*a42^5*h^2*lambda*p32n*w1 - 77344712531573760*a42^5*h^2*lambda*w1^4

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 11 through 20. -/
private abbrev order72Part09SpeedT_chunk02
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 21678662355517440*a42^5*h^2*p32n*s2 - 221679377211801600*a42^5*h^2*p32n*w1^2 - 115117711674900480*a42^5*h^2*s2*w1^3 - 34375427791810560*a42^5*h^2*w1^5 + 8129498383319040*a42^5*h*lambda*p21 - 27098327944396800*a42^5*h*p1 + 99360535796121600*a42^5*h*p21*w1 + 49002809699450880*a42^5*h*u2*w1^2 + 3251799353327616*a42^5*q53 + 19510796119965696*a42^4*b63*h*p32n

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 21 through 30. -/
private abbrev order72Part09SpeedT_chunk03
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 70004013856358400*a42^4*b63*h*w1^3 - 9755398059982848*a42^4*h^2*lambda*p0 + 20323745958297600*a42^4*h^2*lambda*p32n^2 + 215845709390438400*a42^4*h^2*lambda*p32n*w1^3 + 105274747612419840*a42^4*h^2*lambda*w1^6 - 86714649422069760*a42^4*h^2*p0*w1 + 248401339490304000*a42^4*h^2*p32n^2*w1 + 280016055425433600*a42^4*h^2*p32n*s2*w1^2 + 209849995240704000*a42^4*h^2*p32n*w1^4 + 206252566750863360*a42^4*h^2*s2*w1^5

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 31 through 40. -/
private abbrev order72Part09SpeedT_chunk04
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 66841109595187200*a42^4*h^2*w1^7 + 40647491916595200*a42^4*h*lambda*p1*w1 - 105006020784537600*a42^4*h*lambda*p21*w1^2 + 26014394826620928*a42^4*h*p1*s2 + 146782609698816000*a42^4*h*p1*w1^2 - 135491639721984000*a42^4*h*p21*p32n - 108393311777587200*a42^4*h*p21*s2*w1 - 194455594045440000*a42^4*h*p21*w1^3 - 94844147805388800*a42^4*h*p32n*u2*w1 - 125909997144422400*a42^4*h*u2*w1^4

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 41 through 50. -/
private abbrev order72Part09SpeedT_chunk05
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 22762595473293312*a42^4*p21*u2 - 3080652018941952*a42^4*q3n + 13007197413310464*a42^4*q41n*w1 - 33872909930496000*a42^4*q53*w1^2 - 162589967666380800*a42^3*b63*h*p32n*w1^2 - 86338283756175360*a42^3*b63*h*w1^5 - 24645216151535616*a42^3*b63*p1 + 78043184479862784*a42^3*b63*p21*w1 + 81294983833190400*a42^3*h^2*lambda*p0*w1^2 - 210012041569075200*a42^3*h^2*lambda*p32n^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 51 through 60. -/
private abbrev order72Part09SpeedT_chunk06
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 309378850126295040*a42^3*h^2*lambda*p32n*w1^5 - 68929894270036800*a42^3*h^2*lambda*w1^8 + 130071974133104640*a42^3*h^2*p0*p32n + 104057579306483712*a42^3*h^2*p0*s2*w1 + 60218506543104000*a42^3*h^2*p0*w1^3 - 90327759814656000*a42^3*h^2*p32n^3 - 216786623555174400*a42^3*h^2*p32n^2*s2*w1 - 388911188090880000*a42^3*h^2*p32n^2*w1^3 - 575588558374502400*a42^3*h^2*p32n*s2*w1^4 + 143230949132544000*a42^3*h^2*p32n*w1^6

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 61 through 70. -/
private abbrev order72Part09SpeedT_chunk07
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 160418663028449280*a42^3*h^2*s2*w1^7 + 85098634901280000*a42^3*h^2*w1^9 - 39021592239931392*a42^3*h*lambda*p1*p32n - 140008027712716800*a42^3*h*lambda*p1*w1^3 + 162589967666380800*a42^3*h*lambda*p21*p32n*w1 + 215845709390438400*a42^3*h*lambda*p21*w1^4 - 28752752176791552*a42^3*h*p0*u2 - 346858597688279040*a42^3*h*p1*p32n*w1 - 216786623555174400*a42^3*h*p1*s2*w1^2 - 19445559404544000*a42^3*h*p1*w1^4

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 71 through 80. -/
private abbrev order72Part09SpeedT_chunk08
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 104057579306483712*a42^3*h*p21*p32n*s2 + 587130438795264000*a42^3*h*p21*p32n*w1^2 + 373354740567244800*a42^3*h*p21*s2*w1^3 - 47965713197875200*a42^3*h*p21*w1^5 + 45525190946586624*a42^3*h*p32n^2*u2 + 326685397996339200*a42^3*h*p32n*u2*w1^3 + 1895785857810432*a42^3*h*q1 + 120313997271336960*a42^3*h*u2*w1^6 - 19510796119965696*a42^3*lambda*p21^2 + 130071974133104640*a42^3*p1*p21

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 81 through 90. -/
private abbrev order72Part09SpeedT_chunk09
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 91050381893173248*a42^3*p1*u2*w1 - 173429298844139520*a42^3*p21^2*w1 - 189688295610777600*a42^3*p21*u2*w1^2 - 16430144101023744*a42^3*p32n*q41n + 65035987066552320*a42^3*p32n*q53*w1 - 8215072050511872*a42^3*q2*w1 + 19510796119965696*a42^3*q3n*w1^2 - 36131103925862400*a42^3*q41n*w1^3 + 58336678213632000*a42^3*q53*w1^4 - 73935648454606848*a42^2*b63*h*p0*w1

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 91 through 100. -/
private abbrev order72Part09SpeedT_chunk10
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 117064776719794176*a42^2*b63*h*p32n^2*w1 + 210012041569075200*a42^2*b63*h*p32n*w1^4 + 44196978589470720*a42^2*b63*h*w1^7 + 117064776719794176*a42^2*b63*p1*w1^2 - 73935648454606848*a42^2*b63*p21*p32n - 162589967666380800*a42^2*b63*p21*w1^3 - 117064776719794176*a42^2*h^2*lambda*p0*p32n*w1 - 105006020784537600*a42^2*h^2*lambda*p0*w1^4 + 81294983833190400*a42^2*h^2*lambda*p32n^3*w1 + 323768564085657600*a42^2*h^2*lambda*p32n^2*w1^4

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 101 through 110. -/
private abbrev order72Part09SpeedT_chunk11
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 180470995907005440*a42^2*h^2*lambda*p32n*w1^7 + 23359575280401360*a42^2*h^2*lambda*w1^10 - 98580864606142464*a42^2*h^2*p0*p32n*s2 - 227625954732933120*a42^2*h^2*p0*p32n*w1^2 - 216786623555174400*a42^2*h^2*p0*s2*w1^3 + 93338685141811200*a42^2*h^2*p0*w1^5 + 52028789653241856*a42^2*h^2*p32n^3*s2 + 293565219397632000*a42^2*h^2*p32n^3*w1^2 + 560032110850867200*a42^2*h^2*p32n^2*s2*w1^3 - 71948569796812800*a42^2*h^2*p32n^2*w1^5

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 111 through 120. -/
private abbrev order72Part09SpeedT_chunk12
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 412505133501726720*a42^2*h^2*p32n*s2*w1^6 - 213056036834659200*a42^2*h^2*p32n*w1^8 + 61271017128921600*a42^2*h^2*s2*w1^9 - 37752848938022400*a42^2*h^2*w1^11 + 36967824227303424*a42^2*h*lambda*p0*p21 + 243884951499571200*a42^2*h*lambda*p1*p32n*w1^2 + 129507425634263040*a42^2*h*lambda*p1*w1^5 - 58532388359897088*a42^2*h*lambda*p21*p32n^2 - 420024083138150400*a42^2*h*lambda*p21*p32n*w1^3 - 154689425063147520*a42^2*h*lambda*p21*w1^6

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 121 through 130. -/
private abbrev order72Part09SpeedT_chunk13
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 123226080757678080*a42^2*h*p0*p1 + 205376801262796800*a42^2*h*p0*p21*w1 + 136575572839759872*a42^2*h*p0*u2*w1^2 + 195107961199656960*a42^2*h*p1*p32n^2 + 312172737919451136*a42^2*h*p1*p32n*s2*w1 + 180655519629312000*a42^2*h*p1*p32n*w1^3 + 280016055425433600*a42^2*h*p1*s2*w1^4 - 131905711294156800*a42^2*h*p1*w1^6 - 520287896532418560*a42^2*h*p21*p32n^2*w1 - 650359870665523200*a42^2*h*p21*p32n*s2*w1^2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 131 through 140. -/
private abbrev order72Part09SpeedT_chunk14
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 58336678213632000*a42^2*h*p21*p32n*w1^4 - 345353135024701440*a42^2*h*p21*s2*w1^5 + 171877138959052800*a42^2*h*p21*w1^7 - 284532443416166400*a42^2*h*p32n^2*u2*w1^2 - 302183993146613760*a42^2*h*p32n*u2*w1^5 - 6161304037883904*a42^2*h*q1*w1^2 - 52637373806209920*a42^2*h*u2*w1^8 + 18483912113651712*a42^2*lambda*p1^2 - 117064776719794176*a42^2*lambda*p1*p21*w1 + 121942475749785600*a42^2*lambda*p21^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 141 through 150. -/
private abbrev order72Part09SpeedT_chunk15
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 28436787867156480*a42^2*p0*q53 + 102688400631398400*a42^2*p1^2*w1 - 98580864606142464*a42^2*p1*p21*s2 - 227625954732933120*a42^2*p1*p21*w1^2 - 86258256530374656*a42^2*p1*p32n*u2 - 189688295610777600*a42^2*p1*u2*w1^3 + 195107961199656960*a42^2*p21^2*p32n + 156086368959725568*a42^2*p21^2*s2*w1 + 90327759814656000*a42^2*p21^2*w1^3 + 273151145679519744*a42^2*p21*p32n*u2*w1

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 151 through 160. -/
private abbrev order72Part09SpeedT_chunk16
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 245014048497254400*a42^2*p21*u2*w1^4 - 30806520189419520*a42^2*p32n^2*q53 + 11374715146862592*a42^2*p32n*q2 - 36967824227303424*a42^2*p32n*q3n*w1 + 78043184479862784*a42^2*p32n*q41n*w1^2 - 135491639721984000*a42^2*p32n*q53*w1^3 + 13007197413310464*a42^2*q2*w1^3 - 20323745958297600*a42^2*q3n*w1^4 + 28001605542543360*a42^2*q41n*w1^5 - 35974284898406400*a42^2*q53*w1^6

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 161 through 170. -/
private abbrev order72Part09SpeedT_chunk17
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 68248290881175552*a42*b63*h*p0*p32n + 78043184479862784*a42*b63*h*p0*w1^3 - 24645216151535616*a42*b63*h*p32n^3 - 162589967666380800*a42*b63*h*p32n^2*w1^3 - 86338283756175360*a42*b63*h*p32n*w1^6 - 10026166439278080*a42*b63*h*w1^9 - 147871296909213696*a42*b63*p1*p32n*w1 - 81294983833190400*a42*b63*p1*w1^4 + 234129553439588352*a42*b63*p21*p32n*w1^2 + 84004816627630080*a42*b63*p21*w1^5

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 171 through 180. -/
private abbrev order72Part09SpeedT_chunk18
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 17062072720293888*a42*h^2*lambda*p0^2 + 36967824227303424*a42*h^2*lambda*p0*p32n^2 + 162589967666380800*a42*h^2*lambda*p0*p32n*w1^3 + 43169141878087680*a42*h^2*lambda*p0*w1^6 - 9755398059982848*a42*h^2*lambda*p32n^4 - 140008027712716800*a42*h^2*lambda*p32n^3*w1^3 - 154689425063147520*a42*h^2*lambda*p32n^2*w1^6 - 45953262846691200*a42*h^2*lambda*p32n*w1^9 - 3952251373199220*a42*h^2*lambda*w1^12 - 37915717156208640*a42*h^2*p0^2*w1

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 181 through 190. -/
private abbrev order72Part09SpeedT_chunk19
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 205376801262796800*a42*h^2*p0*p32n^2*w1 + 312172737919451136*a42*h^2*p0*p32n*s2*w1^2 - 112909699768320000*a42*h^2*p0*p32n*w1^4 + 112006422170173440*a42*h^2*p0*s2*w1^5 - 68522447425536000*a42*h^2*p0*w1^7 - 86714649422069760*a42*h^2*p32n^4*w1 - 216786623555174400*a42*h^2*p32n^3*s2*w1^2 - 19445559404544000*a42*h^2*p32n^3*w1^4 - 345353135024701440*a42*h^2*p32n^2*s2*w1^5 + 171877138959052800*a42*h^2*p32n^2*w1^7

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 191 through 200. -/
private abbrev order72Part09SpeedT_chunk20
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 120313997271336960*a42*h^2*p32n*s2*w1^8 + 74035812364113600*a42*h^2*p32n*w1^10 - 11325854681406720*a42*h^2*s2*w1^11 + 7431583778665200*a42*h^2*w1^13 + 73935648454606848*a42*h*lambda*p0*p1*w1 - 117064776719794176*a42*h*lambda*p0*p21*w1^2 - 117064776719794176*a42*h*lambda*p1*p32n^2*w1 - 210012041569075200*a42*h*lambda*p1*p32n*w1^4 - 44196978589470720*a42*h*lambda*p1*w1^7 + 243884951499571200*a42*h*lambda*p21*p32n^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 201 through 210. -/
private abbrev order72Part09SpeedT_chunk21
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 259014851268526080*a42*h*lambda*p21*p32n*w1^5 + 45117748976751360*a42*h*lambda*p21*w1^8 + 90997721174900736*a42*h*p0*p1*s2 + 20537680126279680*a42*h*p0*p1*w1^2 - 246452161515356160*a42*h*p0*p21*p32n - 197161729212284928*a42*h*p0*p21*s2*w1 + 43357324711034880*a42*h*p0*p21*w1^3 - 172516513060749312*a42*h*p0*p32n*u2*w1 - 94844147805388800*a42*h*p0*u2*w1^4 - 98580864606142464*a42*h*p1*p32n^2*s2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 211 through 220. -/
private abbrev order72Part09SpeedT_chunk22
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 227625954732933120*a42*h*p1*p32n^2*w1^2 - 433573247110348800*a42*h*p1*p32n*s2*w1^3 + 186677370283622400*a42*h*p1*p32n*w1^5 - 115117711674900480*a42*h*p1*s2*w1^6 + 70592396358182400*a42*h*p1*w1^8 + 130071974133104640*a42*h*p21*p32n^3 + 312172737919451136*a42*h*p21*p32n^2*s2*w1 + 180655519629312000*a42*h*p21*p32n^2*w1^3 + 560032110850867200*a42*h*p21*p32n*s2*w1^4 - 263811422588313600*a42*h*p21*p32n*w1^6

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 221 through 230. -/
private abbrev order72Part09SpeedT_chunk23
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 117858609571921920*a42*h*p21*s2*w1^7 - 72411202061452800*a42*h*p21*w1^9 + 91050381893173248*a42*h*p32n^3*u2*w1 + 245014048497254400*a42*h*p32n^2*u2*w1^4 + 11374715146862592*a42*h*p32n*q1*w1 + 103126283375431680*a42*h*p32n*u2*w1^7 + 3251799353327616*a42*h*q1*w1^4 + 10722427997561280*a42*h*u2*w1^10 - 58532388359897088*a42*lambda*p1^2*w1^2 + 73935648454606848*a42*lambda*p1*p21*p32n

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 231 through 240. -/
private abbrev order72Part09SpeedT_chunk24
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 162589967666380800*a42*lambda*p1*p21*w1^3 - 117064776719794176*a42*lambda*p21^2*p32n*w1 - 105006020784537600*a42*lambda*p21^2*w1^4 + 79623006028038144*a42*p0*p21*u2 - 29249267520503808*a42*p0*q3n + 45498860587450368*a42*p0*q41n*w1 - 61613040378839040*a42*p0*q53*w1^2 - 123226080757678080*a42*p1^2*p32n - 98580864606142464*a42*p1^2*s2*w1 + 21678662355517440*a42*p1^2*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 241 through 250. -/
private abbrev order72Part09SpeedT_chunk25
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 410753602525593600*a42*p1*p21*p32n*w1 + 312172737919451136*a42*p1*p21*s2*w1^2 - 112909699768320000*a42*p1*p21*w1^4 + 273151145679519744*a42*p1*p32n*u2*w1^2 + 98005619398901760*a42*p1*u2*w1^5 - 98580864606142464*a42*p21^2*p32n*s2 - 227625954732933120*a42*p21^2*p32n*w1^2 - 216786623555174400*a42*p21^2*s2*w1^3 + 93338685141811200*a42*p21^2*w1^5 - 86258256530374656*a42*p21*p32n^2*u2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 251 through 260. -/
private abbrev order72Part09SpeedT_chunk26
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 379376591221555200*a42*p21*p32n*u2*w1^3 - 9749755840167936*a42*p21*q1 - 100727997715537920*a42*p21*u2*w1^6 + 17062072720293888*a42*p32n^2*q3n - 49290432303071232*a42*p32n^2*q41n*w1 + 97553980599828480*a42*p32n^2*q53*w1^2 - 24645216151535616*a42*p32n*q2*w1^2 + 39021592239931392*a42*p32n*q3n*w1^3 - 54196655888793600*a42*p32n*q41n*w1^4 + 70004013856358400*a42*p32n*q53*w1^5

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 261 through 270. -/
private abbrev order72Part09SpeedT_chunk27
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 5419665588879360*a42*q2*w1^5 + 7000401385635840*a42*q3n*w1^6 - 8222693691064320*a42*q41n*w1^7 + 9207703872806400*a42*q53*w1^8 - 73935648454606848*b63*h*p0*p32n*w1^2 - 16258996766638080*b63*h*p0*w1^5 + 39021592239931392*b63*h*p32n^3*w1^2 + 42002408313815040*b63*h*p32n^2*w1^5 + 11049244647367680*b63*h*p32n*w1^8 + 835513869939840*b63*h*w1^11

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 271 through 280. -/
private abbrev order72Part09SpeedT_chunk28
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 58498535041007616*b63*p0*p1 + 68248290881175552*b63*p0*p21*w1 + 34124145440587776*b63*p1*p32n^2 + 78043184479862784*b63*p1*p32n*w1^3 + 14000802771271680*b63*p1*w1^6 - 73935648454606848*b63*p21*p32n^2*w1 - 81294983833190400*b63*p21*p32n*w1^4 - 12334040536596480*b63*p21*w1^7 + 18483912113651712*h^2*lambda*p0^2*w1^2 - 58532388359897088*h^2*lambda*p0*p32n^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 281 through 290. -/
private abbrev order72Part09SpeedT_chunk29
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 42002408313815040*h^2*lambda*p0*p32n*w1^5 - 5524622323683840*h^2*lambda*p0*w1^8 + 20323745958297600*h^2*lambda*p32n^4*w1^2 + 43169141878087680*h^2*lambda*p32n^3*w1^5 + 22558874488375680*h^2*lambda*p32n^2*w1^8 + 4247195505527520*h^2*lambda*p32n*w1^11 + 264207280442805*h^2*lambda*w1^14 + 56873575734312960*h^2*p0^2*p32n + 45498860587450368*h^2*p0^2*s2*w1 - 27383573501706240*h^2*p0^2*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 291 through 300. -/
private abbrev order72Part09SpeedT_chunk30
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 41075360252559360*h^2*p0*p32n^3 - 98580864606142464*h^2*p0*p32n^2*s2*w1 + 21678662355517440*h^2*p0*p32n^2*w1^3 - 108393311777587200*h^2*p0*p32n*s2*w1^4 + 66114901975449600*h^2*p0*p32n*w1^6 - 16445387382128640*h^2*p0*s2*w1^7 + 10912834219622400*h^2*p0*w1^9 + 6503598706655232*h^2*p32n^5 + 26014394826620928*h^2*p32n^4*s2*w1 + 15054626635776000*h^2*p32n^4*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 301 through 310. -/
private abbrev order72Part09SpeedT_chunk31
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 93338685141811200*h^2*p32n^3*s2*w1^4 - 43968570431385600*h^2*p32n^3*w1^6 + 58929304785960960*h^2*p32n^2*s2*w1^7 - 36205601030726400*h^2*p32n^2*w1^9 + 12254203425784320*h^2*p32n*s2*w1^10 - 8061806283640200*h^2*p32n*w1^12 + 810718230399840*h^2*s2*w1^13 - 547985470548040*h^2*w1^15 - 34124145440587776*h*lambda*p0*p1*p32n - 39021592239931392*h*lambda*p0*p1*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 311 through 320. -/
private abbrev order72Part09SpeedT_chunk32
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 73935648454606848*h*lambda*p0*p21*p32n*w1 + 40647491916595200*h*lambda*p0*p21*w1^4 + 12322608075767808*h*lambda*p1*p32n^3 + 81294983833190400*h*lambda*p1*p32n^2*w1^3 + 43169141878087680*h*lambda*p1*p32n*w1^6 + 5013083219639040*h*lambda*p1*w1^9 - 39021592239931392*h*lambda*p21*p32n^3*w1 - 105006020784537600*h*lambda*p21*p32n^2*w1^4 - 44196978589470720*h*lambda*p21*p32n*w1^7 - 4595326284669120*h*lambda*p21*w1^10

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 321 through 330. -/
private abbrev order72Part09SpeedT_chunk33
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 34124145440587776*h*p0^2*u2 - 75831434312417280*h*p0*p1*p32n*w1 - 98580864606142464*h*p0*p1*s2*w1^2 + 59616321477672960*h*p0*p1*w1^4 + 90997721174900736*h*p0*p21*p32n*s2 + 20537680126279680*h*p0*p21*p32n*w1^2 + 104057579306483712*h*p0*p21*s2*w1^3 - 63229431870259200*h*p0*p21*w1^5 + 39811503014019072*h*p0*p32n^2*u2 + 91050381893173248*h*p0*p32n*u2*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 331 through 340. -/
private abbrev order72Part09SpeedT_chunk34
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 58498535041007616*h*p0*q1 + 16334269899816960*h*p0*u2*w1^6 + 68458933754265600*h*p1*p32n^3*w1 + 156086368959725568*h*p1*p32n^2*s2*w1^2 - 56454849884160000*h*p1*p32n^2*w1^4 + 112006422170173440*h*p1*p32n*s2*w1^5 - 68522447425536000*h*p1*p32n*w1^7 + 14732326196490240*h*p1*s2*w1^8 - 9747661815964800*h*p1*w1^10 - 32860288202047488*h*p21*p32n^3*s2

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 341 through 350. -/
private abbrev order72Part09SpeedT_chunk35
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 75875318244311040*h*p21*p32n^3*w1^2 - 216786623555174400*h*p21*p32n^2*s2*w1^3 + 93338685141811200*h*p21*p32n^2*w1^5 - 115117711674900480*h*p21*p32n*s2*w1^6 + 70592396358182400*h*p21*p32n*w1^8 - 13368221919037440*h*p21*s2*w1^9 + 8819313071587200*h*p21*w1^11 - 7188188044197888*h*p32n^4*u2 - 63229431870259200*h*p32n^3*u2*w1^3 - 4874877920083968*h*p32n^2*q1

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 351 through 360. -/
private abbrev order72Part09SpeedT_chunk36
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 50363998857768960*h*p32n^2*u2*w1^6 - 4107536025255936*h*p32n*q1*w1^3 - 11697194179157760*h*p32n*u2*w1^9 - 451638799073280*h*q1*w1^6 - 825843570519240*h*u2*w1^12 - 17062072720293888*lambda*p0*p21^2 + 36967824227303424*lambda*p1^2*p32n*w1 + 20323745958297600*lambda*p1^2*w1^4 - 117064776719794176*lambda*p1*p21*p32n*w1^2 - 42002408313815040*lambda*p1*p21*w1^5

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 361 through 370. -/
private abbrev order72Part09SpeedT_chunk37
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 18483912113651712*lambda*p21^2*p32n^2 + 81294983833190400*lambda*p21^2*p32n*w1^3 + 21584570939043840*lambda*p21^2*w1^6 + 113747151468625920*p0*p1*p21 + 79623006028038144*p0*p1*u2*w1 - 37915717156208640*p0*p21^2*w1 - 86258256530374656*p0*p21*u2*w1^2 - 38999023360671744*p0*p32n*q41n + 56873575734312960*p0*p32n*q53*w1 - 19499511680335872*p0*q2*w1

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 371 through 380. -/
private abbrev order72Part09SpeedT_chunk38
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc + 17062072720293888*p0*q3n*w1^2 - 16430144101023744*p0*q41n*w1^3 + 16258996766638080*p0*q53*w1^4 + 45498860587450368*p1^2*p32n*s2 + 10268840063139840*p1^2*p32n*w1^2 + 52028789653241856*p1^2*s2*w1^3 - 31614715935129600*p1^2*w1^5 - 123226080757678080*p1*p21*p32n^2 - 197161729212284928*p1*p21*p32n*s2*w1 + 43357324711034880*p1*p21*p32n*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 381 through 390. -/
private abbrev order72Part09SpeedT_chunk39
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 108393311777587200*p1*p21*s2*w1^4 + 66114901975449600*p1*p21*w1^6 - 86258256530374656*p1*p32n^2*u2*w1 - 94844147805388800*p1*p32n*u2*w1^4 - 9749755840167936*p1*q1*w1 - 14389713959362560*p1*u2*w1^7 + 102688400631398400*p21^2*p32n^2*w1 + 156086368959725568*p21^2*p32n*s2*w1^2 - 56454849884160000*p21^2*p32n*w1^4 + 56003211085086720*p21^2*s2*w1^5

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 391 through 400. -/
private abbrev order72Part09SpeedT_chunk40
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 34261223712768000*p21^2*w1^7 + 136575572839759872*p21*p32n^2*u2*w1^2 + 98005619398901760*p21*p32n*u2*w1^5 + 5687357573431296*p21*q1*w1^2 + 12890785421928960*p21*u2*w1^8 + 7583143431241728*p32n^3*q41n - 20537680126279680*p32n^3*q53*w1 + 11374715146862592*p32n^2*q2*w1 - 18483912113651712*p32n^2*q3n*w1^2 + 26014394826620928*p32n^2*q41n*w1^3

set_option maxHeartbeats 64000000 in
/-- Reducible accumulator step for monomials 401 through 409. -/
private abbrev order72Part09SpeedT_chunk41
    (acc : R)
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  acc - 33872909930496000*p32n^2*q53*w1^4 + 6503598706655232*p32n*q2*w1^4 - 8129498383319040*p32n*q3n*w1^5 + 9333868514181120*p32n*q41n*w1^6 - 10278367113830400*p32n*q53*w1^7 + 666704893870080*q2*w1^7 - 770877533537280*q3n*w1^8 + 818462566471680*q41n*w1^9 - 835513869939840*q53*w1^10

set_option maxHeartbeats 64000000 in
/-- Remaining factor after `h^3` is removed on the `p32 = h · p32n`,
`q41 = h · q41n`, `q3 = h · q3n` substitution. -/
def degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  order72Part09SpeedT_chunk41
    (order72Part09SpeedT_chunk40
    (order72Part09SpeedT_chunk39
    (order72Part09SpeedT_chunk38
    (order72Part09SpeedT_chunk37
    (order72Part09SpeedT_chunk36
    (order72Part09SpeedT_chunk35
    (order72Part09SpeedT_chunk34
    (order72Part09SpeedT_chunk33
    (order72Part09SpeedT_chunk32
    (order72Part09SpeedT_chunk31
    (order72Part09SpeedT_chunk30
    (order72Part09SpeedT_chunk29
    (order72Part09SpeedT_chunk28
    (order72Part09SpeedT_chunk27
    (order72Part09SpeedT_chunk26
    (order72Part09SpeedT_chunk25
    (order72Part09SpeedT_chunk24
    (order72Part09SpeedT_chunk23
    (order72Part09SpeedT_chunk22
    (order72Part09SpeedT_chunk21
    (order72Part09SpeedT_chunk20
    (order72Part09SpeedT_chunk19
    (order72Part09SpeedT_chunk18
    (order72Part09SpeedT_chunk17
    (order72Part09SpeedT_chunk16
    (order72Part09SpeedT_chunk15
    (order72Part09SpeedT_chunk14
    (order72Part09SpeedT_chunk13
    (order72Part09SpeedT_chunk12
    (order72Part09SpeedT_chunk11
    (order72Part09SpeedT_chunk10
    (order72Part09SpeedT_chunk09
    (order72Part09SpeedT_chunk08
    (order72Part09SpeedT_chunk07
    (order72Part09SpeedT_chunk06
    (order72Part09SpeedT_chunk05
    (order72Part09SpeedT_chunk04
    (order72Part09SpeedT_chunk03
    (order72Part09SpeedT_chunk02
    (order72Part09SpeedT_chunk01 h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda) h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
