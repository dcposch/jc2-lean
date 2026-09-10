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
/-- Monomials 1–10, preserving left association. -/
private abbrev order72Part05SpeedTChunk01
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    -1000057340805120*a42^7*h^2*lambda
    - 15556447523635200*a42^7*h^2*w1
    + 21584570939043840*a42^6*h^2*lambda*w1^2
    + 23334671285452800*a42^6*h^2*p32n
    + 18667737028362240*a42^6*h^2*s2*w1
    + 63954284263833600*a42^6*h^2*w1^3
    - 3161471593512960*a42^6*h*u2
    - 16258996766638080*a42^5*b63*h*w1
    + 8129498383319040*a42^5*h^2*lambda*p21n
    - 42002408313815040*a42^5*h^2*lambda*p32n*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 11–20, preserving left association. -/
private abbrev order72Part05SpeedTChunk02 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 77344712531573760*a42^5*h^2*lambda*w1^4
    - 27098327944396800*a42^5*h^2*p1n
    + 99360535796121600*a42^5*h^2*p21n*w1
    - 21678662355517440*a42^5*h^2*p32n*s2
    - 221679377211801600*a42^5*h^2*p32n*w1^2
    - 115117711674900480*a42^5*h^2*s2*w1^3
    - 34375427791810560*a42^5*h^2*w1^5
    + 49002809699450880*a42^5*h*u2*w1^2
    + 3251799353327616*a42^5*q53
    + 19510796119965696*a42^4*b63*h*p32n

set_option maxHeartbeats 64000000 in
/-- Monomials 21–30, preserving left association. -/
private abbrev order72Part05SpeedTChunk03 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 70004013856358400*a42^4*b63*h*w1^3
    - 9755398059982848*a42^4*h^2*lambda*p0
    + 40647491916595200*a42^4*h^2*lambda*p1n*w1
    - 105006020784537600*a42^4*h^2*lambda*p21n*w1^2
    + 20323745958297600*a42^4*h^2*lambda*p32n^2
    + 215845709390438400*a42^4*h^2*lambda*p32n*w1^3
    + 105274747612419840*a42^4*h^2*lambda*w1^6
    - 86714649422069760*a42^4*h^2*p0*w1
    + 26014394826620928*a42^4*h^2*p1n*s2
    + 146782609698816000*a42^4*h^2*p1n*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 31–40, preserving left association. -/
private abbrev order72Part05SpeedTChunk04 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 135491639721984000*a42^4*h^2*p21n*p32n
    - 108393311777587200*a42^4*h^2*p21n*s2*w1
    - 194455594045440000*a42^4*h^2*p21n*w1^3
    + 248401339490304000*a42^4*h^2*p32n^2*w1
    + 280016055425433600*a42^4*h^2*p32n*s2*w1^2
    + 209849995240704000*a42^4*h^2*p32n*w1^4
    + 206252566750863360*a42^4*h^2*s2*w1^5
    - 66841109595187200*a42^4*h^2*w1^7
    + 22762595473293312*a42^4*h*p21n*u2
    - 94844147805388800*a42^4*h*p32n*u2*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 41–50, preserving left association. -/
private abbrev order72Part05SpeedTChunk05 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 125909997144422400*a42^4*h*u2*w1^4
    - 33872909930496000*a42^4*q53*w1^2
    - 24645216151535616*a42^3*b63*h*p1n
    + 78043184479862784*a42^3*b63*h*p21n*w1
    - 162589967666380800*a42^3*b63*h*p32n*w1^2
    - 86338283756175360*a42^3*b63*h*w1^5
    + 81294983833190400*a42^3*h^2*lambda*p0*w1^2
    - 39021592239931392*a42^3*h^2*lambda*p1n*p32n
    - 140008027712716800*a42^3*h^2*lambda*p1n*w1^3
    - 19510796119965696*a42^3*h^2*lambda*p21n^2

set_option maxHeartbeats 64000000 in
/-- Monomials 51–60, preserving left association. -/
private abbrev order72Part05SpeedTChunk06 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 162589967666380800*a42^3*h^2*lambda*p21n*p32n*w1
    + 215845709390438400*a42^3*h^2*lambda*p21n*w1^4
    - 210012041569075200*a42^3*h^2*lambda*p32n^2*w1^2
    - 309378850126295040*a42^3*h^2*lambda*p32n*w1^5
    - 68929894270036800*a42^3*h^2*lambda*w1^8
    + 130071974133104640*a42^3*h^2*p0*p32n
    + 104057579306483712*a42^3*h^2*p0*s2*w1
    + 60218506543104000*a42^3*h^2*p0*w1^3
    + 130071974133104640*a42^3*h^2*p1n*p21n
    - 346858597688279040*a42^3*h^2*p1n*p32n*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 61–70, preserving left association. -/
private abbrev order72Part05SpeedTChunk07 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 216786623555174400*a42^3*h^2*p1n*s2*w1^2
    - 19445559404544000*a42^3*h^2*p1n*w1^4
    - 173429298844139520*a42^3*h^2*p21n^2*w1
    + 104057579306483712*a42^3*h^2*p21n*p32n*s2
    + 587130438795264000*a42^3*h^2*p21n*p32n*w1^2
    + 373354740567244800*a42^3*h^2*p21n*s2*w1^3
    - 47965713197875200*a42^3*h^2*p21n*w1^5
    - 90327759814656000*a42^3*h^2*p32n^3
    - 216786623555174400*a42^3*h^2*p32n^2*s2*w1
    - 388911188090880000*a42^3*h^2*p32n^2*w1^3

set_option maxHeartbeats 64000000 in
/-- Monomials 71–80, preserving left association. -/
private abbrev order72Part05SpeedTChunk08 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 575588558374502400*a42^3*h^2*p32n*s2*w1^4
    + 143230949132544000*a42^3*h^2*p32n*w1^6
    - 160418663028449280*a42^3*h^2*s2*w1^7
    + 85098634901280000*a42^3*h^2*w1^9
    - 28752752176791552*a42^3*h*p0*u2
    + 91050381893173248*a42^3*h*p1n*u2*w1
    - 189688295610777600*a42^3*h*p21n*u2*w1^2
    + 45525190946586624*a42^3*h*p32n^2*u2
    + 326685397996339200*a42^3*h*p32n*u2*w1^3
    + 1895785857810432*a42^3*h*q1

set_option maxHeartbeats 64000000 in
/-- Monomials 81–90, preserving left association. -/
private abbrev order72Part05SpeedTChunk09 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 120313997271336960*a42^3*h*u2*w1^6
    - 20537680126279680*a42^3*p21n*q53
    + 65035987066552320*a42^3*p32n*q53*w1
    - 8215072050511872*a42^3*q2*w1
    + 58336678213632000*a42^3*q53*w1^4
    - 73935648454606848*a42^2*b63*h*p0*w1
    + 117064776719794176*a42^2*b63*h*p1n*w1^2
    - 73935648454606848*a42^2*b63*h*p21n*p32n
    - 162589967666380800*a42^2*b63*h*p21n*w1^3
    + 117064776719794176*a42^2*b63*h*p32n^2*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 91–100, preserving left association. -/
private abbrev order72Part05SpeedTChunk10 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 210012041569075200*a42^2*b63*h*p32n*w1^4
    + 44196978589470720*a42^2*b63*h*w1^7
    + 36967824227303424*a42^2*h^2*lambda*p0*p21n
    - 117064776719794176*a42^2*h^2*lambda*p0*p32n*w1
    - 105006020784537600*a42^2*h^2*lambda*p0*w1^4
    + 18483912113651712*a42^2*h^2*lambda*p1n^2
    - 117064776719794176*a42^2*h^2*lambda*p1n*p21n*w1
    + 243884951499571200*a42^2*h^2*lambda*p1n*p32n*w1^2
    + 129507425634263040*a42^2*h^2*lambda*p1n*w1^5
    + 121942475749785600*a42^2*h^2*lambda*p21n^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 101–110, preserving left association. -/
private abbrev order72Part05SpeedTChunk11 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 58532388359897088*a42^2*h^2*lambda*p21n*p32n^2
    - 420024083138150400*a42^2*h^2*lambda*p21n*p32n*w1^3
    - 154689425063147520*a42^2*h^2*lambda*p21n*w1^6
    + 81294983833190400*a42^2*h^2*lambda*p32n^3*w1
    + 323768564085657600*a42^2*h^2*lambda*p32n^2*w1^4
    + 180470995907005440*a42^2*h^2*lambda*p32n*w1^7
    + 23359575280401360*a42^2*h^2*lambda*w1^10
    - 123226080757678080*a42^2*h^2*p0*p1n
    + 205376801262796800*a42^2*h^2*p0*p21n*w1
    - 98580864606142464*a42^2*h^2*p0*p32n*s2

set_option maxHeartbeats 64000000 in
/-- Monomials 111–120, preserving left association. -/
private abbrev order72Part05SpeedTChunk12 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 227625954732933120*a42^2*h^2*p0*p32n*w1^2
    - 216786623555174400*a42^2*h^2*p0*s2*w1^3
    + 93338685141811200*a42^2*h^2*p0*w1^5
    + 102688400631398400*a42^2*h^2*p1n^2*w1
    - 98580864606142464*a42^2*h^2*p1n*p21n*s2
    - 227625954732933120*a42^2*h^2*p1n*p21n*w1^2
    + 195107961199656960*a42^2*h^2*p1n*p32n^2
    + 312172737919451136*a42^2*h^2*p1n*p32n*s2*w1
    + 180655519629312000*a42^2*h^2*p1n*p32n*w1^3
    + 280016055425433600*a42^2*h^2*p1n*s2*w1^4

set_option maxHeartbeats 64000000 in
/-- Monomials 121–130, preserving left association. -/
private abbrev order72Part05SpeedTChunk13 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 131905711294156800*a42^2*h^2*p1n*w1^6
    + 195107961199656960*a42^2*h^2*p21n^2*p32n
    + 156086368959725568*a42^2*h^2*p21n^2*s2*w1
    + 90327759814656000*a42^2*h^2*p21n^2*w1^3
    - 520287896532418560*a42^2*h^2*p21n*p32n^2*w1
    - 650359870665523200*a42^2*h^2*p21n*p32n*s2*w1^2
    - 58336678213632000*a42^2*h^2*p21n*p32n*w1^4
    - 345353135024701440*a42^2*h^2*p21n*s2*w1^5
    + 171877138959052800*a42^2*h^2*p21n*w1^7
    + 52028789653241856*a42^2*h^2*p32n^3*s2

set_option maxHeartbeats 64000000 in
/-- Monomials 131–140, preserving left association. -/
private abbrev order72Part05SpeedTChunk14 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 293565219397632000*a42^2*h^2*p32n^3*w1^2
    + 560032110850867200*a42^2*h^2*p32n^2*s2*w1^3
    - 71948569796812800*a42^2*h^2*p32n^2*w1^5
    + 412505133501726720*a42^2*h^2*p32n*s2*w1^6
    - 213056036834659200*a42^2*h^2*p32n*w1^8
    + 61271017128921600*a42^2*h^2*s2*w1^9
    - 37752848938022400*a42^2*h^2*w1^11
    + 136575572839759872*a42^2*h*p0*u2*w1^2
    - 86258256530374656*a42^2*h*p1n*p32n*u2
    - 189688295610777600*a42^2*h*p1n*u2*w1^3

set_option maxHeartbeats 64000000 in
/-- Monomials 141–150, preserving left association. -/
private abbrev order72Part05SpeedTChunk15 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 43129128265187328*a42^2*h*p21n^2*u2
    + 273151145679519744*a42^2*h*p21n*p32n*u2*w1
    + 245014048497254400*a42^2*h*p21n*u2*w1^4
    - 284532443416166400*a42^2*h*p32n^2*u2*w1^2
    - 302183993146613760*a42^2*h*p32n*u2*w1^5
    - 6161304037883904*a42^2*h*q1*w1^2
    - 52637373806209920*a42^2*h*u2*w1^8
    + 28436787867156480*a42^2*p0*q53
    - 61613040378839040*a42^2*p1n*q53*w1
    + 97553980599828480*a42^2*p21n*q53*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 151–160, preserving left association. -/
private abbrev order72Part05SpeedTChunk16 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 30806520189419520*a42^2*p32n^2*q53
    + 11374715146862592*a42^2*p32n*q2
    - 135491639721984000*a42^2*p32n*q53*w1^3
    + 13007197413310464*a42^2*q2*w1^3
    - 35974284898406400*a42^2*q53*w1^6
    + 68248290881175552*a42*b63*h*p0*p32n
    + 78043184479862784*a42*b63*h*p0*w1^3
    + 68248290881175552*a42*b63*h*p1n*p21n
    - 147871296909213696*a42*b63*h*p1n*p32n*w1
    - 81294983833190400*a42*b63*h*p1n*w1^4

set_option maxHeartbeats 64000000 in
/-- Monomials 161–170, preserving left association. -/
private abbrev order72Part05SpeedTChunk17 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 73935648454606848*a42*b63*h*p21n^2*w1
    + 234129553439588352*a42*b63*h*p21n*p32n*w1^2
    + 84004816627630080*a42*b63*h*p21n*w1^5
    - 24645216151535616*a42*b63*h*p32n^3
    - 162589967666380800*a42*b63*h*p32n^2*w1^3
    - 86338283756175360*a42*b63*h*p32n*w1^6
    - 10026166439278080*a42*b63*h*w1^9
    - 17062072720293888*a42*h^2*lambda*p0^2
    + 73935648454606848*a42*h^2*lambda*p0*p1n*w1
    - 117064776719794176*a42*h^2*lambda*p0*p21n*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 171–180, preserving left association. -/
private abbrev order72Part05SpeedTChunk18 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 36967824227303424*a42*h^2*lambda*p0*p32n^2
    + 162589967666380800*a42*h^2*lambda*p0*p32n*w1^3
    + 43169141878087680*a42*h^2*lambda*p0*w1^6
    - 58532388359897088*a42*h^2*lambda*p1n^2*w1^2
    + 73935648454606848*a42*h^2*lambda*p1n*p21n*p32n
    + 162589967666380800*a42*h^2*lambda*p1n*p21n*w1^3
    - 117064776719794176*a42*h^2*lambda*p1n*p32n^2*w1
    - 210012041569075200*a42*h^2*lambda*p1n*p32n*w1^4
    - 44196978589470720*a42*h^2*lambda*p1n*w1^7
    + 12322608075767808*a42*h^2*lambda*p21n^3

set_option maxHeartbeats 64000000 in
/-- Monomials 181–190, preserving left association. -/
private abbrev order72Part05SpeedTChunk19 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 117064776719794176*a42*h^2*lambda*p21n^2*p32n*w1
    - 105006020784537600*a42*h^2*lambda*p21n^2*w1^4
    + 243884951499571200*a42*h^2*lambda*p21n*p32n^2*w1^2
    + 259014851268526080*a42*h^2*lambda*p21n*p32n*w1^5
    + 45117748976751360*a42*h^2*lambda*p21n*w1^8
    - 9755398059982848*a42*h^2*lambda*p32n^4
    - 140008027712716800*a42*h^2*lambda*p32n^3*w1^3
    - 154689425063147520*a42*h^2*lambda*p32n^2*w1^6
    - 45953262846691200*a42*h^2*lambda*p32n*w1^9
    - 3952251373199220*a42*h^2*lambda*w1^12

set_option maxHeartbeats 64000000 in
/-- Monomials 191–200, preserving left association. -/
private abbrev order72Part05SpeedTChunk20 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 37915717156208640*a42*h^2*p0^2*w1
    + 90997721174900736*a42*h^2*p0*p1n*s2
    + 20537680126279680*a42*h^2*p0*p1n*w1^2
    - 246452161515356160*a42*h^2*p0*p21n*p32n
    - 197161729212284928*a42*h^2*p0*p21n*s2*w1
    + 43357324711034880*a42*h^2*p0*p21n*w1^3
    + 205376801262796800*a42*h^2*p0*p32n^2*w1
    + 312172737919451136*a42*h^2*p0*p32n*s2*w1^2
    - 112909699768320000*a42*h^2*p0*p32n*w1^4
    + 112006422170173440*a42*h^2*p0*s2*w1^5

set_option maxHeartbeats 64000000 in
/-- Monomials 201–210, preserving left association. -/
private abbrev order72Part05SpeedTChunk21 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 68522447425536000*a42*h^2*p0*w1^7
    - 123226080757678080*a42*h^2*p1n^2*p32n
    - 98580864606142464*a42*h^2*p1n^2*s2*w1
    + 21678662355517440*a42*h^2*p1n^2*w1^3
    - 123226080757678080*a42*h^2*p1n*p21n^2
    + 410753602525593600*a42*h^2*p1n*p21n*p32n*w1
    + 312172737919451136*a42*h^2*p1n*p21n*s2*w1^2
    - 112909699768320000*a42*h^2*p1n*p21n*w1^4
    - 98580864606142464*a42*h^2*p1n*p32n^2*s2
    - 227625954732933120*a42*h^2*p1n*p32n^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 211–220, preserving left association. -/
private abbrev order72Part05SpeedTChunk22 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 433573247110348800*a42*h^2*p1n*p32n*s2*w1^3
    + 186677370283622400*a42*h^2*p1n*p32n*w1^5
    - 115117711674900480*a42*h^2*p1n*s2*w1^6
    + 70592396358182400*a42*h^2*p1n*w1^8
    + 68458933754265600*a42*h^2*p21n^3*w1
    - 98580864606142464*a42*h^2*p21n^2*p32n*s2
    - 227625954732933120*a42*h^2*p21n^2*p32n*w1^2
    - 216786623555174400*a42*h^2*p21n^2*s2*w1^3
    + 93338685141811200*a42*h^2*p21n^2*w1^5
    + 130071974133104640*a42*h^2*p21n*p32n^3

set_option maxHeartbeats 64000000 in
/-- Monomials 221–230, preserving left association. -/
private abbrev order72Part05SpeedTChunk23 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 312172737919451136*a42*h^2*p21n*p32n^2*s2*w1
    + 180655519629312000*a42*h^2*p21n*p32n^2*w1^3
    + 560032110850867200*a42*h^2*p21n*p32n*s2*w1^4
    - 263811422588313600*a42*h^2*p21n*p32n*w1^6
    + 117858609571921920*a42*h^2*p21n*s2*w1^7
    - 72411202061452800*a42*h^2*p21n*w1^9
    - 86714649422069760*a42*h^2*p32n^4*w1
    - 216786623555174400*a42*h^2*p32n^3*s2*w1^2
    - 19445559404544000*a42*h^2*p32n^3*w1^4
    - 345353135024701440*a42*h^2*p32n^2*s2*w1^5

set_option maxHeartbeats 64000000 in
/-- Monomials 231–240, preserving left association. -/
private abbrev order72Part05SpeedTChunk24 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 171877138959052800*a42*h^2*p32n^2*w1^7
    - 120313997271336960*a42*h^2*p32n*s2*w1^8
    + 74035812364113600*a42*h^2*p32n*w1^10
    - 11325854681406720*a42*h^2*s2*w1^11
    + 7431583778665200*a42*h^2*w1^13
    + 79623006028038144*a42*h*p0*p21n*u2
    - 172516513060749312*a42*h*p0*p32n*u2*w1
    - 94844147805388800*a42*h*p0*u2*w1^4
    + 39811503014019072*a42*h*p1n^2*u2
    - 172516513060749312*a42*h*p1n*p21n*u2*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 241–250, preserving left association. -/
private abbrev order72Part05SpeedTChunk25 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 273151145679519744*a42*h*p1n*p32n*u2*w1^2
    + 98005619398901760*a42*h*p1n*u2*w1^5
    + 136575572839759872*a42*h*p21n^2*u2*w1^2
    - 86258256530374656*a42*h*p21n*p32n^2*u2
    - 379376591221555200*a42*h*p21n*p32n*u2*w1^3
    - 9749755840167936*a42*h*p21n*q1
    - 100727997715537920*a42*h*p21n*u2*w1^6
    + 91050381893173248*a42*h*p32n^3*u2*w1
    + 245014048497254400*a42*h*p32n^2*u2*w1^4
    + 11374715146862592*a42*h*p32n*q1*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 251–260, preserving left association. -/
private abbrev order72Part05SpeedTChunk26 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 103126283375431680*a42*h*p32n*u2*w1^7
    + 3251799353327616*a42*h*q1*w1^4
    + 10722427997561280*a42*h*u2*w1^10
    - 61613040378839040*a42*p0*q53*w1^2
    + 56873575734312960*a42*p1n*p32n*q53
    - 19499511680335872*a42*p1n*q2
    + 65035987066552320*a42*p1n*q53*w1^3
    + 28436787867156480*a42*p21n^2*q53
    - 123226080757678080*a42*p21n*p32n*q53*w1
    + 22749430293725184*a42*p21n*q2*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 261–270, preserving left association. -/
private abbrev order72Part05SpeedTChunk27 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 67745819860992000*a42*p21n*q53*w1^4
    + 97553980599828480*a42*p32n^2*q53*w1^2
    - 24645216151535616*a42*p32n*q2*w1^2
    + 70004013856358400*a42*p32n*q53*w1^5
    - 5419665588879360*a42*q2*w1^5
    + 9207703872806400*a42*q53*w1^8
    - 58498535041007616*b63*h*p0*p1n
    + 68248290881175552*b63*h*p0*p21n*w1
    - 73935648454606848*b63*h*p0*p32n*w1^2
    - 16258996766638080*b63*h*p0*w1^5

set_option maxHeartbeats 64000000 in
/-- Monomials 271–280, preserving left association. -/
private abbrev order72Part05SpeedTChunk28 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 34124145440587776*b63*h*p1n^2*w1
    - 73935648454606848*b63*h*p1n*p21n*w1^2
    + 34124145440587776*b63*h*p1n*p32n^2
    + 78043184479862784*b63*h*p1n*p32n*w1^3
    + 14000802771271680*b63*h*p1n*w1^6
    + 34124145440587776*b63*h*p21n^2*p32n
    + 39021592239931392*b63*h*p21n^2*w1^3
    - 73935648454606848*b63*h*p21n*p32n^2*w1
    - 81294983833190400*b63*h*p21n*p32n*w1^4
    - 12334040536596480*b63*h*p21n*w1^7

set_option maxHeartbeats 64000000 in
/-- Monomials 281–290, preserving left association. -/
private abbrev order72Part05SpeedTChunk29 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 39021592239931392*b63*h*p32n^3*w1^2
    + 42002408313815040*b63*h*p32n^2*w1^5
    + 11049244647367680*b63*h*p32n*w1^8
    + 835513869939840*b63*h*w1^11
    + 18483912113651712*h^2*lambda*p0^2*w1^2
    - 34124145440587776*h^2*lambda*p0*p1n*p32n
    - 39021592239931392*h^2*lambda*p0*p1n*w1^3
    - 17062072720293888*h^2*lambda*p0*p21n^2
    + 73935648454606848*h^2*lambda*p0*p21n*p32n*w1
    + 40647491916595200*h^2*lambda*p0*p21n*w1^4

set_option maxHeartbeats 64000000 in
/-- Monomials 291–300, preserving left association. -/
private abbrev order72Part05SpeedTChunk30 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 58532388359897088*h^2*lambda*p0*p32n^2*w1^2
    - 42002408313815040*h^2*lambda*p0*p32n*w1^5
    - 5524622323683840*h^2*lambda*p0*w1^8
    - 17062072720293888*h^2*lambda*p1n^2*p21n
    + 36967824227303424*h^2*lambda*p1n^2*p32n*w1
    + 20323745958297600*h^2*lambda*p1n^2*w1^4
    + 36967824227303424*h^2*lambda*p1n*p21n^2*w1
    - 117064776719794176*h^2*lambda*p1n*p21n*p32n*w1^2
    - 42002408313815040*h^2*lambda*p1n*p21n*w1^5
    + 12322608075767808*h^2*lambda*p1n*p32n^3

set_option maxHeartbeats 64000000 in
/-- Monomials 301–310, preserving left association. -/
private abbrev order72Part05SpeedTChunk31 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 81294983833190400*h^2*lambda*p1n*p32n^2*w1^3
    + 43169141878087680*h^2*lambda*p1n*p32n*w1^6
    + 5013083219639040*h^2*lambda*p1n*w1^9
    - 19510796119965696*h^2*lambda*p21n^3*w1^2
    + 18483912113651712*h^2*lambda*p21n^2*p32n^2
    + 81294983833190400*h^2*lambda*p21n^2*p32n*w1^3
    + 21584570939043840*h^2*lambda*p21n^2*w1^6
    - 39021592239931392*h^2*lambda*p21n*p32n^3*w1
    - 105006020784537600*h^2*lambda*p21n*p32n^2*w1^4
    - 44196978589470720*h^2*lambda*p21n*p32n*w1^7

set_option maxHeartbeats 64000000 in
/-- Monomials 311–320, preserving left association. -/
private abbrev order72Part05SpeedTChunk32 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 4595326284669120*h^2*lambda*p21n*w1^10
    + 20323745958297600*h^2*lambda*p32n^4*w1^2
    + 43169141878087680*h^2*lambda*p32n^3*w1^5
    + 22558874488375680*h^2*lambda*p32n^2*w1^8
    + 4247195505527520*h^2*lambda*p32n*w1^11
    + 264207280442805*h^2*lambda*w1^14
    + 56873575734312960*h^2*p0^2*p32n
    + 45498860587450368*h^2*p0^2*s2*w1
    - 27383573501706240*h^2*p0^2*w1^3
    + 113747151468625920*h^2*p0*p1n*p21n

set_option maxHeartbeats 64000000 in
/-- Monomials 321–330, preserving left association. -/
private abbrev order72Part05SpeedTChunk33 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 75831434312417280*h^2*p0*p1n*p32n*w1
    - 98580864606142464*h^2*p0*p1n*s2*w1^2
    + 59616321477672960*h^2*p0*p1n*w1^4
    - 37915717156208640*h^2*p0*p21n^2*w1
    + 90997721174900736*h^2*p0*p21n*p32n*s2
    + 20537680126279680*h^2*p0*p21n*p32n*w1^2
    + 104057579306483712*h^2*p0*p21n*s2*w1^3
    - 63229431870259200*h^2*p0*p21n*w1^5
    - 41075360252559360*h^2*p0*p32n^3
    - 98580864606142464*h^2*p0*p32n^2*s2*w1

set_option maxHeartbeats 64000000 in
/-- Monomials 331–340, preserving left association. -/
private abbrev order72Part05SpeedTChunk34 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 21678662355517440*h^2*p0*p32n^2*w1^3
    - 108393311777587200*h^2*p0*p32n*s2*w1^4
    + 66114901975449600*h^2*p0*p32n*w1^6
    - 16445387382128640*h^2*p0*s2*w1^7
    + 10912834219622400*h^2*p0*w1^9
    + 18957858578104320*h^2*p1n^3
    - 37915717156208640*h^2*p1n^2*p21n*w1
    + 45498860587450368*h^2*p1n^2*p32n*s2
    + 10268840063139840*h^2*p1n^2*p32n*w1^2
    + 52028789653241856*h^2*p1n^2*s2*w1^3

set_option maxHeartbeats 64000000 in
/-- Monomials 341–350, preserving left association. -/
private abbrev order72Part05SpeedTChunk35 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 31614715935129600*h^2*p1n^2*w1^5
    + 45498860587450368*h^2*p1n*p21n^2*s2
    + 10268840063139840*h^2*p1n*p21n^2*w1^2
    - 123226080757678080*h^2*p1n*p21n*p32n^2
    - 197161729212284928*h^2*p1n*p21n*p32n*s2*w1
    + 43357324711034880*h^2*p1n*p21n*p32n*w1^3
    - 108393311777587200*h^2*p1n*p21n*s2*w1^4
    + 66114901975449600*h^2*p1n*p21n*w1^6
    + 68458933754265600*h^2*p1n*p32n^3*w1
    + 156086368959725568*h^2*p1n*p32n^2*s2*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 351–360, preserving left association. -/
private abbrev order72Part05SpeedTChunk36 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 56454849884160000*h^2*p1n*p32n^2*w1^4
    + 112006422170173440*h^2*p1n*p32n*s2*w1^5
    - 68522447425536000*h^2*p1n*p32n*w1^7
    + 14732326196490240*h^2*p1n*s2*w1^8
    - 9747661815964800*h^2*p1n*w1^10
    - 41075360252559360*h^2*p21n^3*p32n
    - 32860288202047488*h^2*p21n^3*s2*w1
    + 7226220785172480*h^2*p21n^3*w1^3
    + 102688400631398400*h^2*p21n^2*p32n^2*w1
    + 156086368959725568*h^2*p21n^2*p32n*s2*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 361–370, preserving left association. -/
private abbrev order72Part05SpeedTChunk37 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 56454849884160000*h^2*p21n^2*p32n*w1^4
    + 56003211085086720*h^2*p21n^2*s2*w1^5
    - 34261223712768000*h^2*p21n^2*w1^7
    - 32860288202047488*h^2*p21n*p32n^3*s2
    - 75875318244311040*h^2*p21n*p32n^3*w1^2
    - 216786623555174400*h^2*p21n*p32n^2*s2*w1^3
    + 93338685141811200*h^2*p21n*p32n^2*w1^5
    - 115117711674900480*h^2*p21n*p32n*s2*w1^6
    + 70592396358182400*h^2*p21n*p32n*w1^8
    - 13368221919037440*h^2*p21n*s2*w1^9

set_option maxHeartbeats 64000000 in
/-- Monomials 371–380, preserving left association. -/
private abbrev order72Part05SpeedTChunk38 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 8819313071587200*h^2*p21n*w1^11
    + 6503598706655232*h^2*p32n^5
    + 26014394826620928*h^2*p32n^4*s2*w1
    + 15054626635776000*h^2*p32n^4*w1^3
    + 93338685141811200*h^2*p32n^3*s2*w1^4
    - 43968570431385600*h^2*p32n^3*w1^6
    + 58929304785960960*h^2*p32n^2*s2*w1^7
    - 36205601030726400*h^2*p32n^2*w1^9
    + 12254203425784320*h^2*p32n*s2*w1^10
    - 8061806283640200*h^2*p32n*w1^12

set_option maxHeartbeats 64000000 in
/-- Monomials 381–390, preserving left association. -/
private abbrev order72Part05SpeedTChunk39 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 810718230399840*h^2*s2*w1^13
    - 547985470548040*h^2*w1^15
    - 34124145440587776*h*p0^2*u2
    + 79623006028038144*h*p0*p1n*u2*w1
    - 86258256530374656*h*p0*p21n*u2*w1^2
    + 39811503014019072*h*p0*p32n^2*u2
    + 91050381893173248*h*p0*p32n*u2*w1^3
    + 58498535041007616*h*p0*q1
    + 16334269899816960*h*p0*u2*w1^6
    - 43129128265187328*h*p1n^2*u2*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 391–400, preserving left association. -/
private abbrev order72Part05SpeedTChunk40 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 79623006028038144*h*p1n*p21n*p32n*u2
    + 91050381893173248*h*p1n*p21n*u2*w1^3
    - 86258256530374656*h*p1n*p32n^2*u2*w1
    - 94844147805388800*h*p1n*p32n*u2*w1^4
    - 9749755840167936*h*p1n*q1*w1
    - 14389713959362560*h*p1n*u2*w1^7
    + 13270501004673024*h*p21n^3*u2
    - 86258256530374656*h*p21n^2*p32n*u2*w1
    - 47422073902694400*h*p21n^2*u2*w1^4
    + 136575572839759872*h*p21n*p32n^2*u2*w1^2

set_option maxHeartbeats 64000000 in
/-- Monomials 401–410, preserving left association. -/
private abbrev order72Part05SpeedTChunk41 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    + 98005619398901760*h*p21n*p32n*u2*w1^5
    + 5687357573431296*h*p21n*q1*w1^2
    + 12890785421928960*h*p21n*u2*w1^8
    - 7188188044197888*h*p32n^4*u2
    - 63229431870259200*h*p32n^3*u2*w1^3
    - 4874877920083968*h*p32n^2*q1
    - 50363998857768960*h*p32n^2*u2*w1^6
    - 4107536025255936*h*p32n*q1*w1^3
    - 11697194179157760*h*p32n*u2*w1^9
    - 451638799073280*h*q1*w1^6

set_option maxHeartbeats 64000000 in
/-- Monomials 411–420, preserving left association. -/
private abbrev order72Part05SpeedTChunk42 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 825843570519240*h*u2*w1^12
    - 48748779200839680*p0*p21n*q53
    + 56873575734312960*p0*p32n*q53*w1
    - 19499511680335872*p0*q2*w1
    + 16258996766638080*p0*q53*w1^4
    - 24374389600419840*p1n^2*q53
    + 56873575734312960*p1n*p21n*q53*w1
    - 61613040378839040*p1n*p32n*q53*w1^2
    + 11374715146862592*p1n*q2*w1^2
    - 13549163972198400*p1n*q53*w1^5

set_option maxHeartbeats 64000000 in
/-- Monomials 421–430, preserving left association. -/
private abbrev order72Part05SpeedTChunk43 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 30806520189419520*p21n^2*q53*w1^2
    + 28436787867156480*p21n*p32n^2*q53
    - 19499511680335872*p21n*p32n*q2
    + 65035987066552320*p21n*p32n*q53*w1^3
    - 8215072050511872*p21n*q2*w1^3
    + 11667335642726400*p21n*q53*w1^6
    - 20537680126279680*p32n^3*q53*w1
    + 11374715146862592*p32n^2*q2*w1
    - 33872909930496000*p32n^2*q53*w1^4
    + 6503598706655232*p32n*q2*w1^4

set_option maxHeartbeats 64000000 in
/-- Monomials 431–433, preserving left association. -/
private abbrev order72Part05SpeedTChunk44 (acc : R)
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
    acc
    - 10278367113830400*p32n*q53*w1^7
    + 666704893870080*q2*w1^7
    - 835513869939840*q53*w1^10

set_option maxHeartbeats 64000000 in
/-- Remaining factor after `h^3` is removed on the `p32 = h · p32n`,
`p21 = h · p21n`, `p1 = h · p1n` substitution. -/
def degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
  order72Part05SpeedTChunk44
    (order72Part05SpeedTChunk43
    (order72Part05SpeedTChunk42
    (order72Part05SpeedTChunk41
    (order72Part05SpeedTChunk40
    (order72Part05SpeedTChunk39
    (order72Part05SpeedTChunk38
    (order72Part05SpeedTChunk37
    (order72Part05SpeedTChunk36
    (order72Part05SpeedTChunk35
    (order72Part05SpeedTChunk34
    (order72Part05SpeedTChunk33
    (order72Part05SpeedTChunk32
    (order72Part05SpeedTChunk31
    (order72Part05SpeedTChunk30
    (order72Part05SpeedTChunk29
    (order72Part05SpeedTChunk28
    (order72Part05SpeedTChunk27
    (order72Part05SpeedTChunk26
    (order72Part05SpeedTChunk25
    (order72Part05SpeedTChunk24
    (order72Part05SpeedTChunk23
    (order72Part05SpeedTChunk22
    (order72Part05SpeedTChunk21
    (order72Part05SpeedTChunk20
    (order72Part05SpeedTChunk19
    (order72Part05SpeedTChunk18
    (order72Part05SpeedTChunk17
    (order72Part05SpeedTChunk16
    (order72Part05SpeedTChunk15
    (order72Part05SpeedTChunk14
    (order72Part05SpeedTChunk13
    (order72Part05SpeedTChunk12
    (order72Part05SpeedTChunk11
    (order72Part05SpeedTChunk10
    (order72Part05SpeedTChunk09
    (order72Part05SpeedTChunk08
    (order72Part05SpeedTChunk07
    (order72Part05SpeedTChunk06
    (order72Part05SpeedTChunk05
    (order72Part05SpeedTChunk04
    (order72Part05SpeedTChunk03
    (order72Part05SpeedTChunk02
    (order72Part05SpeedTChunk01 h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
    h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda

-- Realize the shared equation here before independent downstream consumers.
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610.eq_1

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
