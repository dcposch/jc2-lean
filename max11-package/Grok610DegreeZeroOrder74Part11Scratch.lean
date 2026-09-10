import Grok610DegreeZeroOrder73Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 64000000 in
/-- Original monomials 1–10; preserves left association. -/
private abbrev order74Part11SpeedT_chunk01
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    18957858578104320*p1^3
    - 90327759814656000*a42^3*p32^3
    - 43968570431385600*p32^3*w1^6
    - 41075360252559360*p0*p32^3
    - 4874877920083968*q1*p32^2
    - 3080652018941952*q3*a42^4
    - 770877533537280*q3*w1^8
    - 547985470548040*h^3*w1^15
    + 7226220785172480*p21^3*w1^3
    - 123226080757678080*a42*p1*p21^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 11–20; preserves left association. -/
private abbrev order74Part11SpeedT_chunk02 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 123226080757678080*a42*p32*p1^2
    - 66841109595187200*a42^4*h^3*w1^7
    - 56454849884160000*p1*p32^2*w1^4
    - 56454849884160000*p32*p21^2*w1^4
    - 50363998857768960*u2*p32^2*w1^6
    - 48748779200839680*p0*p21*q53
    - 47422073902694400*u2*p21^2*w1^4
    - 43129128265187328*u2*a42^2*p21^2
    - 43129128265187328*u2*p1^2*w1^2
    - 38999023360671744*p0*p32*q41n

set_option maxHeartbeats 64000000 in
/-- Original monomials 21–30; preserves left association. -/
private abbrev order74Part11SpeedT_chunk03 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 37915717156208640*p21*w1*p1^2
    - 37752848938022400*a42^2*h^3*w1^11
    - 36205601030726400*h*p32^2*w1^9
    - 34375427791810560*a42^5*h^3*w1^5
    - 34261223712768000*h*p21^2*w1^7
    - 34124145440587776*u2*h^2*p0^2
    - 32860288202047488*s2*w1*p21^3
    - 31614715935129600*h*p1^2*w1^5
    - 29249267520503808*a42*p0*q3
    - 27383573501706240*h^3*p0^2*w1^3

set_option maxHeartbeats 64000000 in
/-- Original monomials 31–40; preserves left association. -/
private abbrev order74Part11SpeedT_chunk04 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 27098327944396800*p1*a42^5*h^2
    - 20537680126279680*p21*q53*a42^3
    - 20323745958297600*q3*a42^2*w1^4
    - 19510796119965696*lambda*p21^3*w1^2
    - 19499511680335872*a42*p1*q2
    - 19445559404544000*a42*p32^3*w1^4
    - 17062072720293888*lambda*p21*p1^2
    - 16430144101023744*p32*q41n*a42^3
    - 15556447523635200*w1*a42^7*h^3
    - 13549163972198400*p1*q53*w1^5

set_option maxHeartbeats 64000000 in
/-- Original monomials 41–50; preserves left association. -/
private abbrev order74Part11SpeedT_chunk05 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 10839331177758720*p21*q41n*w1^5
    - 10278367113830400*p32*q53*w1^7
    - 9747661815964800*p1*h^2*w1^10
    - 8215072050511872*p21*q2*w1^3
    - 8061806283640200*p32*h^2*w1^12
    - 3161471593512960*u2*a42^6*h^2
    - 1000057340805120*lambda*a42^7*h^3
    - 835513869939840*h*q53*w1^10
    - 825843570519240*u2*h^2*w1^12
    - 451638799073280*q1*h^2*w1^6

set_option maxHeartbeats 64000000 in
/-- Original monomials 51–60; preserves left association. -/
private abbrev order74Part11SpeedT_chunk06 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 264207280442805*lambda*h^3*w1^14
    + 666704893870080*h*q2*w1^7
    + 810718230399840*s2*h^3*w1^13
    + 818462566471680*h*q41n*w1^9
    + 835513869939840*b63*h^2*w1^11
    + 1895785857810432*q1*a42^3*h^2
    + 3251799353327616*h*q53*a42^5
    + 6503598706655232*p32*q2*w1^4
    + 7000401385635840*a42*q3*w1^6
    + 7431583778665200*a42*h^3*w1^13

set_option maxHeartbeats 64000000 in
/-- Original monomials 61–70; preserves left association. -/
private abbrev order74Part11SpeedT_chunk07 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 8819313071587200*p21*h^2*w1^11
    + 9333868514181120*p32*q41n*w1^6
    + 10268840063139840*p1*p21^2*w1^2
    + 10268840063139840*p32*p1^2*w1^2
    + 10912834219622400*p0*h^3*w1^9
    + 11374715146862592*p1*q2*w1^2
    + 11374715146862592*p32*q2*a42^2
    + 11667335642726400*p21*q53*w1^6
    + 12322608075767808*a42*lambda*p21^3
    + 13007197413310464*p1*q41n*w1^4

set_option maxHeartbeats 64000000 in
/-- Original monomials 71–80; preserves left association. -/
private abbrev order74Part11SpeedT_chunk08 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 17062072720293888*p0*q3*w1^2
    + 19510796119965696*q3*a42^3*w1^2
    + 22749430293725184*p1*q41n*a42^2
    + 23334671285452800*p32*a42^6*h^2
    + 34124145440587776*b63*w1*p1^2
    + 39021592239931392*b63*p21^2*w1^3
    + 39811503014019072*a42*u2*p1^2
    + 39811503014019072*p0*u2*p32^2
    + 42002408313815040*b63*p32^2*w1^5
    + 43169141878087680*lambda*p32^3*w1^5

set_option maxHeartbeats 64000000 in
/-- Original monomials 81–90; preserves left association. -/
private abbrev order74Part11SpeedT_chunk09 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 45498860587450368*p1*s2*p21^2
    + 45498860587450368*p32*s2*p1^2
    + 45525190946586624*u2*a42^3*p32^2
    + 52028789653241856*s2*a42^2*p32^3
    + 56873575734312960*p32*h^2*p0^2
    + 58498535041007616*p0*q1*h^2
    + 63954284263833600*a42^6*h^3*w1^3
    + 68458933754265600*a42*w1*p21^3
    + 85098634901280000*a42^3*h^3*w1^9
    + 93338685141811200*p21*p32^2*w1^5

set_option maxHeartbeats 64000000 in
/-- Original monomials 91–100; preserves left association. -/
private abbrev order74Part11SpeedT_chunk10 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 93338685141811200*s2*p32^3*w1^4
    + 195107961199656960*p1*a42^2*p32^2
    + 195107961199656960*p32*a42^2*p21^2
    + 293565219397632000*a42^2*p32^3*w1^2
    - 520287896532418560*p21*w1*a42^2*p32^2
    - 388911188090880000*h*a42^3*p32^2*w1^3
    - 284532443416166400*u2*a42^2*p32^2*w1^2
    - 227625954732933120*a42*p1*p32^2*w1^2
    - 227625954732933120*a42*p32*p21^2*w1^2
    - 221679377211801600*p32*a42^5*h^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 101–110; preserves left association. -/
private abbrev order74Part11SpeedT_chunk11 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 216786623555174400*a42*s2*p32^3*w1^2
    - 216786623555174400*p21*s2*p32^2*w1^3
    - 213056036834659200*p32*a42^2*h^2*w1^8
    - 194455594045440000*p21*a42^4*h^2*w1^3
    - 173429298844139520*h*w1*a42^3*p21^2
    - 162589967666380800*a42*b63*p32^2*w1^3
    - 160418663028449280*s2*a42^3*h^3*w1^7
    - 140008027712716800*a42*lambda*p32^3*w1^3
    - 135491639721984000*h*p21*p32*a42^4
    - 135491639721984000*p32*q53*a42^2*w1^3

set_option maxHeartbeats 64000000 in
/-- Original monomials 111–120; preserves left association. -/
private abbrev order74Part11SpeedT_chunk12 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 131905711294156800*p1*a42^2*h^2*w1^6
    - 125909997144422400*u2*a42^4*h^2*w1^4
    - 123226080757678080*p0*p1*a42^2*h^2
    - 115117711674900480*s2*a42^5*h^3*w1^3
    - 105006020784537600*lambda*p21*p32^2*w1^4
    - 98580864606142464*a42*p1*s2*p32^2
    - 98580864606142464*a42*p32*s2*p21^2
    - 94844147805388800*p1*p32*u2*w1^4
    - 86714649422069760*p0*w1*a42^4*h^3
    - 86338283756175360*b63*a42^3*h^2*w1^5

set_option maxHeartbeats 64000000 in
/-- Original monomials 121–130; preserves left association. -/
private abbrev order74Part11SpeedT_chunk13 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 86258256530374656*p1*p32*u2*a42^2
    - 81294983833190400*b63*p21*p32*w1^4
    - 77344712531573760*lambda*a42^5*h^3*w1^4
    - 73935648454606848*a42*b63*w1*p21^2
    - 73935648454606848*b63*p1*p21*w1^2
    - 73935648454606848*b63*p21*p32*a42^2
    - 72411202061452800*a42*p21*h^2*w1^9
    - 71948569796812800*h*a42^2*p32^2*w1^5
    - 68929894270036800*lambda*a42^3*h^3*w1^8
    - 68522447425536000*a42*p0*h^3*w1^7

set_option maxHeartbeats 64000000 in
/-- Original monomials 131–140; preserves left association. -/
private abbrev order74Part11SpeedT_chunk14 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 68522447425536000*h*p1*p32*w1^7
    - 67745819860992000*a42*p21*q53*w1^4
    - 63229431870259200*p0*p21*h^2*w1^5
    - 61613040378839040*p1*q53*w1*a42^2
    - 58532388359897088*lambda*p21*a42^2*p32^2
    - 58498535041007616*b63*h*p0*p1
    - 54196655888793600*a42*p32*q41n*w1^4
    - 52637373806209920*u2*a42^2*h^2*w1^8
    - 49290432303071232*a42*p1*q41n*w1^2
    - 49290432303071232*p21*q41n*w1*a42^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 141–150; preserves left association. -/
private abbrev order74Part11SpeedT_chunk15 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 47965713197875200*p21*a42^3*h^2*w1^5
    - 37915717156208640*a42*w1*h^3*p0^2
    - 37915717156208640*h*p0*w1*p21^2
    - 36131103925862400*h*q41n*a42^3*w1^3
    - 35974284898406400*h*q53*a42^2*w1^6
    - 33872909930496000*h*q53*a42^4*w1^2
    - 28752752176791552*p0*u2*a42^3*h^2
    - 24645216151535616*a42*p32*q2*w1^2
    - 24645216151535616*b63*h*p1*a42^3
    - 21678662355517440*p32*s2*a42^5*h^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 151–160; preserves left association. -/
private abbrev order74Part11SpeedT_chunk16 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 19510796119965696*h*lambda*a42^3*p21^2
    - 19499511680335872*h*p0*q2*w1
    - 19445559404544000*p1*a42^3*h^2*w1^4
    - 17062072720293888*a42*lambda*h^3*p0^2
    - 17062072720293888*h*lambda*p0*p21^2
    - 16445387382128640*p0*s2*h^3*w1^7
    - 16430144101023744*h*p0*q41n*w1^3
    - 16258996766638080*b63*p0*h^2*w1^5
    - 16258996766638080*b63*w1*a42^5*h^2
    - 14389713959362560*h*p1*u2*w1^7

set_option maxHeartbeats 64000000 in
/-- Original monomials 161–170; preserves left association. -/
private abbrev order74Part11SpeedT_chunk17 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 13368221919037440*p21*s2*h^2*w1^9
    - 12334040536596480*b63*h*p21*w1^7
    - 11697194179157760*h*p32*u2*w1^9
    - 11325854681406720*a42*s2*h^3*w1^11
    - 10026166439278080*a42*b63*h^2*w1^9
    - 9755398059982848*lambda*p0*a42^4*h^3
    - 9749755840167936*a42*h*p21*q1
    - 9749755840167936*h*p1*q1*w1
    - 8222693691064320*a42*h*q41n*w1^7
    - 8215072050511872*h*q2*w1*a42^3

set_option maxHeartbeats 64000000 in
/-- Original monomials 171–180; preserves left association. -/
private abbrev order74Part11SpeedT_chunk18 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 6161304037883904*q1*a42^2*h^2*w1^2
    - 5524622323683840*lambda*p0*h^3*w1^8
    - 5419665588879360*a42*h*q2*w1^5
    - 4595326284669120*lambda*p21*h^2*w1^10
    - 4107536025255936*h*p32*q1*w1^3
    - 3952251373199220*a42*lambda*h^3*w1^12
    + 3251799353327616*a42*q1*h^2*w1^4
    + 4247195505527520*lambda*p32*h^2*w1^11
    + 5013083219639040*lambda*p1*h^2*w1^9
    + 5687357573431296*h*p21*q1*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 181–190; preserves left association. -/
private abbrev order74Part11SpeedT_chunk19 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 8129498383319040*lambda*p21*a42^5*h^2
    + 9207703872806400*a42*h*q53*w1^8
    + 10722427997561280*a42*u2*h^2*w1^10
    + 11049244647367680*b63*h*p32*w1^8
    + 12254203425784320*p32*s2*h^2*w1^10
    + 12890785421928960*h*p21*u2*w1^8
    + 13007197413310464*h*q2*a42^2*w1^3
    + 13007197413310464*h*q41n*w1*a42^4
    + 14000802771271680*b63*h*p1*w1^6
    + 14732326196490240*p1*s2*h^2*w1^8

set_option maxHeartbeats 64000000 in
/-- Original monomials 191–200; preserves left association. -/
private abbrev order74Part11SpeedT_chunk20 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 16258996766638080*h*p0*q53*w1^4
    + 16334269899816960*p0*u2*h^2*w1^6
    + 18483912113651712*h*lambda*a42^2*p1^2
    + 18483912113651712*lambda*h^3*p0^2*w1^2
    + 18667737028362240*s2*w1*a42^6*h^3
    + 19510796119965696*b63*h*p32*a42^4
    + 20323745958297600*h*lambda*a42^4*p32^2
    + 20323745958297600*h*lambda*p1^2*w1^4
    + 21584570939043840*h*lambda*p21^2*w1^6
    + 21584570939043840*lambda*a42^6*h^3*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 201–210; preserves left association. -/
private abbrev order74Part11SpeedT_chunk21 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 21678662355517440*a42*h*p1^2*w1^3
    + 21678662355517440*h*p0*p32^2*w1^3
    + 22558874488375680*h*lambda*p32^2*w1^8
    + 22749430293725184*a42*p21*q2*w1
    + 22762595473293312*h*p21*u2*a42^4
    + 23359575280401360*lambda*a42^2*h^3*w1^10
    + 26014394826620928*p1*s2*a42^4*h^2
    + 28001605542543360*h*q41n*a42^2*w1^5
    + 28436787867156480*h*p0*q53*a42^2
    + 36967824227303424*lambda*p1*w1*p21^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 211–220; preserves left association. -/
private abbrev order74Part11SpeedT_chunk22 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 36967824227303424*lambda*p32*w1*p1^2
    + 43357324711034880*p1*p21*p32*w1^3
    + 44196978589470720*b63*a42^2*h^2*w1^7
    + 45498860587450368*s2*w1*h^3*p0^2
    + 49002809699450880*u2*a42^5*h^2*w1^2
    + 52028789653241856*a42*p21*q41n*w1^3
    + 52028789653241856*h*s2*p1^2*w1^3
    + 56003211085086720*h*s2*p21^2*w1^5
    + 56873575734312960*p0*p32*q53*w1
    + 58336678213632000*h*q53*a42^3*w1^4

set_option maxHeartbeats 64000000 in
/-- Original monomials 221–230; preserves left association. -/
private abbrev order74Part11SpeedT_chunk23 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 58929304785960960*h*s2*p32^2*w1^7
    + 59616321477672960*p0*p1*h^2*w1^4
    + 60218506543104000*p0*a42^3*h^3*w1^3
    + 61271017128921600*s2*a42^2*h^3*w1^9
    + 65035987066552320*a42*p1*q53*w1^3
    + 65035987066552320*p32*q53*w1*a42^3
    + 66114901975449600*h*p1*p21*w1^6
    + 66114901975449600*p0*p32*h^2*w1^6
    + 68248290881175552*a42*b63*p1*p21
    + 70004013856358400*a42*p32*q53*w1^5

set_option maxHeartbeats 64000000 in
/-- Original monomials 231–240; preserves left association. -/
private abbrev order74Part11SpeedT_chunk24 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 70004013856358400*b63*a42^4*h^2*w1^3
    + 70592396358182400*a42*p1*h^2*w1^8
    + 70592396358182400*h*p21*p32*w1^8
    + 74035812364113600*a42*p32*h^2*w1^10
    + 78043184479862784*b63*p1*p32*w1^3
    + 78043184479862784*p32*q41n*a42^2*w1^2
    + 81294983833190400*lambda*p1*p32^2*w1^3
    + 81294983833190400*lambda*p32*p21^2*w1^3
    + 81294983833190400*lambda*w1*a42^2*p32^3
    + 90327759814656000*h*a42^2*p21^2*w1^3

set_option maxHeartbeats 64000000 in
/-- Original monomials 241–250; preserves left association. -/
private abbrev order74Part11SpeedT_chunk25 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 91050381893173248*p1*p21*u2*w1^3
    + 93338685141811200*a42*h*p21^2*w1^5
    + 93338685141811200*p0*a42^2*h^3*w1^5
    + 97553980599828480*p21*q53*a42^2*w1^2
    + 98005619398901760*p21*p32*u2*w1^5
    + 99360535796121600*p21*w1*a42^5*h^2
    + 102688400631398400*h*w1*a42^2*p1^2
    + 105274747612419840*lambda*a42^4*h^3*w1^6
    + 113747151468625920*h*p0*p1*p21
    + 117064776719794176*b63*w1*a42^2*p32^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 251–260; preserves left association. -/
private abbrev order74Part11SpeedT_chunk26 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 120313997271336960*u2*a42^3*h^2*w1^6
    + 130071974133104640*h*p1*p21*a42^3
    + 130071974133104640*p0*p32*a42^3*h^2
    + 136575572839759872*a42*u2*p21^2*w1^2
    + 143230949132544000*p32*a42^3*h^2*w1^6
    + 146782609698816000*p1*a42^4*h^2*w1^2
    + 156086368959725568*p1*s2*p32^2*w1^2
    + 156086368959725568*p32*s2*p21^2*w1^2
    + 171877138959052800*a42*h*p32^2*w1^7
    + 171877138959052800*p21*a42^2*h^2*w1^7

set_option maxHeartbeats 64000000 in
/-- Original monomials 261–270; preserves left association. -/
private abbrev order74Part11SpeedT_chunk27 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 180655519629312000*a42*p21*p32^2*w1^3
    + 206252566750863360*s2*a42^4*h^3*w1^5
    + 209849995240704000*p32*a42^4*h^2*w1^4
    + 245014048497254400*a42*u2*p32^2*w1^4
    + 248401339490304000*h*w1*a42^4*p32^2
    - 575588558374502400*p32*s2*a42^3*h^2*w1^4
    - 379376591221555200*a42*p21*p32*u2*w1^3
    - 346858597688279040*h*p1*p32*w1*a42^3
    - 345353135024701440*a42*h*s2*p32^2*w1^5
    - 345353135024701440*p21*s2*a42^2*h^2*w1^5

set_option maxHeartbeats 64000000 in
/-- Original monomials 271–280; preserves left association. -/
private abbrev order74Part11SpeedT_chunk28 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 309378850126295040*lambda*p32*a42^3*h^2*w1^5
    - 302183993146613760*h*p32*u2*a42^2*w1^5
    - 263811422588313600*a42*h*p21*p32*w1^6
    - 246452161515356160*a42*h*p0*p21*p32
    - 227625954732933120*h*p1*p21*a42^2*w1^2
    - 227625954732933120*p0*p32*a42^2*h^2*w1^2
    - 216786623555174400*a42*h*s2*p21^2*w1^3
    - 216786623555174400*h*s2*w1*a42^3*p32^2
    - 216786623555174400*p0*s2*a42^2*h^3*w1^3
    - 216786623555174400*p1*s2*a42^3*h^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 281–290; preserves left association. -/
private abbrev order74Part11SpeedT_chunk29 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 210012041569075200*h*lambda*a42^3*p32^2*w1^2
    - 197161729212284928*p1*p21*p32*s2*w1
    - 189688295610777600*h*p1*u2*a42^2*w1^3
    - 189688295610777600*h*p21*u2*a42^3*w1^2
    - 172516513060749312*a42*p1*p21*u2*w1
    - 162589967666380800*b63*h*p21*a42^2*w1^3
    - 162589967666380800*b63*h*p32*a42^3*w1^2
    - 154689425063147520*a42*h*lambda*p32^2*w1^6
    - 154689425063147520*lambda*p21*a42^2*h^2*w1^6
    - 147871296909213696*a42*b63*p1*p32*w1

set_option maxHeartbeats 64000000 in
/-- Original monomials 291–300; preserves left association. -/
private abbrev order74Part11SpeedT_chunk30 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 140008027712716800*lambda*p1*a42^3*h^2*w1^3
    - 120313997271336960*a42*p32*s2*h^2*w1^8
    - 117064776719794176*a42*lambda*p1*w1*p32^2
    - 117064776719794176*a42*lambda*p32*w1*p21^2
    - 117064776719794176*lambda*p1*p21*p32*w1^2
    - 115117711674900480*a42*p1*s2*h^2*w1^6
    - 115117711674900480*h*p21*p32*s2*w1^6
    - 112909699768320000*a42*h*p1*p21*w1^4
    - 112909699768320000*a42*p0*p32*h^2*w1^4
    - 108393311777587200*h*p1*p21*s2*w1^4

set_option maxHeartbeats 64000000 in
/-- Original monomials 301–310; preserves left association. -/
private abbrev order74Part11SpeedT_chunk31 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 108393311777587200*p0*p32*s2*h^2*w1^4
    - 108393311777587200*p21*s2*w1*a42^4*h^2
    - 105006020784537600*a42*h*lambda*p21^2*w1^4
    - 105006020784537600*lambda*p0*a42^2*h^3*w1^4
    - 105006020784537600*lambda*p21*a42^4*h^2*w1^2
    - 100727997715537920*a42*h*p21*u2*w1^6
    - 98580864606142464*a42*h*s2*w1*p1^2
    - 98580864606142464*h*p0*s2*w1*p32^2
    - 98580864606142464*h*p1*p21*s2*a42^2
    - 98580864606142464*p0*p1*s2*h^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 311–320; preserves left association. -/
private abbrev order74Part11SpeedT_chunk32 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 98580864606142464*p0*p32*s2*a42^2*h^2
    - 94844147805388800*a42*p0*u2*h^2*w1^4
    - 94844147805388800*h*p32*u2*w1*a42^4
    - 86338283756175360*a42*b63*h*p32*w1^6
    - 86258256530374656*h*p0*p21*u2*w1^2
    - 81294983833190400*a42*b63*h*p1*w1^4
    - 75831434312417280*h*p0*p1*p32*w1
    - 73935648454606848*b63*h*p0*p32*w1^2
    - 73935648454606848*b63*p0*w1*a42^2*h^2
    - 61613040378839040*a42*h*p0*q53*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 321–330; preserves left association. -/
private abbrev order74Part11SpeedT_chunk33 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 58532388359897088*a42*h*lambda*p1^2*w1^2
    - 58532388359897088*h*lambda*p0*p32^2*w1^2
    - 58336678213632000*h*p21*p32*a42^2*w1^4
    - 45953262846691200*a42*lambda*p32*h^2*w1^9
    - 44196978589470720*a42*lambda*p1*h^2*w1^7
    - 44196978589470720*h*lambda*p21*p32*w1^7
    - 42002408313815040*h*lambda*p1*p21*w1^5
    - 42002408313815040*lambda*p0*p32*h^2*w1^5
    - 42002408313815040*lambda*p32*w1*a42^5*h^2
    - 39021592239931392*h*lambda*p1*p32*a42^3

set_option maxHeartbeats 64000000 in
/-- Original monomials 331–340; preserves left association. -/
private abbrev order74Part11SpeedT_chunk34 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 39021592239931392*lambda*p0*p1*h^2*w1^3
    - 34124145440587776*h*lambda*p0*p1*p32
    + 11374715146862592*a42*h*p32*q1*w1
    + 20537680126279680*a42*p0*p1*h^2*w1^2
    + 20537680126279680*h*p0*p21*p32*w1^2
    + 36967824227303424*a42*h*lambda*p0*p32^2
    + 36967824227303424*lambda*p0*p21*a42^2*h^2
    + 40647491916595200*lambda*p0*p21*h^2*w1^4
    + 40647491916595200*lambda*p1*w1*a42^4*h^2
    + 43169141878087680*a42*lambda*p0*h^3*w1^6

set_option maxHeartbeats 64000000 in
/-- Original monomials 341–350; preserves left association. -/
private abbrev order74Part11SpeedT_chunk35 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 43169141878087680*h*lambda*p1*p32*w1^6
    + 43357324711034880*a42*p0*p21*h^2*w1^3
    + 45117748976751360*a42*lambda*p21*h^2*w1^8
    + 45498860587450368*a42*h*p0*q41n*w1
    + 68248290881175552*a42*b63*h*p0*p32
    + 68248290881175552*b63*h*p0*p21*w1
    + 73935648454606848*a42*lambda*p1*p21*p32
    + 78043184479862784*a42*b63*p0*h^2*w1^3
    + 78043184479862784*b63*h*p21*w1*a42^3
    + 79623006028038144*a42*h*p0*p21*u2

set_option maxHeartbeats 64000000 in
/-- Original monomials 351–360; preserves left association. -/
private abbrev order74Part11SpeedT_chunk36 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 79623006028038144*h*p0*p1*u2*w1
    + 81294983833190400*lambda*p0*a42^3*h^3*w1^2
    + 84004816627630080*a42*b63*h*p21*w1^5
    + 90997721174900736*a42*p0*p1*s2*h^2
    + 90997721174900736*h*p0*p21*p32*s2
    + 91050381893173248*h*p0*p32*u2*w1^3
    + 91050381893173248*h*p1*u2*w1*a42^3
    + 98005619398901760*a42*h*p1*u2*w1^5
    + 103126283375431680*a42*h*p32*u2*w1^7
    + 104057579306483712*h*p21*p32*s2*a42^3

set_option maxHeartbeats 64000000 in
/-- Original monomials 361–370; preserves left association. -/
private abbrev order74Part11SpeedT_chunk37 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 104057579306483712*p0*p21*s2*h^2*w1^3
    + 104057579306483712*p0*s2*w1*a42^3*h^3
    + 112006422170173440*a42*p0*s2*h^3*w1^5
    + 112006422170173440*h*p1*p32*s2*w1^5
    + 117064776719794176*b63*h*p1*a42^2*w1^2
    + 117858609571921920*a42*p21*s2*h^2*w1^7
    + 121942475749785600*h*lambda*a42^2*p21^2*w1^2
    + 129507425634263040*lambda*p1*a42^2*h^2*w1^5
    + 136575572839759872*p0*u2*a42^2*h^2*w1^2
    + 156086368959725568*h*s2*w1*a42^2*p21^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 371–380; preserves left association. -/
private abbrev order74Part11SpeedT_chunk38 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 180470995907005440*lambda*p32*a42^2*h^2*w1^7
    + 180655519629312000*h*p1*p32*a42^2*w1^3
    + 186677370283622400*a42*h*p1*p32*w1^5
    + 205376801262796800*a42*h*p0*w1*p32^2
    + 205376801262796800*p0*p21*w1*a42^2*h^2
    + 210012041569075200*b63*h*p32*a42^2*w1^4
    + 215845709390438400*lambda*p21*a42^3*h^2*w1^4
    + 215845709390438400*lambda*p32*a42^4*h^2*w1^3
    + 234129553439588352*a42*b63*p21*p32*w1^2
    + 243884951499571200*a42*lambda*p21*p32^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 381–390; preserves left association. -/
private abbrev order74Part11SpeedT_chunk39 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 245014048497254400*h*p21*u2*a42^2*w1^4
    + 273151145679519744*a42*p1*p32*u2*w1^2
    + 273151145679519744*p21*p32*u2*w1*a42^2
    + 280016055425433600*p1*s2*a42^2*h^2*w1^4
    + 280016055425433600*p32*s2*a42^4*h^2*w1^2
    + 312172737919451136*a42*p21*s2*w1*p32^2
    + 323768564085657600*h*lambda*a42^2*p32^2*w1^4
    + 326685397996339200*h*p32*u2*a42^3*w1^3
    + 373354740567244800*p21*s2*a42^3*h^2*w1^3
    + 410753602525593600*a42*p1*p21*p32*w1

set_option maxHeartbeats 64000000 in
/-- Original monomials 391–400; preserves left association. -/
private abbrev order74Part11SpeedT_chunk40 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 412505133501726720*p32*s2*a42^2*h^2*w1^6
    + 560032110850867200*h*s2*a42^2*p32^2*w1^3
    + 587130438795264000*h*p21*p32*a42^3*w1^2
    - 650359870665523200*h*p21*p32*s2*a42^2*w1^2
    - 433573247110348800*a42*h*p1*p32*s2*w1^3
    - 420024083138150400*h*lambda*p21*p32*a42^2*w1^3
    - 210012041569075200*a42*h*lambda*p1*p32*w1^4
    - 197161729212284928*a42*p0*p21*s2*w1*h^2
    - 172516513060749312*a42*h*p0*p32*u2*w1
    - 117064776719794176*a42*lambda*p0*p21*h^2*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 401–410; preserves left association. -/
private abbrev order74Part11SpeedT_chunk41 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    - 117064776719794176*h*lambda*p1*p21*w1*a42^2
    - 117064776719794176*lambda*p0*p32*w1*a42^2*h^2
    + 73935648454606848*a42*lambda*p0*p1*w1*h^2
    + 73935648454606848*h*lambda*p0*p21*p32*w1
    + 162589967666380800*a42*h*lambda*p1*p21*w1^3
    + 162589967666380800*a42*lambda*p0*p32*h^2*w1^3
    + 162589967666380800*h*lambda*p21*p32*w1*a42^3
    + 243884951499571200*h*lambda*p1*p32*a42^2*w1^2
    + 259014851268526080*a42*h*lambda*p21*p32*w1^5
    + 312172737919451136*a42*h*p1*p21*s2*w1^2

set_option maxHeartbeats 64000000 in
/-- Original monomials 411–413; preserves left association. -/
private abbrev order74Part11SpeedT_chunk42 (acc : R)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
    acc
    + 312172737919451136*a42*p0*p32*s2*h^2*w1^2
    + 312172737919451136*h*p1*p32*s2*w1*a42^2
    + 560032110850867200*a42*h*p21*p32*s2*w1^4

set_option maxHeartbeats 64000000 in
/-- Remaining factor after `h^2` is removed on the mixed `q41 = h · q41n`
substitution of `JetOrderTwoPlus`. -/
def degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) : R :=
  order74Part11SpeedT_chunk42
      (order74Part11SpeedT_chunk41
      (order74Part11SpeedT_chunk40
      (order74Part11SpeedT_chunk39
      (order74Part11SpeedT_chunk38
      (order74Part11SpeedT_chunk37
      (order74Part11SpeedT_chunk36
      (order74Part11SpeedT_chunk35
      (order74Part11SpeedT_chunk34
      (order74Part11SpeedT_chunk33
      (order74Part11SpeedT_chunk32
      (order74Part11SpeedT_chunk31
      (order74Part11SpeedT_chunk30
      (order74Part11SpeedT_chunk29
      (order74Part11SpeedT_chunk28
      (order74Part11SpeedT_chunk27
      (order74Part11SpeedT_chunk26
      (order74Part11SpeedT_chunk25
      (order74Part11SpeedT_chunk24
      (order74Part11SpeedT_chunk23
      (order74Part11SpeedT_chunk22
      (order74Part11SpeedT_chunk21
      (order74Part11SpeedT_chunk20
      (order74Part11SpeedT_chunk19
      (order74Part11SpeedT_chunk18
      (order74Part11SpeedT_chunk17
      (order74Part11SpeedT_chunk16
      (order74Part11SpeedT_chunk15
      (order74Part11SpeedT_chunk14
      (order74Part11SpeedT_chunk13
      (order74Part11SpeedT_chunk12
      (order74Part11SpeedT_chunk11
      (order74Part11SpeedT_chunk10
      (order74Part11SpeedT_chunk09
      (order74Part11SpeedT_chunk08
      (order74Part11SpeedT_chunk07
      (order74Part11SpeedT_chunk06
      (order74Part11SpeedT_chunk05
      (order74Part11SpeedT_chunk04
      (order74Part11SpeedT_chunk03
      (order74Part11SpeedT_chunk02
      (order74Part11SpeedT_chunk01 h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda) h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
