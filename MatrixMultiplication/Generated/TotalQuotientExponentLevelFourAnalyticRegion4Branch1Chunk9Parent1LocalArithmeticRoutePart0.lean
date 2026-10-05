import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk9Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 64369067200825098938351616 }, { target := 27, numerator := 479191944717253514318839808 }, { target := 28, numerator := 486344063295122969756434432 }, { target := 29, numerator := 71521185778694554375946240 }, { target := 30, numerator := 429127114672167326255677440 }, { target := 31, numerator := 71521185778694554375946240 }, { target := 32, numerator := 475615885428318786600042496 }, { target := 33, numerator := 486344063295122969756434432 }, { target := 34, numerator := 429127114672167326255677440 }, { target := 35, numerator := 8664791657088845262645886976 }, { target := 36, numerator := 429127114672167326255677440 }, { target := 37, numerator := 475615885428318786600042496 }, { target := 38, numerator := 475615885428318786600042496 }, { target := 39, numerator := 71521185778694554375946240 }, { target := 40, numerator := 429127114672167326255677440 }, { target := 41, numerator := 71521185778694554375946240 }, { target := 42, numerator := 486344063295122969756434432 }, { target := 43, numerator := 486344063295122969756434432 }, { target := 44, numerator := 64369067200825098938351616 }, { target := 131, numerator := 22574503330670344300134400 }, { target := 134, numerator := 77023387591253760092930048 }, { target := 136, numerator := 22574452356396486930464768 }, { target := 157, numerator := 219432397884427589822447616 }, { target := 158, numerator := 1633552295361849835344887808 }, { target := 159, numerator := 1657933672904564011991826432 }, { target := 160, numerator := 243813775427141766469386240 }, { target := 161, numerator := 1462882652562850598816317440 }, { target := 162, numerator := 243813775427141766469386240 }, { target := 163, numerator := 1621361606590492747021418496 }, { target := 164, numerator := 1657933672904564011991826432 }, { target := 165, numerator := 1462882652562850598816317440 }, { target := 166, numerator := 29538038892998225007766142976 }, { target := 167, numerator := 1462882652562850598816317440 }, { target := 168, numerator := 1621361606590492747021418496 }, { target := 169, numerator := 1621361606590492747021418496 }, { target := 170, numerator := 243813775427141766469386240 }, { target := 171, numerator := 1462882652562850598816317440 }, { target := 172, numerator := 243813775427141766469386240 }, { target := 173, numerator := 1657933672904564011991826432 }, { target := 174, numerator := 1657933672904564011991826432 }, { target := 175, numerator := 219432397884427589822447616 }, { target := 227, numerator := 1108929828797844553308569600 }, { target := 230, numerator := 3783628404304863305119301632 }, { target := 232, numerator := 1108927324782940936430682112 }, { target := 302, numerator := 12376447236959871463273267200 }, { target := 305, numerator := 42227989629340587422619009024 }, { target := 307, numerator := 12376419290368905674577936384 }, { target := 589, numerator := 1108931573956773908211302400 }, { target := 592, numerator := 3783634358723910984278212608 }, { target := 594, numerator := 1108929069937929641659465728 }, { target := 763, numerator := 22571013012811634494668800 }, { target := 766, numerator := 77011478753158401775108096 }, { target := 768, numerator := 22570962046419076472897536 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 97894111260726165661286400 }, { target := 27, numerator := 3327070164673618609900093440 }, { target := 29, numerator := 36634031769485991075265904640 }, { target := 37, numerator := 3327122001640132100059299840 }, { target := 44, numerator := 97881152019097793121484800 }, { target := 80, numerator := 70228660855450421050736640 }, { target := 82, numerator := 2820719046147127137586380800 }, { target := 85, numerator := 2821267349469914942238883840 }, { target := 92, numerator := 69685182326200661190901760 }, { target := 131, numerator := 97894111260726165661286400 }, { target := 134, numerator := 339280510856412908979486720 }, { target := 136, numerator := 97916724056820424523120640 }, { target := 157, numerator := 339280510856412908979486720 }, { target := 158, numerator := 11530929190614746879294963712 }, { target := 160, numerator := 126965890526120998213854953472 }, { target := 168, numerator := 11531108846696746568418066432 }, { target := 175, numerator := 339235596835912986698711040 }, { target := 176, numerator := 2335593036554958652550676480 }, { target := 178, numerator := 93808591563765791111879065600 }, { target := 181, numerator := 93826826475367750760797306880 }, { target := 188, numerator := 2317518583006064644791992320 }, { target := 227, numerator := 3327070164673618609900093440 }, { target := 230, numerator := 11530929190614746879294963712 }, { target := 232, numerator := 3327838692609121098393452544 }, { target := 267, numerator := 64369170963760513554579456 }, { target := 268, numerator := 479192717174661600906313728 }, { target := 269, numerator := 486344847281746102412378112 }, { target := 270, numerator := 71521301070845015060643840 }, { target := 271, numerator := 429127806425070090363863040 }, { target := 272, numerator := 71521301070845015060643840 }, { target := 273, numerator := 475616652121119350153281536 }, { target := 274, numerator := 486344847281746102412378112 }, { target := 275, numerator := 429127806425070090363863040 }, { target := 276, numerator := 8664805624732873574597001216 }, { target := 277, numerator := 429127806425070090363863040 }, { target := 278, numerator := 475616652121119350153281536 }, { target := 279, numerator := 475616652121119350153281536 }, { target := 280, numerator := 71521301070845015060643840 }, { target := 281, numerator := 429127806425070090363863040 }, { target := 282, numerator := 71521301070845015060643840 }, { target := 283, numerator := 486344847281746102412378112 }, { target := 284, numerator := 486344847281746102412378112 }, { target := 285, numerator := 64369170963760513554579456 }, { target := 286, numerator := 2335593036554958652550676480 }, { target := 288, numerator := 93808591563765791111879065600 }, { target := 291, numerator := 93826826475367750760797306880 }, { target := 298, numerator := 2317518583006064644791992320 }, { target := 302, numerator := 36634031769485991075265904640 }, { target := 305, numerator := 126965890526120998213854953472 }, { target := 307, numerator := 36642493952551402183971569664 }, { target := 573, numerator := 70228087262928130308833280 }, { target := 575, numerator := 2820696007926938328471961600 }, { target := 578, numerator := 2821244306771459253657927680 }, { target := 585, numerator := 69684613172538753176043520 }, { target := 589, numerator := 3327122001640132100059299840 }, { target := 592, numerator := 11531108846696746568418066432 }, { target := 594, numerator := 3327890541549580097823965184 }, { target := 763, numerator := 97881152019097793121484800 }, { target := 766, numerator := 339235596835912986698711040 }, { target := 768, numerator := 97903761821705674665492480 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected,
    Slot16.Left5.expected,
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot16.Left10.expected,
    Slot16.Left11.expected,
    Slot16.Left12.expected,
    Slot16.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 70228660855450421050736640 }, { target := 82, numerator := 2335593036554958652550676480 }, { target := 85, numerator := 2335593036554958652550676480 }, { target := 92, numerator := 70228087262928130308833280 }, { target := 131, numerator := 64369067200825098938351616 }, { target := 134, numerator := 219432397884427589822447616 }, { target := 136, numerator := 64369170963760513554579456 }, { target := 176, numerator := 2820719046147127137586380800 }, { target := 178, numerator := 93808591563765791111879065600 }, { target := 181, numerator := 93808591563765791111879065600 }, { target := 188, numerator := 2820696007926938328471961600 }, { target := 227, numerator := 479191944717253514318839808 }, { target := 230, numerator := 1633552295361849835344887808 }, { target := 232, numerator := 479192717174661600906313728 }, { target := 253, numerator := 486344063295122969756434432 }, { target := 256, numerator := 1657933672904564011991826432 }, { target := 258, numerator := 486344847281746102412378112 }, { target := 267, numerator := 97916724056820424523120640 }, { target := 268, numerator := 3327838692609121098393452544 }, { target := 270, numerator := 36642493952551402183971569664 }, { target := 278, numerator := 3327890541549580097823965184 }, { target := 285, numerator := 97903761821705674665492480 }, { target := 286, numerator := 2821267349469914942238883840 }, { target := 288, numerator := 93826826475367750760797306880 }, { target := 291, numerator := 93826826475367750760797306880 }, { target := 298, numerator := 2821244306771459253657927680 }, { target := 302, numerator := 71521185778694554375946240 }, { target := 305, numerator := 243813775427141766469386240 }, { target := 307, numerator := 71521301070845015060643840 }, { target := 328, numerator := 429127114672167326255677440 }, { target := 331, numerator := 1462882652562850598816317440 }, { target := 333, numerator := 429127806425070090363863040 }, { target := 342, numerator := 71521185778694554375946240 }, { target := 345, numerator := 243813775427141766469386240 }, { target := 347, numerator := 71521301070845015060643840 }, { target := 443, numerator := 475615885428318786600042496 }, { target := 446, numerator := 1621361606590492747021418496 }, { target := 448, numerator := 475616652121119350153281536 }, { target := 469, numerator := 486344063295122969756434432 }, { target := 472, numerator := 1657933672904564011991826432 }, { target := 474, numerator := 486344847281746102412378112 }, { target := 518, numerator := 429127114672167326255677440 }, { target := 521, numerator := 1462882652562850598816317440 }, { target := 523, numerator := 429127806425070090363863040 }, { target := 544, numerator := 8664791657088845262645886976 }, { target := 547, numerator := 29538038892998225007766142976 }, { target := 549, numerator := 8664805624732873574597001216 }, { target := 558, numerator := 429127114672167326255677440 }, { target := 561, numerator := 1462882652562850598816317440 }, { target := 563, numerator := 429127806425070090363863040 }, { target := 573, numerator := 69685182326200661190901760 }, { target := 575, numerator := 2317518583006064644791992320 }, { target := 578, numerator := 2317518583006064644791992320 }, { target := 585, numerator := 69684613172538753176043520 }, { target := 589, numerator := 475615885428318786600042496 }, { target := 592, numerator := 1621361606590492747021418496 }, { target := 594, numerator := 475616652121119350153281536 }, { target := 603, numerator := 475615885428318786600042496 }, { target := 606, numerator := 1621361606590492747021418496 }, { target := 608, numerator := 475616652121119350153281536 }, { target := 658, numerator := 71521185778694554375946240 }, { target := 661, numerator := 243813775427141766469386240 }, { target := 663, numerator := 71521301070845015060643840 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left14.expected,
    Slot16.Left15.expected,
    Slot16.Left16.expected,
    Slot16.Left17.expected,
    Slot16.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 22574503330670344300134400 }, { target := 27, numerator := 1108929828797844553308569600 }, { target := 29, numerator := 12376447236959871463273267200 }, { target := 37, numerator := 1108931573956773908211302400 }, { target := 44, numerator := 22571013012811634494668800 }, { target := 157, numerator := 77023387591253760092930048 }, { target := 158, numerator := 3783628404304863305119301632 }, { target := 160, numerator := 42227989629340587422619009024 }, { target := 168, numerator := 3783634358723910984278212608 }, { target := 175, numerator := 77011478753158401775108096 }, { target := 267, numerator := 22574452356396486930464768 }, { target := 268, numerator := 1108927324782940936430682112 }, { target := 270, numerator := 12376419290368905674577936384 }, { target := 278, numerator := 1108929069937929641659465728 }, { target := 285, numerator := 22570962046419076472897536 }, { target := 684, numerator := 429127114672167326255677440 }, { target := 687, numerator := 1462882652562850598816317440 }, { target := 689, numerator := 429127806425070090363863040 }, { target := 698, numerator := 71521185778694554375946240 }, { target := 701, numerator := 243813775427141766469386240 }, { target := 703, numerator := 71521301070845015060643840 }, { target := 729, numerator := 486344063295122969756434432 }, { target := 732, numerator := 1657933672904564011991826432 }, { target := 734, numerator := 486344847281746102412378112 }, { target := 743, numerator := 486344063295122969756434432 }, { target := 746, numerator := 1657933672904564011991826432 }, { target := 748, numerator := 486344847281746102412378112 }, { target := 763, numerator := 64369067200825098938351616 }, { target := 766, numerator := 219432397884427589822447616 }, { target := 768, numerator := 64369170963760513554579456 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent1
