import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 22706053367417970454691840 }, { target := 27, numerator := 1115391975831250110313922560 }, { target := 29, numerator := 12448569403502296146294865920 }, { target := 37, numerator := 1115393731159870373772656640 }, { target := 44, numerator := 22702542710177443537223680 }, { target := 131, numerator := 60793007911890371219554304 }, { target := 134, numerator := 207241709113070501498978304 }, { target := 136, numerator := 60793105910218262801547264 }, { target := 227, numerator := 486344063295122969756434432 }, { target := 230, numerator := 1657933672904564011991826432 }, { target := 232, numerator := 486344847281746102412378112 }, { target := 253, numerator := 489920122584057697475231744 }, { target := 256, numerator := 1670124361675921100315295744 }, { target := 258, numerator := 489920912335288353165410304 }, { target := 302, numerator := 67945126489759826657148928 }, { target := 305, numerator := 231623086655784678145916928 }, { target := 307, numerator := 67945236017302764307611648 }, { target := 328, numerator := 436279233250036781693272064 }, { target := 331, numerator := 1487264030105564775463256064 }, { target := 333, numerator := 436279936532154591869927424 }, { target := 342, numerator := 67945126489759826657148928 }, { target := 345, numerator := 231623086655784678145916928 }, { target := 347, numerator := 67945236017302764307611648 }, { target := 443, numerator := 486344063295122969756434432 }, { target := 446, numerator := 1657933672904564011991826432 }, { target := 448, numerator := 486344847281746102412378112 }, { target := 469, numerator := 489920122584057697475231744 }, { target := 472, numerator := 1670124361675921100315295744 }, { target := 474, numerator := 489920912335288353165410304 }, { target := 518, numerator := 436279233250036781693272064 }, { target := 521, numerator := 1487264030105564775463256064 }, { target := 523, numerator := 436279936532154591869927424 }, { target := 544, numerator := 8600422589888020163707535360 }, { target := 547, numerator := 29318606495113797417943695360 }, { target := 549, numerator := 8600436453769113061042421760 }, { target := 558, numerator := 436279233250036781693272064 }, { target := 561, numerator := 1487264030105564775463256064 }, { target := 563, numerator := 436279936532154591869927424 }, { target := 589, numerator := 486344063295122969756434432 }, { target := 592, numerator := 1657933672904564011991826432 }, { target := 594, numerator := 486344847281746102412378112 }, { target := 603, numerator := 486344063295122969756434432 }, { target := 606, numerator := 1657933672904564011991826432 }, { target := 608, numerator := 486344847281746102412378112 }, { target := 658, numerator := 67945126489759826657148928 }, { target := 661, numerator := 231623086655784678145916928 }, { target := 663, numerator := 67945236017302764307611648 }, { target := 684, numerator := 436279233250036781693272064 }, { target := 687, numerator := 1487264030105564775463256064 }, { target := 689, numerator := 436279936532154591869927424 }, { target := 698, numerator := 67945126489759826657148928 }, { target := 701, numerator := 231623086655784678145916928 }, { target := 703, numerator := 67945236017302764307611648 }, { target := 729, numerator := 489920122584057697475231744 }, { target := 732, numerator := 1670124361675921100315295744 }, { target := 734, numerator := 489920912335288353165410304 }, { target := 743, numerator := 489920122584057697475231744 }, { target := 746, numerator := 1670124361675921100315295744 }, { target := 748, numerator := 489920912335288353165410304 }, { target := 763, numerator := 64369067200825098938351616 }, { target := 766, numerator := 219432397884427589822447616 }, { target := 768, numerator := 64369170963760513554579456 }]

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
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 104018673796074189279461376 }, { target := 27, numerator := 3522818891091054088522039296 }, { target := 29, numerator := 38231895869148994738021466112 }, { target := 37, numerator := 3522813468792005631556976640 }, { target := 44, numerator := 103994273450356132936679424 }, { target := 80, numerator := 145133298457670041290670080 }, { target := 82, numerator := 5217836502968285931807703040 }, { target := 85, numerator := 5217703549052573963119493120 }, { target := 92, numerator := 145261253895709585875927040 }, { target := 131, numerator := 104018673796074189279461376 }, { target := 134, numerator := 335717743762760280091656192 }, { target := 136, numerator := 103812686985944564370505728 }, { target := 157, numerator := 412494517817092085722906624 }, { target := 158, numerator := 15141326405617355280896491520 }, { target := 160, numerator := 165485299544282291560482078720 }, { target := 168, numerator := 15141314840633032121989988352 }, { target := 175, numerator := 412403895585438252790710272 }, { target := 176, numerator := 5217836502968285931807703040 }, { target := 178, numerator := 187489788875925916864762347520 }, { target := 181, numerator := 187484892509638703652913807360 }, { target := 188, numerator := 5222548973073856781950648320 }, { target := 227, numerator := 3522818891091054088522039296 }, { target := 230, numerator := 11369812425416190430996856832 }, { target := 232, numerator := 3515842699225131491669311488 }, { target := 267, numerator := 126502202842515379608092672 }, { target := 268, numerator := 4630422301078365326314307584 }, { target := 270, numerator := 50595688480068419504736043008 }, { target := 278, numerator := 4630418643567185200146284544 }, { target := 285, numerator := 126474342716158836798914560 }, { target := 286, numerator := 2547941815818170250108600320 }, { target := 288, numerator := 93739894760524556723510312960 }, { target := 291, numerator := 93739998066165872551421542400 }, { target := 298, numerator := 2547838510176854422197370880 }, { target := 302, numerator := 38231895869148994738021466112 }, { target := 305, numerator := 123392515522034189845873557504 }, { target := 307, numerator := 38156185749149452805169217536 }, { target := 573, numerator := 72697546862881626841415680 }, { target := 575, numerator := 2674574572295155998565335040 }, { target := 578, numerator := 2674577519798373746055577600 }, { target := 585, numerator := 72694599359663879351173120 }, { target := 589, numerator := 3522813468792005631556976640 }, { target := 592, numerator := 11369794925077682715497594880 }, { target := 594, numerator := 3515837287663790446262353920 }, { target := 763, numerator := 103994273450356132936679424 }, { target := 766, numerator := 335638992239475560344977408 }, { target := 768, numerator := 103788334959909860039196672 }]

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
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 60793007911890371219554304 }, { target := 27, numerator := 486344063295122969756434432 }, { target := 28, numerator := 489920122584057697475231744 }, { target := 29, numerator := 67945126489759826657148928 }, { target := 30, numerator := 436279233250036781693272064 }, { target := 31, numerator := 67945126489759826657148928 }, { target := 32, numerator := 486344063295122969756434432 }, { target := 33, numerator := 489920122584057697475231744 }, { target := 34, numerator := 436279233250036781693272064 }, { target := 35, numerator := 8600422589888020163707535360 }, { target := 36, numerator := 436279233250036781693272064 }, { target := 37, numerator := 486344063295122969756434432 }, { target := 38, numerator := 486344063295122969756434432 }, { target := 39, numerator := 67945126489759826657148928 }, { target := 40, numerator := 436279233250036781693272064 }, { target := 41, numerator := 67945126489759826657148928 }, { target := 42, numerator := 489920122584057697475231744 }, { target := 43, numerator := 489920122584057697475231744 }, { target := 44, numerator := 64369067200825098938351616 }, { target := 131, numerator := 22706053367417970454691840 }, { target := 134, numerator := 76776774054331805631250432 }, { target := 136, numerator := 22689515856570815237586944 }, { target := 157, numerator := 207241709113070501498978304 }, { target := 158, numerator := 1657933672904564011991826432 }, { target := 159, numerator := 1670124361675921100315295744 }, { target := 160, numerator := 231623086655784678145916928 }, { target := 161, numerator := 1487264030105564775463256064 }, { target := 162, numerator := 231623086655784678145916928 }, { target := 163, numerator := 1657933672904564011991826432 }, { target := 164, numerator := 1670124361675921100315295744 }, { target := 165, numerator := 1487264030105564775463256064 }, { target := 166, numerator := 29318606495113797417943695360 }, { target := 167, numerator := 1487264030105564775463256064 }, { target := 168, numerator := 1657933672904564011991826432 }, { target := 169, numerator := 1657933672904564011991826432 }, { target := 170, numerator := 231623086655784678145916928 }, { target := 171, numerator := 1487264030105564775463256064 }, { target := 172, numerator := 231623086655784678145916928 }, { target := 173, numerator := 1670124361675921100315295744 }, { target := 174, numerator := 1670124361675921100315295744 }, { target := 175, numerator := 219432397884427589822447616 }, { target := 227, numerator := 1115391975831250110313922560 }, { target := 230, numerator := 3771513980201164849899634688 }, { target := 232, numerator := 1114579601853233834644996096 }, { target := 286, numerator := 2669761733234403713010892800 }, { target := 288, numerator := 93744997749114146929403494400 }, { target := 291, numerator := 93739998066165872551421542400 }, { target := 298, numerator := 2674577519798373746055577600 }, { target := 302, numerator := 12448569403502296146294865920 }, { target := 305, numerator := 42092784022248101714608521216 }, { target := 307, numerator := 12439502730918966699566825472 }, { target := 573, numerator := 72563707032827959034511360 }, { target := 575, numerator := 2547974400778700783385313280 }, { target := 578, numerator := 2547838510176854422197370880 }, { target := 585, numerator := 72694599359663879351173120 }, { target := 589, numerator := 1115393731159870373772656640 }, { target := 592, numerator := 3771519915555349406492393472 }, { target := 594, numerator := 1114581355903394753883930624 }, { target := 763, numerator := 22702542710177443537223680 }, { target := 766, numerator := 76764903345962692445732864 }, { target := 768, numerator := 22686007756248976759717888 }]

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
    Slot22.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 267, numerator := 60793105910218262801547264 }, { target := 268, numerator := 486344847281746102412378112 }, { target := 269, numerator := 489920912335288353165410304 }, { target := 270, numerator := 67945236017302764307611648 }, { target := 271, numerator := 436279936532154591869927424 }, { target := 272, numerator := 67945236017302764307611648 }, { target := 273, numerator := 486344847281746102412378112 }, { target := 274, numerator := 489920912335288353165410304 }, { target := 275, numerator := 436279936532154591869927424 }, { target := 276, numerator := 8600436453769113061042421760 }, { target := 277, numerator := 436279936532154591869927424 }, { target := 278, numerator := 486344847281746102412378112 }, { target := 279, numerator := 486344847281746102412378112 }, { target := 280, numerator := 67945236017302764307611648 }, { target := 281, numerator := 436279936532154591869927424 }, { target := 282, numerator := 67945236017302764307611648 }, { target := 283, numerator := 489920912335288353165410304 }, { target := 284, numerator := 489920912335288353165410304 }, { target := 285, numerator := 64369170963760513554579456 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent3
