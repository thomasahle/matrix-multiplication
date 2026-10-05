import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 8057094582253101089617346560 }, { target := 38, numerator := 27658596912100290978526527488 }, { target := 40, numerator := 8057094582253101089617346560 }, { target := 61, numerator := 197528770403624413809973657600 }, { target := 64, numerator := 678081730748265198183230996480 }, { target := 66, numerator := 197528770403624413809973657600 }, { target := 71, numerator := 121627608859788612008838955008 }, { target := 73, numerator := 121627608859788612008838955008 }, { target := 75, numerator := 8057094582253101089617346560 }, { target := 78, numerator := 27658596912100290978526527488 }, { target := 80, numerator := 8057094582253101089617346560 }, { target := 85, numerator := 119093700341876349258654810112 }, { target := 87, numerator := 119093700341876349258654810112 }, { target := 89, numerator := 6615242084931250843992195072 }, { target := 106, numerator := 165560298351458883680201605120 }, { target := 109, numerator := 568339555903480172687787032576 }, { target := 111, numerator := 165560298351458883680201605120 }, { target := 116, numerator := 93754615162753721756813361152 }, { target := 118, numerator := 93754615162753721756813361152 }, { target := 130, numerator := 2946935606331961578464160514048 }, { target := 132, numerator := 2946935606331961578464160514048 }, { target := 134, numerator := 176406455598166689173125201920 }, { target := 135, numerator := 93754615162753721756813361152 }, { target := 137, numerator := 93754615162753721756813361152 }, { target := 139, numerator := 168688673165746896521800974336 }, { target := 150, numerator := 93754615162753721756813361152 }, { target := 152, numerator := 93754615162753721756813361152 }, { target := 154, numerator := 5512701737442709036660162560 }, { target := 155, numerator := 96288523680665984506997506048 }, { target := 157, numerator := 96288523680665984506997506048 }, { target := 159, numerator := 173098834555701063751129104384 }, { target := 160, numerator := 5512701737442709036660162560 }, { target := 187, numerator := 96288523680665984506997506048 }, { target := 189, numerator := 96288523680665984506997506048 }, { target := 201, numerator := 1629303177017584948368405168128 }, { target := 203, numerator := 1629303177017584948368405168128 }, { target := 205, numerator := 168688673165746896521800974336 }, { target := 206, numerator := 88686798126929196256445071360 }, { target := 208, numerator := 88686798126929196256445071360 }, { target := 210, numerator := 95921010231503137237886828544 }, { target := 221, numerator := 2946935606331961578464160514048 }, { target := 223, numerator := 2946935606331961578464160514048 }, { target := 225, numerator := 173098834555701063751129104384 }, { target := 226, numerator := 1629303177017584948368405168128 }, { target := 228, numerator := 1629303177017584948368405168128 }, { target := 230, numerator := 2702326391694415969770811686912 }, { target := 231, numerator := 105843873358900013503875121152 }, { target := 232, numerator := 121627608859788612008838955008 }, { target := 234, numerator := 121627608859788612008838955008 }, { target := 236, numerator := 176406455598166689173125201920 }, { target := 237, numerator := 168688673165746896521800974336 }, { target := 248, numerator := 93754615162753721756813361152 }, { target := 250, numerator := 93754615162753721756813361152 }, { target := 252, numerator := 5512701737442709036660162560 }, { target := 253, numerator := 88686798126929196256445071360 }, { target := 255, numerator := 88686798126929196256445071360 }, { target := 257, numerator := 105843873358900013503875121152 }, { target := 258, numerator := 5512701737442709036660162560 }, { target := 259, numerator := 119093700341876349258654810112 }, { target := 261, numerator := 119093700341876349258654810112 }, { target := 263, numerator := 169791213513235438329133006848 }, { target := 264, numerator := 95921010231503137237886828544 }, { target := 265, numerator := 6615242084931250843992195072 }]

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
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 124160459567608711958495232 }, { target := 1, numerator := 19821868859322295084356993024 }, { target := 3, numerator := 197792443072112653796936515584 }, { target := 11, numerator := 19821868859322295084356993024 }, { target := 18, numerator := 124146292468160103022854144 }, { target := 19, numerator := 3598015064899858669869465600 }, { target := 21, numerator := 135186669026859570586399539200 }, { target := 24, numerator := 135176444573080265685362278400 }, { target := 31, numerator := 3608239518679163570906726400 }, { target := 35, numerator := 2132114731525505212953730744320 }, { target := 38, numerator := 7227293117684803515586833285120 }, { target := 40, numerator := 2132114731525505212953730744320 }, { target := 45, numerator := 3573443254700542561880113152 }, { target := 47, numerator := 134263442994481017421419249664 }, { target := 50, numerator := 134253288366239717529462243328 }, { target := 57, numerator := 3583597882941842453837119488 }, { target := 71, numerator := 276217274379243070303888211968 }, { target := 73, numerator := 276217274379243070303888211968 }, { target := 89, numerator := 1535137451518298526777868288 }, { target := 90, numerator := 3598015064899858669869465600 }, { target := 92, numerator := 135186669026859570586399539200 }, { target := 95, numerator := 135176444573080265685362278400 }, { target := 102, numerator := 3608239518679163570906726400 }, { target := 106, numerator := 7289844723857135025699132801024 }, { target := 109, numerator := 24710604838805926949679827779584 }, { target := 111, numerator := 7289844723857135025699132801024 }, { target := 116, numerator := 9666915935846944097404928917504 }, { target := 118, numerator := 9666915935846944097404928917504 }, { target := 120, numerator := 162701329306143267164530933760 }, { target := 123, numerator := 558525215063702650082503426048 }, { target := 125, numerator := 162701329306143267164530933760 }, { target := 134, numerator := 160956393068224694059670700032 }, { target := 140, numerator := 2140171137431311743188035698688 }, { target := 143, numerator := 7254949380169741412734846631936 }, { target := 145, numerator := 2140171137431311743188035698688 }, { target := 150, numerator := 9666920677102892898528723468288 }, { target := 152, numerator := 9666920677102892898528723468288 }, { target := 154, numerator := 1734949041549858237648470016000 }, { target := 161, numerator := 3608545840699565573293473792 }, { target := 163, numerator := 135582337326450379085676806144 }, { target := 166, numerator := 135572082947440500609319436288 }, { target := 173, numerator := 3618800219709444049650843648 }, { target := 177, numerator := 162961235582990141393228267520 }, { target := 180, numerator := 559417427867318788501165572096 }, { target := 182, numerator := 162961235582990141393228267520 }, { target := 191, numerator := 146067327587943316527901573120 }, { target := 194, numerator := 501423595632269791288126078976 }, { target := 196, numerator := 146067327587943316527901573120 }, { target := 211, numerator := 197528770403624413809973657600 }, { target := 214, numerator := 678081730748265198183230996480 }, { target := 216, numerator := 197528770403624413809973657600 }, { target := 232, numerator := 276214903751268669741990936576 }, { target := 234, numerator := 276214903751268669741990936576 }, { target := 236, numerator := 160956515849753248670446256128 }, { target := 238, numerator := 8057094582253101089617346560 }, { target := 241, numerator := 27658596912100290978526527488 }, { target := 243, numerator := 8057094582253101089617346560 }, { target := 265, numerator := 1535137451518298526777868288 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1939253963289868415939903488 }, { target := 1, numerator := 218112464926979902015595872256 }, { target := 3, numerator := 2332882122714817237430545940480 }, { target := 11, numerator := 218112592430874939496016642048 }, { target := 18, numerator := 1939253963289868415939903488 }, { target := 19, numerator := 320886273170982578717441654784 }, { target := 21, numerator := 11286419081207704077861862244352 }, { target := 24, numerator := 11286424415256805776985260294144 }, { target := 31, numerator := 320883305027488797286295666688 }, { target := 35, numerator := 2132114731525505212953730744320 }, { target := 38, numerator := 7289844723857135025699132801024 }, { target := 40, numerator := 2132114042849058642098418352128 }, { target := 71, numerator := 50688210272807703747986718720 }, { target := 72, numerator := 3318197307936218093174390784 }, { target := 73, numerator := 50666800922273809754010681344 }, { target := 74, numerator := 3350792566363882318058225664 }, { target := 89, numerator := 469233223203859427013689344 }, { target := 90, numerator := 320865826038450208049037574144 }, { target := 92, numerator := 11285678070356706132587783913472 }, { target := 95, numerator := 11285683404133489235992923602944 }, { target := 102, numerator := 320862858167275022336149946368 }, { target := 106, numerator := 7227293117684803515586833285120 }, { target := 109, numerator := 24710604838805926949679827779584 }, { target := 111, numerator := 7227290783257641121756320104448 }, { target := 116, numerator := 1841408543690694443137226506240 }, { target := 117, numerator := 124673197066303801891317874688 }, { target := 118, numerator := 1840632661740826006320838606848 }, { target := 119, numerator := 125897884660275352008128462848 }, { target := 134, numerator := 70787310215453476345679446016 }, { target := 140, numerator := 2132114731525505212953730744320 }, { target := 143, numerator := 7289844723857135025699132801024 }, { target := 145, numerator := 2132114042849058642098418352128 }, { target := 150, numerator := 1715878695887102813490747801600 }, { target := 152, numerator := 1715102813652100788216418795520 }, { target := 154, numerator := 728996714946692490592532824064 }, { target := 232, numerator := 47346565705479863370787061760 }, { target := 234, numerator := 47325156640079557834752131072 }, { target := 236, numerator := 70787310215453476345679446016 }, { target := 265, numerator := 469219056104410818078048256 }]

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
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 121627608859788612008838955008 }, { target := 20, numerator := 119093700341876349258654810112 }, { target := 21, numerator := 93754615162753721756813361152 }, { target := 22, numerator := 2946935606331961578464160514048 }, { target := 23, numerator := 93754615162753721756813361152 }, { target := 24, numerator := 93754615162753721756813361152 }, { target := 25, numerator := 96288523680665984506997506048 }, { target := 26, numerator := 96288523680665984506997506048 }, { target := 27, numerator := 1629303177017584948368405168128 }, { target := 28, numerator := 88686798126929196256445071360 }, { target := 29, numerator := 2946935606331961578464160514048 }, { target := 30, numerator := 1629303177017584948368405168128 }, { target := 31, numerator := 121627608859788612008838955008 }, { target := 32, numerator := 93754615162753721756813361152 }, { target := 33, numerator := 88686798126929196256445071360 }, { target := 34, numerator := 119093700341876349258654810112 }, { target := 35, numerator := 8277836899575103859195904000 }, { target := 36, numerator := 202940517537970288160931840000 }, { target := 37, numerator := 8277836899575103859195904000 }, { target := 38, numerator := 170096196936430359945412608000 }, { target := 39, numerator := 167158899972065000511504384000 }, { target := 40, numerator := 8277836899575103859195904000 }, { target := 41, numerator := 167425926968825487732768768000 }, { target := 42, numerator := 150069172179393818350583808000 }, { target := 43, numerator := 202940517537970288160931840000 }, { target := 44, numerator := 8277836899575103859195904000 }, { target := 106, numerator := 28416366690513997580677939200 }, { target := 107, numerator := 696659312412601231010168832000 }, { target := 108, numerator := 28416366690513997580677939200 }, { target := 109, numerator := 583910502640561821254575718400 }, { target := 110, numerator := 573827275750379435016270643200 }, { target := 111, numerator := 28416366690513997580677939200 }, { target := 112, numerator := 574743932740396015583389286400 }, { target := 113, numerator := 515161228389318278720677478400 }, { target := 114, numerator := 696659312412601231010168832000 }, { target := 115, numerator := 28416366690513997580677939200 }, { target := 140, numerator := 8277836899575103859195904000 }, { target := 141, numerator := 202940517537970288160931840000 }, { target := 142, numerator := 8277836899575103859195904000 }, { target := 143, numerator := 170096196936430359945412608000 }, { target := 144, numerator := 167158899972065000511504384000 }, { target := 145, numerator := 8277836899575103859195904000 }, { target := 146, numerator := 167425926968825487732768768000 }, { target := 147, numerator := 150069172179393818350583808000 }, { target := 148, numerator := 202940517537970288160931840000 }, { target := 149, numerator := 8277836899575103859195904000 }, { target := 150, numerator := 125520984246431675279264972800 }, { target := 151, numerator := 124663767768651166277357797376 }, { target := 152, numerator := 125520984246431675279264972800 }, { target := 153, numerator := 125888362736909036280082333696 }, { target := 232, numerator := 3350508124487794744413388800 }, { target := 233, numerator := 3327626605588853707134468096 }, { target := 234, numerator := 3350508124487794744413388800 }, { target := 235, numerator := 3360314489730198046104354816 }]

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

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot18.Left2.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 6383128327565242042448609280 }, { target := 1, numerator := 170216755401739787798629580800 }, { target := 2, numerator := 162769772352913672082439536640 }, { target := 3, numerator := 5319273606304368368707174400 }, { target := 4, numerator := 167025191237957166777405276160 }, { target := 5, numerator := 5319273606304368368707174400 }, { target := 6, numerator := 162769772352913672082439536640 }, { target := 7, numerator := 92555360749696009615504834560 }, { target := 8, numerator := 167025191237957166777405276160 }, { target := 9, numerator := 2607507921810401374340256890880 }, { target := 10, numerator := 102130053241043872679177748480 }, { target := 11, numerator := 170216755401739787798629580800 }, { target := 12, numerator := 162769772352913672082439536640 }, { target := 13, numerator := 5319273606304368368707174400 }, { target := 14, numerator := 102130053241043872679177748480 }, { target := 15, numerator := 5319273606304368368707174400 }, { target := 16, numerator := 163833627074174545756180971520 }, { target := 17, numerator := 92555360749696009615504834560 }, { target := 18, numerator := 6383128327565242042448609280 }, { target := 90, numerator := 121627608859788612008838955008 }, { target := 91, numerator := 119093700341876349258654810112 }, { target := 92, numerator := 93754615162753721756813361152 }, { target := 93, numerator := 2946935606331961578464160514048 }, { target := 94, numerator := 93754615162753721756813361152 }, { target := 95, numerator := 93754615162753721756813361152 }, { target := 96, numerator := 96288523680665984506997506048 }, { target := 97, numerator := 96288523680665984506997506048 }, { target := 98, numerator := 1629303177017584948368405168128 }, { target := 99, numerator := 88686798126929196256445071360 }, { target := 100, numerator := 2946935606331961578464160514048 }, { target := 101, numerator := 1629303177017584948368405168128 }, { target := 102, numerator := 121627608859788612008838955008 }, { target := 103, numerator := 93754615162753721756813361152 }, { target := 104, numerator := 88686798126929196256445071360 }, { target := 105, numerator := 119093700341876349258654810112 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent1
