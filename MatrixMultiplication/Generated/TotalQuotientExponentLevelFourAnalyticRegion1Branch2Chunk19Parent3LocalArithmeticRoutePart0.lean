import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot1.Left5.expected,
    Slot1.Left12.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 3489099940657586607487077842944 }, { target := 17, numerator := 30987186608362175006068703232 }, { target := 18, numerator := 1740853180245066011576893440 }, { target := 19, numerator := 12503360390325396885945238683648 }, { target := 20, numerator := 47061064305958284512962019328 }, { target := 21, numerator := 3489098781316615062989177880576 }, { target := 22, numerator := 47061064305958284512962019328 }, { target := 23, numerator := 47061064305958284512962019328 }, { target := 24, numerator := 30987186608362175006068703232 }, { target := 25, numerator := 1740853180245066011576893440 }, { target := 26, numerator := 12154955327610905480903606140928 }, { target := 27, numerator := 3862089568037628308849950720 }, { target := 28, numerator := 12154955327610905480903606140928 }, { target := 29, numerator := 3862089568037628308849950720 }, { target := 44, numerator := 949615675054151597067847335936 }, { target := 50, numerator := 3489099940657586607487077842944 }, { target := 51, numerator := 30987186608362175006068703232 }, { target := 52, numerator := 1740853180245066011576893440 }, { target := 53, numerator := 12503360390325396885945238683648 }, { target := 54, numerator := 47061064305958284512962019328 }, { target := 55, numerator := 3489098781316615062989177880576 }, { target := 56, numerator := 47061064305958284512962019328 }, { target := 57, numerator := 47061064305958284512962019328 }, { target := 58, numerator := 30987186608362175006068703232 }, { target := 59, numerator := 1740853180245066011576893440 }, { target := 60, numerator := 41705833877742068135589371183104 }, { target := 61, numerator := 13204745900554271639421845504 }, { target := 62, numerator := 41705833877742068135589371183104 }, { target := 63, numerator := 13204745900554271639421845504 }, { target := 64, numerator := 35534953139152743450410915725312 }, { target := 71, numerator := 12154955326497183307453391962112 }, { target := 72, numerator := 3862088320576560324241522688 }, { target := 73, numerator := 12154955326497183307453391962112 }, { target := 74, numerator := 3862088320576560324241522688 }, { target := 75, numerator := 35532549756844417704654438137856 }, { target := 104, numerator := 952019104586142171520777060352 }]

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
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 490924752511613540552472002560 }, { target := 1, numerator := 16170591763165279840869810176 }, { target := 2, numerator := 17638668437196552917211611660288 }, { target := 3, numerator := 127237024662800491379475611648 }, { target := 4, numerator := 15319507986156580901876662272 }, { target := 5, numerator := 17638664120953587574355886342144 }, { target := 6, numerator := 15319507986156580901876662272 }, { target := 7, numerator := 15319507986156580901876662272 }, { target := 8, numerator := 656185592073706881963717033984 }, { target := 9, numerator := 15319507986156580901876662272 }, { target := 10, numerator := 127237024662800491379475611648 }, { target := 11, numerator := 656185592073706881963717033984 }, { target := 12, numerator := 490929068754578883408197320704 }, { target := 13, numerator := 15319507986156580901876662272 }, { target := 14, numerator := 15319507986156580901876662272 }, { target := 15, numerator := 16170591763165279840869810176 }, { target := 16, numerator := 35541197918111015316146188451840 }, { target := 19, numerator := 126908814521798161082172183674880 }, { target := 21, numerator := 35541197918111015316146188451840 }, { target := 26, numerator := 27351504004177532717395045515264 }, { target := 28, numerator := 27351492607935371803999434964992 }, { target := 44, numerator := 501369116014446677478699171840 }, { target := 49, numerator := 16170591763165279840869810176 }, { target := 50, numerator := 35541186481658649777357826555904 }, { target := 53, numerator := 126908772924955668023352450088960 }, { target := 55, numerator := 35541186481658649777357826555904 }, { target := 60, numerator := 99276959107189546494913106935808 }, { target := 62, numerator := 99276917656600235363050840915968 }, { target := 64, numerator := 18024364886265041468253104242688 }, { target := 69, numerator := 127237024662800491379475611648 }, { target := 70, numerator := 15319507986156580901876662272 }, { target := 71, numerator := 27351502856642477380071258587136 }, { target := 73, numerator := 27351491460400316466675648036864 }, { target := 75, numerator := 18024360475574746468004474650624 }, { target := 76, numerator := 15319507986156580901876662272 }, { target := 91, numerator := 15319507986156580901876662272 }, { target := 96, numerator := 656185592073706881963717033984 }, { target := 97, numerator := 15319507986156580901876662272 }, { target := 102, numerator := 127237024662800491379475611648 }, { target := 103, numerator := 656185592073706881963717033984 }, { target := 104, numerator := 501373526704741677727328763904 }, { target := 109, numerator := 15319507986156580901876662272 }, { target := 110, numerator := 15319507986156580901876662272 }, { target := 111, numerator := 16170591763165279840869810176 }]

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
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left2.expected,
    Slot21.Left3.expected,
    Slot22.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 968028219749792206713209749504 }, { target := 2, numerator := 36229594057085481879107448864768 }, { target := 5, numerator := 36227132277993228967318258712576 }, { target := 12, numerator := 970490046065709947198852038656 }, { target := 16, numerator := 459143050044622132854046851072 }, { target := 19, numerator := 1556472096434636081666241593344 }, { target := 21, numerator := 459143048930899959403832672256 }, { target := 26, numerator := 2030995376952577013506375680 }, { target := 28, numerator := 2030995376952577013506375680 }, { target := 30, numerator := 3862089568037628308849950720 }, { target := 33, numerator := 13204745900554271639421845504 }, { target := 35, numerator := 3862088320576560324241522688 }, { target := 40, numerator := 36151717709755870840413487104 }, { target := 42, numerator := 36151717709755870840413487104 }, { target := 45, numerator := 2030995376952577013506375680 }, { target := 47, numerator := 2030995376952577013506375680 }, { target := 50, numerator := 459143050044622132854046851072 }, { target := 53, numerator := 1556472096434636081666241593344 }, { target := 55, numerator := 459143048930899959403832672256 }, { target := 60, numerator := 32157426801749136047184281600 }, { target := 62, numerator := 32157426801749136047184281600 }, { target := 65, numerator := 54904575023617998598455689216 }, { target := 67, numerator := 54904575023617998598455689216 }, { target := 71, numerator := 2030995376952577013506375680 }, { target := 73, numerator := 2030995376952577013506375680 }, { target := 77, numerator := 3862089568037628308849950720 }, { target := 80, numerator := 13204745900554271639421845504 }, { target := 82, numerator := 3862088320576560324241522688 }, { target := 87, numerator := 54904575023617998598455689216 }, { target := 89, numerator := 54904575023617998598455689216 }, { target := 92, numerator := 54904575023617998598455689216 }, { target := 94, numerator := 54904575023617998598455689216 }, { target := 98, numerator := 36151717709755870840413487104 }, { target := 100, numerator := 36151717709755870840413487104 }, { target := 105, numerator := 2030995376952577013506375680 }, { target := 107, numerator := 2030995376952577013506375680 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent3
