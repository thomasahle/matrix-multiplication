import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 91; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent1

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
    Slot0.Left3.expected,
    Slot0.Left11.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left3.expected,
    Slot1.Left11.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
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
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 4426339325163234068130693120 }, { target := 36, numerator := 78788839987905566412726337536 }, { target := 37, numerator := 4426339325163234068130693120 }, { target := 38, numerator := 70083705981751206078735974400 }, { target := 39, numerator := 119658706423579427641799737344 }, { target := 40, numerator := 4426339325163234068130693120 }, { target := 41, numerator := 119658706423579427641799737344 }, { target := 42, numerator := 119658706423579427641799737344 }, { target := 43, numerator := 78788839987905566412726337536 }, { target := 44, numerator := 4426339325163234068130693120 }, { target := 71, numerator := 22228566600960408658546524160 }, { target := 72, numerator := 3255514118652248429936246784 }, { target := 73, numerator := 22228566600960408658546524160 }, { target := 74, numerator := 3255514118652248429936246784 }, { target := 89, numerator := 1196317101105367221985607680 }, { target := 116, numerator := 822742881463766965227286953984 }, { target := 117, numerator := 122318028616358513205143666688 }, { target := 118, numerator := 822742881463766965227286953984 }, { target := 119, numerator := 122318028616358513205143666688 }, { target := 134, numerator := 77888219358948972982028992512 }, { target := 139, numerator := 28163135893742401253955076096 }, { target := 150, numerator := 822734447372568792262063947776 }, { target := 151, numerator := 122308777445078339349041381376 }, { target := 152, numerator := 822734447372568792262063947776 }, { target := 153, numerator := 122308777445078339349041381376 }, { target := 154, numerator := 662585196737930856198316228608 }, { target := 159, numerator := 14855280471424563298789490688 }, { target := 160, numerator := 1083197534374707740536733696 }, { target := 205, numerator := 28163135893742401253955076096 }, { target := 210, numerator := 28163135893742401253955076096 }, { target := 225, numerator := 14855280471424563298789490688 }, { target := 230, numerator := 347551666029370512177929125888 }, { target := 231, numerator := 27853650883921056185230295040 }, { target := 232, numerator := 22237000692158581623769530368 }, { target := 233, numerator := 3264765289932422286038532096 }, { target := 234, numerator := 22237000692158581623769530368 }, { target := 235, numerator := 3264765289932422286038532096 }, { target := 236, numerator := 77888219358948972982028992512 }, { target := 237, numerator := 28163135893742401253955076096 }, { target := 252, numerator := 1083197534374707740536733696 }, { target := 257, numerator := 27853650883921056185230295040 }, { target := 258, numerator := 1083197534374707740536733696 }, { target := 263, numerator := 28163135893742401253955076096 }, { target := 264, numerator := 28163135893742401253955076096 }, { target := 265, numerator := 1351035994183625408121929728 }]

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
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 292892735503064678162979880960 }, { target := 38, numerator := 1047804422941390940216513003520 }, { target := 40, numerator := 292892638133525144429804912640 }, { target := 71, numerator := 16093220510709943573688614912 }, { target := 73, numerator := 16093220510709943573688614912 }, { target := 85, numerator := 19110699356468057993755230208 }, { target := 87, numerator := 19110699356468057993755230208 }, { target := 106, numerator := 1063903973207910418246187089920 }, { target := 107, numerator := 286571994744046708928198737920 }, { target := 108, numerator := 16099550266519478029674086400 }, { target := 109, numerator := 4003360687393458181516809994240 }, { target := 110, numerator := 435224508871576556068856135680 }, { target := 111, numerator := 1063903624874811586081015726080 }, { target := 112, numerator := 435224508871576556068856135680 }, { target := 113, numerator := 435224508871576556068856135680 }, { target := 114, numerator := 286571994744046708928198737920 }, { target := 115, numerator := 16099550266519478029674086400 }, { target := 116, numerator := 14584481087830886363655307264 }, { target := 118, numerator := 14584481087830886363655307264 }, { target := 130, numerator := 150371029146946035266652995584 }, { target := 132, numerator := 150371029146946035266652995584 }, { target := 135, numerator := 18104873074548686520399691776 }, { target := 137, numerator := 18104873074548686520399691776 }, { target := 140, numerator := 297318977458688378497935605760 }, { target := 141, numerator := 78788839987905566412726337536 }, { target := 142, numerator := 4426339325163234068130693120 }, { target := 143, numerator := 1117887780590043314130077614080 }, { target := 144, numerator := 119658706423579427641799737344 }, { target := 145, numerator := 297318880089181214387082362880 }, { target := 146, numerator := 119658706423579427641799737344 }, { target := 147, numerator := 119658706423579427641799737344 }, { target := 148, numerator := 78788839987905566412726337536 }, { target := 149, numerator := 4426339325163234068130693120 }, { target := 150, numerator := 14584481087830886363655307264 }, { target := 152, numerator := 14584481087830886363655307264 }, { target := 155, numerator := 18104873074548686520399691776 }, { target := 157, numerator := 18104873074548686520399691776 }, { target := 187, numerator := 18104873074548686520399691776 }, { target := 189, numerator := 18104873074548686520399691776 }, { target := 201, numerator := 775492063359835405957120131072 }, { target := 203, numerator := 775492063359835405957120131072 }, { target := 206, numerator := 18104873074548686520399691776 }, { target := 208, numerator := 18104873074548686520399691776 }, { target := 221, numerator := 150371029146946035266652995584 }, { target := 223, numerator := 150371029146946035266652995584 }, { target := 226, numerator := 775492063359835405957120131072 }, { target := 228, numerator := 775492063359835405957120131072 }, { target := 232, numerator := 16093220510709943573688614912 }, { target := 234, numerator := 16093220510709943573688614912 }, { target := 248, numerator := 18104873074548686520399691776 }, { target := 250, numerator := 18104873074548686520399691776 }, { target := 253, numerator := 18104873074548686520399691776 }, { target := 255, numerator := 18104873074548686520399691776 }, { target := 259, numerator := 19110699356468057993755230208 }, { target := 261, numerator := 19110699356468057993755230208 }]

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
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 16093220510709943573688614912 }, { target := 20, numerator := 19110699356468057993755230208 }, { target := 21, numerator := 14584481087830886363655307264 }, { target := 22, numerator := 150371029146946035266652995584 }, { target := 23, numerator := 18104873074548686520399691776 }, { target := 24, numerator := 14584481087830886363655307264 }, { target := 25, numerator := 18104873074548686520399691776 }, { target := 26, numerator := 18104873074548686520399691776 }, { target := 27, numerator := 775492063359835405957120131072 }, { target := 28, numerator := 18104873074548686520399691776 }, { target := 29, numerator := 150371029146946035266652995584 }, { target := 30, numerator := 775492063359835405957120131072 }, { target := 31, numerator := 16093220510709943573688614912 }, { target := 32, numerator := 18104873074548686520399691776 }, { target := 33, numerator := 18104873074548686520399691776 }, { target := 34, numerator := 19110699356468057993755230208 }, { target := 35, numerator := 4632215572845244955020492800 }, { target := 38, numerator := 16848366557985500263612416000 }, { target := 40, numerator := 4632215572845244955020492800 }, { target := 61, numerator := 82453437196645360199364771840 }, { target := 64, numerator := 299900924732141904692301004800 }, { target := 66, numerator := 82453437196645360199364771840 }, { target := 75, numerator := 4632215572845244955020492800 }, { target := 78, numerator := 16848366557985500263612416000 }, { target := 80, numerator := 4632215572845244955020492800 }, { target := 90, numerator := 16093220510709943573688614912 }, { target := 91, numerator := 19110699356468057993755230208 }, { target := 92, numerator := 14584481087830886363655307264 }, { target := 93, numerator := 150371029146946035266652995584 }, { target := 94, numerator := 18104873074548686520399691776 }, { target := 95, numerator := 14584481087830886363655307264 }, { target := 96, numerator := 18104873074548686520399691776 }, { target := 97, numerator := 18104873074548686520399691776 }, { target := 98, numerator := 775492063359835405957120131072 }, { target := 99, numerator := 18104873074548686520399691776 }, { target := 100, numerator := 150371029146946035266652995584 }, { target := 101, numerator := 775492063359835405957120131072 }, { target := 102, numerator := 16093220510709943573688614912 }, { target := 103, numerator := 18104873074548686520399691776 }, { target := 104, numerator := 18104873074548686520399691776 }, { target := 105, numerator := 19110699356468057993755230208 }, { target := 106, numerator := 73343413236716378454491136000 }, { target := 109, numerator := 266765803834770420840529920000 }, { target := 111, numerator := 73343413236716378454491136000 }, { target := 120, numerator := 125224227652583121950720655360 }, { target := 123, numerator := 455467509284208023792988979200 }, { target := 125, numerator := 125224227652583121950720655360 }, { target := 140, numerator := 4632215572845244955020492800 }, { target := 143, numerator := 16848366557985500263612416000 }, { target := 145, numerator := 4632215572845244955020492800 }, { target := 177, numerator := 125224227652583121950720655360 }, { target := 180, numerator := 455467509284208023792988979200 }, { target := 182, numerator := 125224227652583121950720655360 }, { target := 191, numerator := 125224227652583121950720655360 }, { target := 194, numerator := 455467509284208023792988979200 }, { target := 196, numerator := 125224227652583121950720655360 }, { target := 211, numerator := 82453437196645360199364771840 }, { target := 214, numerator := 299900924732141904692301004800 }, { target := 216, numerator := 82453437196645360199364771840 }, { target := 238, numerator := 4632215572845244955020492800 }, { target := 241, numerator := 16848366557985500263612416000 }, { target := 243, numerator := 4632215572845244955020492800 }]

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1196317101105367221985607680 }, { target := 1, numerator := 77888219358948972982028992512 }, { target := 2, numerator := 28163135893742401253955076096 }, { target := 3, numerator := 662585196737930856198316228608 }, { target := 4, numerator := 14855280471424563298789490688 }, { target := 5, numerator := 1083197534374707740536733696 }, { target := 6, numerator := 28163135893742401253955076096 }, { target := 7, numerator := 28163135893742401253955076096 }, { target := 8, numerator := 14855280471424563298789490688 }, { target := 9, numerator := 347551666029370512177929125888 }, { target := 10, numerator := 27853650883921056185230295040 }, { target := 11, numerator := 77888219358948972982028992512 }, { target := 12, numerator := 28163135893742401253955076096 }, { target := 13, numerator := 1083197534374707740536733696 }, { target := 14, numerator := 27853650883921056185230295040 }, { target := 15, numerator := 1083197534374707740536733696 }, { target := 16, numerator := 28163135893742401253955076096 }, { target := 17, numerator := 28163135893742401253955076096 }, { target := 18, numerator := 1351035994183625408121929728 }, { target := 19, numerator := 22228566600960408658546524160 }, { target := 21, numerator := 822742881463766965227286953984 }, { target := 24, numerator := 822734447372568792262063947776 }, { target := 31, numerator := 22237000692158581623769530368 }, { target := 45, numerator := 3255514118652248429936246784 }, { target := 47, numerator := 122318028616358513205143666688 }, { target := 50, numerator := 122308777445078339349041381376 }, { target := 57, numerator := 3264765289932422286038532096 }, { target := 90, numerator := 22228566600960408658546524160 }, { target := 92, numerator := 822742881463766965227286953984 }, { target := 95, numerator := 822734447372568792262063947776 }, { target := 102, numerator := 22237000692158581623769530368 }, { target := 161, numerator := 3255514118652248429936246784 }, { target := 163, numerator := 122318028616358513205143666688 }, { target := 166, numerator := 122308777445078339349041381376 }, { target := 173, numerator := 3264765289932422286038532096 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent1
