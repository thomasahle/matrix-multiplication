import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk2Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent3

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 12221549948730948058087424 }, { target := 30, numerator := 529651730072803603466158080 }, { target := 35, numerator := 529359124787665348314791936 }, { target := 43, numerator := 12215414989099931894022144 }, { target := 71, numerator := 1176635467401744896491520 }, { target := 72, numerator := 38808050108206361295716352 }, { target := 74, numerator := 423707280017914781302259712 }, { target := 82, numerator := 38767487117481858197094400 }, { target := 89, numerator := 1138431388697089542193152 }, { target := 104, numerator := 434635378909100474730807296 }, { target := 105, numerator := 18836021728484404788272824320 }, { target := 110, numerator := 18825615797198244428480774144 }, { target := 118, numerator := 434417201139913709297074176 }, { target := 146, numerator := 17293186244252354394193920 }, { target := 147, numerator := 473840131241696571804352512 }, { target := 149, numerator := 5047068514944596940655951872 }, { target := 157, numerator := 475115198257378353878138880 }, { target := 164, numerator := 16016322347206871951081472 }, { target := 200, numerator := 11667291363033484068126720 }, { target := 202, numerator := 384621331066947373356810240 }, { target := 205, numerator := 384621897963179968152207360 }, { target := 212, numerator := 11667858259266078863523840 }, { target := 226, numerator := 434633621018213498274971648 }, { target := 227, numerator := 18835945545843620918234972160 }, { target := 232, numerator := 18825539656644443501150339072 }, { target := 240, numerator := 434415444131450784829145088 }, { target := 242, numerator := 191619584674734473320857600 }, { target := 243, numerator := 5250452280355987660325519360 }, { target := 245, numerator := 55924753194631684893609820160 }, { target := 253, numerator := 5264580839924274399962726400 }, { target := 260, numerator := 177471114509536393858908160 }, { target := 296, numerator := 571472182562564499113508864 }, { target := 298, numerator := 18839024816107723254176677888 }, { target := 301, numerator := 18839052583086128704081887232 }, { target := 308, numerator := 571499949540969949018718208 }, { target := 624, numerator := 12222029373518305273315328 }, { target := 625, numerator := 529672507156653749840117760 }, { target := 630, numerator := 529379890393247419404910592 }, { target := 638, numerator := 12215894173226184021639168 }, { target := 640, numerator := 17292983075614164642693120 }, { target := 641, numerator := 473834564340789804250693632 }, { target := 643, numerator := 5047009219565333187334766592 }, { target := 651, numerator := 475109616376373325783367680 }, { target := 658, numerator := 16016134179777565993992192 }, { target := 659, numerator := 571482957610446467654221824 }, { target := 661, numerator := 18839380023938720226458206208 }, { target := 664, numerator := 18839407791440669133045235712 }, { target := 671, numerator := 571510725112395374241251328 }, { target := 1017, numerator := 517104817920555519836160 }, { target := 1018, numerator := 14168876187904777572581376 }, { target := 1020, numerator := 150918599302104953080774656 }, { target := 1028, numerator := 14207003533997506811658240 }, { target := 1035, numerator := 478923741069521983635456 }, { target := 1036, numerator := 11669863471237566881071104 }, { target := 1038, numerator := 384706122613701489320787968 }, { target := 1041, numerator := 384706689634908973775716352 }, { target := 1048, numerator := 11670430492445051335999488 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11667291363033484068126720 }, { target := 30, numerator := 571472182562564499113508864 }, { target := 35, numerator := 571482957610446467654221824 }, { target := 43, numerator := 11669863471237566881071104 }, { target := 71, numerator := 517416343165779805470720 }, { target := 72, numerator := 17293186244252354394193920 }, { target := 74, numerator := 191619584674734473320857600 }, { target := 82, numerator := 17292983075614164642693120 }, { target := 89, numerator := 517104817920555519836160 }, { target := 104, numerator := 384621331066947373356810240 }, { target := 105, numerator := 18839024816107723254176677888 }, { target := 110, numerator := 18839380023938720226458206208 }, { target := 118, numerator := 384706122613701489320787968 }, { target := 146, numerator := 38808050108206361295716352 }, { target := 147, numerator := 1394123397090431931225473024 }, { target := 149, numerator := 15439355472772433645972488192 }, { target := 157, numerator := 1391176837001600231146520576 }, { target := 164, numerator := 38799514193482651046772736 }, { target := 200, numerator := 12221549948730948058087424 }, { target := 202, numerator := 434635378909100474730807296 }, { target := 205, numerator := 434633621018213498274971648 }, { target := 212, numerator := 12222029373518305273315328 }, { target := 226, numerator := 384621897963179968152207360 }, { target := 227, numerator := 18839052583086128704081887232 }, { target := 232, numerator := 18839407791440669133045235712 }, { target := 240, numerator := 384706689634908973775716352 }, { target := 242, numerator := 272697761134272073129000960 }, { target := 243, numerator := 10188903192416445985646968832 }, { target := 245, numerator := 112806297926857716697873252352 }, { target := 253, numerator := 10156342027834487023320694784 }, { target := 260, numerator := 272697761134272073129000960 }, { target := 296, numerator := 529651730072803603466158080 }, { target := 298, numerator := 18836021728484404788272824320 }, { target := 301, numerator := 18835945545843620918234972160 }, { target := 308, numerator := 529672507156653749840117760 }, { target := 624, numerator := 11667858259266078863523840 }, { target := 625, numerator := 571499949540969949018718208 }, { target := 630, numerator := 571510725112395374241251328 }, { target := 638, numerator := 11670430492445051335999488 }, { target := 640, numerator := 24551924699276641640120320 }, { target := 641, numerator := 917342272660810426895826944 }, { target := 643, numerator := 10156342027834487023320694784 }, { target := 651, numerator := 914410678145286044729212928 }, { target := 658, numerator := 24551924699276641640120320 }, { target := 659, numerator := 529359124787665348314791936 }, { target := 661, numerator := 18825615797198244428480774144 }, { target := 664, numerator := 18825539656644443501150339072 }, { target := 671, numerator := 529379890393247419404910592 }, { target := 1017, numerator := 659219124235965091020800 }, { target := 1018, numerator := 24630638005577873474191360 }, { target := 1020, numerator := 272697761134272073129000960 }, { target := 1028, numerator := 24551924699276641640120320 }, { target := 1035, numerator := 659219124235965091020800 }, { target := 1036, numerator := 12215414989099931894022144 }, { target := 1038, numerator := 434417201139913709297074176 }, { target := 1041, numerator := 434415444131450784829145088 }, { target := 1048, numerator := 12215894173226184021639168 }]

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
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 242, numerator := 151009518883642708173258752 }, { target := 243, numerator := 5047068514944596940655951872 }, { target := 245, numerator := 55924753194631684893609820160 }, { target := 253, numerator := 5047009219565333187334766592 }, { target := 260, numerator := 150918599302104953080774656 }, { target := 640, numerator := 14215562418205216556974080 }, { target := 641, numerator := 475115198257378353878138880 }, { target := 643, numerator := 5264580839924274399962726400 }, { target := 651, numerator := 475109616376373325783367680 }, { target := 658, numerator := 14207003533997506811658240 }, { target := 1017, numerator := 479212264461124451172352 }, { target := 1018, numerator := 16016322347206871951081472 }, { target := 1020, numerator := 177471114509536393858908160 }, { target := 1028, numerator := 16016134179777565993992192 }, { target := 1035, numerator := 478923741069521983635456 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent3
