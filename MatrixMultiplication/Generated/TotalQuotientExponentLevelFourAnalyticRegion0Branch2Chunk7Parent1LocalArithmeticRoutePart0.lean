import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk7Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4375644940024714302062592 }, { target := 57, numerator := 37321677429622563164651520 }, { target := 58, numerator := 38093850066097512747368448 }, { target := 59, numerator := 4633035818849697496301568 }, { target := 60, numerator := 27283433155448218589331456 }, { target := 61, numerator := 4633035818849697496301568 }, { target := 62, numerator := 37321677429622563164651520 }, { target := 63, numerator := 38093850066097512747368448 }, { target := 64, numerator := 27283433155448218589331456 }, { target := 65, numerator := 616451154785834750202347520 }, { target := 66, numerator := 27283433155448218589331456 }, { target := 67, numerator := 37321677429622563164651520 }, { target := 68, numerator := 37321677429622563164651520 }, { target := 69, numerator := 4633035818849697496301568 }, { target := 70, numerator := 27283433155448218589331456 }, { target := 71, numerator := 4633035818849697496301568 }, { target := 72, numerator := 38093850066097512747368448 }, { target := 73, numerator := 38093850066097512747368448 }, { target := 74, numerator := 4118254061199731107823616 }, { target := 110, numerator := 2123789478455095628660736 }, { target := 112, numerator := 101866623392850763050909696 }, { target := 115, numerator := 101924642904873357100974080 }, { target := 122, numerator := 2166578558505961270542336 }, { target := 152, numerator := 160046557186104481294581760 }, { target := 153, numerator := 1365102987763832340453785600 }, { target := 154, numerator := 1393346497855497837152829440 }, { target := 155, numerator := 169461060549992980194263040 }, { target := 156, numerator := 997937356572180883366215680 }, { target := 157, numerator := 169461060549992980194263040 }, { target := 158, numerator := 1365102987763832340453785600 }, { target := 159, numerator := 1393346497855497837152829440 }, { target := 160, numerator := 997937356572180883366215680 }, { target := 161, numerator := 22547735556512954864736665600 }, { target := 162, numerator := 997937356572180883366215680 }, { target := 163, numerator := 1365102987763832340453785600 }, { target := 164, numerator := 1365102987763832340453785600 }, { target := 165, numerator := 169461060549992980194263040 }, { target := 166, numerator := 997937356572180883366215680 }, { target := 167, numerator := 169461060549992980194263040 }, { target := 168, numerator := 1393346497855497837152829440 }, { target := 169, numerator := 1393346497855497837152829440 }, { target := 170, numerator := 150632053822215982394900480 }, { target := 206, numerator := 57829558907591591272120320 }, { target := 208, numerator := 2773769226175618410369515520 }, { target := 211, numerator := 2775349063924292548925849600 }, { target := 218, numerator := 58994680804326473277112320 }, { target := 302, numerator := 688737461848639585671708672 }, { target := 304, numerator := 33034987862224078029132398592 }, { target := 307, numerator := 33053803386009988410543964160 }, { target := 314, numerator := 702613810087500384275791872 }, { target := 679, numerator := 57829896300105700290330624 }, { target := 681, numerator := 2773785409058394207644811264 }, { target := 684, numerator := 2775365256024247933568286720 }, { target := 691, numerator := 58995024994461269857665024 }, { target := 966, numerator := 2123162892357464594841600 }, { target := 968, numerator := 101836569467695710968217600 }, { target := 971, numerator := 101894571862099071336448000 }, { target := 978, numerator := 2165939348255624763801600 }]

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
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 4375644940024714302062592 }, { target := 112, numerator := 160046557186104481294581760 }, { target := 115, numerator := 160046694383763529509371904 }, { target := 122, numerator := 4358926425286410414063616 }, { target := 206, numerator := 37321677429622563164651520 }, { target := 208, numerator := 1365102987763832340453785600 }, { target := 211, numerator := 1365104157979159516403466240 }, { target := 218, numerator := 37179078333325265296424960 }, { target := 241, numerator := 38093850066097512747368448 }, { target := 243, numerator := 1393346497855497837152829440 }, { target := 246, numerator := 1393347692282176609846296576 }, { target := 253, numerator := 37948300643669925957730304 }, { target := 283, numerator := 160046694383763529509371904 }, { target := 284, numerator := 1365104157979159516403466240 }, { target := 285, numerator := 1393347692282176609846296576 }, { target := 286, numerator := 169461205818102560656982016 }, { target := 287, numerator := 997938212039937301646671872 }, { target := 288, numerator := 169461205818102560656982016 }, { target := 289, numerator := 1365104157979159516403466240 }, { target := 290, numerator := 1393347692282176609846296576 }, { target := 291, numerator := 997938212039937301646671872 }, { target := 292, numerator := 22547754885241979598526218240 }, { target := 293, numerator := 997938212039937301646671872 }, { target := 294, numerator := 1365104157979159516403466240 }, { target := 295, numerator := 1365104157979159516403466240 }, { target := 296, numerator := 169461205818102560656982016 }, { target := 297, numerator := 997938212039937301646671872 }, { target := 298, numerator := 169461205818102560656982016 }, { target := 299, numerator := 1393347692282176609846296576 }, { target := 300, numerator := 1393347692282176609846296576 }, { target := 301, numerator := 150632182949424498361761792 }, { target := 302, numerator := 4633035818849697496301568 }, { target := 304, numerator := 169461060549992980194263040 }, { target := 307, numerator := 169461205818102560656982016 }, { target := 314, numerator := 4615333862067963967832064 }, { target := 337, numerator := 27283433155448218589331456 }, { target := 339, numerator := 997937356572180883366215680 }, { target := 342, numerator := 997938212039937301646671872 }, { target := 349, numerator := 27179188298844676699455488 }, { target := 363, numerator := 4633035818849697496301568 }, { target := 365, numerator := 169461060549992980194263040 }, { target := 368, numerator := 169461205818102560656982016 }, { target := 375, numerator := 4615333862067963967832064 }, { target := 660, numerator := 4358926425286410414063616 }, { target := 661, numerator := 37179078333325265296424960 }, { target := 662, numerator := 37948300643669925957730304 }, { target := 663, numerator := 4615333862067963967832064 }, { target := 664, numerator := 27179188298844676699455488 }, { target := 665, numerator := 4615333862067963967832064 }, { target := 666, numerator := 37179078333325265296424960 }, { target := 667, numerator := 37948300643669925957730304 }, { target := 668, numerator := 27179188298844676699455488 }, { target := 669, numerator := 614095811091820761275432960 }, { target := 670, numerator := 27179188298844676699455488 }, { target := 671, numerator := 37179078333325265296424960 }, { target := 672, numerator := 37179078333325265296424960 }, { target := 673, numerator := 4615333862067963967832064 }, { target := 674, numerator := 27179188298844676699455488 }, { target := 675, numerator := 4615333862067963967832064 }, { target := 676, numerator := 37948300643669925957730304 }, { target := 677, numerator := 37948300643669925957730304 }, { target := 678, numerator := 4102518988504856860295168 }]

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
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot11.Left16.expected,
    Slot11.Left17.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2123789478455095628660736 }, { target := 57, numerator := 57829558907591591272120320 }, { target := 59, numerator := 688737461848639585671708672 }, { target := 67, numerator := 57829896300105700290330624 }, { target := 74, numerator := 2123162892357464594841600 }, { target := 152, numerator := 101866623392850763050909696 }, { target := 153, numerator := 2773769226175618410369515520 }, { target := 155, numerator := 33034987862224078029132398592 }, { target := 163, numerator := 2773785409058394207644811264 }, { target := 170, numerator := 101836569467695710968217600 }, { target := 473, numerator := 37321677429622563164651520 }, { target := 475, numerator := 1365102987763832340453785600 }, { target := 478, numerator := 1365104157979159516403466240 }, { target := 485, numerator := 37179078333325265296424960 }, { target := 508, numerator := 38093850066097512747368448 }, { target := 510, numerator := 1393346497855497837152829440 }, { target := 513, numerator := 1393347692282176609846296576 }, { target := 520, numerator := 37948300643669925957730304 }, { target := 569, numerator := 27283433155448218589331456 }, { target := 571, numerator := 997937356572180883366215680 }, { target := 574, numerator := 997938212039937301646671872 }, { target := 581, numerator := 27179188298844676699455488 }, { target := 604, numerator := 616451154785834750202347520 }, { target := 606, numerator := 22547735556512954864736665600 }, { target := 609, numerator := 22547754885241979598526218240 }, { target := 616, numerator := 614095811091820761275432960 }, { target := 630, numerator := 27283433155448218589331456 }, { target := 632, numerator := 997937356572180883366215680 }, { target := 635, numerator := 997938212039937301646671872 }, { target := 642, numerator := 27179188298844676699455488 }, { target := 679, numerator := 37321677429622563164651520 }, { target := 681, numerator := 1365102987763832340453785600 }, { target := 684, numerator := 1365104157979159516403466240 }, { target := 691, numerator := 37179078333325265296424960 }, { target := 705, numerator := 37321677429622563164651520 }, { target := 707, numerator := 1365102987763832340453785600 }, { target := 710, numerator := 1365104157979159516403466240 }, { target := 717, numerator := 37179078333325265296424960 }, { target := 785, numerator := 4633035818849697496301568 }, { target := 787, numerator := 169461060549992980194263040 }, { target := 790, numerator := 169461205818102560656982016 }, { target := 797, numerator := 4615333862067963967832064 }, { target := 820, numerator := 27283433155448218589331456 }, { target := 822, numerator := 997937356572180883366215680 }, { target := 825, numerator := 997938212039937301646671872 }, { target := 832, numerator := 27179188298844676699455488 }, { target := 846, numerator := 4633035818849697496301568 }, { target := 848, numerator := 169461060549992980194263040 }, { target := 851, numerator := 169461205818102560656982016 }, { target := 858, numerator := 4615333862067963967832064 }, { target := 895, numerator := 38093850066097512747368448 }, { target := 897, numerator := 1393346497855497837152829440 }, { target := 900, numerator := 1393347692282176609846296576 }, { target := 907, numerator := 37948300643669925957730304 }, { target := 921, numerator := 38093850066097512747368448 }, { target := 923, numerator := 1393346497855497837152829440 }, { target := 926, numerator := 1393347692282176609846296576 }, { target := 933, numerator := 37948300643669925957730304 }, { target := 966, numerator := 4118254061199731107823616 }, { target := 968, numerator := 150632053822215982394900480 }, { target := 971, numerator := 150632182949424498361761792 }, { target := 978, numerator := 4102518988504856860295168 }]

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
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 283, numerator := 101924642904873357100974080 }, { target := 284, numerator := 2775349063924292548925849600 }, { target := 286, numerator := 33053803386009988410543964160 }, { target := 294, numerator := 2775365256024247933568286720 }, { target := 301, numerator := 101894571862099071336448000 }, { target := 660, numerator := 2166578558505961270542336 }, { target := 661, numerator := 58994680804326473277112320 }, { target := 663, numerator := 702613810087500384275791872 }, { target := 671, numerator := 58995024994461269857665024 }, { target := 678, numerator := 2165939348255624763801600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7.Parent1
