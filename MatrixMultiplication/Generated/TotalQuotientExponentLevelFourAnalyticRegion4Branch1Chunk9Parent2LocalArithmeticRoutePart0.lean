import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk9Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 75; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 5081748256756663911972864 }, { target := 57, numerator := 37830792578077386900242432 }, { target := 58, numerator := 38395431273272571779350528 }, { target := 59, numerator := 5646386951951848791080960 }, { target := 60, numerator := 33878321711711092746485760 }, { target := 61, numerator := 5646386951951848791080960 }, { target := 62, numerator := 37548473230479794460688384 }, { target := 63, numerator := 38395431273272571779350528 }, { target := 64, numerator := 33878321711711092746485760 }, { target := 65, numerator := 684059779228966481039458304 }, { target := 66, numerator := 33878321711711092746485760 }, { target := 67, numerator := 37548473230479794460688384 }, { target := 68, numerator := 37548473230479794460688384 }, { target := 69, numerator := 5646386951951848791080960 }, { target := 70, numerator := 33878321711711092746485760 }, { target := 71, numerator := 5646386951951848791080960 }, { target := 72, numerator := 38395431273272571779350528 }, { target := 73, numerator := 38395431273272571779350528 }, { target := 74, numerator := 5081748256756663911972864 }, { target := 152, numerator := 169003590520337020168962048 }, { target := 153, numerator := 1258137840540286705702273024 }, { target := 154, numerator := 1276916017264768596832157696 }, { target := 155, numerator := 187781767244818911298846720 }, { target := 156, numerator := 1126690603468913467793080320 }, { target := 157, numerator := 187781767244818911298846720 }, { target := 158, numerator := 1248748752178045760137330688 }, { target := 159, numerator := 1276916017264768596832157696 }, { target := 160, numerator := 1126690603468913467793080320 }, { target := 161, numerator := 22749761101709811103855280128 }, { target := 162, numerator := 1126690603468913467793080320 }, { target := 163, numerator := 1248748752178045760137330688 }, { target := 164, numerator := 1248748752178045760137330688 }, { target := 165, numerator := 187781767244818911298846720 }, { target := 166, numerator := 1126690603468913467793080320 }, { target := 167, numerator := 187781767244818911298846720 }, { target := 168, numerator := 1276916017264768596832157696 }, { target := 169, numerator := 1276916017264768596832157696 }, { target := 170, numerator := 169003590520337020168962048 }, { target := 283, numerator := 169003590520337020168962048 }, { target := 284, numerator := 1258137840540286705702273024 }, { target := 285, numerator := 1276916017264768596832157696 }, { target := 286, numerator := 187781767244818911298846720 }, { target := 287, numerator := 1126690603468913467793080320 }, { target := 288, numerator := 187781767244818911298846720 }, { target := 289, numerator := 1248748752178045760137330688 }, { target := 290, numerator := 1276916017264768596832157696 }, { target := 291, numerator := 1126690603468913467793080320 }, { target := 292, numerator := 22749761101709811103855280128 }, { target := 293, numerator := 1126690603468913467793080320 }, { target := 294, numerator := 1248748752178045760137330688 }, { target := 295, numerator := 1248748752178045760137330688 }, { target := 296, numerator := 187781767244818911298846720 }, { target := 297, numerator := 1126690603468913467793080320 }, { target := 298, numerator := 187781767244818911298846720 }, { target := 299, numerator := 1276916017264768596832157696 }, { target := 300, numerator := 1276916017264768596832157696 }, { target := 301, numerator := 169003590520337020168962048 }]

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
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4332917913384264337981440 }, { target := 57, numerator := 147260358462277957372084224 }, { target := 59, numerator := 1621468854962427026938527744 }, { target := 67, numerator := 147262652832367120339697664 }, { target := 74, numerator := 4332344320861973596078080 }, { target := 110, numerator := 9414666170140928249954304 }, { target := 112, numerator := 343034305826601070491598848 }, { target := 115, numerator := 343068134654608560711794688 }, { target := 122, numerator := 9381093513635642304626688 }, { target := 152, numerator := 174030715306264050322636800 }, { target := 153, numerator := 5914680599021605895830241280 }, { target := 155, numerator := 65125947529325952756277575680 }, { target := 163, numerator := 5914772751902361132287918080 }, { target := 170, numerator := 174007677086075241208217600 }, { target := 206, numerator := 147260358462277957372084224 }, { target := 208, numerator := 5914680599021605895830241280 }, { target := 211, numerator := 5915830319703678730050207744 }, { target := 218, numerator := 146120754744095141806473216 }, { target := 283, numerator := 174064544134271540542832640 }, { target := 284, numerator := 5915830319703678730050207744 }, { target := 286, numerator := 65138606987019482680067620864 }, { target := 294, numerator := 5915922490497501484374032384 }, { target := 301, numerator := 174041501435815851961876480 }, { target := 302, numerator := 1621468854962427026938527744 }, { target := 304, numerator := 65125947529325952756277575680 }, { target := 307, numerator := 65138606987019482680067620864 }, { target := 314, numerator := 1608920794131065185444560896 }, { target := 660, numerator := 9381093513635642304626688 }, { target := 661, numerator := 183951238339209294071726080 }, { target := 662, numerator := 38395117678623318716973056 }, { target := 663, numerator := 1614567134966156849961762816 }, { target := 664, numerator := 33878045010549987103211520 }, { target := 665, numerator := 5646340835091664517201920 }, { target := 666, numerator := 37548166553359569039392768 }, { target := 667, numerator := 38395117678623318716973056 }, { target := 668, numerator := 33878045010549987103211520 }, { target := 669, numerator := 684054192171355156259012608 }, { target := 670, numerator := 33878045010549987103211520 }, { target := 671, numerator := 183671197912102342905298944 }, { target := 672, numerator := 37548166553359569039392768 }, { target := 673, numerator := 5646340835091664517201920 }, { target := 674, numerator := 33878045010549987103211520 }, { target := 675, numerator := 5646340835091664517201920 }, { target := 676, numerator := 38395117678623318716973056 }, { target := 677, numerator := 38395117678623318716973056 }, { target := 678, numerator := 9380524359973734289768448 }, { target := 679, numerator := 147262652832367120339697664 }, { target := 681, numerator := 5914772751902361132287918080 }, { target := 684, numerator := 5915922490497501484374032384 }, { target := 691, numerator := 146123031358742773865906176 }, { target := 966, numerator := 4332344320861973596078080 }, { target := 968, numerator := 174007677086075241208217600 }, { target := 971, numerator := 174041501435815851961876480 }, { target := 978, numerator := 4298817608391236224286720 }]

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
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot13.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 37830792578077386900242432 }, { target := 208, numerator := 1258137840540286705702273024 }, { target := 211, numerator := 1258137840540286705702273024 }, { target := 218, numerator := 37830483595114152265252864 }, { target := 241, numerator := 38395431273272571779350528 }, { target := 243, numerator := 1276916017264768596832157696 }, { target := 246, numerator := 1276916017264768596832157696 }, { target := 253, numerator := 38395117678623318716973056 }, { target := 302, numerator := 5646386951951848791080960 }, { target := 304, numerator := 187781767244818911298846720 }, { target := 307, numerator := 187781767244818911298846720 }, { target := 314, numerator := 5646340835091664517201920 }, { target := 337, numerator := 33878321711711092746485760 }, { target := 339, numerator := 1126690603468913467793080320 }, { target := 342, numerator := 1126690603468913467793080320 }, { target := 349, numerator := 33878045010549987103211520 }, { target := 363, numerator := 5646386951951848791080960 }, { target := 365, numerator := 187781767244818911298846720 }, { target := 368, numerator := 187781767244818911298846720 }, { target := 375, numerator := 5646340835091664517201920 }, { target := 473, numerator := 37548473230479794460688384 }, { target := 475, numerator := 1248748752178045760137330688 }, { target := 478, numerator := 1248748752178045760137330688 }, { target := 485, numerator := 37548166553359569039392768 }, { target := 508, numerator := 38395431273272571779350528 }, { target := 510, numerator := 1276916017264768596832157696 }, { target := 513, numerator := 1276916017264768596832157696 }, { target := 520, numerator := 38395117678623318716973056 }, { target := 569, numerator := 33878321711711092746485760 }, { target := 571, numerator := 1126690603468913467793080320 }, { target := 574, numerator := 1126690603468913467793080320 }, { target := 581, numerator := 33878045010549987103211520 }, { target := 604, numerator := 684059779228966481039458304 }, { target := 606, numerator := 22749761101709811103855280128 }, { target := 609, numerator := 22749761101709811103855280128 }, { target := 616, numerator := 684054192171355156259012608 }, { target := 630, numerator := 33878321711711092746485760 }, { target := 632, numerator := 1126690603468913467793080320 }, { target := 635, numerator := 1126690603468913467793080320 }, { target := 642, numerator := 33878045010549987103211520 }, { target := 679, numerator := 37548473230479794460688384 }, { target := 681, numerator := 1248748752178045760137330688 }, { target := 684, numerator := 1248748752178045760137330688 }, { target := 691, numerator := 37548166553359569039392768 }, { target := 705, numerator := 37548473230479794460688384 }, { target := 707, numerator := 1248748752178045760137330688 }, { target := 710, numerator := 1248748752178045760137330688 }, { target := 717, numerator := 37548166553359569039392768 }, { target := 785, numerator := 5646386951951848791080960 }, { target := 787, numerator := 187781767244818911298846720 }, { target := 790, numerator := 187781767244818911298846720 }, { target := 797, numerator := 5646340835091664517201920 }, { target := 820, numerator := 33878321711711092746485760 }, { target := 822, numerator := 1126690603468913467793080320 }, { target := 825, numerator := 1126690603468913467793080320 }, { target := 832, numerator := 33878045010549987103211520 }, { target := 846, numerator := 5646386951951848791080960 }, { target := 848, numerator := 187781767244818911298846720 }, { target := 851, numerator := 187781767244818911298846720 }, { target := 858, numerator := 5646340835091664517201920 }, { target := 895, numerator := 38395431273272571779350528 }, { target := 897, numerator := 1276916017264768596832157696 }, { target := 900, numerator := 1276916017264768596832157696 }, { target := 907, numerator := 38395117678623318716973056 }]

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
    Slot13.Left17.expected,
    Slot13.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 921, numerator := 38395431273272571779350528 }, { target := 923, numerator := 1276916017264768596832157696 }, { target := 926, numerator := 1276916017264768596832157696 }, { target := 933, numerator := 38395117678623318716973056 }, { target := 966, numerator := 5081748256756663911972864 }, { target := 968, numerator := 169003590520337020168962048 }, { target := 971, numerator := 169003590520337020168962048 }, { target := 978, numerator := 5081706751582498065481728 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9.Parent2
