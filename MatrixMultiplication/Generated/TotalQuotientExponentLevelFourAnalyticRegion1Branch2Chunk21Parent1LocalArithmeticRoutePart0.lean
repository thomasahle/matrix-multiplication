import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 87; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot0.Left5.expected,
    Slot0.Left12.expected,
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
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 3644637786989302115201429012480 }, { target := 17, numerator := 144606870839023483361653948416 }, { target := 18, numerator := 8123981507810308054025502720 }, { target := 19, numerator := 13138017744525069657363206635520 }, { target := 20, numerator := 219618300094471994393822756864 }, { target := 21, numerator := 3644636578063194270196102594560 }, { target := 22, numerator := 219618300094471994393822756864 }, { target := 23, numerator := 219618300094471994393822756864 }, { target := 24, numerator := 144606870839023483361653948416 }, { target := 25, numerator := 8123981507810308054025502720 }, { target := 26, numerator := 6765981717287212624993430011904 }, { target := 27, numerator := 31064894255642439440633167872 }, { target := 28, numerator := 6765981717287212624993430011904 }, { target := 29, numerator := 31064894255642439440633167872 }, { target := 44, numerator := 348860002385816030254028816384 }, { target := 50, numerator := 8123981507810308054025502720 }, { target := 51, numerator := 144606870839023483361653948416 }, { target := 52, numerator := 8123981507810308054025502720 }, { target := 53, numerator := 128629707206996544188737126400 }, { target := 54, numerator := 219618300094471994393822756864 }, { target := 55, numerator := 8123981507810308054025502720 }, { target := 56, numerator := 219618300094471994393822756864 }, { target := 57, numerator := 219618300094471994393822756864 }, { target := 58, numerator := 144606870839023483361653948416 }, { target := 59, numerator := 8123981507810308054025502720 }, { target := 60, numerator := 24448965425730505619124445511680 }, { target := 61, numerator := 105301601802062803298840215552 }, { target := 62, numerator := 24448965425730505619124445511680 }, { target := 63, numerator := 105301601802062803298840215552 }, { target := 64, numerator := 12921857204586361068055647223808 }, { target := 71, numerator := 6765981717287212624993430011904 }, { target := 72, numerator := 31064894255642439440633167872 }, { target := 73, numerator := 6765981717287212624993430011904 }, { target := 74, numerator := 31064894255642439440633167872 }, { target := 75, numerator := 12921610102037778431000195366912 }, { target := 104, numerator := 349107133268597564527351955456 }]

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
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
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
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 268848026205091471817560817664 }, { target := 1, numerator := 38956425611261810525731815424 }, { target := 2, numerator := 8746469652703804214202106642432 }, { target := 3, numerator := 306525559414928456505100337152 }, { target := 4, numerator := 36906087421195399445430140928 }, { target := 5, numerator := 8746467518194153957122470051840 }, { target := 6, numerator := 36906087421195399445430140928 }, { target := 7, numerator := 36906087421195399445430140928 }, { target := 8, numerator := 1580810744541202942912591036416 }, { target := 9, numerator := 36906087421195399445430140928 }, { target := 10, numerator := 306525559414928456505100337152 }, { target := 11, numerator := 1580810744541202942912591036416 }, { target := 12, numerator := 268850160714741728897197408256 }, { target := 13, numerator := 36906087421195399445430140928 }, { target := 14, numerator := 36906087421195399445430140928 }, { target := 15, numerator := 38956425611261810525731815424 }, { target := 16, numerator := 5888829288363524205692659433472 }, { target := 19, numerator := 21418941516749709040309596323840 }, { target := 21, numerator := 5888829288363524205692659433472 }, { target := 26, numerator := 3652030495212340664889193267200 }, { target := 28, numerator := 3652028757801078723841584267264 }, { target := 40, numerator := 149771401940417179195998732288 }, { target := 42, numerator := 149771401940417179195998732288 }, { target := 44, numerator := 34043351080347957559725916160 }, { target := 45, numerator := 8414123704517819055954984960 }, { target := 47, numerator := 8414123704517819055954984960 }, { target := 49, numerator := 40426479407913199602174525440 }, { target := 50, numerator := 9525341359820520664270129594368 }, { target := 53, numerator := 34428323350709639472838231457792 }, { target := 55, numerator := 9525340150894989280017106599936 }, { target := 60, numerator := 13168020623649992109776258990080 }, { target := 62, numerator := 13168014408175915556707288219648 }, { target := 64, numerator := 30851786916565336538501611520 }, { target := 65, numerator := 227461810812131708479316426752 }, { target := 67, numerator := 227461810812131708479316426752 }, { target := 69, numerator := 318092561657001228448689029120 }, { target := 70, numerator := 38298769965391452254691655680 }, { target := 71, numerator := 3652029283925049015499090821120 }, { target := 73, numerator := 3652027546514364661103692087296 }, { target := 75, numerator := 30851786916565336538501611520 }, { target := 76, numerator := 38298769965391452254691655680 }, { target := 91, numerator := 38298769965391452254691655680 }, { target := 96, numerator := 1640463980184267204909292584960 }, { target := 97, numerator := 38298769965391452254691655680 }, { target := 102, numerator := 318092561657001228448689029120 }, { target := 103, numerator := 1640463980184267204909292584960 }, { target := 104, numerator := 34043351080347957559725916160 }, { target := 109, numerator := 38298769965391452254691655680 }, { target := 110, numerator := 38298769965391452254691655680 }, { target := 111, numerator := 40426479407913199602174525440 }]

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
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 107579640550443028907556864000 }, { target := 2, numerator := 4012284796024203077347792912384 }, { target := 5, numerator := 4012034080865261045013752578048 }, { target := 12, numerator := 107830384043583958459468480512 }, { target := 16, numerator := 789887459334942317497961938944 }, { target := 19, numerator := 2710499715604739048334944108544 }, { target := 21, numerator := 789887459334942317497961938944 }, { target := 30, numerator := 27181782473687134510554021888 }, { target := 33, numerator := 92138901576804952886485188608 }, { target := 35, numerator := 27181782473687134510554021888 }, { target := 50, numerator := 789887459334942317497961938944 }, { target := 53, numerator := 2710499715604739048334944108544 }, { target := 55, numerator := 789887459334942317497961938944 }, { target := 77, numerator := 27181782473687134510554021888 }, { target := 80, numerator := 92138901576804952886485188608 }, { target := 82, numerator := 27181782473687134510554021888 }, { target := 87, numerator := 227461810812131708479316426752 }, { target := 89, numerator := 227461810812131708479316426752 }, { target := 92, numerator := 227461810812131708479316426752 }, { target := 94, numerator := 227461810812131708479316426752 }, { target := 98, numerator := 149771401940417179195998732288 }, { target := 100, numerator := 149771401940417179195998732288 }, { target := 105, numerator := 8414123704517819055954984960 }, { target := 107, numerator := 8414123704517819055954984960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent1
