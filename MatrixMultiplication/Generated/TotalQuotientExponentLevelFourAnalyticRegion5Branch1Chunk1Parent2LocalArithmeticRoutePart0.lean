import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10838536312332609430487040 }, { target := 30, numerator := 530879174048663858522882048 }, { target := 35, numerator := 530889183719640779632672768 }, { target := 43, numerator := 10840925717662584147017728 }, { target := 71, numerator := 735909695059558808944640 }, { target := 72, numerator := 26045883558295081387556864 }, { target := 74, numerator := 288479217796135644020342784 }, { target := 82, numerator := 26001803849047902884200448 }, { target := 89, numerator := 735688157364388920033280 }, { target := 104, numerator := 385451219910113437585244160 }, { target := 105, numerator := 18879673358578434794577723392 }, { target := 110, numerator := 18880029332833423727653814272 }, { target := 118, numerator := 385536194409691440964698112 }, { target := 146, numerator := 12297856053165327667691520 }, { target := 147, numerator := 459489158542367202144681984 }, { target := 149, numerator := 5087227735294481974872244224 }, { target := 157, numerator := 458020747091951260331409408 }, { target := 164, numerator := 12297856053165327667691520 }, { target := 200, numerator := 10838536312332609430487040 }, { target := 202, numerator := 385451219910113437585244160 }, { target := 205, numerator := 385449660945473801897902080 }, { target := 212, numerator := 10838961484507055527034880 }, { target := 226, numerator := 385449660945473801897902080 }, { target := 227, numerator := 18879596999387819807338397696 }, { target := 232, numerator := 18879952972203064234539483136 }, { target := 240, numerator := 385534635101370858713645056 }, { target := 242, numerator := 136268125261209760536985600 }, { target := 243, numerator := 5091434307063881016037867520 }, { target := 245, numerator := 56369743089241983172707614720 }, { target := 253, numerator := 5075163367267934111258378240 }, { target := 260, numerator := 136268125261209760536985600 }, { target := 296, numerator := 530879174048663858522882048 }, { target := 298, numerator := 18879673358578434794577723392 }, { target := 301, numerator := 18879596999387819807338397696 }, { target := 308, numerator := 530899999282467945951789056 }, { target := 624, numerator := 10838961484507055527034880 }, { target := 625, numerator := 530899999282467945951789056 }, { target := 630, numerator := 530910009346102459572944896 }, { target := 638, numerator := 10841350983568197488214016 }, { target := 640, numerator := 12297711572059782087966720 }, { target := 641, numerator := 459483760243564109390413824 }, { target := 643, numerator := 5087167968105454884265918464 }, { target := 651, numerator := 458015366044749490173247488 }, { target := 658, numerator := 12297711572059782087966720 }, { target := 659, numerator := 530889183719640779632672768 }, { target := 661, numerator := 18880029332833423727653814272 }, { target := 664, numerator := 18879952972203064234539483136 }, { target := 671, numerator := 530910009346102459572944896 }, { target := 1017, numerator := 367733309834609515560960 }, { target := 1018, numerator := 13739750113631678163320832 }, { target := 1020, numerator := 152119449511751011220324352 }, { target := 1028, numerator := 13695841337945406553718784 }, { target := 1035, numerator := 367733309834609515560960 }, { target := 1036, numerator := 10840925717662584147017728 }, { target := 1038, numerator := 385536194409691440964698112 }, { target := 1041, numerator := 385534635101370858713645056 }, { target := 1048, numerator := 10841350983568197488214016 }]

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
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 13748027505129753719865344 }, { target := 147, numerator := 459489158542367202144681984 }, { target := 149, numerator := 5091434307063881016037867520 }, { target := 157, numerator := 459483760243564109390413824 }, { target := 164, numerator := 13739750113631678163320832 }, { target := 242, numerator := 152211092534925883483357184 }, { target := 243, numerator := 5087227735294481974872244224 }, { target := 245, numerator := 56369743089241983172707614720 }, { target := 253, numerator := 5087167968105454884265918464 }, { target := 260, numerator := 152119449511751011220324352 }, { target := 640, numerator := 13704092276988120796233728 }, { target := 641, numerator := 458020747091951260331409408 }, { target := 643, numerator := 5075163367267934111258378240 }, { target := 651, numerator := 458015366044749490173247488 }, { target := 658, numerator := 13695841337945406553718784 }, { target := 1017, numerator := 367954847529779404472320 }, { target := 1018, numerator := 12297856053165327667691520 }, { target := 1020, numerator := 136268125261209760536985600 }, { target := 1028, numerator := 12297711572059782087966720 }, { target := 1035, numerator := 367733309834609515560960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent2
