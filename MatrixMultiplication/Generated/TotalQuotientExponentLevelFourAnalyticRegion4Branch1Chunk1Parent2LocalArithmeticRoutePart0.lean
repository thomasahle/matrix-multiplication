import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 90591117848163875020603392 }, { target := 17, numerator := 3068065470111889703443628032 }, { target := 19, numerator := 33296619326553290930498043904 }, { target := 27, numerator := 3068060747766235982075002880 }, { target := 34, numerator := 90569867292722128861790208 }, { target := 35, numerator := 824577946655999726014431232 }, { target := 37, numerator := 29280596183964942514190811136 }, { target := 40, numerator := 29279424732900694309853986816 }, { target := 47, numerator := 825706019327860274630754304 }, { target := 86, numerator := 824577946655999726014431232 }, { target := 89, numerator := 2691280372875752910689927168 }, { target := 91, numerator := 823188953556880605350723584 }, { target := 122, numerator := 90591117848163875020603392 }, { target := 124, numerator := 90591917000095802893271040 }, { target := 126, numerator := 90591917000095802893271040 }, { target := 127, numerator := 3068092535132235633619107840 }, { target := 129, numerator := 33296913053557588199190036480 }, { target := 137, numerator := 3068087812744923615697305600 }, { target := 144, numerator := 90570666257191722245160960 }, { target := 145, numerator := 2691280372875752910689927168 }, { target := 147, numerator := 95605209230445882602248208384 }, { target := 150, numerator := 95601429615914284985826148352 }, { target := 157, numerator := 2694919984699288803117891584 }, { target := 161, numerator := 29280596183964942514190811136 }, { target := 164, numerator := 95605209230445882602248208384 }, { target := 166, numerator := 29231585677824805700078927872 }, { target := 197, numerator := 3068065470111889703443628032 }, { target := 199, numerator := 3068092535132235633619107840 }, { target := 216, numerator := 823188953556880605350723584 }, { target := 218, numerator := 29231585677824805700078927872 }, { target := 221, numerator := 29230416556458852460640862208 }, { target := 228, numerator := 824314782432105481533128704 }, { target := 232, numerator := 22111856271206507991810441216 }, { target := 235, numerator := 71365479167030658642028265472 }, { target := 237, numerator := 22068068453374105734503989248 }, { target := 242, numerator := 33296619326553290930498043904 }, { target := 244, numerator := 33296913053557588199190036480 }, { target := 406, numerator := 630892627736540570487619584 }, { target := 409, numerator := 2036190635880459912377008128 }, { target := 411, numerator := 629643279372644667623473152 }, { target := 416, numerator := 3068060747766235982075002880 }, { target := 418, numerator := 3068087812744923615697305600 }, { target := 498, numerator := 90569867292722128861790208 }, { target := 500, numerator := 90570666257191722245160960 }]

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
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 232, numerator := 7167568461694186318043545600 }, { target := 235, numerator := 24235950448883626343797882880 }, { target := 237, numerator := 7162348103084746726136872960 }, { target := 406, numerator := 194813391591319704143134720 }, { target := 409, numerator := 658729348818828890740883456 }, { target := 411, numerator := 194671503059460813909655552 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent2
