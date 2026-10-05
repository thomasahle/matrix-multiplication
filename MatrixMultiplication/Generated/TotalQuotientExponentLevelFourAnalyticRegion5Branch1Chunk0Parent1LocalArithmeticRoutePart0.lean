import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1921225376457724579020800 }, { target := 57, numerator := 64211555531832697867468800 }, { target := 59, numerator := 711505180626728637169664000 }, { target := 67, numerator := 64210801143710741220556800 }, { target := 74, numerator := 1920068648004057720422400 }, { target := 110, numerator := 1921225376457724579020800 }, { target := 112, numerator := 88278636703110322890735616 }, { target := 115, numerator := 88277421656419181304741888 }, { target := 122, numerator := 1921838276116088033902592 }, { target := 152, numerator := 88278636703110322890735616 }, { target := 153, numerator := 2950465183521369570542616576 }, { target := 155, numerator := 32693044825764083776387809280 }, { target := 163, numerator := 2950430520042650514631950336 }, { target := 170, numerator := 88225486035741103827714048 }, { target := 206, numerator := 64211555531832697867468800 }, { target := 208, numerator := 2950465183521369570542616576 }, { target := 211, numerator := 2950424574002549942195847168 }, { target := 218, numerator := 64232039979378882077786112 }, { target := 283, numerator := 88277421656419181304741888 }, { target := 284, numerator := 2950424574002549942195847168 }, { target := 286, numerator := 32692594846273887496348631040 }, { target := 294, numerator := 2950389911000930971809742848 }, { target := 301, numerator := 88224271720603426712715264 }, { target := 302, numerator := 711505180626728637169664000 }, { target := 304, numerator := 32693044825764083776387809280 }, { target := 307, numerator := 32692594846273887496348631040 }, { target := 314, numerator := 711732161431517911171727360 }, { target := 660, numerator := 1921838276116088033902592 }, { target := 661, numerator := 64232039979378882077786112 }, { target := 663, numerator := 711732161431517911171727360 }, { target := 671, numerator := 64231285350595820343263232 }, { target := 678, numerator := 1920681178648726707634176 }, { target := 679, numerator := 64210801143710741220556800 }, { target := 681, numerator := 2950430520042650514631950336 }, { target := 684, numerator := 2950389911000930971809742848 }, { target := 691, numerator := 64231285350595820343263232 }, { target := 966, numerator := 1920068648004057720422400 }, { target := 968, numerator := 88225486035741103827714048 }, { target := 971, numerator := 88224271720603426712715264 }, { target := 978, numerator := 1920681178648726707634176 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent1
