import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 10; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent1

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
  [{ target := 35, numerator := 663908188220886197269954560 }, { target := 38, numerator := 2269947077174763886259208192 }, { target := 40, numerator := 663907973777486340396417024 }, { target := 61, numerator := 16276458807995919675005337600 }, { target := 64, numerator := 55650315440413566243774136320 }, { target := 66, numerator := 16276453550673858667783127040 }, { target := 71, numerator := 1392997485457623252436254720 }, { target := 73, numerator := 1392367602934482366086774784 }, { target := 75, numerator := 663908188220886197269954560 }, { target := 78, numerator := 2269947077174763886259208192 }, { target := 80, numerator := 663907973777486340396417024 }, { target := 85, numerator := 1363976704510589434677166080 }, { target := 87, numerator := 1363359944540013983459966976 }, { target := 89, numerator := 116056878683004400771792896 }, { target := 106, numerator := 13642242448280790569708421120 }, { target := 109, numerator := 46643751230978212759584374784 }, { target := 111, numerator := 13642238041814799962339278848 }, { target := 116, numerator := 1073768895040251257086279680 }, { target := 118, numerator := 1073283360595330157191888896 }, { target := 130, numerator := 33751168241400330053820088320 }, { target := 132, numerator := 33735906712766728994977480704 }, { target := 134, numerator := 3094850098213450687247810560 }, { target := 135, numerator := 1073768895040251257086279680 }, { target := 137, numerator := 1073283360595330157191888896 }, { target := 139, numerator := 2959450406416612219680718848 }, { target := 150, numerator := 1073768895040251257086279680 }, { target := 152, numerator := 1073283360595330157191888896 }, { target := 154, numerator := 96714065569170333976494080 }, { target := 155, numerator := 1102789675987285074845368320 }, { target := 157, numerator := 1102291018989798539818696704 }, { target := 159, numerator := 3036821658871948486861914112 }, { target := 160, numerator := 96714065569170333976494080 }, { target := 187, numerator := 1102789675987285074845368320 }, { target := 189, numerator := 1102291018989798539818696704 }, { target := 201, numerator := 18660362148942744819093995520 }, { target := 203, numerator := 18651924347643170029037420544 }, { target := 205, numerator := 2959450406416612219680718848 }, { target := 206, numerator := 1015727333146183621568102400 }, { target := 208, numerator := 1015268043806393391938273280 }, { target := 210, numerator := 1682824740903563811190996992 }, { target := 221, numerator := 33751168241400330053820088320 }, { target := 223, numerator := 33735906712766728994977480704 }, { target := 225, numerator := 3036821658871948486861914112 }, { target := 226, numerator := 18660362148942744819093995520 }, { target := 228, numerator := 18651924347643170029037420544 }, { target := 230, numerator := 47409234942007297715277398016 }, { target := 231, numerator := 1856910058928070412348686336 }, { target := 232, numerator := 1392997485457623252436254720 }, { target := 234, numerator := 1392367602934482366086774784 }, { target := 236, numerator := 3094850098213450687247810560 }, { target := 237, numerator := 2959450406416612219680718848 }, { target := 248, numerator := 1073768895040251257086279680 }, { target := 250, numerator := 1073283360595330157191888896 }, { target := 252, numerator := 96714065569170333976494080 }, { target := 253, numerator := 1015727333146183621568102400 }, { target := 255, numerator := 1015268043806393391938273280 }, { target := 257, numerator := 1856910058928070412348686336 }, { target := 258, numerator := 96714065569170333976494080 }, { target := 259, numerator := 1363976704510589434677166080 }, { target := 261, numerator := 1363359944540013983459966976 }, { target := 263, numerator := 2978793219530446286476017664 }, { target := 264, numerator := 1682824740903563811190996992 }, { target := 265, numerator := 116056878683004400771792896 }]

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
    Slot6.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 177131244405957522320523264 }, { target := 1, numerator := 18571891507872080083808157696 }, { target := 3, numerator := 200186427871137488959438848000 }, { target := 11, numerator := 18571905674971528692743798784 }, { target := 18, numerator := 177131244405957522320523264 }, { target := 19, numerator := 1376927379538117778210816000 }, { target := 21, numerator := 48189025315938967274651648000 }, { target := 24, numerator := 48189048950829811715014656000 }, { target := 31, numerator := 1376915562092695558029312000 }, { target := 45, numerator := 1367523973043711120213278720 }, { target := 47, numerator := 47859929533293530424971100160 }, { target := 50, numerator := 47859953006775364220375531520 }, { target := 57, numerator := 1367512236302794222511063040 }, { target := 71, numerator := 1376927379538117778210816000 }, { target := 72, numerator := 1367523973043711120213278720 }, { target := 73, numerator := 1376927379538117778210816000 }, { target := 74, numerator := 1380957410892863488781189120 }, { target := 89, numerator := 177131244405957522320523264 }, { target := 90, numerator := 1376927379538117778210816000 }, { target := 92, numerator := 48189025315938967274651648000 }, { target := 95, numerator := 48189048950829811715014656000 }, { target := 102, numerator := 1376915562092695558029312000 }, { target := 116, numerator := 48189025315938967274651648000 }, { target := 117, numerator := 47859929533293530424971100160 }, { target := 118, numerator := 48189025315938967274651648000 }, { target := 119, numerator := 48330066365644154495943311360 }, { target := 120, numerator := 13406662123428218048096501760 }, { target := 123, numerator := 45838286139077490090266591232 }, { target := 125, numerator := 13406657793055046744779259904 }, { target := 134, numerator := 18571891507872080083808157696 }, { target := 140, numerator := 663908188220886197269954560 }, { target := 143, numerator := 2269947077174763886259208192 }, { target := 145, numerator := 663907973777486340396417024 }, { target := 150, numerator := 48189048950829811715014656000 }, { target := 151, numerator := 47859953006775364220375531520 }, { target := 152, numerator := 48189048950829811715014656000 }, { target := 153, numerator := 48330090069710289212717137920 }, { target := 154, numerator := 200186427871137488959438848000 }, { target := 161, numerator := 1380957410892863488781189120 }, { target := 163, numerator := 48330066365644154495943311360 }, { target := 166, numerator := 48330090069710289212717137920 }, { target := 173, numerator := 1380945558859796130394275840 }, { target := 177, numerator := 13428078516596633731879403520 }, { target := 180, numerator := 45911510238341192151113662464 }, { target := 182, numerator := 13428074179305933400921079808 }, { target := 191, numerator := 12036012960649614285990789120 }, { target := 194, numerator := 41151943786200558196054032384 }, { target := 196, numerator := 12036009072998300751702786048 }, { target := 211, numerator := 16276458807995919675005337600 }, { target := 214, numerator := 55650315440413566243774136320 }, { target := 216, numerator := 16276453550673858667783127040 }, { target := 232, numerator := 1376915562092695558029312000 }, { target := 233, numerator := 1367512236302794222511063040 }, { target := 234, numerator := 1376915562092695558029312000 }, { target := 235, numerator := 1380945558859796130394275840 }, { target := 236, numerator := 18571905674971528692743798784 }, { target := 238, numerator := 663908188220886197269954560 }, { target := 241, numerator := 2269947077174763886259208192 }, { target := 243, numerator := 663907973777486340396417024 }, { target := 265, numerator := 177131244405957522320523264 }]

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
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1392997485457623252436254720 }, { target := 20, numerator := 1363976704510589434677166080 }, { target := 21, numerator := 1073768895040251257086279680 }, { target := 22, numerator := 33751168241400330053820088320 }, { target := 23, numerator := 1073768895040251257086279680 }, { target := 24, numerator := 1073768895040251257086279680 }, { target := 25, numerator := 1102789675987285074845368320 }, { target := 26, numerator := 1102789675987285074845368320 }, { target := 27, numerator := 18660362148942744819093995520 }, { target := 28, numerator := 1015727333146183621568102400 }, { target := 29, numerator := 33751168241400330053820088320 }, { target := 30, numerator := 18660362148942744819093995520 }, { target := 31, numerator := 1392997485457623252436254720 }, { target := 32, numerator := 1073768895040251257086279680 }, { target := 33, numerator := 1015727333146183621568102400 }, { target := 34, numerator := 1363976704510589434677166080 }, { target := 35, numerator := 663908188220886197269954560 }, { target := 36, numerator := 16276458807995919675005337600 }, { target := 37, numerator := 663908188220886197269954560 }, { target := 38, numerator := 13642242448280790569708421120 }, { target := 39, numerator := 13406662123428218048096501760 }, { target := 40, numerator := 663908188220886197269954560 }, { target := 41, numerator := 13428078516596633731879403520 }, { target := 42, numerator := 12036012960649614285990789120 }, { target := 43, numerator := 16276458807995919675005337600 }, { target := 44, numerator := 663908188220886197269954560 }, { target := 90, numerator := 1392367602934482366086774784 }, { target := 91, numerator := 1363359944540013983459966976 }, { target := 92, numerator := 1073283360595330157191888896 }, { target := 93, numerator := 33735906712766728994977480704 }, { target := 94, numerator := 1073283360595330157191888896 }, { target := 95, numerator := 1073283360595330157191888896 }, { target := 96, numerator := 1102291018989798539818696704 }, { target := 97, numerator := 1102291018989798539818696704 }, { target := 98, numerator := 18651924347643170029037420544 }, { target := 99, numerator := 1015268043806393391938273280 }, { target := 100, numerator := 33735906712766728994977480704 }, { target := 101, numerator := 18651924347643170029037420544 }, { target := 102, numerator := 1392367602934482366086774784 }, { target := 103, numerator := 1073283360595330157191888896 }, { target := 104, numerator := 1015268043806393391938273280 }, { target := 105, numerator := 1363359944540013983459966976 }, { target := 106, numerator := 2269947077174763886259208192 }, { target := 107, numerator := 55650315440413566243774136320 }, { target := 108, numerator := 2269947077174763886259208192 }, { target := 109, numerator := 46643751230978212759584374784 }, { target := 110, numerator := 45838286139077490090266591232 }, { target := 111, numerator := 2269947077174763886259208192 }, { target := 112, numerator := 45911510238341192151113662464 }, { target := 113, numerator := 41151943786200558196054032384 }, { target := 114, numerator := 55650315440413566243774136320 }, { target := 115, numerator := 2269947077174763886259208192 }, { target := 140, numerator := 663907973777486340396417024 }, { target := 141, numerator := 16276453550673858667783127040 }, { target := 142, numerator := 663907973777486340396417024 }, { target := 143, numerator := 13642238041814799962339278848 }, { target := 144, numerator := 13406657793055046744779259904 }, { target := 145, numerator := 663907973777486340396417024 }, { target := 146, numerator := 13428074179305933400921079808 }, { target := 147, numerator := 12036009072998300751702786048 }, { target := 148, numerator := 16276453550673858667783127040 }, { target := 149, numerator := 663907973777486340396417024 }]

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
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 3094850098213450687247810560 }, { target := 2, numerator := 2959450406416612219680718848 }, { target := 3, numerator := 96714065569170333976494080 }, { target := 4, numerator := 3036821658871948486861914112 }, { target := 5, numerator := 96714065569170333976494080 }, { target := 6, numerator := 2959450406416612219680718848 }, { target := 7, numerator := 1682824740903563811190996992 }, { target := 8, numerator := 3036821658871948486861914112 }, { target := 9, numerator := 47409234942007297715277398016 }, { target := 10, numerator := 1856910058928070412348686336 }, { target := 11, numerator := 3094850098213450687247810560 }, { target := 12, numerator := 2959450406416612219680718848 }, { target := 13, numerator := 96714065569170333976494080 }, { target := 14, numerator := 1856910058928070412348686336 }, { target := 15, numerator := 96714065569170333976494080 }, { target := 16, numerator := 2978793219530446286476017664 }, { target := 17, numerator := 1682824740903563811190996992 }, { target := 18, numerator := 116056878683004400771792896 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent1
