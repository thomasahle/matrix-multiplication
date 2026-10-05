import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 2; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 3, numerator := 169249614746048084458864640 }, { target := 4, numerator := 169249614746048084458864640 }, { target := 5, numerator := 169249614746048084458864640 }, { target := 6, numerator := 169249614746048084458864640 }, { target := 9, numerator := 174085318024506601157689344 }, { target := 10, numerator := 174085318024506601157689344 }, { target := 11, numerator := 174085318024506601157689344 }, { target := 12, numerator := 174085318024506601157689344 }, { target := 14, numerator := 169249614746048084458864640 }, { target := 15, numerator := 169249614746048084458864640 }, { target := 16, numerator := 169249614746048084458864640 }, { target := 17, numerator := 169249614746048084458864640 }, { target := 18, numerator := 41380053359559033067929600 }, { target := 20, numerator := 400810221126733603746611200 }, { target := 25, numerator := 41380053359559033067929600 }, { target := 45, numerator := 829256269325563022681309184 }, { target := 47, numerator := 8032236831379741419082088448 }, { target := 52, numerator := 829256269325563022681309184 }, { target := 65, numerator := 1392024995015565872405151744 }, { target := 67, numerator := 13483255838703318430036000768 }, { target := 72, numerator := 1392024995015565872405151744 }, { target := 79, numerator := 1335748122446565587432767488 }, { target := 81, numerator := 12938153937970960728940609536 }, { target := 86, numerator := 1335748122446565587432767488 }, { target := 89, numerator := 122135143113052946799001600 }, { target := 90, numerator := 10226269872788172788685864960 }, { target := 95, numerator := 10226273573666202576664657920 }, { target := 103, numerator := 122131442235023158820208640 }, { target := 116, numerator := 41380053359559033067929600 }, { target := 118, numerator := 400810221126733603746611200 }, { target := 123, numerator := 41380053359559033067929600 }, { target := 136, numerator := 1335748122446565587432767488 }, { target := 138, numerator := 12938153937970960728940609536 }, { target := 143, numerator := 1335748122446565587432767488 }, { target := 150, numerator := 892153950432092752944562176 }, { target := 152, numerator := 8641468367492376496776937472 }, { target := 157, numerator := 892153950432092752944562176 }, { target := 160, numerator := 111633803705201665391984640 }, { target := 161, numerator := 9347001808959656997509136384 }, { target := 166, numerator := 9347005191631351513998163968 }, { target := 174, numerator := 111630421033507148902957056 }, { target := 181, numerator := 43035255493941394390646784 }, { target := 183, numerator := 416842629971802947896475648 }, { target := 188, numerator := 43035255493941394390646784 }, { target := 195, numerator := 829256269325563022681309184 }, { target := 197, numerator := 8032236831379741419082088448 }, { target := 202, numerator := 829256269325563022681309184 }, { target := 205, numerator := 122135143113052946799001600 }, { target := 206, numerator := 10226269872788172788685864960 }, { target := 211, numerator := 10226273573666202576664657920 }, { target := 219, numerator := 122131442235023158820208640 }, { target := 221, numerator := 39724851225176671745212416 }, { target := 223, numerator := 384777812281664259596746752 }, { target := 228, numerator := 39724851225176671745212416 }, { target := 231, numerator := 111633803705201665391984640 }, { target := 232, numerator := 9347001808959656997509136384 }, { target := 237, numerator := 9347005191631351513998163968 }, { target := 245, numerator := 111630421033507148902957056 }, { target := 247, numerator := 177131244405957522320523264 }, { target := 248, numerator := 18571891507872080083808157696 }, { target := 250, numerator := 200186427871137488959438848000 }, { target := 258, numerator := 18571905674971528692743798784 }, { target := 265, numerator := 177131244405957522320523264 }]

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
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 18, numerator := 41380053359559033067929600 }, { target := 19, numerator := 829256269325563022681309184 }, { target := 20, numerator := 1392024995015565872405151744 }, { target := 21, numerator := 1335748122446565587432767488 }, { target := 22, numerator := 41380053359559033067929600 }, { target := 23, numerator := 1335748122446565587432767488 }, { target := 24, numerator := 892153950432092752944562176 }, { target := 25, numerator := 43035255493941394390646784 }, { target := 26, numerator := 829256269325563022681309184 }, { target := 27, numerator := 39724851225176671745212416 }, { target := 30, numerator := 149906801632214017663565824 }, { target := 31, numerator := 149906801632214017663565824 }, { target := 32, numerator := 149906801632214017663565824 }, { target := 33, numerator := 149906801632214017663565824 }, { target := 36, numerator := 7016605457043307729994645504 }, { target := 37, numerator := 7016605457043307729994645504 }, { target := 38, numerator := 7016605457043307729994645504 }, { target := 39, numerator := 7016605457043307729994645504 }, { target := 41, numerator := 1910102794991114096035758080 }, { target := 42, numerator := 1910102794991114096035758080 }, { target := 43, numerator := 1910102794991114096035758080 }, { target := 44, numerator := 1910102794991114096035758080 }, { target := 56, numerator := 174085318024506601157689344 }, { target := 57, numerator := 174085318024506601157689344 }, { target := 58, numerator := 174085318024506601157689344 }, { target := 59, numerator := 174085318024506601157689344 }, { target := 61, numerator := 7016605457043307729994645504 }, { target := 62, numerator := 7016605457043307729994645504 }, { target := 63, numerator := 7016605457043307729994645504 }, { target := 64, numerator := 7016605457043307729994645504 }, { target := 75, numerator := 169249614746048084458864640 }, { target := 76, numerator := 169249614746048084458864640 }, { target := 77, numerator := 169249614746048084458864640 }, { target := 78, numerator := 169249614746048084458864640 }, { target := 107, numerator := 169249614746048084458864640 }, { target := 108, numerator := 169249614746048084458864640 }, { target := 109, numerator := 169249614746048084458864640 }, { target := 110, numerator := 169249614746048084458864640 }, { target := 112, numerator := 145071098353755500964741120 }, { target := 113, numerator := 145071098353755500964741120 }, { target := 114, numerator := 145071098353755500964741120 }, { target := 115, numerator := 145071098353755500964741120 }, { target := 127, numerator := 169249614746048084458864640 }, { target := 128, numerator := 169249614746048084458864640 }, { target := 129, numerator := 169249614746048084458864640 }, { target := 130, numerator := 169249614746048084458864640 }, { target := 132, numerator := 1910102794991114096035758080 }, { target := 133, numerator := 1910102794991114096035758080 }, { target := 134, numerator := 1910102794991114096035758080 }, { target := 135, numerator := 1910102794991114096035758080 }, { target := 146, numerator := 145071098353755500964741120 }, { target := 147, numerator := 145071098353755500964741120 }, { target := 148, numerator := 145071098353755500964741120 }, { target := 149, numerator := 145071098353755500964741120 }, { target := 177, numerator := 169249614746048084458864640 }, { target := 178, numerator := 169249614746048084458864640 }, { target := 179, numerator := 169249614746048084458864640 }, { target := 180, numerator := 169249614746048084458864640 }, { target := 191, numerator := 149906801632214017663565824 }, { target := 192, numerator := 149906801632214017663565824 }, { target := 193, numerator := 149906801632214017663565824 }, { target := 194, numerator := 149906801632214017663565824 }]

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
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 177131244405957522320523264 }, { target := 1, numerator := 18571891507872080083808157696 }, { target := 3, numerator := 122135143113052946799001600 }, { target := 4, numerator := 111633803705201665391984640 }, { target := 5, numerator := 122135143113052946799001600 }, { target := 6, numerator := 111633803705201665391984640 }, { target := 7, numerator := 200186427871137488959438848000 }, { target := 9, numerator := 10226269872788172788685864960 }, { target := 10, numerator := 9347001808959656997509136384 }, { target := 11, numerator := 10226269872788172788685864960 }, { target := 12, numerator := 9347001808959656997509136384 }, { target := 55, numerator := 18571905674971528692743798784 }, { target := 56, numerator := 10226273573666202576664657920 }, { target := 57, numerator := 9347005191631351513998163968 }, { target := 58, numerator := 10226273573666202576664657920 }, { target := 59, numerator := 9347005191631351513998163968 }, { target := 65, numerator := 400810221126733603746611200 }, { target := 66, numerator := 8032236831379741419082088448 }, { target := 67, numerator := 13483255838703318430036000768 }, { target := 68, numerator := 12938153937970960728940609536 }, { target := 69, numerator := 400810221126733603746611200 }, { target := 70, numerator := 12938153937970960728940609536 }, { target := 71, numerator := 8641468367492376496776937472 }, { target := 72, numerator := 416842629971802947896475648 }, { target := 73, numerator := 8032236831379741419082088448 }, { target := 74, numerator := 384777812281664259596746752 }, { target := 176, numerator := 177131244405957522320523264 }, { target := 177, numerator := 122131442235023158820208640 }, { target := 178, numerator := 111630421033507148902957056 }, { target := 179, numerator := 122131442235023158820208640 }, { target := 180, numerator := 111630421033507148902957056 }, { target := 181, numerator := 41380053359559033067929600 }, { target := 182, numerator := 829256269325563022681309184 }, { target := 183, numerator := 1392024995015565872405151744 }, { target := 184, numerator := 1335748122446565587432767488 }, { target := 185, numerator := 41380053359559033067929600 }, { target := 186, numerator := 1335748122446565587432767488 }, { target := 187, numerator := 892153950432092752944562176 }, { target := 188, numerator := 43035255493941394390646784 }, { target := 189, numerator := 829256269325563022681309184 }, { target := 190, numerator := 39724851225176671745212416 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent1
