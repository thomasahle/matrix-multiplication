import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 3; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent2

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
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 117841933213529126662569984 }, { target := 1, numerator := 19312023284365756708505518080 }, { target := 3, numerator := 198824757107634441110295674880 }, { target := 11, numerator := 19312023284365756708505518080 }, { target := 18, numerator := 117841933213529126662569984 }, { target := 19, numerator := 1154060464232033034059120640 }, { target := 21, numerator := 46139123236878417807928197120 }, { target := 24, numerator := 46139111961306102752964771840 }, { target := 31, numerator := 1154060464232033034059120640 }, { target := 35, numerator := 575886947882266678687432704 }, { target := 38, numerator := 2097818319977964316334751744 }, { target := 40, numerator := 575887335263892226588016640 }, { target := 45, numerator := 1262622389292715078162841600 }, { target := 47, numerator := 50479408858343463245892812800 }, { target := 50, numerator := 50479396522083363952630169600 }, { target := 57, numerator := 1262622389292715078162841600 }, { target := 61, numerator := 12021640037042316917600157696 }, { target := 64, numerator := 43791957429540005103487942656 }, { target := 66, numerator := 12021648123633750230024847360 }, { target := 71, numerator := 1199254413057712141308526592 }, { target := 73, numerator := 1199254413057712141308526592 }, { target := 75, numerator := 623877526872455568578052096 }, { target := 78, numerator := 2272636513309461342695981056 }, { target := 80, numerator := 623877946535883245470351360 }, { target := 85, numerator := 1353996917968384675670917120 }, { target := 87, numerator := 1353996917968384675670917120 }, { target := 90, numerator := 1154060464232033034059120640 }, { target := 92, numerator := 46139123236878417807928197120 }, { target := 95, numerator := 46139111961306102752964771840 }, { target := 102, numerator := 1154060464232033034059120640 }, { target := 106, numerator := 12933461037855905825521926144 }, { target := 109, numerator := 47113503102838448604351299584 }, { target := 111, numerator := 12933469737801579588789207040 }, { target := 116, numerator := 1160568786830044007717928960 }, { target := 118, numerator := 1160568786830044007717928960 }, { target := 120, numerator := 19364198622541217070864924672 }, { target := 123, numerator := 70539141009259050136756027392 }, { target := 125, numerator := 19364211648248376119022059520 }, { target := 130, numerator := 15280822359928912768286064640 }, { target := 132, numerator := 15280822359928912768286064640 }, { target := 135, numerator := 1353996917968384675670917120 }, { target := 137, numerator := 1353996917968384675670917120 }, { target := 140, numerator := 599882237377361123632742400 }, { target := 143, numerator := 2185227416643712829515366400 }, { target := 145, numerator := 599882640899887736029184000 }, { target := 150, numerator := 1160568786830044007717928960 }, { target := 152, numerator := 1160568786830044007717928960 }, { target := 161, numerator := 1262622389292715078162841600 }, { target := 163, numerator := 50479408858343463245892812800 }, { target := 166, numerator := 50479396522083363952630169600 }, { target := 173, numerator := 1262622389292715078162841600 }, { target := 177, numerator := 19364198622541217070864924672 }, { target := 180, numerator := 70539141009259050136756027392 }, { target := 182, numerator := 19364211648248376119022059520 }, { target := 191, numerator := 20180038465374428199005454336 }, { target := 194, numerator := 73511050295894499584896925696 }, { target := 196, numerator := 20180052039872223440021749760 }, { target := 211, numerator := 12021640037042316917600157696 }, { target := 214, numerator := 43791957429540005103487942656 }, { target := 216, numerator := 12021648123633750230024847360 }, { target := 238, numerator := 599882237377361123632742400 }, { target := 241, numerator := 2185227416643712829515366400 }, { target := 243, numerator := 599882640899887736029184000 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 1682824740903563811190996992 }, { target := 2, numerator := 2978793219530446286476017664 }, { target := 3, numerator := 96714065569170333976494080 }, { target := 4, numerator := 1856910058928070412348686336 }, { target := 5, numerator := 96714065569170333976494080 }, { target := 6, numerator := 2959450406416612219680718848 }, { target := 7, numerator := 3094850098213450687247810560 }, { target := 8, numerator := 1856910058928070412348686336 }, { target := 9, numerator := 47409234942007297715277398016 }, { target := 10, numerator := 3036821658871948486861914112 }, { target := 11, numerator := 1682824740903563811190996992 }, { target := 12, numerator := 2959450406416612219680718848 }, { target := 13, numerator := 96714065569170333976494080 }, { target := 14, numerator := 3036821658871948486861914112 }, { target := 15, numerator := 96714065569170333976494080 }, { target := 16, numerator := 2959450406416612219680718848 }, { target := 17, numerator := 3094850098213450687247810560 }, { target := 18, numerator := 116056878683004400771792896 }, { target := 89, numerator := 116056878683004400771792896 }, { target := 134, numerator := 1682824740903563811190996992 }, { target := 139, numerator := 2978793219530446286476017664 }, { target := 154, numerator := 96714065569170333976494080 }, { target := 155, numerator := 1353996917968384675670917120 }, { target := 157, numerator := 1353996917968384675670917120 }, { target := 159, numerator := 1856910058928070412348686336 }, { target := 160, numerator := 96714065569170333976494080 }, { target := 187, numerator := 1353996917968384675670917120 }, { target := 189, numerator := 1353996917968384675670917120 }, { target := 201, numerator := 56132843656346461839957164032 }, { target := 203, numerator := 56132843656346461839957164032 }, { target := 205, numerator := 2959450406416612219680718848 }, { target := 206, numerator := 1392682544196052809261514752 }, { target := 208, numerator := 1392682544196052809261514752 }, { target := 210, numerator := 3094850098213450687247810560 }, { target := 221, numerator := 15280822359928912768286064640 }, { target := 223, numerator := 15280822359928912768286064640 }, { target := 225, numerator := 1856910058928070412348686336 }, { target := 226, numerator := 56132843656346461839957164032 }, { target := 228, numerator := 56132843656346461839957164032 }, { target := 230, numerator := 47409234942007297715277398016 }, { target := 231, numerator := 3036821658871948486861914112 }, { target := 232, numerator := 1199254413057712141308526592 }, { target := 234, numerator := 1199254413057712141308526592 }, { target := 236, numerator := 1682824740903563811190996992 }, { target := 237, numerator := 2959450406416612219680718848 }, { target := 248, numerator := 1353996917968384675670917120 }, { target := 250, numerator := 1353996917968384675670917120 }, { target := 252, numerator := 96714065569170333976494080 }, { target := 253, numerator := 1392682544196052809261514752 }, { target := 255, numerator := 1392682544196052809261514752 }, { target := 257, numerator := 3036821658871948486861914112 }, { target := 258, numerator := 96714065569170333976494080 }, { target := 259, numerator := 1353996917968384675670917120 }, { target := 261, numerator := 1353996917968384675670917120 }, { target := 263, numerator := 2959450406416612219680718848 }, { target := 264, numerator := 3094850098213450687247810560 }, { target := 265, numerator := 116056878683004400771792896 }]

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
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1199254413057712141308526592 }, { target := 20, numerator := 1353996917968384675670917120 }, { target := 21, numerator := 1160568786830044007717928960 }, { target := 22, numerator := 15280822359928912768286064640 }, { target := 23, numerator := 1353996917968384675670917120 }, { target := 24, numerator := 1160568786830044007717928960 }, { target := 25, numerator := 1353996917968384675670917120 }, { target := 26, numerator := 1353996917968384675670917120 }, { target := 27, numerator := 56132843656346461839957164032 }, { target := 28, numerator := 1392682544196052809261514752 }, { target := 29, numerator := 15280822359928912768286064640 }, { target := 30, numerator := 56132843656346461839957164032 }, { target := 31, numerator := 1199254413057712141308526592 }, { target := 32, numerator := 1353996917968384675670917120 }, { target := 33, numerator := 1392682544196052809261514752 }, { target := 34, numerator := 1353996917968384675670917120 }, { target := 35, numerator := 575886947882266678687432704 }, { target := 36, numerator := 12021640037042316917600157696 }, { target := 37, numerator := 623877526872455568578052096 }, { target := 38, numerator := 12933461037855905825521926144 }, { target := 39, numerator := 19364198622541217070864924672 }, { target := 40, numerator := 599882237377361123632742400 }, { target := 41, numerator := 19364198622541217070864924672 }, { target := 42, numerator := 20180038465374428199005454336 }, { target := 43, numerator := 12021640037042316917600157696 }, { target := 44, numerator := 599882237377361123632742400 }, { target := 90, numerator := 1199254413057712141308526592 }, { target := 91, numerator := 1353996917968384675670917120 }, { target := 92, numerator := 1160568786830044007717928960 }, { target := 93, numerator := 15280822359928912768286064640 }, { target := 94, numerator := 1353996917968384675670917120 }, { target := 95, numerator := 1160568786830044007717928960 }, { target := 96, numerator := 1353996917968384675670917120 }, { target := 97, numerator := 1353996917968384675670917120 }, { target := 98, numerator := 56132843656346461839957164032 }, { target := 99, numerator := 1392682544196052809261514752 }, { target := 100, numerator := 15280822359928912768286064640 }, { target := 101, numerator := 56132843656346461839957164032 }, { target := 102, numerator := 1199254413057712141308526592 }, { target := 103, numerator := 1353996917968384675670917120 }, { target := 104, numerator := 1392682544196052809261514752 }, { target := 105, numerator := 1353996917968384675670917120 }, { target := 106, numerator := 2097818319977964316334751744 }, { target := 107, numerator := 43791957429540005103487942656 }, { target := 108, numerator := 2272636513309461342695981056 }, { target := 109, numerator := 47113503102838448604351299584 }, { target := 110, numerator := 70539141009259050136756027392 }, { target := 111, numerator := 2185227416643712829515366400 }, { target := 112, numerator := 70539141009259050136756027392 }, { target := 113, numerator := 73511050295894499584896925696 }, { target := 114, numerator := 43791957429540005103487942656 }, { target := 115, numerator := 2185227416643712829515366400 }, { target := 140, numerator := 575887335263892226588016640 }, { target := 141, numerator := 12021648123633750230024847360 }, { target := 142, numerator := 623877946535883245470351360 }, { target := 143, numerator := 12933469737801579588789207040 }, { target := 144, numerator := 19364211648248376119022059520 }, { target := 145, numerator := 599882640899887736029184000 }, { target := 146, numerator := 19364211648248376119022059520 }, { target := 147, numerator := 20180052039872223440021749760 }, { target := 148, numerator := 12021648123633750230024847360 }, { target := 149, numerator := 599882640899887736029184000 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1154060464232033034059120640 }, { target := 72, numerator := 1262622389292715078162841600 }, { target := 73, numerator := 1154060464232033034059120640 }, { target := 74, numerator := 1262622389292715078162841600 }, { target := 89, numerator := 117841933213529126662569984 }, { target := 116, numerator := 46139123236878417807928197120 }, { target := 117, numerator := 50479408858343463245892812800 }, { target := 118, numerator := 46139123236878417807928197120 }, { target := 119, numerator := 50479408858343463245892812800 }, { target := 134, numerator := 19312023284365756708505518080 }, { target := 150, numerator := 46139111961306102752964771840 }, { target := 151, numerator := 50479396522083363952630169600 }, { target := 152, numerator := 46139111961306102752964771840 }, { target := 153, numerator := 50479396522083363952630169600 }, { target := 154, numerator := 198824757107634441110295674880 }, { target := 232, numerator := 1154060464232033034059120640 }, { target := 233, numerator := 1262622389292715078162841600 }, { target := 234, numerator := 1154060464232033034059120640 }, { target := 235, numerator := 1262622389292715078162841600 }, { target := 236, numerator := 19312023284365756708505518080 }, { target := 265, numerator := 117841933213529126662569984 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent2
