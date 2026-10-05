import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk24Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 98; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent0

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
    Slot0.Left3.expected,
    Slot0.Left11.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot1.Left5.expected,
    Slot1.Left12.expected,
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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 670708414402962560087228416 }, { target := 36, numerator := 13414168288059251201744568320 }, { target := 37, numerator := 694662286345925508661772288 }, { target := 38, numerator := 12479967282283696207337357312 }, { target := 39, numerator := 18684020115511099888144220160 }, { target := 40, numerator := 670708414402962560087228416 }, { target := 41, numerator := 18707973987454062836718764032 }, { target := 42, numerator := 18707973987454062836718764032 }, { target := 43, numerator := 13390214416116288253170024448 }, { target := 44, numerator := 694662286345925508661772288 }, { target := 71, numerator := 1179752939498100098659778560 }, { target := 72, numerator := 1295794212235618141150904320 }, { target := 73, numerator := 1179752939498100098659778560 }, { target := 74, numerator := 1295794212235618141150904320 }, { target := 89, numerator := 290822217481044230840254464 }, { target := 106, numerator := 2449774767478166874646118400 }, { target := 107, numerator := 48995495349563337492922368000 }, { target := 108, numerator := 2537266723459529977312051200 }, { target := 109, numerator := 45583309066290176488950988800 }, { target := 110, numerator := 68243725665463220079427584000 }, { target := 111, numerator := 2449774767478166874646118400 }, { target := 112, numerator := 68331217621444583182093516800 }, { target := 113, numerator := 68331217621444583182093516800 }, { target := 114, numerator := 48908003393581974390256435200 }, { target := 115, numerator := 2537266723459529977312051200 }, { target := 116, numerator := 46016716684513965363282575360 }, { target := 117, numerator := 50542951112498945562949713920 }, { target := 118, numerator := 46016716684513965363282575360 }, { target := 119, numerator := 50542951112498945562949713920 }, { target := 134, numerator := 22396994191897044097966276608 }, { target := 139, numerator := 3056164471985782553657212928 }, { target := 150, numerator := 46016699805743137919042846720 }, { target := 151, numerator := 50542932573521151484850339840 }, { target := 152, numerator := 46016699805743137919042846720 }, { target := 153, numerator := 50542932573521151484850339840 }, { target := 154, numerator := 196138717553476532739552313344 }, { target := 159, numerator := 1934281311383406679529881600 }, { target := 160, numerator := 116056878683004400771792896 }, { target := 205, numerator := 3056164471985782553657212928 }, { target := 210, numerator := 3036821658871948486861914112 }, { target := 225, numerator := 1934281311383406679529881600 }, { target := 230, numerator := 46867636174819943845009031168 }, { target := 231, numerator := 2998136032644280353271316480 }, { target := 232, numerator := 1179758565755042580073021440 }, { target := 233, numerator := 1295800391894882833850695680 }, { target := 234, numerator := 1179758565755042580073021440 }, { target := 235, numerator := 1295800391894882833850695680 }, { target := 236, numerator := 22397008358996492706901917696 }, { target := 237, numerator := 3056164471985782553657212928 }, { target := 252, numerator := 116056878683004400771792896 }, { target := 257, numerator := 2998136032644280353271316480 }, { target := 258, numerator := 116056878683004400771792896 }, { target := 263, numerator := 3056164471985782553657212928 }, { target := 264, numerator := 3056164471985782553657212928 }, { target := 265, numerator := 290822217481044230840254464 }]

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
    Slot3.Left5.expected,
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
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1392682544196052809261514752 }, { target := 20, numerator := 1586110675334393477214502912 }, { target := 21, numerator := 1237940039285380274899124224 }, { target := 22, numerator := 16596133651669629310366384128 }, { target := 23, numerator := 1470053796651389076442710016 }, { target := 24, numerator := 1237940039285380274899124224 }, { target := 25, numerator := 1470053796651389076442710016 }, { target := 26, numerator := 1431368170423720942852112384 }, { target := 27, numerator := 54082505466280050759655489536 }, { target := 28, numerator := 1431368170423720942852112384 }, { target := 29, numerator := 16596133651669629310366384128 }, { target := 30, numerator := 54082505466280050759655489536 }, { target := 31, numerator := 1392682544196052809261514752 }, { target := 32, numerator := 1431368170423720942852112384 }, { target := 33, numerator := 1431368170423720942852112384 }, { target := 34, numerator := 1586110675334393477214502912 }, { target := 71, numerator := 1392682544196052809261514752 }, { target := 73, numerator := 1392682544196052809261514752 }, { target := 85, numerator := 1586110675334393477214502912 }, { target := 87, numerator := 1586110675334393477214502912 }, { target := 116, numerator := 1237940039285380274899124224 }, { target := 118, numerator := 1237940039285380274899124224 }, { target := 130, numerator := 16596133651669629310366384128 }, { target := 132, numerator := 16596133651669629310366384128 }, { target := 135, numerator := 1470053796651389076442710016 }, { target := 137, numerator := 1470053796651389076442710016 }, { target := 140, numerator := 670708188430347657145221120 }, { target := 141, numerator := 13414163768606953142904422400 }, { target := 142, numerator := 694662052302860073471836160 }, { target := 143, numerator := 12479963077578968906166435840 }, { target := 144, numerator := 18684013820559684734759731200 }, { target := 145, numerator := 670708188430347657145221120 }, { target := 146, numerator := 18707967684432197151086346240 }, { target := 147, numerator := 18707967684432197151086346240 }, { target := 148, numerator := 13390209904734440726577807360 }, { target := 149, numerator := 694662052302860073471836160 }, { target := 150, numerator := 1237940039285380274899124224 }, { target := 152, numerator := 1237940039285380274899124224 }, { target := 155, numerator := 1470053796651389076442710016 }, { target := 157, numerator := 1470053796651389076442710016 }, { target := 187, numerator := 1431368170423720942852112384 }, { target := 189, numerator := 1431368170423720942852112384 }, { target := 201, numerator := 54082505466280050759655489536 }, { target := 203, numerator := 54082505466280050759655489536 }, { target := 206, numerator := 1431368170423720942852112384 }, { target := 208, numerator := 1431368170423720942852112384 }, { target := 221, numerator := 16596133651669629310366384128 }, { target := 223, numerator := 16596133651669629310366384128 }, { target := 226, numerator := 54082505466280050759655489536 }, { target := 228, numerator := 54082505466280050759655489536 }, { target := 232, numerator := 1392682544196052809261514752 }, { target := 234, numerator := 1392682544196052809261514752 }, { target := 248, numerator := 1431368170423720942852112384 }, { target := 250, numerator := 1431368170423720942852112384 }, { target := 253, numerator := 1431368170423720942852112384 }, { target := 255, numerator := 1431368170423720942852112384 }, { target := 259, numerator := 1586110675334393477214502912 }, { target := 261, numerator := 1586110675334393477214502912 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 670708414402962560087228416 }, { target := 38, numerator := 2449774767478166874646118400 }, { target := 40, numerator := 670708188430347657145221120 }, { target := 61, numerator := 13414168288059251201744568320 }, { target := 64, numerator := 48995495349563337492922368000 }, { target := 66, numerator := 13414163768606953142904422400 }, { target := 75, numerator := 694662286345925508661772288 }, { target := 78, numerator := 2537266723459529977312051200 }, { target := 80, numerator := 694662052302860073471836160 }, { target := 90, numerator := 1392682544196052809261514752 }, { target := 91, numerator := 1586110675334393477214502912 }, { target := 92, numerator := 1237940039285380274899124224 }, { target := 93, numerator := 16596133651669629310366384128 }, { target := 94, numerator := 1470053796651389076442710016 }, { target := 95, numerator := 1237940039285380274899124224 }, { target := 96, numerator := 1470053796651389076442710016 }, { target := 97, numerator := 1431368170423720942852112384 }, { target := 98, numerator := 54082505466280050759655489536 }, { target := 99, numerator := 1431368170423720942852112384 }, { target := 100, numerator := 16596133651669629310366384128 }, { target := 101, numerator := 54082505466280050759655489536 }, { target := 102, numerator := 1392682544196052809261514752 }, { target := 103, numerator := 1431368170423720942852112384 }, { target := 104, numerator := 1431368170423720942852112384 }, { target := 105, numerator := 1586110675334393477214502912 }, { target := 106, numerator := 12479967282283696207337357312 }, { target := 109, numerator := 45583309066290176488950988800 }, { target := 111, numerator := 12479963077578968906166435840 }, { target := 120, numerator := 18684020115511099888144220160 }, { target := 123, numerator := 68243725665463220079427584000 }, { target := 125, numerator := 18684013820559684734759731200 }, { target := 140, numerator := 670708414402962560087228416 }, { target := 143, numerator := 2449774767478166874646118400 }, { target := 145, numerator := 670708188430347657145221120 }, { target := 177, numerator := 18707973987454062836718764032 }, { target := 180, numerator := 68331217621444583182093516800 }, { target := 182, numerator := 18707967684432197151086346240 }, { target := 191, numerator := 18707973987454062836718764032 }, { target := 194, numerator := 68331217621444583182093516800 }, { target := 196, numerator := 18707967684432197151086346240 }, { target := 211, numerator := 13390214416116288253170024448 }, { target := 214, numerator := 48908003393581974390256435200 }, { target := 216, numerator := 13390209904734440726577807360 }, { target := 238, numerator := 694662286345925508661772288 }, { target := 241, numerator := 2537266723459529977312051200 }, { target := 243, numerator := 694662052302860073471836160 }]

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
    Slot7.Left0.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 290822217481044230840254464 }, { target := 1, numerator := 22396994191897044097966276608 }, { target := 2, numerator := 3056164471985782553657212928 }, { target := 3, numerator := 196138717553476532739552313344 }, { target := 4, numerator := 1934281311383406679529881600 }, { target := 5, numerator := 116056878683004400771792896 }, { target := 6, numerator := 3056164471985782553657212928 }, { target := 7, numerator := 3036821658871948486861914112 }, { target := 8, numerator := 1934281311383406679529881600 }, { target := 9, numerator := 46867636174819943845009031168 }, { target := 10, numerator := 2998136032644280353271316480 }, { target := 11, numerator := 22397008358996492706901917696 }, { target := 12, numerator := 3056164471985782553657212928 }, { target := 13, numerator := 116056878683004400771792896 }, { target := 14, numerator := 2998136032644280353271316480 }, { target := 15, numerator := 116056878683004400771792896 }, { target := 16, numerator := 3056164471985782553657212928 }, { target := 17, numerator := 3056164471985782553657212928 }, { target := 18, numerator := 290822217481044230840254464 }, { target := 19, numerator := 1179752939498100098659778560 }, { target := 21, numerator := 46016716684513965363282575360 }, { target := 24, numerator := 46016699805743137919042846720 }, { target := 31, numerator := 1179758565755042580073021440 }, { target := 45, numerator := 1295794212235618141150904320 }, { target := 47, numerator := 50542951112498945562949713920 }, { target := 50, numerator := 50542932573521151484850339840 }, { target := 57, numerator := 1295800391894882833850695680 }, { target := 90, numerator := 1179752939498100098659778560 }, { target := 92, numerator := 46016716684513965363282575360 }, { target := 95, numerator := 46016699805743137919042846720 }, { target := 102, numerator := 1179758565755042580073021440 }, { target := 161, numerator := 1295794212235618141150904320 }, { target := 163, numerator := 50542951112498945562949713920 }, { target := 166, numerator := 50542932573521151484850339840 }, { target := 173, numerator := 1295800391894882833850695680 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent0
