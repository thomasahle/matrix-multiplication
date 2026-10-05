import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk8Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 57362125511562703876915200 }, { target := 82, numerator := 2643187006247995858065817600 }, { target := 85, numerator := 2643182821158415258930380800 }, { target := 92, numerator := 57356652702111151161344000 }, { target := 131, numerator := 115589704563709660723412992 }, { target := 134, numerator := 416408807060545891521789952 }, { target := 136, numerator := 115570159438693156618502144 }, { target := 176, numerator := 2046240137652878107371110400 }, { target := 178, numerator := 94288614574035728529044275200 }, { target := 181, numerator := 94288465282178024117737881600 }, { target := 188, numerator := 2046044909838956954124288000 }, { target := 227, numerator := 3994318234113136021047607296 }, { target := 230, numerator := 14378780906592037648937779200 }, { target := 232, numerator := 3993634126769641741451526144 }, { target := 286, numerator := 2046240137652878107371110400 }, { target := 288, numerator := 94288614574035728529044275200 }, { target := 291, numerator := 94288465282178024117737881600 }, { target := 298, numerator := 2046044909838956954124288000 }, { target := 302, numerator := 48365200744588574147259400192 }, { target := 305, numerator := 174146461974409240683395153920 }, { target := 307, numerator := 48356950767317989302361653248 }, { target := 573, numerator := 57361122436076698714767360 }, { target := 575, numerator := 2643140785574210673762631680 }, { target := 578, numerator := 2643136600557813568571965440 }, { target := 585, numerator := 57355649722326638080819200 }, { target := 589, numerator := 3994390833565362940436021248 }, { target := 592, numerator := 14379037125465073129325854720 }, { target := 594, numerator := 3993706709595423261518200832 }, { target := 763, numerator := 118164700213820340312211456 }, { target := 766, numerator := 426290048898715225899925504 }, { target := 768, numerator := 118145214465387223366762496 }]

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
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 55398505485657503321554944 }, { target := 27, numerator := 467424890035235184275619840 }, { target := 28, numerator := 470887296628088778233217024 }, { target := 29, numerator := 58860912078511097279152128 }, { target := 30, numerator := 401639164771016899081273344 }, { target := 31, numerator := 58860912078511097279152128 }, { target := 32, numerator := 467424890035235184275619840 }, { target := 33, numerator := 467424890035235184275619840 }, { target := 34, numerator := 401639164771016899081273344 }, { target := 35, numerator := 8486358559084158790070697984 }, { target := 36, numerator := 401639164771016899081273344 }, { target := 37, numerator := 467424890035235184275619840 }, { target := 38, numerator := 467424890035235184275619840 }, { target := 39, numerator := 58860912078511097279152128 }, { target := 40, numerator := 401639164771016899081273344 }, { target := 41, numerator := 58860912078511097279152128 }, { target := 42, numerator := 467424890035235184275619840 }, { target := 43, numerator := 467424890035235184275619840 }, { target := 44, numerator := 55398505485657503321554944 }, { target := 131, numerator := 55398505485657503321554944 }, { target := 134, numerator := 198687906616309693533913088 }, { target := 136, numerator := 55398597719377871869313024 }, { target := 157, numerator := 198687906616309693533913088 }, { target := 158, numerator := 1676429212075113039192391680 }, { target := 159, numerator := 1688847206238632395038261248 }, { target := 160, numerator := 211105900779829049379782656 }, { target := 161, numerator := 1440487322968245278120869888 }, { target := 162, numerator := 211105900779829049379782656 }, { target := 163, numerator := 1676429212075113039192391680 }, { target := 164, numerator := 1676429212075113039192391680 }, { target := 165, numerator := 1440487322968245278120869888 }, { target := 166, numerator := 30436503694785941178226311168 }, { target := 167, numerator := 1440487322968245278120869888 }, { target := 168, numerator := 1676429212075113039192391680 }, { target := 169, numerator := 1676429212075113039192391680 }, { target := 170, numerator := 211105900779829049379782656 }, { target := 171, numerator := 1440487322968245278120869888 }, { target := 172, numerator := 211105900779829049379782656 }, { target := 173, numerator := 1676429212075113039192391680 }, { target := 174, numerator := 1676429212075113039192391680 }, { target := 175, numerator := 198687906616309693533913088 }, { target := 227, numerator := 467424890035235184275619840 }, { target := 230, numerator := 1676429212075113039192391680 }, { target := 232, numerator := 467425668257250793897328640 }, { target := 267, numerator := 55398597719377871869313024 }, { target := 268, numerator := 467425668257250793897328640 }, { target := 269, numerator := 470888080614711910889160704 }, { target := 270, numerator := 58861010076838988861145088 }, { target := 271, numerator := 401639833465489571052519424 }, { target := 272, numerator := 58861010076838988861145088 }, { target := 273, numerator := 467425668257250793897328640 }, { target := 274, numerator := 467425668257250793897328640 }, { target := 275, numerator := 401639833465489571052519424 }, { target := 276, numerator := 8486372688137197746980388864 }, { target := 277, numerator := 401639833465489571052519424 }, { target := 278, numerator := 467425668257250793897328640 }, { target := 279, numerator := 467425668257250793897328640 }, { target := 280, numerator := 58861010076838988861145088 }, { target := 281, numerator := 401639833465489571052519424 }, { target := 282, numerator := 58861010076838988861145088 }, { target := 283, numerator := 467425668257250793897328640 }, { target := 284, numerator := 467425668257250793897328640 }, { target := 285, numerator := 55398597719377871869313024 }]

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
    Slot13.Left16.expected,
    Slot13.Left17.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 57362125511562703876915200 }, { target := 82, numerator := 2046240137652878107371110400 }, { target := 85, numerator := 2046240137652878107371110400 }, { target := 92, numerator := 57361122436076698714767360 }, { target := 176, numerator := 2643187006247995858065817600 }, { target := 178, numerator := 94288614574035728529044275200 }, { target := 181, numerator := 94288614574035728529044275200 }, { target := 188, numerator := 2643140785574210673762631680 }, { target := 253, numerator := 470887296628088778233217024 }, { target := 256, numerator := 1688847206238632395038261248 }, { target := 258, numerator := 470888080614711910889160704 }, { target := 286, numerator := 2643182821158415258930380800 }, { target := 288, numerator := 94288465282178024117737881600 }, { target := 291, numerator := 94288465282178024117737881600 }, { target := 298, numerator := 2643136600557813568571965440 }, { target := 302, numerator := 58860912078511097279152128 }, { target := 305, numerator := 211105900779829049379782656 }, { target := 307, numerator := 58861010076838988861145088 }, { target := 328, numerator := 401639164771016899081273344 }, { target := 331, numerator := 1440487322968245278120869888 }, { target := 333, numerator := 401639833465489571052519424 }, { target := 342, numerator := 58860912078511097279152128 }, { target := 345, numerator := 211105900779829049379782656 }, { target := 347, numerator := 58861010076838988861145088 }, { target := 443, numerator := 467424890035235184275619840 }, { target := 446, numerator := 1676429212075113039192391680 }, { target := 448, numerator := 467425668257250793897328640 }, { target := 469, numerator := 467424890035235184275619840 }, { target := 472, numerator := 1676429212075113039192391680 }, { target := 474, numerator := 467425668257250793897328640 }, { target := 518, numerator := 401639164771016899081273344 }, { target := 521, numerator := 1440487322968245278120869888 }, { target := 523, numerator := 401639833465489571052519424 }, { target := 544, numerator := 8486358559084158790070697984 }, { target := 547, numerator := 30436503694785941178226311168 }, { target := 549, numerator := 8486372688137197746980388864 }, { target := 558, numerator := 401639164771016899081273344 }, { target := 561, numerator := 1440487322968245278120869888 }, { target := 563, numerator := 401639833465489571052519424 }, { target := 589, numerator := 467424890035235184275619840 }, { target := 592, numerator := 1676429212075113039192391680 }, { target := 594, numerator := 467425668257250793897328640 }, { target := 603, numerator := 467424890035235184275619840 }, { target := 606, numerator := 1676429212075113039192391680 }, { target := 608, numerator := 467425668257250793897328640 }, { target := 658, numerator := 58860912078511097279152128 }, { target := 661, numerator := 211105900779829049379782656 }, { target := 663, numerator := 58861010076838988861145088 }, { target := 684, numerator := 401639164771016899081273344 }, { target := 687, numerator := 1440487322968245278120869888 }, { target := 689, numerator := 401639833465489571052519424 }, { target := 698, numerator := 58860912078511097279152128 }, { target := 701, numerator := 211105900779829049379782656 }, { target := 703, numerator := 58861010076838988861145088 }, { target := 729, numerator := 467424890035235184275619840 }, { target := 732, numerator := 1676429212075113039192391680 }, { target := 734, numerator := 467425668257250793897328640 }, { target := 743, numerator := 467424890035235184275619840 }, { target := 746, numerator := 1676429212075113039192391680 }, { target := 748, numerator := 467425668257250793897328640 }, { target := 763, numerator := 55398505485657503321554944 }, { target := 766, numerator := 198687906616309693533913088 }, { target := 768, numerator := 55398597719377871869313024 }]

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
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 115589704563709660723412992 }, { target := 27, numerator := 3994318234113136021047607296 }, { target := 29, numerator := 48365200744588574147259400192 }, { target := 37, numerator := 3994390833565362940436021248 }, { target := 44, numerator := 118164700213820340312211456 }, { target := 157, numerator := 416408807060545891521789952 }, { target := 158, numerator := 14378780906592037648937779200 }, { target := 160, numerator := 174146461974409240683395153920 }, { target := 168, numerator := 14379037125465073129325854720 }, { target := 175, numerator := 426290048898715225899925504 }, { target := 267, numerator := 115570159438693156618502144 }, { target := 268, numerator := 3993634126769641741451526144 }, { target := 270, numerator := 48356950767317989302361653248 }, { target := 278, numerator := 3993706709595423261518200832 }, { target := 285, numerator := 118145214465387223366762496 }, { target := 573, numerator := 57356652702111151161344000 }, { target := 575, numerator := 2046044909838956954124288000 }, { target := 578, numerator := 2046044909838956954124288000 }, { target := 585, numerator := 57355649722326638080819200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8.Parent2
