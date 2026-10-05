import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk8Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 36; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent2

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 9243012359057030662443761664 }, { target := 2, numerator := 347283718955132488508504014848 }, { target := 5, numerator := 347257453152754767541825437696 }, { target := 12, numerator := 9269278161434751629122338816 }, { target := 16, numerator := 51091165380173221668585472000 }, { target := 19, numerator := 175387037423172415175367065600 }, { target := 21, numerator := 51091165380173221668585472000 }, { target := 26, numerator := 790878383386991626599480164352 }, { target := 28, numerator := 790878383386991626599480164352 }, { target := 30, numerator := 50742250104406185032800010240 }, { target := 33, numerator := 174189272289550749900998705152 }, { target := 35, numerator := 50742250104406185032800010240 }, { target := 40, numerator := 213157800514451416084192952320 }, { target := 42, numerator := 213157800514451416084192952320 }, { target := 44, numerator := 51239093049080511462165708800 }, { target := 45, numerator := 8694594494668413024486817792 }, { target := 47, numerator := 8694594494668413024486817792 }, { target := 49, numerator := 20000468759704425066338975744 }, { target := 50, numerator := 51091165380173221668585472000 }, { target := 53, numerator := 175387037423172415175367065600 }, { target := 55, numerator := 51091165380173221668585472000 }, { target := 60, numerator := 2852999262701030825585411096576 }, { target := 62, numerator := 2852999262701030825585411096576 }, { target := 64, numerator := 1094126110447228399404592398336 }, { target := 65, numerator := 175574714634271824300927352832 }, { target := 67, numerator := 175574714634271824300927352832 }, { target := 69, numerator := 494905216330558433024515506176 }, { target := 70, numerator := 15745049874660930371373236224 }, { target := 71, numerator := 790878130740384793073461231616 }, { target := 73, numerator := 790878130740384793073461231616 }, { target := 75, numerator := 1094126639352274480804856332288 }, { target := 76, numerator := 16170591763165279840869810176 }, { target := 77, numerator := 51240700498359094512493527040 }, { target := 80, numerator := 175900365337581700292953505792 }, { target := 82, numerator := 51240700498359094512493527040 }, { target := 87, numerator := 175855185424422418269459185664 }, { target := 89, numerator := 175855185424422418269459185664 }, { target := 91, numerator := 16170591763165279840869810176 }, { target := 92, numerator := 157624584064633810314890051584 }, { target := 94, numerator := 157624584064633810314890051584 }, { target := 96, numerator := 273623434308296708886297051136 }, { target := 97, numerator := 14893966097652231432380088320 }, { target := 98, numerator := 213157800514451416084192952320 }, { target := 100, numerator := 213157800514451416084192952320 }, { target := 102, numerator := 494905216330558433024515506176 }, { target := 103, numerator := 273623434308296708886297051136 }, { target := 104, numerator := 51238828596557470762033741824 }, { target := 105, numerator := 8694594494668413024486817792 }, { target := 107, numerator := 8694594494668413024486817792 }, { target := 109, numerator := 15745049874660930371373236224 }, { target := 110, numerator := 14893966097652231432380088320 }, { target := 111, numerator := 20000468759704425066338975744 }]

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
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 47869670396453570993257971712 }, { target := 2, numerator := 1695149767968733852844997738496 }, { target := 5, numerator := 1695150528269737594857877143552 }, { target := 12, numerator := 47869183992705835419800961024 }, { target := 16, numerator := 1231466204275157509331855867904 }, { target := 17, numerator := 205807531531194470701979402240 }, { target := 18, numerator := 8394780891403984989159686144 }, { target := 19, numerator := 4342400903082250593189505269760 }, { target := 20, numerator := 169520414129641761393998823424 }, { target := 21, numerator := 1231465939822634468631723900928 }, { target := 22, numerator := 169791213513235438329133006848 }, { target := 23, numerator := 152189253579646437545411084288 }, { target := 24, numerator := 205807531531194470701979402240 }, { target := 25, numerator := 8394780891403984989159686144 }, { target := 26, numerator := 455428155530840765446802636800 }, { target := 27, numerator := 50742250104406185032800010240 }, { target := 28, numerator := 455245323324599111021819330560 }, { target := 29, numerator := 51240700498359094512493527040 }, { target := 44, numerator := 24135391741571017894032048128 }, { target := 50, numerator := 1222888591177511869917712875520 }, { target := 53, numerator := 4169281943931581285492255096832 }, { target := 55, numerator := 1222888326724988829217580908544 }, { target := 60, numerator := 1545980234371096815874762342400 }, { target := 61, numerator := 174189272289550749900998705152 }, { target := 62, numerator := 1545360482569599715857987010560 }, { target := 63, numerator := 175900365337581700292953505792 }, { target := 64, numerator := 886988477172468864431723380736 }, { target := 71, numerator := 455428155530840765446802636800 }, { target := 72, numerator := 50742250104406185032800010240 }, { target := 73, numerator := 455245323324599111021819330560 }, { target := 74, numerator := 51240700498359094512493527040 }, { target := 75, numerator := 886962409709483423990143778816 }, { target := 104, numerator := 24161459204556458335611650048 }]

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
    Slot14.Left2.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 21354465677672809742009892864 }, { target := 1, numerator := 20909580976054626205718020096 }, { target := 2, numerator := 16460733959872790842799292416 }, { target := 3, numerator := 517400907981947452707448029184 }, { target := 4, numerator := 16460733959872790842799292416 }, { target := 5, numerator := 16460733959872790842799292416 }, { target := 6, numerator := 16905618661490974379091165184 }, { target := 7, numerator := 16905618661490974379091165184 }, { target := 8, numerator := 286060863140492013835674189824 }, { target := 9, numerator := 15570964556636423770215546880 }, { target := 10, numerator := 517400907981947452707448029184 }, { target := 11, numerator := 286060863140492013835674189824 }, { target := 12, numerator := 21354465677672809742009892864 }, { target := 13, numerator := 16460733959872790842799292416 }, { target := 14, numerator := 15570964556636423770215546880 }, { target := 15, numerator := 20909580976054626205718020096 }, { target := 50, numerator := 8394780891403984989159686144 }, { target := 51, numerator := 205807531531194470701979402240 }, { target := 52, numerator := 8394780891403984989159686144 }, { target := 53, numerator := 172499207349172207680474841088 }, { target := 54, numerator := 169520414129641761393998823424 }, { target := 55, numerator := 8394780891403984989159686144 }, { target := 56, numerator := 169791213513235438329133006848 }, { target := 57, numerator := 152189253579646437545411084288 }, { target := 58, numerator := 205807531531194470701979402240 }, { target := 59, numerator := 8394780891403984989159686144 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent2
