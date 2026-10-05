import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk18Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent0

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
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1856910058928070412348686336 }, { target := 1, numerator := 2205080694977083614664065024 }, { target := 2, numerator := 1682824740903563811190996992 }, { target := 3, numerator := 17350503363109157915383037952 }, { target := 4, numerator := 2089023816294079213892272128 }, { target := 5, numerator := 1682824740903563811190996992 }, { target := 6, numerator := 2089023816294079213892272128 }, { target := 7, numerator := 2089023816294079213892272128 }, { target := 8, numerator := 89479853464596392995052322816 }, { target := 9, numerator := 2089023816294079213892272128 }, { target := 10, numerator := 17350503363109157915383037952 }, { target := 11, numerator := 89479853464596392995052322816 }, { target := 12, numerator := 1856910058928070412348686336 }, { target := 13, numerator := 2089023816294079213892272128 }, { target := 14, numerator := 2089023816294079213892272128 }, { target := 15, numerator := 2205080694977083614664065024 }, { target := 16, numerator := 788384640957199411616661110784 }, { target := 19, numerator := 2820393999718611712473676382208 }, { target := 21, numerator := 788384378865859612351351750656 }, { target := 26, numerator := 54938401831799336539816722432000 }, { target := 28, numerator := 54938378925889770679272273346560 }, { target := 44, numerator := 2754801894736041411742827282432 }, { target := 49, numerator := 909112216350201139379044352 }, { target := 50, numerator := 788384640957199411616661110784 }, { target := 53, numerator := 2820393999718611712473676382208 }, { target := 55, numerator := 788384378865859612351351750656 }, { target := 60, numerator := 23395189679735793478970149699584 }, { target := 62, numerator := 23395189679735793478970149699584 }, { target := 64, numerator := 101629946205806171811600280846336 }, { target := 69, numerator := 22495691651389019682932523008 }, { target := 70, numerator := 715684085211860471426056192 }, { target := 71, numerator := 6901216299730331924142665760768 }, { target := 73, numerator := 6901216299730331924142665760768 }, { target := 75, numerator := 101625971904675487064015241216000 }, { target := 76, numerator := 735026898325694538221355008 }, { target := 91, numerator := 735026898325694538221355008 }, { target := 96, numerator := 12437428832195304949377138688 }, { target := 97, numerator := 676998458984192337835458560 }, { target := 102, numerator := 22495691651389019682932523008 }, { target := 103, numerator := 12437428832195304949377138688 }, { target := 104, numerator := 2758776498098181062985160589312 }, { target := 109, numerator := 715684085211860471426056192 }, { target := 110, numerator := 676998458984192337835458560 }, { target := 111, numerator := 909112216350201139379044352 }]

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
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected,
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1593093336421157917934701510656 }, { target := 2, numerator := 59729504449619439379468316049408 }, { target := 5, numerator := 59725536528405872988773960122368 }, { target := 12, numerator := 1597061257634724308629057437696 }, { target := 16, numerator := 75997814042022114012410320781312 }, { target := 19, numerator := 264863411423887220726059868618752 }, { target := 21, numerator := 75997814042022114012410320781312 }, { target := 26, numerator := 21658918517241726226751201214464 }, { target := 28, numerator := 21658918517241726226751201214464 }, { target := 44, numerator := 202388689313324299395910336512 }, { target := 49, numerator := 2205080694977083614664065024 }, { target := 50, numerator := 75997791056143525684532459077632 }, { target := 53, numerator := 264863332517385124376917561049088 }, { target := 55, numerator := 75997791056143525684532459077632 }, { target := 60, numerator := 243636406091276978639501051035648 }, { target := 62, numerator := 243636327459294553779699277889536 }, { target := 64, numerator := 7407054646855883743807848579072 }, { target := 69, numerator := 17350503363109157915383037952 }, { target := 70, numerator := 2089023816294079213892272128 }, { target := 71, numerator := 69696103777774658077420658098176 }, { target := 73, numerator := 69696080871865092216876209012736 }, { target := 75, numerator := 7407052833467154321864086519808 }, { target := 76, numerator := 2089023816294079213892272128 }, { target := 91, numerator := 2089023816294079213892272128 }, { target := 96, numerator := 89479853464596392995052322816 }, { target := 97, numerator := 2089023816294079213892272128 }, { target := 102, numerator := 17350503363109157915383037952 }, { target := 103, numerator := 89479853464596392995052322816 }, { target := 104, numerator := 202390502702053721339672395776 }, { target := 109, numerator := 2089023816294079213892272128 }, { target := 110, numerator := 2089023816294079213892272128 }, { target := 111, numerator := 2205080694977083614664065024 }]

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
    Slot20.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1364793121386024015513790709760 }, { target := 1, numerator := 909112216350201139379044352 }, { target := 2, numerator := 49382488952276866174130417827840 }, { target := 3, numerator := 22495691651389019682932523008 }, { target := 4, numerator := 715684085211860471426056192 }, { target := 5, numerator := 49382507256169353776875266113536 }, { target := 6, numerator := 735026898325694538221355008 }, { target := 7, numerator := 735026898325694538221355008 }, { target := 8, numerator := 12437428832195304949377138688 }, { target := 9, numerator := 676998458984192337835458560 }, { target := 10, numerator := 22495691651389019682932523008 }, { target := 11, numerator := 12437428832195304949377138688 }, { target := 12, numerator := 1364775129169724282165526528000 }, { target := 13, numerator := 715684085211860471426056192 }, { target := 14, numerator := 676998458984192337835458560 }, { target := 15, numerator := 909112216350201139379044352 }, { target := 16, numerator := 65791159813372980581074206720 }, { target := 19, numerator := 224944432938092730922202824704 }, { target := 21, numerator := 65791138562723807667670745088 }, { target := 50, numerator := 65791159813372980581074206720 }, { target := 53, numerator := 224944432938092730922202824704 }, { target := 55, numerator := 65791138562723807667670745088 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18.Parent0
