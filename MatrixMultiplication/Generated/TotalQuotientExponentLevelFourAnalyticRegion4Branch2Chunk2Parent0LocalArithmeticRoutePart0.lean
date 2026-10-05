import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 163333467955379489803862016 }, { target := 134, numerator := 576963861760474774870425600 }, { target := 136, numerator := 163464445409255566677639168 }, { target := 227, numerator := 3605151772193580260675026944 }, { target := 230, numerator := 12656110700702735218298060800 }, { target := 232, numerator := 3609208982267673993923264512 }, { target := 253, numerator := 474349703220942372190814208 }, { target := 256, numerator := 1701265200402151750884130816 }, { target := 258, numerator := 474350492972173027880992768 }, { target := 302, numerator := 65785725264218285194346496 }, { target := 305, numerator := 235941889106867761071521792 }, { target := 307, numerator := 65785834791761222844809216 }, { target := 328, numerator := 422413604328138462826856448 }, { target := 331, numerator := 1514995287949361413196087296 }, { target := 333, numerator := 422414307610256273003511808 }, { target := 342, numerator := 65785725264218285194346496 }, { target := 345, numerator := 235941889106867761071521792 }, { target := 347, numerator := 65785834791761222844809216 }, { target := 443, numerator := 470887296628088778233217024 }, { target := 446, numerator := 1688847206238632395038261248 }, { target := 448, numerator := 470888080614711910889160704 }, { target := 469, numerator := 470887296628088778233217024 }, { target := 472, numerator := 1688847206238632395038261248 }, { target := 474, numerator := 470888080614711910889160704 }, { target := 518, numerator := 422413604328138462826856448 }, { target := 521, numerator := 1514995287949361413196087296 }, { target := 523, numerator := 422414307610256273003511808 }, { target := 544, numerator := 8327087855812893468021227520 }, { target := 547, numerator := 29865275963264050809316311040 }, { target := 549, numerator := 8327101719693986365356113920 }, { target := 558, numerator := 422413604328138462826856448 }, { target := 561, numerator := 1514995287949361413196087296 }, { target := 563, numerator := 422414307610256273003511808 }, { target := 589, numerator := 474349703220942372190814208 }, { target := 592, numerator := 1701265200402151750884130816 }, { target := 594, numerator := 474350492972173027880992768 }, { target := 603, numerator := 470887296628088778233217024 }, { target := 606, numerator := 1688847206238632395038261248 }, { target := 608, numerator := 470888080614711910889160704 }, { target := 658, numerator := 65785725264218285194346496 }, { target := 661, numerator := 235941889106867761071521792 }, { target := 663, numerator := 65785834791761222844809216 }, { target := 684, numerator := 422413604328138462826856448 }, { target := 687, numerator := 1514995287949361413196087296 }, { target := 689, numerator := 422414307610256273003511808 }, { target := 698, numerator := 65785725264218285194346496 }, { target := 701, numerator := 235941889106867761071521792 }, { target := 703, numerator := 65785834791761222844809216 }, { target := 729, numerator := 474349703220942372190814208 }, { target := 732, numerator := 1701265200402151750884130816 }, { target := 734, numerator := 474350492972173027880992768 }, { target := 743, numerator := 470887296628088778233217024 }, { target := 746, numerator := 1688847206238632395038261248 }, { target := 748, numerator := 470888080614711910889160704 }, { target := 763, numerator := 58860912078511097279152128 }, { target := 766, numerator := 211105900779829049379782656 }, { target := 768, numerator := 58861010076838988861145088 }]

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
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 29906858741251912331427840 }, { target := 27, numerator := 997575695313727370066657280 }, { target := 29, numerator := 12217381054392972422267535360 }, { target := 37, numerator := 997576546173175469640253440 }, { target := 44, numerator := 32612591786208556367216640 }, { target := 80, numerator := 110821813153524564885504000 }, { target := 82, numerator := 4638919335618788011047649280 }, { target := 85, numerator := 4638922453687397395894108160 }, { target := 92, numerator := 110825202648453991817543680 }, { target := 131, numerator := 29906858741251912331427840 }, { target := 134, numerator := 106145307171030229856550912 }, { target := 136, numerator := 29934293594103017428221952 }, { target := 157, numerator := 106145307171030229856550912 }, { target := 158, numerator := 3540591792723903538689736704 }, { target := 160, numerator := 43361881502295883456444366848 }, { target := 168, numerator := 3540594812590960098769108992 }, { target := 175, numerator := 115748484410891282260426752 }, { target := 176, numerator := 4638919335618788011047649280 }, { target := 178, numerator := 188681486071191998559871303680 }, { target := 181, numerator := 188681624624012322148114759680 }, { target := 188, numerator := 4639034005233857454554480640 }, { target := 227, numerator := 997575695313727370066657280 }, { target := 230, numerator := 3540591792723903538689736704 }, { target := 232, numerator := 998490814572675838072848384 }, { target := 267, numerator := 29934293594103017428221952 }, { target := 268, numerator := 998490814572675838072848384 }, { target := 270, numerator := 12228588585560089560516395008 }, { target := 278, numerator := 998491666212654048065093632 }, { target := 285, numerator := 32642508724810792768110592 }, { target := 286, numerator := 2709828498479065941934080000 }, { target := 288, numerator := 94340777464400586002871091200 }, { target := 291, numerator := 94340881588454321990035046400 }, { target := 298, numerator := 2709816929139761943360307200 }, { target := 302, numerator := 48966334800506376040432533504 }, { target := 305, numerator := 171948455075907218074012483584 }, { target := 307, numerator := 49025156073946445678362230784 }, { target := 573, numerator := 55414532642965385379840000 }, { target := 575, numerator := 1929218065017019687344537600 }, { target := 578, numerator := 1929220194297812884861747200 }, { target := 585, numerator := 55414296056210585655705600 }, { target := 589, numerator := 4128401796198508774224297984 }, { target := 592, numerator := 14495521424646684299470307328 }, { target := 594, numerator := 4133373366595356345141035008 }, { target := 763, numerator := 133635619432831919434235904 }, { target := 766, numerator := 469233513314206948175904768 }, { target := 768, numerator := 133796426748211437500366848 }]

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
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 163333467955379489803862016 }, { target := 27, numerator := 3605151772193580260675026944 }, { target := 28, numerator := 474349703220942372190814208 }, { target := 29, numerator := 36814739471377621903359344640 }, { target := 30, numerator := 422413604328138462826856448 }, { target := 31, numerator := 65785725264218285194346496 }, { target := 32, numerator := 470887296628088778233217024 }, { target := 33, numerator := 470887296628088778233217024 }, { target := 34, numerator := 422413604328138462826856448 }, { target := 35, numerator := 8327087855812893468021227520 }, { target := 36, numerator := 422413604328138462826856448 }, { target := 37, numerator := 3605174953246275676774858752 }, { target := 38, numerator := 470887296628088778233217024 }, { target := 39, numerator := 65785725264218285194346496 }, { target := 40, numerator := 422413604328138462826856448 }, { target := 41, numerator := 65785725264218285194346496 }, { target := 42, numerator := 474349703220942372190814208 }, { target := 43, numerator := 470887296628088778233217024 }, { target := 44, numerator := 159883939725134460346171392 }, { target := 157, numerator := 576963861760474774870425600 }, { target := 158, numerator := 12656110700702735218298060800 }, { target := 159, numerator := 1701265200402151750884130816 }, { target := 160, numerator := 128822515462718202378639638528 }, { target := 161, numerator := 1514995287949361413196087296 }, { target := 162, numerator := 235941889106867761071521792 }, { target := 163, numerator := 1688847206238632395038261248 }, { target := 164, numerator := 1688847206238632395038261248 }, { target := 165, numerator := 1514995287949361413196087296 }, { target := 166, numerator := 29865275963264050809316311040 }, { target := 167, numerator := 1514995287949361413196087296 }, { target := 168, numerator := 12656191812457875951585329152 }, { target := 169, numerator := 1688847206238632395038261248 }, { target := 170, numerator := 235941889106867761071521792 }, { target := 171, numerator := 1514995287949361413196087296 }, { target := 172, numerator := 235941889106867761071521792 }, { target := 173, numerator := 1701265200402151750884130816 }, { target := 174, numerator := 1688847206238632395038261248 }, { target := 175, numerator := 564590929683144715295260672 }, { target := 267, numerator := 101141022974955460824662016 }, { target := 268, numerator := 3134858489295500966042271744 }, { target := 270, numerator := 36796567488386356117845835776 }, { target := 278, numerator := 3134881700382702297075941376 }, { target := 285, numerator := 101153918023400644732256256 }, { target := 286, numerator := 1929093955208331453960028160 }, { target := 288, numerator := 94340847159611736145243668480 }, { target := 291, numerator := 94340881588454321990035046400 }, { target := 298, numerator := 1929220194297812884861747200 }, { target := 573, numerator := 55410670005488606437703680 }, { target := 575, numerator := 2709815940216837767209943040 }, { target := 578, numerator := 2709816929139761943360307200 }, { target := 585, numerator := 55414296056210585655705600 }]

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
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 267, numerator := 62323422434300105852977152 }, { target := 268, numerator := 474350492972173027880992768 }, { target := 269, numerator := 474350492972173027880992768 }, { target := 270, numerator := 65785834791761222844809216 }, { target := 271, numerator := 422414307610256273003511808 }, { target := 272, numerator := 65785834791761222844809216 }, { target := 273, numerator := 470888080614711910889160704 }, { target := 274, numerator := 470888080614711910889160704 }, { target := 275, numerator := 422414307610256273003511808 }, { target := 276, numerator := 8327101719693986365356113920 }, { target := 277, numerator := 422414307610256273003511808 }, { target := 278, numerator := 474350492972173027880992768 }, { target := 279, numerator := 470888080614711910889160704 }, { target := 280, numerator := 65785834791761222844809216 }, { target := 281, numerator := 422414307610256273003511808 }, { target := 282, numerator := 65785834791761222844809216 }, { target := 283, numerator := 474350492972173027880992768 }, { target := 284, numerator := 470888080614711910889160704 }, { target := 285, numerator := 58861010076838988861145088 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent0
