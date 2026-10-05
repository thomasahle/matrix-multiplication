import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 2754705157749798254673920 }, { target := 35, numerator := 148922562730873509512216576 }, { target := 40, numerator := 148963160111366242188656640 }, { target := 48, numerator := 2714950126590719281856512 }, { target := 79, numerator := 108946498248257715887407104 }, { target := 80, numerator := 5959861019319420008494268416 }, { target := 85, numerator := 5961540114213443124020117504 }, { target := 93, numerator := 107295931348653283519496192 }, { target := 121, numerator := 1025988338083769266208768 }, { target := 122, numerator := 50399738830756110885978112 }, { target := 124, numerator := 562497005848980950177808384 }, { target := 132, numerator := 50399818146463898274889728 }, { target := 139, numerator := 1025829706668194488385536 }, { target := 154, numerator := 1197884086117759100710289408 }, { target := 155, numerator := 65589155380202530400058212352 }, { target := 160, numerator := 65607679729629760330932420608 }, { target := 168, numerator := 1179669340830193858457370624 }, { target := 196, numerator := 60060183301076526395555840 }, { target := 197, numerator := 2950343040112068286543298560 }, { target := 199, numerator := 32927931072485701330057297920 }, { target := 207, numerator := 2950347683162843368799600640 }, { target := 214, numerator := 60050897199526361882951680 }, { target := 492, numerator := 108946487449188759406379008 }, { target := 493, numerator := 5959861030140444013158727680 }, { target := 498, numerator := 5961540125498900840257159168 }, { target := 506, numerator := 107295920041240519099023360 }, { target := 508, numerator := 60080121524193880417763328 }, { target := 509, numerator := 2951322467655797288208433152 }, { target := 511, numerator := 32938862181923462679745265664 }, { target := 519, numerator := 2951327112247929342932287488 }, { target := 526, numerator := 60070832339929770970054656 }, { target := 890, numerator := 2754141009838876062121984 }, { target := 891, numerator := 148892431595443495836319744 }, { target := 896, numerator := 148933021047067609550290944 }, { target := 904, numerator := 2714393709952982400892928 }, { target := 906, numerator := 1006050114966415244001280 }, { target := 907, numerator := 49420311287027109220843520 }, { target := 909, numerator := 551565896411219600489840640 }, { target := 917, numerator := 49420389061377924142202880 }, { target := 924, numerator := 1005894566264785401282560 }]

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
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 1728716819666028988465152 }, { target := 122, numerator := 58546759417501605001428992 }, { target := 124, numerator := 635387080268778150532481024 }, { target := 132, numerator := 58546669302724861131489280 }, { target := 139, numerator := 1728311303170681573736448 }, { target := 196, numerator := 88862379429796983116660736 }, { target := 197, numerator := 3009517979207351721950969856 }, { target := 199, numerator := 32661224307716829070000914432 }, { target := 207, numerator := 3009513346977600644359127040 }, { target := 214, numerator := 88841534395917133953368064 }, { target := 508, numerator := 88883038587172361770893312 }, { target := 509, numerator := 3010217646557645835811684352 }, { target := 511, numerator := 32668817547706297651187154944 }, { target := 519, numerator := 3010213013250971497324871680 }, { target := 526, numerator := 88862188707137838580236288 }, { target := 906, numerator := 1708900011624304037855232 }, { target := 907, numerator := 57875620061626174298652672 }, { target := 909, numerator := 628103444418974257967529984 }, { target := 917, numerator := 57875530979862594956820480 }, { target := 924, numerator := 1708499143688196999610368 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2.Parent2
