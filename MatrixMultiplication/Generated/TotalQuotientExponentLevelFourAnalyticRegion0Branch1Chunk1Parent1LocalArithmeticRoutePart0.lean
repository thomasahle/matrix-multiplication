import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 83243638892355284732215296 }, { target := 27, numerator := 3722370703896121513489727488 }, { target := 29, numerator := 37286139165436683678054875136 }, { target := 37, numerator := 3722400201464311523754115072 }, { target := 44, numerator := 83235610613529947500707840 }, { target := 80, numerator := 44058944135585016393498624 }, { target := 82, numerator := 1602105175022075989110816768 }, { target := 85, numerator := 1602851414357325519658156032 }, { target := 92, numerator := 44806754087693793519206400 }, { target := 131, numerator := 60961793050861226201972736 }, { target := 134, numerator := 197159805518719145272672256 }, { target := 136, numerator := 60997038876818773486075904 }, { target := 157, numerator := 273286137594349136535093248 }, { target := 158, numerator := 12243541860592637761671921664 }, { target := 160, numerator := 122838811992334558416726917120 }, { target := 168, numerator := 12243638691209766510486618112 }, { target := 175, numerator := 273259695923983030151020544 }, { target := 176, numerator := 1545601055769275229064396800 }, { target := 178, numerator := 56202333000703464007375257600 }, { target := 181, numerator := 56228511301773704164697702400 }, { target := 188, numerator := 1571834454552896581140480000 }, { target := 227, numerator := 2599219028476778575936094208 }, { target := 230, numerator := 8406273708640465927188512768 }, { target := 232, numerator := 2600721799588297636642291712 }, { target := 267, numerator := 83278381162394246419841024 }, { target := 268, numerator := 3723848092475257484342198272 }, { target := 270, numerator := 37300285418999950959982936064 }, { target := 278, numerator := 3723877602383873423555166208 }, { target := 285, numerator := 83270349813239863228497920 }, { target := 286, numerator := 1545595939202716975679668224 }, { target := 288, numerator := 56202146948179461237236563968 }, { target := 291, numerator := 56228325162588904089905528832 }, { target := 298, numerator := 1571829251143145238193766400 }, { target := 302, numerator := 24949811824017655173287510016 }, { target := 305, numerator := 80691524982670545301469659136 }, { target := 307, numerator := 24964236870939900489261645824 }, { target := 573, numerator := 44067850751445679692840960 }, { target := 575, numerator := 1602429044230525255648542720 }, { target := 578, numerator := 1603175434419755279481569280 }, { target := 585, numerator := 44815811875038723833856000 }, { target := 589, numerator := 2599240679403634570215555072 }, { target := 592, numerator := 8406343731064587645838426112 }, { target := 594, numerator := 2600743463032908795198046208 }, { target := 763, numerator := 60956380319147227632107520 }, { target := 766, numerator := 197142299912688715610193920 }, { target := 768, numerator := 60991623015665983847137280 }]

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
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 44058944135585016393498624 }, { target := 82, numerator := 1545601055769275229064396800 }, { target := 85, numerator := 1545595939202716975679668224 }, { target := 92, numerator := 44067850751445679692840960 }, { target := 131, numerator := 22281845841494058530242560 }, { target := 134, numerator := 76126332075629991262420992 }, { target := 136, numerator := 22281342285575472933765120 }, { target := 176, numerator := 1602105175022075989110816768 }, { target := 178, numerator := 56202333000703464007375257600 }, { target := 181, numerator := 56202146948179461237236563968 }, { target := 188, numerator := 1602429044230525255648542720 }, { target := 227, numerator := 1123151675419342937553633280 }, { target := 230, numerator := 3837268151952171834483408896 }, { target := 232, numerator := 1123126292886959847699906560 }, { target := 286, numerator := 1602851414357325519658156032 }, { target := 288, numerator := 56228511301773704164697702400 }, { target := 291, numerator := 56228325162588904089905528832 }, { target := 298, numerator := 1603175434419755279481569280 }, { target := 302, numerator := 12336327341419028504767365120 }, { target := 305, numerator := 42147287009664013115257257984 }, { target := 307, numerator := 12336048548060050470721290240 }, { target := 573, numerator := 44806754087693793519206400 }, { target := 575, numerator := 1571834454552896581140480000 }, { target := 578, numerator := 1571829251143145238193766400 }, { target := 585, numerator := 44815811875038723833856000 }, { target := 589, numerator := 1123159522060676953538560000 }, { target := 592, numerator := 3837294960145178864648192000 }, { target := 594, numerator := 1123134139350964628357120000 }, { target := 763, numerator := 22279230294382719868600320 }, { target := 766, numerator := 76117396011294314540826624 }, { target := 768, numerator := 22278726797573879381360640 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent1
