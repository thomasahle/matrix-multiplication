import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2183668977218087810771189760 }, { target := 21, numerator := 77042226785401147054851358720 }, { target := 24, numerator := 77069237392334548791271096320 }, { target := 31, numerator := 2154689174927980028734996480 }, { target := 35, numerator := 27962191724595893409241104384 }, { target := 38, numerator := 100149350098353845494414835712 }, { target := 40, numerator := 27974750249355215961453494272 }, { target := 71, numerator := 2525855033540941234902663168 }, { target := 73, numerator := 2526033460136864952159830016 }, { target := 90, numerator := 527145191694229118832869376 }, { target := 92, numerator := 19281220077101120505543393280 }, { target := 95, numerator := 19281236605655715376804134912 }, { target := 102, numerator := 525131069255739806631067648 }, { target := 106, numerator := 100192580667008580155420442624 }, { target := 109, numerator := 358823125260742938698052534272 }, { target := 111, numerator := 100237217509926510387162775552 }, { target := 116, numerator := 96507135664844857281190297600 }, { target := 118, numerator := 96513341909228571418370768896 }, { target := 140, numerator := 27977373859249145555472875520 }, { target := 143, numerator := 100203265720785223566795735040 }, { target := 145, numerator := 27989932566890360300969656320 }, { target := 150, numerator := 96534228913437999841023098880 }, { target := 152, numerator := 96540437816026358037365129216 }, { target := 232, numerator := 2496802034352205866414899200 }, { target := 234, numerator := 2496977739753889336293064704 }]

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
    Slot17.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 342186056322853424131473408 }, { target := 21, numerator := 19464908879443710226338938880 }, { target := 24, numerator := 19464991521103451049752002560 }, { target := 31, numerator := 342112859424225837679902720 }, { target := 35, numerator := 2593394212543121107288326144 }, { target := 38, numerator := 9170464972359935352775901184 }, { target := 40, numerator := 2593306069908416661584609280 }, { target := 90, numerator := 1998888268442635833326960640 }, { target := 92, numerator := 77232121832127450912827375616 }, { target := 95, numerator := 77259201210370642660560994304 }, { target := 102, numerator := 1971846670498149529661997056 }, { target := 106, numerator := 9127234403705200691770294272 }, { target := 109, numerator := 32274685810923681200096673792 }, { target := 111, numerator := 9126924193061552060513648640 }, { target := 140, numerator := 2590682460014487067565228032 }, { target := 143, numerator := 9160875982202838880880689152 }, { target := 145, numerator := 2590594409545104571068579840 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent0
