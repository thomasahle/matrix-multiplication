import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk6Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

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
    Slot9.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 115814003532060255867371520 }, { target := 27, numerator := 3450612454726159196875653120 }, { target := 29, numerator := 36756427824712657681986355200 }, { target := 37, numerator := 3460251190518276746473635840 }, { target := 44, numerator := 124348328109332949117173760 }, { target := 80, numerator := 190412107152524361481584640 }, { target := 82, numerator := 7002090758376284732644130816 }, { target := 85, numerator := 7001501918816124536310726656 }, { target := 92, numerator := 190408525072697344095420416 }, { target := 131, numerator := 66108029526121710989869056 }, { target := 134, numerator := 229764321720854828462112768 }, { target := 136, numerator := 66196209361122028727304192 }, { target := 157, numerator := 395292763292186636948865024 }, { target := 158, numerator := 11777523362289676078697938944 }, { target := 160, numerator := 125455898945401148733118218240 }, { target := 168, numerator := 11810421996217435177151889408 }, { target := 175, numerator := 424421855129933696427098112 }, { target := 176, numerator := 6605526072797209592594432000 }, { target := 178, numerator := 243677702662565303568314662912 }, { target := 181, numerator := 243656306928054363704547868672 }, { target := 188, numerator := 6605390451141044303741059072 }, { target := 227, numerator := 3332279769329755412892745728 }, { target := 230, numerator := 11581633978088028527325609984 }, { target := 232, numerator := 3336724613357639918992490496 }, { target := 267, numerator := 115829885075044336108830720 }, { target := 268, numerator := 3451085636278906104651448320 }, { target := 270, numerator := 36761468223720000698135347200 }, { target := 278, numerator := 3460725693828256166565642240 }, { target := 285, numerator := 124365379961938322506383360 }, { target := 286, numerator := 6606059046343965913603112960 }, { target := 288, numerator := 243703815891158586321522393088 }, { target := 291, numerator := 243682410319447646766333165568 }, { target := 298, numerator := 6605923318633940374685483008 }, { target := 302, numerator := 36600661270697856850420826112 }, { target := 305, numerator := 127208845456114237695156289536 }, { target := 307, numerator := 36649481970617181726660624384 }, { target := 573, numerator := 190956905327944308327710720 }, { target := 575, numerator := 7028626630701585586664243200 }, { target := 578, numerator := 7028027932695694456788090880 }, { target := 585, numerator := 190953217151472844417269760 }, { target := 589, numerator := 3332303049537359399878656000 }, { target := 592, numerator := 11581714890514975653101568000 }, { target := 594, numerator := 3336747924618126286651392000 }, { target := 763, numerator := 66100269456920381994565632 }, { target := 766, numerator := 229737350911872453203460096 }, { target := 768, numerator := 66188438940959906174337024 }]

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
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 66108029526121710989869056 }, { target := 27, numerator := 3332279769329755412892745728 }, { target := 29, numerator := 36600661270697856850420826112 }, { target := 37, numerator := 3332303049537359399878656000 }, { target := 44, numerator := 66100269456920381994565632 }, { target := 80, numerator := 31940640496059555407462400 }, { target := 82, numerator := 1161450108172848402844876800 }, { target := 85, numerator := 1161991096224170600772403200 }, { target := 92, numerator := 32482767169957543280640000 }, { target := 131, numerator := 115814003532060255867371520 }, { target := 134, numerator := 395292763292186636948865024 }, { target := 136, numerator := 115829885075044336108830720 }, { target := 157, numerator := 229764321720854828462112768 }, { target := 158, numerator := 11581633978088028527325609984 }, { target := 160, numerator := 127208845456114237695156289536 }, { target := 168, numerator := 11581714890514975653101568000 }, { target := 175, numerator := 229737350911872453203460096 }, { target := 176, numerator := 1558014793751923542894575616 }, { target := 178, numerator := 56653730878105295987945766912 }, { target := 181, numerator := 56680119434318093031768588288 }, { target := 188, numerator := 1584458890204052966709657600 }, { target := 227, numerator := 3450612454726159196875653120 }, { target := 230, numerator := 11777523362289676078697938944 }, { target := 232, numerator := 3451085636278906104651448320 }, { target := 267, numerator := 66196209361122028727304192 }, { target := 268, numerator := 3336724613357639918992490496 }, { target := 270, numerator := 36649481970617181726660624384 }, { target := 278, numerator := 3336747924618126286651392000 }, { target := 285, numerator := 66188438940959906174337024 }, { target := 286, numerator := 1557433968696329223480016896 }, { target := 288, numerator := 56632610471213870414794063872 }, { target := 291, numerator := 56658989189821343800731107328 }, { target := 298, numerator := 1583868206837835702573465600 }, { target := 302, numerator := 36756427824712657681986355200 }, { target := 305, numerator := 125455898945401148733118218240 }, { target := 307, numerator := 36761468223720000698135347200 }, { target := 573, numerator := 31934386914710579048349696 }, { target := 575, numerator := 1161222710643511683786473472 }, { target := 578, numerator := 1161763592776081620470857728 }, { target := 585, numerator := 32476407446928124123545600 }, { target := 589, numerator := 3460251190518276746473635840 }, { target := 592, numerator := 11810421996217435177151889408 }, { target := 594, numerator := 3460725693828256166565642240 }, { target := 763, numerator := 124348328109332949117173760 }, { target := 766, numerator := 424421855129933696427098112 }, { target := 768, numerator := 124365379961938322506383360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent2
