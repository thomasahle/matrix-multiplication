import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2077762369120968405982117888 }, { target := 21, numerator := 77117155543566898530715959296 }, { target := 24, numerator := 77109836501819132585283944448 }, { target := 31, numerator := 2077712802229594413963673600 }, { target := 35, numerator := 29472452537870200513536983040 }, { target := 38, numerator := 101678805069918449545756278784 }, { target := 40, numerator := 29492014228422889304838111232 }, { target := 71, numerator := 2607645940548991519704481792 }, { target := 73, numerator := 2609610382625943903451217920 }, { target := 90, numerator := 2079719357434292716896780288 }, { target := 92, numerator := 77189059372486275049671622656 }, { target := 95, numerator := 77181734355770662225295966208 }, { target := 102, numerator := 2079669754629526446365736960 }, { target := 106, numerator := 100936225549646012774424248320 }, { target := 109, numerator := 348168631007142390748638347264 }, { target := 111, numerator := 101003123906582348977282220032 }, { target := 116, numerator := 96385189051849780557485441024 }, { target := 118, numerator := 96457363920248568519359201280 }, { target := 140, numerator := 29493696948831424568948162560 }, { target := 143, numerator := 101751574934878208246432137216 }, { target := 145, numerator := 29513263473615788849126965248 }, { target := 150, numerator := 76989261132081307260744105984 }, { target := 152, numerator := 77045630217698590853890572288 }, { target := 232, numerator := 2218852525854408718537457664 }, { target := 234, numerator := 2220493088963892918211313664 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 529883571428023113722363904 }, { target := 21, numerator := 19268033508282882026769481728 }, { target := 24, numerator := 19277008302660278985343107072 }, { target := 31, numerator := 538877255138495361869414400 }, { target := 35, numerator := 2749748901686983470077706240 }, { target := 38, numerator := 8893110447548724983931863040 }, { target := 40, numerator := 2751338703534428425405071360 }, { target := 90, numerator := 529891025191651186554437632 }, { target := 92, numerator := 19268304547762293469687578624 }, { target := 95, numerator := 19277279468386284032571211776 }, { target := 102, numerator := 538884835414429417026355200 }, { target := 106, numerator := 9635689967821161755263893504 }, { target := 109, numerator := 31163301881709575775698550784 }, { target := 111, numerator := 9641260962941061877209235456 }, { target := 140, numerator := 2749655983125893161295020032 }, { target := 143, numerator := 8892809934645202608059318272 }, { target := 145, numerator := 2751245731251305536603291648 }, { target := 150, numerator := 19397583672398104309882945536 }, { target := 152, numerator := 19413383606458355403976605696 }, { target := 232, numerator := 397737531513681057295630336 }, { target := 234, numerator := 398061501080062945180778496 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7.Parent3
