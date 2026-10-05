import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent0

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
  [{ target := 19, numerator := 3198837770482816654348648448 }, { target := 21, numerator := 115643639758044177209267060736 }, { target := 24, numerator := 115643746011632033872987815936 }, { target := 31, numerator := 3198726794549306269259268096 }, { target := 35, numerator := 53149508866258759836307030016 }, { target := 38, numerator := 176759514515500408518396084224 }, { target := 40, numerator := 53100213480937100656364224512 }, { target := 71, numerator := 4295765462068636693362114560 }, { target := 73, numerator := 4295758661744663454690574336 }, { target := 90, numerator := 3198826001116698156067717120 }, { target := 92, numerator := 115643188735515803630593638400 }, { target := 95, numerator := 115643294988419676100907499520 }, { target := 102, numerator := 3198715025825513667832053760 }, { target := 106, numerator := 176532001501801004054005940224 }, { target := 109, numerator := 586701417490333418882603155456 }, { target := 111, numerator := 176363930296169087987255083008 }, { target := 116, numerator := 154160741377473646008008179712 }, { target := 118, numerator := 154160464836000613002083565568 }, { target := 140, numerator := 53097629187758681657717030912 }, { target := 143, numerator := 176582539244106378906202800128 }, { target := 145, numerator := 53048333188157573778483707904 }, { target := 150, numerator := 134930025253967113920127696896 }, { target := 152, numerator := 134929579075419864598658940928 }, { target := 232, numerator := 3719450401923601482125410304 }, { target := 234, numerator := 3719438510750875662168358912 }]

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
  [{ target := 19, numerator := 1096927691585820039013466112 }, { target := 21, numerator := 38517101619429468798741118976 }, { target := 24, numerator := 38515047394662201868100304896 }, { target := 31, numerator := 1098906358660497841170939904 }, { target := 35, numerator := 2693872115267475508664729600 }, { target := 38, numerator := 9108884198340773166532526080 }, { target := 40, numerator := 2691910086084939906138767360 }, { target := 90, numerator := 1096932660627965298622857216 }, { target := 92, numerator := 38517276100484809371489927168 }, { target := 95, numerator := 38515221866411979710794825728 }, { target := 102, numerator := 1098911336665932259154460672 }, { target := 106, numerator := 9336397212040177630922670080 }, { target := 109, numerator := 31569487115664938823879491584 }, { target := 111, numerator := 9329597229336489397613232128 }, { target := 140, numerator := 2694494379263358904785960960 }, { target := 143, numerator := 9110988281399198478665515008 }, { target := 145, numerator := 2692531896866985776341057536 }, { target := 150, numerator := 19228768152327121820960423936 }, { target := 152, numerator := 19228937779411791213043384320 }, { target := 232, numerator := 578182751286202628304797696 }, { target := 234, numerator := 578187851740570264818155520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent0
