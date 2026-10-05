import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk6Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent1

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 104446904360242158527053824 }, { target := 17, numerator := 3111936191233334786857631744 }, { target := 19, numerator := 33148798802807535381501706240 }, { target := 27, numerator := 3120628888875500783961899008 }, { target := 34, numerator := 112143588316555847518912512 }, { target := 35, numerator := 2374021422491225493287731200 }, { target := 37, numerator := 85942992767791110020822728704 }, { target := 40, numerator := 85937358076695834702511079424 }, { target := 47, numerator := 2373996776951529324385665024 }, { target := 86, numerator := 3037407051184987959701012480 }, { target := 89, numerator := 10427574041462824938881679360 }, { target := 91, numerator := 3038981410009166676502773760 }, { target := 122, numerator := 120630891906464199707983872 }, { target := 124, numerator := 120748148498934845744873472 }, { target := 126, numerator := 104531979606188251114635264 }, { target := 127, numerator := 3114470959864912339884048384 }, { target := 129, numerator := 33175799528470400322911600640 }, { target := 137, numerator := 3123170737979155246101823488 }, { target := 144, numerator := 112234932750512475164639232 }, { target := 145, numerator := 8048496746612061450346168320 }, { target := 147, numerator := 290682481549945045521304387584 }, { target := 150, numerator := 290664239353216182896488873984 }, { target := 157, numerator := 8048423285801651275053400064 }, { target := 161, numerator := 106289857245716627799052124160 }, { target := 164, numerator := 364981209967636520080852910080 }, { target := 166, numerator := 106346535013295124282207109120 }, { target := 197, numerator := 6080590868273872015338766336 }, { target := 199, numerator := 6086501372243077224135131136 }, { target := 216, numerator := 2374481091830678531604480000 }, { target := 218, numerator := 85961320292939149490578784256 }, { target := 221, numerator := 85955682390245352151120347136 }, { target := 228, numerator := 2374456416652230265023758336 }, { target := 232, numerator := 35197035473699870837928099840 }, { target := 235, numerator := 122330419469000165660578283520 }, { target := 237, numerator := 35243983912532778591065210880 }, { target := 242, numerator := 66787203386633506698238623744 }, { target := 244, numerator := 66852122411652677483253202944 }, { target := 406, numerator := 983912107485172196179968000 }, { target := 409, numerator := 3419673822223663003336704000 }, { target := 411, numerator := 985224523055788694962176000 }, { target := 416, numerator := 6080633348926028300419072000 }, { target := 418, numerator := 6086543894187612592668672000 }, { target := 498, numerator := 120616731689078771347881984 }, { target := 500, numerator := 120733974517423056233693184 }]

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
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 120630891906464199707983872 }, { target := 17, numerator := 6080590868273872015338766336 }, { target := 19, numerator := 66787203386633506698238623744 }, { target := 27, numerator := 6080633348926028300419072000 }, { target := 34, numerator := 120616731689078771347881984 }, { target := 35, numerator := 967490938825248783340666880 }, { target := 37, numerator := 35180648794236397776179036160 }, { target := 40, numerator := 35197035473699870837928099840 }, { target := 47, numerator := 983912107485172196179968000 }, { target := 86, numerator := 304105310131486316927385600 }, { target := 89, numerator := 983523298809639870241177600 }, { target := 91, numerator := 304281132434231214368358400 }, { target := 122, numerator := 104446904360242158527053824 }, { target := 124, numerator := 104531979606188251114635264 }, { target := 126, numerator := 120748148498934845744873472 }, { target := 127, numerator := 6086501372243077224135131136 }, { target := 129, numerator := 66852122411652677483253202944 }, { target := 137, numerator := 6086543894187612592668672000 }, { target := 144, numerator := 120733974517423056233693184 }, { target := 145, numerator := 3362600593660403358776688640 }, { target := 147, numerator := 122273466110699049906056724480 }, { target := 150, numerator := 122330419469000165660578283520 }, { target := 157, numerator := 3419673822223663003336704000 }, { target := 161, numerator := 14833784316310879997949640704 }, { target := 164, numerator := 47974737693007575346508201984 }, { target := 166, numerator := 14842360654934455008421216256 }, { target := 197, numerator := 3111936191233334786857631744 }, { target := 199, numerator := 3114470959864912339884048384 }, { target := 216, numerator := 968781450612719359266652160 }, { target := 218, numerator := 35227575375290429800049541120 }, { target := 221, numerator := 35243983912532778591065210880 }, { target := 228, numerator := 985224523055788694962176000 }, { target := 232, numerator := 85937358076695834702511079424 }, { target := 235, numerator := 290664239353216182896488873984 }, { target := 237, numerator := 85955682390245352151120347136 }, { target := 242, numerator := 33148798802807535381501706240 }, { target := 244, numerator := 33175799528470400322911600640 }, { target := 406, numerator := 2373996776951529324385665024 }, { target := 409, numerator := 8048423285801651275053400064 }, { target := 411, numerator := 2374456416652230265023758336 }, { target := 416, numerator := 3120628888875500783961899008 }, { target := 418, numerator := 3123170737979155246101823488 }, { target := 498, numerator := 112143588316555847518912512 }, { target := 500, numerator := 112234932750512475164639232 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent1
