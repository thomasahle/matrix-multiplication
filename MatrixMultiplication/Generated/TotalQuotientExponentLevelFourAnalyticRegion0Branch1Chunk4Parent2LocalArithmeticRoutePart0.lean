import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk4Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot16.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 120640387532357528098701312 }, { target := 17, numerator := 6081069510313095995437613056 }, { target := 19, numerator := 66792460632831378197393178624 }, { target := 27, numerator := 6081111994309175003840512000 }, { target := 34, numerator := 120626226200331191964401664 }, { target := 35, numerator := 1070263952418698884924047360 }, { target := 37, numerator := 36767491221605443743567052800 }, { target := 40, numerator := 36767437094288303757868400640 }, { target := 47, numerator := 1070281994857745546823598080 }, { target := 86, numerator := 2358655001605759708279341056 }, { target := 89, numerator := 8075514231187516303110832128 }, { target := 91, numerator := 2359458258471920537165627392 }, { target := 122, numerator := 200381291702166433285799936 }, { target := 124, numerator := 200557067426432184647417856 }, { target := 145, numerator := 3461398068401882519893442560 }, { target := 147, numerator := 118911715943376977331539148800 }, { target := 150, numerator := 118911540887316673034914365440 }, { target := 157, numerator := 3461456420421983952101703680 }, { target := 161, numerator := 85253041484139792551431372800 }, { target := 164, numerator := 291860961347483806208014417920 }, { target := 166, numerator := 85281564270694382859976704000 }, { target := 197, numerator := 9480970745061677922074492928 }, { target := 199, numerator := 9489228763808042387282853888 }, { target := 216, numerator := 1070882738958722632033239040 }, { target := 218, numerator := 36788748808228776264807219200 }, { target := 221, numerator := 36788694649617248368417832960 }, { target := 228, numerator := 1070900791829231930829701120 }, { target := 232, numerator := 85286153431051798629429805056 }, { target := 235, numerator := 291973975110972216538979893248 }, { target := 237, numerator := 85314680702517766704743841792 }, { target := 242, numerator := 99427992728382993383731232768 }, { target := 244, numerator := 99514119908717241279770001408 }, { target := 406, numerator := 2391964347562947716044554240 }, { target := 409, numerator := 8189209716357708129207582720 }, { target := 411, numerator := 2392772269126435236143431680 }, { target := 416, numerator := 9481041549492527787197595648 }, { target := 418, numerator := 9489299630371678611516162048 }, { target := 498, numerator := 200360050261447382971449344 }, { target := 500, numerator := 200535807568805408154845184 }]

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
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 79740904169808905187098624 }, { target := 17, numerator := 3399901234748581926636879872 }, { target := 19, numerator := 32635532095551615186338054144 }, { target := 27, numerator := 3399929555183352783357083648 }, { target := 34, numerator := 79733824061116191007047680 }, { target := 35, numerator := 2358655001605759708279341056 }, { target := 37, numerator := 85253041484139792551431372800 }, { target := 40, numerator := 85286153431051798629429805056 }, { target := 47, numerator := 2391964347562947716044554240 }, { target := 86, numerator := 1070263952418698884924047360 }, { target := 89, numerator := 3461398068401882519893442560 }, { target := 91, numerator := 1070882738958722632033239040 }, { target := 126, numerator := 200557067426432184647417856 }, { target := 127, numerator := 9489228763808042387282853888 }, { target := 129, numerator := 99514119908717241279770001408 }, { target := 137, numerator := 9489299630371678611516162048 }, { target := 144, numerator := 200535807568805408154845184 }, { target := 145, numerator := 8075514231187516303110832128 }, { target := 147, numerator := 291860961347483806208014417920 }, { target := 150, numerator := 291973975110972216538979893248 }, { target := 157, numerator := 8189209716357708129207582720 }, { target := 161, numerator := 36767491221605443743567052800 }, { target := 164, numerator := 118911715943376977331539148800 }, { target := 166, numerator := 36788748808228776264807219200 }, { target := 216, numerator := 2359458258471920537165627392 }, { target := 218, numerator := 85281564270694382859976704000 }, { target := 221, numerator := 85314680702517766704743841792 }, { target := 228, numerator := 2392772269126435236143431680 }, { target := 232, numerator := 36767437094288303757868400640 }, { target := 235, numerator := 118911540887316673034914365440 }, { target := 237, numerator := 36788694649617248368417832960 }, { target := 406, numerator := 1070281994857745546823598080 }, { target := 409, numerator := 3461456420421983952101703680 }, { target := 411, numerator := 1070900791829231930829701120 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent2
