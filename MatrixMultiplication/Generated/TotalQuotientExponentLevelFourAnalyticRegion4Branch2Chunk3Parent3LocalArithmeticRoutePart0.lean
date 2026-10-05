import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent3

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
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 2004490533650148956622028800 }, { target := 37, numerator := 69951927996265174012363014144 }, { target := 40, numerator := 69951997539423260260662509568 }, { target := 47, numerator := 2004479403194791419627700224 }, { target := 86, numerator := 2520321838876169639276052480 }, { target := 89, numerator := 8880884158250718446391132160 }, { target := 91, numerator := 2522667965781846478689402880 }, { target := 122, numerator := 268190154275447786946166784 }, { target := 124, numerator := 268190397948335125361065984 }, { target := 145, numerator := 7023579772465586759490600960 }, { target := 147, numerator := 245113705090390132834493792256 }, { target := 150, numerator := 245113948425655555034355597312 }, { target := 157, numerator := 7023540655745646941410689024 }, { target := 161, numerator := 97753582540943555972126736384 }, { target := 164, numerator := 345084067838922786107258044416 }, { target := 166, numerator := 97835277969055002766256111616 }, { target := 197, numerator := 8508494294785931355768225792 }, { target := 199, numerator := 8508501380203523605687959552 }, { target := 216, numerator := 194808386815644676139253760 }, { target := 218, numerator := 6949267250796478372270571520 }, { target := 221, numerator := 6949267250796478372270571520 }, { target := 228, numerator := 194804980255731836170272768 }, { target := 232, numerator := 97753664763813285971380666368 }, { target := 235, numerator := 345084356650241053226635886592 }, { target := 237, numerator := 97835360282049361133564854272 }, { target := 242, numerator := 101281250603712249047002644480 }, { target := 244, numerator := 101281330410610759294611619840 }, { target := 406, numerator := 2520360604134631587409035264 }, { target := 409, numerator := 8881023866526102906854178816 }, { target := 411, numerator := 2522706721106212073773203456 }, { target := 416, numerator := 8508539157219667871356944384 }, { target := 418, numerator := 8508546242732961613358301184 }, { target := 498, numerator := 275722337738381632789807104 }, { target := 500, numerator := 275722563565755447749115904 }]

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
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 268190154275447786946166784 }, { target := 17, numerator := 8508494294785931355768225792 }, { target := 19, numerator := 101281250603712249047002644480 }, { target := 27, numerator := 8508539157219667871356944384 }, { target := 34, numerator := 275722337738381632789807104 }, { target := 35, numerator := 710461149681557644907642880 }, { target := 37, numerator := 34744552775145409061993840640 }, { target := 40, numerator := 34744565454857052812948275200 }, { target := 47, numerator := 710507641957584731740569600 }, { target := 86, numerator := 194629844455536962253619200 }, { target := 89, numerator := 690779489852835356014018560 }, { target := 91, numerator := 194808386815644676139253760 }, { target := 126, numerator := 268190397948335125361065984 }, { target := 127, numerator := 8508501380203523605687959552 }, { target := 129, numerator := 101281330410610759294611619840 }, { target := 137, numerator := 8508546242732961613358301184 }, { target := 144, numerator := 275722563565755447749115904 }, { target := 145, numerator := 2548083875637967042914549760 }, { target := 147, numerator := 124612070248010265339919073280 }, { target := 150, numerator := 124612115724063110259435110400 }, { target := 157, numerator := 2548250621165065081140019200 }, { target := 161, numerator := 6942898230467027102230118400 }, { target := 164, numerator := 24641707499477612067154821120 }, { target := 166, numerator := 6949267250796478372270571520 }, { target := 216, numerator := 2522667965781846478689402880 }, { target := 218, numerator := 97835277969055002766256111616 }, { target := 221, numerator := 97835360282049361133564854272 }, { target := 228, numerator := 2522706721106212073773203456 }, { target := 232, numerator := 6942898230467027102230118400 }, { target := 235, numerator := 24641707499477612067154821120 }, { target := 237, numerator := 6949267250796478372270571520 }, { target := 406, numerator := 194626441017744563959234560 }, { target := 409, numerator := 690767410384609115696529408 }, { target := 411, numerator := 194804980255731836170272768 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent3
