import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk8Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 9181839659821280092225536 }, { target := 30, numerator := 471980205452171371660443648 }, { target := 35, numerator := 472089933701685590586556416 }, { target := 43, numerator := 9076585431980928952958976 }, { target := 71, numerator := 803089147607105981644800 }, { target := 72, numerator := 27294123294714612500398080 }, { target := 74, numerator := 300532820292033451634196480 }, { target := 82, numerator := 27294548547109426959482880 }, { target := 89, numerator := 802982834508402366873600 }, { target := 104, numerator := 368786613494380779976785920 }, { target := 105, numerator := 18956983355607447633458626560 }, { target := 110, numerator := 18961390567129566817047019520 }, { target := 118, numerator := 364559100089734307480862720 }, { target := 146, numerator := 27294123294714612500398080 }, { target := 147, numerator := 927629477557755427178938368 }, { target := 149, numerator := 10214033990622549768570667008 }, { target := 157, numerator := 927643930363312596685160448 }, { target := 164, numerator := 27290510093325320123842560 }, { target := 200, numerator := 9181839659821280092225536 }, { target := 202, numerator := 368786613494380779976785920 }, { target := 205, numerator := 368858299799280528513826816 }, { target := 212, numerator := 9110784158358738644762624 }, { target := 226, numerator := 368858299799280528513826816 }, { target := 227, numerator := 18960668294374429857769586688 }, { target := 232, numerator := 18965076362589003083306500096 }, { target := 240, numerator := 364629964632661673908371456 }, { target := 242, numerator := 300532820292033451634196480 }, { target := 243, numerator := 10214033990622549768570667008 }, { target := 245, numerator := 112465691189828866834429902848 }, { target := 253, numerator := 10214193128997075600422207488 }, { target := 260, numerator := 300493035698401993671311360 }, { target := 296, numerator := 471980205452171371660443648 }, { target := 298, numerator := 18956983355607447633458626560 }, { target := 301, numerator := 18960668294374429857769586688 }, { target := 308, numerator := 468327692293446690492383232 }, { target := 624, numerator := 9110784158358738644762624 }, { target := 625, numerator := 468327692293446690492383232 }, { target := 630, numerator := 468436571388969693734764544 }, { target := 638, numerator := 9006344461398617918275584 }, { target := 640, numerator := 27294548547109426959482880 }, { target := 641, numerator := 927643930363312596685160448 }, { target := 643, numerator := 10214193128997075600422207488 }, { target := 651, numerator := 927658383394049747559907328 }, { target := 658, numerator := 27290935289425139240796160 }, { target := 659, numerator := 472089933701685590586556416 }, { target := 661, numerator := 18961390567129566817047019520 }, { target := 664, numerator := 18965076362589003083306500096 }, { target := 671, numerator := 468436571388969693734764544 }, { target := 1017, numerator := 802982834508402366873600 }, { target := 1018, numerator := 27290510093325320123842560 }, { target := 1020, numerator := 300493035698401993671311360 }, { target := 1028, numerator := 27290935289425139240796160 }, { target := 1035, numerator := 802876535483447587635200 }, { target := 1036, numerator := 9076585431980928952958976 }, { target := 1038, numerator := 364559100089734307480862720 }, { target := 1041, numerator := 364629964632661673908371456 }, { target := 1048, numerator := 9006344461398617918275584 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent0
