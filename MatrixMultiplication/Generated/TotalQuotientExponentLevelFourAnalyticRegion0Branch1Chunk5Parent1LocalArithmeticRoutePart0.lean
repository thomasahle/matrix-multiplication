import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 12282562184896623002255360 }, { target := 30, numerator := 547963164625549365046411264 }, { target := 35, numerator := 547981597986050881959755776 }, { target := 43, numerator := 12281627159363937361723392 }, { target := 71, numerator := 1273363432295337195208704 }, { target := 72, numerator := 51062518837501547237081088 }, { target := 74, numerator := 554564988831072981010612224 }, { target := 82, numerator := 51115731517467310354857984 }, { target := 89, numerator := 1320205719922688938475520 }, { target := 104, numerator := 421951048889796796402892800 }, { target := 105, numerator := 18824543982446686503666974720 }, { target := 110, numerator := 18825177235971569372081684480 }, { target := 118, numerator := 421918927334186795831132160 }, { target := 146, numerator := 32092948729967865627672576 }, { target := 147, numerator := 956191179125065443134406656 }, { target := 149, numerator := 10185488090382077594970357760 }, { target := 157, numerator := 958862146746977441170849792 }, { target := 164, numerator := 34457875532860894570610688 }, { target := 200, numerator := 12282562184896623002255360 }, { target := 202, numerator := 421951048889796796402892800 }, { target := 205, numerator := 421950427713929692724592640 }, { target := 212, numerator := 12282769243518990895022080 }, { target := 226, numerator := 421950427713929692724592640 }, { target := 227, numerator := 18824516269866135052863143936 }, { target := 232, numerator := 18825149522458772798412161024 }, { target := 240, numerator := 421918306205607488240222208 }, { target := 242, numerator := 352498357567284018312904704 }, { target := 243, numerator := 10502488350257858386040193024 }, { target := 245, numerator := 111874039780214657418044375040 }, { target := 253, numerator := 10531825377146889797231443968 }, { target := 260, numerator := 378473933099494561862909952 }, { target := 296, numerator := 547963164625549365046411264 }, { target := 298, numerator := 18824543982446686503666974720 }, { target := 301, numerator := 18824516269866135052863143936 }, { target := 308, numerator := 547972402152399848647688192 }, { target := 624, numerator := 12282769243518990895022080 }, { target := 625, numerator := 547972402152399848647688192 }, { target := 630, numerator := 547990835823649739849596928 }, { target := 638, numerator := 12281834202223706558693376 }, { target := 640, numerator := 32093172939986464407552000 }, { target := 641, numerator := 956197859335221870067712000 }, { target := 643, numerator := 10185559248956298908139520000 }, { target := 651, numerator := 958868845617235974160384000 }, { target := 658, numerator := 34458116264897676312576000 }, { target := 659, numerator := 547981597986050881959755776 }, { target := 661, numerator := 18825177235971569372081684480 }, { target := 664, numerator := 18825149522458772798412161024 }, { target := 671, numerator := 547990835823649739849596928 }, { target := 1017, numerator := 636606979474802337644544 }, { target := 1018, numerator := 18967343370814872631640064 }, { target := 1020, numerator := 202042911739048524974653440 }, { target := 1028, numerator := 19020325620728001617461248 }, { target := 1035, numerator := 683518496435626020175872 }, { target := 1036, numerator := 12281627159363937361723392 }, { target := 1038, numerator := 421918927334186795831132160 }, { target := 1041, numerator := 421918306205607488240222208 }, { target := 1048, numerator := 12281834202223706558693376 }]

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
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 18969570107533681609408512 }, { target := 147, numerator := 956191179125065443134406656 }, { target := 149, numerator := 10502488350257858386040193024 }, { target := 157, numerator := 956197859335221870067712000 }, { target := 164, numerator := 18967343370814872631640064 }, { target := 242, numerator := 202066631263788962697707520 }, { target := 243, numerator := 10185488090382077594970357760 }, { target := 245, numerator := 111874039780214657418044375040 }, { target := 253, numerator := 10185559248956298908139520000 }, { target := 260, numerator := 202042911739048524974653440 }, { target := 640, numerator := 19022558577480845947305984 }, { target := 641, numerator := 958862146746977441170849792 }, { target := 643, numerator := 10531825377146889797231443968 }, { target := 651, numerator := 958868845617235974160384000 }, { target := 658, numerator := 19020325620728001617461248 }, { target := 1017, numerator := 683598740447886600830976 }, { target := 1018, numerator := 34457875532860894570610688 }, { target := 1020, numerator := 378473933099494561862909952 }, { target := 1028, numerator := 34458116264897676312576000 }, { target := 1035, numerator := 683518496435626020175872 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5.Parent1
