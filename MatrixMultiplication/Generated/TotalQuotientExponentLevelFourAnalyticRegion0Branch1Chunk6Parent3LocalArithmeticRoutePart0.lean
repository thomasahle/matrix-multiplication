import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 8866646763843782241681408 }, { target := 57, numerator := 264176704214418908982018048 }, { target := 59, numerator := 2814048835918420806551470080 }, { target := 67, numerator := 264914639722322026284711936 }, { target := 74, numerator := 9520029248576898050555904 }, { target := 110, numerator := 11291628194632418992324608 }, { target := 112, numerator := 422888653377283853257801728 }, { target := 115, numerator := 422844107846090517035089920 }, { target := 122, numerator := 11291302886683485092708352 }, { target := 152, numerator := 304601828659147564740771840 }, { target := 153, numerator := 9075438475906389399086039040 }, { target := 155, numerator := 96672896100047963625514598400 }, { target := 163, numerator := 9100789266473167707470561280 }, { target := 170, numerator := 327047912840050107136081920 }, { target := 206, numerator := 386411728019270190285979648 }, { target := 208, numerator := 15037872930721767199902531584 }, { target := 211, numerator := 15035636785679906620273852416 }, { target := 218, numerator := 386392249390746609236574208 }, { target := 257, numerator := 158568391830045431252910080 }, { target := 260, numerator := 551118513989302438057738240 }, { target := 262, numerator := 158779902212794233714114560 }, { target := 283, numerator := 304601380239110367181012992 }, { target := 284, numerator := 9075425115486076545219428352 }, { target := 286, numerator := 96672753782899520999176273920 }, { target := 294, numerator := 9100775868732650641491492864 }, { target := 301, numerator := 327047431375976543652151296 }, { target := 302, numerator := 4156637997511210477006356480 }, { target := 304, numerator := 162162308435114179609730482176 }, { target := 307, numerator := 162137751785243803430500171776 }, { target := 314, numerator := 4156422574250797777494736896 }, { target := 353, numerator := 7074227387476248628289339392 }, { target := 356, numerator := 24587104910460504514941157376 }, { target := 358, numerator := 7083663521154017626993721344 }, { target := 660, numerator := 8866796237189514761601024 }, { target := 661, numerator := 264181157687856526937554944 }, { target := 663, numerator := 2814096274967901681997578240 }, { target := 671, numerator := 264919105635827714944401408 }, { target := 678, numerator := 9520189736601419211866112 }, { target := 679, numerator := 122235877771783123763200000 }, { target := 681, numerator := 5962476109994877085810688000 }, { target := 684, numerator := 5960253309844354894921728000 }, { target := 691, numerator := 122211945502625788592128000 }, { target := 695, numerator := 7074465362931756050811977728 }, { target := 698, numerator := 24587932015269297356206505984 }, { target := 700, numerator := 7083901814038989385284714496 }, { target := 966, numerator := 2424696775144689264230400 }, { target := 968, numerator := 118272939658303193518964736 }, { target := 971, numerator := 118228847723471876564975616 }, { target := 978, numerator := 2424222049582068233404416 }, { target := 982, numerator := 158556320611287808371326976 }, { target := 985, numerator := 551076559397552076544278528 }, { target := 987, numerator := 158767814892542043076165632 }]

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
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 158568391830045431252910080 }, { target := 15, numerator := 7074227387476248628289339392 }, { target := 20, numerator := 7074465362931756050811977728 }, { target := 28, numerator := 158556320611287808371326976 }, { target := 56, numerator := 2424981430788636750643200 }, { target := 57, numerator := 122235023804851281303961600 }, { target := 59, numerator := 1342589161592789670454886400 }, { target := 67, numerator := 122235877771783123763200000 }, { target := 74, numerator := 2424696775144689264230400 }, { target := 136, numerator := 551118513989302438057738240 }, { target := 137, numerator := 24587104910460504514941157376 }, { target := 142, numerator := 24587932015269297356206505984 }, { target := 150, numerator := 551076559397552076544278528 }, { target := 152, numerator := 118286824718136288517029888 }, { target := 153, numerator := 5962434454815377800816492544 }, { target := 155, numerator := 65489412335066215984215883776 }, { target := 163, numerator := 5962476109994877085810688000 }, { target := 170, numerator := 118272939658303193518964736 }, { target := 267, numerator := 158779902212794233714114560 }, { target := 268, numerator := 7083663521154017626993721344 }, { target := 273, numerator := 7083901814038989385284714496 }, { target := 281, numerator := 158767814892542043076165632 }, { target := 283, numerator := 118242727606980149854076928 }, { target := 284, numerator := 5960211670193830075054424064 }, { target := 286, numerator := 65464998002344282431323897856 }, { target := 294, numerator := 5960253309844354894921728000 }, { target := 301, numerator := 118228847723471876564975616 }, { target := 660, numerator := 2424506649493970331107328 }, { target := 661, numerator := 122211091702890082299019264 }, { target := 663, numerator := 1342326299282896095497158656 }, { target := 671, numerator := 122211945502625788592128000 }, { target := 678, numerator := 2424222049582068233404416 }, { target := 679, numerator := 264914639722322026284711936 }, { target := 681, numerator := 9100789266473167707470561280 }, { target := 684, numerator := 9100775868732650641491492864 }, { target := 691, numerator := 264919105635827714944401408 }, { target := 966, numerator := 9520029248576898050555904 }, { target := 968, numerator := 327047912840050107136081920 }, { target := 971, numerator := 327047431375976543652151296 }, { target := 978, numerator := 9520189736601419211866112 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6.Parent3
