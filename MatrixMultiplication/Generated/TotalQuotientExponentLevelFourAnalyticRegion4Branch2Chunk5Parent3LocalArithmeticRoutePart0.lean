import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent3

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
  [{ target := 19, numerator := 3305346931623479596768296960 }, { target := 21, numerator := 115536759891206948068712775680 }, { target := 24, numerator := 115536866144326148896210288640 }, { target := 31, numerator := 3305325680977121433131941888 }, { target := 35, numerator := 48994408799840787570075107328 }, { target := 38, numerator := 173532728749520661305144377344 }, { target := 40, numerator := 49023914562126813426918359040 }, { target := 71, numerator := 4099149444108573913741524992 }, { target := 73, numerator := 4099152667409136616657125376 }, { target := 90, numerator := 540108216702073020413378560 }, { target := 92, numerator := 19266913522392450399857541120 }, { target := 95, numerator := 19266913522392450399857541120 }, { target := 102, numerator := 540098771980366280191377408 }, { target := 106, numerator := 173593337022901616554989846528 }, { target := 109, numerator := 614759194726074599612545499136 }, { target := 111, numerator := 173699179039258239304351088640 }, { target := 116, numerator := 154357057525276606880678936576 }, { target := 118, numerator := 154357139304535581134451376128 }, { target := 140, numerator := 49026883508704732210584879104 }, { target := 143, numerator := 173649052540982384243580600320 }, { target := 145, numerator := 49056388821612580049145298944 }, { target := 150, numerator := 154357177945513833665574993920 }, { target := 152, numerator := 154357259724988980701461217280 }, { target := 232, numerator := 4099180139561644260566499328 }, { target := 234, numerator := 4099183362720343575219929088 }]

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
  [{ target := 19, numerator := 793802512485094316973228032 }, { target := 21, numerator := 38820297634069658811966160896 }, { target := 24, numerator := 38820311801187684769364705280 }, { target := 31, numerator := 793854458584522827434557440 }, { target := 35, numerator := 2583484112032041600213319680 }, { target := 38, numerator := 9169291800775669879903617024 }, { target := 40, numerator := 2585854053558498284068143104 }, { target := 90, numerator := 3559044450707063596243746816 }, { target := 92, numerator := 135090225782143130734593835008 }, { target := 95, numerator := 135090346202596530301603676160 }, { target := 102, numerator := 3559084590739977295028551680 }, { target := 106, numerator := 9108683527394714630058147840 }, { target := 109, numerator := 32328504284049147142091046912 }, { target := 111, numerator := 9117039316091996523255037952 }, { target := 140, numerator := 2582885106980579500401623040 }, { target := 143, numerator := 9167165814367851584025526272 }, { target := 145, numerator := 2585254499013838449527488512 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent3
