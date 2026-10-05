import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 27; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 89, numerator := 227381946150173417039462400 }, { target := 90, numerator := 176852624783468213252915200 }, { target := 91, numerator := 202117285466820815146188800 }, { target := 92, numerator := 237487810423514457796771840 }, { target := 93, numerator := 2804377335852138810153369600 }, { target := 94, numerator := 6306059306564809432561090560 }, { target := 95, numerator := 176852624783468213252915200 }, { target := 96, numerator := 2804377335852138810153369600 }, { target := 97, numerator := 202117285466820815146188800 }, { target := 98, numerator := 197064353330150294767534080 }, { target := 99, numerator := 197064353330150294767534080 }, { target := 100, numerator := 197064353330150294767534080 }, { target := 101, numerator := 6306059306564809432561090560 }, { target := 102, numerator := 197064353330150294767534080 }, { target := 103, numerator := 227381946150173417039462400 }, { target := 104, numerator := 237487810423514457796771840 }, { target := 160, numerator := 207831348911093085854760960 }, { target := 161, numerator := 161646604708627955664814080 }, { target := 162, numerator := 184738976809860520759787520 }, { target := 163, numerator := 217068297751586111892750336 }, { target := 164, numerator := 2563253303236814725542051840 }, { target := 165, numerator := 5763856076467648247705370624 }, { target := 166, numerator := 161646604708627955664814080 }, { target := 167, numerator := 2563253303236814725542051840 }, { target := 168, numerator := 184738976809860520759787520 }, { target := 169, numerator := 180120502389614007740792832 }, { target := 170, numerator := 180120502389614007740792832 }, { target := 171, numerator := 180120502389614007740792832 }, { target := 172, numerator := 5763856076467648247705370624 }, { target := 173, numerator := 180120502389614007740792832 }, { target := 174, numerator := 207831348911093085854760960 }, { target := 175, numerator := 217068297751586111892750336 }, { target := 205, numerator := 227381946150173417039462400 }, { target := 206, numerator := 176852624783468213252915200 }, { target := 207, numerator := 202117285466820815146188800 }, { target := 208, numerator := 237487810423514457796771840 }, { target := 209, numerator := 2804377335852138810153369600 }, { target := 210, numerator := 6306059306564809432561090560 }, { target := 211, numerator := 176852624783468213252915200 }, { target := 212, numerator := 2804377335852138810153369600 }, { target := 213, numerator := 202117285466820815146188800 }, { target := 214, numerator := 197064353330150294767534080 }, { target := 215, numerator := 197064353330150294767534080 }, { target := 216, numerator := 197064353330150294767534080 }, { target := 217, numerator := 6306059306564809432561090560 }, { target := 218, numerator := 197064353330150294767534080 }, { target := 219, numerator := 227381946150173417039462400 }, { target := 220, numerator := 237487810423514457796771840 }, { target := 247, numerator := 124160459567608711958495232 }, { target := 248, numerator := 19821868859322295084356993024 }, { target := 250, numerator := 197792443072112653796936515584 }, { target := 258, numerator := 19821868859322295084356993024 }, { target := 265, numerator := 124146292468160103022854144 }]

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
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 18, numerator := 51311266165853201004232704 }, { target := 20, numerator := 497004674197149668645797888 }, { target := 25, numerator := 51311266165853201004232704 }, { target := 45, numerator := 1228159983711712101456150528 }, { target := 47, numerator := 11896047363041453359199420416 }, { target := 52, numerator := 1228159983711712101456150528 }, { target := 65, numerator := 918637184582210534108037120 }, { target := 67, numerator := 8897986909013486003174768640 }, { target := 72, numerator := 918637184582210534108037120 }, { target := 79, numerator := 1065950174542240691829866496 }, { target := 81, numerator := 10324871296224657632512704512 }, { target := 86, numerator := 1065950174542240691829866496 }, { target := 89, numerator := 116389805520046710759358464 }, { target := 90, numerator := 9787130508762995488433635328 }, { target := 95, numerator := 9787128147579754053611028480 }, { target := 103, numerator := 116392166703288145581965312 }, { target := 116, numerator := 51311266165853201004232704 }, { target := 118, numerator := 497004674197149668645797888 }, { target := 123, numerator := 51311266165853201004232704 }, { target := 136, numerator := 1064294972407858330507149312 }, { target := 138, numerator := 10308838887379588288362840064 }, { target := 143, numerator := 1064294972407858330507149312 }, { target := 150, numerator := 1069260578811005414475300864 }, { target := 152, numerator := 10356936113914796320812433408 }, { target := 157, numerator := 1069260578811005414475300864 }, { target := 160, numerator := 116389805520046710759358464 }, { target := 161, numerator := 9787130508762995488433635328 }, { target := 166, numerator := 9787128147579754053611028480 }, { target := 174, numerator := 116392166703288145581965312 }, { target := 181, numerator := 51311266165853201004232704 }, { target := 183, numerator := 497004674197149668645797888 }, { target := 188, numerator := 51311266165853201004232704 }, { target := 195, numerator := 1228159983711712101456150528 }, { target := 197, numerator := 11896047363041453359199420416 }, { target := 202, numerator := 1228159983711712101456150528 }, { target := 205, numerator := 116389805520046710759358464 }, { target := 206, numerator := 9787130508762995488433635328 }, { target := 211, numerator := 9787128147579754053611028480 }, { target := 219, numerator := 116392166703288145581965312 }, { target := 221, numerator := 51311266165853201004232704 }, { target := 223, numerator := 497004674197149668645797888 }, { target := 228, numerator := 51311266165853201004232704 }, { target := 231, numerator := 324221154431139796614119424 }, { target := 232, numerator := 9948777113471623444098449408 }, { target := 233, numerator := 184738976809860520759787520 }, { target := 234, numerator := 217068297751586111892750336 }, { target := 235, numerator := 2563253303236814725542051840 }, { target := 236, numerator := 5763856076467648247705370624 }, { target := 237, numerator := 9948774752288382009275842560 }, { target := 238, numerator := 2563253303236814725542051840 }, { target := 239, numerator := 184738976809860520759787520 }, { target := 240, numerator := 180120502389614007740792832 }, { target := 241, numerator := 180120502389614007740792832 }, { target := 242, numerator := 180120502389614007740792832 }, { target := 243, numerator := 5763856076467648247705370624 }, { target := 244, numerator := 180120502389614007740792832 }, { target := 245, numerator := 324223515614381231436726272 }, { target := 246, numerator := 217068297751586111892750336 }]

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

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 3, numerator := 343771751670220127798820864 }, { target := 4, numerator := 324221154431139796614119424 }, { target := 5, numerator := 343771751670220127798820864 }, { target := 6, numerator := 324221154431139796614119424 }, { target := 9, numerator := 9963983133546463701686550528 }, { target := 10, numerator := 9948777113471623444098449408 }, { target := 11, numerator := 9963983133546463701686550528 }, { target := 12, numerator := 9948777113471623444098449408 }, { target := 14, numerator := 202117285466820815146188800 }, { target := 15, numerator := 184738976809860520759787520 }, { target := 16, numerator := 202117285466820815146188800 }, { target := 17, numerator := 184738976809860520759787520 }, { target := 30, numerator := 237487810423514457796771840 }, { target := 31, numerator := 217068297751586111892750336 }, { target := 32, numerator := 237487810423514457796771840 }, { target := 33, numerator := 217068297751586111892750336 }, { target := 36, numerator := 2804377335852138810153369600 }, { target := 37, numerator := 2563253303236814725542051840 }, { target := 38, numerator := 2804377335852138810153369600 }, { target := 39, numerator := 2563253303236814725542051840 }, { target := 41, numerator := 6306059306564809432561090560 }, { target := 42, numerator := 5763856076467648247705370624 }, { target := 43, numerator := 6306059306564809432561090560 }, { target := 44, numerator := 5763856076467648247705370624 }, { target := 56, numerator := 9963980772363222266863943680 }, { target := 57, numerator := 9948774752288382009275842560 }, { target := 58, numerator := 9963980772363222266863943680 }, { target := 59, numerator := 9948774752288382009275842560 }, { target := 61, numerator := 2804377335852138810153369600 }, { target := 62, numerator := 2563253303236814725542051840 }, { target := 63, numerator := 2804377335852138810153369600 }, { target := 64, numerator := 2563253303236814725542051840 }, { target := 75, numerator := 202117285466820815146188800 }, { target := 76, numerator := 184738976809860520759787520 }, { target := 77, numerator := 202117285466820815146188800 }, { target := 78, numerator := 184738976809860520759787520 }, { target := 107, numerator := 197064353330150294767534080 }, { target := 108, numerator := 180120502389614007740792832 }, { target := 109, numerator := 197064353330150294767534080 }, { target := 110, numerator := 180120502389614007740792832 }, { target := 112, numerator := 197064353330150294767534080 }, { target := 113, numerator := 180120502389614007740792832 }, { target := 114, numerator := 197064353330150294767534080 }, { target := 115, numerator := 180120502389614007740792832 }, { target := 127, numerator := 197064353330150294767534080 }, { target := 128, numerator := 180120502389614007740792832 }, { target := 129, numerator := 197064353330150294767534080 }, { target := 130, numerator := 180120502389614007740792832 }, { target := 177, numerator := 116392166703288145581965312 }, { target := 178, numerator := 116392166703288145581965312 }, { target := 179, numerator := 116392166703288145581965312 }, { target := 180, numerator := 116392166703288145581965312 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 124160459567608711958495232 }, { target := 1, numerator := 19821868859322295084356993024 }, { target := 7, numerator := 197792443072112653796936515584 }, { target := 55, numerator := 19821868859322295084356993024 }, { target := 132, numerator := 6306059306564809432561090560 }, { target := 133, numerator := 5763856076467648247705370624 }, { target := 134, numerator := 6306059306564809432561090560 }, { target := 135, numerator := 5763856076467648247705370624 }, { target := 146, numerator := 197064353330150294767534080 }, { target := 147, numerator := 180120502389614007740792832 }, { target := 148, numerator := 197064353330150294767534080 }, { target := 149, numerator := 180120502389614007740792832 }, { target := 176, numerator := 124146292468160103022854144 }, { target := 177, numerator := 227381946150173417039462400 }, { target := 178, numerator := 207831348911093085854760960 }, { target := 179, numerator := 227381946150173417039462400 }, { target := 180, numerator := 207831348911093085854760960 }, { target := 191, numerator := 237487810423514457796771840 }, { target := 192, numerator := 217068297751586111892750336 }, { target := 193, numerator := 237487810423514457796771840 }, { target := 194, numerator := 217068297751586111892750336 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent1
