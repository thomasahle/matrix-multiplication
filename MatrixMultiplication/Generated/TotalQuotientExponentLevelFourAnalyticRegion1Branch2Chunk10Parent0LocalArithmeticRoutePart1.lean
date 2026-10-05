import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk20

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left18.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 2597066461825085439297454080 }, { target := 30, numerator := 2671268360734373594705952768 }, { target := 31, numerator := 2597066461825085439297454080 }, { target := 32, numerator := 2300258866187932817663459328 }, { target := 33, numerator := 107666955317377113497731596288 }, { target := 34, numerator := 29309750069168821386356981760 }, { target := 35, numerator := 2671268360734373594705952768 }, { target := 36, numerator := 107666955317377113497731596288 }, { target := 37, numerator := 2597066461825085439297454080 }, { target := 38, numerator := 2597066461825085439297454080 }, { target := 39, numerator := 2226056967278644662254960640 }, { target := 40, numerator := 2597066461825085439297454080 }, { target := 41, numerator := 29309750069168821386356981760 }, { target := 42, numerator := 2226056967278644662254960640 }, { target := 43, numerator := 2597066461825085439297454080 }, { target := 44, numerator := 2300258866187932817663459328 }, { target := 104, numerator := 95906209320374899715761766400 }, { target := 105, numerator := 98646386729528468279069245440 }, { target := 106, numerator := 95906209320374899715761766400 }, { target := 107, numerator := 84945499683760625462531850240 }, { target := 108, numerator := 3975997420681827985359152087040 }, { target := 109, numerator := 1082370076615659582506454220800 }, { target := 110, numerator := 98646386729528468279069245440 }, { target := 111, numerator := 3975997420681827985359152087040 }, { target := 112, numerator := 95906209320374899715761766400 }, { target := 113, numerator := 95906209320374899715761766400 }, { target := 114, numerator := 82205322274607056899224371200 }, { target := 115, numerator := 95906209320374899715761766400 }, { target := 116, numerator := 1082370076615659582506454220800 }, { target := 117, numerator := 82205322274607056899224371200 }, { target := 118, numerator := 95906209320374899715761766400 }, { target := 119, numerator := 84945499683760625462531850240 }, { target := 1017, numerator := 26520810167795927520116736 }, { target := 1018, numerator := 707221604474558067203112960 }, { target := 1019, numerator := 676280659278796151762976768 }, { target := 1020, numerator := 22100675139829939600097280 }, { target := 1021, numerator := 693961199390660103443054592 }, { target := 1022, numerator := 22100675139829939600097280 }, { target := 1023, numerator := 676280659278796151762976768 }, { target := 1024, numerator := 384551747433040949041692672 }, { target := 1025, numerator := 693961199390660103443054592 }, { target := 1026, numerator := 10833750953544636391967686656 }, { target := 1027, numerator := 424332962684734840321867776 }, { target := 1028, numerator := 707221604474558067203112960 }, { target := 1029, numerator := 676280659278796151762976768 }, { target := 1030, numerator := 22100675139829939600097280 }, { target := 1031, numerator := 424332962684734840321867776 }, { target := 1032, numerator := 22100675139829939600097280 }, { target := 1033, numerator := 680700794306762139682996224 }, { target := 1034, numerator := 384551747433040949041692672 }, { target := 1035, numerator := 26520810167795927520116736 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk20

namespace RouteChunk21

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot21.Left5.expected,
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected,
    Slot22.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 5, numerator := 4117524953640217737795993600 }, { target := 6, numerator := 82515200070949963465431711744 }, { target := 7, numerator := 138513539440456924699457224704 }, { target := 8, numerator := 132913705503506228576054673408 }, { target := 9, numerator := 4117524953640217737795993600 }, { target := 10, numerator := 132913705503506228576054673408 }, { target := 11, numerator := 88773838000483094426881622016 }, { target := 12, numerator := 4282225951785826447307833344 }, { target := 13, numerator := 82515200070949963465431711744 }, { target := 14, numerator := 3952823955494609028284153856 }, { target := 94, numerator := 14976325829320444678766592000 }, { target := 95, numerator := 300125569619581711362482503680 }, { target := 96, numerator := 503803600898339758993708154880 }, { target := 97, numerator := 483435797770463954230585589760 }, { target := 98, numerator := 14976325829320444678766592000 }, { target := 99, numerator := 483435797770463954230585589760 }, { target := 100, numerator := 322889584880148787274207723520 }, { target := 101, numerator := 15575378862493262465917255680 }, { target := 102, numerator := 300125569619581711362482503680 }, { target := 103, numerator := 14377272796147626891615928320 }, { target := 216, numerator := 4117524953640217737795993600 }, { target := 217, numerator := 82515200070949963465431711744 }, { target := 218, numerator := 138513539440456924699457224704 }, { target := 219, numerator := 132913705503506228576054673408 }, { target := 220, numerator := 4117524953640217737795993600 }, { target := 221, numerator := 132913705503506228576054673408 }, { target := 222, numerator := 88773838000483094426881622016 }, { target := 223, numerator := 4282225951785826447307833344 }, { target := 224, numerator := 82515200070949963465431711744 }, { target := 225, numerator := 3952823955494609028284153856 }, { target := 226, numerator := 95906185835363850874288865280 }, { target := 227, numerator := 98646362573517103756411404288 }, { target := 228, numerator := 95906185835363850874288865280 }, { target := 229, numerator := 84945478882750839345798709248 }, { target := 230, numerator := 3975996447060369931959804100608 }, { target := 231, numerator := 1082369811570534888438402908160 }, { target := 232, numerator := 98646362573517103756411404288 }, { target := 233, numerator := 3975996447060369931959804100608 }, { target := 234, numerator := 95906185835363850874288865280 }, { target := 235, numerator := 95906185835363850874288865280 }, { target := 236, numerator := 82205302144597586463676170240 }, { target := 237, numerator := 95906185835363850874288865280 }, { target := 238, numerator := 1082369811570534888438402908160 }, { target := 239, numerator := 82205302144597586463676170240 }, { target := 240, numerator := 95906185835363850874288865280 }, { target := 241, numerator := 84945478882750839345798709248 }, { target := 624, numerator := 2597089946836134280770355200 }, { target := 625, numerator := 2671292516745738117363793920 }, { target := 626, numerator := 2597089946836134280770355200 }, { target := 627, numerator := 2300279667197718934396600320 }, { target := 628, numerator := 107667928938835166897079582720 }, { target := 629, numerator := 29310015114293515454408294400 }, { target := 630, numerator := 2671292516745738117363793920 }, { target := 631, numerator := 107667928938835166897079582720 }, { target := 632, numerator := 2597089946836134280770355200 }, { target := 633, numerator := 2597089946836134280770355200 }, { target := 634, numerator := 2226077097288115097803161600 }, { target := 635, numerator := 2597089946836134280770355200 }, { target := 636, numerator := 29310015114293515454408294400 }, { target := 637, numerator := 2226077097288115097803161600 }, { target := 638, numerator := 2597089946836134280770355200 }, { target := 639, numerator := 2300279667197718934396600320 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk21

namespace RouteChunk22

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left0.expected,
    Slot23.Left2.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 79228162514264337593543950336 }, { target := 1, numerator := 51742037415766227970686976000 }, { target := 2, numerator := 47293189338896608369469030400 }, { target := 3, numerator := 51742037415766227970686976000 }, { target := 4, numerator := 47293189338896608369469030400 }, { target := 90, numerator := 51742012743246029384161689600 }, { target := 91, numerator := 47293166787751978259542179840 }, { target := 92, numerator := 51742012743246029384161689600 }, { target := 93, numerator := 47293166787751978259542179840 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk22

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
