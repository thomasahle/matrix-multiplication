import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 291, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 200, numerator := 2597066461825085439297454080 }, some { target := 202, numerator := 95906209320374899715761766400 }, some { target := 205, numerator := 95906185835363850874288865280 }, some { target := 212, numerator := 2597089946836134280770355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 2671268360734373594705952768 }, some { target := 298, numerator := 98646386729528468279069245440 }, some { target := 301, numerator := 98646362573517103756411404288 }, some { target := 308, numerator := 2671292516745738117363793920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 2597066461825085439297454080 }, some { target := 333, numerator := 95906209320374899715761766400 }, some { target := 336, numerator := 95906185835363850874288865280 }, some { target := 343, numerator := 2597089946836134280770355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 2300258866187932817663459328 }, some { target := 469, numerator := 84945499683760625462531850240 }, some { target := 472, numerator := 84945478882750839345798709248 }, some { target := 479, numerator := 2300279667197718934396600320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 107666955317377113497731596288 }, some { target := 565, numerator := 3975997420681827985359152087040 }, some { target := 568, numerator := 3975996447060369931959804100608 }, some { target := 575, numerator := 107667928938835166897079582720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 29309750069168821386356981760 }, some { target := 600, numerator := 1082370076615659582506454220800 }, some { target := 603, numerator := 1082369811570534888438402908160 }, some { target := 610, numerator := 29310015114293515454408294400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 2671268360734373594705952768 }, some { target := 661, numerator := 98646386729528468279069245440 }, some { target := 664, numerator := 98646362573517103756411404288 }, some { target := 671, numerator := 2671292516745738117363793920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 107666955317377113497731596288 }, some { target := 696, numerator := 3975997420681827985359152087040 }, some { target := 699, numerator := 3975996447060369931959804100608 }, some { target := 706, numerator := 107667928938835166897079582720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 2597066461825085439297454080 }, some { target := 722, numerator := 95906209320374899715761766400 }, some { target := 725, numerator := 95906185835363850874288865280 }, some { target := 732, numerator := 2597089946836134280770355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 2597066461825085439297454080 }, some { target := 832, numerator := 95906209320374899715761766400 }, some { target := 835, numerator := 95906185835363850874288865280 }, some { target := 842, numerator := 2597089946836134280770355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 2226056967278644662254960640 }, some { target := 867, numerator := 82205322274607056899224371200 }, some { target := 870, numerator := 82205302144597586463676170240 }, some { target := 877, numerator := 2226077097288115097803161600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 2597066461825085439297454080 }, some { target := 928, numerator := 95906209320374899715761766400 }, some { target := 931, numerator := 95906185835363850874288865280 }, some { target := 938, numerator := 2597089946836134280770355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 29309750069168821386356981760 }, some { target := 963, numerator := 1082370076615659582506454220800 }, some { target := 966, numerator := 1082369811570534888438402908160 }, some { target := 973, numerator := 29310015114293515454408294400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 2226056967278644662254960640 }, some { target := 989, numerator := 82205322274607056899224371200 }, some { target := 992, numerator := 82205302144597586463676170240 }, some { target := 999, numerator := 2226077097288115097803161600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 2597066461825085439297454080 }, some { target := 1038, numerator := 95906209320374899715761766400 }, some { target := 1041, numerator := 95906185835363850874288865280 }, some { target := 1048, numerator := 2597089946836134280770355200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 2300258866187932817663459328 }, some { target := 1064, numerator := 84945499683760625462531850240 }, some { target := 1067, numerator := 84945478882750839345798709248 }, some { target := 1074, numerator := 2300279667197718934396600320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 150, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 21250649172913403461632000 }, some { target := 72, numerator := 357010906104945178155417600 }, some { target := 73, numerator := 773523629894047886003404800 }, some { target := 74, numerator := 25500779007496084153958400 }, some { target := 75, numerator := 408012464119937346463334400 }, some { target := 76, numerator := 29750908842078764846284800 }, some { target := 77, numerator := 773523629894047886003404800 }, some { target := 78, numerator := 773523629894047886003404800 }, some { target := 79, numerator := 408012464119937346463334400 }, some { target := 80, numerator := 9545791608472700834965094400 }, some { target := 81, numerator := 765023370224882524618752000 }, some { target := 82, numerator := 357010906104945178155417600 }, some { target := 83, numerator := 773523629894047886003404800 }, some { target := 84, numerator := 29750908842078764846284800 }, some { target := 85, numerator := 765023370224882524618752000 }, some { target := 86, numerator := 29750908842078764846284800 }, some { target := 87, numerator := 773523629894047886003404800 }, some { target := 88, numerator := 773523629894047886003404800 }, some { target := 89, numerator := 25500779007496084153958400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 566683977944357425643520000 }, some { target := 147, numerator := 9520290829465204750811136000 }, some { target := 148, numerator := 20627296797174610293424128000 }, some { target := 149, numerator := 680020773533228910772224000 }, some { target := 150, numerator := 10880332376531662572355584000 }, some { target := 151, numerator := 793357569122100395900928000 }, some { target := 152, numerator := 20627296797174610293424128000 }, some { target := 153, numerator := 20627296797174610293424128000 }, some { target := 154, numerator := 10880332376531662572355584000 }, some { target := 155, numerator := 254554442892605355599069184000 }, some { target := 156, numerator := 20400623205996867323166720000 }, some { target := 157, numerator := 9520290829465204750811136000 }, some { target := 158, numerator := 20627296797174610293424128000 }, some { target := 159, numerator := 793357569122100395900928000 }, some { target := 160, numerator := 20400623205996867323166720000 }, some { target := 161, numerator := 793357569122100395900928000 }, some { target := 162, numerator := 20627296797174610293424128000 }, some { target := 163, numerator := 20627296797174610293424128000 }, some { target := 164, numerator := 680020773533228910772224000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 541891553909291788271616000 }, some { target := 182, numerator := 9103778105676102042963148800 }, some { target := 183, numerator := 19724852562298221093086822400 }, some { target := 184, numerator := 650269864691150145925939200 }, some { target := 185, numerator := 10404317835058402334815027200 }, some { target := 186, numerator := 758648175473008503580262400 }, some { target := 187, numerator := 19724852562298221093086822400 }, some { target := 188, numerator := 19724852562298221093086822400 }, some { target := 189, numerator := 10404317835058402334815027200 }, some { target := 190, numerator := 243417686016053871291609907200 }, some { target := 191, numerator := 19508095940734504377778176000 }, some { target := 192, numerator := 9103778105676102042963148800 }, some { target := 193, numerator := 19724852562298221093086822400 }, some { target := 194, numerator := 758648175473008503580262400 }, some { target := 195, numerator := 19508095940734504377778176000 }, some { target := 196, numerator := 758648175473008503580262400 }, some { target := 197, numerator := 19724852562298221093086822400 }, some { target := 198, numerator := 19724852562298221093086822400 }, some { target := 199, numerator := 650269864691150145925939200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 17708874310761169551360000 }, some { target := 243, numerator := 297509088420787648462848000 }, some { target := 244, numerator := 644603024911706571669504000 }, some { target := 245, numerator := 21250649172913403461632000 }, some { target := 246, numerator := 340010386766614455386112000 }, some { target := 247, numerator := 24792424035065637371904000 }, some { target := 248, numerator := 644603024911706571669504000 }, some { target := 249, numerator := 644603024911706571669504000 }, some { target := 250, numerator := 340010386766614455386112000 }, some { target := 251, numerator := 7954826340393917362470912000 }, some { target := 252, numerator := 637519475187402103848960000 }, some { target := 253, numerator := 297509088420787648462848000 }, some { target := 254, numerator := 644603024911706571669504000 }, some { target := 255, numerator := 24792424035065637371904000 }, some { target := 256, numerator := 637519475187402103848960000 }, some { target := 257, numerator := 24792424035065637371904000 }, some { target := 258, numerator := 644603024911706571669504000 }, some { target := 259, numerator := 644603024911706571669504000 }, some { target := 260, numerator := 21250649172913403461632000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 556058653357900723912704000 }, some { target := 278, numerator := 9341785376412732161733427200 }, some { target := 279, numerator := 20240534982227586350422425600 }, some { target := 280, numerator := 667270384029480868695244800 }, some { target := 281, numerator := 10676326144471693899123916800 }, some { target := 282, numerator := 778482114701061013477785600 }, some { target := 283, numerator := 20240534982227586350422425600 }, some { target := 284, numerator := 20240534982227586350422425600 }, some { target := 285, numerator := 10676326144471693899123916800 }, some { target := 286, numerator := 249781547088369005181586636800 }, some { target := 287, numerator := 20018111520884426060857344000 }, some { target := 288, numerator := 9341785376412732161733427200 }, some { target := 289, numerator := 20240534982227586350422425600 }, some { target := 290, numerator := 778482114701061013477785600 }, some { target := 291, numerator := 20018111520884426060857344000 }, some { target := 292, numerator := 778482114701061013477785600 }, some { target := 293, numerator := 20240534982227586350422425600 }, some { target := 294, numerator := 20240534982227586350422425600 }, some { target := 295, numerator := 667270384029480868695244800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 17708874310761169551360000 }, some { target := 313, numerator := 297509088420787648462848000 }, some { target := 314, numerator := 644603024911706571669504000 }, some { target := 315, numerator := 21250649172913403461632000 }, some { target := 316, numerator := 340010386766614455386112000 }, some { target := 317, numerator := 24792424035065637371904000 }, some { target := 318, numerator := 644603024911706571669504000 }, some { target := 319, numerator := 644603024911706571669504000 }, some { target := 320, numerator := 340010386766614455386112000 }, some { target := 321, numerator := 7954826340393917362470912000 }, some { target := 322, numerator := 637519475187402103848960000 }, some { target := 323, numerator := 297509088420787648462848000 }, some { target := 324, numerator := 644603024911706571669504000 }, some { target := 325, numerator := 24792424035065637371904000 }, some { target := 326, numerator := 637519475187402103848960000 }, some { target := 327, numerator := 24792424035065637371904000 }, some { target := 328, numerator := 644603024911706571669504000 }, some { target := 329, numerator := 644603024911706571669504000 }, some { target := 330, numerator := 21250649172913403461632000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 541891553909291788271616000 }, some { target := 414, numerator := 9103778105676102042963148800 }, some { target := 415, numerator := 19724852562298221093086822400 }, some { target := 416, numerator := 650269864691150145925939200 }, some { target := 417, numerator := 10404317835058402334815027200 }, some { target := 418, numerator := 758648175473008503580262400 }, some { target := 419, numerator := 19724852562298221093086822400 }, some { target := 420, numerator := 19724852562298221093086822400 }, some { target := 421, numerator := 10404317835058402334815027200 }, some { target := 422, numerator := 243417686016053871291609907200 }, some { target := 423, numerator := 19508095940734504377778176000 }, some { target := 424, numerator := 9103778105676102042963148800 }, some { target := 425, numerator := 19724852562298221093086822400 }, some { target := 426, numerator := 758648175473008503580262400 }, some { target := 427, numerator := 19508095940734504377778176000 }, some { target := 428, numerator := 758648175473008503580262400 }, some { target := 429, numerator := 19724852562298221093086822400 }, some { target := 430, numerator := 19724852562298221093086822400 }, some { target := 431, numerator := 650269864691150145925939200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 308134413007244350193664000 }, some { target := 449, numerator := 5176658138521705083253555200 }, some { target := 450, numerator := 11216092633463694347049369600 }, some { target := 451, numerator := 369761295608693220232396800 }, some { target := 452, numerator := 5916180729739091523718348800 }, some { target := 453, numerator := 431388178210142090271129600 }, some { target := 454, numerator := 11216092633463694347049369600 }, some { target := 455, numerator := 11216092633463694347049369600 }, some { target := 456, numerator := 5916180729739091523718348800 }, some { target := 457, numerator := 138413978322854162106993868800 }, some { target := 458, numerator := 11092838868260796606971904000 }, some { target := 459, numerator := 5176658138521705083253555200 }, some { target := 460, numerator := 11216092633463694347049369600 }, some { target := 461, numerator := 431388178210142090271129600 }, some { target := 462, numerator := 11092838868260796606971904000 }, some { target := 463, numerator := 431388178210142090271129600 }, some { target := 464, numerator := 11216092633463694347049369600 }, some { target := 465, numerator := 11216092633463694347049369600 }, some { target := 466, numerator := 369761295608693220232396800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 556058653357900723912704000 }, some { target := 510, numerator := 9341785376412732161733427200 }, some { target := 511, numerator := 20240534982227586350422425600 }, some { target := 512, numerator := 667270384029480868695244800 }, some { target := 513, numerator := 10676326144471693899123916800 }, some { target := 514, numerator := 778482114701061013477785600 }, some { target := 515, numerator := 20240534982227586350422425600 }, some { target := 516, numerator := 20240534982227586350422425600 }, some { target := 517, numerator := 10676326144471693899123916800 }, some { target := 518, numerator := 249781547088369005181586636800 }, some { target := 519, numerator := 20018111520884426060857344000 }, some { target := 520, numerator := 9341785376412732161733427200 }, some { target := 521, numerator := 20240534982227586350422425600 }, some { target := 522, numerator := 778482114701061013477785600 }, some { target := 523, numerator := 20018111520884426060857344000 }, some { target := 524, numerator := 778482114701061013477785600 }, some { target := 525, numerator := 20240534982227586350422425600 }, some { target := 526, numerator := 20240534982227586350422425600 }, some { target := 527, numerator := 667270384029480868695244800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 8680890187135125314076672000 }, some { target := 545, numerator := 145838955143870105276488089600 }, some { target := 546, numerator := 315984402811718561432390860800 }, some { target := 547, numerator := 10417068224562150376892006400 }, some { target := 548, numerator := 166673091592994406030272102400 }, some { target := 549, numerator := 12153246261989175439707340800 }, some { target := 550, numerator := 315984402811718561432390860800 }, some { target := 551, numerator := 315984402811718561432390860800 }, some { target := 552, numerator := 166673091592994406030272102400 }, some { target := 553, numerator := 3899455872061098291083241062400 }, some { target := 554, numerator := 312512046736864511306760192000 }, some { target := 555, numerator := 145838955143870105276488089600 }, some { target := 556, numerator := 315984402811718561432390860800 }, some { target := 557, numerator := 12153246261989175439707340800 }, some { target := 558, numerator := 312512046736864511306760192000 }, some { target := 559, numerator := 12153246261989175439707340800 }, some { target := 560, numerator := 315984402811718561432390860800 }, some { target := 561, numerator := 315984402811718561432390860800 }, some { target := 562, numerator := 10417068224562150376892006400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 340010386766614455386112000 }, some { target := 580, numerator := 5712174497679122850486681600 }, some { target := 581, numerator := 12376378078304766176054476800 }, some { target := 582, numerator := 408012464119937346463334400 }, some { target := 583, numerator := 6528199425918997543413350400 }, some { target := 584, numerator := 476014541473260237540556800 }, some { target := 585, numerator := 12376378078304766176054476800 }, some { target := 586, numerator := 12376378078304766176054476800 }, some { target := 587, numerator := 6528199425918997543413350400 }, some { target := 588, numerator := 152732665735563213359441510400 }, some { target := 589, numerator := 12240373923598120393900032000 }, some { target := 590, numerator := 5712174497679122850486681600 }, some { target := 591, numerator := 12376378078304766176054476800 }, some { target := 592, numerator := 476014541473260237540556800 }, some { target := 593, numerator := 12240373923598120393900032000 }, some { target := 594, numerator := 476014541473260237540556800 }, some { target := 595, numerator := 12376378078304766176054476800 }, some { target := 596, numerator := 12376378078304766176054476800 }, some { target := 597, numerator := 408012464119937346463334400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 566683977944357425643520000 }, some { target := 641, numerator := 9520290829465204750811136000 }, some { target := 642, numerator := 20627296797174610293424128000 }, some { target := 643, numerator := 680020773533228910772224000 }, some { target := 644, numerator := 10880332376531662572355584000 }, some { target := 645, numerator := 793357569122100395900928000 }, some { target := 646, numerator := 20627296797174610293424128000 }, some { target := 647, numerator := 20627296797174610293424128000 }, some { target := 648, numerator := 10880332376531662572355584000 }, some { target := 649, numerator := 254554442892605355599069184000 }, some { target := 650, numerator := 20400623205996867323166720000 }, some { target := 651, numerator := 9520290829465204750811136000 }, some { target := 652, numerator := 20627296797174610293424128000 }, some { target := 653, numerator := 793357569122100395900928000 }, some { target := 654, numerator := 20400623205996867323166720000 }, some { target := 655, numerator := 793357569122100395900928000 }, some { target := 656, numerator := 20627296797174610293424128000 }, some { target := 657, numerator := 20627296797174610293424128000 }, some { target := 658, numerator := 680020773533228910772224000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 541891553909291788271616000 }, some { target := 676, numerator := 9103778105676102042963148800 }, some { target := 677, numerator := 19724852562298221093086822400 }, some { target := 678, numerator := 650269864691150145925939200 }, some { target := 679, numerator := 10404317835058402334815027200 }, some { target := 680, numerator := 758648175473008503580262400 }, some { target := 681, numerator := 19724852562298221093086822400 }, some { target := 682, numerator := 19724852562298221093086822400 }, some { target := 683, numerator := 10404317835058402334815027200 }, some { target := 684, numerator := 243417686016053871291609907200 }, some { target := 685, numerator := 19508095940734504377778176000 }, some { target := 686, numerator := 9103778105676102042963148800 }, some { target := 687, numerator := 19724852562298221093086822400 }, some { target := 688, numerator := 758648175473008503580262400 }, some { target := 689, numerator := 19508095940734504377778176000 }, some { target := 690, numerator := 758648175473008503580262400 }, some { target := 691, numerator := 19724852562298221093086822400 }, some { target := 692, numerator := 19724852562298221093086822400 }, some { target := 693, numerator := 650269864691150145925939200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 17708874310761169551360000 }, some { target := 777, numerator := 297509088420787648462848000 }, some { target := 778, numerator := 644603024911706571669504000 }, some { target := 779, numerator := 21250649172913403461632000 }, some { target := 780, numerator := 340010386766614455386112000 }, some { target := 781, numerator := 24792424035065637371904000 }, some { target := 782, numerator := 644603024911706571669504000 }, some { target := 783, numerator := 644603024911706571669504000 }, some { target := 784, numerator := 340010386766614455386112000 }, some { target := 785, numerator := 7954826340393917362470912000 }, some { target := 786, numerator := 637519475187402103848960000 }, some { target := 787, numerator := 297509088420787648462848000 }, some { target := 788, numerator := 644603024911706571669504000 }, some { target := 789, numerator := 24792424035065637371904000 }, some { target := 790, numerator := 637519475187402103848960000 }, some { target := 791, numerator := 24792424035065637371904000 }, some { target := 792, numerator := 644603024911706571669504000 }, some { target := 793, numerator := 644603024911706571669504000 }, some { target := 794, numerator := 21250649172913403461632000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 340010386766614455386112000 }, some { target := 812, numerator := 5712174497679122850486681600 }, some { target := 813, numerator := 12376378078304766176054476800 }, some { target := 814, numerator := 408012464119937346463334400 }, some { target := 815, numerator := 6528199425918997543413350400 }, some { target := 816, numerator := 476014541473260237540556800 }, some { target := 817, numerator := 12376378078304766176054476800 }, some { target := 818, numerator := 12376378078304766176054476800 }, some { target := 819, numerator := 6528199425918997543413350400 }, some { target := 820, numerator := 152732665735563213359441510400 }, some { target := 821, numerator := 12240373923598120393900032000 }, some { target := 822, numerator := 5712174497679122850486681600 }, some { target := 823, numerator := 12376378078304766176054476800 }, some { target := 824, numerator := 476014541473260237540556800 }, some { target := 825, numerator := 12240373923598120393900032000 }, some { target := 826, numerator := 476014541473260237540556800 }, some { target := 827, numerator := 12376378078304766176054476800 }, some { target := 828, numerator := 12376378078304766176054476800 }, some { target := 829, numerator := 408012464119937346463334400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 17708874310761169551360000 }, some { target := 847, numerator := 297509088420787648462848000 }, some { target := 848, numerator := 644603024911706571669504000 }, some { target := 849, numerator := 21250649172913403461632000 }, some { target := 850, numerator := 340010386766614455386112000 }, some { target := 851, numerator := 24792424035065637371904000 }, some { target := 852, numerator := 644603024911706571669504000 }, some { target := 853, numerator := 644603024911706571669504000 }, some { target := 854, numerator := 340010386766614455386112000 }, some { target := 855, numerator := 7954826340393917362470912000 }, some { target := 856, numerator := 637519475187402103848960000 }, some { target := 857, numerator := 297509088420787648462848000 }, some { target := 858, numerator := 644603024911706571669504000 }, some { target := 859, numerator := 24792424035065637371904000 }, some { target := 860, numerator := 637519475187402103848960000 }, some { target := 861, numerator := 24792424035065637371904000 }, some { target := 862, numerator := 644603024911706571669504000 }, some { target := 863, numerator := 644603024911706571669504000 }, some { target := 864, numerator := 21250649172913403461632000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 545433328771444022181888000 }, some { target := 908, numerator := 9163279923360259572655718400 }, some { target := 909, numerator := 19853773167280562407420723200 }, some { target := 910, numerator := 654519994525732826618265600 }, some { target := 911, numerator := 10472319912411725225892249600 }, some { target := 912, numerator := 763606660280021631054643200 }, some { target := 913, numerator := 19853773167280562407420723200 }, some { target := 914, numerator := 19853773167280562407420723200 }, some { target := 915, numerator := 10472319912411725225892249600 }, some { target := 916, numerator := 245008651284132654764104089600 }, some { target := 917, numerator := 19635599835771984798547968000 }, some { target := 918, numerator := 9163279923360259572655718400 }, some { target := 919, numerator := 19853773167280562407420723200 }, some { target := 920, numerator := 763606660280021631054643200 }, some { target := 921, numerator := 19635599835771984798547968000 }, some { target := 922, numerator := 763606660280021631054643200 }, some { target := 923, numerator := 19853773167280562407420723200 }, some { target := 924, numerator := 19853773167280562407420723200 }, some { target := 925, numerator := 654519994525732826618265600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 308134413007244350193664000 }, some { target := 943, numerator := 5176658138521705083253555200 }, some { target := 944, numerator := 11216092633463694347049369600 }, some { target := 945, numerator := 369761295608693220232396800 }, some { target := 946, numerator := 5916180729739091523718348800 }, some { target := 947, numerator := 431388178210142090271129600 }, some { target := 948, numerator := 11216092633463694347049369600 }, some { target := 949, numerator := 11216092633463694347049369600 }, some { target := 950, numerator := 5916180729739091523718348800 }, some { target := 951, numerator := 138413978322854162106993868800 }, some { target := 952, numerator := 11092838868260796606971904000 }, some { target := 953, numerator := 5176658138521705083253555200 }, some { target := 954, numerator := 11216092633463694347049369600 }, some { target := 955, numerator := 431388178210142090271129600 }, some { target := 956, numerator := 11092838868260796606971904000 }, some { target := 957, numerator := 431388178210142090271129600 }, some { target := 958, numerator := 11216092633463694347049369600 }, some { target := 959, numerator := 11216092633463694347049369600 }, some { target := 960, numerator := 369761295608693220232396800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 21250649172913403461632000 }, some { target := 1018, numerator := 357010906104945178155417600 }, some { target := 1019, numerator := 773523629894047886003404800 }, some { target := 1020, numerator := 25500779007496084153958400 }, some { target := 1021, numerator := 408012464119937346463334400 }, some { target := 1022, numerator := 29750908842078764846284800 }, some { target := 1023, numerator := 773523629894047886003404800 }, some { target := 1024, numerator := 773523629894047886003404800 }, some { target := 1025, numerator := 408012464119937346463334400 }, some { target := 1026, numerator := 9545791608472700834965094400 }, some { target := 1027, numerator := 765023370224882524618752000 }, some { target := 1028, numerator := 357010906104945178155417600 }, some { target := 1029, numerator := 773523629894047886003404800 }, some { target := 1030, numerator := 29750908842078764846284800 }, some { target := 1031, numerator := 765023370224882524618752000 }, some { target := 1032, numerator := 29750908842078764846284800 }, some { target := 1033, numerator := 773523629894047886003404800 }, some { target := 1034, numerator := 773523629894047886003404800 }, some { target := 1035, numerator := 25500779007496084153958400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
