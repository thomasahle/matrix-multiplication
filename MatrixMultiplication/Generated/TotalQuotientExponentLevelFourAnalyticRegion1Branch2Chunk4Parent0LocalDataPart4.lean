import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 18; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 122, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 6, 14]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 121, numerator := 83200525039720890894385152 }, some { target := 122, numerator := 2218680667725890423850270720 }, some { target := 123, numerator := 2121613388512882717806821376 }, some { target := 124, numerator := 69333770866434075745320960 }, some { target := 125, numerator := 2177080405206029978403078144 }, some { target := 126, numerator := 69333770866434075745320960 }, some { target := 127, numerator := 2121613388512882717806821376 }, some { target := 128, numerator := 1206407613075952917968584704 }, some { target := 129, numerator := 2177080405206029978403078144 }, some { target := 130, numerator := 33987414478725983930356334592 }, some { target := 131, numerator := 1331208400635534254310162432 }, some { target := 132, numerator := 2218680667725890423850270720 }, some { target := 133, numerator := 2121613388512882717806821376 }, some { target := 134, numerator := 69333770866434075745320960 }, some { target := 135, numerator := 1331208400635534254310162432 }, some { target := 136, numerator := 69333770866434075745320960 }, some { target := 137, numerator := 2135480142686169532955885568 }, some { target := 138, numerator := 1206407613075952917968584704 }, some { target := 139, numerator := 83200525039720890894385152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 6996269074623547556184981504 }, some { target := 197, numerator := 186567175323294601498266173440 }, some { target := 198, numerator := 178404861402900462682717028352 }, some { target := 199, numerator := 5830224228852956296820817920 }, some { target := 200, numerator := 183069040785982827720173682688 }, some { target := 201, numerator := 5830224228852956296820817920 }, some { target := 202, numerator := 178404861402900462682717028352 }, some { target := 203, numerator := 101445901582041439564682231808 }, some { target := 204, numerator := 183069040785982827720173682688 }, some { target := 205, numerator := 2857975916983719176701564944384 }, some { target := 206, numerator := 111940305193976760898959704064 }, some { target := 207, numerator := 186567175323294601498266173440 }, some { target := 208, numerator := 178404861402900462682717028352 }, some { target := 209, numerator := 5830224228852956296820817920 }, some { target := 210, numerator := 111940305193976760898959704064 }, some { target := 211, numerator := 5830224228852956296820817920 }, some { target := 212, numerator := 179570906248671053942081191936 }, some { target := 213, numerator := 101445901582041439564682231808 }, some { target := 214, numerator := 6996269074623547556184981504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 6996267386746464811761008640 }, some { target := 509, numerator := 186567130313239061646960230400 }, some { target := 510, numerator := 178404818362034852699905720320 }, some { target := 511, numerator := 5830222822288720676467507200 }, some { target := 512, numerator := 183068996619865829241079726080 }, some { target := 513, numerator := 5830222822288720676467507200 }, some { target := 514, numerator := 178404818362034852699905720320 }, some { target := 515, numerator := 101445877107823739770534625280 }, some { target := 516, numerator := 183068996619865829241079726080 }, some { target := 517, numerator := 2857975227485930875604372029440 }, some { target := 518, numerator := 111940278187943436988176138240 }, some { target := 519, numerator := 186567130313239061646960230400 }, some { target := 520, numerator := 178404818362034852699905720320 }, some { target := 521, numerator := 5830222822288720676467507200 }, some { target := 522, numerator := 111940278187943436988176138240 }, some { target := 523, numerator := 5830222822288720676467507200 }, some { target := 524, numerator := 179570862926492596835199221760 }, some { target := 525, numerator := 101445877107823739770534625280 }, some { target := 526, numerator := 6996267386746464811761008640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 83202212916803635318358016 }, some { target := 907, numerator := 2218725677781430275156213760 }, some { target := 908, numerator := 2121656429378492700618129408 }, some { target := 909, numerator := 69335177430669696098631680 }, some { target := 910, numerator := 2177124571323028457497034752 }, some { target := 911, numerator := 69335177430669696098631680 }, some { target := 912, numerator := 2121656429378492700618129408 }, some { target := 913, numerator := 1206432087293652712116191232 }, some { target := 914, numerator := 2177124571323028457497034752 }, some { target := 915, numerator := 33988103976514285027549249536 }, some { target := 916, numerator := 1331235406668858165093728256 }, some { target := 917, numerator := 2218725677781430275156213760 }, some { target := 918, numerator := 2121656429378492700618129408 }, some { target := 919, numerator := 69335177430669696098631680 }, some { target := 920, numerator := 1331235406668858165093728256 }, some { target := 921, numerator := 69335177430669696098631680 }, some { target := 922, numerator := 2135523464864626639837855744 }, some { target := 923, numerator := 1206432087293652712116191232 }, some { target := 924, numerator := 83202212916803635318358016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left6.expected ++ Left14.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left6.routed_eq, Left14.routed_eq]
  rfl

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 383, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 3, 11, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 34, numerator := 141165173234373194437099520 }, some { target := 35, numerator := 145198463898212428563873792 }, some { target := 36, numerator := 141165173234373194437099520 }, some { target := 37, numerator := 125032010579016257930002432 }, some { target := 38, numerator := 5852304753230728717949468672 }, some { target := 39, numerator := 1593149812216497480075837440 }, some { target := 40, numerator := 145198463898212428563873792 }, some { target := 41, numerator := 5852304753230728717949468672 }, some { target := 42, numerator := 141165173234373194437099520 }, some { target := 43, numerator := 141165173234373194437099520 }, some { target := 44, numerator := 120998719915177023803228160 }, some { target := 45, numerator := 141165173234373194437099520 }, some { target := 46, numerator := 1593149812216497480075837440 }, some { target := 47, numerator := 120998719915177023803228160 }, some { target := 48, numerator := 141165173234373194437099520 }, some { target := 49, numerator := 125032010579016257930002432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 20849357341886550439698104320 }, some { target := 80, numerator := 21445053265940451880832335872 }, some { target := 81, numerator := 20849357341886550439698104320 }, some { target := 82, numerator := 18466573645670944675161178112 }, some { target := 83, numerator := 864354785802210991085769981952 }, some { target := 84, numerator := 235299890001291069248021463040 }, some { target := 85, numerator := 21445053265940451880832335872 }, some { target := 86, numerator := 864354785802210991085769981952 }, some { target := 87, numerator := 20849357341886550439698104320 }, some { target := 88, numerator := 20849357341886550439698104320 }, some { target := 89, numerator := 17870877721617043234026946560 }, some { target := 90, numerator := 20849357341886550439698104320 }, some { target := 91, numerator := 235299890001291069248021463040 }, some { target := 92, numerator := 17870877721617043234026946560 }, some { target := 93, numerator := 20849357341886550439698104320 }, some { target := 94, numerator := 18466573645670944675161178112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 217309364760703818122710220800 }, some { target := 155, numerator := 223518203753866784354787655680 }, some { target := 156, numerator := 217309364760703818122710220800 }, some { target := 157, numerator := 192474008788051953194400481280 }, some { target := 158, numerator := 9009025379079464002744358010880 }, some { target := 159, numerator := 2452491402299371661670586777600 }, some { target := 160, numerator := 223518203753866784354787655680 }, some { target := 161, numerator := 9009025379079464002744358010880 }, some { target := 162, numerator := 217309364760703818122710220800 }, some { target := 163, numerator := 217309364760703818122710220800 }, some { target := 164, numerator := 186265169794888986962323046400 }, some { target := 165, numerator := 217309364760703818122710220800 }, some { target := 166, numerator := 2452491402299371661670586777600 }, some { target := 167, numerator := 186265169794888986962323046400 }, some { target := 168, numerator := 217309364760703818122710220800 }, some { target := 169, numerator := 192474008788051953194400481280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 20849357341886550439698104320 }, some { target := 493, numerator := 21445053265940451880832335872 }, some { target := 494, numerator := 20849357341886550439698104320 }, some { target := 495, numerator := 18466573645670944675161178112 }, some { target := 496, numerator := 864354785802210991085769981952 }, some { target := 497, numerator := 235299890001291069248021463040 }, some { target := 498, numerator := 21445053265940451880832335872 }, some { target := 499, numerator := 864354785802210991085769981952 }, some { target := 500, numerator := 20849357341886550439698104320 }, some { target := 501, numerator := 20849357341886550439698104320 }, some { target := 502, numerator := 17870877721617043234026946560 }, some { target := 503, numerator := 20849357341886550439698104320 }, some { target := 504, numerator := 235299890001291069248021463040 }, some { target := 505, numerator := 17870877721617043234026946560 }, some { target := 506, numerator := 20849357341886550439698104320 }, some { target := 507, numerator := 18466573645670944675161178112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 141165173234373194437099520 }, some { target := 891, numerator := 145198463898212428563873792 }, some { target := 892, numerator := 141165173234373194437099520 }, some { target := 893, numerator := 125032010579016257930002432 }, some { target := 894, numerator := 5852304753230728717949468672 }, some { target := 895, numerator := 1593149812216497480075837440 }, some { target := 896, numerator := 145198463898212428563873792 }, some { target := 897, numerator := 5852304753230728717949468672 }, some { target := 898, numerator := 141165173234373194437099520 }, some { target := 899, numerator := 141165173234373194437099520 }, some { target := 900, numerator := 120998719915177023803228160 }, some { target := 901, numerator := 141165173234373194437099520 }, some { target := 902, numerator := 1593149812216497480075837440 }, some { target := 903, numerator := 120998719915177023803228160 }, some { target := 904, numerator := 141165173234373194437099520 }, some { target := 905, numerator := 125032010579016257930002432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left3.expected ++ Left11.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left3.routed_eq, Left11.routed_eq, Left18.routed_eq]
  rfl

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 79, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 5, 12]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 512912410722396846791065600 }, some { target := 11, numerator := 10278764710876832809692954624 }, some { target := 12, numerator := 17254373496701429926051446784 }, some { target := 13, numerator := 16556812618118970214415597568 }, some { target := 14, numerator := 512912410722396846791065600 }, some { target := 15, numerator := 16556812618118970214415597568 }, some { target := 16, numerator := 11058391575174876016815374336 }, some { target := 17, numerator := 533428907151292720662708224 }, some { target := 18, numerator := 10278764710876832809692954624 }, some { target := 19, numerator := 492395914293500972919422976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 18588115539188744113566515200 }, some { target := 56, numerator := 372505835405342432035872964608 }, some { target := 57, numerator := 625304206738309351980377571328 }, some { target := 58, numerator := 600024369605012659985927110656 }, some { target := 59, numerator := 18588115539188744113566515200 }, some { target := 60, numerator := 600024369605012659985927110656 }, some { target := 61, numerator := 400759771024909323088494067712 }, some { target := 62, numerator := 19331640160756293878109175808 }, some { target := 63, numerator := 372505835405342432035872964608 }, some { target := 64, numerator := 17844590917621194349023854592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 18588122370248658909134848000 }, some { target := 145, numerator := 372505972299783124539062353920 }, some { target := 146, numerator := 625304436535164885703296286720 }, some { target := 147, numerator := 600024590111626709586872893440 }, some { target := 148, numerator := 18588122370248658909134848000 }, some { target := 149, numerator := 600024590111626709586872893440 }, some { target := 150, numerator := 400759918302561086080947322880 }, some { target := 151, numerator := 19331647265058605265500241920 }, some { target := 152, numerator := 372505972299783124539062353920 }, some { target := 153, numerator := 17844597475438712552769454080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 512905579662482051222732800 }, some { target := 483, numerator := 10278627816436140306503565312 }, some { target := 484, numerator := 17254143699845896203132731392 }, some { target := 485, numerator := 16556592111504920613469814784 }, some { target := 486, numerator := 512905579662482051222732800 }, some { target := 487, numerator := 16556592111504920613469814784 }, some { target := 488, numerator := 11058244297523113024362119168 }, some { target := 489, numerator := 533421802848981333271642112 }, some { target := 490, numerator := 10278627816436140306503565312 }, some { target := 491, numerator := 492389356475982769173823488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left5.expected ++ Left12.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left5.routed_eq, Left12.routed_eq]
  rfl

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 8, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 3, 5]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 30720366777761007579923742720 }, some { target := 2, numerator := 28078989447336696647818149888 }, some { target := 3, numerator := 30720366777761007579923742720 }, some { target := 4, numerator := 28078989447336696647818149888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 104133746698897596607910379520 }, some { target := 52, numerator := 95180190907964345310781636608 }, some { target := 53, numerator := 104133746698897596607910379520 }, some { target := 54, numerator := 95180190907964345310781636608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 30720366777761007579923742720 }, some { target := 141, numerator := 28078989447336696647818149888 }, some { target := 142, numerator := 30720366777761007579923742720 }, some { target := 143, numerator := 28078989447336696647818149888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left3.expected ++ Left5.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left3.routed_eq, Left5.routed_eq]
  rfl

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 1, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 39614081257132168796771975168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 50, numerator := 39614081257132168796771975168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent0
