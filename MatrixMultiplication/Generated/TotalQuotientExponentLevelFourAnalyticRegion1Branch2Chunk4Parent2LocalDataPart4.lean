import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 1772, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 2761156835848366215231700992 }, some { target := 57, numerator := 73630848955956432406178693120 }, some { target := 58, numerator := 70409499314133338488408375296 }, some { target := 59, numerator := 2300964029873638512693084160 }, some { target := 60, numerator := 72250270538032249298562842624 }, some { target := 61, numerator := 2300964029873638512693084160 }, some { target := 62, numerator := 70409499314133338488408375296 }, some { target := 63, numerator := 40036774119801310120859664384 }, some { target := 64, numerator := 72250270538032249298562842624 }, some { target := 65, numerator := 1127932567444057598922149855232 }, some { target := 66, numerator := 44178509373573859443707215872 }, some { target := 67, numerator := 73630848955956432406178693120 }, some { target := 68, numerator := 70409499314133338488408375296 }, some { target := 69, numerator := 2300964029873638512693084160 }, some { target := 70, numerator := 44178509373573859443707215872 }, some { target := 71, numerator := 2300964029873638512693084160 }, some { target := 72, numerator := 70869692120108066190946992128 }, some { target := 73, numerator := 40036774119801310120859664384 }, some { target := 74, numerator := 2761156835848366215231700992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 100065237677293532868576804864 }, some { target := 153, numerator := 2668406338061160876495381463040 }, some { target := 154, numerator := 2551663560770985088148708524032 }, some { target := 155, numerator := 83387698064411277390480670720 }, some { target := 156, numerator := 2618373719222514110061093060608 }, some { target := 157, numerator := 83387698064411277390480670720 }, some { target := 158, numerator := 2551663560770985088148708524032 }, some { target := 159, numerator := 1450945946320756226594363670528 }, some { target := 160, numerator := 2618373719222514110061093060608 }, some { target := 161, numerator := 40876649591174408176813624786944 }, some { target := 162, numerator := 1601043802836696525897228877824 }, some { target := 163, numerator := 2668406338061160876495381463040 }, some { target := 164, numerator := 2551663560770985088148708524032 }, some { target := 165, numerator := 83387698064411277390480670720 }, some { target := 166, numerator := 1601043802836696525897228877824 }, some { target := 167, numerator := 83387698064411277390480670720 }, some { target := 168, numerator := 2568341100383867343626804658176 }, some { target := 169, numerator := 1450945946320756226594363670528 }, some { target := 170, numerator := 100065237677293532868576804864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 100065274450877843808567951360 }, some { target := 284, numerator := 2668407318690075834895145369600 }, some { target := 285, numerator := 2551664498497385017118482759680 }, some { target := 286, numerator := 83387728709064869840473292800 }, some { target := 287, numerator := 2618374681464636912990861393920 }, some { target := 288, numerator := 83387728709064869840473292800 }, some { target := 289, numerator := 2551664498497385017118482759680 }, some { target := 290, numerator := 1450946479537728735224235294720 }, some { target := 291, numerator := 2618374681464636912990861393920 }, some { target := 292, numerator := 40876664613183599195800008130560 }, some { target := 293, numerator := 1601044391214045500937087221760 }, some { target := 294, numerator := 2668407318690075834895145369600 }, some { target := 295, numerator := 2551664498497385017118482759680 }, some { target := 296, numerator := 83387728709064869840473292800 }, some { target := 297, numerator := 1601044391214045500937087221760 }, some { target := 298, numerator := 83387728709064869840473292800 }, some { target := 299, numerator := 2568342044239197991086577418240 }, some { target := 300, numerator := 1450946479537728735224235294720 }, some { target := 301, numerator := 100065274450877843808567951360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 2761120062264055275240554496 }, some { target := 661, numerator := 73629868327041474006414786560 }, some { target := 662, numerator := 70408561587733409518634139648 }, some { target := 663, numerator := 2300933385220046062700462080 }, some { target := 664, numerator := 72249308295909446368794509312 }, some { target := 665, numerator := 2300933385220046062700462080 }, some { target := 666, numerator := 70408561587733409518634139648 }, some { target := 667, numerator := 40036240902828801490988040192 }, some { target := 668, numerator := 72249308295909446368794509312 }, some { target := 669, numerator := 1127917545434866579935766511616 }, some { target := 670, numerator := 44177920996224884403848871936 }, some { target := 671, numerator := 73629868327041474006414786560 }, some { target := 672, numerator := 70408561587733409518634139648 }, some { target := 673, numerator := 2300933385220046062700462080 }, some { target := 674, numerator := 44177920996224884403848871936 }, some { target := 675, numerator := 2300933385220046062700462080 }, some { target := 676, numerator := 70868748264777418731174232064 }, some { target := 677, numerator := 40036240902828801490988040192 }, some { target := 678, numerator := 2761120062264055275240554496 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 452, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 14, numerator := 56775257292544292046074019840 }, some { target := 15, numerator := 58397407500902700390247563264 }, some { target := 16, numerator := 56775257292544292046074019840 }, some { target := 17, numerator := 50286656459110658669379846144 }, some { target := 18, numerator := 2353739952328050507395811508224 }, some { target := 19, numerator := 640749332301571295948549652480 }, some { target := 20, numerator := 58397407500902700390247563264 }, some { target := 21, numerator := 2353739952328050507395811508224 }, some { target := 22, numerator := 56775257292544292046074019840 }, some { target := 23, numerator := 56775257292544292046074019840 }, some { target := 24, numerator := 48664506250752250325206302720 }, some { target := 25, numerator := 56775257292544292046074019840 }, some { target := 26, numerator := 640749332301571295948549652480 }, some { target := 27, numerator := 48664506250752250325206302720 }, some { target := 28, numerator := 56775257292544292046074019840 }, some { target := 29, numerator := 50286656459110658669379846144 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 192452788875766352609479229440 }, some { target := 137, numerator := 197951439986502534112607207424 }, some { target := 138, numerator := 192452788875766352609479229440 }, some { target := 139, numerator := 170458184432821626596967317504 }, some { target := 140, numerator := 7978542761678199361038696054784 }, some { target := 141, numerator := 2171967188740791693735551303680 }, some { target := 142, numerator := 197951439986502534112607207424 }, some { target := 143, numerator := 7978542761678199361038696054784 }, some { target := 144, numerator := 192452788875766352609479229440 }, some { target := 145, numerator := 192452788875766352609479229440 }, some { target := 146, numerator := 164959533322085445093839339520 }, some { target := 147, numerator := 192452788875766352609479229440 }, some { target := 148, numerator := 2171967188740791693735551303680 }, some { target := 149, numerator := 164959533322085445093839339520 }, some { target := 150, numerator := 192452788875766352609479229440 }, some { target := 151, numerator := 170458184432821626596967317504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 56775257292544292046074019840 }, some { target := 268, numerator := 58397407500902700390247563264 }, some { target := 269, numerator := 56775257292544292046074019840 }, some { target := 270, numerator := 50286656459110658669379846144 }, some { target := 271, numerator := 2353739952328050507395811508224 }, some { target := 272, numerator := 640749332301571295948549652480 }, some { target := 273, numerator := 58397407500902700390247563264 }, some { target := 274, numerator := 2353739952328050507395811508224 }, some { target := 275, numerator := 56775257292544292046074019840 }, some { target := 276, numerator := 56775257292544292046074019840 }, some { target := 277, numerator := 48664506250752250325206302720 }, some { target := 278, numerator := 56775257292544292046074019840 }, some { target := 279, numerator := 640749332301571295948549652480 }, some { target := 280, numerator := 48664506250752250325206302720 }, some { target := 281, numerator := 56775257292544292046074019840 }, some { target := 282, numerator := 50286656459110658669379846144 }]

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

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 7, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 4, numerator := 1692496147460480844588646400 }, some { target := 5, numerator := 33917622795108036125556473856 }, some { target := 6, numerator := 56935570400570575611962064896 }, some { target := 7, numerator := 54633775640024321663321505792 }, some { target := 8, numerator := 1692496147460480844588646400 }, some { target := 9, numerator := 54633775640024321663321505792 }, some { target := 10, numerator := 36490216939247967009331216384 }, some { target := 11, numerator := 1760195993358900078372192256 }, some { target := 12, numerator := 33917622795108036125556473856 }, some { target := 13, numerator := 1624796301562061610805100544 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 1692496147460480844588646400 }, some { target := 127, numerator := 33917622795108036125556473856 }, some { target := 128, numerator := 56935570400570575611962064896 }, some { target := 129, numerator := 54633775640024321663321505792 }, some { target := 130, numerator := 1692496147460480844588646400 }, some { target := 131, numerator := 54633775640024321663321505792 }, some { target := 132, numerator := 36490216939247967009331216384 }, some { target := 133, numerator := 1760195993358900078372192256 }, some { target := 134, numerator := 33917622795108036125556473856 }, some { target := 135, numerator := 1624796301562061610805100544 }]

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

end Slot20

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot21

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent2
