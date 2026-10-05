import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 1,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 53, #[140737471578112, 0, 140737505132544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 24091470861352862217888858112 }, some { target := 11, numerator := 17940457024411705906938511360 }, some { target := 12, numerator := 18965625997235231958763569152 }, some { target := 13, numerator := 24604055347764625243801387008 }, some { target := 14, numerator := 329591824762763625661756080128 }, some { target := 15, numerator := 596135757696880399136271106048 }, some { target := 16, numerator := 17940457024411705906938511360 }, some { target := 17, numerator := 329591824762763625661756080128 }, some { target := 18, numerator := 19478210483646994984676098048 }, some { target := 19, numerator := 19478210483646994984676098048 }, some { target := 20, numerator := 18965625997235231958763569152 }, some { target := 21, numerator := 18965625997235231958763569152 }, some { target := 22, numerator := 596135757696880399136271106048 }, some { target := 23, numerator := 18965625997235231958763569152 }, some { target := 24, numerator := 24091470861352862217888858112 }, some { target := 25, numerator := 24604055347764625243801387008 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 24091476605207798169200492544 }, some { target := 142, numerator := 17940461301750487998340792320 }, some { target := 143, numerator := 18965630518993373026817409024 }, some { target := 144, numerator := 24604061213829240683438800896 }, some { target := 145, numerator := 329591903343587536655232270336 }, some { target := 146, numerator := 596135899826737644059152613376 }, some { target := 147, numerator := 17940461301750487998340792320 }, some { target := 148, numerator := 329591903343587536655232270336 }, some { target := 149, numerator := 19478215127614815541055717376 }, some { target := 150, numerator := 19478215127614815541055717376 }, some { target := 151, numerator := 18965630518993373026817409024 }, some { target := 152, numerator := 18965630518993373026817409024 }, some { target := 153, numerator := 596135899826737644059152613376 }, some { target := 154, numerator := 18965630518993373026817409024 }, some { target := 155, numerator := 24091476605207798169200492544 }, some { target := 156, numerator := 24604061213829240683438800896 }]

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

end Slot27

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 155, #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 3182442986707934596332257280 }, some { target := 27, numerator := 46145423307265051646817730560 }, some { target := 28, numerator := 81682703325503654639194603520 }, some { target := 29, numerator := 2652035822256612163610214400 }, some { target := 30, numerator := 50919087787326953541316116480 }, some { target := 31, numerator := 2652035822256612163610214400 }, some { target := 32, numerator := 81152296161052332206472560640 }, some { target := 33, numerator := 84865146312211589235526860800 }, some { target := 34, numerator := 50919087787326953541316116480 }, some { target := 35, numerator := 1300027960070191282601727098880 }, some { target := 36, numerator := 83273924818857621937360732160 }, some { target := 37, numerator := 46145423307265051646817730560 }, some { target := 38, numerator := 81152296161052332206472560640 }, some { target := 39, numerator := 2652035822256612163610214400 }, some { target := 40, numerator := 83273924818857621937360732160 }, some { target := 41, numerator := 2652035822256612163610214400 }, some { target := 42, numerator := 81152296161052332206472560640 }, some { target := 43, numerator := 84865146312211589235526860800 }, some { target := 44, numerator := 3182442986707934596332257280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 11623931294666812211331072000 }, some { target := 158, numerator := 168547003772668777064300544000 }, some { target := 159, numerator := 298347569896448180090830848000 }, some { target := 160, numerator := 9686609412222343509442560000 }, some { target := 161, numerator := 185982900714668995381297152000 }, some { target := 162, numerator := 9686609412222343509442560000 }, some { target := 163, numerator := 296410248014003711388942336000 }, some { target := 164, numerator := 309971501191114992302161920000 }, some { target := 165, numerator := 185982900714668995381297152000 }, some { target := 166, numerator := 4748375933871392788328742912000 }, some { target := 167, numerator := 304159535543781586196496384000 }, some { target := 168, numerator := 168547003772668777064300544000 }, some { target := 169, numerator := 296410248014003711388942336000 }, some { target := 170, numerator := 9686609412222343509442560000 }, some { target := 171, numerator := 304159535543781586196496384000 }, some { target := 172, numerator := 9686609412222343509442560000 }, some { target := 173, numerator := 296410248014003711388942336000 }, some { target := 174, numerator := 309971501191114992302161920000 }, some { target := 175, numerator := 11623931294666812211331072000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 3182441914490935311964569600 }, some { target := 268, numerator := 46145407760118562023486259200 }, some { target := 269, numerator := 81682675805267339673757286400 }, some { target := 270, numerator := 2652034928742446093303808000 }, some { target := 271, numerator := 50919070631854964991433113600 }, some { target := 272, numerator := 2652034928742446093303808000 }, some { target := 273, numerator := 81152268819518850455096524800 }, some { target := 274, numerator := 84865117719758274985721856000 }, some { target := 275, numerator := 50919070631854964991433113600 }, some { target := 276, numerator := 1300027522069547074937526681600 }, some { target := 277, numerator := 83273896762512807329739571200 }, some { target := 278, numerator := 46145407760118562023486259200 }, some { target := 279, numerator := 81152268819518850455096524800 }, some { target := 280, numerator := 2652034928742446093303808000 }, some { target := 281, numerator := 83273896762512807329739571200 }, some { target := 282, numerator := 2652034928742446093303808000 }, some { target := 283, numerator := 81152268819518850455096524800 }, some { target := 284, numerator := 84865117719758274985721856000 }, some { target := 285, numerator := 3182441914490935311964569600 }]

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

end Slot28

namespace Slot29

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨29, 27, #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 142294346861828149579087872 }, some { target := 81, numerator := 160654907747225330169937920 }, some { target := 82, numerator := 137704206640478854431375360 }, some { target := 83, numerator := 1813105387432971583346442240 }, some { target := 84, numerator := 160654907747225330169937920 }, some { target := 85, numerator := 137704206640478854431375360 }, some { target := 86, numerator := 160654907747225330169937920 }, some { target := 87, numerator := 160654907747225330169937920 }, some { target := 88, numerator := 6660293461177827259330854912 }, some { target := 89, numerator := 165245047968574625317650432 }, some { target := 90, numerator := 1813105387432971583346442240 }, some { target := 91, numerator := 6660293461177827259330854912 }, some { target := 92, numerator := 142294346861828149579087872 }, some { target := 93, numerator := 160654907747225330169937920 }, some { target := 94, numerator := 165245047968574625317650432 }, some { target := 95, numerator := 160654907747225330169937920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 115, numerator := 162057450592637614798405632 }, some { target := 116, numerator := 182968089378784403804651520 }, some { target := 117, numerator := 156829790896100917546844160 }, some { target := 118, numerator := 2064925580131995414366781440 }, some { target := 119, numerator := 182968089378784403804651520 }, some { target := 120, numerator := 156829790896100917546844160 }, some { target := 121, numerator := 182968089378784403804651520 }, some { target := 122, numerator := 182968089378784403804651520 }, some { target := 123, numerator := 7585334219674747712015695872 }, some { target := 124, numerator := 188195749075321101056212992 }, some { target := 125, numerator := 2064925580131995414366781440 }, some { target := 126, numerator := 7585334219674747712015695872 }, some { target := 127, numerator := 162057450592637614798405632 }, some { target := 128, numerator := 182968089378784403804651520 }, some { target := 129, numerator := 188195749075321101056212992 }, some { target := 130, numerator := 182968089378784403804651520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 126483863877180577403633664 }, some { target := 177, numerator := 142804362441978071262167040 }, some { target := 178, numerator := 122403739235981203939000320 }, some { target := 179, numerator := 1611649233273752518530170880 }, some { target := 180, numerator := 142804362441978071262167040 }, some { target := 181, numerator := 122403739235981203939000320 }, some { target := 182, numerator := 142804362441978071262167040 }, some { target := 183, numerator := 142804362441978071262167040 }, some { target := 184, numerator := 5920260854380290897182982144 }, some { target := 185, numerator := 146884487083177444726800384 }, some { target := 186, numerator := 1611649233273752518530170880 }, some { target := 187, numerator := 5920260854380290897182982144 }, some { target := 188, numerator := 126483863877180577403633664 }, some { target := 189, numerator := 142804362441978071262167040 }, some { target := 190, numerator := 146884487083177444726800384 }, some { target := 191, numerator := 142804362441978071262167040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 211, numerator := 1695674300103452115817463808 }, some { target := 212, numerator := 1914470983987768517858426880 }, some { target := 213, numerator := 1640975129132373015307223040 }, some { target := 214, numerator := 21606172533576244701545103360 }, some { target := 215, numerator := 1914470983987768517858426880 }, some { target := 216, numerator := 1640975129132373015307223040 }, some { target := 217, numerator := 1914470983987768517858426880 }, some { target := 218, numerator := 1914470983987768517858426880 }, some { target := 219, numerator := 79368497079035774840359354368 }, some { target := 220, numerator := 1969170154958847618368667648 }, some { target := 221, numerator := 21606172533576244701545103360 }, some { target := 222, numerator := 79368497079035774840359354368 }, some { target := 223, numerator := 1695674300103452115817463808 }, some { target := 224, numerator := 1914470983987768517858426880 }, some { target := 225, numerator := 1969170154958847618368667648 }, some { target := 226, numerator := 1914470983987768517858426880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 237, numerator := 150199588354151935666814976 }, some { target := 238, numerator := 169580180399848959623823360 }, some { target := 239, numerator := 145354440342727679677562880 }, some { target := 240, numerator := 1913833464512581115754577920 }, some { target := 241, numerator := 169580180399848959623823360 }, some { target := 242, numerator := 145354440342727679677562880 }, some { target := 243, numerator := 169580180399848959623823360 }, some { target := 244, numerator := 169580180399848959623823360 }, some { target := 245, numerator := 7030309764576595440404791296 }, some { target := 246, numerator := 174425328411273215613075456 }, some { target := 247, numerator := 1913833464512581115754577920 }, some { target := 248, numerator := 7030309764576595440404791296 }, some { target := 249, numerator := 150199588354151935666814976 }, some { target := 250, numerator := 169580180399848959623823360 }, some { target := 251, numerator := 174425328411273215613075456 }, some { target := 252, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 126483863877180577403633664 }, some { target := 287, numerator := 142804362441978071262167040 }, some { target := 288, numerator := 122403739235981203939000320 }, some { target := 289, numerator := 1611649233273752518530170880 }, some { target := 290, numerator := 142804362441978071262167040 }, some { target := 291, numerator := 122403739235981203939000320 }, some { target := 292, numerator := 142804362441978071262167040 }, some { target := 293, numerator := 142804362441978071262167040 }, some { target := 294, numerator := 5920260854380290897182982144 }, some { target := 295, numerator := 146884487083177444726800384 }, some { target := 296, numerator := 1611649233273752518530170880 }, some { target := 297, numerator := 5920260854380290897182982144 }, some { target := 298, numerator := 126483863877180577403633664 }, some { target := 299, numerator := 142804362441978071262167040 }, some { target := 300, numerator := 146884487083177444726800384 }, some { target := 301, numerator := 142804362441978071262167040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 150199588354151935666814976 }, some { target := 313, numerator := 169580180399848959623823360 }, some { target := 314, numerator := 145354440342727679677562880 }, some { target := 315, numerator := 1913833464512581115754577920 }, some { target := 316, numerator := 169580180399848959623823360 }, some { target := 317, numerator := 145354440342727679677562880 }, some { target := 318, numerator := 169580180399848959623823360 }, some { target := 319, numerator := 169580180399848959623823360 }, some { target := 320, numerator := 7030309764576595440404791296 }, some { target := 321, numerator := 174425328411273215613075456 }, some { target := 322, numerator := 1913833464512581115754577920 }, some { target := 323, numerator := 7030309764576595440404791296 }, some { target := 324, numerator := 150199588354151935666814976 }, some { target := 325, numerator := 169580180399848959623823360 }, some { target := 326, numerator := 174425328411273215613075456 }, some { target := 327, numerator := 169580180399848959623823360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 146246967607990042622951424 }, some { target := 393, numerator := 165117544073537144896880640 }, some { target := 394, numerator := 141529323491603267054469120 }, some { target := 395, numerator := 1863469425972776349550510080 }, some { target := 396, numerator := 165117544073537144896880640 }, some { target := 397, numerator := 141529323491603267054469120 }, some { target := 398, numerator := 165117544073537144896880640 }, some { target := 399, numerator := 165117544073537144896880640 }, some { target := 400, numerator := 6845301612877211349867823104 }, some { target := 401, numerator := 169835188189923920465362944 }, some { target := 402, numerator := 1863469425972776349550510080 }, some { target := 403, numerator := 6845301612877211349867823104 }, some { target := 404, numerator := 146246967607990042622951424 }, some { target := 405, numerator := 165117544073537144896880640 }, some { target := 406, numerator := 169835188189923920465362944 }, some { target := 407, numerator := 165117544073537144896880640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 5525763803134326475321245696 }, some { target := 428, numerator := 6238765584183916988265922560 }, some { target := 429, numerator := 5347513357871928847085076480 }, some { target := 430, numerator := 70408925878647063153286840320 }, some { target := 431, numerator := 6238765584183916988265922560 }, some { target := 432, numerator := 5347513357871928847085076480 }, some { target := 433, numerator := 6238765584183916988265922560 }, some { target := 434, numerator := 6238765584183916988265922560 }, some { target := 435, numerator := 258641396075738958570681532416 }, some { target := 436, numerator := 6417016029446314616502091776 }, some { target := 437, numerator := 70408925878647063153286840320 }, some { target := 438, numerator := 258641396075738958570681532416 }, some { target := 439, numerator := 5525763803134326475321245696 }, some { target := 440, numerator := 6238765584183916988265922560 }, some { target := 441, numerator := 6417016029446314616502091776 }, some { target := 442, numerator := 6238765584183916988265922560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 146246967607990042622951424 }, some { target := 454, numerator := 165117544073537144896880640 }, some { target := 455, numerator := 141529323491603267054469120 }, some { target := 456, numerator := 1863469425972776349550510080 }, some { target := 457, numerator := 165117544073537144896880640 }, some { target := 458, numerator := 141529323491603267054469120 }, some { target := 459, numerator := 165117544073537144896880640 }, some { target := 460, numerator := 165117544073537144896880640 }, some { target := 461, numerator := 6845301612877211349867823104 }, some { target := 462, numerator := 169835188189923920465362944 }, some { target := 463, numerator := 1863469425972776349550510080 }, some { target := 464, numerator := 6845301612877211349867823104 }, some { target := 465, numerator := 146246967607990042622951424 }, some { target := 466, numerator := 165117544073537144896880640 }, some { target := 467, numerator := 169835188189923920465362944 }, some { target := 468, numerator := 165117544073537144896880640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 502, numerator := 1695674300103452115817463808 }, some { target := 503, numerator := 1914470983987768517858426880 }, some { target := 504, numerator := 1640975129132373015307223040 }, some { target := 505, numerator := 21606172533576244701545103360 }, some { target := 506, numerator := 1914470983987768517858426880 }, some { target := 507, numerator := 1640975129132373015307223040 }, some { target := 508, numerator := 1914470983987768517858426880 }, some { target := 509, numerator := 1914470983987768517858426880 }, some { target := 510, numerator := 79368497079035774840359354368 }, some { target := 511, numerator := 1969170154958847618368667648 }, some { target := 512, numerator := 21606172533576244701545103360 }, some { target := 513, numerator := 79368497079035774840359354368 }, some { target := 514, numerator := 1695674300103452115817463808 }, some { target := 515, numerator := 1914470983987768517858426880 }, some { target := 516, numerator := 1969170154958847618368667648 }, some { target := 517, numerator := 1914470983987768517858426880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 528, numerator := 5525763803134326475321245696 }, some { target := 529, numerator := 6238765584183916988265922560 }, some { target := 530, numerator := 5347513357871928847085076480 }, some { target := 531, numerator := 70408925878647063153286840320 }, some { target := 532, numerator := 6238765584183916988265922560 }, some { target := 533, numerator := 5347513357871928847085076480 }, some { target := 534, numerator := 6238765584183916988265922560 }, some { target := 535, numerator := 6238765584183916988265922560 }, some { target := 536, numerator := 258641396075738958570681532416 }, some { target := 537, numerator := 6417016029446314616502091776 }, some { target := 538, numerator := 70408925878647063153286840320 }, some { target := 539, numerator := 258641396075738958570681532416 }, some { target := 540, numerator := 5525763803134326475321245696 }, some { target := 541, numerator := 6238765584183916988265922560 }, some { target := 542, numerator := 6417016029446314616502091776 }, some { target := 543, numerator := 6238765584183916988265922560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 142294346861828149579087872 }, some { target := 574, numerator := 160654907747225330169937920 }, some { target := 575, numerator := 137704206640478854431375360 }, some { target := 576, numerator := 1813105387432971583346442240 }, some { target := 577, numerator := 160654907747225330169937920 }, some { target := 578, numerator := 137704206640478854431375360 }, some { target := 579, numerator := 160654907747225330169937920 }, some { target := 580, numerator := 160654907747225330169937920 }, some { target := 581, numerator := 6660293461177827259330854912 }, some { target := 582, numerator := 165245047968574625317650432 }, some { target := 583, numerator := 1813105387432971583346442240 }, some { target := 584, numerator := 6660293461177827259330854912 }, some { target := 585, numerator := 142294346861828149579087872 }, some { target := 586, numerator := 160654907747225330169937920 }, some { target := 587, numerator := 165245047968574625317650432 }, some { target := 588, numerator := 160654907747225330169937920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 642, numerator := 146246967607990042622951424 }, some { target := 643, numerator := 165117544073537144896880640 }, some { target := 644, numerator := 141529323491603267054469120 }, some { target := 645, numerator := 1863469425972776349550510080 }, some { target := 646, numerator := 165117544073537144896880640 }, some { target := 647, numerator := 141529323491603267054469120 }, some { target := 648, numerator := 165117544073537144896880640 }, some { target := 649, numerator := 165117544073537144896880640 }, some { target := 650, numerator := 6845301612877211349867823104 }, some { target := 651, numerator := 169835188189923920465362944 }, some { target := 652, numerator := 1863469425972776349550510080 }, some { target := 653, numerator := 6845301612877211349867823104 }, some { target := 654, numerator := 146246967607990042622951424 }, some { target := 655, numerator := 165117544073537144896880640 }, some { target := 656, numerator := 169835188189923920465362944 }, some { target := 657, numerator := 165117544073537144896880640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 668, numerator := 146246967607990042622951424 }, some { target := 669, numerator := 165117544073537144896880640 }, some { target := 670, numerator := 141529323491603267054469120 }, some { target := 671, numerator := 1863469425972776349550510080 }, some { target := 672, numerator := 165117544073537144896880640 }, some { target := 673, numerator := 141529323491603267054469120 }, some { target := 674, numerator := 165117544073537144896880640 }, some { target := 675, numerator := 165117544073537144896880640 }, some { target := 676, numerator := 6845301612877211349867823104 }, some { target := 677, numerator := 169835188189923920465362944 }, some { target := 678, numerator := 1863469425972776349550510080 }, some { target := 679, numerator := 6845301612877211349867823104 }, some { target := 680, numerator := 146246967607990042622951424 }, some { target := 681, numerator := 165117544073537144896880640 }, some { target := 682, numerator := 169835188189923920465362944 }, some { target := 683, numerator := 165117544073537144896880640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 713, numerator := 162057450592637614798405632 }, some { target := 714, numerator := 182968089378784403804651520 }, some { target := 715, numerator := 156829790896100917546844160 }, some { target := 716, numerator := 2064925580131995414366781440 }, some { target := 717, numerator := 182968089378784403804651520 }, some { target := 718, numerator := 156829790896100917546844160 }, some { target := 719, numerator := 182968089378784403804651520 }, some { target := 720, numerator := 182968089378784403804651520 }, some { target := 721, numerator := 7585334219674747712015695872 }, some { target := 722, numerator := 188195749075321101056212992 }, some { target := 723, numerator := 2064925580131995414366781440 }, some { target := 724, numerator := 7585334219674747712015695872 }, some { target := 725, numerator := 162057450592637614798405632 }, some { target := 726, numerator := 182968089378784403804651520 }, some { target := 727, numerator := 188195749075321101056212992 }, some { target := 728, numerator := 182968089378784403804651520 }]

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

end Slot29

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1
