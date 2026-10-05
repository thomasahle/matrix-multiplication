import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 3, #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

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
  [some { target := 14, numerator := 19763103730809465219317760 }, some { target := 15, numerator := 15371302901740695170580480 }, some { target := 16, numerator := 17567203316275080194949120 }, some { target := 17, numerator := 20641463896623219229065216 }, some { target := 18, numerator := 243744946013316737704919040 }, some { target := 19, numerator := 548096743467782502082412544 }, some { target := 20, numerator := 15371302901740695170580480 }, some { target := 21, numerator := 243744946013316737704919040 }, some { target := 22, numerator := 17567203316275080194949120 }, some { target := 23, numerator := 17128023233368203190075392 }, some { target := 24, numerator := 17128023233368203190075392 }, some { target := 25, numerator := 17128023233368203190075392 }, some { target := 26, numerator := 548096743467782502082412544 }, some { target := 27, numerator := 17128023233368203190075392 }, some { target := 28, numerator := 19763103730809465219317760 }, some { target := 29, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 40, numerator := 484514801142425598925209600 }, some { target := 41, numerator := 376844845332997688052940800 }, some { target := 42, numerator := 430679823237711643489075200 }, some { target := 43, numerator := 506048792304311181099663360 }, some { target := 44, numerator := 5975682547423249053410918400 }, some { target := 45, numerator := 13437210485016603276859146240 }, some { target := 46, numerator := 376844845332997688052940800 }, some { target := 47, numerator := 5975682547423249053410918400 }, some { target := 48, numerator := 430679823237711643489075200 }, some { target := 49, numerator := 419912827656768852401848320 }, some { target := 50, numerator := 419912827656768852401848320 }, some { target := 51, numerator := 419912827656768852401848320 }, some { target := 52, numerator := 13437210485016603276859146240 }, some { target := 53, numerator := 419912827656768852401848320 }, some { target := 54, numerator := 484514801142425598925209600 }, some { target := 55, numerator := 506048792304311181099663360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 75, numerator := 19763103730809465219317760 }, some { target := 76, numerator := 15371302901740695170580480 }, some { target := 77, numerator := 17567203316275080194949120 }, some { target := 78, numerator := 20641463896623219229065216 }, some { target := 79, numerator := 243744946013316737704919040 }, some { target := 80, numerator := 548096743467782502082412544 }, some { target := 81, numerator := 15371302901740695170580480 }, some { target := 82, numerator := 243744946013316737704919040 }, some { target := 83, numerator := 17567203316275080194949120 }, some { target := 84, numerator := 17128023233368203190075392 }, some { target := 85, numerator := 17128023233368203190075392 }, some { target := 86, numerator := 17128023233368203190075392 }, some { target := 87, numerator := 548096743467782502082412544 }, some { target := 88, numerator := 17128023233368203190075392 }, some { target := 89, numerator := 19763103730809465219317760 }, some { target := 90, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 406099905694375140151787520 }, some { target := 137, numerator := 315855482206736220118056960 }, some { target := 138, numerator := 360977693950555680134922240 }, some { target := 139, numerator := 424148790391902924158533632 }, some { target := 140, numerator := 5008565503563960061872046080 }, some { target := 141, numerator := 11262504051257337220209573888 }, some { target := 142, numerator := 315855482206736220118056960 }, some { target := 143, numerator := 5008565503563960061872046080 }, some { target := 144, numerator := 360977693950555680134922240 }, some { target := 145, numerator := 351953251601791788131549184 }, some { target := 146, numerator := 351953251601791788131549184 }, some { target := 147, numerator := 351953251601791788131549184 }, some { target := 148, numerator := 11262504051257337220209573888 }, some { target := 149, numerator := 351953251601791788131549184 }, some { target := 150, numerator := 406099905694375140151787520 }, some { target := 151, numerator := 424148790391902924158533632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 399087191467313717009448960 }, some { target := 172, numerator := 310401148919021779896238080 }, some { target := 173, numerator := 354744170193167748452843520 }, some { target := 174, numerator := 416824399976972104432091136 }, some { target := 175, numerator := 4922075361430202509783203840 }, some { target := 176, numerator := 11068018110026833751728717824 }, some { target := 177, numerator := 310401148919021779896238080 }, some { target := 178, numerator := 4922075361430202509783203840 }, some { target := 179, numerator := 354744170193167748452843520 }, some { target := 180, numerator := 345875565938338554741522432 }, some { target := 181, numerator := 345875565938338554741522432 }, some { target := 182, numerator := 345875565938338554741522432 }, some { target := 183, numerator := 11068018110026833751728717824 }, some { target := 184, numerator := 345875565938338554741522432 }, some { target := 185, numerator := 399087191467313717009448960 }, some { target := 186, numerator := 416824399976972104432091136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 19763103730809465219317760 }, some { target := 268, numerator := 15371302901740695170580480 }, some { target := 269, numerator := 17567203316275080194949120 }, some { target := 270, numerator := 20641463896623219229065216 }, some { target := 271, numerator := 243744946013316737704919040 }, some { target := 272, numerator := 548096743467782502082412544 }, some { target := 273, numerator := 15371302901740695170580480 }, some { target := 274, numerator := 243744946013316737704919040 }, some { target := 275, numerator := 17567203316275080194949120 }, some { target := 276, numerator := 17128023233368203190075392 }, some { target := 277, numerator := 17128023233368203190075392 }, some { target := 278, numerator := 17128023233368203190075392 }, some { target := 279, numerator := 548096743467782502082412544 }, some { target := 280, numerator := 17128023233368203190075392 }, some { target := 281, numerator := 19763103730809465219317760 }, some { target := 282, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 403, numerator := 399724710942501119113297920 }, some { target := 404, numerator := 310896997399723092643676160 }, some { target := 405, numerator := 355310854171112105878487040 }, some { target := 406, numerator := 417490253651056724407222272 }, some { target := 407, numerator := 4929938101624180469064007680 }, some { target := 408, numerator := 11085698650138697703408795648 }, some { target := 409, numerator := 310896997399723092643676160 }, some { target := 410, numerator := 4929938101624180469064007680 }, some { target := 411, numerator := 355310854171112105878487040 }, some { target := 412, numerator := 346428082816834303231524864 }, some { target := 413, numerator := 346428082816834303231524864 }, some { target := 414, numerator := 346428082816834303231524864 }, some { target := 415, numerator := 11085698650138697703408795648 }, some { target := 416, numerator := 346428082816834303231524864 }, some { target := 417, numerator := 399724710942501119113297920 }, some { target := 418, numerator := 417490253651056724407222272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 438, numerator := 358285945055319982363115520 }, some { target := 439, numerator := 278666846154137764060200960 }, some { target := 440, numerator := 318476395604728873211658240 }, some { target := 441, numerator := 374209764835556426023698432 }, some { target := 442, numerator := 4418859989015613115811758080 }, some { target := 443, numerator := 9936463542867540844203737088 }, some { target := 444, numerator := 278666846154137764060200960 }, some { target := 445, numerator := 4418859989015613115811758080 }, some { target := 446, numerator := 318476395604728873211658240 }, some { target := 447, numerator := 310514485714610651381366784 }, some { target := 448, numerator := 310514485714610651381366784 }, some { target := 449, numerator := 310514485714610651381366784 }, some { target := 450, numerator := 9936463542867540844203737088 }, some { target := 451, numerator := 310514485714610651381366784 }, some { target := 452, numerator := 358285945055319982363115520 }, some { target := 453, numerator := 374209764835556426023698432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 534, numerator := 484514801142425598925209600 }, some { target := 535, numerator := 376844845332997688052940800 }, some { target := 536, numerator := 430679823237711643489075200 }, some { target := 537, numerator := 506048792304311181099663360 }, some { target := 538, numerator := 5975682547423249053410918400 }, some { target := 539, numerator := 13437210485016603276859146240 }, some { target := 540, numerator := 376844845332997688052940800 }, some { target := 541, numerator := 5975682547423249053410918400 }, some { target := 542, numerator := 430679823237711643489075200 }, some { target := 543, numerator := 419912827656768852401848320 }, some { target := 544, numerator := 419912827656768852401848320 }, some { target := 545, numerator := 419912827656768852401848320 }, some { target := 546, numerator := 13437210485016603276859146240 }, some { target := 547, numerator := 419912827656768852401848320 }, some { target := 548, numerator := 484514801142425598925209600 }, some { target := 549, numerator := 506048792304311181099663360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 750, numerator := 19763103730809465219317760 }, some { target := 751, numerator := 15371302901740695170580480 }, some { target := 752, numerator := 17567203316275080194949120 }, some { target := 753, numerator := 20641463896623219229065216 }, some { target := 754, numerator := 243744946013316737704919040 }, some { target := 755, numerator := 548096743467782502082412544 }, some { target := 756, numerator := 15371302901740695170580480 }, some { target := 757, numerator := 243744946013316737704919040 }, some { target := 758, numerator := 17567203316275080194949120 }, some { target := 759, numerator := 17128023233368203190075392 }, some { target := 760, numerator := 17128023233368203190075392 }, some { target := 761, numerator := 17128023233368203190075392 }, some { target := 762, numerator := 548096743467782502082412544 }, some { target := 763, numerator := 17128023233368203190075392 }, some { target := 764, numerator := 19763103730809465219317760 }, some { target := 765, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 9, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 7]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 389, numerator := 30508685740935683900323135488 }, some { target := 391, numerator := 30508685740935683900323135488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 731, numerator := 295509359832318151370301505536 }, some { target := 733, numerator := 295509359832318151370301505536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 992, numerator := 30508685740935683900323135488 }, some { target := 994, numerator := 30508685740935683900323135488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left7.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left7.routed_eq]
  rfl

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 684, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 257, numerator := 59334312378421514833483530240 }, some { target := 260, numerator := 201127294490529279810302115840 }, some { target := 262, numerator := 59334312378421514833483530240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 4968010644867432196638448287744 }, some { target := 356, numerator := 16840214370896166754237865263104 }, some { target := 358, numerator := 4968010644867432196638448287744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 4968012442786094236581324914688 }, some { target := 698, numerator := 16840220465354865522864090513408 }, some { target := 700, numerator := 4968012442786094236581324914688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 59332514459759474890606903296 }, some { target := 985, numerator := 201121200031830511184076865536 }, some { target := 987, numerator := 59332514459759474890606903296 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 6593, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 5226530229335345186832646144 }, some { target := 112, numerator := 189411185498744312256369000448 }, some { target := 115, numerator := 189411255106615747450261995520 }, some { target := 122, numerator := 5226460621463909992939651072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 547992268147612789433503318016 }, some { target := 208, numerator := 19859421183752491209324360630272 }, some { target := 211, numerator := 19859428482012268719527721697280 }, some { target := 218, numerator := 547984969887835279230142251008 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 5906808933003633387538219008000 }, some { target := 304, numerator := 214064710892731277397391835136000 }, some { target := 307, numerator := 214064789560677076891745648640000 }, some { target := 314, numerator := 5906730265057833893184405504000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 547992686169705833930439000064 }, some { target := 681, numerator := 19859436333011508944612871897088 }, some { target := 684, numerator := 19859443631276853748380593029120 }, some { target := 691, numerator := 547985387904361030162717868032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 5226530229335345186832646144 }, some { target := 968, numerator := 189411185498744312256369000448 }, some { target := 971, numerator := 189411255106615747450261995520 }, some { target := 978, numerator := 5226460621463909992939651072 }]

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

end Slot9

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2
