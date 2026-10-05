import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 691, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 59941534873522319809849589760 }, some { target := 15, numerator := 5018852859069291882861356384256 }, some { target := 20, numerator := 5018854675387706312101894029312 }, some { target := 28, numerator := 59939718555107890569311944704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 203185614755783234428243804160 }, some { target := 137, numerator := 17012555746036916998798779088896 }, some { target := 142, numerator := 17012561902865807129092231790592 }, some { target := 150, numerator := 203179457926893104134791102464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 59941534873522319809849589760 }, some { target := 268, numerator := 5018852859069291882861356384256 }, some { target := 273, numerator := 5018854675387706312101894029312 }, some { target := 281, numerator := 59939718555107890569311944704 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 8, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 4, numerator := 27118831769720607911398342656 }, some { target := 6, numerator := 262674986517616134551379116032 }, some { target := 11, numerator := 27118831769720607911398342656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 27118831769720607911398342656 }, some { target := 128, numerator := 262674986517616134551379116032 }, some { target := 133, numerator := 27118831769720607911398342656 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 3, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 257, numerator := 19763103730809465219317760 }, some { target := 258, numerator := 484514801142425598925209600 }, some { target := 259, numerator := 19763103730809465219317760 }, some { target := 260, numerator := 406099905694375140151787520 }, some { target := 261, numerator := 399087191467313717009448960 }, some { target := 262, numerator := 19763103730809465219317760 }, some { target := 263, numerator := 399724710942501119113297920 }, some { target := 264, numerator := 358285945055319982363115520 }, some { target := 265, numerator := 484514801142425598925209600 }, some { target := 266, numerator := 19763103730809465219317760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 15371302901740695170580480 }, some { target := 354, numerator := 376844845332997688052940800 }, some { target := 355, numerator := 15371302901740695170580480 }, some { target := 356, numerator := 315855482206736220118056960 }, some { target := 357, numerator := 310401148919021779896238080 }, some { target := 358, numerator := 15371302901740695170580480 }, some { target := 359, numerator := 310896997399723092643676160 }, some { target := 360, numerator := 278666846154137764060200960 }, some { target := 361, numerator := 376844845332997688052940800 }, some { target := 362, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 379, numerator := 17567203316275080194949120 }, some { target := 380, numerator := 430679823237711643489075200 }, some { target := 381, numerator := 17567203316275080194949120 }, some { target := 382, numerator := 360977693950555680134922240 }, some { target := 383, numerator := 354744170193167748452843520 }, some { target := 384, numerator := 17567203316275080194949120 }, some { target := 385, numerator := 355310854171112105878487040 }, some { target := 386, numerator := 318476395604728873211658240 }, some { target := 387, numerator := 430679823237711643489075200 }, some { target := 388, numerator := 17567203316275080194949120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 524, numerator := 20641463896623219229065216 }, some { target := 525, numerator := 506048792304311181099663360 }, some { target := 526, numerator := 20641463896623219229065216 }, some { target := 527, numerator := 424148790391902924158533632 }, some { target := 528, numerator := 416824399976972104432091136 }, some { target := 529, numerator := 20641463896623219229065216 }, some { target := 530, numerator := 417490253651056724407222272 }, some { target := 531, numerator := 374209764835556426023698432 }, some { target := 532, numerator := 506048792304311181099663360 }, some { target := 533, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 620, numerator := 243744946013316737704919040 }, some { target := 621, numerator := 5975682547423249053410918400 }, some { target := 622, numerator := 243744946013316737704919040 }, some { target := 623, numerator := 5008565503563960061872046080 }, some { target := 624, numerator := 4922075361430202509783203840 }, some { target := 625, numerator := 243744946013316737704919040 }, some { target := 626, numerator := 4929938101624180469064007680 }, some { target := 627, numerator := 4418859989015613115811758080 }, some { target := 628, numerator := 5975682547423249053410918400 }, some { target := 629, numerator := 243744946013316737704919040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 646, numerator := 548096743467782502082412544 }, some { target := 647, numerator := 13437210485016603276859146240 }, some { target := 648, numerator := 548096743467782502082412544 }, some { target := 649, numerator := 11262504051257337220209573888 }, some { target := 650, numerator := 11068018110026833751728717824 }, some { target := 651, numerator := 548096743467782502082412544 }, some { target := 652, numerator := 11085698650138697703408795648 }, some { target := 653, numerator := 9936463542867540844203737088 }, some { target := 654, numerator := 13437210485016603276859146240 }, some { target := 655, numerator := 548096743467782502082412544 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 15371302901740695170580480 }, some { target := 696, numerator := 376844845332997688052940800 }, some { target := 697, numerator := 15371302901740695170580480 }, some { target := 698, numerator := 315855482206736220118056960 }, some { target := 699, numerator := 310401148919021779896238080 }, some { target := 700, numerator := 15371302901740695170580480 }, some { target := 701, numerator := 310896997399723092643676160 }, some { target := 702, numerator := 278666846154137764060200960 }, some { target := 703, numerator := 376844845332997688052940800 }, some { target := 704, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 721, numerator := 243744946013316737704919040 }, some { target := 722, numerator := 5975682547423249053410918400 }, some { target := 723, numerator := 243744946013316737704919040 }, some { target := 724, numerator := 5008565503563960061872046080 }, some { target := 725, numerator := 4922075361430202509783203840 }, some { target := 726, numerator := 243744946013316737704919040 }, some { target := 727, numerator := 4929938101624180469064007680 }, some { target := 728, numerator := 4418859989015613115811758080 }, some { target := 729, numerator := 5975682547423249053410918400 }, some { target := 730, numerator := 243744946013316737704919040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 735, numerator := 17567203316275080194949120 }, some { target := 736, numerator := 430679823237711643489075200 }, some { target := 737, numerator := 17567203316275080194949120 }, some { target := 738, numerator := 360977693950555680134922240 }, some { target := 739, numerator := 354744170193167748452843520 }, some { target := 740, numerator := 17567203316275080194949120 }, some { target := 741, numerator := 355310854171112105878487040 }, some { target := 742, numerator := 318476395604728873211658240 }, some { target := 743, numerator := 430679823237711643489075200 }, some { target := 744, numerator := 17567203316275080194949120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 836, numerator := 17128023233368203190075392 }, some { target := 837, numerator := 419912827656768852401848320 }, some { target := 838, numerator := 17128023233368203190075392 }, some { target := 839, numerator := 351953251601791788131549184 }, some { target := 840, numerator := 345875565938338554741522432 }, some { target := 841, numerator := 17128023233368203190075392 }, some { target := 842, numerator := 346428082816834303231524864 }, some { target := 843, numerator := 310514485714610651381366784 }, some { target := 844, numerator := 419912827656768852401848320 }, some { target := 845, numerator := 17128023233368203190075392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 862, numerator := 17128023233368203190075392 }, some { target := 863, numerator := 419912827656768852401848320 }, some { target := 864, numerator := 17128023233368203190075392 }, some { target := 865, numerator := 351953251601791788131549184 }, some { target := 866, numerator := 345875565938338554741522432 }, some { target := 867, numerator := 17128023233368203190075392 }, some { target := 868, numerator := 346428082816834303231524864 }, some { target := 869, numerator := 310514485714610651381366784 }, some { target := 870, numerator := 419912827656768852401848320 }, some { target := 871, numerator := 17128023233368203190075392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 911, numerator := 17128023233368203190075392 }, some { target := 912, numerator := 419912827656768852401848320 }, some { target := 913, numerator := 17128023233368203190075392 }, some { target := 914, numerator := 351953251601791788131549184 }, some { target := 915, numerator := 345875565938338554741522432 }, some { target := 916, numerator := 17128023233368203190075392 }, some { target := 917, numerator := 346428082816834303231524864 }, some { target := 918, numerator := 310514485714610651381366784 }, some { target := 919, numerator := 419912827656768852401848320 }, some { target := 920, numerator := 17128023233368203190075392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 937, numerator := 548096743467782502082412544 }, some { target := 938, numerator := 13437210485016603276859146240 }, some { target := 939, numerator := 548096743467782502082412544 }, some { target := 940, numerator := 11262504051257337220209573888 }, some { target := 941, numerator := 11068018110026833751728717824 }, some { target := 942, numerator := 548096743467782502082412544 }, some { target := 943, numerator := 11085698650138697703408795648 }, some { target := 944, numerator := 9936463542867540844203737088 }, some { target := 945, numerator := 13437210485016603276859146240 }, some { target := 946, numerator := 548096743467782502082412544 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 951, numerator := 17128023233368203190075392 }, some { target := 952, numerator := 419912827656768852401848320 }, some { target := 953, numerator := 17128023233368203190075392 }, some { target := 954, numerator := 351953251601791788131549184 }, some { target := 955, numerator := 345875565938338554741522432 }, some { target := 956, numerator := 17128023233368203190075392 }, some { target := 957, numerator := 346428082816834303231524864 }, some { target := 958, numerator := 310514485714610651381366784 }, some { target := 959, numerator := 419912827656768852401848320 }, some { target := 960, numerator := 17128023233368203190075392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 19763103730809465219317760 }, some { target := 983, numerator := 484514801142425598925209600 }, some { target := 984, numerator := 19763103730809465219317760 }, some { target := 985, numerator := 406099905694375140151787520 }, some { target := 986, numerator := 399087191467313717009448960 }, some { target := 987, numerator := 19763103730809465219317760 }, some { target := 988, numerator := 399724710942501119113297920 }, some { target := 989, numerator := 358285945055319982363115520 }, some { target := 990, numerator := 484514801142425598925209600 }, some { target := 991, numerator := 19763103730809465219317760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 996, numerator := 20641463896623219229065216 }, some { target := 997, numerator := 506048792304311181099663360 }, some { target := 998, numerator := 20641463896623219229065216 }, some { target := 999, numerator := 424148790391902924158533632 }, some { target := 1000, numerator := 416824399976972104432091136 }, some { target := 1001, numerator := 20641463896623219229065216 }, some { target := 1002, numerator := 417490253651056724407222272 }, some { target := 1003, numerator := 374209764835556426023698432 }, some { target := 1004, numerator := 506048792304311181099663360 }, some { target := 1005, numerator := 20641463896623219229065216 }]

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

end Slot20

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 206, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 99910369808310135404101632 }, some { target := 111, numerator := 97828903770637007583182848 }, some { target := 112, numerator := 77014243393905729373995008 }, some { target := 113, numerator := 2420745001813847655728545792 }, some { target := 114, numerator := 77014243393905729373995008 }, some { target := 115, numerator := 77014243393905729373995008 }, some { target := 116, numerator := 79095709431578857194913792 }, some { target := 117, numerator := 79095709431578857194913792 }, some { target := 118, numerator := 1338382662223821188850778112 }, some { target := 119, numerator := 72851311318559473732157440 }, some { target := 120, numerator := 2420745001813847655728545792 }, some { target := 121, numerator := 1338382662223821188850778112 }, some { target := 122, numerator := 99910369808310135404101632 }, some { target := 123, numerator := 77014243393905729373995008 }, some { target := 124, numerator := 72851311318559473732157440 }, some { target := 125, numerator := 97828903770637007583182848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 15950410097735909325693517824 }, some { target := 207, numerator := 15618109887366411214741569536 }, some { target := 208, numerator := 12295107783671430105222086656 }, some { target := 209, numerator := 386465144659726303037115858944 }, some { target := 210, numerator := 12295107783671430105222086656 }, some { target := 211, numerator := 12295107783671430105222086656 }, some { target := 212, numerator := 12627407994040928216174034944 }, some { target := 213, numerator := 12627407994040928216174034944 }, some { target := 214, numerator := 213669035267587285342102749184 }, some { target := 215, numerator := 11630507362932433883318190080 }, some { target := 216, numerator := 386465144659726303037115858944 }, some { target := 217, numerator := 213669035267587285342102749184 }, some { target := 218, numerator := 15950410097735909325693517824 }, some { target := 219, numerator := 12295107783671430105222086656 }, some { target := 220, numerator := 11630507362932433883318190080 }, some { target := 221, numerator := 15618109887366411214741569536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 159161106534590651102222352384 }, some { target := 303, numerator := 155845250148453345870926053376 }, some { target := 304, numerator := 122686686287080293557963063296 }, some { target := 305, numerator := 3856340977077685983997595746304 }, some { target := 306, numerator := 122686686287080293557963063296 }, some { target := 307, numerator := 122686686287080293557963063296 }, some { target := 308, numerator := 126002542673217598789259362304 }, some { target := 309, numerator := 126002542673217598789259362304 }, some { target := 310, numerator := 2132095656286287263723520262144 }, some { target := 311, numerator := 116054973514805683095370465280 }, some { target := 312, numerator := 3856340977077685983997595746304 }, some { target := 313, numerator := 2132095656286287263723520262144 }, some { target := 314, numerator := 159161106534590651102222352384 }, some { target := 315, numerator := 122686686287080293557963063296 }, some { target := 316, numerator := 116054973514805683095370465280 }, some { target := 317, numerator := 155845250148453345870926053376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 15950410097735909325693517824 }, some { target := 680, numerator := 15618109887366411214741569536 }, some { target := 681, numerator := 12295107783671430105222086656 }, some { target := 682, numerator := 386465144659726303037115858944 }, some { target := 683, numerator := 12295107783671430105222086656 }, some { target := 684, numerator := 12295107783671430105222086656 }, some { target := 685, numerator := 12627407994040928216174034944 }, some { target := 686, numerator := 12627407994040928216174034944 }, some { target := 687, numerator := 213669035267587285342102749184 }, some { target := 688, numerator := 11630507362932433883318190080 }, some { target := 689, numerator := 386465144659726303037115858944 }, some { target := 690, numerator := 213669035267587285342102749184 }, some { target := 691, numerator := 15950410097735909325693517824 }, some { target := 692, numerator := 12295107783671430105222086656 }, some { target := 693, numerator := 11630507362932433883318190080 }, some { target := 694, numerator := 15618109887366411214741569536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 99898969720472582901202944 }, some { target := 967, numerator := 97817741184629404090761216 }, some { target := 968, numerator := 77005455826197615986343936 }, some { target := 969, numerator := 2420468787185616956543729664 }, some { target := 970, numerator := 77005455826197615986343936 }, some { target := 971, numerator := 77005455826197615986343936 }, some { target := 972, numerator := 79086684362040794796785664 }, some { target := 973, numerator := 79086684362040794796785664 }, some { target := 974, numerator := 1338229948547163975114031104 }, some { target := 975, numerator := 72842998754511258365460480 }, some { target := 976, numerator := 2420468787185616956543729664 }, some { target := 977, numerator := 1338229948547163975114031104 }, some { target := 978, numerator := 99898969720472582901202944 }, some { target := 979, numerator := 77005455826197615986343936 }, some { target := 980, numerator := 72842998754511258365460480 }, some { target := 981, numerator := 97817741184629404090761216 }]

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

end Slot21

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2
