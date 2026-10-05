import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 7, for region 1, branch 2,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 3, #[2061584302080, 36696200577024, 2061584302080, 32641751449600, 55731495632896, 2061584302080, 55731495632896, 55731495632896, 36696200577024, 2061584302080, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 35, numerator := 20400623205996867323166720 }, some { target := 36, numerator := 19975610222538599253934080 }, some { target := 37, numerator := 15725480387955918561607680 }, some { target := 38, numerator := 494290099761965764517560320 }, some { target := 39, numerator := 15725480387955918561607680 }, some { target := 40, numerator := 15725480387955918561607680 }, some { target := 41, numerator := 16150493371414186630840320 }, some { target := 42, numerator := 16150493371414186630840320 }, some { target := 43, numerator := 273283348363666368516587520 }, some { target := 44, numerator := 14875454421039382423142400 }, some { target := 45, numerator := 494290099761965764517560320 }, some { target := 46, numerator := 273283348363666368516587520 }, some { target := 47, numerator := 20400623205996867323166720 }, some { target := 48, numerator := 15725480387955918561607680 }, some { target := 49, numerator := 14875454421039382423142400 }, some { target := 50, numerator := 19975610222538599253934080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 70, numerator := 363131093066744238352367616 }, some { target := 71, numerator := 355565861961187066720026624 }, some { target := 72, numerator := 279913550905615350396616704 }, some { target := 73, numerator := 8798363775762990608412573696 }, some { target := 74, numerator := 279913550905615350396616704 }, some { target := 75, numerator := 279913550905615350396616704 }, some { target := 76, numerator := 287478782011172522028957696 }, some { target := 77, numerator := 287478782011172522028957696 }, some { target := 78, numerator := 4864443600873261359595257856 }, some { target := 79, numerator := 264783088694501007131934720 }, some { target := 80, numerator := 8798363775762990608412573696 }, some { target := 81, numerator := 4864443600873261359595257856 }, some { target := 82, numerator := 363131093066744238352367616 }, some { target := 83, numerator := 279913550905615350396616704 }, some { target := 84, numerator := 264783088694501007131934720 }, some { target := 85, numerator := 355565861961187066720026624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 20400623205996867323166720 }, some { target := 97, numerator := 19975610222538599253934080 }, some { target := 98, numerator := 15725480387955918561607680 }, some { target := 99, numerator := 494290099761965764517560320 }, some { target := 100, numerator := 15725480387955918561607680 }, some { target := 101, numerator := 15725480387955918561607680 }, some { target := 102, numerator := 16150493371414186630840320 }, some { target := 103, numerator := 16150493371414186630840320 }, some { target := 104, numerator := 273283348363666368516587520 }, some { target := 105, numerator := 14875454421039382423142400 }, some { target := 106, numerator := 494290099761965764517560320 }, some { target := 107, numerator := 273283348363666368516587520 }, some { target := 108, numerator := 20400623205996867323166720 }, some { target := 109, numerator := 15725480387955918561607680 }, some { target := 110, numerator := 14875454421039382423142400 }, some { target := 111, numerator := 19975610222538599253934080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 145, numerator := 323009867428283732616806400 }, some { target := 146, numerator := 316280495190194488187289600 }, some { target := 147, numerator := 248986772809302043892121600 }, some { target := 148, numerator := 7826259912897791271528038400 }, some { target := 149, numerator := 248986772809302043892121600 }, some { target := 150, numerator := 248986772809302043892121600 }, some { target := 151, numerator := 255716145047391288321638400 }, some { target := 152, numerator := 255716145047391288321638400 }, some { target := 153, numerator := 4326986349091384168179302400 }, some { target := 154, numerator := 235528028333123555033088000 }, some { target := 155, numerator := 7826259912897791271528038400 }, some { target := 156, numerator := 4326986349091384168179302400 }, some { target := 157, numerator := 323009867428283732616806400 }, some { target := 158, numerator := 248986772809302043892121600 }, some { target := 159, numerator := 235528028333123555033088000 }, some { target := 160, numerator := 316280495190194488187289600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 551496847335448646636273664 }, some { target := 172, numerator := 540007329682626799831351296 }, some { target := 173, numerator := 425112153154408331782127616 }, some { target := 174, numerator := 13362309030231807834124713984 }, some { target := 175, numerator := 425112153154408331782127616 }, some { target := 176, numerator := 425112153154408331782127616 }, some { target := 177, numerator := 436601670807230178587049984 }, some { target := 178, numerator := 436601670807230178587049984 }, some { target := 179, numerator := 7387759850764447495565082624 }, some { target := 180, numerator := 402133117848764638172282880 }, some { target := 181, numerator := 13362309030231807834124713984 }, some { target := 182, numerator := 7387759850764447495565082624 }, some { target := 183, numerator := 551496847335448646636273664 }, some { target := 184, numerator := 425112153154408331782127616 }, some { target := 185, numerator := 402133117848764638172282880 }, some { target := 186, numerator := 540007329682626799831351296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 20400623205996867323166720 }, some { target := 217, numerator := 19975610222538599253934080 }, some { target := 218, numerator := 15725480387955918561607680 }, some { target := 219, numerator := 494290099761965764517560320 }, some { target := 220, numerator := 15725480387955918561607680 }, some { target := 221, numerator := 15725480387955918561607680 }, some { target := 222, numerator := 16150493371414186630840320 }, some { target := 223, numerator := 16150493371414186630840320 }, some { target := 224, numerator := 273283348363666368516587520 }, some { target := 225, numerator := 14875454421039382423142400 }, some { target := 226, numerator := 494290099761965764517560320 }, some { target := 227, numerator := 273283348363666368516587520 }, some { target := 228, numerator := 20400623205996867323166720 }, some { target := 229, numerator := 15725480387955918561607680 }, some { target := 230, numerator := 14875454421039382423142400 }, some { target := 231, numerator := 19975610222538599253934080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 285, numerator := 551496847335448646636273664 }, some { target := 286, numerator := 540007329682626799831351296 }, some { target := 287, numerator := 425112153154408331782127616 }, some { target := 288, numerator := 13362309030231807834124713984 }, some { target := 289, numerator := 425112153154408331782127616 }, some { target := 290, numerator := 425112153154408331782127616 }, some { target := 291, numerator := 436601670807230178587049984 }, some { target := 292, numerator := 436601670807230178587049984 }, some { target := 293, numerator := 7387759850764447495565082624 }, some { target := 294, numerator := 402133117848764638172282880 }, some { target := 295, numerator := 13362309030231807834124713984 }, some { target := 296, numerator := 7387759850764447495565082624 }, some { target := 297, numerator := 551496847335448646636273664 }, some { target := 298, numerator := 425112153154408331782127616 }, some { target := 299, numerator := 402133117848764638172282880 }, some { target := 300, numerator := 540007329682626799831351296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 311, numerator := 551496847335448646636273664 }, some { target := 312, numerator := 540007329682626799831351296 }, some { target := 313, numerator := 425112153154408331782127616 }, some { target := 314, numerator := 13362309030231807834124713984 }, some { target := 315, numerator := 425112153154408331782127616 }, some { target := 316, numerator := 425112153154408331782127616 }, some { target := 317, numerator := 436601670807230178587049984 }, some { target := 318, numerator := 436601670807230178587049984 }, some { target := 319, numerator := 7387759850764447495565082624 }, some { target := 320, numerator := 402133117848764638172282880 }, some { target := 321, numerator := 13362309030231807834124713984 }, some { target := 322, numerator := 7387759850764447495565082624 }, some { target := 323, numerator := 551496847335448646636273664 }, some { target := 324, numerator := 425112153154408331782127616 }, some { target := 325, numerator := 402133117848764638172282880 }, some { target := 326, numerator := 540007329682626799831351296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 356, numerator := 363131093066744238352367616 }, some { target := 357, numerator := 355565861961187066720026624 }, some { target := 358, numerator := 279913550905615350396616704 }, some { target := 359, numerator := 8798363775762990608412573696 }, some { target := 360, numerator := 279913550905615350396616704 }, some { target := 361, numerator := 279913550905615350396616704 }, some { target := 362, numerator := 287478782011172522028957696 }, some { target := 363, numerator := 287478782011172522028957696 }, some { target := 364, numerator := 4864443600873261359595257856 }, some { target := 365, numerator := 264783088694501007131934720 }, some { target := 366, numerator := 8798363775762990608412573696 }, some { target := 367, numerator := 4864443600873261359595257856 }, some { target := 368, numerator := 363131093066744238352367616 }, some { target := 369, numerator := 279913550905615350396616704 }, some { target := 370, numerator := 264783088694501007131934720 }, some { target := 371, numerator := 355565861961187066720026624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 427, numerator := 20400623205996867323166720 }, some { target := 428, numerator := 19975610222538599253934080 }, some { target := 429, numerator := 15725480387955918561607680 }, some { target := 430, numerator := 494290099761965764517560320 }, some { target := 431, numerator := 15725480387955918561607680 }, some { target := 432, numerator := 15725480387955918561607680 }, some { target := 433, numerator := 16150493371414186630840320 }, some { target := 434, numerator := 16150493371414186630840320 }, some { target := 435, numerator := 273283348363666368516587520 }, some { target := 436, numerator := 14875454421039382423142400 }, some { target := 437, numerator := 494290099761965764517560320 }, some { target := 438, numerator := 273283348363666368516587520 }, some { target := 439, numerator := 20400623205996867323166720 }, some { target := 440, numerator := 15725480387955918561607680 }, some { target := 441, numerator := 14875454421039382423142400 }, some { target := 442, numerator := 19975610222538599253934080 }]

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

end Slot27

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 10, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 16, numerator := 580284393415022003858964480 }, some { target := 17, numerator := 15474250491067253436239052800 }, some { target := 18, numerator := 14797252032083061098403594240 }, some { target := 19, numerator := 483570327845851669882470400 }, some { target := 20, numerator := 15184108294359742434309570560 }, some { target := 21, numerator := 483570327845851669882470400 }, some { target := 22, numerator := 14797252032083061098403594240 }, some { target := 23, numerator := 8414123704517819055954984960 }, some { target := 24, numerator := 15184108294359742434309570560 }, some { target := 25, numerator := 237046174710036488576386990080 }, some { target := 26, numerator := 9284550294640352061743431680 }, some { target := 27, numerator := 15474250491067253436239052800 }, some { target := 28, numerator := 14797252032083061098403594240 }, some { target := 29, numerator := 483570327845851669882470400 }, some { target := 30, numerator := 9284550294640352061743431680 }, some { target := 31, numerator := 483570327845851669882470400 }, some { target := 32, numerator := 14893966097652231432380088320 }, some { target := 33, numerator := 8414123704517819055954984960 }, some { target := 34, numerator := 580284393415022003858964480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 580284393415022003858964480 }, some { target := 127, numerator := 15474250491067253436239052800 }, some { target := 128, numerator := 14797252032083061098403594240 }, some { target := 129, numerator := 483570327845851669882470400 }, some { target := 130, numerator := 15184108294359742434309570560 }, some { target := 131, numerator := 483570327845851669882470400 }, some { target := 132, numerator := 14797252032083061098403594240 }, some { target := 133, numerator := 8414123704517819055954984960 }, some { target := 134, numerator := 15184108294359742434309570560 }, some { target := 135, numerator := 237046174710036488576386990080 }, some { target := 136, numerator := 9284550294640352061743431680 }, some { target := 137, numerator := 15474250491067253436239052800 }, some { target := 138, numerator := 14797252032083061098403594240 }, some { target := 139, numerator := 483570327845851669882470400 }, some { target := 140, numerator := 9284550294640352061743431680 }, some { target := 141, numerator := 483570327845851669882470400 }, some { target := 142, numerator := 14893966097652231432380088320 }, some { target := 143, numerator := 8414123704517819055954984960 }, some { target := 144, numerator := 580284393415022003858964480 }]

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

end Slot28

namespace Slot29

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨29, 3, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 2030995376952577013506375680 }, some { target := 1, numerator := 2089023816294079213892272128 }, some { target := 2, numerator := 2030995376952577013506375680 }, some { target := 3, numerator := 1798881619586568211962789888 }, some { target := 4, numerator := 84199265484519692759935746048 }, some { target := 5, numerator := 22921233539893369152429096960 }, some { target := 6, numerator := 2089023816294079213892272128 }, some { target := 7, numerator := 84199265484519692759935746048 }, some { target := 8, numerator := 2030995376952577013506375680 }, some { target := 9, numerator := 2030995376952577013506375680 }, some { target := 10, numerator := 1740853180245066011576893440 }, some { target := 11, numerator := 2030995376952577013506375680 }, some { target := 12, numerator := 22921233539893369152429096960 }, some { target := 13, numerator := 1740853180245066011576893440 }, some { target := 14, numerator := 2030995376952577013506375680 }, some { target := 15, numerator := 1798881619586568211962789888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot29

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent2
