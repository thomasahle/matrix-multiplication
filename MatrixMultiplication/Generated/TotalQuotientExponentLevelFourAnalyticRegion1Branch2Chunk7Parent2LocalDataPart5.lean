import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 1923, #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 56, numerator := 2892954551833767897766821888 }, some { target := 57, numerator := 77145454715567143940448583680 }, some { target := 58, numerator := 73770341071761081393053958144 }, some { target := 59, numerator := 2410795459861473248139018240 }, some { target := 60, numerator := 75698977439650259991565172736 }, some { target := 61, numerator := 2410795459861473248139018240 }, some { target := 62, numerator := 73770341071761081393053958144 }, some { target := 63, numerator := 41947841001589634517618917376 }, some { target := 64, numerator := 75698977439650259991565172736 }, some { target := 65, numerator := 1181771934424094186237746741248 }, some { target := 66, numerator := 46287272829340286364269150208 }, some { target := 67, numerator := 77145454715567143940448583680 }, some { target := 68, numerator := 73770341071761081393053958144 }, some { target := 69, numerator := 2410795459861473248139018240 }, some { target := 70, numerator := 46287272829340286364269150208 }, some { target := 71, numerator := 2410795459861473248139018240 }, some { target := 72, numerator := 74252500163733376042681761792 }, some { target := 73, numerator := 41947841001589634517618917376 }, some { target := 74, numerator := 2892954551833767897766821888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 108695734301874963444312047616 }, some { target := 153, numerator := 2898552914716665691848321269760 }, some { target := 154, numerator := 2771741224697811567829957214208 }, some { target := 155, numerator := 90579778584895802870260039680 }, some { target := 156, numerator := 2844205047565728210126165245952 }, some { target := 157, numerator := 90579778584895802870260039680 }, some { target := 158, numerator := 2771741224697811567829957214208 }, some { target := 159, numerator := 1576088147377186969942524690432 }, some { target := 160, numerator := 2844205047565728210126165245952 }, some { target := 161, numerator := 44402207462315922567001471451136 }, some { target := 162, numerator := 1739131748829999415108992761856 }, some { target := 163, numerator := 2898552914716665691848321269760 }, some { target := 164, numerator := 2771741224697811567829957214208 }, some { target := 165, numerator := 90579778584895802870260039680 }, some { target := 166, numerator := 1739131748829999415108992761856 }, some { target := 167, numerator := 90579778584895802870260039680 }, some { target := 168, numerator := 2789857180414790728404009222144 }, some { target := 169, numerator := 1576088147377186969942524690432 }, some { target := 170, numerator := 108695734301874963444312047616 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 108687513413533108395659231232 }, some { target := 284, numerator := 2898333691027549557217579499520 }, some { target := 285, numerator := 2771531592045094264089310396416 }, some { target := 286, numerator := 90572927844610923663049359360 }, some { target := 287, numerator := 2843989934320783003019749883904 }, some { target := 288, numerator := 90572927844610923663049359360 }, some { target := 289, numerator := 2771531592045094264089310396416 }, some { target := 290, numerator := 1575968944496230071737058852864 }, some { target := 291, numerator := 2843989934320783003019749883904 }, some { target := 292, numerator := 44398849229428274779626795958272 }, some { target := 293, numerator := 1739000214616529734330547699712 }, some { target := 294, numerator := 2898333691027549557217579499520 }, some { target := 295, numerator := 2771531592045094264089310396416 }, some { target := 296, numerator := 90572927844610923663049359360 }, some { target := 297, numerator := 1739000214616529734330547699712 }, some { target := 298, numerator := 90572927844610923663049359360 }, some { target := 299, numerator := 2789646177614016448821920268288 }, some { target := 300, numerator := 1575968944496230071737058852864 }, some { target := 301, numerator := 108687513413533108395659231232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 2901175440175622946419638272 }, some { target := 661, numerator := 77364678404683278571190353920 }, some { target := 662, numerator := 73979973724478385133700775936 }, some { target := 663, numerator := 2417646200146352455349698560 }, some { target := 664, numerator := 75914090684595467097980534784 }, some { target := 665, numerator := 2417646200146352455349698560 }, some { target := 666, numerator := 73979973724478385133700775936 }, some { target := 667, numerator := 42067043882546532723084754944 }, some { target := 668, numerator := 75914090684595467097980534784 }, some { target := 669, numerator := 1185130167311741973612422234112 }, some { target := 670, numerator := 46418807042809967142714212352 }, some { target := 671, numerator := 77364678404683278571190353920 }, some { target := 672, numerator := 73979973724478385133700775936 }, some { target := 673, numerator := 2417646200146352455349698560 }, some { target := 674, numerator := 46418807042809967142714212352 }, some { target := 675, numerator := 2417646200146352455349698560 }, some { target := 676, numerator := 74463502964507655624770715648 }, some { target := 677, numerator := 42067043882546532723084754944 }, some { target := 678, numerator := 2901175440175622946419638272 }]

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

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 1144, #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 142556812670532111192345804800 }, some { target := 15, numerator := 146629864461118742940698542080 }, some { target := 16, numerator := 142556812670532111192345804800 }, some { target := 17, numerator := 126264605508185584198934855680 }, some { target := 18, numerator := 5909998148141202666859821793280 }, some { target := 19, numerator := 1608855457281719540599331225600 }, some { target := 20, numerator := 146629864461118742940698542080 }, some { target := 21, numerator := 5909998148141202666859821793280 }, some { target := 22, numerator := 142556812670532111192345804800 }, some { target := 23, numerator := 142556812670532111192345804800 }, some { target := 24, numerator := 122191553717598952450582118400 }, some { target := 25, numerator := 142556812670532111192345804800 }, some { target := 26, numerator := 1608855457281719540599331225600 }, some { target := 27, numerator := 122191553717598952450582118400 }, some { target := 28, numerator := 142556812670532111192345804800 }, some { target := 29, numerator := 126264605508185584198934855680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 489372611736851812099072983040 }, some { target := 137, numerator := 503354686357904721016189353984 }, some { target := 138, numerator := 489372611736851812099072983040 }, some { target := 139, numerator := 433444313252640176430607499264 }, some { target := 140, numerator := 20287990275147770838735854239744 }, some { target := 141, numerator := 5522919475315899022260966522880 }, some { target := 142, numerator := 503354686357904721016189353984 }, some { target := 143, numerator := 20287990275147770838735854239744 }, some { target := 144, numerator := 489372611736851812099072983040 }, some { target := 145, numerator := 489372611736851812099072983040 }, some { target := 146, numerator := 419462238631587267513491128320 }, some { target := 147, numerator := 489372611736851812099072983040 }, some { target := 148, numerator := 5522919475315899022260966522880 }, some { target := 149, numerator := 419462238631587267513491128320 }, some { target := 150, numerator := 489372611736851812099072983040 }, some { target := 151, numerator := 433444313252640176430607499264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 142556812670532111192345804800 }, some { target := 268, numerator := 146629864461118742940698542080 }, some { target := 269, numerator := 142556812670532111192345804800 }, some { target := 270, numerator := 126264605508185584198934855680 }, some { target := 271, numerator := 5909998148141202666859821793280 }, some { target := 272, numerator := 1608855457281719540599331225600 }, some { target := 273, numerator := 146629864461118742940698542080 }, some { target := 274, numerator := 5909998148141202666859821793280 }, some { target := 275, numerator := 142556812670532111192345804800 }, some { target := 276, numerator := 142556812670532111192345804800 }, some { target := 277, numerator := 122191553717598952450582118400 }, some { target := 278, numerator := 142556812670532111192345804800 }, some { target := 279, numerator := 1608855457281719540599331225600 }, some { target := 280, numerator := 122191553717598952450582118400 }, some { target := 281, numerator := 142556812670532111192345804800 }, some { target := 282, numerator := 126264605508185584198934855680 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 30, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 4, numerator := 7253554917687775048237056000 }, some { target := 5, numerator := 145361240550463011966670602240 }, some { target := 6, numerator := 244009587431016752622694563840 }, some { target := 7, numerator := 234144752742961378557092167680 }, some { target := 8, numerator := 7253554917687775048237056000 }, some { target := 9, numerator := 234144752742961378557092167680 }, some { target := 10, numerator := 156386644025348430039990927360 }, some { target := 11, numerator := 7543697114395286050166538240 }, some { target := 12, numerator := 145361240550463011966670602240 }, some { target := 13, numerator := 6963412720980264046307573760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 7253554917687775048237056000 }, some { target := 127, numerator := 145361240550463011966670602240 }, some { target := 128, numerator := 244009587431016752622694563840 }, some { target := 129, numerator := 234144752742961378557092167680 }, some { target := 130, numerator := 7253554917687775048237056000 }, some { target := 131, numerator := 234144752742961378557092167680 }, some { target := 132, numerator := 156386644025348430039990927360 }, some { target := 133, numerator := 7543697114395286050166538240 }, some { target := 134, numerator := 145361240550463011966670602240 }, some { target := 135, numerator := 6963412720980264046307573760 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 20696810031802451470969733120 }, some { target := 1, numerator := 18917271225329717325802242048 }, some { target := 2, numerator := 20696810031802451470969733120 }, some { target := 3, numerator := 18917271225329717325802242048 }]

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

end Slot25

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2
