import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 2,
parent 50; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

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
  [some { target := 774, numerator := 14205128665895484893993893888 }, some { target := 777, numerator := 50817909904839850675201376256 }, some { target := 779, numerator := 14205123943529002024348680192 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 1, #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 411, numerator := 161693828373456652116951040 }, some { target := 412, numerator := 192011421193479774388879360 }, some { target := 413, numerator := 146535031963445090980986880 }, some { target := 414, numerator := 1510826708864485593217761280 }, some { target := 415, numerator := 181905556920138733631569920 }, some { target := 416, numerator := 146535031963445090980986880 }, some { target := 417, numerator := 181905556920138733631569920 }, some { target := 418, numerator := 181905556920138733631569920 }, some { target := 419, numerator := 7791621354745942423885578240 }, some { target := 420, numerator := 181905556920138733631569920 }, some { target := 421, numerator := 1510826708864485593217761280 }, some { target := 422, numerator := 7791621354745942423885578240 }, some { target := 423, numerator := 161693828373456652116951040 }, some { target := 424, numerator := 181905556920138733631569920 }, some { target := 425, numerator := 181905556920138733631569920 }, some { target := 426, numerator := 192011421193479774388879360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 147791181447888416607830016 }, some { target := 628, numerator := 175502027969367494721798144 }, some { target := 629, numerator := 133935758187148877550845952 }, some { target := 630, numerator := 1380923851653707392679411712 }, some { target := 631, numerator := 166265079128874468683808768 }, some { target := 632, numerator := 133935758187148877550845952 }, some { target := 633, numerator := 166265079128874468683808768 }, some { target := 634, numerator := 166265079128874468683808768 }, some { target := 635, numerator := 7121687556020123075289808896 }, some { target := 636, numerator := 166265079128874468683808768 }, some { target := 637, numerator := 1380923851653707392679411712 }, some { target := 638, numerator := 7121687556020123075289808896 }, some { target := 639, numerator := 147791181447888416607830016 }, some { target := 640, numerator := 166265079128874468683808768 }, some { target := 641, numerator := 166265079128874468683808768 }, some { target := 642, numerator := 175502027969367494721798144 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 161693828373456652116951040 }, some { target := 724, numerator := 192011421193479774388879360 }, some { target := 725, numerator := 146535031963445090980986880 }, some { target := 726, numerator := 1510826708864485593217761280 }, some { target := 727, numerator := 181905556920138733631569920 }, some { target := 728, numerator := 146535031963445090980986880 }, some { target := 729, numerator := 181905556920138733631569920 }, some { target := 730, numerator := 181905556920138733631569920 }, some { target := 731, numerator := 7791621354745942423885578240 }, some { target := 732, numerator := 181905556920138733631569920 }, some { target := 733, numerator := 1510826708864485593217761280 }, some { target := 734, numerator := 7791621354745942423885578240 }, some { target := 735, numerator := 161693828373456652116951040 }, some { target := 736, numerator := 181905556920138733631569920 }, some { target := 737, numerator := 181905556920138733631569920 }, some { target := 738, numerator := 192011421193479774388879360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 147791181447888416607830016 }, some { target := 759, numerator := 175502027969367494721798144 }, some { target := 760, numerator := 133935758187148877550845952 }, some { target := 761, numerator := 1380923851653707392679411712 }, some { target := 762, numerator := 166265079128874468683808768 }, some { target := 763, numerator := 133935758187148877550845952 }, some { target := 764, numerator := 166265079128874468683808768 }, some { target := 765, numerator := 166265079128874468683808768 }, some { target := 766, numerator := 7121687556020123075289808896 }, some { target := 767, numerator := 166265079128874468683808768 }, some { target := 768, numerator := 1380923851653707392679411712 }, some { target := 769, numerator := 7121687556020123075289808896 }, some { target := 770, numerator := 147791181447888416607830016 }, some { target := 771, numerator := 166265079128874468683808768 }, some { target := 772, numerator := 166265079128874468683808768 }, some { target := 773, numerator := 175502027969367494721798144 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 4, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 411, numerator := 1044436350283313692622716928 }, some { target := 413, numerator := 38569644906848855104149258240 }, some { target := 416, numerator := 38569635462115889364858830848 }, some { target := 423, numerator := 1044445795016279431913144320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 1044436350283313692622716928 }, some { target := 629, numerator := 38569644906848855104149258240 }, some { target := 632, numerator := 38569635462115889364858830848 }, some { target := 639, numerator := 1044445795016279431913144320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 1044436350283313692622716928 }, some { target := 725, numerator := 38569644906848855104149258240 }, some { target := 728, numerator := 38569635462115889364858830848 }, some { target := 735, numerator := 1044445795016279431913144320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 1044436350283313692622716928 }, some { target := 760, numerator := 38569644906848855104149258240 }, some { target := 763, numerator := 38569635462115889364858830848 }, some { target := 770, numerator := 1044445795016279431913144320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 10, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 142, numerator := 82760106719118066135859200 }, some { target := 143, numerator := 1390369792881183511082434560 }, some { target := 144, numerator := 3012467884575897607345274880 }, some { target := 145, numerator := 99312128062941679363031040 }, some { target := 146, numerator := 1588994049007066869808496640 }, some { target := 147, numerator := 115864149406765292590202880 }, some { target := 148, numerator := 3012467884575897607345274880 }, some { target := 149, numerator := 3012467884575897607345274880 }, some { target := 150, numerator := 1588994049007066869808496640 }, some { target := 151, numerator := 37175839938227835308227952640 }, some { target := 152, numerator := 2979363841888250380890931200 }, some { target := 153, numerator := 1390369792881183511082434560 }, some { target := 154, numerator := 3012467884575897607345274880 }, some { target := 155, numerator := 115864149406765292590202880 }, some { target := 156, numerator := 2979363841888250380890931200 }, some { target := 157, numerator := 115864149406765292590202880 }, some { target := 158, numerator := 3012467884575897607345274880 }, some { target := 159, numerator := 3012467884575897607345274880 }, some { target := 160, numerator := 99312128062941679363031040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 801620442253467207493222400 }, some { target := 358, numerator := 13467223429858249085886136320 }, some { target := 359, numerator := 29178984098026206352753295360 }, some { target := 360, numerator := 961944530704160648991866880 }, some { target := 361, numerator := 15391112491266570383869870080 }, some { target := 362, numerator := 1122268619154854090490511360 }, some { target := 363, numerator := 29178984098026206352753295360 }, some { target := 364, numerator := 29178984098026206352753295360 }, some { target := 365, numerator := 15391112491266570383869870080 }, some { target := 366, numerator := 360087902660257469605955502080 }, some { target := 367, numerator := 28858335921124819469756006400 }, some { target := 368, numerator := 13467223429858249085886136320 }, some { target := 369, numerator := 29178984098026206352753295360 }, some { target := 370, numerator := 1122268619154854090490511360 }, some { target := 371, numerator := 28858335921124819469756006400 }, some { target := 372, numerator := 1122268619154854090490511360 }, some { target := 373, numerator := 29178984098026206352753295360 }, some { target := 374, numerator := 29178984098026206352753295360 }, some { target := 375, numerator := 961944530704160648991866880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 82760106719118066135859200 }, some { target := 670, numerator := 1390369792881183511082434560 }, some { target := 671, numerator := 3012467884575897607345274880 }, some { target := 672, numerator := 99312128062941679363031040 }, some { target := 673, numerator := 1588994049007066869808496640 }, some { target := 674, numerator := 115864149406765292590202880 }, some { target := 675, numerator := 3012467884575897607345274880 }, some { target := 676, numerator := 3012467884575897607345274880 }, some { target := 677, numerator := 1588994049007066869808496640 }, some { target := 678, numerator := 37175839938227835308227952640 }, some { target := 679, numerator := 2979363841888250380890931200 }, some { target := 680, numerator := 1390369792881183511082434560 }, some { target := 681, numerator := 3012467884575897607345274880 }, some { target := 682, numerator := 115864149406765292590202880 }, some { target := 683, numerator := 2979363841888250380890931200 }, some { target := 684, numerator := 115864149406765292590202880 }, some { target := 685, numerator := 3012467884575897607345274880 }, some { target := 686, numerator := 3012467884575897607345274880 }, some { target := 687, numerator := 99312128062941679363031040 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 27, #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 142, numerator := 8457218803555378573344768 }, some { target := 143, numerator := 1350171243103252033333886976 }, some { target := 145, numerator := 13472678617460798439781564416 }, some { target := 153, numerator := 1350171243103252033333886976 }, some { target := 160, numerator := 8456253808256022642425856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 202427624265744867787800576 }, some { target := 283, numerator := 32317002012342355120443359232 }, some { target := 285, numerator := 322475081746964917494126477312 }, some { target := 293, numerator := 32317002012342355120443359232 }, some { target := 300, numerator := 202404526636321574215483392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 151411497934620487361495040 }, some { target := 358, numerator := 24172420642654996080655073280 }, some { target := 360, numerator := 241204407506153004325121556480 }, some { target := 368, numerator := 24172420642654996080655073280 }, some { target := 375, numerator := 151394221405873953759559680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 175691900306118187136581632 }, some { target := 393, numerator := 28048718727693364821516877824 }, some { target := 395, numerator := 279884033214346909523204112384 }, some { target := 403, numerator := 28048718727693364821516877824 }, some { target := 410, numerator := 175671853306996083281362944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 8457218803555378573344768 }, some { target := 499, numerator := 1350171243103252033333886976 }, some { target := 501, numerator := 13472678617460798439781564416 }, some { target := 509, numerator := 1350171243103252033333886976 }, some { target := 516, numerator := 8456253808256022642425856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 175419086796326078150344704 }, some { target := 574, numerator := 28005164816625517981731913728 }, some { target := 576, numerator := 279449430678299786992888578048 }, some { target := 584, numerator := 28005164816625517981731913728 }, some { target := 591, numerator := 175399070926084598679994368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 176237527325702405109055488 }, some { target := 609, numerator := 28135826549829058501086806016 }, some { target := 611, numerator := 280753238286441154583835181056 }, some { target := 619, numerator := 28135826549829058501086806016 }, some { target := 626, numerator := 176217418068819052484100096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 8457218803555378573344768 }, some { target := 670, numerator := 1350171243103252033333886976 }, some { target := 672, numerator := 13472678617460798439781564416 }, some { target := 680, numerator := 1350171243103252033333886976 }, some { target := 687, numerator := 8456253808256022642425856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 202427624265744867787800576 }, some { target := 705, numerator := 32317002012342355120443359232 }, some { target := 707, numerator := 322475081746964917494126477312 }, some { target := 715, numerator := 32317002012342355120443359232 }, some { target := 722, numerator := 202404526636321574215483392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 8457218803555378573344768 }, some { target := 740, numerator := 1350171243103252033333886976 }, some { target := 742, numerator := 13472678617460798439781564416 }, some { target := 750, numerator := 1350171243103252033333886976 }, some { target := 757, numerator := 8456253808256022642425856 }]

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

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent0
