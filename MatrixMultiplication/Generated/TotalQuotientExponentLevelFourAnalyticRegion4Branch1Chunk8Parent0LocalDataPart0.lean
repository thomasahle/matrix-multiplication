import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk8Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 4, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 0, #[2363792293888, 138373696061440, 0, 0, 0, 0, 138419632078848, 0, 0, 0, 0, 0, 0, 0, 2317856276480, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[52009789030400, 0, 0, 177455516090368, 0, 52009671589888, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737840676864, 0, 140737136033792, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 0, #[434043355136, 21321559834624, 0, 237963803885568, 0, 0, 0, 0, 0, 0, 0, 21321593389056, 0, 0, 0, 0, 0, 0, 433976246272], #[1236950581248, 9208409882624, 9345848836096, 1374389534720, 8246337208320, 1374389534720, 9139690405888, 9345848836096, 8246337208320, 166507292131328, 8246337208320, 9139690405888, 9139690405888, 1374389534720, 8246337208320, 1374389534720, 9345848836096, 9345848836096, 1236950581248]⟩

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
def data : BetaFourLocalSlotData := ⟨7, 1, #[2685629628416, 138051204415488, 0, 0, 0, 0, 138083299229696, 0, 0, 0, 0, 0, 0, 0, 2654843437056, 0, 0, 0, 0], #[3418877853696, 0, 137318493061120, 0, 0, 137345185611776, 0, 0, 0, 0, 0, 0, 3392420184064, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 9181839659821280092225536 }, some { target := 202, numerator := 368786613494380779976785920 }, some { target := 205, numerator := 368858299799280528513826816 }, some { target := 212, numerator := 9110784158358738644762624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 471980205452171371660443648 }, some { target := 298, numerator := 18956983355607447633458626560 }, some { target := 301, numerator := 18960668294374429857769586688 }, some { target := 308, numerator := 468327692293446690492383232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 472089933701685590586556416 }, some { target := 661, numerator := 18961390567129566817047019520 }, some { target := 664, numerator := 18965076362589003083306500096 }, some { target := 671, numerator := 468436571388969693734764544 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 9076585431980928952958976 }, some { target := 1038, numerator := 364559100089734307480862720 }, some { target := 1041, numerator := 364629964632661673908371456 }, some { target := 1048, numerator := 9006344461398617918275584 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[51495399587840, 0, 0, 178472282488832, 0, 51507294633984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 0, #[4108287213568, 0, 136629217918976, 0, 0, 136629217918976, 0, 0, 0, 0, 0, 0, 4108253659136, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 2, #[633675448320, 21536358531072, 0, 237134657093632, 0, 0, 0, 0, 0, 0, 0, 21536694075392, 0, 0, 0, 0, 0, 0, 633591562240], #[633675448320, 21536358531072, 0, 237134657093632, 0, 0, 0, 0, 0, 0, 0, 21536694075392, 0, 0, 0, 0, 0, 0, 633591562240]⟩

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
  [some { target := 71, numerator := 803089147607105981644800 }, some { target := 72, numerator := 27294123294714612500398080 }, some { target := 74, numerator := 300532820292033451634196480 }, some { target := 82, numerator := 27294548547109426959482880 }, some { target := 89, numerator := 802982834508402366873600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 27294123294714612500398080 }, some { target := 147, numerator := 927629477557755427178938368 }, some { target := 149, numerator := 10214033990622549768570667008 }, some { target := 157, numerator := 927643930363312596685160448 }, some { target := 164, numerator := 27290510093325320123842560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 300532820292033451634196480 }, some { target := 243, numerator := 10214033990622549768570667008 }, some { target := 245, numerator := 112465691189828866834429902848 }, some { target := 253, numerator := 10214193128997075600422207488 }, some { target := 260, numerator := 300493035698401993671311360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 27294548547109426959482880 }, some { target := 641, numerator := 927643930363312596685160448 }, some { target := 643, numerator := 10214193128997075600422207488 }, some { target := 651, numerator := 927658383394049747559907328 }, some { target := 658, numerator := 27290935289425139240796160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 802982834508402366873600 }, some { target := 1018, numerator := 27290510093325320123842560 }, some { target := 1020, numerator := 300493035698401993671311360 }, some { target := 1028, numerator := 27290935289425139240796160 }, some { target := 1035, numerator := 802876535483447587635200 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 0, #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[4108287213568, 0, 136629217918976, 0, 0, 136629217918976, 0, 0, 0, 0, 0, 0, 4108253659136, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 0, #[51495399587840, 0, 0, 178472282488832, 0, 51507294633984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 1, #[3418877853696, 0, 137318493061120, 0, 0, 137345185611776, 0, 0, 0, 0, 0, 0, 3392420184064, 0, 0, 0, 0, 0, 0], #[2685629628416, 138051204415488, 0, 0, 0, 0, 138083299229696, 0, 0, 0, 0, 0, 0, 0, 2654843437056, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 29, numerator := 9181839659821280092225536 }, some { target := 30, numerator := 471980205452171371660443648 }, some { target := 35, numerator := 472089933701685590586556416 }, some { target := 43, numerator := 9076585431980928952958976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 368786613494380779976785920 }, some { target := 105, numerator := 18956983355607447633458626560 }, some { target := 110, numerator := 18961390567129566817047019520 }, some { target := 118, numerator := 364559100089734307480862720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 368858299799280528513826816 }, some { target := 227, numerator := 18960668294374429857769586688 }, some { target := 232, numerator := 18965076362589003083306500096 }, some { target := 240, numerator := 364629964632661673908371456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 9110784158358738644762624 }, some { target := 625, numerator := 468327692293446690492383232 }, some { target := 630, numerator := 468436571388969693734764544 }, some { target := 638, numerator := 9006344461398617918275584 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 0, #[1236950581248, 9208409882624, 9345848836096, 1374389534720, 8246337208320, 1374389534720, 9139690405888, 9345848836096, 8246337208320, 166507292131328, 8246337208320, 9139690405888, 9139690405888, 1374389534720, 8246337208320, 1374389534720, 9345848836096, 9345848836096, 1236950581248], #[434043355136, 21321559834624, 0, 237963803885568, 0, 0, 0, 0, 0, 0, 0, 21321593389056, 0, 0, 0, 0, 0, 0, 433976246272]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 0, #[140737840676864, 0, 140737136033792, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 0, #[52009789030400, 0, 0, 177455516090368, 0, 52009671589888, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot16

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8.Parent0
