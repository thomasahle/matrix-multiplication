import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 1,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 49, #[140737438023680, 0, 140737538686976, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 22273241335045252586080829440 }, some { target := 11, numerator := 16586456313331571074741043200 }, some { target := 12, numerator := 17534253816950517993297674240 }, some { target := 13, numerator := 22747140086854726045359144960 }, some { target := 14, numerator := 304716897413491434315956879360 }, some { target := 15, numerator := 551144248354417633140680949760 }, some { target := 16, numerator := 16586456313331571074741043200 }, some { target := 17, numerator := 304716897413491434315956879360 }, some { target := 18, numerator := 18008152568759991452575989760 }, some { target := 19, numerator := 18008152568759991452575989760 }, some { target := 20, numerator := 17534253816950517993297674240 }, some { target := 21, numerator := 17534253816950517993297674240 }, some { target := 22, numerator := 551144248354417633140680949760 }, some { target := 23, numerator := 17534253816950517993297674240 }, some { target := 24, numerator := 22273241335045252586080829440 }, some { target := 25, numerator := 22747140086854726045359144960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 22273257266114603243492343808 }, some { target := 142, numerator := 16586468176893853479196426240 }, some { target := 143, numerator := 17534266358430645106579079168 }, some { target := 144, numerator := 22747156356882999057183670272 }, some { target := 145, numerator := 304717115364078508203522916352 }, some { target := 146, numerator := 551144642563644331323012677632 }, some { target := 147, numerator := 16586468176893853479196426240 }, some { target := 148, numerator := 304717115364078508203522916352 }, some { target := 149, numerator := 18008165449199040920270405632 }, some { target := 150, numerator := 18008165449199040920270405632 }, some { target := 151, numerator := 17534266358430645106579079168 }, some { target := 152, numerator := 17534266358430645106579079168 }, some { target := 153, numerator := 551144642563644331323012677632 }, some { target := 154, numerator := 17534266358430645106579079168 }, some { target := 155, numerator := 22273257266114603243492343808 }, some { target := 156, numerator := 22747156356882999057183670272 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 898, #[50401223114752, 0, 0, 180657883971584, 0, 50415869624320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 26, numerator := 18661584120069184074742235136 }, some { target := 27, numerator := 270592969741003169083762409472 }, some { target := 28, numerator := 478980659081775724585050701824 }, some { target := 29, numerator := 15551320100057653395618529280 }, some { target := 30, numerator := 298585345921106945195875762176 }, some { target := 31, numerator := 15551320100057653395618529280 }, some { target := 32, numerator := 475870395061764193905926995968 }, some { target := 33, numerator := 497642243201844908659792936960 }, some { target := 34, numerator := 298585345921106945195875762176 }, some { target := 35, numerator := 7623257113048261694532203053056 }, some { target := 36, numerator := 488311451141810316622421819392 }, some { target := 37, numerator := 270592969741003169083762409472 }, some { target := 38, numerator := 475870395061764193905926995968 }, some { target := 39, numerator := 15551320100057653395618529280 }, some { target := 40, numerator := 488311451141810316622421819392 }, some { target := 41, numerator := 15551320100057653395618529280 }, some { target := 42, numerator := 475870395061764193905926995968 }, some { target := 43, numerator := 497642243201844908659792936960 }, some { target := 44, numerator := 18661584120069184074742235136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 66890485792648248406900211712 }, some { target := 158, numerator := 969912043993399601900053069824 }, some { target := 159, numerator := 1716855802011305042443772100608 }, some { target := 160, numerator := 55742071493873540339083509760 }, some { target := 161, numerator := 1070247772682371974510403387392 }, some { target := 162, numerator := 55742071493873540339083509760 }, some { target := 163, numerator := 1705707387712530334375955398656 }, some { target := 164, numerator := 1783746287803953290850672312320 }, some { target := 165, numerator := 1070247772682371974510403387392 }, some { target := 166, numerator := 27324763446296809474218736484352 }, some { target := 167, numerator := 1750301044907629166647222206464 }, some { target := 168, numerator := 969912043993399601900053069824 }, some { target := 169, numerator := 1705707387712530334375955398656 }, some { target := 170, numerator := 55742071493873540339083509760 }, some { target := 171, numerator := 1750301044907629166647222206464 }, some { target := 172, numerator := 55742071493873540339083509760 }, some { target := 173, numerator := 1705707387712530334375955398656 }, some { target := 174, numerator := 1783746287803953290850672312320 }, some { target := 175, numerator := 66890485792648248406900211712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 18667007144620519411427573760 }, some { target := 268, numerator := 270671603596997531465699819520 }, some { target := 269, numerator := 479119850045259998226641059840 }, some { target := 270, numerator := 15555839287183766176189644800 }, some { target := 271, numerator := 298672114313928310582841180160 }, some { target := 272, numerator := 15555839287183766176189644800 }, some { target := 273, numerator := 476008682187823244991403130880 }, some { target := 274, numerator := 497786857189880517638068633600 }, some { target := 275, numerator := 298672114313928310582841180160 }, some { target := 276, numerator := 7625472418577482179568163880960 }, some { target := 277, numerator := 488453353617570257932354846720 }, some { target := 278, numerator := 270671603596997531465699819520 }, some { target := 279, numerator := 476008682187823244991403130880 }, some { target := 280, numerator := 15555839287183766176189644800 }, some { target := 281, numerator := 488453353617570257932354846720 }, some { target := 282, numerator := 15555839287183766176189644800 }, some { target := 283, numerator := 476008682187823244991403130880 }, some { target := 284, numerator := 497786857189880517638068633600 }, some { target := 285, numerator := 18667007144620519411427573760 }]

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
def data : BetaFourLocalSlotData := ⟨17, 790, #[3506505252864, 0, 137230932770816, 0, 0, 137230983102464, 0, 0, 0, 0, 0, 0, 3506555584512, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 80, numerator := 5901237898585322917157928960 }, some { target := 81, numerator := 6662687950015687164533145600 }, some { target := 82, numerator := 5710875385727731855314124800 }, some { target := 83, numerator := 75193192578748469428302643200 }, some { target := 84, numerator := 6662687950015687164533145600 }, some { target := 85, numerator := 5710875385727731855314124800 }, some { target := 86, numerator := 6662687950015687164533145600 }, some { target := 87, numerator := 6662687950015687164533145600 }, some { target := 88, numerator := 276216006156364630735359836160 }, some { target := 89, numerator := 6853050462873278226376949760 }, some { target := 90, numerator := 75193192578748469428302643200 }, some { target := 91, numerator := 276216006156364630735359836160 }, some { target := 92, numerator := 5901237898585322917157928960 }, some { target := 93, numerator := 6662687950015687164533145600 }, some { target := 94, numerator := 6853050462873278226376949760 }, some { target := 95, numerator := 6662687950015687164533145600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 230951423975169881526228746240 }, some { target := 177, numerator := 260751607713901479142516326400 }, some { target := 178, numerator := 223501378040486982122156851200 }, some { target := 179, numerator := 2942768144199745264608398540800 }, some { target := 180, numerator := 260751607713901479142516326400 }, some { target := 181, numerator := 223501378040486982122156851200 }, some { target := 182, numerator := 260751607713901479142516326400 }, some { target := 183, numerator := 260751607713901479142516326400 }, some { target := 184, numerator := 10810016651224887035308319703040 }, some { target := 185, numerator := 268201653648584378546588221440 }, some { target := 186, numerator := 2942768144199745264608398540800 }, some { target := 187, numerator := 10810016651224887035308319703040 }, some { target := 188, numerator := 230951423975169881526228746240 }, some { target := 189, numerator := 260751607713901479142516326400 }, some { target := 190, numerator := 268201653648584378546588221440 }, some { target := 191, numerator := 260751607713901479142516326400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 230951508680312824991276072960 }, some { target := 287, numerator := 260751703348740286280472985600 }, some { target := 288, numerator := 223501460013205959668976844800 }, some { target := 289, numerator := 2942769223507211802308195123200 }, some { target := 290, numerator := 260751703348740286280472985600 }, some { target := 291, numerator := 223501460013205959668976844800 }, some { target := 292, numerator := 260751703348740286280472985600 }, some { target := 293, numerator := 260751703348740286280472985600 }, some { target := 294, numerator := 10810020615972061582656180060160 }, some { target := 295, numerator := 268201752015847151602772213760 }, some { target := 296, numerator := 2942769223507211802308195123200 }, some { target := 297, numerator := 10810020615972061582656180060160 }, some { target := 298, numerator := 230951508680312824991276072960 }, some { target := 299, numerator := 260751703348740286280472985600 }, some { target := 300, numerator := 268201752015847151602772213760 }, some { target := 301, numerator := 260751703348740286280472985600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 5901322603728266382205255680 }, some { target := 574, numerator := 6662783584854494302489804800 }, some { target := 575, numerator := 5710957358446709402134118400 }, some { target := 576, numerator := 75194271886215007128099225600 }, some { target := 577, numerator := 6662783584854494302489804800 }, some { target := 578, numerator := 5710957358446709402134118400 }, some { target := 579, numerator := 6662783584854494302489804800 }, some { target := 580, numerator := 6662783584854494302489804800 }, some { target := 581, numerator := 276219970903539178083220193280 }, some { target := 582, numerator := 6853148830136051282560942080 }, some { target := 583, numerator := 75194271886215007128099225600 }, some { target := 584, numerator := 276219970903539178083220193280 }, some { target := 585, numerator := 5901322603728266382205255680 }, some { target := 586, numerator := 6662783584854494302489804800 }, some { target := 587, numerator := 6853148830136051282560942080 }, some { target := 588, numerator := 6662783584854494302489804800 }]

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

end Slot17

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 44, #[69122129920, 22265714442240, 0, 236805236457472, 0, 0, 0, 0, 0, 0, 0, 22265781551104, 0, 0, 0, 0, 0, 0, 69122129920], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 131, numerator := 5016038648523101275422720 }, some { target := 132, numerator := 104709806787919739124449280 }, some { target := 133, numerator := 5434041869233359715041280 }, some { target := 134, numerator := 112651867981414649477201920 }, some { target := 135, numerator := 168664299556589280386088960 }, some { target := 136, numerator := 5225040258878230495232000 }, some { target := 137, numerator := 168664299556589280386088960 }, some { target := 138, numerator := 175770354308663673859604480 }, some { target := 139, numerator := 104709806787919739124449280 }, some { target := 140, numerator := 5225040258878230495232000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 1615773187378871025889443840 }, some { target := 228, numerator := 33729265286533932665442140160 }, some { target := 229, numerator := 1750420952993776944713564160 }, some { target := 230, numerator := 36287572833217145123100426240 }, some { target := 231, numerator := 54330373425614538245532549120 }, some { target := 232, numerator := 1683097070186323985301504000 }, some { target := 233, numerator := 54330373425614538245532549120 }, some { target := 234, numerator := 56619385441067938865542594560 }, some { target := 235, numerator := 33729265286533932665442140160 }, some { target := 236, numerator := 1683097070186323985301504000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 17184427326213550822184189952 }, some { target := 303, numerator := 358724920434707873413094965248 }, some { target := 304, numerator := 18616462936731346724032872448 }, some { target := 305, numerator := 385933597034545995548219932672 }, some { target := 306, numerator := 577826368843930646395943387136 }, some { target := 307, numerator := 17900445131472448773108531200 }, some { target := 308, numerator := 577826368843930646395943387136 }, some { target := 309, numerator := 602170974222733176727370989568 }, some { target := 310, numerator := 358724920434707873413094965248 }, some { target := 311, numerator := 17900445131472448773108531200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 1615778057319306485211070464 }, some { target := 590, numerator := 33729366946540522878781095936 }, some { target := 591, numerator := 1750426228762582025645326336 }, some { target := 592, numerator := 36287682203962758147031957504 }, some { target := 593, numerator := 54330537177361680565222244352 }, some { target := 594, numerator := 1683102143040944255428198400 }, some { target := 595, numerator := 54330537177361680565222244352 }, some { target := 596, numerator := 56619556091897364752604594176 }, some { target := 597, numerator := 33729366946540522878781095936 }, some { target := 598, numerator := 1683102143040944255428198400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 5016038648523101275422720 }, some { target := 764, numerator := 104709806787919739124449280 }, some { target := 765, numerator := 5434041869233359715041280 }, some { target := 766, numerator := 112651867981414649477201920 }, some { target := 767, numerator := 168664299556589280386088960 }, some { target := 768, numerator := 5225040258878230495232000 }, some { target := 769, numerator := 168664299556589280386088960 }, some { target := 770, numerator := 175770354308663673859604480 }, some { target := 771, numerator := 104709806787919739124449280 }, some { target := 772, numerator := 5225040258878230495232000 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 1, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[67207648247808, 73529840107520, 67207648247808, 73529840107520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 263, numerator := 53623239258706889561604096 }, some { target := 264, numerator := 58667552154208969152266240 }, some { target := 265, numerator := 53623239258706889561604096 }, some { target := 266, numerator := 58667552154208969152266240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 9405012373406151773339516928 }, some { target := 339, numerator := 10289737463747016766332600320 }, some { target := 340, numerator := 9405012373406151773339516928 }, some { target := 341, numerator := 10289737463747016766332600320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 9405013500963383278835859456 }, some { target := 600, numerator := 10289738697373026695658864640 }, some { target := 601, numerator := 9405013500963383278835859456 }, some { target := 602, numerator := 10289738697373026695658864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 53622111701475384065261568 }, some { target := 774, numerator := 58666318528199039826001920 }, some { target := 775, numerator := 53622111701475384065261568 }, some { target := 776, numerator := 58666318528199039826001920 }]

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

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 0, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot20

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent1
