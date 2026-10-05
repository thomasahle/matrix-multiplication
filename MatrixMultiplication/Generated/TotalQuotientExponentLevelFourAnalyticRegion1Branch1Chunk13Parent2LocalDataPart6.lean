import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 0, numerator := 19884411881021420665567182848 }, some { target := 1, numerator := 19826383441679918465181286400 }, some { target := 2, numerator := 19690983749883079997614194688 }, some { target := 3, numerator := 19826383441679918465181286400 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 6, #[140737471578112, 0, 140737505132544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 4, numerator := 1798881405143168355089252352 }, some { target := 5, numerator := 44101608642219611286059089920 }, some { target := 6, numerator := 32611979022272923082585800704 }, some { target := 7, numerator := 36383827129831179310998749184 }, some { target := 8, numerator := 1798881405143168355089252352 }, some { target := 9, numerator := 36325798697407206138253934592 }, some { target := 10, numerator := 36964111454070911038446895104 }, some { target := 11, numerator := 1798881405143168355089252352 }, some { target := 12, numerator := 44101608642219611286059089920 }, some { target := 13, numerator := 1798881405143168355089252352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 1798881834029968068836327424 }, some { target := 127, numerator := 44101619156863733300503511040 }, some { target := 128, numerator := 32611986797575550151161806848 }, some { target := 129, numerator := 36383835804412579972915396608 }, some { target := 130, numerator := 1798881834029968068836327424 }, some { target := 131, numerator := 36325807358153548744888418304 }, some { target := 132, numerator := 36964120267002892253185179648 }, some { target := 133, numerator := 1798881834029968068836327424 }, some { target := 134, numerator := 44101619156863733300503511040 }, some { target := 135, numerator := 1798881834029968068836327424 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 56, #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 9006655850554068664028495872 }, some { target := 15, numerator := 6707084144029625600872284160 }, some { target := 16, numerator := 7090346095117032778064986112 }, some { target := 17, numerator := 9198286826097772252624846848 }, some { target := 18, numerator := 123218717274601407467453677568 }, some { target := 19, numerator := 222866824557327273537556185088 }, some { target := 20, numerator := 6707084144029625600872284160 }, some { target := 21, numerator := 123218717274601407467453677568 }, some { target := 22, numerator := 7281977070660736366661337088 }, some { target := 23, numerator := 7281977070660736366661337088 }, some { target := 24, numerator := 7090346095117032778064986112 }, some { target := 25, numerator := 7090346095117032778064986112 }, some { target := 26, numerator := 222866824557327273537556185088 }, some { target := 27, numerator := 7090346095117032778064986112 }, some { target := 28, numerator := 9006655850554068664028495872 }, some { target := 29, numerator := 9198286826097772252624846848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 32896975448992526602390732800 }, some { target := 137, numerator := 24497747674781668746461184000 }, some { target := 138, numerator := 25897618970483478389116108800 }, some { target := 139, numerator := 33596911096843431423718195200 }, some { target := 140, numerator := 450058621568131800113558323200 }, some { target := 141, numerator := 814025158450602307203838771200 }, some { target := 142, numerator := 24497747674781668746461184000 }, some { target := 143, numerator := 450058621568131800113558323200 }, some { target := 144, numerator := 26597554618334383210443571200 }, some { target := 145, numerator := 26597554618334383210443571200 }, some { target := 146, numerator := 25897618970483478389116108800 }, some { target := 147, numerator := 25897618970483478389116108800 }, some { target := 148, numerator := 814025158450602307203838771200 }, some { target := 149, numerator := 25897618970483478389116108800 }, some { target := 150, numerator := 32896975448992526602390732800 }, some { target := 151, numerator := 33596911096843431423718195200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 9006652816064668538807255040 }, some { target := 268, numerator := 6707081884303476571452211200 }, some { target := 269, numerator := 7090343706263675232678051840 }, some { target := 270, numerator := 9198283727044767869420175360 }, some { target := 271, numerator := 123218675760203869584107765760 }, some { target := 272, numerator := 222866749469855521502826332160 }, some { target := 273, numerator := 6707081884303476571452211200 }, some { target := 274, numerator := 123218675760203869584107765760 }, some { target := 275, numerator := 7281974617243774563290972160 }, some { target := 276, numerator := 7281974617243774563290972160 }, some { target := 277, numerator := 7090343706263675232678051840 }, some { target := 278, numerator := 7090343706263675232678051840 }, some { target := 279, numerator := 222866749469855521502826332160 }, some { target := 280, numerator := 7090343706263675232678051840 }, some { target := 281, numerator := 9006652816064668538807255040 }, some { target := 282, numerator := 9198283727044767869420175360 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 67, #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 56, numerator := 68342087740089505532608512 }, some { target := 57, numerator := 990960272231297830222823424 }, some { target := 58, numerator := 1754113585328963975336951808 }, some { target := 59, numerator := 56951739783407921277173760 }, some { target := 60, numerator := 1093473403841432088521736192 }, some { target := 61, numerator := 56951739783407921277173760 }, some { target := 62, numerator := 1742723237372282391081517056 }, some { target := 63, numerator := 1822455673069053480869560320 }, some { target := 64, numerator := 1093473403841432088521736192 }, some { target := 65, numerator := 27917742841826563010070577152 }, some { target := 66, numerator := 1788284629199008728103256064 }, some { target := 67, numerator := 990960272231297830222823424 }, some { target := 68, numerator := 1742723237372282391081517056 }, some { target := 69, numerator := 56951739783407921277173760 }, some { target := 70, numerator := 1788284629199008728103256064 }, some { target := 71, numerator := 56951739783407921277173760 }, some { target := 72, numerator := 1742723237372282391081517056 }, some { target := 73, numerator := 1822455673069053480869560320 }, some { target := 74, numerator := 68342087740089505532608512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 91, numerator := 77834044370657492412137472 }, some { target := 92, numerator := 1128593643374533639975993344 }, some { target := 93, numerator := 1997740472180208971911528448 }, some { target := 94, numerator := 64861703642214577010114560 }, some { target := 95, numerator := 1245344709930519878594199552 }, some { target := 96, numerator := 64861703642214577010114560 }, some { target := 97, numerator := 1984768131451766056509505536 }, some { target := 98, numerator := 2075574516550866464323665920 }, some { target := 99, numerator := 1245344709930519878594199552 }, some { target := 100, numerator := 31795207125413585650358157312 }, some { target := 101, numerator := 2036657494365537718117597184 }, some { target := 102, numerator := 1128593643374533639975993344 }, some { target := 103, numerator := 1984768131451766056509505536 }, some { target := 104, numerator := 64861703642214577010114560 }, some { target := 105, numerator := 2036657494365537718117597184 }, some { target := 106, numerator := 64861703642214577010114560 }, some { target := 107, numerator := 1984768131451766056509505536 }, some { target := 108, numerator := 2075574516550866464323665920 }, some { target := 109, numerator := 77834044370657492412137472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 60748522435635116028985344 }, some { target := 153, numerator := 880853575316709182420287488 }, some { target := 154, numerator := 1559212075847967978077290496 }, some { target := 155, numerator := 50623768696362596690821120 }, some { target := 156, numerator := 971976358970161856463765504 }, some { target := 157, numerator := 50623768696362596690821120 }, some { target := 158, numerator := 1549087322108695458739126272 }, some { target := 159, numerator := 1619960598283603094106275840 }, some { target := 160, numerator := 971976358970161856463765504 }, some { target := 161, numerator := 24815771414956944897840513024 }, some { target := 162, numerator := 1589586337065785536091783168 }, some { target := 163, numerator := 880853575316709182420287488 }, some { target := 164, numerator := 1549087322108695458739126272 }, some { target := 165, numerator := 50623768696362596690821120 }, some { target := 166, numerator := 1589586337065785536091783168 }, some { target := 167, numerator := 50623768696362596690821120 }, some { target := 168, numerator := 1549087322108695458739126272 }, some { target := 169, numerator := 1619960598283603094106275840 }, some { target := 170, numerator := 60748522435635116028985344 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 814409878902733274263584768 }, some { target := 188, numerator := 11808943244089632476821979136 }, some { target := 189, numerator := 20903186891836820706098675712 }, some { target := 190, numerator := 678674899085611061886320640 }, some { target := 191, numerator := 13030558062443732388217356288 }, some { target := 192, numerator := 678674899085611061886320640 }, some { target := 193, numerator := 20767451912019698493721411584 }, some { target := 194, numerator := 21717596770739553980362260480 }, some { target := 195, numerator := 13030558062443732388217356288 }, some { target := 196, numerator := 332686435531766542536674377728 }, some { target := 197, numerator := 21310391831288187343230468096 }, some { target := 198, numerator := 11808943244089632476821979136 }, some { target := 199, numerator := 20767451912019698493721411584 }, some { target := 200, numerator := 678674899085611061886320640 }, some { target := 201, numerator := 21310391831288187343230468096 }, some { target := 202, numerator := 678674899085611061886320640 }, some { target := 203, numerator := 20767451912019698493721411584 }, some { target := 204, numerator := 21717596770739553980362260480 }, some { target := 205, numerator := 814409878902733274263584768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 222, numerator := 72138870392316700284420096 }, some { target := 223, numerator := 1046013620688592154124091392 }, some { target := 224, numerator := 1851564340069461973966782464 }, some { target := 225, numerator := 60115725326930583570350080 }, some { target := 226, numerator := 1154221926277067204550721536 }, some { target := 227, numerator := 60115725326930583570350080 }, some { target := 228, numerator := 1839541195004075857252712448 }, some { target := 229, numerator := 1923703210461778674251202560 }, some { target := 230, numerator := 1154221926277067204550721536 }, some { target := 231, numerator := 29468728555261372066185609216 }, some { target := 232, numerator := 1887633775265620324108992512 }, some { target := 233, numerator := 1046013620688592154124091392 }, some { target := 234, numerator := 1839541195004075857252712448 }, some { target := 235, numerator := 60115725326930583570350080 }, some { target := 236, numerator := 1887633775265620324108992512 }, some { target := 237, numerator := 60115725326930583570350080 }, some { target := 238, numerator := 1839541195004075857252712448 }, some { target := 239, numerator := 1923703210461778674251202560 }, some { target := 240, numerator := 72138870392316700284420096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 60748522435635116028985344 }, some { target := 284, numerator := 880853575316709182420287488 }, some { target := 285, numerator := 1559212075847967978077290496 }, some { target := 286, numerator := 50623768696362596690821120 }, some { target := 287, numerator := 971976358970161856463765504 }, some { target := 288, numerator := 50623768696362596690821120 }, some { target := 289, numerator := 1549087322108695458739126272 }, some { target := 290, numerator := 1619960598283603094106275840 }, some { target := 291, numerator := 971976358970161856463765504 }, some { target := 292, numerator := 24815771414956944897840513024 }, some { target := 293, numerator := 1589586337065785536091783168 }, some { target := 294, numerator := 880853575316709182420287488 }, some { target := 295, numerator := 1549087322108695458739126272 }, some { target := 296, numerator := 50623768696362596690821120 }, some { target := 297, numerator := 1589586337065785536091783168 }, some { target := 298, numerator := 50623768696362596690821120 }, some { target := 299, numerator := 1549087322108695458739126272 }, some { target := 300, numerator := 1619960598283603094106275840 }, some { target := 301, numerator := 60748522435635116028985344 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 318, numerator := 72138870392316700284420096 }, some { target := 319, numerator := 1046013620688592154124091392 }, some { target := 320, numerator := 1851564340069461973966782464 }, some { target := 321, numerator := 60115725326930583570350080 }, some { target := 322, numerator := 1154221926277067204550721536 }, some { target := 323, numerator := 60115725326930583570350080 }, some { target := 324, numerator := 1839541195004075857252712448 }, some { target := 325, numerator := 1923703210461778674251202560 }, some { target := 326, numerator := 1154221926277067204550721536 }, some { target := 327, numerator := 29468728555261372066185609216 }, some { target := 328, numerator := 1887633775265620324108992512 }, some { target := 329, numerator := 1046013620688592154124091392 }, some { target := 330, numerator := 1839541195004075857252712448 }, some { target := 331, numerator := 60115725326930583570350080 }, some { target := 332, numerator := 1887633775265620324108992512 }, some { target := 333, numerator := 60115725326930583570350080 }, some { target := 334, numerator := 1839541195004075857252712448 }, some { target := 335, numerator := 1923703210461778674251202560 }, some { target := 336, numerator := 72138870392316700284420096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 419, numerator := 70240479066203102908514304 }, some { target := 420, numerator := 1018486946459944992173457408 }, some { target := 421, numerator := 1802838962699212974651867136 }, some { target := 422, numerator := 58533732555169252423761920 }, some { target := 423, numerator := 1123847665059249646536228864 }, some { target := 424, numerator := 58533732555169252423761920 }, some { target := 425, numerator := 1791132216188179124167114752 }, some { target := 426, numerator := 1873079441765416077560381440 }, some { target := 427, numerator := 1123847665059249646536228864 }, some { target := 428, numerator := 28693235698543967538128093184 }, some { target := 429, numerator := 1837959202232314526106124288 }, some { target := 430, numerator := 1018486946459944992173457408 }, some { target := 431, numerator := 1791132216188179124167114752 }, some { target := 432, numerator := 58533732555169252423761920 }, some { target := 433, numerator := 1837959202232314526106124288 }, some { target := 434, numerator := 58533732555169252423761920 }, some { target := 435, numerator := 1791132216188179124167114752 }, some { target := 436, numerator := 1873079441765416077560381440 }, some { target := 437, numerator := 70240479066203102908514304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 454, numerator := 2653951073906809131516297216 }, some { target := 455, numerator := 38482290571648732406986309632 }, some { target := 456, numerator := 68118077563608101042251628544 }, some { target := 457, numerator := 2211625894922340942930247680 }, some { target := 458, numerator := 42463217182508946104260755456 }, some { target := 459, numerator := 2211625894922340942930247680 }, some { target := 460, numerator := 67675752384623632853665579008 }, some { target := 461, numerator := 70772028637514910173767925760 }, some { target := 462, numerator := 42463217182508946104260755456 }, some { target := 463, numerator := 1084139013690931530224407412736 }, some { target := 464, numerator := 69445053100561505608009777152 }, some { target := 465, numerator := 38482290571648732406986309632 }, some { target := 466, numerator := 67675752384623632853665579008 }, some { target := 467, numerator := 2211625894922340942930247680 }, some { target := 468, numerator := 69445053100561505608009777152 }, some { target := 469, numerator := 2211625894922340942930247680 }, some { target := 470, numerator := 67675752384623632853665579008 }, some { target := 471, numerator := 70772028637514910173767925760 }, some { target := 472, numerator := 2653951073906809131516297216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 489, numerator := 70240479066203102908514304 }, some { target := 490, numerator := 1018486946459944992173457408 }, some { target := 491, numerator := 1802838962699212974651867136 }, some { target := 492, numerator := 58533732555169252423761920 }, some { target := 493, numerator := 1123847665059249646536228864 }, some { target := 494, numerator := 58533732555169252423761920 }, some { target := 495, numerator := 1791132216188179124167114752 }, some { target := 496, numerator := 1873079441765416077560381440 }, some { target := 497, numerator := 1123847665059249646536228864 }, some { target := 498, numerator := 28693235698543967538128093184 }, some { target := 499, numerator := 1837959202232314526106124288 }, some { target := 500, numerator := 1018486946459944992173457408 }, some { target := 501, numerator := 1791132216188179124167114752 }, some { target := 502, numerator := 58533732555169252423761920 }, some { target := 503, numerator := 1837959202232314526106124288 }, some { target := 504, numerator := 58533732555169252423761920 }, some { target := 505, numerator := 1791132216188179124167114752 }, some { target := 506, numerator := 1873079441765416077560381440 }, some { target := 507, numerator := 70240479066203102908514304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 550, numerator := 814409878902733274263584768 }, some { target := 551, numerator := 11808943244089632476821979136 }, some { target := 552, numerator := 20903186891836820706098675712 }, some { target := 553, numerator := 678674899085611061886320640 }, some { target := 554, numerator := 13030558062443732388217356288 }, some { target := 555, numerator := 678674899085611061886320640 }, some { target := 556, numerator := 20767451912019698493721411584 }, some { target := 557, numerator := 21717596770739553980362260480 }, some { target := 558, numerator := 13030558062443732388217356288 }, some { target := 559, numerator := 332686435531766542536674377728 }, some { target := 560, numerator := 21310391831288187343230468096 }, some { target := 561, numerator := 11808943244089632476821979136 }, some { target := 562, numerator := 20767451912019698493721411584 }, some { target := 563, numerator := 678674899085611061886320640 }, some { target := 564, numerator := 21310391831288187343230468096 }, some { target := 565, numerator := 678674899085611061886320640 }, some { target := 566, numerator := 20767451912019698493721411584 }, some { target := 567, numerator := 21717596770739553980362260480 }, some { target := 568, numerator := 814409878902733274263584768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 585, numerator := 2653951073906809131516297216 }, some { target := 586, numerator := 38482290571648732406986309632 }, some { target := 587, numerator := 68118077563608101042251628544 }, some { target := 588, numerator := 2211625894922340942930247680 }, some { target := 589, numerator := 42463217182508946104260755456 }, some { target := 590, numerator := 2211625894922340942930247680 }, some { target := 591, numerator := 67675752384623632853665579008 }, some { target := 592, numerator := 70772028637514910173767925760 }, some { target := 593, numerator := 42463217182508946104260755456 }, some { target := 594, numerator := 1084139013690931530224407412736 }, some { target := 595, numerator := 69445053100561505608009777152 }, some { target := 596, numerator := 38482290571648732406986309632 }, some { target := 597, numerator := 67675752384623632853665579008 }, some { target := 598, numerator := 2211625894922340942930247680 }, some { target := 599, numerator := 69445053100561505608009777152 }, some { target := 600, numerator := 2211625894922340942930247680 }, some { target := 601, numerator := 67675752384623632853665579008 }, some { target := 602, numerator := 70772028637514910173767925760 }, some { target := 603, numerator := 2653951073906809131516297216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 68342087740089505532608512 }, some { target := 661, numerator := 990960272231297830222823424 }, some { target := 662, numerator := 1754113585328963975336951808 }, some { target := 663, numerator := 56951739783407921277173760 }, some { target := 664, numerator := 1093473403841432088521736192 }, some { target := 665, numerator := 56951739783407921277173760 }, some { target := 666, numerator := 1742723237372282391081517056 }, some { target := 667, numerator := 1822455673069053480869560320 }, some { target := 668, numerator := 1093473403841432088521736192 }, some { target := 669, numerator := 27917742841826563010070577152 }, some { target := 670, numerator := 1788284629199008728103256064 }, some { target := 671, numerator := 990960272231297830222823424 }, some { target := 672, numerator := 1742723237372282391081517056 }, some { target := 673, numerator := 56951739783407921277173760 }, some { target := 674, numerator := 1788284629199008728103256064 }, some { target := 675, numerator := 56951739783407921277173760 }, some { target := 676, numerator := 1742723237372282391081517056 }, some { target := 677, numerator := 1822455673069053480869560320 }, some { target := 678, numerator := 68342087740089505532608512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 766, numerator := 70240479066203102908514304 }, some { target := 767, numerator := 1018486946459944992173457408 }, some { target := 768, numerator := 1802838962699212974651867136 }, some { target := 769, numerator := 58533732555169252423761920 }, some { target := 770, numerator := 1123847665059249646536228864 }, some { target := 771, numerator := 58533732555169252423761920 }, some { target := 772, numerator := 1791132216188179124167114752 }, some { target := 773, numerator := 1873079441765416077560381440 }, some { target := 774, numerator := 1123847665059249646536228864 }, some { target := 775, numerator := 28693235698543967538128093184 }, some { target := 776, numerator := 1837959202232314526106124288 }, some { target := 777, numerator := 1018486946459944992173457408 }, some { target := 778, numerator := 1791132216188179124167114752 }, some { target := 779, numerator := 58533732555169252423761920 }, some { target := 780, numerator := 1837959202232314526106124288 }, some { target := 781, numerator := 58533732555169252423761920 }, some { target := 782, numerator := 1791132216188179124167114752 }, some { target := 783, numerator := 1873079441765416077560381440 }, some { target := 784, numerator := 70240479066203102908514304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 801, numerator := 70240479066203102908514304 }, some { target := 802, numerator := 1018486946459944992173457408 }, some { target := 803, numerator := 1802838962699212974651867136 }, some { target := 804, numerator := 58533732555169252423761920 }, some { target := 805, numerator := 1123847665059249646536228864 }, some { target := 806, numerator := 58533732555169252423761920 }, some { target := 807, numerator := 1791132216188179124167114752 }, some { target := 808, numerator := 1873079441765416077560381440 }, some { target := 809, numerator := 1123847665059249646536228864 }, some { target := 810, numerator := 28693235698543967538128093184 }, some { target := 811, numerator := 1837959202232314526106124288 }, some { target := 812, numerator := 1018486946459944992173457408 }, some { target := 813, numerator := 1791132216188179124167114752 }, some { target := 814, numerator := 58533732555169252423761920 }, some { target := 815, numerator := 1837959202232314526106124288 }, some { target := 816, numerator := 58533732555169252423761920 }, some { target := 817, numerator := 1791132216188179124167114752 }, some { target := 818, numerator := 1873079441765416077560381440 }, some { target := 819, numerator := 70240479066203102908514304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 876, numerator := 77834044370657492412137472 }, some { target := 877, numerator := 1128593643374533639975993344 }, some { target := 878, numerator := 1997740472180208971911528448 }, some { target := 879, numerator := 64861703642214577010114560 }, some { target := 880, numerator := 1245344709930519878594199552 }, some { target := 881, numerator := 64861703642214577010114560 }, some { target := 882, numerator := 1984768131451766056509505536 }, some { target := 883, numerator := 2075574516550866464323665920 }, some { target := 884, numerator := 1245344709930519878594199552 }, some { target := 885, numerator := 31795207125413585650358157312 }, some { target := 886, numerator := 2036657494365537718117597184 }, some { target := 887, numerator := 1128593643374533639975993344 }, some { target := 888, numerator := 1984768131451766056509505536 }, some { target := 889, numerator := 64861703642214577010114560 }, some { target := 890, numerator := 2036657494365537718117597184 }, some { target := 891, numerator := 64861703642214577010114560 }, some { target := 892, numerator := 1984768131451766056509505536 }, some { target := 893, numerator := 2075574516550866464323665920 }, some { target := 894, numerator := 77834044370657492412137472 }]

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

end Slot27

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2
