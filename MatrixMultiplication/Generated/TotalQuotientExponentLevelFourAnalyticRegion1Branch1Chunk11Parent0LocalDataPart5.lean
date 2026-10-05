import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 1,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 5, #[140737505132544, 0, 140737471578112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 49711035628570085343111413760 }, some { target := 2, numerator := 49565964512922507273043968000 }, some { target := 3, numerator := 49227465243078158442886594560 }, some { target := 4, numerator := 49565964512922507273043968000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 49711023776537017984724500480 }, some { target := 91, numerator := 49565952695477085052862464000 }, some { target := 92, numerator := 49227453506337241545184378880 }, some { target := 93, numerator := 49565952695477085052862464000 }]

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

end Slot21

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 43, #[50290594152448, 0, 0, 180893771628544, 0, 50290610929664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 5, numerator := 4606772438760057708608487424 }, some { target := 6, numerator := 112940227530891737372337111040 }, some { target := 7, numerator := 83516326147843626846386126848 }, some { target := 8, numerator := 93175687712985683332178116608 }, some { target := 9, numerator := 4606772438760057708608487424 }, some { target := 10, numerator := 93027082150445036309319778304 }, some { target := 11, numerator := 94661743338392153560761499648 }, some { target := 12, numerator := 4606772438760057708608487424 }, some { target := 13, numerator := 112940227530891737372337111040 }, some { target := 14, numerator := 4606772438760057708608487424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 16570423466376329979989327872 }, some { target := 95, numerator := 406242639820839057573931909120 }, some { target := 96, numerator := 300405741551725724153354911744 }, some { target := 97, numerator := 335150177852192222498493825024 }, some { target := 98, numerator := 16570423466376329979989327872 }, some { target := 99, numerator := 334615648062954276370107072512 }, some { target := 100, numerator := 340495475744571683782361350144 }, some { target := 101, numerator := 16570423466376329979989327872 }, some { target := 102, numerator := 406242639820839057573931909120 }, some { target := 103, numerator := 16570423466376329979989327872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 4606773975604423349535506432 }, some { target := 217, numerator := 112940265208366507924096286720 }, some { target := 218, numerator := 83516354009344707175450148864 }, some { target := 219, numerator := 93175718796902369037379436544 }, some { target := 220, numerator := 4606773975604423349535506432 }, some { target := 221, numerator := 93027113184786097316426678272 }, some { target := 222, numerator := 94661774918065086246907019264 }, some { target := 223, numerator := 4606773975604423349535506432 }, some { target := 224, numerator := 112940265208366507924096286720 }, some { target := 225, numerator := 4606773975604423349535506432 }]

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

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 278, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 3158740144975855714977185792 }, some { target := 30, numerator := 2352253299450105319663861760 }, some { target := 31, numerator := 2486667773704397052216082432 }, some { target := 32, numerator := 3225947382103001581253296128 }, some { target := 33, numerator := 43214253472754792015538946048 }, some { target := 34, numerator := 78162016778870642479116320768 }, some { target := 35, numerator := 2352253299450105319663861760 }, some { target := 36, numerator := 43214253472754792015538946048 }, some { target := 37, numerator := 2553875010831542918492192768 }, some { target := 38, numerator := 2553875010831542918492192768 }, some { target := 39, numerator := 2486667773704397052216082432 }, some { target := 40, numerator := 2486667773704397052216082432 }, some { target := 41, numerator := 78162016778870642479116320768 }, some { target := 42, numerator := 2486667773704397052216082432 }, some { target := 43, numerator := 3158740144975855714977185792 }, some { target := 44, numerator := 3225947382103001581253296128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 123207872991774481851772567552 }, some { target := 105, numerator := 91750543717278869464085954560 }, some { target := 106, numerator := 96993431929694804862033723392 }, some { target := 107, numerator := 125829317097982449550746451968 }, some { target := 108, numerator := 1685588560291723230440207679488 }, some { target := 109, numerator := 3048739495519866433906627575808 }, some { target := 110, numerator := 91750543717278869464085954560 }, some { target := 111, numerator := 1685588560291723230440207679488 }, some { target := 112, numerator := 99614876035902772561007607808 }, some { target := 113, numerator := 99614876035902772561007607808 }, some { target := 114, numerator := 96993431929694804862033723392 }, some { target := 115, numerator := 96993431929694804862033723392 }, some { target := 116, numerator := 3048739495519866433906627575808 }, some { target := 117, numerator := 96993431929694804862033723392 }, some { target := 118, numerator := 123207872991774481851772567552 }, some { target := 119, numerator := 125829317097982449550746451968 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 123207827799557344272584802304 }, some { target := 227, numerator := 91750510063500149990222725120 }, some { target := 228, numerator := 96993396352843015703949737984 }, some { target := 229, numerator := 125829270944228777129448308736 }, some { target := 230, numerator := 1685587942023731326963234635776 }, some { target := 231, numerator := 3048738377252876412532257980416 }, some { target := 232, numerator := 91750510063500149990222725120 }, some { target := 233, numerator := 1685587942023731326963234635776 }, some { target := 234, numerator := 99614839497514448560813244416 }, some { target := 235, numerator := 99614839497514448560813244416 }, some { target := 236, numerator := 96993396352843015703949737984 }, some { target := 237, numerator := 96993396352843015703949737984 }, some { target := 238, numerator := 3048738377252876412532257980416 }, some { target := 239, numerator := 96993396352843015703949737984 }, some { target := 240, numerator := 123207827799557344272584802304 }, some { target := 241, numerator := 125829270944228777129448308736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 3158755209048234908039774208 }, some { target := 625, numerator := 2352264517376345144284938240 }, some { target := 626, numerator := 2486679632654993438244077568 }, some { target := 627, numerator := 3225962766687559055019343872 }, some { target := 628, numerator := 43214459562085426507863293952 }, some { target := 629, numerator := 78162389534533982937239519232 }, some { target := 630, numerator := 2352264517376345144284938240 }, some { target := 631, numerator := 43214459562085426507863293952 }, some { target := 632, numerator := 2553887190294317585223647232 }, some { target := 633, numerator := 2553887190294317585223647232 }, some { target := 634, numerator := 2486679632654993438244077568 }, some { target := 635, numerator := 2486679632654993438244077568 }, some { target := 636, numerator := 78162389534533982937239519232 }, some { target := 637, numerator := 2486679632654993438244077568 }, some { target := 638, numerator := 3158755209048234908039774208 }, some { target := 639, numerator := 3225962766687559055019343872 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 173, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

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
  [some { target := 71, numerator := 29410898455312150390898688 }, some { target := 72, numerator := 426458027602026180668030976 }, some { target := 73, numerator := 754879727019678526699732992 }, some { target := 74, numerator := 24509082046093458659082240 }, some { target := 75, numerator := 470574375284994406254379008 }, some { target := 76, numerator := 24509082046093458659082240 }, some { target := 77, numerator := 749977910610459834967916544 }, some { target := 78, numerator := 784290625474990677090631680 }, some { target := 79, numerator := 470574375284994406254379008 }, some { target := 80, numerator := 12014352018995013434682114048 }, some { target := 81, numerator := 769585176247334601895182336 }, some { target := 82, numerator := 426458027602026180668030976 }, some { target := 83, numerator := 749977910610459834967916544 }, some { target := 84, numerator := 24509082046093458659082240 }, some { target := 85, numerator := 769585176247334601895182336 }, some { target := 86, numerator := 24509082046093458659082240 }, some { target := 87, numerator := 749977910610459834967916544 }, some { target := 88, numerator := 784290625474990677090631680 }, some { target := 89, numerator := 29410898455312150390898688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 441163476829682255863480320 }, some { target := 147, numerator := 6396870414030392710020464640 }, some { target := 148, numerator := 11323195905295177900495994880 }, some { target := 149, numerator := 367636230691401879886233600 }, some { target := 150, numerator := 7058615629274916093815685120 }, some { target := 151, numerator := 367636230691401879886233600 }, some { target := 152, numerator := 11249668659156897524518748160 }, some { target := 153, numerator := 11764359382124860156359475200 }, some { target := 154, numerator := 7058615629274916093815685120 }, some { target := 155, numerator := 180215280284925201520231710720 }, some { target := 156, numerator := 11543777643710019028427735040 }, some { target := 157, numerator := 6396870414030392710020464640 }, some { target := 158, numerator := 11249668659156897524518748160 }, some { target := 159, numerator := 367636230691401879886233600 }, some { target := 160, numerator := 11543777643710019028427735040 }, some { target := 161, numerator := 367636230691401879886233600 }, some { target := 162, numerator := 11249668659156897524518748160 }, some { target := 163, numerator := 11764359382124860156359475200 }, some { target := 164, numerator := 441163476829682255863480320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 774486992656553293626998784 }, some { target := 182, numerator := 11230061393520022757591482368 }, some { target := 183, numerator := 19878499478184867869759635456 }, some { target := 184, numerator := 645405827213794411355832320 }, some { target := 185, numerator := 12391791882504852698031980544 }, some { target := 186, numerator := 645405827213794411355832320 }, some { target := 187, numerator := 19749418312742108987488468992 }, some { target := 188, numerator := 20652986470841421163386634240 }, some { target := 189, numerator := 12391791882504852698031980544 }, some { target := 190, numerator := 316377936500202020446629003264 }, some { target := 191, numerator := 20265742974513144516573134848 }, some { target := 192, numerator := 11230061393520022757591482368 }, some { target := 193, numerator := 19749418312742108987488468992 }, some { target := 194, numerator := 645405827213794411355832320 }, some { target := 195, numerator := 20265742974513144516573134848 }, some { target := 196, numerator := 645405827213794411355832320 }, some { target := 197, numerator := 19749418312742108987488468992 }, some { target := 198, numerator := 20652986470841421163386634240 }, some { target := 199, numerator := 774486992656553293626998784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 29410898455312150390898688 }, some { target := 243, numerator := 426458027602026180668030976 }, some { target := 244, numerator := 754879727019678526699732992 }, some { target := 245, numerator := 24509082046093458659082240 }, some { target := 246, numerator := 470574375284994406254379008 }, some { target := 247, numerator := 24509082046093458659082240 }, some { target := 248, numerator := 749977910610459834967916544 }, some { target := 249, numerator := 784290625474990677090631680 }, some { target := 250, numerator := 470574375284994406254379008 }, some { target := 251, numerator := 12014352018995013434682114048 }, some { target := 252, numerator := 769585176247334601895182336 }, some { target := 253, numerator := 426458027602026180668030976 }, some { target := 254, numerator := 749977910610459834967916544 }, some { target := 255, numerator := 24509082046093458659082240 }, some { target := 256, numerator := 769585176247334601895182336 }, some { target := 257, numerator := 24509082046093458659082240 }, some { target := 258, numerator := 749977910610459834967916544 }, some { target := 259, numerator := 784290625474990677090631680 }, some { target := 260, numerator := 29410898455312150390898688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 490181640921869173181644800 }, some { target := 278, numerator := 7107633793367103011133849600 }, some { target := 279, numerator := 12581328783661308778328883200 }, some { target := 280, numerator := 408484700768224310984704000 }, some { target := 281, numerator := 7842906254749906770906316800 }, some { target := 282, numerator := 408484700768224310984704000 }, some { target := 283, numerator := 12499631843507663916131942400 }, some { target := 284, numerator := 13071510424583177951510528000 }, some { target := 285, numerator := 7842906254749906770906316800 }, some { target := 286, numerator := 200239200316583557244701900800 }, some { target := 287, numerator := 12826419604122243364919705600 }, some { target := 288, numerator := 7107633793367103011133849600 }, some { target := 289, numerator := 12499631843507663916131942400 }, some { target := 290, numerator := 408484700768224310984704000 }, some { target := 291, numerator := 12826419604122243364919705600 }, some { target := 292, numerator := 408484700768224310984704000 }, some { target := 293, numerator := 12499631843507663916131942400 }, some { target := 294, numerator := 13071510424583177951510528000 }, some { target := 295, numerator := 490181640921869173181644800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 29410898455312150390898688 }, some { target := 313, numerator := 426458027602026180668030976 }, some { target := 314, numerator := 754879727019678526699732992 }, some { target := 315, numerator := 24509082046093458659082240 }, some { target := 316, numerator := 470574375284994406254379008 }, some { target := 317, numerator := 24509082046093458659082240 }, some { target := 318, numerator := 749977910610459834967916544 }, some { target := 319, numerator := 784290625474990677090631680 }, some { target := 320, numerator := 470574375284994406254379008 }, some { target := 321, numerator := 12014352018995013434682114048 }, some { target := 322, numerator := 769585176247334601895182336 }, some { target := 323, numerator := 426458027602026180668030976 }, some { target := 324, numerator := 749977910610459834967916544 }, some { target := 325, numerator := 24509082046093458659082240 }, some { target := 326, numerator := 769585176247334601895182336 }, some { target := 327, numerator := 24509082046093458659082240 }, some { target := 328, numerator := 749977910610459834967916544 }, some { target := 329, numerator := 784290625474990677090631680 }, some { target := 330, numerator := 29410898455312150390898688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 774486992656553293626998784 }, some { target := 414, numerator := 11230061393520022757591482368 }, some { target := 415, numerator := 19878499478184867869759635456 }, some { target := 416, numerator := 645405827213794411355832320 }, some { target := 417, numerator := 12391791882504852698031980544 }, some { target := 418, numerator := 645405827213794411355832320 }, some { target := 419, numerator := 19749418312742108987488468992 }, some { target := 420, numerator := 20652986470841421163386634240 }, some { target := 421, numerator := 12391791882504852698031980544 }, some { target := 422, numerator := 316377936500202020446629003264 }, some { target := 423, numerator := 20265742974513144516573134848 }, some { target := 424, numerator := 11230061393520022757591482368 }, some { target := 425, numerator := 19749418312742108987488468992 }, some { target := 426, numerator := 645405827213794411355832320 }, some { target := 427, numerator := 20265742974513144516573134848 }, some { target := 428, numerator := 645405827213794411355832320 }, some { target := 429, numerator := 19749418312742108987488468992 }, some { target := 430, numerator := 20652986470841421163386634240 }, some { target := 431, numerator := 774486992656553293626998784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 769585176247334601895182336 }, some { target := 449, numerator := 11158985055586351727480143872 }, some { target := 450, numerator := 19752686190348254781976346624 }, some { target := 451, numerator := 641320980206112168245985280 }, some { target := 452, numerator := 12313362819957353630322917376 }, some { target := 453, numerator := 641320980206112168245985280 }, some { target := 454, numerator := 19624421994307032348327149568 }, some { target := 455, numerator := 20522271366595589383871528960 }, some { target := 456, numerator := 12313362819957353630322917376 }, some { target := 457, numerator := 314375544497036184874181984256 }, some { target := 458, numerator := 20137478778471922082923937792 }, some { target := 459, numerator := 11158985055586351727480143872 }, some { target := 460, numerator := 19624421994307032348327149568 }, some { target := 461, numerator := 641320980206112168245985280 }, some { target := 462, numerator := 20137478778471922082923937792 }, some { target := 463, numerator := 641320980206112168245985280 }, some { target := 464, numerator := 19624421994307032348327149568 }, some { target := 465, numerator := 20522271366595589383871528960 }, some { target := 466, numerator := 769585176247334601895182336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 490181640921869173181644800 }, some { target := 510, numerator := 7107633793367103011133849600 }, some { target := 511, numerator := 12581328783661308778328883200 }, some { target := 512, numerator := 408484700768224310984704000 }, some { target := 513, numerator := 7842906254749906770906316800 }, some { target := 514, numerator := 408484700768224310984704000 }, some { target := 515, numerator := 12499631843507663916131942400 }, some { target := 516, numerator := 13071510424583177951510528000 }, some { target := 517, numerator := 7842906254749906770906316800 }, some { target := 518, numerator := 200239200316583557244701900800 }, some { target := 519, numerator := 12826419604122243364919705600 }, some { target := 520, numerator := 7107633793367103011133849600 }, some { target := 521, numerator := 12499631843507663916131942400 }, some { target := 522, numerator := 408484700768224310984704000 }, some { target := 523, numerator := 12826419604122243364919705600 }, some { target := 524, numerator := 408484700768224310984704000 }, some { target := 525, numerator := 12499631843507663916131942400 }, some { target := 526, numerator := 13071510424583177951510528000 }, some { target := 527, numerator := 490181640921869173181644800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 11877101159536890066191253504 }, some { target := 545, numerator := 172217966813284905959773175808 }, some { target := 546, numerator := 304845596428113511698908839936 }, some { target := 547, numerator := 9897584299614075055159377920 }, some { target := 548, numerator := 190033618552590241059060056064 }, some { target := 549, numerator := 9897584299614075055159377920 }, some { target := 550, numerator := 302866079568190696687876964352 }, some { target := 551, numerator := 316722697587650401765100093440 }, some { target := 552, numerator := 190033618552590241059060056064 }, some { target := 553, numerator := 4851795823670819592039127056384 }, some { target := 554, numerator := 310784147007881956732004466688 }, some { target := 555, numerator := 172217966813284905959773175808 }, some { target := 556, numerator := 302866079568190696687876964352 }, some { target := 557, numerator := 9897584299614075055159377920 }, some { target := 558, numerator := 310784147007881956732004466688 }, some { target := 559, numerator := 9897584299614075055159377920 }, some { target := 560, numerator := 302866079568190696687876964352 }, some { target := 561, numerator := 316722697587650401765100093440 }, some { target := 562, numerator := 11877101159536890066191253504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 759781543428897218431549440 }, some { target := 580, numerator := 11016832379719009667257466880 }, some { target := 581, numerator := 19501059614675028606409768960 }, some { target := 582, numerator := 633151286190747682026291200 }, some { target := 583, numerator := 12156504694862355494904791040 }, some { target := 584, numerator := 633151286190747682026291200 }, some { target := 585, numerator := 19374429357436879070004510720 }, some { target := 586, numerator := 20260841158103925824841318400 }, some { target := 587, numerator := 12156504694862355494904791040 }, some { target := 588, numerator := 310370760490704513729287946240 }, some { target := 589, numerator := 19880950386389477215625543680 }, some { target := 590, numerator := 11016832379719009667257466880 }, some { target := 591, numerator := 19374429357436879070004510720 }, some { target := 592, numerator := 633151286190747682026291200 }, some { target := 593, numerator := 19880950386389477215625543680 }, some { target := 594, numerator := 633151286190747682026291200 }, some { target := 595, numerator := 19374429357436879070004510720 }, some { target := 596, numerator := 20260841158103925824841318400 }, some { target := 597, numerator := 759781543428897218431549440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 441163476829682255863480320 }, some { target := 641, numerator := 6396870414030392710020464640 }, some { target := 642, numerator := 11323195905295177900495994880 }, some { target := 643, numerator := 367636230691401879886233600 }, some { target := 644, numerator := 7058615629274916093815685120 }, some { target := 645, numerator := 367636230691401879886233600 }, some { target := 646, numerator := 11249668659156897524518748160 }, some { target := 647, numerator := 11764359382124860156359475200 }, some { target := 648, numerator := 7058615629274916093815685120 }, some { target := 649, numerator := 180215280284925201520231710720 }, some { target := 650, numerator := 11543777643710019028427735040 }, some { target := 651, numerator := 6396870414030392710020464640 }, some { target := 652, numerator := 11249668659156897524518748160 }, some { target := 653, numerator := 367636230691401879886233600 }, some { target := 654, numerator := 11543777643710019028427735040 }, some { target := 655, numerator := 367636230691401879886233600 }, some { target := 656, numerator := 11249668659156897524518748160 }, some { target := 657, numerator := 11764359382124860156359475200 }, some { target := 658, numerator := 441163476829682255863480320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 774486992656553293626998784 }, some { target := 676, numerator := 11230061393520022757591482368 }, some { target := 677, numerator := 19878499478184867869759635456 }, some { target := 678, numerator := 645405827213794411355832320 }, some { target := 679, numerator := 12391791882504852698031980544 }, some { target := 680, numerator := 645405827213794411355832320 }, some { target := 681, numerator := 19749418312742108987488468992 }, some { target := 682, numerator := 20652986470841421163386634240 }, some { target := 683, numerator := 12391791882504852698031980544 }, some { target := 684, numerator := 316377936500202020446629003264 }, some { target := 685, numerator := 20265742974513144516573134848 }, some { target := 686, numerator := 11230061393520022757591482368 }, some { target := 687, numerator := 19749418312742108987488468992 }, some { target := 688, numerator := 645405827213794411355832320 }, some { target := 689, numerator := 20265742974513144516573134848 }, some { target := 690, numerator := 645405827213794411355832320 }, some { target := 691, numerator := 19749418312742108987488468992 }, some { target := 692, numerator := 20652986470841421163386634240 }, some { target := 693, numerator := 774486992656553293626998784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 29410898455312150390898688 }, some { target := 777, numerator := 426458027602026180668030976 }, some { target := 778, numerator := 754879727019678526699732992 }, some { target := 779, numerator := 24509082046093458659082240 }, some { target := 780, numerator := 470574375284994406254379008 }, some { target := 781, numerator := 24509082046093458659082240 }, some { target := 782, numerator := 749977910610459834967916544 }, some { target := 783, numerator := 784290625474990677090631680 }, some { target := 784, numerator := 470574375284994406254379008 }, some { target := 785, numerator := 12014352018995013434682114048 }, some { target := 786, numerator := 769585176247334601895182336 }, some { target := 787, numerator := 426458027602026180668030976 }, some { target := 788, numerator := 749977910610459834967916544 }, some { target := 789, numerator := 24509082046093458659082240 }, some { target := 790, numerator := 769585176247334601895182336 }, some { target := 791, numerator := 24509082046093458659082240 }, some { target := 792, numerator := 749977910610459834967916544 }, some { target := 793, numerator := 784290625474990677090631680 }, some { target := 794, numerator := 29410898455312150390898688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 759781543428897218431549440 }, some { target := 812, numerator := 11016832379719009667257466880 }, some { target := 813, numerator := 19501059614675028606409768960 }, some { target := 814, numerator := 633151286190747682026291200 }, some { target := 815, numerator := 12156504694862355494904791040 }, some { target := 816, numerator := 633151286190747682026291200 }, some { target := 817, numerator := 19374429357436879070004510720 }, some { target := 818, numerator := 20260841158103925824841318400 }, some { target := 819, numerator := 12156504694862355494904791040 }, some { target := 820, numerator := 310370760490704513729287946240 }, some { target := 821, numerator := 19880950386389477215625543680 }, some { target := 822, numerator := 11016832379719009667257466880 }, some { target := 823, numerator := 19374429357436879070004510720 }, some { target := 824, numerator := 633151286190747682026291200 }, some { target := 825, numerator := 19880950386389477215625543680 }, some { target := 826, numerator := 633151286190747682026291200 }, some { target := 827, numerator := 19374429357436879070004510720 }, some { target := 828, numerator := 20260841158103925824841318400 }, some { target := 829, numerator := 759781543428897218431549440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 29410898455312150390898688 }, some { target := 847, numerator := 426458027602026180668030976 }, some { target := 848, numerator := 754879727019678526699732992 }, some { target := 849, numerator := 24509082046093458659082240 }, some { target := 850, numerator := 470574375284994406254379008 }, some { target := 851, numerator := 24509082046093458659082240 }, some { target := 852, numerator := 749977910610459834967916544 }, some { target := 853, numerator := 784290625474990677090631680 }, some { target := 854, numerator := 470574375284994406254379008 }, some { target := 855, numerator := 12014352018995013434682114048 }, some { target := 856, numerator := 769585176247334601895182336 }, some { target := 857, numerator := 426458027602026180668030976 }, some { target := 858, numerator := 749977910610459834967916544 }, some { target := 859, numerator := 24509082046093458659082240 }, some { target := 860, numerator := 769585176247334601895182336 }, some { target := 861, numerator := 24509082046093458659082240 }, some { target := 862, numerator := 749977910610459834967916544 }, some { target := 863, numerator := 784290625474990677090631680 }, some { target := 864, numerator := 29410898455312150390898688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 774486992656553293626998784 }, some { target := 908, numerator := 11230061393520022757591482368 }, some { target := 909, numerator := 19878499478184867869759635456 }, some { target := 910, numerator := 645405827213794411355832320 }, some { target := 911, numerator := 12391791882504852698031980544 }, some { target := 912, numerator := 645405827213794411355832320 }, some { target := 913, numerator := 19749418312742108987488468992 }, some { target := 914, numerator := 20652986470841421163386634240 }, some { target := 915, numerator := 12391791882504852698031980544 }, some { target := 916, numerator := 316377936500202020446629003264 }, some { target := 917, numerator := 20265742974513144516573134848 }, some { target := 918, numerator := 11230061393520022757591482368 }, some { target := 919, numerator := 19749418312742108987488468992 }, some { target := 920, numerator := 645405827213794411355832320 }, some { target := 921, numerator := 20265742974513144516573134848 }, some { target := 922, numerator := 645405827213794411355832320 }, some { target := 923, numerator := 19749418312742108987488468992 }, some { target := 924, numerator := 20652986470841421163386634240 }, some { target := 925, numerator := 774486992656553293626998784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 774486992656553293626998784 }, some { target := 943, numerator := 11230061393520022757591482368 }, some { target := 944, numerator := 19878499478184867869759635456 }, some { target := 945, numerator := 645405827213794411355832320 }, some { target := 946, numerator := 12391791882504852698031980544 }, some { target := 947, numerator := 645405827213794411355832320 }, some { target := 948, numerator := 19749418312742108987488468992 }, some { target := 949, numerator := 20652986470841421163386634240 }, some { target := 950, numerator := 12391791882504852698031980544 }, some { target := 951, numerator := 316377936500202020446629003264 }, some { target := 952, numerator := 20265742974513144516573134848 }, some { target := 953, numerator := 11230061393520022757591482368 }, some { target := 954, numerator := 19749418312742108987488468992 }, some { target := 955, numerator := 645405827213794411355832320 }, some { target := 956, numerator := 20265742974513144516573134848 }, some { target := 957, numerator := 645405827213794411355832320 }, some { target := 958, numerator := 19749418312742108987488468992 }, some { target := 959, numerator := 20652986470841421163386634240 }, some { target := 960, numerator := 774486992656553293626998784 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 29410898455312150390898688 }, some { target := 1018, numerator := 426458027602026180668030976 }, some { target := 1019, numerator := 754879727019678526699732992 }, some { target := 1020, numerator := 24509082046093458659082240 }, some { target := 1021, numerator := 470574375284994406254379008 }, some { target := 1022, numerator := 24509082046093458659082240 }, some { target := 1023, numerator := 749977910610459834967916544 }, some { target := 1024, numerator := 784290625474990677090631680 }, some { target := 1025, numerator := 470574375284994406254379008 }, some { target := 1026, numerator := 12014352018995013434682114048 }, some { target := 1027, numerator := 769585176247334601895182336 }, some { target := 1028, numerator := 426458027602026180668030976 }, some { target := 1029, numerator := 749977910610459834967916544 }, some { target := 1030, numerator := 24509082046093458659082240 }, some { target := 1031, numerator := 769585176247334601895182336 }, some { target := 1032, numerator := 24509082046093458659082240 }, some { target := 1033, numerator := 749977910610459834967916544 }, some { target := 1034, numerator := 784290625474990677090631680 }, some { target := 1035, numerator := 29410898455312150390898688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot24

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
