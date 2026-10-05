import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 1, #[140737438023680, 0, 140737538686976, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 1, numerator := 9942202384900790125267517440 }, some { target := 2, numerator := 9913188175606332566536192000 }, some { target := 3, numerator := 9845488353919264929496432640 }, some { target := 4, numerator := 9913188175606332566536192000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 9942209496120630540299665408 }, some { target := 91, numerator := 9913195266073585898645094400 }, some { target := 92, numerator := 9845495395963815068117762048 }, some { target := 93, numerator := 9913195266073585898645094400 }]

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
def data : BetaFourLocalSlotData := ⟨16, 41, #[50401223114752, 0, 0, 180657883971584, 0, 50415869624320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 5, numerator := 4402166558390484958982438912 }, some { target := 6, numerator := 107924083366992534478279147520 }, some { target := 7, numerator := 79807019542433953127359053824 }, some { target := 8, numerator := 89037368777768840944580296704 }, some { target := 9, numerator := 4402166558390484958982438912 }, some { target := 10, numerator := 88895363404917534978161508352 }, some { target := 11, numerator := 90457422506281900608768180224 }, some { target := 12, numerator := 4402166558390484958982438912 }, some { target := 13, numerator := 107924083366992534478279147520 }, some { target := 14, numerator := 4402166558390484958982438912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 15779103088800282799771746304 }, some { target := 95, numerator := 386842527338329513800855715840 }, some { target := 96, numerator := 286059868900185772047474884608 }, some { target := 97, numerator := 319145085054121848885705965568 }, some { target := 98, numerator := 15779103088800282799771746304 }, some { target := 99, numerator := 318636081728676678472810102784 }, some { target := 100, numerator := 324235118308573553014664593408 }, some { target := 101, numerator := 15779103088800282799771746304 }, some { target := 102, numerator := 386842527338329513800855715840 }, some { target := 103, numerator := 15779103088800282799771746304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 4403445820492331138070609920 }, some { target := 217, numerator := 107955445921747473062376243200 }, some { target := 218, numerator := 79830211326344841922441379840 }, some { target := 219, numerator := 89063242885441665276460400640 }, some { target := 220, numerator := 4403445820492331138070609920 }, some { target := 221, numerator := 88921196246070944917167800320 }, some { target := 222, numerator := 90483709279148868869386403840 }, some { target := 223, numerator := 4403445820492331138070609920 }, some { target := 224, numerator := 107955445921747473062376243200 }, some { target := 225, numerator := 4403445820492331138070609920 }]

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
def data : BetaFourLocalSlotData := ⟨17, 602, #[3506505252864, 0, 137230932770816, 0, 0, 137230983102464, 0, 0, 0, 0, 0, 0, 3506555584512, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 6817869542775546207352651776 }, some { target := 30, numerator := 5077136893556257813986017280 }, some { target := 31, numerator := 5367259001759472546213789696 }, some { target := 32, numerator := 6962930596877153573466537984 }, some { target := 33, numerator := 93274257787333536411228831744 }, some { target := 34, numerator := 168706005920169366790449659904 }, some { target := 35, numerator := 5077136893556257813986017280 }, some { target := 36, numerator := 93274257787333536411228831744 }, some { target := 37, numerator := 5512320055861079912327675904 }, some { target := 38, numerator := 5512320055861079912327675904 }, some { target := 39, numerator := 5367259001759472546213789696 }, some { target := 40, numerator := 5367259001759472546213789696 }, some { target := 41, numerator := 168706005920169366790449659904 }, some { target := 42, numerator := 5367259001759472546213789696 }, some { target := 43, numerator := 6817869542775546207352651776 }, some { target := 44, numerator := 6962930596877153573466537984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 266824809716351842707354681344 }, some { target := 105, numerator := 198699326384517329675689656320 }, some { target := 106, numerator := 210053573606489748514300493824 }, some { target := 107, numerator := 272501933327338052126660100096 }, some { target := 108, numerator := 3650390481864132656613384257536 }, some { target := 109, numerator := 6602494759576961554652202008576 }, some { target := 110, numerator := 198699326384517329675689656320 }, some { target := 111, numerator := 3650390481864132656613384257536 }, some { target := 112, numerator := 215730697217475957933605912576 }, some { target := 113, numerator := 215730697217475957933605912576 }, some { target := 114, numerator := 210053573606489748514300493824 }, some { target := 115, numerator := 210053573606489748514300493824 }, some { target := 116, numerator := 6602494759576961554652202008576 }, some { target := 117, numerator := 210053573606489748514300493824 }, some { target := 118, numerator := 266824809716351842707354681344 }, some { target := 119, numerator := 272501933327338052126660100096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 266824907578634996745739698176 }, some { target := 227, numerator := 198699399260685635874487009280 }, some { target := 228, numerator := 210053650647010529353029124096 }, some { target := 229, numerator := 272502033271797443485010755584 }, some { target := 230, numerator := 3650391820703453253351289913344 }, some { target := 231, numerator := 6602497181147925557772239765504 }, some { target := 232, numerator := 198699399260685635874487009280 }, some { target := 233, numerator := 3650391820703453253351289913344 }, some { target := 234, numerator := 215730776340172976092300181504 }, some { target := 235, numerator := 215730776340172976092300181504 }, some { target := 236, numerator := 210053650647010529353029124096 }, some { target := 237, numerator := 210053650647010529353029124096 }, some { target := 238, numerator := 6602497181147925557772239765504 }, some { target := 239, numerator := 210053650647010529353029124096 }, some { target := 240, numerator := 266824907578634996745739698176 }, some { target := 241, numerator := 272502033271797443485010755584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 6817967405058700245737668608 }, some { target := 625, numerator := 5077209769724564012783370240 }, some { target := 626, numerator := 5367336042280253384942419968 }, some { target := 627, numerator := 6963030541336544931817193472 }, some { target := 628, numerator := 93275596626654133149134487552 }, some { target := 629, numerator := 168708427491133369910487416832 }, some { target := 630, numerator := 5077209769724564012783370240 }, some { target := 631, numerator := 93275596626654133149134487552 }, some { target := 632, numerator := 5512399178558098071021944832 }, some { target := 633, numerator := 5512399178558098071021944832 }, some { target := 634, numerator := 5367336042280253384942419968 }, some { target := 635, numerator := 5367336042280253384942419968 }, some { target := 636, numerator := 168708427491133369910487416832 }, some { target := 637, numerator := 5367336042280253384942419968 }, some { target := 638, numerator := 6817967405058700245737668608 }, some { target := 639, numerator := 6963030541336544931817193472 }]

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
def data : BetaFourLocalSlotData := ⟨18, 1064, #[69122129920, 22265714442240, 0, 236805236457472, 0, 0, 0, 0, 0, 0, 0, 22265781551104, 0, 0, 0, 0, 0, 0, 69122129920], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 71, numerator := 30324233647889657710510080 }, some { target := 72, numerator := 439701387894400036802396160 }, some { target := 73, numerator := 778321996962501214569758720 }, some { target := 74, numerator := 25270194706574714758758400 }, some { target := 75, numerator := 485187738366234523368161280 }, some { target := 76, numerator := 25270194706574714758758400 }, some { target := 77, numerator := 773267958021186271618007040 }, some { target := 78, numerator := 808646230610390872280268800 }, some { target := 79, numerator := 485187738366234523368161280 }, some { target := 80, numerator := 12387449445162925174743367680 }, some { target := 81, numerator := 793484113786446043425013760 }, some { target := 82, numerator := 439701387894400036802396160 }, some { target := 83, numerator := 773267958021186271618007040 }, some { target := 84, numerator := 25270194706574714758758400 }, some { target := 85, numerator := 793484113786446043425013760 }, some { target := 86, numerator := 25270194706574714758758400 }, some { target := 87, numerator := 773267958021186271618007040 }, some { target := 88, numerator := 808646230610390872280268800 }, some { target := 89, numerator := 30324233647889657710510080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 9768083360063174838331637760 }, some { target := 147, numerator := 141637208720916035155808747520 }, some { target := 148, numerator := 250714139574954820850512035840 }, some { target := 149, numerator := 8140069466719312365276364800 }, some { target := 150, numerator := 156289333761010797413306204160 }, some { target := 151, numerator := 8140069466719312365276364800 }, some { target := 152, numerator := 249086125681610958377456762880 }, some { target := 153, numerator := 260482222935017995688843673600 }, some { target := 154, numerator := 156289333761010797413306204160 }, some { target := 155, numerator := 3990262052585806921458474024960 }, some { target := 156, numerator := 255598181254986408269677854720 }, some { target := 157, numerator := 141637208720916035155808747520 }, some { target := 158, numerator := 249086125681610958377456762880 }, some { target := 159, numerator := 8140069466719312365276364800 }, some { target := 160, numerator := 255598181254986408269677854720 }, some { target := 161, numerator := 8140069466719312365276364800 }, some { target := 162, numerator := 249086125681610958377456762880 }, some { target := 163, numerator := 260482222935017995688843673600 }, some { target := 164, numerator := 9768083360063174838331637760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 103887674290291011788658966528 }, some { target := 243, numerator := 1506371277209219670935555014656 }, some { target := 244, numerator := 2666450306784135969242246807552 }, some { target := 245, numerator := 86573061908575843157215805440 }, some { target := 246, numerator := 1662202788644656188618543464448 }, some { target := 247, numerator := 86573061908575843157215805440 }, some { target := 248, numerator := 2649135694402420800610803646464 }, some { target := 249, numerator := 2770337981074426981030905774080 }, some { target := 250, numerator := 1662202788644656188618543464448 }, some { target := 251, numerator := 42438114947583878315667187826688 }, some { target := 252, numerator := 2718394143929281475136576290816 }, some { target := 253, numerator := 1506371277209219670935555014656 }, some { target := 254, numerator := 2649135694402420800610803646464 }, some { target := 255, numerator := 86573061908575843157215805440 }, some { target := 256, numerator := 2718394143929281475136576290816 }, some { target := 257, numerator := 86573061908575843157215805440 }, some { target := 258, numerator := 2649135694402420800610803646464 }, some { target := 259, numerator := 2770337981074426981030905774080 }, some { target := 260, numerator := 103887674290291011788658966528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 9768112801066716478776016896 }, some { target := 641, numerator := 141637635615467388942252244992 }, some { target := 642, numerator := 250714895227379056288584433664 }, some { target := 643, numerator := 8140094000888930398980014080 }, some { target := 644, numerator := 156289804817067463660416270336 }, some { target := 645, numerator := 8140094000888930398980014080 }, some { target := 646, numerator := 249086876427201270208788430848 }, some { target := 647, numerator := 260483008028445772767360450560 }, some { target := 648, numerator := 156289804817067463660416270336 }, some { target := 649, numerator := 3990274079235753681580002902016 }, some { target := 650, numerator := 255598951627912414527972442112 }, some { target := 651, numerator := 141637635615467388942252244992 }, some { target := 652, numerator := 249086876427201270208788430848 }, some { target := 653, numerator := 8140094000888930398980014080 }, some { target := 654, numerator := 255598951627912414527972442112 }, some { target := 655, numerator := 8140094000888930398980014080 }, some { target := 656, numerator := 249086876427201270208788430848 }, some { target := 657, numerator := 260483008028445772767360450560 }, some { target := 658, numerator := 9768112801066716478776016896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 30324233647889657710510080 }, some { target := 1018, numerator := 439701387894400036802396160 }, some { target := 1019, numerator := 778321996962501214569758720 }, some { target := 1020, numerator := 25270194706574714758758400 }, some { target := 1021, numerator := 485187738366234523368161280 }, some { target := 1022, numerator := 25270194706574714758758400 }, some { target := 1023, numerator := 773267958021186271618007040 }, some { target := 1024, numerator := 808646230610390872280268800 }, some { target := 1025, numerator := 485187738366234523368161280 }, some { target := 1026, numerator := 12387449445162925174743367680 }, some { target := 1027, numerator := 793484113786446043425013760 }, some { target := 1028, numerator := 439701387894400036802396160 }, some { target := 1029, numerator := 773267958021186271618007040 }, some { target := 1030, numerator := 25270194706574714758758400 }, some { target := 1031, numerator := 793484113786446043425013760 }, some { target := 1032, numerator := 25270194706574714758758400 }, some { target := 1033, numerator := 773267958021186271618007040 }, some { target := 1034, numerator := 808646230610390872280268800 }, some { target := 1035, numerator := 30324233647889657710510080 }]

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
def data : BetaFourLocalSlotData := ⟨19, 52, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 88385134647275568479862784 }, some { target := 201, numerator := 99789668150149835380490240 }, some { target := 202, numerator := 85534001271557001754705920 }, some { target := 203, numerator := 1126197683408833856436961280 }, some { target := 204, numerator := 99789668150149835380490240 }, some { target := 205, numerator := 85534001271557001754705920 }, some { target := 206, numerator := 99789668150149835380490240 }, some { target := 207, numerator := 99789668150149835380490240 }, some { target := 208, numerator := 4136994528167640318202609664 }, some { target := 209, numerator := 102640801525868402105647104 }, some { target := 210, numerator := 1126197683408833856436961280 }, some { target := 211, numerator := 4136994528167640318202609664 }, some { target := 212, numerator := 88385134647275568479862784 }, some { target := 213, numerator := 99789668150149835380490240 }, some { target := 214, numerator := 102640801525868402105647104 }, some { target := 215, numerator := 99789668150149835380490240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 15501922235102982268530982912 }, some { target := 297, numerator := 17502170265438850948341432320 }, some { target := 298, numerator := 15001860227519015098578370560 }, some { target := 299, numerator := 197524492995667032131281879040 }, some { target := 300, numerator := 17502170265438850948341432320 }, some { target := 301, numerator := 15001860227519015098578370560 }, some { target := 302, numerator := 17502170265438850948341432320 }, some { target := 303, numerator := 17502170265438850948341432320 }, some { target := 304, numerator := 725589973004336363601240522752 }, some { target := 305, numerator := 18002232273022818118294044672 }, some { target := 306, numerator := 197524492995667032131281879040 }, some { target := 307, numerator := 725589973004336363601240522752 }, some { target := 308, numerator := 15501922235102982268530982912 }, some { target := 309, numerator := 17502170265438850948341432320 }, some { target := 310, numerator := 18002232273022818118294044672 }, some { target := 311, numerator := 17502170265438850948341432320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 15501924093612447694768308224 }, some { target := 660, numerator := 17502172363755989332802928640 }, some { target := 661, numerator := 15001862026076562285259653120 }, some { target := 662, numerator := 197524516676674736755918766080 }, some { target := 663, numerator := 17502172363755989332802928640 }, some { target := 664, numerator := 15001862026076562285259653120 }, some { target := 665, numerator := 17502172363755989332802928640 }, some { target := 666, numerator := 17502172363755989332802928640 }, some { target := 667, numerator := 725590059994569729197058555904 }, some { target := 668, numerator := 18002234431291874742311583744 }, some { target := 669, numerator := 197524516676674736755918766080 }, some { target := 670, numerator := 725590059994569729197058555904 }, some { target := 671, numerator := 15501924093612447694768308224 }, some { target := 672, numerator := 17502172363755989332802928640 }, some { target := 673, numerator := 18002234431291874742311583744 }, some { target := 674, numerator := 17502172363755989332802928640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 88383276137810142242537472 }, some { target := 1037, numerator := 99787569833011450918993920 }, some { target := 1038, numerator := 85532202714009815073423360 }, some { target := 1039, numerator := 1126174002401129231800074240 }, some { target := 1040, numerator := 99787569833011450918993920 }, some { target := 1041, numerator := 85532202714009815073423360 }, some { target := 1042, numerator := 99787569833011450918993920 }, some { target := 1043, numerator := 99787569833011450918993920 }, some { target := 1044, numerator := 4136907537934274722384576512 }, some { target := 1045, numerator := 102638643256811778088108032 }, some { target := 1046, numerator := 1126174002401129231800074240 }, some { target := 1047, numerator := 4136907537934274722384576512 }, some { target := 1048, numerator := 88383276137810142242537472 }, some { target := 1049, numerator := 99787569833011450918993920 }, some { target := 1050, numerator := 102638643256811778088108032 }, some { target := 1051, numerator := 99787569833011450918993920 }]

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
def data : BetaFourLocalSlotData := ⟨20, 0, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent3
