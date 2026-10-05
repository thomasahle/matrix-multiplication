import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 37; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 9, #[3506605916160, 0, 137230882439168, 0, 0, 137230882439168, 0, 0, 0, 0, 0, 0, 3506605916160, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 8883196367261260915031408640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 6, numerator := 347643534946928258255916367872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 27, numerator := 347643534946928258255916367872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 148, numerator := 8883196367261260915031408640 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 5, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 73103339959466530481111040 }, some { target := 3, numerator := 72890003364254079516672000 }, some { target := 4, numerator := 72392217975425027266314240 }, some { target := 5, numerator := 72890003364254079516672000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 8, numerator := 8640345442699476510745559040 }, some { target := 9, numerator := 8615130426816112279683072000 }, some { target := 10, numerator := 8556295389754929073870602240 }, some { target := 11, numerator := 8615130426816112279683072000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 28, numerator := 81995155913772683566189117440 }, some { target := 29, numerator := 81755870439316148497416192000 }, some { target := 30, numerator := 81197537665584233336946032640 }, some { target := 31, numerator := 81755870439316148497416192000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 149, numerator := 8640351368716010189939015680 }, some { target := 150, numerator := 8615136335538823389773824000 }, some { target := 151, numerator := 8556301258125387522721710080 }, some { target := 152, numerator := 8615136335538823389773824000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 378, numerator := 73103339959466530481111040 }, some { target := 379, numerator := 72890003364254079516672000 }, some { target := 380, numerator := 72392217975425027266314240 }, some { target := 381, numerator := 72890003364254079516672000 }]

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
def data : BetaFourLocalSlotData := ⟨11, 3, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 17, numerator := 21080643979530096233938944 }, some { target := 18, numerator := 516815787885253972186890240 }, some { target := 19, numerator := 382171674725674647853989888 }, some { target := 20, numerator := 426373025005334527054184448 }, some { target := 21, numerator := 21080643979530096233938944 }, some { target := 22, numerator := 425693004231801298143412224 }, some { target := 23, numerator := 433173232740666816161906688 }, some { target := 24, numerator := 21080643979530096233938944 }, some { target := 25, numerator := 516815787885253972186890240 }, some { target := 26, numerator := 21080643979530096233938944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 15810482984647572175454208 }, some { target := 38, numerator := 387611840913940479140167680 }, some { target := 39, numerator := 286628756044255985890492416 }, some { target := 40, numerator := 319779768754000895290638336 }, some { target := 41, numerator := 15810482984647572175454208 }, some { target := 42, numerator := 319269753173850973607559168 }, some { target := 43, numerator := 324879924555500112121430016 }, some { target := 44, numerator := 15810482984647572175454208 }, some { target := 45, numerator := 387611840913940479140167680 }, some { target := 46, numerator := 15810482984647572175454208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 16688843150461326185201664 }, some { target := 52, numerator := 409145832075826061314621440 }, some { target := 53, numerator := 302552575824492429551075328 }, some { target := 54, numerator := 337545311462556500584562688 }, some { target := 55, numerator := 16688843150461326185201664 }, some { target := 56, numerator := 337006961683509361030201344 }, some { target := 57, numerator := 342928809253027896128176128 }, some { target := 58, numerator := 16688843150461326185201664 }, some { target := 59, numerator := 409145832075826061314621440 }, some { target := 60, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 88, numerator := 21519824062436973238812672 }, some { target := 89, numerator := 527582783466196763274117120 }, some { target := 90, numerator := 390133584615792869684281344 }, some { target := 91, numerator := 435255796359612329701146624 }, some { target := 92, numerator := 21519824062436973238812672 }, some { target := 93, numerator := 434561608486630491854733312 }, some { target := 94, numerator := 442197675089430708165279744 }, some { target := 95, numerator := 21519824062436973238812672 }, some { target := 96, numerator := 527582783466196763274117120 }, some { target := 97, numerator := 21519824062436973238812672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 108, numerator := 288102134386911315197165568 }, some { target := 109, numerator := 7063149101098470953220833280 }, some { target := 110, numerator := 5223012887917553520671195136 }, some { target := 111, numerator := 5827098008406238536407187456 }, some { target := 112, numerator := 288102134386911315197165568 }, some { target := 113, numerator := 5817804391167951074626633728 }, some { target := 114, numerator := 5920034180789113154212724736 }, some { target := 115, numerator := 288102134386911315197165568 }, some { target := 116, numerator := 7063149101098470953220833280 }, some { target := 117, numerator := 288102134386911315197165568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 122, numerator := 503739555094187924590166016 }, some { target := 123, numerator := 12349743931341381377049231360 }, some { target := 124, numerator := 9132310643965600439344300032 }, some { target := 125, numerator := 10188538743356639636065615872 }, some { target := 126, numerator := 503739555094187924590166016 }, some { target := 127, numerator := 10172289080289085186885287936 }, some { target := 128, numerator := 10351035374032184127868895232 }, some { target := 129, numerator := 503739555094187924590166016 }, some { target := 130, numerator := 12349743931341381377049231360 }, some { target := 131, numerator := 503739555094187924590166016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 15371302901740695170580480 }, some { target := 154, numerator := 376844845332997688052940800 }, some { target := 155, numerator := 278666846154137764060200960 }, some { target := 156, numerator := 310896997399723092643676160 }, some { target := 157, numerator := 15371302901740695170580480 }, some { target := 158, numerator := 310401148919021779896238080 }, some { target := 159, numerator := 315855482206736220118056960 }, some { target := 160, numerator := 15371302901740695170580480 }, some { target := 161, numerator := 376844845332997688052940800 }, some { target := 162, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 167, numerator := 288102134386911315197165568 }, some { target := 168, numerator := 7063149101098470953220833280 }, some { target := 169, numerator := 5223012887917553520671195136 }, some { target := 170, numerator := 5827098008406238536407187456 }, some { target := 171, numerator := 288102134386911315197165568 }, some { target := 172, numerator := 5817804391167951074626633728 }, some { target := 173, numerator := 5920034180789113154212724736 }, some { target := 174, numerator := 288102134386911315197165568 }, some { target := 175, numerator := 7063149101098470953220833280 }, some { target := 176, numerator := 288102134386911315197165568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 193, numerator := 16249663067554449180327936 }, some { target := 194, numerator := 398378836494883270227394560 }, some { target := 195, numerator := 294590665934374207720783872 }, some { target := 196, numerator := 328662540108278697937600512 }, some { target := 197, numerator := 16249663067554449180327936 }, some { target := 198, numerator := 328138357428680167318880256 }, some { target := 199, numerator := 333904366904264004124803072 }, some { target := 200, numerator := 16249663067554449180327936 }, some { target := 201, numerator := 398378836494883270227394560 }, some { target := 202, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 248, numerator := 16688843150461326185201664 }, some { target := 249, numerator := 409145832075826061314621440 }, some { target := 250, numerator := 302552575824492429551075328 }, some { target := 251, numerator := 337545311462556500584562688 }, some { target := 252, numerator := 16688843150461326185201664 }, some { target := 253, numerator := 337006961683509361030201344 }, some { target := 254, numerator := 342928809253027896128176128 }, some { target := 255, numerator := 16688843150461326185201664 }, some { target := 256, numerator := 409145832075826061314621440 }, some { target := 257, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 262, numerator := 16688843150461326185201664 }, some { target := 263, numerator := 409145832075826061314621440 }, some { target := 264, numerator := 302552575824492429551075328 }, some { target := 265, numerator := 337545311462556500584562688 }, some { target := 266, numerator := 16688843150461326185201664 }, some { target := 267, numerator := 337006961683509361030201344 }, some { target := 268, numerator := 342928809253027896128176128 }, some { target := 269, numerator := 16688843150461326185201664 }, some { target := 270, numerator := 409145832075826061314621440 }, some { target := 271, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 293, numerator := 16249663067554449180327936 }, some { target := 294, numerator := 398378836494883270227394560 }, some { target := 295, numerator := 294590665934374207720783872 }, some { target := 296, numerator := 328662540108278697937600512 }, some { target := 297, numerator := 16249663067554449180327936 }, some { target := 298, numerator := 328138357428680167318880256 }, some { target := 299, numerator := 333904366904264004124803072 }, some { target := 300, numerator := 16249663067554449180327936 }, some { target := 301, numerator := 398378836494883270227394560 }, some { target := 302, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 307, numerator := 503739555094187924590166016 }, some { target := 308, numerator := 12349743931341381377049231360 }, some { target := 309, numerator := 9132310643965600439344300032 }, some { target := 310, numerator := 10188538743356639636065615872 }, some { target := 311, numerator := 503739555094187924590166016 }, some { target := 312, numerator := 10172289080289085186885287936 }, some { target := 313, numerator := 10351035374032184127868895232 }, some { target := 314, numerator := 503739555094187924590166016 }, some { target := 315, numerator := 12349743931341381377049231360 }, some { target := 316, numerator := 503739555094187924590166016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 333, numerator := 16249663067554449180327936 }, some { target := 334, numerator := 398378836494883270227394560 }, some { target := 335, numerator := 294590665934374207720783872 }, some { target := 336, numerator := 328662540108278697937600512 }, some { target := 337, numerator := 16249663067554449180327936 }, some { target := 338, numerator := 328138357428680167318880256 }, some { target := 339, numerator := 333904366904264004124803072 }, some { target := 340, numerator := 16249663067554449180327936 }, some { target := 341, numerator := 398378836494883270227394560 }, some { target := 342, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 21080643979530096233938944 }, some { target := 383, numerator := 516815787885253972186890240 }, some { target := 384, numerator := 382171674725674647853989888 }, some { target := 385, numerator := 426373025005334527054184448 }, some { target := 386, numerator := 21080643979530096233938944 }, some { target := 387, numerator := 425693004231801298143412224 }, some { target := 388, numerator := 433173232740666816161906688 }, some { target := 389, numerator := 21080643979530096233938944 }, some { target := 390, numerator := 516815787885253972186890240 }, some { target := 391, numerator := 21080643979530096233938944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 21519824062436973238812672 }, some { target := 409, numerator := 527582783466196763274117120 }, some { target := 410, numerator := 390133584615792869684281344 }, some { target := 411, numerator := 435255796359612329701146624 }, some { target := 412, numerator := 21519824062436973238812672 }, some { target := 413, numerator := 434561608486630491854733312 }, some { target := 414, numerator := 442197675089430708165279744 }, some { target := 415, numerator := 21519824062436973238812672 }, some { target := 416, numerator := 527582783466196763274117120 }, some { target := 417, numerator := 21519824062436973238812672 }]

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

end Slot11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent3
