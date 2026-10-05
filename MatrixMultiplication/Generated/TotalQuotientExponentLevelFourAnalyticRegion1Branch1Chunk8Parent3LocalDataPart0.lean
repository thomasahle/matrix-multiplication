import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 37; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 21080643979530096233938944 }, some { target := 62, numerator := 15810482984647572175454208 }, some { target := 63, numerator := 16688843150461326185201664 }, some { target := 64, numerator := 21519824062436973238812672 }, some { target := 65, numerator := 288102134386911315197165568 }, some { target := 66, numerator := 503739555094187924590166016 }, some { target := 67, numerator := 15371302901740695170580480 }, some { target := 68, numerator := 288102134386911315197165568 }, some { target := 69, numerator := 16249663067554449180327936 }, some { target := 70, numerator := 16688843150461326185201664 }, some { target := 71, numerator := 16688843150461326185201664 }, some { target := 72, numerator := 16249663067554449180327936 }, some { target := 73, numerator := 503739555094187924590166016 }, some { target := 74, numerator := 16249663067554449180327936 }, some { target := 75, numerator := 21080643979530096233938944 }, some { target := 76, numerator := 21519824062436973238812672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 132, numerator := 516815787885253972186890240 }, some { target := 133, numerator := 387611840913940479140167680 }, some { target := 134, numerator := 409145832075826061314621440 }, some { target := 135, numerator := 527582783466196763274117120 }, some { target := 136, numerator := 7063149101098470953220833280 }, some { target := 137, numerator := 12349743931341381377049231360 }, some { target := 138, numerator := 376844845332997688052940800 }, some { target := 139, numerator := 7063149101098470953220833280 }, some { target := 140, numerator := 398378836494883270227394560 }, some { target := 141, numerator := 409145832075826061314621440 }, some { target := 142, numerator := 409145832075826061314621440 }, some { target := 143, numerator := 398378836494883270227394560 }, some { target := 144, numerator := 12349743931341381377049231360 }, some { target := 145, numerator := 398378836494883270227394560 }, some { target := 146, numerator := 516815787885253972186890240 }, some { target := 147, numerator := 527582783466196763274117120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 382171674725674647853989888 }, some { target := 178, numerator := 286628756044255985890492416 }, some { target := 179, numerator := 302552575824492429551075328 }, some { target := 180, numerator := 390133584615792869684281344 }, some { target := 181, numerator := 5223012887917553520671195136 }, some { target := 182, numerator := 9132310643965600439344300032 }, some { target := 183, numerator := 278666846154137764060200960 }, some { target := 184, numerator := 5223012887917553520671195136 }, some { target := 185, numerator := 294590665934374207720783872 }, some { target := 186, numerator := 302552575824492429551075328 }, some { target := 187, numerator := 302552575824492429551075328 }, some { target := 188, numerator := 294590665934374207720783872 }, some { target := 189, numerator := 9132310643965600439344300032 }, some { target := 190, numerator := 294590665934374207720783872 }, some { target := 191, numerator := 382171674725674647853989888 }, some { target := 192, numerator := 390133584615792869684281344 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 203, numerator := 426373025005334527054184448 }, some { target := 204, numerator := 319779768754000895290638336 }, some { target := 205, numerator := 337545311462556500584562688 }, some { target := 206, numerator := 435255796359612329701146624 }, some { target := 207, numerator := 5827098008406238536407187456 }, some { target := 208, numerator := 10188538743356639636065615872 }, some { target := 209, numerator := 310896997399723092643676160 }, some { target := 210, numerator := 5827098008406238536407187456 }, some { target := 211, numerator := 328662540108278697937600512 }, some { target := 212, numerator := 337545311462556500584562688 }, some { target := 213, numerator := 337545311462556500584562688 }, some { target := 214, numerator := 328662540108278697937600512 }, some { target := 215, numerator := 10188538743356639636065615872 }, some { target := 216, numerator := 328662540108278697937600512 }, some { target := 217, numerator := 426373025005334527054184448 }, some { target := 218, numerator := 435255796359612329701146624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 272, numerator := 21080643979530096233938944 }, some { target := 273, numerator := 15810482984647572175454208 }, some { target := 274, numerator := 16688843150461326185201664 }, some { target := 275, numerator := 21519824062436973238812672 }, some { target := 276, numerator := 288102134386911315197165568 }, some { target := 277, numerator := 503739555094187924590166016 }, some { target := 278, numerator := 15371302901740695170580480 }, some { target := 279, numerator := 288102134386911315197165568 }, some { target := 280, numerator := 16249663067554449180327936 }, some { target := 281, numerator := 16688843150461326185201664 }, some { target := 282, numerator := 16688843150461326185201664 }, some { target := 283, numerator := 16249663067554449180327936 }, some { target := 284, numerator := 503739555094187924590166016 }, some { target := 285, numerator := 16249663067554449180327936 }, some { target := 286, numerator := 21080643979530096233938944 }, some { target := 287, numerator := 21519824062436973238812672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 317, numerator := 425693004231801298143412224 }, some { target := 318, numerator := 319269753173850973607559168 }, some { target := 319, numerator := 337006961683509361030201344 }, some { target := 320, numerator := 434561608486630491854733312 }, some { target := 321, numerator := 5817804391167951074626633728 }, some { target := 322, numerator := 10172289080289085186885287936 }, some { target := 323, numerator := 310401148919021779896238080 }, some { target := 324, numerator := 5817804391167951074626633728 }, some { target := 325, numerator := 328138357428680167318880256 }, some { target := 326, numerator := 337006961683509361030201344 }, some { target := 327, numerator := 337006961683509361030201344 }, some { target := 328, numerator := 328138357428680167318880256 }, some { target := 329, numerator := 10172289080289085186885287936 }, some { target := 330, numerator := 328138357428680167318880256 }, some { target := 331, numerator := 425693004231801298143412224 }, some { target := 332, numerator := 434561608486630491854733312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 343, numerator := 433173232740666816161906688 }, some { target := 344, numerator := 324879924555500112121430016 }, some { target := 345, numerator := 342928809253027896128176128 }, some { target := 346, numerator := 442197675089430708165279744 }, some { target := 347, numerator := 5920034180789113154212724736 }, some { target := 348, numerator := 10351035374032184127868895232 }, some { target := 349, numerator := 315855482206736220118056960 }, some { target := 350, numerator := 5920034180789113154212724736 }, some { target := 351, numerator := 333904366904264004124803072 }, some { target := 352, numerator := 342928809253027896128176128 }, some { target := 353, numerator := 342928809253027896128176128 }, some { target := 354, numerator := 333904366904264004124803072 }, some { target := 355, numerator := 10351035374032184127868895232 }, some { target := 356, numerator := 333904366904264004124803072 }, some { target := 357, numerator := 433173232740666816161906688 }, some { target := 358, numerator := 442197675089430708165279744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 21080643979530096233938944 }, some { target := 393, numerator := 15810482984647572175454208 }, some { target := 394, numerator := 16688843150461326185201664 }, some { target := 395, numerator := 21519824062436973238812672 }, some { target := 396, numerator := 288102134386911315197165568 }, some { target := 397, numerator := 503739555094187924590166016 }, some { target := 398, numerator := 15371302901740695170580480 }, some { target := 399, numerator := 288102134386911315197165568 }, some { target := 400, numerator := 16249663067554449180327936 }, some { target := 401, numerator := 16688843150461326185201664 }, some { target := 402, numerator := 16688843150461326185201664 }, some { target := 403, numerator := 16249663067554449180327936 }, some { target := 404, numerator := 503739555094187924590166016 }, some { target := 405, numerator := 16249663067554449180327936 }, some { target := 406, numerator := 21080643979530096233938944 }, some { target := 407, numerator := 21519824062436973238812672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 418, numerator := 516815787885253972186890240 }, some { target := 419, numerator := 387611840913940479140167680 }, some { target := 420, numerator := 409145832075826061314621440 }, some { target := 421, numerator := 527582783466196763274117120 }, some { target := 422, numerator := 7063149101098470953220833280 }, some { target := 423, numerator := 12349743931341381377049231360 }, some { target := 424, numerator := 376844845332997688052940800 }, some { target := 425, numerator := 7063149101098470953220833280 }, some { target := 426, numerator := 398378836494883270227394560 }, some { target := 427, numerator := 409145832075826061314621440 }, some { target := 428, numerator := 409145832075826061314621440 }, some { target := 429, numerator := 398378836494883270227394560 }, some { target := 430, numerator := 12349743931341381377049231360 }, some { target := 431, numerator := 398378836494883270227394560 }, some { target := 432, numerator := 516815787885253972186890240 }, some { target := 433, numerator := 527582783466196763274117120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 21080643979530096233938944 }, some { target := 454, numerator := 15810482984647572175454208 }, some { target := 455, numerator := 16688843150461326185201664 }, some { target := 456, numerator := 21519824062436973238812672 }, some { target := 457, numerator := 288102134386911315197165568 }, some { target := 458, numerator := 503739555094187924590166016 }, some { target := 459, numerator := 15371302901740695170580480 }, some { target := 460, numerator := 288102134386911315197165568 }, some { target := 461, numerator := 16249663067554449180327936 }, some { target := 462, numerator := 16688843150461326185201664 }, some { target := 463, numerator := 16688843150461326185201664 }, some { target := 464, numerator := 16249663067554449180327936 }, some { target := 465, numerator := 503739555094187924590166016 }, some { target := 466, numerator := 16249663067554449180327936 }, some { target := 467, numerator := 21080643979530096233938944 }, some { target := 468, numerator := 21519824062436973238812672 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 5, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 219, numerator := 73103339959466530481111040 }, some { target := 220, numerator := 8640345442699476510745559040 }, some { target := 222, numerator := 81995155913772683566189117440 }, some { target := 230, numerator := 8640351368716010189939015680 }, some { target := 237, numerator := 73103339959466530481111040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 359, numerator := 72890003364254079516672000 }, some { target := 360, numerator := 8615130426816112279683072000 }, some { target := 362, numerator := 81755870439316148497416192000 }, some { target := 370, numerator := 8615136335538823389773824000 }, some { target := 377, numerator := 72890003364254079516672000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 434, numerator := 72392217975425027266314240 }, some { target := 435, numerator := 8556295389754929073870602240 }, some { target := 437, numerator := 81197537665584233336946032640 }, some { target := 445, numerator := 8556301258125387522721710080 }, some { target := 452, numerator := 72392217975425027266314240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 72890003364254079516672000 }, some { target := 470, numerator := 8615130426816112279683072000 }, some { target := 472, numerator := 81755870439316148497416192000 }, some { target := 480, numerator := 8615136335538823389773824000 }, some { target := 487, numerator := 72890003364254079516672000 }]

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
def data : BetaFourLocalSlotData := ⟨2, 9, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3506605916160, 0, 137230882439168, 0, 0, 137230882439168, 0, 0, 0, 0, 0, 0, 3506605916160, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 488, numerator := 8883196367261260915031408640 }, some { target := 490, numerator := 347643534946928258255916367872 }, some { target := 493, numerator := 347643534946928258255916367872 }, some { target := 500, numerator := 8883196367261260915031408640 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 7, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 17, numerator := 10528491862206277260148736 }, some { target := 18, numerator := 255061206081190781366829056 }, some { target := 19, numerator := 193248769986947476162084864 }, some { target := 20, numerator := 215324640020605799449493504 }, some { target := 21, numerator := 10528491862206277260148736 }, some { target := 22, numerator := 215324640020605799449493504 }, some { target := 23, numerator := 214985011250857209860456448 }, some { target := 24, numerator := 10528491862206277260148736 }, some { target := 25, numerator := 255061206081190781366829056 }, some { target := 26, numerator := 10528491862206277260148736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 2088166730988789970029772800 }, some { target := 38, numerator := 50587523063631653790076108800 }, some { target := 39, numerator := 38327963546213596546675507200 }, some { target := 40, numerator := 42706377659577188419318579200 }, some { target := 41, numerator := 2088166730988789970029772800 }, some { target := 42, numerator := 42706377659577188419318579200 }, some { target := 43, numerator := 42639017442448517775124070400 }, some { target := 44, numerator := 2088166730988789970029772800 }, some { target := 45, numerator := 50587523063631653790076108800 }, some { target := 46, numerator := 2088166730988789970029772800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 2088166730988789970029772800 }, some { target := 154, numerator := 50587523063631653790076108800 }, some { target := 155, numerator := 38327963546213596546675507200 }, some { target := 156, numerator := 42706377659577188419318579200 }, some { target := 157, numerator := 2088166730988789970029772800 }, some { target := 158, numerator := 42706377659577188419318579200 }, some { target := 159, numerator := 42639017442448517775124070400 }, some { target := 160, numerator := 2088166730988789970029772800 }, some { target := 161, numerator := 50587523063631653790076108800 }, some { target := 162, numerator := 2088166730988789970029772800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 10528491862206277260148736 }, some { target := 383, numerator := 255061206081190781366829056 }, some { target := 384, numerator := 193248769986947476162084864 }, some { target := 385, numerator := 215324640020605799449493504 }, some { target := 386, numerator := 10528491862206277260148736 }, some { target := 387, numerator := 215324640020605799449493504 }, some { target := 388, numerator := 214985011250857209860456448 }, some { target := 389, numerator := 10528491862206277260148736 }, some { target := 390, numerator := 255061206081190781366829056 }, some { target := 391, numerator := 10528491862206277260148736 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 8, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 38061838108399194003734528 }, some { target := 62, numerator := 6675688811655512449146159104 }, some { target := 67, numerator := 6675689611996957628598059008 }, some { target := 75, numerator := 38061037766954014551834624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 1720325838853281653958115328 }, some { target := 178, numerator := 301728989601804230566036373504 }, some { target := 183, numerator := 301729025775781538917733367808 }, some { target := 191, numerator := 1720289664875973302261121024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 38264985644972891460075520 }, some { target := 393, numerator := 6711318980990953619571343360 }, some { target := 398, numerator := 6711319785604063045584158720 }, some { target := 406, numerator := 38264181031863465447260160 }]

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

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent3
