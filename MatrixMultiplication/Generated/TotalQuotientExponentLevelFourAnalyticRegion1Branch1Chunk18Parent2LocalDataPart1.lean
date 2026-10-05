import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 219, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 2541303872951645130555654144 }, some { target := 202, numerator := 99124533972871066372710334464 }, some { target := 205, numerator := 99124497614338497091184099328 }, some { target := 212, numerator := 2541315992462501557731065856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 1905977904713733847916740608 }, some { target := 298, numerator := 74343400479653299779532750848 }, some { target := 301, numerator := 74343373210753872818388074496 }, some { target := 308, numerator := 1905986994346876168298299392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 2011865566086719061689892864 }, some { target := 333, numerator := 78473589395189594211729014784 }, some { target := 336, numerator := 78473560611351310197187411968 }, some { target := 343, numerator := 2011875160699480399870427136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 2594247703638137737442230272 }, some { target := 469, numerator := 101189628430639213588808466432 }, some { target := 472, numerator := 101189591314637215780583768064 }, some { target := 479, numerator := 2594260075638803673517129728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 34731152930339150117593939968 }, some { target := 565, numerator := 1354701964295904573760374571008 }, some { target := 568, numerator := 1354701467395959460246182690816 }, some { target := 575, numerator := 34731318563654187955657900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 60726573797407020098902818816 }, some { target := 600, numerator := 2368663343060064856864557367296 }, some { target := 603, numerator := 2368662474242630336741420040192 }, some { target := 610, numerator := 60726863403218526806615261184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 1853034074027241241030164480 }, some { target := 661, numerator := 72278306021885152563434618880 }, some { target := 664, numerator := 72278279510455154128988405760 }, some { target := 671, numerator := 1853042911170574052512235520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 34731152930339150117593939968 }, some { target := 696, numerator := 1354701964295904573760374571008 }, some { target := 699, numerator := 1354701467395959460246182690816 }, some { target := 706, numerator := 34731318563654187955657900032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 1958921735400226454803316736 }, some { target := 722, numerator := 76408494937421446995630882816 }, some { target := 725, numerator := 76408466911052591507787743232 }, some { target := 732, numerator := 1958931077523178284084363264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 2011865566086719061689892864 }, some { target := 832, numerator := 78473589395189594211729014784 }, some { target := 835, numerator := 78473560611351310197187411968 }, some { target := 842, numerator := 2011875160699480399870427136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 2011865566086719061689892864 }, some { target := 867, numerator := 78473589395189594211729014784 }, some { target := 870, numerator := 78473560611351310197187411968 }, some { target := 877, numerator := 2011875160699480399870427136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 1958921735400226454803316736 }, some { target := 928, numerator := 76408494937421446995630882816 }, some { target := 931, numerator := 76408466911052591507787743232 }, some { target := 938, numerator := 1958931077523178284084363264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 60726573797407020098902818816 }, some { target := 963, numerator := 2368663343060064856864557367296 }, some { target := 966, numerator := 2368662474242630336741420040192 }, some { target := 973, numerator := 60726863403218526806615261184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 1958921735400226454803316736 }, some { target := 989, numerator := 76408494937421446995630882816 }, some { target := 992, numerator := 76408466911052591507787743232 }, some { target := 999, numerator := 1958931077523178284084363264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 2541303872951645130555654144 }, some { target := 1038, numerator := 99124533972871066372710334464 }, some { target := 1041, numerator := 99124497614338497091184099328 }, some { target := 1048, numerator := 2541315992462501557731065856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 2594247703638137737442230272 }, some { target := 1064, numerator := 101189628430639213588808466432 }, some { target := 1067, numerator := 101189591314637215780583768064 }, some { target := 1074, numerator := 2594260075638803673517129728 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 220, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 2552908000225396934804766720 }, some { target := 30, numerator := 1914681000169047701103575040 }, some { target := 31, numerator := 2021052166845105906720440320 }, some { target := 32, numerator := 2606093583563426037613199360 }, some { target := 33, numerator := 34889742669747091442331811840 }, some { target := 34, numerator := 61003864088719380921272238080 }, some { target := 35, numerator := 1861495416831018598295142400 }, some { target := 36, numerator := 34889742669747091442331811840 }, some { target := 37, numerator := 1967866583507076803912007680 }, some { target := 38, numerator := 2021052166845105906720440320 }, some { target := 39, numerator := 2021052166845105906720440320 }, some { target := 40, numerator := 1967866583507076803912007680 }, some { target := 41, numerator := 61003864088719380921272238080 }, some { target := 42, numerator := 1967866583507076803912007680 }, some { target := 43, numerator := 2552908000225396934804766720 }, some { target := 44, numerator := 2606093583563426037613199360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 99577157415669564392677048320 }, some { target := 105, numerator := 74682868061752173294507786240 }, some { target := 106, numerator := 78831916287405071810869329920 }, some { target := 107, numerator := 101651681528496013650857820160 }, some { target := 108, numerator := 1360887818014150713366586327040 }, some { target := 109, numerator := 2379479157411937299133345300480 }, some { target := 110, numerator := 72608343948925724036327014400 }, some { target := 111, numerator := 1360887818014150713366586327040 }, some { target := 112, numerator := 76757392174578622552688558080 }, some { target := 113, numerator := 78831916287405071810869329920 }, some { target := 114, numerator := 78831916287405071810869329920 }, some { target := 115, numerator := 76757392174578622552688558080 }, some { target := 116, numerator := 2379479157411937299133345300480 }, some { target := 117, numerator := 76757392174578622552688558080 }, some { target := 118, numerator := 99577157415669564392677048320 }, some { target := 119, numerator := 101651681528496013650857820160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 99577120891116298447764848640 }, some { target := 227, numerator := 74682840668337223835823636480 }, some { target := 228, numerator := 78831887372133736271147171840 }, some { target := 229, numerator := 101651644243014554665426616320 }, some { target := 230, numerator := 1360887318845256078786119598080 }, some { target := 231, numerator := 2379478284627299881658047528960 }, some { target := 232, numerator := 72608317316438967618161868800 }, some { target := 233, numerator := 1360887318845256078786119598080 }, some { target := 234, numerator := 76757364020235480053485404160 }, some { target := 235, numerator := 78831887372133736271147171840 }, some { target := 236, numerator := 78831887372133736271147171840 }, some { target := 237, numerator := 76757364020235480053485404160 }, some { target := 238, numerator := 2379478284627299881658047528960 }, some { target := 239, numerator := 76757364020235480053485404160 }, some { target := 240, numerator := 99577120891116298447764848640 }, some { target := 241, numerator := 101651644243014554665426616320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 2552920175076485583108833280 }, some { target := 625, numerator := 1914690131307364187331624960 }, some { target := 626, numerator := 2021061805268884419961159680 }, some { target := 627, numerator := 2606106012057245699423600640 }, some { target := 628, numerator := 34889909059378636302487388160 }, some { target := 629, numerator := 61004155016931853413038161920 }, some { target := 630, numerator := 1861504294326604071016857600 }, some { target := 631, numerator := 34889909059378636302487388160 }, some { target := 632, numerator := 1967875968288124303646392320 }, some { target := 633, numerator := 2021061805268884419961159680 }, some { target := 634, numerator := 2021061805268884419961159680 }, some { target := 635, numerator := 1967875968288124303646392320 }, some { target := 636, numerator := 61004155016931853413038161920 }, some { target := 637, numerator := 1967875968288124303646392320 }, some { target := 638, numerator := 2552920175076485583108833280 }, some { target := 639, numerator := 2606106012057245699423600640 }]

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

end Slot8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
