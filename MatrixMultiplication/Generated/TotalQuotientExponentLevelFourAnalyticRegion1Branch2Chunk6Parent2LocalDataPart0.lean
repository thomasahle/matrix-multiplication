import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 2,
parent 28; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 8, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 488, numerator := 8216010985828471699950010368 }, some { target := 490, numerator := 308696639071228878674225790976 }, some { target := 493, numerator := 308673291691337571148289277952 }, some { target := 500, numerator := 8239358365719779225886523392 }]

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
def data : BetaFourLocalSlotData := ⟨1, 5, #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  [some { target := 219, numerator := 54057491755103076902502400 }, some { target := 220, numerator := 8630126822702984920353996800 }, some { target := 222, numerator := 86115687698226131006966988800 }, some { target := 230, numerator := 8630126822702984920353996800 }, some { target := 237, numerator := 54051323625053430271180800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 359, numerator := 49409557884570849729576960 }, some { target := 360, numerator := 7888097226732260983276830720 }, some { target := 362, numerator := 78711348195201080490480107520 }, some { target := 370, numerator := 7888097226732260983276830720 }, some { target := 377, numerator := 49403920098413322247864320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 434, numerator := 54057491755103076902502400 }, some { target := 435, numerator := 8630126822702984920353996800 }, some { target := 437, numerator := 86115687698226131006966988800 }, some { target := 445, numerator := 8630126822702984920353996800 }, some { target := 452, numerator := 54051323625053430271180800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 49409557884570849729576960 }, some { target := 470, numerator := 7888097226732260983276830720 }, some { target := 472, numerator := 78711348195201080490480107520 }, some { target := 480, numerator := 7888097226732260983276830720 }, some { target := 487, numerator := 49403920098413322247864320 }]

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
def data : BetaFourLocalSlotData := ⟨2, 3, #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 61, numerator := 15937986879685052596224000 }, some { target := 62, numerator := 12396212017532818685952000 }, some { target := 63, numerator := 14167099448608935641088000 }, some { target := 64, numerator := 16646341852115499378278400 }, some { target := 65, numerator := 196568504849448982020096000 }, some { target := 66, numerator := 442013502796598792001945600 }, some { target := 67, numerator := 12396212017532818685952000 }, some { target := 68, numerator := 196568504849448982020096000 }, some { target := 69, numerator := 14167099448608935641088000 }, some { target := 70, numerator := 13812921962393712250060800 }, some { target := 71, numerator := 13812921962393712250060800 }, some { target := 72, numerator := 13812921962393712250060800 }, some { target := 73, numerator := 442013502796598792001945600 }, some { target := 74, numerator := 13812921962393712250060800 }, some { target := 75, numerator := 15937986879685052596224000 }, some { target := 76, numerator := 16646341852115499378278400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 132, numerator := 319397257068888454028328960 }, some { target := 133, numerator := 248420088831357686466478080 }, some { target := 134, numerator := 283908672950123070247403520 }, some { target := 135, numerator := 333592690716394607540699136 }, some { target := 136, numerator := 3939232837182957599682723840 }, some { target := 137, numerator := 8857950596043839791718989824 }, some { target := 138, numerator := 248420088831357686466478080 }, some { target := 139, numerator := 3939232837182957599682723840 }, some { target := 140, numerator := 283908672950123070247403520 }, some { target := 141, numerator := 276810956126369993491218432 }, some { target := 142, numerator := 276810956126369993491218432 }, some { target := 143, numerator := 276810956126369993491218432 }, some { target := 144, numerator := 8857950596043839791718989824 }, some { target := 145, numerator := 276810956126369993491218432 }, some { target := 146, numerator := 319397257068888454028328960 }, some { target := 147, numerator := 333592690716394607540699136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 536153878632605169336975360 }, some { target := 178, numerator := 417008572269804020595425280 }, some { target := 179, numerator := 476581225451204594966200320 }, some { target := 180, numerator := 559982939905165399085285376 }, some { target := 181, numerator := 6612564503135463755156029440 }, some { target := 182, numerator := 14869334234077583362945449984 }, some { target := 183, numerator := 417008572269804020595425280 }, some { target := 184, numerator := 6612564503135463755156029440 }, some { target := 185, numerator := 476581225451204594966200320 }, some { target := 186, numerator := 464666694814924480092045312 }, some { target := 187, numerator := 464666694814924480092045312 }, some { target := 188, numerator := 464666694814924480092045312 }, some { target := 189, numerator := 14869334234077583362945449984 }, some { target := 190, numerator := 464666694814924480092045312 }, some { target := 191, numerator := 536153878632605169336975360 }, some { target := 192, numerator := 559982939905165399085285376 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 203, numerator := 514478216476233497806110720 }, some { target := 204, numerator := 400149723925959387182530560 }, some { target := 205, numerator := 457313970201096442494320640 }, some { target := 206, numerator := 537343914986288319930826752 }, some { target := 207, numerator := 6345231336540213139608698880 }, some { target := 208, numerator := 14268195870274209005822803968 }, some { target := 209, numerator := 400149723925959387182530560 }, some { target := 210, numerator := 6345231336540213139608698880 }, some { target := 211, numerator := 457313970201096442494320640 }, some { target := 212, numerator := 445881120946069031431962624 }, some { target := 213, numerator := 445881120946069031431962624 }, some { target := 214, numerator := 445881120946069031431962624 }, some { target := 215, numerator := 14268195870274209005822803968 }, some { target := 216, numerator := 445881120946069031431962624 }, some { target := 217, numerator := 514478216476233497806110720 }, some { target := 218, numerator := 537343914986288319930826752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 272, numerator := 15937986879685052596224000 }, some { target := 273, numerator := 12396212017532818685952000 }, some { target := 274, numerator := 14167099448608935641088000 }, some { target := 275, numerator := 16646341852115499378278400 }, some { target := 276, numerator := 196568504849448982020096000 }, some { target := 277, numerator := 442013502796598792001945600 }, some { target := 278, numerator := 12396212017532818685952000 }, some { target := 279, numerator := 196568504849448982020096000 }, some { target := 280, numerator := 14167099448608935641088000 }, some { target := 281, numerator := 13812921962393712250060800 }, some { target := 282, numerator := 13812921962393712250060800 }, some { target := 283, numerator := 13812921962393712250060800 }, some { target := 284, numerator := 442013502796598792001945600 }, some { target := 285, numerator := 13812921962393712250060800 }, some { target := 286, numerator := 15937986879685052596224000 }, some { target := 287, numerator := 16646341852115499378278400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 317, numerator := 514478216476233497806110720 }, some { target := 318, numerator := 400149723925959387182530560 }, some { target := 319, numerator := 457313970201096442494320640 }, some { target := 320, numerator := 537343914986288319930826752 }, some { target := 321, numerator := 6345231336540213139608698880 }, some { target := 322, numerator := 14268195870274209005822803968 }, some { target := 323, numerator := 400149723925959387182530560 }, some { target := 324, numerator := 6345231336540213139608698880 }, some { target := 325, numerator := 457313970201096442494320640 }, some { target := 326, numerator := 445881120946069031431962624 }, some { target := 327, numerator := 445881120946069031431962624 }, some { target := 328, numerator := 445881120946069031431962624 }, some { target := 329, numerator := 14268195870274209005822803968 }, some { target := 330, numerator := 445881120946069031431962624 }, some { target := 331, numerator := 514478216476233497806110720 }, some { target := 332, numerator := 537343914986288319930826752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 343, numerator := 343622997126009733974589440 }, some { target := 344, numerator := 267262331098007570869125120 }, some { target := 345, numerator := 305442664112008652421857280 }, some { target := 346, numerator := 358895130331610166595682304 }, some { target := 347, numerator := 4238016964554120052353269760 }, some { target := 348, numerator := 9529811120294669955561947136 }, some { target := 349, numerator := 267262331098007570869125120 }, some { target := 350, numerator := 4238016964554120052353269760 }, some { target := 351, numerator := 305442664112008652421857280 }, some { target := 352, numerator := 297806597509208436111310848 }, some { target := 353, numerator := 297806597509208436111310848 }, some { target := 354, numerator := 297806597509208436111310848 }, some { target := 355, numerator := 9529811120294669955561947136 }, some { target := 356, numerator := 297806597509208436111310848 }, some { target := 357, numerator := 343622997126009733974589440 }, some { target := 358, numerator := 358895130331610166595682304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 16575506354872454700072960 }, some { target := 393, numerator := 12892060498234131433390080 }, some { target := 394, numerator := 14733783426553293066731520 }, some { target := 395, numerator := 17312195526200119353409536 }, some { target := 396, numerator := 204431245043426941300899840 }, some { target := 397, numerator := 459694042908462743682023424 }, some { target := 398, numerator := 12892060498234131433390080 }, some { target := 399, numerator := 204431245043426941300899840 }, some { target := 400, numerator := 14733783426553293066731520 }, some { target := 401, numerator := 14365438840889460740063232 }, some { target := 402, numerator := 14365438840889460740063232 }, some { target := 403, numerator := 14365438840889460740063232 }, some { target := 404, numerator := 459694042908462743682023424 }, some { target := 405, numerator := 14365438840889460740063232 }, some { target := 406, numerator := 16575506354872454700072960 }, some { target := 407, numerator := 17312195526200119353409536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 418, numerator := 319397257068888454028328960 }, some { target := 419, numerator := 248420088831357686466478080 }, some { target := 420, numerator := 283908672950123070247403520 }, some { target := 421, numerator := 333592690716394607540699136 }, some { target := 422, numerator := 3939232837182957599682723840 }, some { target := 423, numerator := 8857950596043839791718989824 }, some { target := 424, numerator := 248420088831357686466478080 }, some { target := 425, numerator := 3939232837182957599682723840 }, some { target := 426, numerator := 283908672950123070247403520 }, some { target := 427, numerator := 276810956126369993491218432 }, some { target := 428, numerator := 276810956126369993491218432 }, some { target := 429, numerator := 276810956126369993491218432 }, some { target := 430, numerator := 8857950596043839791718989824 }, some { target := 431, numerator := 276810956126369993491218432 }, some { target := 432, numerator := 319397257068888454028328960 }, some { target := 433, numerator := 333592690716394607540699136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 15300467404497650492375040 }, some { target := 454, numerator := 11900363536831505938513920 }, some { target := 455, numerator := 13600415470664578215444480 }, some { target := 456, numerator := 15980488178030879403147264 }, some { target := 457, numerator := 188705764655471022739292160 }, some { target := 458, numerator := 424332962684734840321867776 }, some { target := 459, numerator := 11900363536831505938513920 }, some { target := 460, numerator := 188705764655471022739292160 }, some { target := 461, numerator := 13600415470664578215444480 }, some { target := 462, numerator := 13260405083897963760058368 }, some { target := 463, numerator := 13260405083897963760058368 }, some { target := 464, numerator := 13260405083897963760058368 }, some { target := 465, numerator := 424332962684734840321867776 }, some { target := 466, numerator := 13260405083897963760058368 }, some { target := 467, numerator := 15300467404497650492375040 }, some { target := 468, numerator := 15980488178030879403147264 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 8, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944]⟩

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
  [some { target := 219, numerator := 86268190909062678763798528 }, some { target := 220, numerator := 12741360339032795315330613248 }, some { target := 222, numerator := 132801067968644959198899077120 }, some { target := 230, numerator := 12741360339032795315330613248 }, some { target := 237, numerator := 86268190909062678763798528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 359, numerator := 86268190909062678763798528 }, some { target := 360, numerator := 12741360339032795315330613248 }, some { target := 362, numerator := 132801067968644959198899077120 }, some { target := 370, numerator := 12741360339032795315330613248 }, some { target := 377, numerator := 86268190909062678763798528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 434, numerator := 86268190909062678763798528 }, some { target := 435, numerator := 12741360339032795315330613248 }, some { target := 437, numerator := 132801067968644959198899077120 }, some { target := 445, numerator := 12741360339032795315330613248 }, some { target := 452, numerator := 86268190909062678763798528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 86268190909062678763798528 }, some { target := 470, numerator := 12741360339032795315330613248 }, some { target := 472, numerator := 132801067968644959198899077120 }, some { target := 480, numerator := 12741360339032795315330613248 }, some { target := 487, numerator := 86268190909062678763798528 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 9, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0]⟩

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
  [some { target := 61, numerator := 358549272114740053772599296 }, some { target := 62, numerator := 30150136468820943846550536192 }, some { target := 67, numerator := 30150129194983439236564254720 }, some { target := 75, numerator := 358556545952244663758880768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 3472934454492201479791706112 }, some { target := 178, numerator := 292036425377825949890509799424 }, some { target := 183, numerator := 292036354922904267456868515840 }, some { target := 191, numerator := 3473004909413883913432989696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 358549272114740053772599296 }, some { target := 393, numerator := 30150136468820943846550536192 }, some { target := 398, numerator := 30150129194983439236564254720 }, some { target := 406, numerator := 358556545952244663758880768 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent2
