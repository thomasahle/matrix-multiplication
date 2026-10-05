import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 28; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 3, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 17, numerator := 15937986879685052596224000 }, some { target := 18, numerator := 319397257068888454028328960 }, some { target := 19, numerator := 536153878632605169336975360 }, some { target := 20, numerator := 514478216476233497806110720 }, some { target := 21, numerator := 15937986879685052596224000 }, some { target := 22, numerator := 514478216476233497806110720 }, some { target := 23, numerator := 343622997126009733974589440 }, some { target := 24, numerator := 16575506354872454700072960 }, some { target := 25, numerator := 319397257068888454028328960 }, some { target := 26, numerator := 15300467404497650492375040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 12396212017532818685952000 }, some { target := 38, numerator := 248420088831357686466478080 }, some { target := 39, numerator := 417008572269804020595425280 }, some { target := 40, numerator := 400149723925959387182530560 }, some { target := 41, numerator := 12396212017532818685952000 }, some { target := 42, numerator := 400149723925959387182530560 }, some { target := 43, numerator := 267262331098007570869125120 }, some { target := 44, numerator := 12892060498234131433390080 }, some { target := 45, numerator := 248420088831357686466478080 }, some { target := 46, numerator := 11900363536831505938513920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 14167099448608935641088000 }, some { target := 52, numerator := 283908672950123070247403520 }, some { target := 53, numerator := 476581225451204594966200320 }, some { target := 54, numerator := 457313970201096442494320640 }, some { target := 55, numerator := 14167099448608935641088000 }, some { target := 56, numerator := 457313970201096442494320640 }, some { target := 57, numerator := 305442664112008652421857280 }, some { target := 58, numerator := 14733783426553293066731520 }, some { target := 59, numerator := 283908672950123070247403520 }, some { target := 60, numerator := 13600415470664578215444480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 88, numerator := 16646341852115499378278400 }, some { target := 89, numerator := 333592690716394607540699136 }, some { target := 90, numerator := 559982939905165399085285376 }, some { target := 91, numerator := 537343914986288319930826752 }, some { target := 92, numerator := 16646341852115499378278400 }, some { target := 93, numerator := 537343914986288319930826752 }, some { target := 94, numerator := 358895130331610166595682304 }, some { target := 95, numerator := 17312195526200119353409536 }, some { target := 96, numerator := 333592690716394607540699136 }, some { target := 97, numerator := 15980488178030879403147264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 108, numerator := 196568504849448982020096000 }, some { target := 109, numerator := 3939232837182957599682723840 }, some { target := 110, numerator := 6612564503135463755156029440 }, some { target := 111, numerator := 6345231336540213139608698880 }, some { target := 112, numerator := 196568504849448982020096000 }, some { target := 113, numerator := 6345231336540213139608698880 }, some { target := 114, numerator := 4238016964554120052353269760 }, some { target := 115, numerator := 204431245043426941300899840 }, some { target := 116, numerator := 3939232837182957599682723840 }, some { target := 117, numerator := 188705764655471022739292160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 122, numerator := 442013502796598792001945600 }, some { target := 123, numerator := 8857950596043839791718989824 }, some { target := 124, numerator := 14869334234077583362945449984 }, some { target := 125, numerator := 14268195870274209005822803968 }, some { target := 126, numerator := 442013502796598792001945600 }, some { target := 127, numerator := 14268195870274209005822803968 }, some { target := 128, numerator := 9529811120294669955561947136 }, some { target := 129, numerator := 459694042908462743682023424 }, some { target := 130, numerator := 8857950596043839791718989824 }, some { target := 131, numerator := 424332962684734840321867776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 12396212017532818685952000 }, some { target := 154, numerator := 248420088831357686466478080 }, some { target := 155, numerator := 417008572269804020595425280 }, some { target := 156, numerator := 400149723925959387182530560 }, some { target := 157, numerator := 12396212017532818685952000 }, some { target := 158, numerator := 400149723925959387182530560 }, some { target := 159, numerator := 267262331098007570869125120 }, some { target := 160, numerator := 12892060498234131433390080 }, some { target := 161, numerator := 248420088831357686466478080 }, some { target := 162, numerator := 11900363536831505938513920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 167, numerator := 196568504849448982020096000 }, some { target := 168, numerator := 3939232837182957599682723840 }, some { target := 169, numerator := 6612564503135463755156029440 }, some { target := 170, numerator := 6345231336540213139608698880 }, some { target := 171, numerator := 196568504849448982020096000 }, some { target := 172, numerator := 6345231336540213139608698880 }, some { target := 173, numerator := 4238016964554120052353269760 }, some { target := 174, numerator := 204431245043426941300899840 }, some { target := 175, numerator := 3939232837182957599682723840 }, some { target := 176, numerator := 188705764655471022739292160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 193, numerator := 14167099448608935641088000 }, some { target := 194, numerator := 283908672950123070247403520 }, some { target := 195, numerator := 476581225451204594966200320 }, some { target := 196, numerator := 457313970201096442494320640 }, some { target := 197, numerator := 14167099448608935641088000 }, some { target := 198, numerator := 457313970201096442494320640 }, some { target := 199, numerator := 305442664112008652421857280 }, some { target := 200, numerator := 14733783426553293066731520 }, some { target := 201, numerator := 283908672950123070247403520 }, some { target := 202, numerator := 13600415470664578215444480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 248, numerator := 13812921962393712250060800 }, some { target := 249, numerator := 276810956126369993491218432 }, some { target := 250, numerator := 464666694814924480092045312 }, some { target := 251, numerator := 445881120946069031431962624 }, some { target := 252, numerator := 13812921962393712250060800 }, some { target := 253, numerator := 445881120946069031431962624 }, some { target := 254, numerator := 297806597509208436111310848 }, some { target := 255, numerator := 14365438840889460740063232 }, some { target := 256, numerator := 276810956126369993491218432 }, some { target := 257, numerator := 13260405083897963760058368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 262, numerator := 13812921962393712250060800 }, some { target := 263, numerator := 276810956126369993491218432 }, some { target := 264, numerator := 464666694814924480092045312 }, some { target := 265, numerator := 445881120946069031431962624 }, some { target := 266, numerator := 13812921962393712250060800 }, some { target := 267, numerator := 445881120946069031431962624 }, some { target := 268, numerator := 297806597509208436111310848 }, some { target := 269, numerator := 14365438840889460740063232 }, some { target := 270, numerator := 276810956126369993491218432 }, some { target := 271, numerator := 13260405083897963760058368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 293, numerator := 13812921962393712250060800 }, some { target := 294, numerator := 276810956126369993491218432 }, some { target := 295, numerator := 464666694814924480092045312 }, some { target := 296, numerator := 445881120946069031431962624 }, some { target := 297, numerator := 13812921962393712250060800 }, some { target := 298, numerator := 445881120946069031431962624 }, some { target := 299, numerator := 297806597509208436111310848 }, some { target := 300, numerator := 14365438840889460740063232 }, some { target := 301, numerator := 276810956126369993491218432 }, some { target := 302, numerator := 13260405083897963760058368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 307, numerator := 442013502796598792001945600 }, some { target := 308, numerator := 8857950596043839791718989824 }, some { target := 309, numerator := 14869334234077583362945449984 }, some { target := 310, numerator := 14268195870274209005822803968 }, some { target := 311, numerator := 442013502796598792001945600 }, some { target := 312, numerator := 14268195870274209005822803968 }, some { target := 313, numerator := 9529811120294669955561947136 }, some { target := 314, numerator := 459694042908462743682023424 }, some { target := 315, numerator := 8857950596043839791718989824 }, some { target := 316, numerator := 424332962684734840321867776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 333, numerator := 13812921962393712250060800 }, some { target := 334, numerator := 276810956126369993491218432 }, some { target := 335, numerator := 464666694814924480092045312 }, some { target := 336, numerator := 445881120946069031431962624 }, some { target := 337, numerator := 13812921962393712250060800 }, some { target := 338, numerator := 445881120946069031431962624 }, some { target := 339, numerator := 297806597509208436111310848 }, some { target := 340, numerator := 14365438840889460740063232 }, some { target := 341, numerator := 276810956126369993491218432 }, some { target := 342, numerator := 13260405083897963760058368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 15937986879685052596224000 }, some { target := 383, numerator := 319397257068888454028328960 }, some { target := 384, numerator := 536153878632605169336975360 }, some { target := 385, numerator := 514478216476233497806110720 }, some { target := 386, numerator := 15937986879685052596224000 }, some { target := 387, numerator := 514478216476233497806110720 }, some { target := 388, numerator := 343622997126009733974589440 }, some { target := 389, numerator := 16575506354872454700072960 }, some { target := 390, numerator := 319397257068888454028328960 }, some { target := 391, numerator := 15300467404497650492375040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 16646341852115499378278400 }, some { target := 409, numerator := 333592690716394607540699136 }, some { target := 410, numerator := 559982939905165399085285376 }, some { target := 411, numerator := 537343914986288319930826752 }, some { target := 412, numerator := 16646341852115499378278400 }, some { target := 413, numerator := 537343914986288319930826752 }, some { target := 414, numerator := 358895130331610166595682304 }, some { target := 415, numerator := 17312195526200119353409536 }, some { target := 416, numerator := 333592690716394607540699136 }, some { target := 417, numerator := 15980488178030879403147264 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 5, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 2, numerator := 54057491755103076902502400 }, some { target := 3, numerator := 49409557884570849729576960 }, some { target := 4, numerator := 54057491755103076902502400 }, some { target := 5, numerator := 49409557884570849729576960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 8, numerator := 8630126822702984920353996800 }, some { target := 9, numerator := 7888097226732260983276830720 }, some { target := 10, numerator := 8630126822702984920353996800 }, some { target := 11, numerator := 7888097226732260983276830720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 28, numerator := 86115687698226131006966988800 }, some { target := 29, numerator := 78711348195201080490480107520 }, some { target := 30, numerator := 86115687698226131006966988800 }, some { target := 31, numerator := 78711348195201080490480107520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 149, numerator := 8630126822702984920353996800 }, some { target := 150, numerator := 7888097226732260983276830720 }, some { target := 151, numerator := 8630126822702984920353996800 }, some { target := 152, numerator := 7888097226732260983276830720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 378, numerator := 54051323625053430271180800 }, some { target := 379, numerator := 49403920098413322247864320 }, some { target := 380, numerator := 54051323625053430271180800 }, some { target := 381, numerator := 49403920098413322247864320 }]

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
def data : BetaFourLocalSlotData := ⟨11, 9, #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 0, numerator := 9243012359057030662443761664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 6, numerator := 347283718955132488508504014848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 27, numerator := 347257453152754767541825437696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 148, numerator := 9269278161434751629122338816 }]

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

end Slot11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6.Parent2
