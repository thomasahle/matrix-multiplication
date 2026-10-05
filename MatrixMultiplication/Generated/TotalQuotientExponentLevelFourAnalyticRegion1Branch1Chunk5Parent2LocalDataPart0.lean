import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 24; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 17, numerator := 20641463896623219229065216 }, some { target := 18, numerator := 500056109237549601323483136 }, some { target := 19, numerator := 378870740554148765849616384 }, some { target := 20, numerator := 422151229369649064233140224 }, some { target := 21, numerator := 20641463896623219229065216 }, some { target := 22, numerator := 422151229369649064233140224 }, some { target := 23, numerator := 421485375695564444258009088 }, some { target := 24, numerator := 20641463896623219229065216 }, some { target := 25, numerator := 500056109237549601323483136 }, some { target := 26, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 15371302901740695170580480 }, some { target := 38, numerator := 372382209006685873325998080 }, some { target := 39, numerator := 282137785519046953292267520 }, some { target := 40, numerator := 314367936764632281875742720 }, some { target := 41, numerator := 15371302901740695170580480 }, some { target := 42, numerator := 314367936764632281875742720 }, some { target := 43, numerator := 313872088283930969128304640 }, some { target := 44, numerator := 15371302901740695170580480 }, some { target := 45, numerator := 372382209006685873325998080 }, some { target := 46, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 16249663067554449180327936 }, some { target := 52, numerator := 393661192378496494658912256 }, some { target := 53, numerator := 298259944691563922051825664 }, some { target := 54, numerator := 332331818865468412268642304 }, some { target := 55, numerator := 16249663067554449180327936 }, some { target := 56, numerator := 332331818865468412268642304 }, some { target := 57, numerator := 331807636185869881649922048 }, some { target := 58, numerator := 16249663067554449180327936 }, some { target := 59, numerator := 393661192378496494658912256 }, some { target := 60, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 88, numerator := 21080643979530096233938944 }, some { target := 89, numerator := 510695600923454911989940224 }, some { target := 90, numerator := 386931820140407250229395456 }, some { target := 91, numerator := 431133170420067129429590016 }, some { target := 92, numerator := 21080643979530096233938944 }, some { target := 93, numerator := 431133170420067129429590016 }, some { target := 94, numerator := 430453149646533900518817792 }, some { target := 95, numerator := 21080643979530096233938944 }, some { target := 96, numerator := 510695600923454911989940224 }, some { target := 97, numerator := 21080643979530096233938944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 108, numerator := 282392793309121914133807104 }, some { target := 109, numerator := 6841193154037114758531907584 }, some { target := 110, numerator := 5183274173964205456197943296 }, some { target := 111, numerator := 5775388095418815921317216256 }, some { target := 112, numerator := 282392793309121914133807104 }, some { target := 113, numerator := 5775388095418815921317216256 }, some { target := 114, numerator := 5766278650473360375699996672 }, some { target := 115, numerator := 282392793309121914133807104 }, some { target := 116, numerator := 6841193154037114758531907584 }, some { target := 117, numerator := 282392793309121914133807104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 122, numerator := 510766436420697956668145664 }, some { target := 123, numerator := 12373728830707876305089593344 }, some { target := 124, numerator := 9375035558818617333683060736 }, some { target := 125, numerator := 10445997441636209823471108096 }, some { target := 126, numerator := 510766436420697956668145664 }, some { target := 127, numerator := 10445997441636209823471108096 }, some { target := 128, numerator := 10429521104977477631320522752 }, some { target := 129, numerator := 510766436420697956668145664 }, some { target := 130, numerator := 12373728830707876305089593344 }, some { target := 131, numerator := 510766436420697956668145664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 15371302901740695170580480 }, some { target := 154, numerator := 372382209006685873325998080 }, some { target := 155, numerator := 282137785519046953292267520 }, some { target := 156, numerator := 314367936764632281875742720 }, some { target := 157, numerator := 15371302901740695170580480 }, some { target := 158, numerator := 314367936764632281875742720 }, some { target := 159, numerator := 313872088283930969128304640 }, some { target := 160, numerator := 15371302901740695170580480 }, some { target := 161, numerator := 372382209006685873325998080 }, some { target := 162, numerator := 15371302901740695170580480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 167, numerator := 282392793309121914133807104 }, some { target := 168, numerator := 6841193154037114758531907584 }, some { target := 169, numerator := 5183274173964205456197943296 }, some { target := 170, numerator := 5775388095418815921317216256 }, some { target := 171, numerator := 282392793309121914133807104 }, some { target := 172, numerator := 5775388095418815921317216256 }, some { target := 173, numerator := 5766278650473360375699996672 }, some { target := 174, numerator := 282392793309121914133807104 }, some { target := 175, numerator := 6841193154037114758531907584 }, some { target := 176, numerator := 282392793309121914133807104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 193, numerator := 16688843150461326185201664 }, some { target := 194, numerator := 404300684064401805325369344 }, some { target := 195, numerator := 306321024277822406431604736 }, some { target := 196, numerator := 341313759915886477465092096 }, some { target := 197, numerator := 16688843150461326185201664 }, some { target := 198, numerator := 341313759915886477465092096 }, some { target := 199, numerator := 340775410136839337910730752 }, some { target := 200, numerator := 16688843150461326185201664 }, some { target := 201, numerator := 404300684064401805325369344 }, some { target := 202, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 248, numerator := 16688843150461326185201664 }, some { target := 249, numerator := 404300684064401805325369344 }, some { target := 250, numerator := 306321024277822406431604736 }, some { target := 251, numerator := 341313759915886477465092096 }, some { target := 252, numerator := 16688843150461326185201664 }, some { target := 253, numerator := 341313759915886477465092096 }, some { target := 254, numerator := 340775410136839337910730752 }, some { target := 255, numerator := 16688843150461326185201664 }, some { target := 256, numerator := 404300684064401805325369344 }, some { target := 257, numerator := 16688843150461326185201664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 262, numerator := 16249663067554449180327936 }, some { target := 263, numerator := 393661192378496494658912256 }, some { target := 264, numerator := 298259944691563922051825664 }, some { target := 265, numerator := 332331818865468412268642304 }, some { target := 266, numerator := 16249663067554449180327936 }, some { target := 267, numerator := 332331818865468412268642304 }, some { target := 268, numerator := 331807636185869881649922048 }, some { target := 269, numerator := 16249663067554449180327936 }, some { target := 270, numerator := 393661192378496494658912256 }, some { target := 271, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 293, numerator := 16249663067554449180327936 }, some { target := 294, numerator := 393661192378496494658912256 }, some { target := 295, numerator := 298259944691563922051825664 }, some { target := 296, numerator := 332331818865468412268642304 }, some { target := 297, numerator := 16249663067554449180327936 }, some { target := 298, numerator := 332331818865468412268642304 }, some { target := 299, numerator := 331807636185869881649922048 }, some { target := 300, numerator := 16249663067554449180327936 }, some { target := 301, numerator := 393661192378496494658912256 }, some { target := 302, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 307, numerator := 510766436420697956668145664 }, some { target := 308, numerator := 12373728830707876305089593344 }, some { target := 309, numerator := 9375035558818617333683060736 }, some { target := 310, numerator := 10445997441636209823471108096 }, some { target := 311, numerator := 510766436420697956668145664 }, some { target := 312, numerator := 10445997441636209823471108096 }, some { target := 313, numerator := 10429521104977477631320522752 }, some { target := 314, numerator := 510766436420697956668145664 }, some { target := 315, numerator := 12373728830707876305089593344 }, some { target := 316, numerator := 510766436420697956668145664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 333, numerator := 16249663067554449180327936 }, some { target := 334, numerator := 393661192378496494658912256 }, some { target := 335, numerator := 298259944691563922051825664 }, some { target := 336, numerator := 332331818865468412268642304 }, some { target := 337, numerator := 16249663067554449180327936 }, some { target := 338, numerator := 332331818865468412268642304 }, some { target := 339, numerator := 331807636185869881649922048 }, some { target := 340, numerator := 16249663067554449180327936 }, some { target := 341, numerator := 393661192378496494658912256 }, some { target := 342, numerator := 16249663067554449180327936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 20641463896623219229065216 }, some { target := 383, numerator := 500056109237549601323483136 }, some { target := 384, numerator := 378870740554148765849616384 }, some { target := 385, numerator := 422151229369649064233140224 }, some { target := 386, numerator := 20641463896623219229065216 }, some { target := 387, numerator := 422151229369649064233140224 }, some { target := 388, numerator := 421485375695564444258009088 }, some { target := 389, numerator := 20641463896623219229065216 }, some { target := 390, numerator := 500056109237549601323483136 }, some { target := 391, numerator := 20641463896623219229065216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 21080643979530096233938944 }, some { target := 409, numerator := 510695600923454911989940224 }, some { target := 410, numerator := 386931820140407250229395456 }, some { target := 411, numerator := 431133170420067129429590016 }, some { target := 412, numerator := 21080643979530096233938944 }, some { target := 413, numerator := 431133170420067129429590016 }, some { target := 414, numerator := 430453149646533900518817792 }, some { target := 415, numerator := 21080643979530096233938944 }, some { target := 416, numerator := 510695600923454911989940224 }, some { target := 417, numerator := 21080643979530096233938944 }]

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

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 6, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0]⟩

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
  [some { target := 61, numerator := 10198284766993334824599552 }, some { target := 62, numerator := 1788683334819574877138190336 }, some { target := 67, numerator := 1788683549262974734011727872 }, some { target := 75, numerator := 10198070323593477951062016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 132, numerator := 250022465255320466667601920 }, some { target := 133, numerator := 43851591434286351826613698560 }, some { target := 138, numerator := 43851596691608412833835909120 }, some { target := 146, numerator := 250017207933259459445391360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 184885033517750134562095104 }, some { target := 178, numerator := 32427097876406486482311708672 }, some { target := 183, numerator := 32427101764057800016599711744 }, some { target := 191, numerator := 184881145866436600274092032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 203, numerator := 206268533835639385000771584 }, some { target := 204, numerator := 36177562933286240256956301312 }, some { target := 209, numerator := 36177567270576940587914625024 }, some { target := 217, numerator := 206264196544939054042447872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 272, numerator := 10198284766993334824599552 }, some { target := 273, numerator := 1788683334819574877138190336 }, some { target := 278, numerator := 1788683549262974734011727872 }, some { target := 286, numerator := 10198070323593477951062016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 317, numerator := 205939556907671858070945792 }, some { target := 318, numerator := 36119863470872705583500230656 }, some { target := 323, numerator := 36119867801245876886817472512 }, some { target := 331, numerator := 205935226534500554753703936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 343, numerator := 209558303115314654299029504 }, some { target := 344, numerator := 36754557557421586991517007872 }, some { target := 349, numerator := 36754561963887577598886150144 }, some { target := 357, numerator := 209553896649324046929887232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 10198284766993334824599552 }, some { target := 393, numerator := 1788683334819574877138190336 }, some { target := 398, numerator := 1788683549262974734011727872 }, some { target := 406, numerator := 10198070323593477951062016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 418, numerator := 250022465255320466667601920 }, some { target := 419, numerator := 43851591434286351826613698560 }, some { target := 424, numerator := 43851596691608412833835909120 }, some { target := 432, numerator := 250017207933259459445391360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 10198284766993334824599552 }, some { target := 454, numerator := 1788683334819574877138190336 }, some { target := 459, numerator := 1788683549262974734011727872 }, some { target := 467, numerator := 10198070323593477951062016 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 7, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[69122129920, 22265714442240, 0, 236805236457472, 0, 0, 0, 0, 0, 0, 0, 22265781551104, 0, 0, 0, 0, 0, 0, 69122129920]⟩

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
  [some { target := 219, numerator := 34181263366261587857899520 }, some { target := 220, numerator := 11010515015509806725663293440 }, some { target := 222, numerator := 117101457423705219428444536832 }, some { target := 230, numerator := 11010548201202395329146650624 }, some { target := 237, numerator := 34181263366261587857899520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 359, numerator := 34081512597683003457536000 }, some { target := 360, numerator := 10978383162351704176852992000 }, some { target := 362, numerator := 116759721653013472679139737600 }, some { target := 370, numerator := 10978416251198886393361203200 }, some { target := 377, numerator := 34081512597683003457536000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 434, numerator := 33848760804332973190021120 }, some { target := 435, numerator := 10903408838316131562962288640 }, some { target := 437, numerator := 115962338188066063597428539392 }, some { target := 445, numerator := 10903441701190698876528492544 }, some { target := 452, numerator := 33848760804332973190021120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 34081512597683003457536000 }, some { target := 470, numerator := 10978383162351704176852992000 }, some { target := 472, numerator := 116759721653013472679139737600 }, some { target := 480, numerator := 10978416251198886393361203200 }, some { target := 487, numerator := 34081512597683003457536000 }]

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

end Slot2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent2
