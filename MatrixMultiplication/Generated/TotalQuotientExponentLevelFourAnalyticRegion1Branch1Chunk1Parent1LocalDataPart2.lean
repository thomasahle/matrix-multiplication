import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 0, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 48, #[49882488373248, 0, 0, 181709966409728, 0, 49882521927680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 7733339014419009685231239168 }, some { target := 15, numerator := 5758869478822666786874327040 }, some { target := 16, numerator := 6087947734755390603267145728 }, some { target := 17, numerator := 7897878142385371593427648512 }, some { target := 18, numerator := 105798659282370706970291208192 }, some { target := 19, numerator := 191359005824878899232424067072 }, some { target := 20, numerator := 5758869478822666786874327040 }, some { target := 21, numerator := 105798659282370706970291208192 }, some { target := 22, numerator := 6252486862721752511463555072 }, some { target := 23, numerator := 6252486862721752511463555072 }, some { target := 24, numerator := 6087947734755390603267145728 }, some { target := 25, numerator := 6087947734755390603267145728 }, some { target := 26, numerator := 191359005824878899232424067072 }, some { target := 27, numerator := 6087947734755390603267145728 }, some { target := 28, numerator := 7733339014419009685231239168 }, some { target := 29, numerator := 7897878142385371593427648512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 28170703153989806533638094848 }, some { target := 137, numerator := 20978183199779643163347517440 }, some { target := 138, numerator := 22176936525481337058395947008 }, some { target := 139, numerator := 28770079816840653481162309632 }, some { target := 140, numerator := 385399194213094587258070106112 }, some { target := 141, numerator := 697075058895534999970661793792 }, some { target := 142, numerator := 20978183199779643163347517440 }, some { target := 143, numerator := 385399194213094587258070106112 }, some { target := 144, numerator := 22776313188332184005920161792 }, some { target := 145, numerator := 22776313188332184005920161792 }, some { target := 146, numerator := 22176936525481337058395947008 }, some { target := 147, numerator := 22176936525481337058395947008 }, some { target := 148, numerator := 697075058895534999970661793792 }, some { target := 149, numerator := 22176936525481337058395947008 }, some { target := 150, numerator := 28170703153989806533638094848 }, some { target := 151, numerator := 28770079816840653481162309632 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 7733344216400838471324794880 }, some { target := 268, numerator := 5758873352638922265880166400 }, some { target := 269, numerator := 6087951829932574966787604480 }, some { target := 270, numerator := 7897883455047664821778513920 }, some { target := 271, numerator := 105798730449909343341741342720 }, some { target := 272, numerator := 191359134546259045577675243520 }, some { target := 273, numerator := 5758873352638922265880166400 }, some { target := 274, numerator := 105798730449909343341741342720 }, some { target := 275, numerator := 6252491068579401317241323520 }, some { target := 276, numerator := 6252491068579401317241323520 }, some { target := 277, numerator := 6087951829932574966787604480 }, some { target := 278, numerator := 6087951829932574966787604480 }, some { target := 279, numerator := 191359134546259045577675243520 }, some { target := 280, numerator := 6087951829932574966787604480 }, some { target := 281, numerator := 7733344216400838471324794880 }, some { target := 282, numerator := 7897883455047664821778513920 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 568, #[3434312892416, 0, 137303192240128, 0, 0, 137303158685696, 0, 0, 0, 0, 0, 0, 3434312892416, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 56, numerator := 804302262188705231098871808 }, some { target := 57, numerator := 11662382801736225850933641216 }, some { target := 58, numerator := 20643758062843434264871043072 }, some { target := 59, numerator := 670251885157254359249059840 }, some { target := 60, numerator := 12868836195019283697581948928 }, some { target := 61, numerator := 670251885157254359249059840 }, some { target := 62, numerator := 20509707685811983393021231104 }, some { target := 63, numerator := 21448060325032139495969914880 }, some { target := 64, numerator := 12868836195019283697581948928 }, some { target := 65, numerator := 328557474104086086903889133568 }, some { target := 66, numerator := 21045909193937786880420478976 }, some { target := 67, numerator := 11662382801736225850933641216 }, some { target := 68, numerator := 20509707685811983393021231104 }, some { target := 69, numerator := 670251885157254359249059840 }, some { target := 70, numerator := 21045909193937786880420478976 }, some { target := 71, numerator := 670251885157254359249059840 }, some { target := 72, numerator := 20509707685811983393021231104 }, some { target := 73, numerator := 21448060325032139495969914880 }, some { target := 74, numerator := 804302262188705231098871808 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 32155855212941032288224804864 }, some { target := 153, numerator := 466259900587644968179259670528 }, some { target := 154, numerator := 825333617132153162064436658176 }, some { target := 155, numerator := 26796546010784193573520670720 }, some { target := 156, numerator := 514493683407056516611596877824 }, some { target := 157, numerator := 26796546010784193573520670720 }, some { target := 158, numerator := 819974307929996323349732524032 }, some { target := 159, numerator := 857489472345094194352661463040 }, some { target := 160, numerator := 514493683407056516611596877824 }, some { target := 161, numerator := 13135666854486411689739832786944 }, some { target := 162, numerator := 841411544738623678208549060608 }, some { target := 163, numerator := 466259900587644968179259670528 }, some { target := 164, numerator := 819974307929996323349732524032 }, some { target := 165, numerator := 26796546010784193573520670720 }, some { target := 166, numerator := 841411544738623678208549060608 }, some { target := 167, numerator := 26796546010784193573520670720 }, some { target := 168, numerator := 819974307929996323349732524032 }, some { target := 169, numerator := 857489472345094194352661463040 }, some { target := 170, numerator := 32155855212941032288224804864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 32155847354628056887955816448 }, some { target := 284, numerator := 466259786642106824875359338496 }, some { target := 285, numerator := 825333415435453460124199288832 }, some { target := 286, numerator := 26796539462190047406629847040 }, some { target := 287, numerator := 514493557674048910207293063168 }, some { target := 288, numerator := 26796539462190047406629847040 }, some { target := 289, numerator := 819974107543015450642873319424 }, some { target := 290, numerator := 857489262790081517012155105280 }, some { target := 291, numerator := 514493557674048910207293063168 }, some { target := 292, numerator := 13135663644365561238729951019008 }, some { target := 293, numerator := 841411339112767488568177197056 }, some { target := 294, numerator := 466259786642106824875359338496 }, some { target := 295, numerator := 819974107543015450642873319424 }, some { target := 296, numerator := 26796539462190047406629847040 }, some { target := 297, numerator := 841411339112767488568177197056 }, some { target := 298, numerator := 26796539462190047406629847040 }, some { target := 299, numerator := 819974107543015450642873319424 }, some { target := 300, numerator := 857489262790081517012155105280 }, some { target := 301, numerator := 32155847354628056887955816448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 804302262188705231098871808 }, some { target := 661, numerator := 11662382801736225850933641216 }, some { target := 662, numerator := 20643758062843434264871043072 }, some { target := 663, numerator := 670251885157254359249059840 }, some { target := 664, numerator := 12868836195019283697581948928 }, some { target := 665, numerator := 670251885157254359249059840 }, some { target := 666, numerator := 20509707685811983393021231104 }, some { target := 667, numerator := 21448060325032139495969914880 }, some { target := 668, numerator := 12868836195019283697581948928 }, some { target := 669, numerator := 328557474104086086903889133568 }, some { target := 670, numerator := 21045909193937786880420478976 }, some { target := 671, numerator := 11662382801736225850933641216 }, some { target := 672, numerator := 20509707685811983393021231104 }, some { target := 673, numerator := 670251885157254359249059840 }, some { target := 674, numerator := 21045909193937786880420478976 }, some { target := 675, numerator := 670251885157254359249059840 }, some { target := 676, numerator := 20509707685811983393021231104 }, some { target := 677, numerator := 21448060325032139495969914880 }, some { target := 678, numerator := 804302262188705231098871808 }]

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

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 244, #[139552882688, 22870029762560, 0, 235455811420160, 0, 0, 0, 0, 0, 0, 0, 22870029762560, 0, 0, 0, 0, 0, 0, 139552882688], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 72538768133718612799127552 }, some { target := 111, numerator := 81898609183230691869982720 }, some { target := 112, numerator := 70198807871340593031413760 }, some { target := 113, numerator := 924284303639317808246947840 }, some { target := 114, numerator := 81898609183230691869982720 }, some { target := 115, numerator := 70198807871340593031413760 }, some { target := 116, numerator := 81898609183230691869982720 }, some { target := 117, numerator := 81898609183230691869982720 }, some { target := 118, numerator := 3395282340710506682952712192 }, some { target := 119, numerator := 84238569445608711637696512 }, some { target := 120, numerator := 924284303639317808246947840 }, some { target := 121, numerator := 3395282340710506682952712192 }, some { target := 122, numerator := 72538768133718612799127552 }, some { target := 123, numerator := 81898609183230691869982720 }, some { target := 124, numerator := 84238569445608711637696512 }, some { target := 125, numerator := 81898609183230691869982720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 11887707041255093078054666240 }, some { target := 207, numerator := 13421604723997685733287526400 }, some { target := 208, numerator := 11504232620569444914246451200 }, some { target := 209, numerator := 151472396170831024704244940800 }, some { target := 210, numerator := 13421604723997685733287526400 }, some { target := 211, numerator := 11504232620569444914246451200 }, some { target := 212, numerator := 13421604723997685733287526400 }, some { target := 213, numerator := 13421604723997685733287526400 }, some { target := 214, numerator := 556421384414875485685720023040 }, some { target := 215, numerator := 13805079144683333897095741440 }, some { target := 216, numerator := 151472396170831024704244940800 }, some { target := 217, numerator := 556421384414875485685720023040 }, some { target := 218, numerator := 11887707041255093078054666240 }, some { target := 219, numerator := 13421604723997685733287526400 }, some { target := 220, numerator := 13805079144683333897095741440 }, some { target := 221, numerator := 13421604723997685733287526400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 122388546774263257857932656640 }, some { target := 303, numerator := 138180617325781097581536870400 }, some { target := 304, numerator := 118440529136383797927031603200 }, some { target := 305, numerator := 1559466966962386672705916108800 }, some { target := 306, numerator := 138180617325781097581536870400 }, some { target := 307, numerator := 118440529136383797927031603200 }, some { target := 308, numerator := 138180617325781097581536870400 }, some { target := 309, numerator := 138180617325781097581536870400 }, some { target := 310, numerator := 5728573592563096359737428541440 }, some { target := 311, numerator := 142128634963660557512437923840 }, some { target := 312, numerator := 1559466966962386672705916108800 }, some { target := 313, numerator := 5728573592563096359737428541440 }, some { target := 314, numerator := 122388546774263257857932656640 }, some { target := 315, numerator := 138180617325781097581536870400 }, some { target := 316, numerator := 142128634963660557512437923840 }, some { target := 317, numerator := 138180617325781097581536870400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 11887707041255093078054666240 }, some { target := 680, numerator := 13421604723997685733287526400 }, some { target := 681, numerator := 11504232620569444914246451200 }, some { target := 682, numerator := 151472396170831024704244940800 }, some { target := 683, numerator := 13421604723997685733287526400 }, some { target := 684, numerator := 11504232620569444914246451200 }, some { target := 685, numerator := 13421604723997685733287526400 }, some { target := 686, numerator := 13421604723997685733287526400 }, some { target := 687, numerator := 556421384414875485685720023040 }, some { target := 688, numerator := 13805079144683333897095741440 }, some { target := 689, numerator := 151472396170831024704244940800 }, some { target := 690, numerator := 556421384414875485685720023040 }, some { target := 691, numerator := 11887707041255093078054666240 }, some { target := 692, numerator := 13421604723997685733287526400 }, some { target := 693, numerator := 13805079144683333897095741440 }, some { target := 694, numerator := 13421604723997685733287526400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 72538768133718612799127552 }, some { target := 967, numerator := 81898609183230691869982720 }, some { target := 968, numerator := 70198807871340593031413760 }, some { target := 969, numerator := 924284303639317808246947840 }, some { target := 970, numerator := 81898609183230691869982720 }, some { target := 971, numerator := 70198807871340593031413760 }, some { target := 972, numerator := 81898609183230691869982720 }, some { target := 973, numerator := 81898609183230691869982720 }, some { target := 974, numerator := 3395282340710506682952712192 }, some { target := 975, numerator := 84238569445608711637696512 }, some { target := 976, numerator := 924284303639317808246947840 }, some { target := 977, numerator := 3395282340710506682952712192 }, some { target := 978, numerator := 72538768133718612799127552 }, some { target := 979, numerator := 81898609183230691869982720 }, some { target := 980, numerator := 84238569445608711637696512 }, some { target := 981, numerator := 81898609183230691869982720 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 7, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 257, numerator := 8151090473966150136889344 }, some { target := 258, numerator := 170154013644043384107565056 }, some { target := 259, numerator := 8830348013463329314963456 }, some { target := 260, numerator := 183059906894489788490973184 }, some { target := 261, numerator := 274080417187111798352904192 }, some { target := 262, numerator := 8490719243714739725926400 }, some { target := 263, numerator := 274080417187111798352904192 }, some { target := 264, numerator := 285627795358563844380164096 }, some { target := 265, numerator := 170154013644043384107565056 }, some { target := 266, numerator := 8490719243714739725926400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 1616645211088095460668211200 }, some { target := 354, numerator := 33747468781463992741448908800 }, some { target := 355, numerator := 1751365645345436749057228800 }, some { target := 356, numerator := 36307157032353477220840243200 }, some { target := 357, numerator := 54359695222837209864968601600 }, some { target := 358, numerator := 1684005428216766104862720000 }, some { target := 359, numerator := 54359695222837209864968601600 }, some { target := 360, numerator := 56649942605212011767581900800 }, some { target := 361, numerator := 33747468781463992741448908800 }, some { target := 362, numerator := 1684005428216766104862720000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 1616645211088095460668211200 }, some { target := 696, numerator := 33747468781463992741448908800 }, some { target := 697, numerator := 1751365645345436749057228800 }, some { target := 698, numerator := 36307157032353477220840243200 }, some { target := 699, numerator := 54359695222837209864968601600 }, some { target := 700, numerator := 1684005428216766104862720000 }, some { target := 701, numerator := 54359695222837209864968601600 }, some { target := 702, numerator := 56649942605212011767581900800 }, some { target := 703, numerator := 33747468781463992741448908800 }, some { target := 704, numerator := 1684005428216766104862720000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 8151090473966150136889344 }, some { target := 983, numerator := 170154013644043384107565056 }, some { target := 984, numerator := 8830348013463329314963456 }, some { target := 985, numerator := 183059906894489788490973184 }, some { target := 986, numerator := 274080417187111798352904192 }, some { target := 987, numerator := 8490719243714739725926400 }, some { target := 988, numerator := 274080417187111798352904192 }, some { target := 989, numerator := 285627795358563844380164096 }, some { target := 990, numerator := 170154013644043384107565056 }, some { target := 991, numerator := 8490719243714739725926400 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 0, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[67207648247808, 73529840107520, 67207648247808, 73529840107520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent1
