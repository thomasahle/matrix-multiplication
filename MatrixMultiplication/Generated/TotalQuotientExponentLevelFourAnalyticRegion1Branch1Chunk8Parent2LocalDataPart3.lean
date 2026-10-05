import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 1,
parent 36; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 9, #[49255926464512, 0, 0, 182973492101120, 0, 49245558145024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 124778796790142697563486158848 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 21, numerator := 463522134850471364181601812480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 124752530987764976596807581696 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 14, #[3506605916160, 0, 137230882439168, 0, 0, 137230882439168, 0, 0, 0, 0, 0, 0, 3506605916160, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 3468070803972007028242513920 }, some { target := 3, numerator := 3457949974777536190611456000 }, some { target := 4, numerator := 3434334706657104236138987520 }, some { target := 5, numerator := 3457949974777536190611456000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 135722812363177937630727766016 }, some { target := 23, numerator := 135326734116981893065657548800 }, some { target := 24, numerator := 134402551542524455747160375296 }, some { target := 25, numerator := 135326734116981893065657548800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 135722812363177937630727766016 }, some { target := 73, numerator := 135326734116981893065657548800 }, some { target := 74, numerator := 134402551542524455747160375296 }, some { target := 75, numerator := 135326734116981893065657548800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 3468070803972007028242513920 }, some { target := 302, numerator := 3457949974777536190611456000 }, some { target := 303, numerator := 3434334706657104236138987520 }, some { target := 304, numerator := 3457949974777536190611456000 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 28, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 12345077642960495808872448 }, some { target := 12, numerator := 302653516408063768217518080 }, some { target := 13, numerator := 223804310817541891760848896 }, some { target := 14, numerator := 249689151036652608779452416 }, some { target := 15, numerator := 12345077642960495808872448 }, some { target := 16, numerator := 249290922725589366979166208 }, some { target := 17, numerator := 253671434147285026782314496 }, some { target := 18, numerator := 12345077642960495808872448 }, some { target := 19, numerator := 302653516408063768217518080 }, some { target := 20, numerator := 12345077642960495808872448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 1459108919117343504149250048 }, some { target := 32, numerator := 35771702533199389133981614080 }, some { target := 33, numerator := 26452232662707969333286404096 }, some { target := 34, numerator := 29511654589889496035534831616 }, some { target := 35, numerator := 1459108919117343504149250048 }, some { target := 36, numerator := 29464586560240549470884855808 }, some { target := 37, numerator := 29982334886378961682034589696 }, some { target := 38, numerator := 1459108919117343504149250048 }, some { target := 39, numerator := 35771702533199389133981614080 }, some { target := 40, numerator := 1459108919117343504149250048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 13846652788551495979659952128 }, some { target := 77, numerator := 339466326429004417565856890880 }, some { target := 78, numerator := 251026415069869056147383648256 }, some { target := 79, numerator := 280059719303928644491831934976 }, some { target := 80, numerator := 13846652788551495979659952128 }, some { target := 81, numerator := 279613053084943112363455807488 }, some { target := 82, numerator := 284526381493783965775593209856 }, some { target := 83, numerator := 13846652788551495979659952128 }, some { target := 84, numerator := 339466326429004417565856890880 }, some { target := 85, numerator := 13846652788551495979659952128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 1459109919853209502892425216 }, some { target := 306, numerator := 35771727067369007167685263360 }, some { target := 307, numerator := 26452250805080765826630418432 }, some { target := 308, numerator := 29511674830579430913340342272 }, some { target := 309, numerator := 1459109919853209502892425216 }, some { target := 310, numerator := 29464606768648682219698651136 }, some { target := 311, numerator := 29982355449886917849757253632 }, some { target := 312, numerator := 1459109919853209502892425216 }, some { target := 313, numerator := 35771727067369007167685263360 }, some { target := 314, numerator := 1459109919853209502892425216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 12345077642960495808872448 }, some { target := 644, numerator := 302653516408063768217518080 }, some { target := 645, numerator := 223804310817541891760848896 }, some { target := 646, numerator := 249689151036652608779452416 }, some { target := 647, numerator := 12345077642960495808872448 }, some { target := 648, numerator := 249290922725589366979166208 }, some { target := 649, numerator := 253671434147285026782314496 }, some { target := 650, numerator := 12345077642960495808872448 }, some { target := 651, numerator := 302653516408063768217518080 }, some { target := 652, numerator := 12345077642960495808872448 }]

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

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 23, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 245034152063140150848258048 }, some { target := 56, numerator := 182472240898083091057213440 }, some { target := 57, numerator := 192899226092259267689054208 }, some { target := 58, numerator := 250247644660228239164178432 }, some { target := 59, numerator := 3352275739927640787136806912 }, some { target := 60, numerator := 6063291890413446711415406592 }, some { target := 61, numerator := 182472240898083091057213440 }, some { target := 62, numerator := 3352275739927640787136806912 }, some { target := 63, numerator := 198112718689347356004974592 }, some { target := 64, numerator := 198112718689347356004974592 }, some { target := 65, numerator := 192899226092259267689054208 }, some { target := 66, numerator := 192899226092259267689054208 }, some { target := 67, numerator := 6063291890413446711415406592 }, some { target := 68, numerator := 192899226092259267689054208 }, some { target := 69, numerator := 245034152063140150848258048 }, some { target := 70, numerator := 250247644660228239164178432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 183775614047355113136193536 }, some { target := 101, numerator := 136854180673562318292910080 }, some { target := 102, numerator := 144674419569194450766790656 }, some { target := 103, numerator := 187685733495171179373133824 }, some { target := 104, numerator := 2514206804945730590352605184 }, some { target := 105, numerator := 4547468917810085033561554944 }, some { target := 106, numerator := 136854180673562318292910080 }, some { target := 107, numerator := 2514206804945730590352605184 }, some { target := 108, numerator := 148584539017010517003730944 }, some { target := 109, numerator := 148584539017010517003730944 }, some { target := 110, numerator := 144674419569194450766790656 }, some { target := 111, numerator := 144674419569194450766790656 }, some { target := 112, numerator := 4547468917810085033561554944 }, some { target := 113, numerator := 144674419569194450766790656 }, some { target := 114, numerator := 183775614047355113136193536 }, some { target := 115, numerator := 187685733495171179373133824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 193985370383319286088204288 }, some { target := 127, numerator := 144457190710982447086960640 }, some { target := 128, numerator := 152711887323038586920501248 }, some { target := 129, numerator := 198112718689347356004974592 }, some { target := 130, numerator := 2653884960776048956483305472 }, some { target := 131, numerator := 4800106079910645313203863552 }, some { target := 132, numerator := 144457190710982447086960640 }, some { target := 133, numerator := 2653884960776048956483305472 }, some { target := 134, numerator := 156839235629066656837271552 }, some { target := 135, numerator := 156839235629066656837271552 }, some { target := 136, numerator := 152711887323038586920501248 }, some { target := 137, numerator := 152711887323038586920501248 }, some { target := 138, numerator := 4800106079910645313203863552 }, some { target := 139, numerator := 152711887323038586920501248 }, some { target := 140, numerator := 193985370383319286088204288 }, some { target := 141, numerator := 198112718689347356004974592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 250139030231122237324263424 }, some { target := 196, numerator := 186273745916793155454238720 }, some { target := 197, numerator := 196917959969181335765909504 }, some { target := 198, numerator := 255461137257316327480098816 }, some { target := 199, numerator := 3422114817842799970202157056 }, some { target := 200, numerator := 6189610471463726851236560896 }, some { target := 201, numerator := 186273745916793155454238720 }, some { target := 202, numerator := 3422114817842799970202157056 }, some { target := 203, numerator := 202240066995375425921744896 }, some { target := 204, numerator := 202240066995375425921744896 }, some { target := 205, numerator := 196917959969181335765909504 }, some { target := 206, numerator := 196917959969181335765909504 }, some { target := 207, numerator := 6189610471463726851236560896 }, some { target := 208, numerator := 196917959969181335765909504 }, some { target := 209, numerator := 250139030231122237324263424 }, some { target := 210, numerator := 255461137257316327480098816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 3348800078196248728259526656 }, some { target := 241, numerator := 2493787292273802244448583680 }, some { target := 242, numerator := 2636289423260876658417074176 }, some { target := 243, numerator := 3420051143689785935243771904 }, some { target := 244, numerator := 45814435112344424090869694464 }, some { target := 245, numerator := 82864989168983771722677223424 }, some { target := 246, numerator := 2493787292273802244448583680 }, some { target := 247, numerator := 45814435112344424090869694464 }, some { target := 248, numerator := 2707540488754413865401319424 }, some { target := 249, numerator := 2707540488754413865401319424 }, some { target := 250, numerator := 2636289423260876658417074176 }, some { target := 251, numerator := 2636289423260876658417074176 }, some { target := 252, numerator := 82864989168983771722677223424 }, some { target := 253, numerator := 2636289423260876658417074176 }, some { target := 254, numerator := 3348800078196248728259526656 }, some { target := 255, numerator := 3420051143689785935243771904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 5855295258675453187978166272 }, some { target := 267, numerator := 4360326256460443863387996160 }, some { target := 268, numerator := 4609487756829612084153024512 }, some { target := 269, numerator := 5979876008860037298360680448 }, some { target := 270, numerator := 80105422368687582975956615168 }, some { target := 271, numerator := 144887412464671320374863986688 }, some { target := 272, numerator := 4360326256460443863387996160 }, some { target := 273, numerator := 80105422368687582975956615168 }, some { target := 274, numerator := 4734068507014196194535538688 }, some { target := 275, numerator := 4734068507014196194535538688 }, some { target := 276, numerator := 4609487756829612084153024512 }, some { target := 277, numerator := 4609487756829612084153024512 }, some { target := 278, numerator := 144887412464671320374863986688 }, some { target := 279, numerator := 4609487756829612084153024512 }, some { target := 280, numerator := 5855295258675453187978166272 }, some { target := 281, numerator := 5979876008860037298360680448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 178670735879373026660188160 }, some { target := 316, numerator := 133052675654852253895884800 }, some { target := 317, numerator := 140655685692272382689935360 }, some { target := 318, numerator := 182472240898083091057213440 }, some { target := 319, numerator := 2444367727030571407287255040 }, some { target := 320, numerator := 4421150336759804893740400640 }, some { target := 321, numerator := 133052675654852253895884800 }, some { target := 322, numerator := 2444367727030571407287255040 }, some { target := 323, numerator := 144457190710982447086960640 }, some { target := 324, numerator := 144457190710982447086960640 }, some { target := 325, numerator := 140655685692272382689935360 }, some { target := 326, numerator := 140655685692272382689935360 }, some { target := 327, numerator := 4421150336759804893740400640 }, some { target := 328, numerator := 140655685692272382689935360 }, some { target := 329, numerator := 178670735879373026660188160 }, some { target := 330, numerator := 182472240898083091057213440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 3348800078196248728259526656 }, some { target := 342, numerator := 2493787292273802244448583680 }, some { target := 343, numerator := 2636289423260876658417074176 }, some { target := 344, numerator := 3420051143689785935243771904 }, some { target := 345, numerator := 45814435112344424090869694464 }, some { target := 346, numerator := 82864989168983771722677223424 }, some { target := 347, numerator := 2493787292273802244448583680 }, some { target := 348, numerator := 45814435112344424090869694464 }, some { target := 349, numerator := 2707540488754413865401319424 }, some { target := 350, numerator := 2707540488754413865401319424 }, some { target := 351, numerator := 2636289423260876658417074176 }, some { target := 352, numerator := 2636289423260876658417074176 }, some { target := 353, numerator := 82864989168983771722677223424 }, some { target := 354, numerator := 2636289423260876658417074176 }, some { target := 355, numerator := 3348800078196248728259526656 }, some { target := 356, numerator := 3420051143689785935243771904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 188880492215337199612198912 }, some { target := 377, numerator := 140655685692272382689935360 }, some { target := 378, numerator := 148693153446116518843645952 }, some { target := 379, numerator := 192899226092259267689054208 }, some { target := 380, numerator := 2584045882860889773417955328 }, some { target := 381, numerator := 4673787498860365173382709248 }, some { target := 382, numerator := 140655685692272382689935360 }, some { target := 383, numerator := 2584045882860889773417955328 }, some { target := 384, numerator := 152711887323038586920501248 }, some { target := 385, numerator := 152711887323038586920501248 }, some { target := 386, numerator := 148693153446116518843645952 }, some { target := 387, numerator := 148693153446116518843645952 }, some { target := 388, numerator := 4673787498860365173382709248 }, some { target := 389, numerator := 148693153446116518843645952 }, some { target := 390, numerator := 188880492215337199612198912 }, some { target := 391, numerator := 192899226092259267689054208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 193985370383319286088204288 }, some { target := 457, numerator := 144457190710982447086960640 }, some { target := 458, numerator := 152711887323038586920501248 }, some { target := 459, numerator := 198112718689347356004974592 }, some { target := 460, numerator := 2653884960776048956483305472 }, some { target := 461, numerator := 4800106079910645313203863552 }, some { target := 462, numerator := 144457190710982447086960640 }, some { target := 463, numerator := 2653884960776048956483305472 }, some { target := 464, numerator := 156839235629066656837271552 }, some { target := 465, numerator := 156839235629066656837271552 }, some { target := 466, numerator := 152711887323038586920501248 }, some { target := 467, numerator := 152711887323038586920501248 }, some { target := 468, numerator := 4800106079910645313203863552 }, some { target := 469, numerator := 152711887323038586920501248 }, some { target := 470, numerator := 193985370383319286088204288 }, some { target := 471, numerator := 198112718689347356004974592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 193985370383319286088204288 }, some { target := 483, numerator := 144457190710982447086960640 }, some { target := 484, numerator := 152711887323038586920501248 }, some { target := 485, numerator := 198112718689347356004974592 }, some { target := 486, numerator := 2653884960776048956483305472 }, some { target := 487, numerator := 4800106079910645313203863552 }, some { target := 488, numerator := 144457190710982447086960640 }, some { target := 489, numerator := 2653884960776048956483305472 }, some { target := 490, numerator := 156839235629066656837271552 }, some { target := 491, numerator := 156839235629066656837271552 }, some { target := 492, numerator := 152711887323038586920501248 }, some { target := 493, numerator := 152711887323038586920501248 }, some { target := 494, numerator := 4800106079910645313203863552 }, some { target := 495, numerator := 152711887323038586920501248 }, some { target := 496, numerator := 193985370383319286088204288 }, some { target := 497, numerator := 198112718689347356004974592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 188880492215337199612198912 }, some { target := 532, numerator := 140655685692272382689935360 }, some { target := 533, numerator := 148693153446116518843645952 }, some { target := 534, numerator := 192899226092259267689054208 }, some { target := 535, numerator := 2584045882860889773417955328 }, some { target := 536, numerator := 4673787498860365173382709248 }, some { target := 537, numerator := 140655685692272382689935360 }, some { target := 538, numerator := 2584045882860889773417955328 }, some { target := 539, numerator := 152711887323038586920501248 }, some { target := 540, numerator := 152711887323038586920501248 }, some { target := 541, numerator := 148693153446116518843645952 }, some { target := 542, numerator := 148693153446116518843645952 }, some { target := 543, numerator := 4673787498860365173382709248 }, some { target := 544, numerator := 148693153446116518843645952 }, some { target := 545, numerator := 188880492215337199612198912 }, some { target := 546, numerator := 192899226092259267689054208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 5855295258675453187978166272 }, some { target := 558, numerator := 4360326256460443863387996160 }, some { target := 559, numerator := 4609487756829612084153024512 }, some { target := 560, numerator := 5979876008860037298360680448 }, some { target := 561, numerator := 80105422368687582975956615168 }, some { target := 562, numerator := 144887412464671320374863986688 }, some { target := 563, numerator := 4360326256460443863387996160 }, some { target := 564, numerator := 80105422368687582975956615168 }, some { target := 565, numerator := 4734068507014196194535538688 }, some { target := 566, numerator := 4734068507014196194535538688 }, some { target := 567, numerator := 4609487756829612084153024512 }, some { target := 568, numerator := 4609487756829612084153024512 }, some { target := 569, numerator := 144887412464671320374863986688 }, some { target := 570, numerator := 4609487756829612084153024512 }, some { target := 571, numerator := 5855295258675453187978166272 }, some { target := 572, numerator := 5979876008860037298360680448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 188880492215337199612198912 }, some { target := 593, numerator := 140655685692272382689935360 }, some { target := 594, numerator := 148693153446116518843645952 }, some { target := 595, numerator := 192899226092259267689054208 }, some { target := 596, numerator := 2584045882860889773417955328 }, some { target := 597, numerator := 4673787498860365173382709248 }, some { target := 598, numerator := 140655685692272382689935360 }, some { target := 599, numerator := 2584045882860889773417955328 }, some { target := 600, numerator := 152711887323038586920501248 }, some { target := 601, numerator := 152711887323038586920501248 }, some { target := 602, numerator := 148693153446116518843645952 }, some { target := 603, numerator := 148693153446116518843645952 }, some { target := 604, numerator := 4673787498860365173382709248 }, some { target := 605, numerator := 148693153446116518843645952 }, some { target := 606, numerator := 188880492215337199612198912 }, some { target := 607, numerator := 192899226092259267689054208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 245034152063140150848258048 }, some { target := 654, numerator := 182472240898083091057213440 }, some { target := 655, numerator := 192899226092259267689054208 }, some { target := 656, numerator := 250247644660228239164178432 }, some { target := 657, numerator := 3352275739927640787136806912 }, some { target := 658, numerator := 6063291890413446711415406592 }, some { target := 659, numerator := 182472240898083091057213440 }, some { target := 660, numerator := 3352275739927640787136806912 }, some { target := 661, numerator := 198112718689347356004974592 }, some { target := 662, numerator := 198112718689347356004974592 }, some { target := 663, numerator := 192899226092259267689054208 }, some { target := 664, numerator := 192899226092259267689054208 }, some { target := 665, numerator := 6063291890413446711415406592 }, some { target := 666, numerator := 192899226092259267689054208 }, some { target := 667, numerator := 245034152063140150848258048 }, some { target := 668, numerator := 250247644660228239164178432 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 250139030231122237324263424 }, some { target := 689, numerator := 186273745916793155454238720 }, some { target := 690, numerator := 196917959969181335765909504 }, some { target := 691, numerator := 255461137257316327480098816 }, some { target := 692, numerator := 3422114817842799970202157056 }, some { target := 693, numerator := 6189610471463726851236560896 }, some { target := 694, numerator := 186273745916793155454238720 }, some { target := 695, numerator := 3422114817842799970202157056 }, some { target := 696, numerator := 202240066995375425921744896 }, some { target := 697, numerator := 202240066995375425921744896 }, some { target := 698, numerator := 196917959969181335765909504 }, some { target := 699, numerator := 196917959969181335765909504 }, some { target := 700, numerator := 6189610471463726851236560896 }, some { target := 701, numerator := 196917959969181335765909504 }, some { target := 702, numerator := 250139030231122237324263424 }, some { target := 703, numerator := 255461137257316327480098816 }]

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

end Slot15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent2
