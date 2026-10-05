import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 6; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70437463654400, 69956427317248, 70437463654400, 70643622084608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨9, 0, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨10, 48, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 262990065170536438714859520 }, some { target := 201, numerator := 257511105479483596241633280 }, some { target := 202, numerator := 202721508568955171509370880 }, some { target := 203, numerator := 6372030120694455796362117120 }, some { target := 204, numerator := 202721508568955171509370880 }, some { target := 205, numerator := 202721508568955171509370880 }, some { target := 206, numerator := 208200468260008013982597120 }, some { target := 207, numerator := 208200468260008013982597120 }, some { target := 208, numerator := 3522971081346977710284472320 }, some { target := 209, numerator := 191763589186849486562918400 }, some { target := 210, numerator := 6372030120694455796362117120 }, some { target := 211, numerator := 3522971081346977710284472320 }, some { target := 212, numerator := 262990065170536438714859520 }, some { target := 213, numerator := 202721508568955171509370880 }, some { target := 214, numerator := 191763589186849486562918400 }, some { target := 215, numerator := 257511105479483596241633280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 22019930641966308509469376512 }, some { target := 297, numerator := 21561182086925343748855431168 }, some { target := 298, numerator := 16973696536515696142715977728 }, some { target := 299, numerator := 533524569512642016594018435072 }, some { target := 300, numerator := 16973696536515696142715977728 }, some { target := 301, numerator := 16973696536515696142715977728 }, some { target := 302, numerator := 17432445091556660903329923072 }, some { target := 303, numerator := 17432445091556660903329923072 }, some { target := 304, numerator := 294975320891340341074766856192 }, some { target := 305, numerator := 16056199426433766621488087040 }, some { target := 306, numerator := 533524569512642016594018435072 }, some { target := 307, numerator := 294975320891340341074766856192 }, some { target := 308, numerator := 22019930641966308509469376512 }, some { target := 309, numerator := 16973696536515696142715977728 }, some { target := 310, numerator := 16056199426433766621488087040 }, some { target := 311, numerator := 21561182086925343748855431168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 22019938610959748351995674624 }, some { target := 660, numerator := 21561189889898086927995764736 }, some { target := 661, numerator := 16973702679281472687996665856 }, some { target := 662, numerator := 533524762594712236111895199744 }, some { target := 663, numerator := 16973702679281472687996665856 }, some { target := 664, numerator := 16973702679281472687996665856 }, some { target := 665, numerator := 17432451400343134111996575744 }, some { target := 666, numerator := 17432451400343134111996575744 }, some { target := 667, numerator := 294975427642648295631942057984 }, some { target := 668, numerator := 16056205237158149839996846080 }, some { target := 669, numerator := 533524762594712236111895199744 }, some { target := 670, numerator := 294975427642648295631942057984 }, some { target := 671, numerator := 22019938610959748351995674624 }, some { target := 672, numerator := 16973702679281472687996665856 }, some { target := 673, numerator := 16056205237158149839996846080 }, some { target := 674, numerator := 21561189889898086927995764736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 262982096177096596188561408 }, some { target := 1037, numerator := 257503302506740417101299712 }, some { target := 1038, numerator := 202715365803178626228682752 }, some { target := 1039, numerator := 6371837038624236278485352448 }, some { target := 1040, numerator := 202715365803178626228682752 }, some { target := 1041, numerator := 202715365803178626228682752 }, some { target := 1042, numerator := 208194159473534805315944448 }, some { target := 1043, numerator := 208194159473534805315944448 }, some { target := 1044, numerator := 3522864330039023153109270528 }, some { target := 1045, numerator := 191757778462466268054159360 }, some { target := 1046, numerator := 6371837038624236278485352448 }, some { target := 1047, numerator := 3522864330039023153109270528 }, some { target := 1048, numerator := 262982096177096596188561408 }, some { target := 1049, numerator := 202715365803178626228682752 }, some { target := 1050, numerator := 191757778462466268054159360 }, some { target := 1051, numerator := 257503302506740417101299712 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 568, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 71, numerator := 49126243565714781581082624 }, some { target := 72, numerator := 1310033161752394175495536640 }, some { target := 73, numerator := 1252719210925726930317606912 }, some { target := 74, numerator := 40938536304762317984235520 }, some { target := 75, numerator := 1285470039969536784704995328 }, some { target := 76, numerator := 40938536304762317984235520 }, some { target := 77, numerator := 1252719210925726930317606912 }, some { target := 78, numerator := 712330531702864332925698048 }, some { target := 79, numerator := 1285470039969536784704995328 }, some { target := 80, numerator := 20068070496594488275872251904 }, some { target := 81, numerator := 786019897051436505297321984 }, some { target := 82, numerator := 1310033161752394175495536640 }, some { target := 83, numerator := 1252719210925726930317606912 }, some { target := 84, numerator := 40938536304762317984235520 }, some { target := 85, numerator := 786019897051436505297321984 }, some { target := 86, numerator := 40938536304762317984235520 }, some { target := 87, numerator := 1260906918186679393914454016 }, some { target := 88, numerator := 712330531702864332925698048 }, some { target := 89, numerator := 49126243565714781581082624 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 5150798035386397210743668736 }, some { target := 147, numerator := 137354614276970592286497832960 }, some { target := 148, numerator := 131345349902353128873963552768 }, some { target := 149, numerator := 4292331696155331008953057280 }, some { target := 150, numerator := 134779215259277393681125998592 }, some { target := 151, numerator := 4292331696155331008953057280 }, some { target := 152, numerator := 131345349902353128873963552768 }, some { target := 153, numerator := 74686571513102759555783196672 }, some { target := 154, numerator := 134779215259277393681125998592 }, some { target := 155, numerator := 2104100997455343260588788678656 }, some { target := 156, numerator := 82412768566182355371898699776 }, some { target := 157, numerator := 137354614276970592286497832960 }, some { target := 158, numerator := 131345349902353128873963552768 }, some { target := 159, numerator := 4292331696155331008953057280 }, some { target := 160, numerator := 82412768566182355371898699776 }, some { target := 161, numerator := 4292331696155331008953057280 }, some { target := 162, numerator := 132203816241584195075754164224 }, some { target := 163, numerator := 74686571513102759555783196672 }, some { target := 164, numerator := 5150798035386397210743668736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 55520454604885787953594368000 }, some { target := 243, numerator := 1480545456130287678762516480000 }, some { target := 244, numerator := 1415771592424587592816656384000 }, some { target := 245, numerator := 46267045504071489961328640000 }, some { target := 246, numerator := 1452785228827844784785719296000 }, some { target := 247, numerator := 46267045504071489961328640000 }, some { target := 248, numerator := 1415771592424587592816656384000 }, some { target := 249, numerator := 805046591770843925327118336000 }, some { target := 250, numerator := 1452785228827844784785719296000 }, some { target := 251, numerator := 22680105706095844379043299328000 }, some { target := 252, numerator := 888327273678172607257509888000 }, some { target := 253, numerator := 1480545456130287678762516480000 }, some { target := 254, numerator := 1415771592424587592816656384000 }, some { target := 255, numerator := 46267045504071489961328640000 }, some { target := 256, numerator := 888327273678172607257509888000 }, some { target := 257, numerator := 46267045504071489961328640000 }, some { target := 258, numerator := 1425025001525401890808922112000 }, some { target := 259, numerator := 805046591770843925327118336000 }, some { target := 260, numerator := 55520454604885787953594368000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 5150801964542884910878162944 }, some { target := 641, numerator := 137354719054476930956751011840 }, some { target := 642, numerator := 131345450095843565227393155072 }, some { target := 643, numerator := 4292334970452404092398469120 }, some { target := 644, numerator := 134779318072205488501311930368 }, some { target := 645, numerator := 4292334970452404092398469120 }, some { target := 646, numerator := 131345450095843565227393155072 }, some { target := 647, numerator := 74686628485871831207733362688 }, some { target := 648, numerator := 134779318072205488501311930368 }, some { target := 649, numerator := 2104102602515768486093729562624 }, some { target := 650, numerator := 82412831432686158574050607104 }, some { target := 651, numerator := 137354719054476930956751011840 }, some { target := 652, numerator := 131345450095843565227393155072 }, some { target := 653, numerator := 4292334970452404092398469120 }, some { target := 654, numerator := 82412831432686158574050607104 }, some { target := 655, numerator := 4292334970452404092398469120 }, some { target := 656, numerator := 132203917089934046045872848896 }, some { target := 657, numerator := 74686628485871831207733362688 }, some { target := 658, numerator := 5150801964542884910878162944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 49126243565714781581082624 }, some { target := 1018, numerator := 1310033161752394175495536640 }, some { target := 1019, numerator := 1252719210925726930317606912 }, some { target := 1020, numerator := 40938536304762317984235520 }, some { target := 1021, numerator := 1285470039969536784704995328 }, some { target := 1022, numerator := 40938536304762317984235520 }, some { target := 1023, numerator := 1252719210925726930317606912 }, some { target := 1024, numerator := 712330531702864332925698048 }, some { target := 1025, numerator := 1285470039969536784704995328 }, some { target := 1026, numerator := 20068070496594488275872251904 }, some { target := 1027, numerator := 786019897051436505297321984 }, some { target := 1028, numerator := 1310033161752394175495536640 }, some { target := 1029, numerator := 1252719210925726930317606912 }, some { target := 1030, numerator := 40938536304762317984235520 }, some { target := 1031, numerator := 786019897051436505297321984 }, some { target := 1032, numerator := 40938536304762317984235520 }, some { target := 1033, numerator := 1260906918186679393914454016 }, some { target := 1034, numerator := 712330531702864332925698048 }, some { target := 1035, numerator := 49126243565714781581082624 }]

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

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 244, #[3909644976128, 0, 136827826601984, 0, 0, 136827893710848, 0, 0, 0, 0, 0, 0, 3909611421696, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 2294431184635224551399096320 }, some { target := 30, numerator := 2359986361339088110010499072 }, some { target := 31, numerator := 2294431184635224551399096320 }, some { target := 32, numerator := 2032210477819770316953485312 }, some { target := 33, numerator := 95120561397306023545145393152 }, some { target := 34, numerator := 25894294798026105651504087040 }, some { target := 35, numerator := 2359986361339088110010499072 }, some { target := 36, numerator := 95120561397306023545145393152 }, some { target := 37, numerator := 2294431184635224551399096320 }, some { target := 38, numerator := 2294431184635224551399096320 }, some { target := 39, numerator := 1966655301115906758342082560 }, some { target := 40, numerator := 2294431184635224551399096320 }, some { target := 41, numerator := 25894294798026105651504087040 }, some { target := 42, numerator := 1966655301115906758342082560 }, some { target := 43, numerator := 2294431184635224551399096320 }, some { target := 44, numerator := 2032210477819770316953485312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 80299370965486591322053672960 }, some { target := 105, numerator := 82593638707357636788398063616 }, some { target := 106, numerator := 80299370965486591322053672960 }, some { target := 107, numerator := 71122299998002409456676110336 }, some { target := 108, numerator := 3328982493454886971665710841856 }, some { target := 109, numerator := 906235758039062959206034309120 }, some { target := 110, numerator := 82593638707357636788398063616 }, some { target := 111, numerator := 3328982493454886971665710841856 }, some { target := 112, numerator := 80299370965486591322053672960 }, some { target := 113, numerator := 80299370965486591322053672960 }, some { target := 114, numerator := 68828032256131363990331719680 }, some { target := 115, numerator := 80299370965486591322053672960 }, some { target := 116, numerator := 906235758039062959206034309120 }, some { target := 117, numerator := 68828032256131363990331719680 }, some { target := 118, numerator := 80299370965486591322053672960 }, some { target := 119, numerator := 71122299998002409456676110336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 80299410349285188691946373120 }, some { target := 227, numerator := 82593679216407622654573412352 }, some { target := 228, numerator := 80299410349285188691946373120 }, some { target := 229, numerator := 71122334880795452841438216192 }, some { target := 230, numerator := 3328984126194651679771833925632 }, some { target := 231, numerator := 906236202513361415237680496640 }, some { target := 232, numerator := 82593679216407622654573412352 }, some { target := 233, numerator := 3328984126194651679771833925632 }, some { target := 234, numerator := 80299410349285188691946373120 }, some { target := 235, numerator := 80299410349285188691946373120 }, some { target := 236, numerator := 68828066013673018878811176960 }, some { target := 237, numerator := 80299410349285188691946373120 }, some { target := 238, numerator := 906236202513361415237680496640 }, some { target := 239, numerator := 68828066013673018878811176960 }, some { target := 240, numerator := 80299410349285188691946373120 }, some { target := 241, numerator := 71122334880795452841438216192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 2294411492735925866452746240 }, some { target := 625, numerator := 2359966106814095176922824704 }, some { target := 626, numerator := 2294411492735925866452746240 }, some { target := 627, numerator := 2032193036423248624572432384 }, some { target := 628, numerator := 95119745027423669492083851264 }, some { target := 629, numerator := 25894072560876877635680993280 }, some { target := 630, numerator := 2359966106814095176922824704 }, some { target := 631, numerator := 95119745027423669492083851264 }, some { target := 632, numerator := 2294411492735925866452746240 }, some { target := 633, numerator := 2294411492735925866452746240 }, some { target := 634, numerator := 1966638422345079314102353920 }, some { target := 635, numerator := 2294411492735925866452746240 }, some { target := 636, numerator := 25894072560876877635680993280 }, some { target := 637, numerator := 1966638422345079314102353920 }, some { target := 638, numerator := 2294411492735925866452746240 }, some { target := 639, numerator := 2032193036423248624572432384 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 7, #[51941589647360, 0, 0, 177591814193152, 0, 51941572870144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 5, numerator := 624644800745457443667968000 }, some { target := 6, numerator := 12517881806938967171106078720 }, some { target := 7, numerator := 21013051097077188404990443520 }, some { target := 8, numerator := 20163534168063366281602007040 }, some { target := 9, numerator := 624644800745457443667968000 }, some { target := 10, numerator := 20163534168063366281602007040 }, some { target := 11, numerator := 13467341904072062485481390080 }, some { target := 12, numerator := 649630592775275741414686720 }, some { target := 13, numerator := 12517881806938967171106078720 }, some { target := 14, numerator := 599659008715639145921249280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 2135702895191310108039577600 }, some { target := 95, numerator := 42799486019633854565113135104 }, some { target := 96, numerator := 71845045394235672034451390464 }, some { target := 97, numerator := 68940489456775490287517564928 }, some { target := 98, numerator := 2135702895191310108039577600 }, some { target := 99, numerator := 68940489456775490287517564928 }, some { target := 100, numerator := 46045754420324645929333293056 }, some { target := 101, numerator := 2221131010998962512361160704 }, some { target := 102, numerator := 42799486019633854565113135104 }, some { target := 103, numerator := 2050274779383657703717994496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 624644598984194137469747200 }, some { target := 217, numerator := 12517877763643250514893733888 }, some { target := 218, numerator := 21013044309828290784482295808 }, some { target := 219, numerator := 20163527655209786757523439616 }, some { target := 220, numerator := 624644598984194137469747200 }, some { target := 221, numerator := 20163527655209786757523439616 }, some { target := 222, numerator := 13467337554099225603847749632 }, some { target := 223, numerator := 649630382943561902968537088 }, some { target := 224, numerator := 12517877763643250514893733888 }, some { target := 225, numerator := 599658815024826371970957312 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 0, #[140769314734080, 0, 140705661976576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨15, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent1
