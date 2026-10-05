import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 2,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 26, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 131, numerator := 8143988477497771959517184 }, some { target := 132, numerator := 199659072351558280297840640 }, some { target := 133, numerator := 8143988477497771959517184 }, some { target := 134, numerator := 167345827747292927039111168 }, some { target := 135, numerator := 164456025384309846666379264 }, some { target := 136, numerator := 8143988477497771959517184 }, some { target := 137, numerator := 164718734690035581245718528 }, some { target := 138, numerator := 147642629817862833588666368 }, some { target := 139, numerator := 199659072351558280297840640 }, some { target := 140, numerator := 8143988477497771959517184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 1300164900766094550617817088 }, some { target := 228, numerator := 31875010470394576079662612480 }, some { target := 229, numerator := 1300164900766094550617817088 }, some { target := 230, numerator := 26716291670580717056243531776 }, some { target := 231, numerator := 26254942834825006086669467648 }, some { target := 232, numerator := 1300164900766094550617817088 }, some { target := 233, numerator := 26296883638075525265721655296 }, some { target := 234, numerator := 23570731426791778627329458176 }, some { target := 235, numerator := 31875010470394576079662612480 }, some { target := 236, numerator := 1300164900766094550617817088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 12973690520517805904974839808 }, some { target := 303, numerator := 318064670825597822186479943680 }, some { target := 304, numerator := 12973690520517805904974839808 }, some { target := 305, numerator := 266588414889349753595773321216 }, some { target := 306, numerator := 261984847285295048274653216768 }, some { target := 307, numerator := 12973690520517805904974839808 }, some { target := 308, numerator := 262403353431118203303845953536 }, some { target := 309, numerator := 235200453952613126406318063616 }, some { target := 310, numerator := 318064670825597822186479943680 }, some { target := 311, numerator := 12973690520517805904974839808 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 1300164900766094550617817088 }, some { target := 590, numerator := 31875010470394576079662612480 }, some { target := 591, numerator := 1300164900766094550617817088 }, some { target := 592, numerator := 26716291670580717056243531776 }, some { target := 593, numerator := 26254942834825006086669467648 }, some { target := 594, numerator := 1300164900766094550617817088 }, some { target := 595, numerator := 26296883638075525265721655296 }, some { target := 596, numerator := 23570731426791778627329458176 }, some { target := 597, numerator := 31875010470394576079662612480 }, some { target := 598, numerator := 1300164900766094550617817088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 8143059222765058840854528 }, some { target := 764, numerator := 199636290622627249001594880 }, some { target := 765, numerator := 8143059222765058840854528 }, some { target := 766, numerator := 167326733061333628439494656 }, some { target := 767, numerator := 164437260433900865624997888 }, some { target := 768, numerator := 8143059222765058840854528 }, some { target := 769, numerator := 164699939763667480426315776 }, some { target := 770, numerator := 147625783328837518340653056 }, some { target := 771, numerator := 199636290622627249001594880 }, some { target := 772, numerator := 8143059222765058840854528 }]

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

end Slot21

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 601, #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 7233138577855827380375912448 }, some { target := 81, numerator := 7082448190817164309951414272 }, some { target := 82, numerator := 5575544320430533605706432512 }, some { target := 83, numerator := 175252920125965150903691378688 }, some { target := 84, numerator := 5575544320430533605706432512 }, some { target := 85, numerator := 5575544320430533605706432512 }, some { target := 86, numerator := 5726234707469196676130930688 }, some { target := 87, numerator := 5726234707469196676130930688 }, some { target := 88, numerator := 96893918865860354282952327168 }, some { target := 89, numerator := 5274163546353207464857436160 }, some { target := 90, numerator := 175252920125965150903691378688 }, some { target := 91, numerator := 96893918865860354282952327168 }, some { target := 92, numerator := 7233138577855827380375912448 }, some { target := 93, numerator := 5575544320430533605706432512 }, some { target := 94, numerator := 5274163546353207464857436160 }, some { target := 95, numerator := 7082448190817164309951414272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 271767597776086752075014209536 }, some { target := 177, numerator := 266105772822418278073451413504 }, some { target := 178, numerator := 209487523285733538057823453184 }, some { target := 179, numerator := 6584702421116435263817531785216 }, some { target := 180, numerator := 209487523285733538057823453184 }, some { target := 181, numerator := 209487523285733538057823453184 }, some { target := 182, numerator := 215149348239402012059386249216 }, some { target := 183, numerator := 215149348239402012059386249216 }, some { target := 184, numerator := 3640553445208828783004877848576 }, some { target := 185, numerator := 198163873378396590054697861120 }, some { target := 186, numerator := 6584702421116435263817531785216 }, some { target := 187, numerator := 3640553445208828783004877848576 }, some { target := 188, numerator := 271767597776086752075014209536 }, some { target := 189, numerator := 209487523285733538057823453184 }, some { target := 190, numerator := 198163873378396590054697861120 }, some { target := 191, numerator := 266105772822418278073451413504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 271747043417715644912287875072 }, some { target := 287, numerator := 266085646679846568976615211008 }, some { target := 288, numerator := 209471679301155809619888570368 }, some { target := 289, numerator := 6584204406141735313187308306432 }, some { target := 290, numerator := 209471679301155809619888570368 }, some { target := 291, numerator := 209471679301155809619888570368 }, some { target := 292, numerator := 215133076039024885555561234432 }, some { target := 293, numerator := 215133076039024885555561234432 }, some { target := 294, numerator := 3640278102449815826637522993152 }, some { target := 295, numerator := 198148885825417657748543242240 }, some { target := 296, numerator := 6584204406141735313187308306432 }, some { target := 297, numerator := 3640278102449815826637522993152 }, some { target := 298, numerator := 271747043417715644912287875072 }, some { target := 299, numerator := 209471679301155809619888570368 }, some { target := 300, numerator := 198148885825417657748543242240 }, some { target := 301, numerator := 266085646679846568976615211008 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 7253692936226934543102246912 }, some { target := 574, numerator := 7102574333388873406787616768 }, some { target := 575, numerator := 5591388305008262043641315328 }, some { target := 576, numerator := 175750935100665101533914857472 }, some { target := 577, numerator := 5591388305008262043641315328 }, some { target := 578, numerator := 5591388305008262043641315328 }, some { target := 579, numerator := 5742506907846323179955945472 }, some { target := 580, numerator := 5742506907846323179955945472 }, some { target := 581, numerator := 97169261624873310650307182592 }, some { target := 582, numerator := 5289151099332139771012055040 }, some { target := 583, numerator := 175750935100665101533914857472 }, some { target := 584, numerator := 97169261624873310650307182592 }, some { target := 585, numerator := 7253692936226934543102246912 }, some { target := 586, numerator := 5591388305008262043641315328 }, some { target := 587, numerator := 5289151099332139771012055040 }, some { target := 588, numerator := 7102574333388873406787616768 }]

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

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 2296, #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 49047518764966292801842053120 }, some { target := 27, numerator := 1307933833732434474715788083200 }, some { target := 28, numerator := 1250711728506640466446972354560 }, some { target := 29, numerator := 40872932304138577334868377600 }, some { target := 30, numerator := 1283410074349951328314867056640 }, some { target := 31, numerator := 40872932304138577334868377600 }, some { target := 32, numerator := 1250711728506640466446972354560 }, some { target := 33, numerator := 711189022092011245626709770240 }, some { target := 34, numerator := 1283410074349951328314867056640 }, some { target := 35, numerator := 20035911415488730609552478699520 }, some { target := 36, numerator := 784760300239460684829472849920 }, some { target := 37, numerator := 1307933833732434474715788083200 }, some { target := 38, numerator := 1250711728506640466446972354560 }, some { target := 39, numerator := 40872932304138577334868377600 }, some { target := 40, numerator := 784760300239460684829472849920 }, some { target := 41, numerator := 40872932304138577334868377600 }, some { target := 42, numerator := 1258886314967468181913946030080 }, some { target := 43, numerator := 711189022092011245626709770240 }, some { target := 44, numerator := 49047518764966292801842053120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 168371555926245518568352382976 }, some { target := 158, numerator := 4489908158033213828489396879360 }, some { target := 159, numerator := 4293474676119260723492985765888 }, some { target := 160, numerator := 140309629938537932140293652480 }, some { target := 161, numerator := 4405722380070091069205220687872 }, some { target := 162, numerator := 140309629938537932140293652480 }, some { target := 163, numerator := 4293474676119260723492985765888 }, some { target := 164, numerator := 2441387560930560019241109553152 }, some { target := 165, numerator := 4405722380070091069205220687872 }, some { target := 166, numerator := 68779780595871294335171948445696 }, some { target := 167, numerator := 2693944894819928297093638127616 }, some { target := 168, numerator := 4489908158033213828489396879360 }, some { target := 169, numerator := 4293474676119260723492985765888 }, some { target := 170, numerator := 140309629938537932140293652480 }, some { target := 171, numerator := 2693944894819928297093638127616 }, some { target := 172, numerator := 140309629938537932140293652480 }, some { target := 173, numerator := 4321536602106968309921044496384 }, some { target := 174, numerator := 2441387560930560019241109553152 }, some { target := 175, numerator := 168371555926245518568352382976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 49047518764966292801842053120 }, some { target := 268, numerator := 1307933833732434474715788083200 }, some { target := 269, numerator := 1250711728506640466446972354560 }, some { target := 270, numerator := 40872932304138577334868377600 }, some { target := 271, numerator := 1283410074349951328314867056640 }, some { target := 272, numerator := 40872932304138577334868377600 }, some { target := 273, numerator := 1250711728506640466446972354560 }, some { target := 274, numerator := 711189022092011245626709770240 }, some { target := 275, numerator := 1283410074349951328314867056640 }, some { target := 276, numerator := 20035911415488730609552478699520 }, some { target := 277, numerator := 784760300239460684829472849920 }, some { target := 278, numerator := 1307933833732434474715788083200 }, some { target := 279, numerator := 1250711728506640466446972354560 }, some { target := 280, numerator := 40872932304138577334868377600 }, some { target := 281, numerator := 784760300239460684829472849920 }, some { target := 282, numerator := 40872932304138577334868377600 }, some { target := 283, numerator := 1258886314967468181913946030080 }, some { target := 284, numerator := 711189022092011245626709770240 }, some { target := 285, numerator := 49047518764966292801842053120 }]

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

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 321, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 108658252666962870222591098880 }, some { target := 11, numerator := 111762774171733237943236558848 }, some { target := 12, numerator := 108658252666962870222591098880 }, some { target := 13, numerator := 96240166647881399340009259008 }, some { target := 14, numerator := 4504660703421803562656562413568 }, some { target := 15, numerator := 1226285994384295249654956687360 }, some { target := 16, numerator := 111762774171733237943236558848 }, some { target := 17, numerator := 4504660703421803562656562413568 }, some { target := 18, numerator := 108658252666962870222591098880 }, some { target := 19, numerator := 108658252666962870222591098880 }, some { target := 20, numerator := 93135645143111031619363799040 }, some { target := 21, numerator := 108658252666962870222591098880 }, some { target := 22, numerator := 1226285994384295249654956687360 }, some { target := 23, numerator := 93135645143111031619363799040 }, some { target := 24, numerator := 108658252666962870222591098880 }, some { target := 25, numerator := 96240166647881399340009259008 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 108658252666962870222591098880 }, some { target := 142, numerator := 111762774171733237943236558848 }, some { target := 143, numerator := 108658252666962870222591098880 }, some { target := 144, numerator := 96240166647881399340009259008 }, some { target := 145, numerator := 4504660703421803562656562413568 }, some { target := 146, numerator := 1226285994384295249654956687360 }, some { target := 147, numerator := 111762774171733237943236558848 }, some { target := 148, numerator := 4504660703421803562656562413568 }, some { target := 149, numerator := 108658252666962870222591098880 }, some { target := 150, numerator := 108658252666962870222591098880 }, some { target := 151, numerator := 93135645143111031619363799040 }, some { target := 152, numerator := 108658252666962870222591098880 }, some { target := 153, numerator := 1226285994384295249654956687360 }, some { target := 154, numerator := 93135645143111031619363799040 }, some { target := 155, numerator := 108658252666962870222591098880 }, some { target := 156, numerator := 96240166647881399340009259008 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 3, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 1450710983537555009647411200 }, some { target := 1, numerator := 29072248110092602393334120448 }, some { target := 2, numerator := 48801917486203350524538912768 }, some { target := 3, numerator := 46828950548592275711418433536 }, some { target := 4, numerator := 1450710983537555009647411200 }, some { target := 5, numerator := 46828950548592275711418433536 }, some { target := 6, numerator := 31277328805069686007998185472 }, some { target := 7, numerator := 1508739422879057210033307648 }, some { target := 8, numerator := 29072248110092602393334120448 }, some { target := 9, numerator := 1392682544196052809261514752 }]

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

end Slot25

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent3
