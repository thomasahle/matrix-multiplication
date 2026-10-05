import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 1,
parent 23; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 43, #[69122129920, 22265714442240, 0, 236805236457472, 0, 0, 0, 0, 0, 0, 0, 22265781551104, 0, 0, 0, 0, 0, 0, 69122129920], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 11, numerator := 6331798786440619318312960 }, some { target := 12, numerator := 155231196054673247803801600 }, some { target := 13, numerator := 114789384450955743770705920 }, some { target := 14, numerator := 128065736745105429438136320 }, some { target := 15, numerator := 6331798786440619318312960 }, some { target := 16, numerator := 127861485171349280427868160 }, some { target := 17, numerator := 130108252482666919540817920 }, some { target := 18, numerator := 6331798786440619318312960 }, some { target := 19, numerator := 155231196054673247803801600 }, some { target := 20, numerator := 6331798786440619318312960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 2039607631416699884006277120 }, some { target := 32, numerator := 50003283866990061672411955200 }, some { target := 33, numerator := 36976112543747914026178314240 }, some { target := 34, numerator := 41252709190266800879739863040 }, some { target := 35, numerator := 2039607631416699884006277120 }, some { target := 36, numerator := 41186915395704971851223531520 }, some { target := 37, numerator := 41910647135885091164903178240 }, some { target := 38, numerator := 2039607631416699884006277120 }, some { target := 39, numerator := 50003283866990061672411955200 }, some { target := 40, numerator := 2039607631416699884006277120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 21692084872957067467776065536 }, some { target := 77, numerator := 531805951724108750822897090560 }, some { target := 78, numerator := 393256506406511997319037059072 }, some { target := 79, numerator := 438739910172389719428890099712 }, some { target := 80, numerator := 21692084872957067467776065536 }, some { target := 81, numerator := 438040165499068523704123129856 }, some { target := 82, numerator := 445737356905601676676559798272 }, some { target := 83, numerator := 21692084872957067467776065536 }, some { target := 84, numerator := 531805951724108750822897090560 }, some { target := 85, numerator := 21692084872957067467776065536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 2039613778794162447714353152 }, some { target := 306, numerator := 50003434576889143879448657920 }, some { target := 307, numerator := 36976223989752235342434402304 }, some { target := 308, numerator := 41252833525933543700545142784 }, some { target := 309, numerator := 2039613778794162447714353152 }, some { target := 310, numerator := 41187039533069215879651131392 }, some { target := 311, numerator := 41910773454576821909485256704 }, some { target := 312, numerator := 2039613778794162447714353152 }, some { target := 313, numerator := 50003434576889143879448657920 }, some { target := 314, numerator := 2039613778794162447714353152 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 6331798786440619318312960 }, some { target := 644, numerator := 155231196054673247803801600 }, some { target := 645, numerator := 114789384450955743770705920 }, some { target := 646, numerator := 128065736745105429438136320 }, some { target := 647, numerator := 6331798786440619318312960 }, some { target := 648, numerator := 127861485171349280427868160 }, some { target := 649, numerator := 130108252482666919540817920 }, some { target := 650, numerator := 6331798786440619318312960 }, some { target := 651, numerator := 155231196054673247803801600 }, some { target := 652, numerator := 6331798786440619318312960 }]

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
def data : BetaFourLocalSlotData := ⟨13, 50, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 128849296787281380848435200 }, some { target := 56, numerator := 95951603990528687865856000 }, some { target := 57, numerator := 101434552789987470029619200 }, some { target := 58, numerator := 131590771187010771930316800 }, some { target := 59, numerator := 1762768039025998465649868800 }, some { target := 60, numerator := 3188334726885281828228300800 }, some { target := 61, numerator := 95951603990528687865856000 }, some { target := 62, numerator := 1762768039025998465649868800 }, some { target := 63, numerator := 104176027189716861111500800 }, some { target := 64, numerator := 104176027189716861111500800 }, some { target := 65, numerator := 101434552789987470029619200 }, some { target := 66, numerator := 101434552789987470029619200 }, some { target := 67, numerator := 3188334726885281828228300800 }, some { target := 68, numerator := 101434552789987470029619200 }, some { target := 69, numerator := 128849296787281380848435200 }, some { target := 70, numerator := 131590771187010771930316800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 22598956111967747103627673600 }, some { target := 101, numerator := 16829009870614279758020608000 }, some { target := 102, numerator := 17790667577506524315621785600 }, some { target := 103, numerator := 23079784965413869382428262400 }, some { target := 104, numerator := 309172952765856625268778598400 }, some { target := 105, numerator := 559203956557840210245084774400 }, some { target := 106, numerator := 16829009870614279758020608000 }, some { target := 107, numerator := 309172952765856625268778598400 }, some { target := 108, numerator := 18271496430952646594422374400 }, some { target := 109, numerator := 18271496430952646594422374400 }, some { target := 110, numerator := 17790667577506524315621785600 }, some { target := 111, numerator := 17790667577506524315621785600 }, some { target := 112, numerator := 559203956557840210245084774400 }, some { target := 113, numerator := 17790667577506524315621785600 }, some { target := 114, numerator := 22598956111967747103627673600 }, some { target := 115, numerator := 23079784965413869382428262400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 22598958821333282929718067200 }, some { target := 316, numerator := 16829011888226912820002816000 }, some { target := 317, numerator := 17790669710411307838288691200 }, some { target := 318, numerator := 23079787732425480438861004800 }, some { target := 319, numerator := 309172989832282998378908876800 }, some { target := 320, numerator := 559204023600225703133236428800 }, some { target := 321, numerator := 16829011888226912820002816000 }, some { target := 322, numerator := 309172989832282998378908876800 }, some { target := 323, numerator := 18271498621503505347431628800 }, some { target := 324, numerator := 18271498621503505347431628800 }, some { target := 325, numerator := 17790669710411307838288691200 }, some { target := 326, numerator := 17790669710411307838288691200 }, some { target := 327, numerator := 559204023600225703133236428800 }, some { target := 328, numerator := 17790669710411307838288691200 }, some { target := 329, numerator := 22598958821333282929718067200 }, some { target := 330, numerator := 23079787732425480438861004800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 128846587421745554758041600 }, some { target := 654, numerator := 95949586377895625883648000 }, some { target := 655, numerator := 101432419885203947362713600 }, some { target := 656, numerator := 131588004175399715497574400 }, some { target := 657, numerator := 1762730972599625355519590400 }, some { target := 658, numerator := 3188267684499788940076646400 }, some { target := 659, numerator := 95949586377895625883648000 }, some { target := 660, numerator := 1762730972599625355519590400 }, some { target := 661, numerator := 104173836638858108102246400 }, some { target := 662, numerator := 104173836638858108102246400 }, some { target := 663, numerator := 101432419885203947362713600 }, some { target := 664, numerator := 101432419885203947362713600 }, some { target := 665, numerator := 3188267684499788940076646400 }, some { target := 666, numerator := 101432419885203947362713600 }, some { target := 667, numerator := 128846587421745554758041600 }, some { target := 668, numerator := 131588004175399715497574400 }]

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
def data : BetaFourLocalSlotData := ⟨14, 6, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 142, numerator := 5270160994882524058484736 }, some { target := 143, numerator := 76417334425796598848028672 }, some { target := 144, numerator := 135267465535318117501108224 }, some { target := 145, numerator := 4391800829068770048737280 }, some { target := 146, numerator := 84322575918120384935755776 }, some { target := 147, numerator := 4391800829068770048737280 }, some { target := 148, numerator := 134389105369504363491360768 }, some { target := 149, numerator := 140537626530200641559592960 }, some { target := 150, numerator := 84322575918120384935755776 }, some { target := 151, numerator := 2152860766409511077891014656 }, some { target := 152, numerator := 137902546032759379530350592 }, some { target := 153, numerator := 76417334425796598848028672 }, some { target := 154, numerator := 134389105369504363491360768 }, some { target := 155, numerator := 4391800829068770048737280 }, some { target := 156, numerator := 137902546032759379530350592 }, some { target := 157, numerator := 4391800829068770048737280 }, some { target := 158, numerator := 134389105369504363491360768 }, some { target := 159, numerator := 140537626530200641559592960 }, some { target := 160, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 127673900230863727997485056 }, some { target := 283, numerator := 1851271553347524055963533312 }, some { target := 284, numerator := 3276963439258835685268783104 }, some { target := 285, numerator := 106394916859053106664570880 }, some { target := 286, numerator := 2042782403693819647959760896 }, some { target := 287, numerator := 106394916859053106664570880 }, some { target := 288, numerator := 3255684455887025063935868928 }, some { target := 289, numerator := 3404637339489699413266268160 }, some { target := 290, numerator := 2042782403693819647959760896 }, some { target := 291, numerator := 52154788244307832886972645376 }, some { target := 292, numerator := 3340800389374267549267525632 }, some { target := 293, numerator := 1851271553347524055963533312 }, some { target := 294, numerator := 3255684455887025063935868928 }, some { target := 295, numerator := 106394916859053106664570880 }, some { target := 296, numerator := 3340800389374267549267525632 }, some { target := 297, numerator := 106394916859053106664570880 }, some { target := 298, numerator := 3255684455887025063935868928 }, some { target := 299, numerator := 3404637339489699413266268160 }, some { target := 300, numerator := 127673900230863727997485056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 96732955035101812557348864 }, some { target := 358, numerator := 1402627848008976282081558528 }, some { target := 359, numerator := 2482812512567613188971954176 }, some { target := 360, numerator := 80610795862584843797790720 }, some { target := 361, numerator := 1547727280561629000917581824 }, some { target := 362, numerator := 80610795862584843797790720 }, some { target := 363, numerator := 2466690353395096220212396032 }, some { target := 364, numerator := 2579545467602715001529303040 }, some { target := 365, numerator := 1547727280561629000917581824 }, some { target := 366, numerator := 39515412131839090429677010944 }, some { target := 367, numerator := 2531178990085164095250628608 }, some { target := 368, numerator := 1402627848008976282081558528 }, some { target := 369, numerator := 2466690353395096220212396032 }, some { target := 370, numerator := 80610795862584843797790720 }, some { target := 371, numerator := 2531178990085164095250628608 }, some { target := 372, numerator := 80610795862584843797790720 }, some { target := 373, numerator := 2466690353395096220212396032 }, some { target := 374, numerator := 2579545467602715001529303040 }, some { target := 375, numerator := 96732955035101812557348864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 107783292605016782357397504 }, some { target := 393, numerator := 1562857742772743344182263808 }, some { target := 394, numerator := 2766437843528764080506535936 }, some { target := 395, numerator := 89819410504180651964497920 }, some { target := 396, numerator := 1724532681680268517718360064 }, some { target := 397, numerator := 89819410504180651964497920 }, some { target := 398, numerator := 2748473961427927950113636352 }, some { target := 399, numerator := 2874221136133780862863933440 }, some { target := 400, numerator := 1724532681680268517718360064 }, some { target := 401, numerator := 44029475029149355592996880384 }, some { target := 402, numerator := 2820329489831272471685234688 }, some { target := 403, numerator := 1562857742772743344182263808 }, some { target := 404, numerator := 2748473961427927950113636352 }, some { target := 405, numerator := 89819410504180651964497920 }, some { target := 406, numerator := 2820329489831272471685234688 }, some { target := 407, numerator := 89819410504180651964497920 }, some { target := 408, numerator := 2748473961427927950113636352 }, some { target := 409, numerator := 2874221136133780862863933440 }, some { target := 410, numerator := 107783292605016782357397504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 5270160994882524058484736 }, some { target := 499, numerator := 76417334425796598848028672 }, some { target := 500, numerator := 135267465535318117501108224 }, some { target := 501, numerator := 4391800829068770048737280 }, some { target := 502, numerator := 84322575918120384935755776 }, some { target := 503, numerator := 4391800829068770048737280 }, some { target := 504, numerator := 134389105369504363491360768 }, some { target := 505, numerator := 140537626530200641559592960 }, some { target := 506, numerator := 84322575918120384935755776 }, some { target := 507, numerator := 2152860766409511077891014656 }, some { target := 508, numerator := 137902546032759379530350592 }, some { target := 509, numerator := 76417334425796598848028672 }, some { target := 510, numerator := 134389105369504363491360768 }, some { target := 511, numerator := 4391800829068770048737280 }, some { target := 512, numerator := 137902546032759379530350592 }, some { target := 513, numerator := 4391800829068770048737280 }, some { target := 514, numerator := 134389105369504363491360768 }, some { target := 515, numerator := 140537626530200641559592960 }, some { target := 516, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 107783292605016782357397504 }, some { target := 574, numerator := 1562857742772743344182263808 }, some { target := 575, numerator := 2766437843528764080506535936 }, some { target := 576, numerator := 89819410504180651964497920 }, some { target := 577, numerator := 1724532681680268517718360064 }, some { target := 578, numerator := 89819410504180651964497920 }, some { target := 579, numerator := 2748473961427927950113636352 }, some { target := 580, numerator := 2874221136133780862863933440 }, some { target := 581, numerator := 1724532681680268517718360064 }, some { target := 582, numerator := 44029475029149355592996880384 }, some { target := 583, numerator := 2820329489831272471685234688 }, some { target := 584, numerator := 1562857742772743344182263808 }, some { target := 585, numerator := 2748473961427927950113636352 }, some { target := 586, numerator := 89819410504180651964497920 }, some { target := 587, numerator := 2820329489831272471685234688 }, some { target := 588, numerator := 89819410504180651964497920 }, some { target := 589, numerator := 2748473961427927950113636352 }, some { target := 590, numerator := 2874221136133780862863933440 }, some { target := 591, numerator := 107783292605016782357397504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 107613287411633475129704448 }, some { target := 609, numerator := 1560392667468685389380714496 }, some { target := 610, numerator := 2762074376898592528329080832 }, some { target := 611, numerator := 89677739509694562608087040 }, some { target := 612, numerator := 1721812598586135602075271168 }, some { target := 613, numerator := 89677739509694562608087040 }, some { target := 614, numerator := 2744138828996653615807463424 }, some { target := 615, numerator := 2869687664310226003458785280 }, some { target := 616, numerator := 1721812598586135602075271168 }, some { target := 617, numerator := 43960027907652274590484267008 }, some { target := 618, numerator := 2815881020604409265893933056 }, some { target := 619, numerator := 1560392667468685389380714496 }, some { target := 620, numerator := 2744138828996653615807463424 }, some { target := 621, numerator := 89677739509694562608087040 }, some { target := 622, numerator := 2815881020604409265893933056 }, some { target := 623, numerator := 89677739509694562608087040 }, some { target := 624, numerator := 2744138828996653615807463424 }, some { target := 625, numerator := 2869687664310226003458785280 }, some { target := 626, numerator := 107613287411633475129704448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 5270160994882524058484736 }, some { target := 670, numerator := 76417334425796598848028672 }, some { target := 671, numerator := 135267465535318117501108224 }, some { target := 672, numerator := 4391800829068770048737280 }, some { target := 673, numerator := 84322575918120384935755776 }, some { target := 674, numerator := 4391800829068770048737280 }, some { target := 675, numerator := 134389105369504363491360768 }, some { target := 676, numerator := 140537626530200641559592960 }, some { target := 677, numerator := 84322575918120384935755776 }, some { target := 678, numerator := 2152860766409511077891014656 }, some { target := 679, numerator := 137902546032759379530350592 }, some { target := 680, numerator := 76417334425796598848028672 }, some { target := 681, numerator := 134389105369504363491360768 }, some { target := 682, numerator := 4391800829068770048737280 }, some { target := 683, numerator := 137902546032759379530350592 }, some { target := 684, numerator := 4391800829068770048737280 }, some { target := 685, numerator := 134389105369504363491360768 }, some { target := 686, numerator := 140537626530200641559592960 }, some { target := 687, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 127673900230863727997485056 }, some { target := 705, numerator := 1851271553347524055963533312 }, some { target := 706, numerator := 3276963439258835685268783104 }, some { target := 707, numerator := 106394916859053106664570880 }, some { target := 708, numerator := 2042782403693819647959760896 }, some { target := 709, numerator := 106394916859053106664570880 }, some { target := 710, numerator := 3255684455887025063935868928 }, some { target := 711, numerator := 3404637339489699413266268160 }, some { target := 712, numerator := 2042782403693819647959760896 }, some { target := 713, numerator := 52154788244307832886972645376 }, some { target := 714, numerator := 3340800389374267549267525632 }, some { target := 715, numerator := 1851271553347524055963533312 }, some { target := 716, numerator := 3255684455887025063935868928 }, some { target := 717, numerator := 106394916859053106664570880 }, some { target := 718, numerator := 3340800389374267549267525632 }, some { target := 719, numerator := 106394916859053106664570880 }, some { target := 720, numerator := 3255684455887025063935868928 }, some { target := 721, numerator := 3404637339489699413266268160 }, some { target := 722, numerator := 127673900230863727997485056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 5270160994882524058484736 }, some { target := 740, numerator := 76417334425796598848028672 }, some { target := 741, numerator := 135267465535318117501108224 }, some { target := 742, numerator := 4391800829068770048737280 }, some { target := 743, numerator := 84322575918120384935755776 }, some { target := 744, numerator := 4391800829068770048737280 }, some { target := 745, numerator := 134389105369504363491360768 }, some { target := 746, numerator := 140537626530200641559592960 }, some { target := 747, numerator := 84322575918120384935755776 }, some { target := 748, numerator := 2152860766409511077891014656 }, some { target := 749, numerator := 137902546032759379530350592 }, some { target := 750, numerator := 76417334425796598848028672 }, some { target := 751, numerator := 134389105369504363491360768 }, some { target := 752, numerator := 4391800829068770048737280 }, some { target := 753, numerator := 137902546032759379530350592 }, some { target := 754, numerator := 4391800829068770048737280 }, some { target := 755, numerator := 134389105369504363491360768 }, some { target := 756, numerator := 140537626530200641559592960 }, some { target := 757, numerator := 5270160994882524058484736 }]

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

end Slot14

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent1
