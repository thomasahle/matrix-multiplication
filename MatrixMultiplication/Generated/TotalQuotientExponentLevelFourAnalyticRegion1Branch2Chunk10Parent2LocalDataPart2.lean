import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 6, #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

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
  [some { target := 26, numerator := 4391800829068770048737280 }, some { target := 27, numerator := 73782253928355336818786304 }, some { target := 28, numerator := 159861550178103229774036992 }, some { target := 29, numerator := 5270160994882524058484736 }, some { target := 30, numerator := 84322575918120384935755776 }, some { target := 31, numerator := 6148521160696278068232192 }, some { target := 32, numerator := 159861550178103229774036992 }, some { target := 33, numerator := 159861550178103229774036992 }, some { target := 34, numerator := 84322575918120384935755776 }, some { target := 35, numerator := 1972796932417691505892786176 }, some { target := 36, numerator := 158104829846475721754542080 }, some { target := 37, numerator := 73782253928355336818786304 }, some { target := 38, numerator := 159861550178103229774036992 }, some { target := 39, numerator := 6148521160696278068232192 }, some { target := 40, numerator := 158104829846475721754542080 }, some { target := 41, numerator := 6148521160696278068232192 }, some { target := 42, numerator := 159861550178103229774036992 }, some { target := 43, numerator := 159861550178103229774036992 }, some { target := 44, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 107669955809427910872268800 }, some { target := 62, numerator := 1808855257598388902654115840 }, some { target := 63, numerator := 3919186391463175955750584320 }, some { target := 64, numerator := 129203946971313493046722560 }, some { target := 65, numerator := 2067263151541015888747560960 }, some { target := 66, numerator := 150737938133199075221176320 }, some { target := 67, numerator := 3919186391463175955750584320 }, some { target := 68, numerator := 3919186391463175955750584320 }, some { target := 69, numerator := 2067263151541015888747560960 }, some { target := 70, numerator := 48365344149595017563823144960 }, some { target := 71, numerator := 3876118409139404791401676800 }, some { target := 72, numerator := 1808855257598388902654115840 }, some { target := 73, numerator := 3919186391463175955750584320 }, some { target := 74, numerator := 150737938133199075221176320 }, some { target := 75, numerator := 3876118409139404791401676800 }, some { target := 76, numerator := 150737938133199075221176320 }, some { target := 77, numerator := 3919186391463175955750584320 }, some { target := 78, numerator := 3919186391463175955750584320 }, some { target := 79, numerator := 129203946971313493046722560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 96, numerator := 4391800829068770048737280 }, some { target := 97, numerator := 73782253928355336818786304 }, some { target := 98, numerator := 159861550178103229774036992 }, some { target := 99, numerator := 5270160994882524058484736 }, some { target := 100, numerator := 84322575918120384935755776 }, some { target := 101, numerator := 6148521160696278068232192 }, some { target := 102, numerator := 159861550178103229774036992 }, some { target := 103, numerator := 159861550178103229774036992 }, some { target := 104, numerator := 84322575918120384935755776 }, some { target := 105, numerator := 1972796932417691505892786176 }, some { target := 106, numerator := 158104829846475721754542080 }, some { target := 107, numerator := 73782253928355336818786304 }, some { target := 108, numerator := 159861550178103229774036992 }, some { target := 109, numerator := 6148521160696278068232192 }, some { target := 110, numerator := 158104829846475721754542080 }, some { target := 111, numerator := 6148521160696278068232192 }, some { target := 112, numerator := 159861550178103229774036992 }, some { target := 113, numerator := 159861550178103229774036992 }, some { target := 114, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 90244423487638920033730560 }, some { target := 158, numerator := 1516106314592333856566673408 }, some { target := 159, numerator := 3284897014950056689227792384 }, some { target := 160, numerator := 108293308185166704040476672 }, some { target := 161, numerator := 1732692930962667264647626752 }, some { target := 162, numerator := 126342192882694488047222784 }, some { target := 163, numerator := 3284897014950056689227792384 }, some { target := 164, numerator := 3284897014950056689227792384 }, some { target := 165, numerator := 1732692930962667264647626752 }, some { target := 166, numerator := 40537795030647402879151767552 }, some { target := 167, numerator := 3248799245555001121214300160 }, some { target := 168, numerator := 1516106314592333856566673408 }, some { target := 169, numerator := 3284897014950056689227792384 }, some { target := 170, numerator := 126342192882694488047222784 }, some { target := 171, numerator := 3248799245555001121214300160 }, some { target := 172, numerator := 126342192882694488047222784 }, some { target := 173, numerator := 3284897014950056689227792384 }, some { target := 174, numerator := 3284897014950056689227792384 }, some { target := 175, numerator := 108293308185166704040476672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 192, numerator := 88686042548291937113210880 }, some { target := 193, numerator := 1489925514811304543501942784 }, some { target := 194, numerator := 3228171948757826510920876032 }, some { target := 195, numerator := 106423251057950324535853056 }, some { target := 196, numerator := 1702772016927205192573648896 }, some { target := 197, numerator := 124160459567608711958495232 }, some { target := 198, numerator := 3228171948757826510920876032 }, some { target := 199, numerator := 3228171948757826510920876032 }, some { target := 200, numerator := 1702772016927205192573648896 }, some { target := 201, numerator := 39837770312692738151254327296 }, some { target := 202, numerator := 3192697531738509736075591680 }, some { target := 203, numerator := 1489925514811304543501942784 }, some { target := 204, numerator := 3228171948757826510920876032 }, some { target := 205, numerator := 124160459567608711958495232 }, some { target := 206, numerator := 3192697531738509736075591680 }, some { target := 207, numerator := 124160459567608711958495232 }, some { target := 208, numerator := 3228171948757826510920876032 }, some { target := 209, numerator := 3228171948757826510920876032 }, some { target := 210, numerator := 106423251057950324535853056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 4391800829068770048737280 }, some { target := 268, numerator := 73782253928355336818786304 }, some { target := 269, numerator := 159861550178103229774036992 }, some { target := 270, numerator := 5270160994882524058484736 }, some { target := 271, numerator := 84322575918120384935755776 }, some { target := 272, numerator := 6148521160696278068232192 }, some { target := 273, numerator := 159861550178103229774036992 }, some { target := 274, numerator := 159861550178103229774036992 }, some { target := 275, numerator := 84322575918120384935755776 }, some { target := 276, numerator := 1972796932417691505892786176 }, some { target := 277, numerator := 158104829846475721754542080 }, some { target := 278, numerator := 73782253928355336818786304 }, some { target := 279, numerator := 159861550178103229774036992 }, some { target := 280, numerator := 6148521160696278068232192 }, some { target := 281, numerator := 158104829846475721754542080 }, some { target := 282, numerator := 6148521160696278068232192 }, some { target := 283, numerator := 159861550178103229774036992 }, some { target := 284, numerator := 159861550178103229774036992 }, some { target := 285, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 373, numerator := 88827713542778026469621760 }, some { target := 374, numerator := 1492305587518670844689645568 }, some { target := 375, numerator := 3233328772957120163494232064 }, some { target := 376, numerator := 106593256251333631763546112 }, some { target := 377, numerator := 1705492100021338108216737792 }, some { target := 378, numerator := 124358798959889237057470464 }, some { target := 379, numerator := 3233328772957120163494232064 }, some { target := 380, numerator := 3233328772957120163494232064 }, some { target := 381, numerator := 1705492100021338108216737792 }, some { target := 382, numerator := 39901408923415889490154094592 }, some { target := 383, numerator := 3197797687540008952906383360 }, some { target := 384, numerator := 1492305587518670844689645568 }, some { target := 385, numerator := 3233328772957120163494232064 }, some { target := 386, numerator := 124358798959889237057470464 }, some { target := 387, numerator := 3197797687540008952906383360 }, some { target := 388, numerator := 124358798959889237057470464 }, some { target := 389, numerator := 3233328772957120163494232064 }, some { target := 390, numerator := 3233328772957120163494232064 }, some { target := 391, numerator := 106593256251333631763546112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 408, numerator := 79619098901182218302914560 }, some { target := 409, numerator := 1337600861539861267488964608 }, some { target := 410, numerator := 2898135200003032746226089984 }, some { target := 411, numerator := 95542918681418661963497472 }, some { target := 412, numerator := 1528686698902698591415959552 }, some { target := 413, numerator := 111466738461655105624080384 }, some { target := 414, numerator := 2898135200003032746226089984 }, some { target := 415, numerator := 2898135200003032746226089984 }, some { target := 416, numerator := 1528686698902698591415959552 }, some { target := 417, numerator := 35764899226411052461669220352 }, some { target := 418, numerator := 2866287560442559858904924160 }, some { target := 419, numerator := 1337600861539861267488964608 }, some { target := 420, numerator := 2898135200003032746226089984 }, some { target := 421, numerator := 111466738461655105624080384 }, some { target := 422, numerator := 2866287560442559858904924160 }, some { target := 423, numerator := 111466738461655105624080384 }, some { target := 424, numerator := 2898135200003032746226089984 }, some { target := 425, numerator := 2898135200003032746226089984 }, some { target := 426, numerator := 95542918681418661963497472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 483, numerator := 107669955809427910872268800 }, some { target := 484, numerator := 1808855257598388902654115840 }, some { target := 485, numerator := 3919186391463175955750584320 }, some { target := 486, numerator := 129203946971313493046722560 }, some { target := 487, numerator := 2067263151541015888747560960 }, some { target := 488, numerator := 150737938133199075221176320 }, some { target := 489, numerator := 3919186391463175955750584320 }, some { target := 490, numerator := 3919186391463175955750584320 }, some { target := 491, numerator := 2067263151541015888747560960 }, some { target := 492, numerator := 48365344149595017563823144960 }, some { target := 493, numerator := 3876118409139404791401676800 }, some { target := 494, numerator := 1808855257598388902654115840 }, some { target := 495, numerator := 3919186391463175955750584320 }, some { target := 496, numerator := 150737938133199075221176320 }, some { target := 497, numerator := 3876118409139404791401676800 }, some { target := 498, numerator := 150737938133199075221176320 }, some { target := 499, numerator := 3919186391463175955750584320 }, some { target := 500, numerator := 3919186391463175955750584320 }, some { target := 501, numerator := 129203946971313493046722560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 623, numerator := 4391800829068770048737280 }, some { target := 624, numerator := 73782253928355336818786304 }, some { target := 625, numerator := 159861550178103229774036992 }, some { target := 626, numerator := 5270160994882524058484736 }, some { target := 627, numerator := 84322575918120384935755776 }, some { target := 628, numerator := 6148521160696278068232192 }, some { target := 629, numerator := 159861550178103229774036992 }, some { target := 630, numerator := 159861550178103229774036992 }, some { target := 631, numerator := 84322575918120384935755776 }, some { target := 632, numerator := 1972796932417691505892786176 }, some { target := 633, numerator := 158104829846475721754542080 }, some { target := 634, numerator := 73782253928355336818786304 }, some { target := 635, numerator := 159861550178103229774036992 }, some { target := 636, numerator := 6148521160696278068232192 }, some { target := 637, numerator := 158104829846475721754542080 }, some { target := 638, numerator := 6148521160696278068232192 }, some { target := 639, numerator := 159861550178103229774036992 }, some { target := 640, numerator := 159861550178103229774036992 }, some { target := 641, numerator := 5270160994882524058484736 }]

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

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 3, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

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
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 356, numerator := 20339123827290455933548756992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 617, numerator := 197006239888212100913534337024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 777, numerator := 20339123827290455933548756992 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 453, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 263, numerator := 105897332908669339322516766720 }, some { target := 265, numerator := 105897332908669339322516766720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 8866692071831766893146335608832 }, some { target := 340, numerator := 8866692071831766893146335608832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 8866695280679792003070258315264 }, some { target := 601, numerator := 8866695280679792003070258315264 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 105894124060644229398594060288 }, some { target := 775, numerator := 105894124060644229398594060288 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 6919, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 131, numerator := 75195442909161445255062487040 }, some { target := 134, numerator := 258132807529950475135108513792 }, some { target := 136, numerator := 75195442909161445255062487040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 7884106568995376655957030338560 }, some { target := 230, numerator := 27064759309664887388042153689088 }, some { target := 232, numerator := 7884106568995376655957030338560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 84982788658525326481324769280000 }, some { target := 305, numerator := 291731054163082775740802924544000 }, some { target := 307, numerator := 84982788658525326481324769280000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 7884112583187403302477485834240 }, some { target := 592, numerator := 27064779955334529070076476260352 }, some { target := 594, numerator := 7884112583187403302477485834240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 75195442909161445255062487040 }, some { target := 766, numerator := 258132807529950475135108513792 }, some { target := 768, numerator := 75195442909161445255062487040 }]

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

end Slot7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent2
