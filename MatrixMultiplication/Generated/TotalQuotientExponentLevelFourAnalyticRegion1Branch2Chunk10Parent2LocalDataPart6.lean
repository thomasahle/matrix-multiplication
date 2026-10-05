import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 6, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

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
  [some { target := 131, numerator := 4391800829068770048737280 }, some { target := 132, numerator := 107669955809427910872268800 }, some { target := 133, numerator := 4391800829068770048737280 }, some { target := 134, numerator := 90244423487638920033730560 }, some { target := 135, numerator := 88686042548291937113210880 }, some { target := 136, numerator := 4391800829068770048737280 }, some { target := 137, numerator := 88827713542778026469621760 }, some { target := 138, numerator := 79619098901182218302914560 }, some { target := 139, numerator := 107669955809427910872268800 }, some { target := 140, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 73782253928355336818786304 }, some { target := 228, numerator := 1808855257598388902654115840 }, some { target := 229, numerator := 73782253928355336818786304 }, some { target := 230, numerator := 1516106314592333856566673408 }, some { target := 231, numerator := 1489925514811304543501942784 }, some { target := 232, numerator := 73782253928355336818786304 }, some { target := 233, numerator := 1492305587518670844689645568 }, some { target := 234, numerator := 1337600861539861267488964608 }, some { target := 235, numerator := 1808855257598388902654115840 }, some { target := 236, numerator := 73782253928355336818786304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 253, numerator := 159861550178103229774036992 }, some { target := 254, numerator := 3919186391463175955750584320 }, some { target := 255, numerator := 159861550178103229774036992 }, some { target := 256, numerator := 3284897014950056689227792384 }, some { target := 257, numerator := 3228171948757826510920876032 }, some { target := 258, numerator := 159861550178103229774036992 }, some { target := 259, numerator := 3233328772957120163494232064 }, some { target := 260, numerator := 2898135200003032746226089984 }, some { target := 261, numerator := 3919186391463175955750584320 }, some { target := 262, numerator := 159861550178103229774036992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 5270160994882524058484736 }, some { target := 303, numerator := 129203946971313493046722560 }, some { target := 304, numerator := 5270160994882524058484736 }, some { target := 305, numerator := 108293308185166704040476672 }, some { target := 306, numerator := 106423251057950324535853056 }, some { target := 307, numerator := 5270160994882524058484736 }, some { target := 308, numerator := 106593256251333631763546112 }, some { target := 309, numerator := 95542918681418661963497472 }, some { target := 310, numerator := 129203946971313493046722560 }, some { target := 311, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 328, numerator := 84322575918120384935755776 }, some { target := 329, numerator := 2067263151541015888747560960 }, some { target := 330, numerator := 84322575918120384935755776 }, some { target := 331, numerator := 1732692930962667264647626752 }, some { target := 332, numerator := 1702772016927205192573648896 }, some { target := 333, numerator := 84322575918120384935755776 }, some { target := 334, numerator := 1705492100021338108216737792 }, some { target := 335, numerator := 1528686698902698591415959552 }, some { target := 336, numerator := 2067263151541015888747560960 }, some { target := 337, numerator := 84322575918120384935755776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 342, numerator := 6148521160696278068232192 }, some { target := 343, numerator := 150737938133199075221176320 }, some { target := 344, numerator := 6148521160696278068232192 }, some { target := 345, numerator := 126342192882694488047222784 }, some { target := 346, numerator := 124160459567608711958495232 }, some { target := 347, numerator := 6148521160696278068232192 }, some { target := 348, numerator := 124358798959889237057470464 }, some { target := 349, numerator := 111466738461655105624080384 }, some { target := 350, numerator := 150737938133199075221176320 }, some { target := 351, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 159861550178103229774036992 }, some { target := 444, numerator := 3919186391463175955750584320 }, some { target := 445, numerator := 159861550178103229774036992 }, some { target := 446, numerator := 3284897014950056689227792384 }, some { target := 447, numerator := 3228171948757826510920876032 }, some { target := 448, numerator := 159861550178103229774036992 }, some { target := 449, numerator := 3233328772957120163494232064 }, some { target := 450, numerator := 2898135200003032746226089984 }, some { target := 451, numerator := 3919186391463175955750584320 }, some { target := 452, numerator := 159861550178103229774036992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 159861550178103229774036992 }, some { target := 470, numerator := 3919186391463175955750584320 }, some { target := 471, numerator := 159861550178103229774036992 }, some { target := 472, numerator := 3284897014950056689227792384 }, some { target := 473, numerator := 3228171948757826510920876032 }, some { target := 474, numerator := 159861550178103229774036992 }, some { target := 475, numerator := 3233328772957120163494232064 }, some { target := 476, numerator := 2898135200003032746226089984 }, some { target := 477, numerator := 3919186391463175955750584320 }, some { target := 478, numerator := 159861550178103229774036992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 518, numerator := 84322575918120384935755776 }, some { target := 519, numerator := 2067263151541015888747560960 }, some { target := 520, numerator := 84322575918120384935755776 }, some { target := 521, numerator := 1732692930962667264647626752 }, some { target := 522, numerator := 1702772016927205192573648896 }, some { target := 523, numerator := 84322575918120384935755776 }, some { target := 524, numerator := 1705492100021338108216737792 }, some { target := 525, numerator := 1528686698902698591415959552 }, some { target := 526, numerator := 2067263151541015888747560960 }, some { target := 527, numerator := 84322575918120384935755776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 1972796932417691505892786176 }, some { target := 545, numerator := 48365344149595017563823144960 }, some { target := 546, numerator := 1972796932417691505892786176 }, some { target := 547, numerator := 40537795030647402879151767552 }, some { target := 548, numerator := 39837770312692738151254327296 }, some { target := 549, numerator := 1972796932417691505892786176 }, some { target := 550, numerator := 39901408923415889490154094592 }, some { target := 551, numerator := 35764899226411052461669220352 }, some { target := 552, numerator := 48365344149595017563823144960 }, some { target := 553, numerator := 1972796932417691505892786176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 558, numerator := 158104829846475721754542080 }, some { target := 559, numerator := 3876118409139404791401676800 }, some { target := 560, numerator := 158104829846475721754542080 }, some { target := 561, numerator := 3248799245555001121214300160 }, some { target := 562, numerator := 3192697531738509736075591680 }, some { target := 563, numerator := 158104829846475721754542080 }, some { target := 564, numerator := 3197797687540008952906383360 }, some { target := 565, numerator := 2866287560442559858904924160 }, some { target := 566, numerator := 3876118409139404791401676800 }, some { target := 567, numerator := 158104829846475721754542080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 73782253928355336818786304 }, some { target := 590, numerator := 1808855257598388902654115840 }, some { target := 591, numerator := 73782253928355336818786304 }, some { target := 592, numerator := 1516106314592333856566673408 }, some { target := 593, numerator := 1489925514811304543501942784 }, some { target := 594, numerator := 73782253928355336818786304 }, some { target := 595, numerator := 1492305587518670844689645568 }, some { target := 596, numerator := 1337600861539861267488964608 }, some { target := 597, numerator := 1808855257598388902654115840 }, some { target := 598, numerator := 73782253928355336818786304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 603, numerator := 159861550178103229774036992 }, some { target := 604, numerator := 3919186391463175955750584320 }, some { target := 605, numerator := 159861550178103229774036992 }, some { target := 606, numerator := 3284897014950056689227792384 }, some { target := 607, numerator := 3228171948757826510920876032 }, some { target := 608, numerator := 159861550178103229774036992 }, some { target := 609, numerator := 3233328772957120163494232064 }, some { target := 610, numerator := 2898135200003032746226089984 }, some { target := 611, numerator := 3919186391463175955750584320 }, some { target := 612, numerator := 159861550178103229774036992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 658, numerator := 6148521160696278068232192 }, some { target := 659, numerator := 150737938133199075221176320 }, some { target := 660, numerator := 6148521160696278068232192 }, some { target := 661, numerator := 126342192882694488047222784 }, some { target := 662, numerator := 124160459567608711958495232 }, some { target := 663, numerator := 6148521160696278068232192 }, some { target := 664, numerator := 124358798959889237057470464 }, some { target := 665, numerator := 111466738461655105624080384 }, some { target := 666, numerator := 150737938133199075221176320 }, some { target := 667, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 684, numerator := 158104829846475721754542080 }, some { target := 685, numerator := 3876118409139404791401676800 }, some { target := 686, numerator := 158104829846475721754542080 }, some { target := 687, numerator := 3248799245555001121214300160 }, some { target := 688, numerator := 3192697531738509736075591680 }, some { target := 689, numerator := 158104829846475721754542080 }, some { target := 690, numerator := 3197797687540008952906383360 }, some { target := 691, numerator := 2866287560442559858904924160 }, some { target := 692, numerator := 3876118409139404791401676800 }, some { target := 693, numerator := 158104829846475721754542080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 6148521160696278068232192 }, some { target := 699, numerator := 150737938133199075221176320 }, some { target := 700, numerator := 6148521160696278068232192 }, some { target := 701, numerator := 126342192882694488047222784 }, some { target := 702, numerator := 124160459567608711958495232 }, some { target := 703, numerator := 6148521160696278068232192 }, some { target := 704, numerator := 124358798959889237057470464 }, some { target := 705, numerator := 111466738461655105624080384 }, some { target := 706, numerator := 150737938133199075221176320 }, some { target := 707, numerator := 6148521160696278068232192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 729, numerator := 159861550178103229774036992 }, some { target := 730, numerator := 3919186391463175955750584320 }, some { target := 731, numerator := 159861550178103229774036992 }, some { target := 732, numerator := 3284897014950056689227792384 }, some { target := 733, numerator := 3228171948757826510920876032 }, some { target := 734, numerator := 159861550178103229774036992 }, some { target := 735, numerator := 3233328772957120163494232064 }, some { target := 736, numerator := 2898135200003032746226089984 }, some { target := 737, numerator := 3919186391463175955750584320 }, some { target := 738, numerator := 159861550178103229774036992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 743, numerator := 159861550178103229774036992 }, some { target := 744, numerator := 3919186391463175955750584320 }, some { target := 745, numerator := 159861550178103229774036992 }, some { target := 746, numerator := 3284897014950056689227792384 }, some { target := 747, numerator := 3228171948757826510920876032 }, some { target := 748, numerator := 159861550178103229774036992 }, some { target := 749, numerator := 3233328772957120163494232064 }, some { target := 750, numerator := 2898135200003032746226089984 }, some { target := 751, numerator := 3919186391463175955750584320 }, some { target := 752, numerator := 159861550178103229774036992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 5270160994882524058484736 }, some { target := 764, numerator := 129203946971313493046722560 }, some { target := 765, numerator := 5270160994882524058484736 }, some { target := 766, numerator := 108293308185166704040476672 }, some { target := 767, numerator := 106423251057950324535853056 }, some { target := 768, numerator := 5270160994882524058484736 }, some { target := 769, numerator := 106593256251333631763546112 }, some { target := 770, numerator := 95542918681418661963497472 }, some { target := 771, numerator := 129203946971313493046722560 }, some { target := 772, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 234, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 80, numerator := 2864040304292524266488856576 }, some { target := 81, numerator := 2804372797953096677603672064 }, some { target := 82, numerator := 2207697734558820788751826944 }, some { target := 83, numerator := 69393309872754285873469587456 }, some { target := 84, numerator := 2207697734558820788751826944 }, some { target := 85, numerator := 2207697734558820788751826944 }, some { target := 86, numerator := 2267365240898248377637011456 }, some { target := 87, numerator := 2267365240898248377637011456 }, some { target := 88, numerator := 38366206576251939653173641216 }, some { target := 89, numerator := 2088362721879965610981457920 }, some { target := 90, numerator := 69393309872754285873469587456 }, some { target := 91, numerator := 38366206576251939653173641216 }, some { target := 92, numerator := 2864040304292524266488856576 }, some { target := 93, numerator := 2207697734558820788751826944 }, some { target := 94, numerator := 2088362721879965610981457920 }, some { target := 95, numerator := 2804372797953096677603672064 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 105765198142999594855909294080 }, some { target := 177, numerator := 103561756515020436629744517120 }, some { target := 178, numerator := 81527340235228854368096747520 }, some { target := 179, numerator := 2562602613339761017029635604480 }, some { target := 180, numerator := 81527340235228854368096747520 }, some { target := 181, numerator := 81527340235228854368096747520 }, some { target := 182, numerator := 83730781863208012594261524480 }, some { target := 183, numerator := 83730781863208012594261524480 }, some { target := 184, numerator := 1416812966790598739423951585280 }, some { target := 185, numerator := 77120456979270537915767193600 }, some { target := 186, numerator := 2562602613339761017029635604480 }, some { target := 187, numerator := 1416812966790598739423951585280 }, some { target := 188, numerator := 105765198142999594855909294080 }, some { target := 189, numerator := 81527340235228854368096747520 }, some { target := 190, numerator := 77120456979270537915767193600 }, some { target := 191, numerator := 103561756515020436629744517120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 105765172243770915367698825216 }, some { target := 287, numerator := 103561731155359021297538433024 }, some { target := 288, numerator := 81527320271240080595934511104 }, some { target := 289, numerator := 2562601985823032803596536119296 }, some { target := 290, numerator := 81527320271240080595934511104 }, some { target := 291, numerator := 81527320271240080595934511104 }, some { target := 292, numerator := 83730761359651974666094903296 }, some { target := 293, numerator := 83730761359651974666094903296 }, some { target := 294, numerator := 1416812619848847887113132179456 }, some { target := 295, numerator := 77120438094416292455613726720 }, some { target := 296, numerator := 2562601985823032803596536119296 }, some { target := 297, numerator := 1416812619848847887113132179456 }, some { target := 298, numerator := 105765172243770915367698825216 }, some { target := 299, numerator := 81527320271240080595934511104 }, some { target := 300, numerator := 77120438094416292455613726720 }, some { target := 301, numerator := 103561731155359021297538433024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 2864066203521203754699325440 }, some { target := 574, numerator := 2804398157614512009809756160 }, some { target := 575, numerator := 2207717698547594560914063360 }, some { target := 576, numerator := 69393937389482499306569072640 }, some { target := 577, numerator := 2207717698547594560914063360 }, some { target := 578, numerator := 2207717698547594560914063360 }, some { target := 579, numerator := 2267385744454286305803632640 }, some { target := 580, numerator := 2267385744454286305803632640 }, some { target := 581, numerator := 38366553518002791963993047040 }, some { target := 582, numerator := 2088381606734211071134924800 }, some { target := 583, numerator := 69393937389482499306569072640 }, some { target := 584, numerator := 38366553518002791963993047040 }, some { target := 585, numerator := 2864066203521203754699325440 }, some { target := 586, numerator := 2207717698547594560914063360 }, some { target := 587, numerator := 2088381606734211071134924800 }, some { target := 588, numerator := 2804398157614512009809756160 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 1385, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 26, numerator := 28513860303958507834237255680 }, some { target := 27, numerator := 760369608105560208912993484800 }, some { target := 28, numerator := 727103437750941949773050019840 }, some { target := 29, numerator := 23761550253298756528531046400 }, some { target := 30, numerator := 746112677953580954995874856960 }, some { target := 31, numerator := 23761550253298756528531046400 }, some { target := 32, numerator := 727103437750941949773050019840 }, some { target := 33, numerator := 413450974407398363596440207360 }, some { target := 34, numerator := 746112677953580954995874856960 }, some { target := 35, numerator := 11647911934167050450285918945280 }, some { target := 36, numerator := 456221764863336125347796090880 }, some { target := 37, numerator := 760369608105560208912993484800 }, some { target := 38, numerator := 727103437750941949773050019840 }, some { target := 39, numerator := 23761550253298756528531046400 }, some { target := 40, numerator := 456221764863336125347796090880 }, some { target := 41, numerator := 23761550253298756528531046400 }, some { target := 42, numerator := 731855747801601701078756229120 }, some { target := 43, numerator := 413450974407398363596440207360 }, some { target := 44, numerator := 28513860303958507834237255680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 103711056368044079400458649600 }, some { target := 158, numerator := 2765628169814508784012230656000 }, some { target := 159, numerator := 2644631937385124024711695564800 }, some { target := 160, numerator := 86425880306703399500382208000 }, some { target := 161, numerator := 2713772641630486744312001331200 }, some { target := 162, numerator := 86425880306703399500382208000 }, some { target := 163, numerator := 2644631937385124024711695564800 }, some { target := 164, numerator := 1503810317336639151306650419200 }, some { target := 165, numerator := 2713772641630486744312001331200 }, some { target := 166, numerator := 42365966526346006435087358361600 }, some { target := 167, numerator := 1659376901888705270407338393600 }, some { target := 168, numerator := 2765628169814508784012230656000 }, some { target := 169, numerator := 2644631937385124024711695564800 }, some { target := 170, numerator := 86425880306703399500382208000 }, some { target := 171, numerator := 1659376901888705270407338393600 }, some { target := 172, numerator := 86425880306703399500382208000 }, some { target := 173, numerator := 2661917113446464704611772006400 }, some { target := 174, numerator := 1503810317336639151306650419200 }, some { target := 175, numerator := 103711056368044079400458649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 28513860303958507834237255680 }, some { target := 268, numerator := 760369608105560208912993484800 }, some { target := 269, numerator := 727103437750941949773050019840 }, some { target := 270, numerator := 23761550253298756528531046400 }, some { target := 271, numerator := 746112677953580954995874856960 }, some { target := 272, numerator := 23761550253298756528531046400 }, some { target := 273, numerator := 727103437750941949773050019840 }, some { target := 274, numerator := 413450974407398363596440207360 }, some { target := 275, numerator := 746112677953580954995874856960 }, some { target := 276, numerator := 11647911934167050450285918945280 }, some { target := 277, numerator := 456221764863336125347796090880 }, some { target := 278, numerator := 760369608105560208912993484800 }, some { target := 279, numerator := 727103437750941949773050019840 }, some { target := 280, numerator := 23761550253298756528531046400 }, some { target := 281, numerator := 456221764863336125347796090880 }, some { target := 282, numerator := 23761550253298756528531046400 }, some { target := 283, numerator := 731855747801601701078756229120 }, some { target := 284, numerator := 413450974407398363596440207360 }, some { target := 285, numerator := 28513860303958507834237255680 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 387, #[140737521909760, 0, 140737454800896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 130999233046084777170645811200 }, some { target := 11, numerator := 134742068275972913661235691520 }, some { target := 12, numerator := 130999233046084777170645811200 }, some { target := 13, numerator := 116027892126532231208286289920 }, some { target := 14, numerator := 5430853918567686047845916344320 }, some { target := 15, numerator := 1478419915805813913783002726400 }, some { target := 16, numerator := 134742068275972913661235691520 }, some { target := 17, numerator := 5430853918567686047845916344320 }, some { target := 18, numerator := 130999233046084777170645811200 }, some { target := 19, numerator := 130999233046084777170645811200 }, some { target := 20, numerator := 112285056896644094717696409600 }, some { target := 21, numerator := 130999233046084777170645811200 }, some { target := 22, numerator := 1478419915805813913783002726400 }, some { target := 23, numerator := 112285056896644094717696409600 }, some { target := 24, numerator := 130999233046084777170645811200 }, some { target := 25, numerator := 116027892126532231208286289920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 130999170580797657571676651520 }, some { target := 142, numerator := 134742004025963304930867412992 }, some { target := 143, numerator := 130999170580797657571676651520 }, some { target := 144, numerator := 116027836800135068134913605632 }, some { target := 145, numerator := 5430851328935354318185794895872 }, some { target := 146, numerator := 1478419210840430706880350781440 }, some { target := 147, numerator := 134742004025963304930867412992 }, some { target := 148, numerator := 5430851328935354318185794895872 }, some { target := 149, numerator := 130999170580797657571676651520 }, some { target := 150, numerator := 130999170580797657571676651520 }, some { target := 151, numerator := 112285003354969420775722844160 }, some { target := 152, numerator := 130999170580797657571676651520 }, some { target := 153, numerator := 1478419210840430706880350781440 }, some { target := 154, numerator := 112285003354969420775722844160 }, some { target := 155, numerator := 130999170580797657571676651520 }, some { target := 156, numerator := 116027836800135068134913605632 }]

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

end Slot27

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent2
