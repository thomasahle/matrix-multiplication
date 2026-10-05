import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 3, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 257, numerator := 18643902874369359303671808 }, some { target := 258, numerator := 372878057487387186073436160 }, some { target := 259, numerator := 19309756548453979278802944 }, some { target := 260, numerator := 346909764198087007043321856 }, some { target := 261, numerator := 519365865786003580602286080 }, some { target := 262, numerator := 18643902874369359303671808 }, some { target := 263, numerator := 520031719460088200577417216 }, some { target := 264, numerator := 520031719460088200577417216 }, some { target := 265, numerator := 372212203813302566098305024 }, some { target := 266, numerator := 19309756548453979278802944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 13883757459636756928266240 }, some { target := 354, numerator := 277675149192735138565324800 }, some { target := 355, numerator := 14379605940338069675704320 }, some { target := 356, numerator := 258337058445383941415239680 }, some { target := 357, numerator := 386761814947023943001702400 }, some { target := 358, numerator := 13883757459636756928266240 }, some { target := 359, numerator := 387257663427725255749140480 }, some { target := 360, numerator := 387257663427725255749140480 }, some { target := 361, numerator := 277179300712033825817886720 }, some { target := 362, numerator := 14379605940338069675704320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 379, numerator := 14677115028758857324167168 }, some { target := 380, numerator := 293542300575177146483343360 }, some { target := 381, numerator := 15201297708357387942887424 }, some { target := 382, numerator := 273099176070834452353253376 }, some { target := 383, numerator := 408862490086853882601799680 }, some { target := 384, numerator := 14677115028758857324167168 }, some { target := 385, numerator := 409386672766452413220519936 }, some { target := 386, numerator := 409386672766452413220519936 }, some { target := 387, numerator := 293018117895578615864623104 }, some { target := 388, numerator := 15201297708357387942887424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 524, numerator := 19040581658930409501622272 }, some { target := 525, numerator := 380811633178608190032445440 }, some { target := 526, numerator := 19720602432463638412394496 }, some { target := 527, numerator := 354290823010812262512328704 }, some { target := 528, numerator := 530416203355918550402334720 }, some { target := 529, numerator := 19040581658930409501622272 }, some { target := 530, numerator := 531096224129451779313106944 }, some { target := 531, numerator := 531096224129451779313106944 }, some { target := 532, numerator := 380131612405074961121673216 }, some { target := 533, numerator := 19720602432463638412394496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 620, numerator := 255064458472755277282148352 }, some { target := 621, numerator := 5101289169455105545642967040 }, some { target := 622, numerator := 264173903418210822899367936 }, some { target := 623, numerator := 4746020816582339266571403264 }, some { target := 624, numerator := 7105367057455325581431275520 }, some { target := 625, numerator := 255064458472755277282148352 }, some { target := 626, numerator := 7114476502400781127048495104 }, some { target := 627, numerator := 7114476502400781127048495104 }, some { target := 628, numerator := 5092179724509650000025747456 }, some { target := 629, numerator := 264173903418210822899367936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 646, numerator := 461337426444501380216389632 }, some { target := 647, numerator := 9226748528890027604327792640 }, some { target := 648, numerator := 477813763103233572366974976 }, some { target := 649, numerator := 8584171399199472110454964224 }, some { target := 650, numerator := 12851542593811109877456568320 }, some { target := 651, numerator := 461337426444501380216389632 }, some { target := 652, numerator := 12868018930469842069607153664 }, some { target := 653, numerator := 12868018930469842069607153664 }, some { target := 654, numerator := 9210272192231295412177207296 }, some { target := 655, numerator := 477813763103233572366974976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 13883757459636756928266240 }, some { target := 696, numerator := 277675149192735138565324800 }, some { target := 697, numerator := 14379605940338069675704320 }, some { target := 698, numerator := 258337058445383941415239680 }, some { target := 699, numerator := 386761814947023943001702400 }, some { target := 700, numerator := 13883757459636756928266240 }, some { target := 701, numerator := 387257663427725255749140480 }, some { target := 702, numerator := 387257663427725255749140480 }, some { target := 703, numerator := 277179300712033825817886720 }, some { target := 704, numerator := 14379605940338069675704320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 721, numerator := 255064458472755277282148352 }, some { target := 722, numerator := 5101289169455105545642967040 }, some { target := 723, numerator := 264173903418210822899367936 }, some { target := 724, numerator := 4746020816582339266571403264 }, some { target := 725, numerator := 7105367057455325581431275520 }, some { target := 726, numerator := 255064458472755277282148352 }, some { target := 727, numerator := 7114476502400781127048495104 }, some { target := 728, numerator := 7114476502400781127048495104 }, some { target := 729, numerator := 5092179724509650000025747456 }, some { target := 730, numerator := 264173903418210822899367936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 735, numerator := 15073793813319907522117632 }, some { target := 736, numerator := 301475876266398150442352640 }, some { target := 737, numerator := 15612143592367047076478976 }, some { target := 738, numerator := 280480234883559707822260224 }, some { target := 739, numerator := 419912827656768852401848320 }, some { target := 740, numerator := 15073793813319907522117632 }, some { target := 741, numerator := 420451177435815991956209664 }, some { target := 742, numerator := 420451177435815991956209664 }, some { target := 743, numerator := 300937526487351010887991296 }, some { target := 744, numerator := 15612143592367047076478976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 836, numerator := 15073793813319907522117632 }, some { target := 837, numerator := 301475876266398150442352640 }, some { target := 838, numerator := 15612143592367047076478976 }, some { target := 839, numerator := 280480234883559707822260224 }, some { target := 840, numerator := 419912827656768852401848320 }, some { target := 841, numerator := 15073793813319907522117632 }, some { target := 842, numerator := 420451177435815991956209664 }, some { target := 843, numerator := 420451177435815991956209664 }, some { target := 844, numerator := 300937526487351010887991296 }, some { target := 845, numerator := 15612143592367047076478976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 862, numerator := 14677115028758857324167168 }, some { target := 863, numerator := 293542300575177146483343360 }, some { target := 864, numerator := 15201297708357387942887424 }, some { target := 865, numerator := 273099176070834452353253376 }, some { target := 866, numerator := 408862490086853882601799680 }, some { target := 867, numerator := 14677115028758857324167168 }, some { target := 868, numerator := 409386672766452413220519936 }, some { target := 869, numerator := 409386672766452413220519936 }, some { target := 870, numerator := 293018117895578615864623104 }, some { target := 871, numerator := 15201297708357387942887424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 911, numerator := 14677115028758857324167168 }, some { target := 912, numerator := 293542300575177146483343360 }, some { target := 913, numerator := 15201297708357387942887424 }, some { target := 914, numerator := 273099176070834452353253376 }, some { target := 915, numerator := 408862490086853882601799680 }, some { target := 916, numerator := 14677115028758857324167168 }, some { target := 917, numerator := 409386672766452413220519936 }, some { target := 918, numerator := 409386672766452413220519936 }, some { target := 919, numerator := 293018117895578615864623104 }, some { target := 920, numerator := 15201297708357387942887424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 937, numerator := 461337426444501380216389632 }, some { target := 938, numerator := 9226748528890027604327792640 }, some { target := 939, numerator := 477813763103233572366974976 }, some { target := 940, numerator := 8584171399199472110454964224 }, some { target := 941, numerator := 12851542593811109877456568320 }, some { target := 942, numerator := 461337426444501380216389632 }, some { target := 943, numerator := 12868018930469842069607153664 }, some { target := 944, numerator := 12868018930469842069607153664 }, some { target := 945, numerator := 9210272192231295412177207296 }, some { target := 946, numerator := 477813763103233572366974976 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 951, numerator := 14677115028758857324167168 }, some { target := 952, numerator := 293542300575177146483343360 }, some { target := 953, numerator := 15201297708357387942887424 }, some { target := 954, numerator := 273099176070834452353253376 }, some { target := 955, numerator := 408862490086853882601799680 }, some { target := 956, numerator := 14677115028758857324167168 }, some { target := 957, numerator := 409386672766452413220519936 }, some { target := 958, numerator := 409386672766452413220519936 }, some { target := 959, numerator := 293018117895578615864623104 }, some { target := 960, numerator := 15201297708357387942887424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 18643902874369359303671808 }, some { target := 983, numerator := 372878057487387186073436160 }, some { target := 984, numerator := 19309756548453979278802944 }, some { target := 985, numerator := 346909764198087007043321856 }, some { target := 986, numerator := 519365865786003580602286080 }, some { target := 987, numerator := 18643902874369359303671808 }, some { target := 988, numerator := 520031719460088200577417216 }, some { target := 989, numerator := 520031719460088200577417216 }, some { target := 990, numerator := 372212203813302566098305024 }, some { target := 991, numerator := 19309756548453979278802944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 996, numerator := 19040581658930409501622272 }, some { target := 997, numerator := 380811633178608190032445440 }, some { target := 998, numerator := 19720602432463638412394496 }, some { target := 999, numerator := 354290823010812262512328704 }, some { target := 1000, numerator := 530416203355918550402334720 }, some { target := 1001, numerator := 19040581658930409501622272 }, some { target := 1002, numerator := 531096224129451779313106944 }, some { target := 1003, numerator := 531096224129451779313106944 }, some { target := 1004, numerator := 380131612405074961121673216 }, some { target := 1005, numerator := 19720602432463638412394496 }]

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
def data : BetaFourLocalSlotData := ⟨1, 1, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 389, numerator := 299813603264428035327131648 }, some { target := 391, numerator := 299813603264428035327131648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 656, numerator := 7350268983256945382213550080 }, some { target := 658, numerator := 7350268983256945382213550080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 731, numerator := 5435330484987372769478967296 }, some { target := 733, numerator := 5435330484987372769478967296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 745, numerator := 6063971911186979940326178816 }, some { target := 747, numerator := 6063971911186979940326178816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 872, numerator := 299813603264428035327131648 }, some { target := 874, numerator := 299813603264428035327131648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 947, numerator := 6054300504630062906928529408 }, some { target := 949, numerator := 6054300504630062906928529408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 6160685976756150274302672896 }, some { target := 963, numerator := 6160685976756150274302672896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 992, numerator := 299813603264428035327131648 }, some { target := 994, numerator := 299813603264428035327131648 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1006, numerator := 7350268983256945382213550080 }, some { target := 1008, numerator := 7350268983256945382213550080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1011, numerator := 299813603264428035327131648 }, some { target := 1013, numerator := 299813603264428035327131648 }]

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
def data : BetaFourLocalSlotData := ⟨2, 0, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 369, #[139552882688, 22870029762560, 0, 235455811420160, 0, 0, 0, 0, 0, 0, 0, 22870029762560, 0, 0, 0, 0, 0, 0, 139552882688], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 127393574284547600796352512 }, some { target := 111, numerator := 145087126268512545351401472 }, some { target := 112, numerator := 113238732697375645152313344 }, some { target := 113, numerator := 1518106760224192242823200768 }, some { target := 114, numerator := 134470995078133578618372096 }, some { target := 115, numerator := 113238732697375645152313344 }, some { target := 116, numerator := 134470995078133578618372096 }, some { target := 117, numerator := 130932284681340589707362304 }, some { target := 118, numerator := 4947117134716598497591689216 }, some { target := 119, numerator := 130932284681340589707362304 }, some { target := 120, numerator := 1518106760224192242823200768 }, some { target := 121, numerator := 4947117134716598497591689216 }, some { target := 122, numerator := 127393574284547600796352512 }, some { target := 123, numerator := 130932284681340589707362304 }, some { target := 124, numerator := 130932284681340589707362304 }, some { target := 125, numerator := 145087126268512545351401472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 20877353296672746754214461440 }, some { target := 207, numerator := 23776985698988406025633136640 }, some { target := 208, numerator := 18557647374820219337079521280 }, some { target := 209, numerator := 248788460118683565487722332160 }, some { target := 210, numerator := 22037206257599010462781931520 }, some { target := 211, numerator := 18557647374820219337079521280 }, some { target := 212, numerator := 22037206257599010462781931520 }, some { target := 213, numerator := 21457279777135878608498196480 }, some { target := 214, numerator := 810737219687458332288661585920 }, some { target := 215, numerator := 21457279777135878608498196480 }, some { target := 216, numerator := 248788460118683565487722332160 }, some { target := 217, numerator := 810737219687458332288661585920 }, some { target := 218, numerator := 20877353296672746754214461440 }, some { target := 219, numerator := 21457279777135878608498196480 }, some { target := 220, numerator := 21457279777135878608498196480 }, some { target := 221, numerator := 23776985698988406025633136640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 214940435662257154598727843840 }, some { target := 303, numerator := 244793273948681759404106711040 }, some { target := 304, numerator := 191058165033117470754424750080 }, some { target := 305, numerator := 2561373524975231092301506805760 }, some { target := 306, numerator := 226881570976826996520879390720 }, some { target := 307, numerator := 191058165033117470754424750080 }, some { target := 308, numerator := 226881570976826996520879390720 }, some { target := 309, numerator := 220911003319542075559803617280 }, some { target := 310, numerator := 8346853584884319503583931269120 }, some { target := 311, numerator := 220911003319542075559803617280 }, some { target := 312, numerator := 2561373524975231092301506805760 }, some { target := 313, numerator := 8346853584884319503583931269120 }, some { target := 314, numerator := 214940435662257154598727843840 }, some { target := 315, numerator := 220911003319542075559803617280 }, some { target := 316, numerator := 220911003319542075559803617280 }, some { target := 317, numerator := 244793273948681759404106711040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 20877353296672746754214461440 }, some { target := 680, numerator := 23776985698988406025633136640 }, some { target := 681, numerator := 18557647374820219337079521280 }, some { target := 682, numerator := 248788460118683565487722332160 }, some { target := 683, numerator := 22037206257599010462781931520 }, some { target := 684, numerator := 18557647374820219337079521280 }, some { target := 685, numerator := 22037206257599010462781931520 }, some { target := 686, numerator := 21457279777135878608498196480 }, some { target := 687, numerator := 810737219687458332288661585920 }, some { target := 688, numerator := 21457279777135878608498196480 }, some { target := 689, numerator := 248788460118683565487722332160 }, some { target := 690, numerator := 810737219687458332288661585920 }, some { target := 691, numerator := 20877353296672746754214461440 }, some { target := 692, numerator := 21457279777135878608498196480 }, some { target := 693, numerator := 21457279777135878608498196480 }, some { target := 694, numerator := 23776985698988406025633136640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 127393574284547600796352512 }, some { target := 967, numerator := 145087126268512545351401472 }, some { target := 968, numerator := 113238732697375645152313344 }, some { target := 969, numerator := 1518106760224192242823200768 }, some { target := 970, numerator := 134470995078133578618372096 }, some { target := 971, numerator := 113238732697375645152313344 }, some { target := 972, numerator := 134470995078133578618372096 }, some { target := 973, numerator := 130932284681340589707362304 }, some { target := 974, numerator := 4947117134716598497591689216 }, some { target := 975, numerator := 130932284681340589707362304 }, some { target := 976, numerator := 1518106760224192242823200768 }, some { target := 977, numerator := 4947117134716598497591689216 }, some { target := 978, numerator := 127393574284547600796352512 }, some { target := 979, numerator := 130932284681340589707362304 }, some { target := 980, numerator := 130932284681340589707362304 }, some { target := 981, numerator := 145087126268512545351401472 }]

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

end Slot3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0
