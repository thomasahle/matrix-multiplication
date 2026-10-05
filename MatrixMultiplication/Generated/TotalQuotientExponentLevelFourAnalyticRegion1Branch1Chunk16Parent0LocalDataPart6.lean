import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 3, #[1924145348608, 38482906972160, 1992864825344, 35802847379456, 53601191854080, 1924145348608, 53669911330816, 53669911330816, 38414187495424, 1992864825344, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 18643902874369359303671808 }, some { target := 15, numerator := 13883757459636756928266240 }, some { target := 16, numerator := 14677115028758857324167168 }, some { target := 17, numerator := 19040581658930409501622272 }, some { target := 18, numerator := 255064458472755277282148352 }, some { target := 19, numerator := 461337426444501380216389632 }, some { target := 20, numerator := 13883757459636756928266240 }, some { target := 21, numerator := 255064458472755277282148352 }, some { target := 22, numerator := 15073793813319907522117632 }, some { target := 23, numerator := 15073793813319907522117632 }, some { target := 24, numerator := 14677115028758857324167168 }, some { target := 25, numerator := 14677115028758857324167168 }, some { target := 26, numerator := 461337426444501380216389632 }, some { target := 27, numerator := 14677115028758857324167168 }, some { target := 28, numerator := 18643902874369359303671808 }, some { target := 29, numerator := 19040581658930409501622272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 40, numerator := 372878057487387186073436160 }, some { target := 41, numerator := 277675149192735138565324800 }, some { target := 42, numerator := 293542300575177146483343360 }, some { target := 43, numerator := 380811633178608190032445440 }, some { target := 44, numerator := 5101289169455105545642967040 }, some { target := 45, numerator := 9226748528890027604327792640 }, some { target := 46, numerator := 277675149192735138565324800 }, some { target := 47, numerator := 5101289169455105545642967040 }, some { target := 48, numerator := 301475876266398150442352640 }, some { target := 49, numerator := 301475876266398150442352640 }, some { target := 50, numerator := 293542300575177146483343360 }, some { target := 51, numerator := 293542300575177146483343360 }, some { target := 52, numerator := 9226748528890027604327792640 }, some { target := 53, numerator := 293542300575177146483343360 }, some { target := 54, numerator := 372878057487387186073436160 }, some { target := 55, numerator := 380811633178608190032445440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 75, numerator := 19309756548453979278802944 }, some { target := 76, numerator := 14379605940338069675704320 }, some { target := 77, numerator := 15201297708357387942887424 }, some { target := 78, numerator := 19720602432463638412394496 }, some { target := 79, numerator := 264173903418210822899367936 }, some { target := 80, numerator := 477813763103233572366974976 }, some { target := 81, numerator := 14379605940338069675704320 }, some { target := 82, numerator := 264173903418210822899367936 }, some { target := 83, numerator := 15612143592367047076478976 }, some { target := 84, numerator := 15612143592367047076478976 }, some { target := 85, numerator := 15201297708357387942887424 }, some { target := 86, numerator := 15201297708357387942887424 }, some { target := 87, numerator := 477813763103233572366974976 }, some { target := 88, numerator := 15201297708357387942887424 }, some { target := 89, numerator := 19309756548453979278802944 }, some { target := 90, numerator := 19720602432463638412394496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 346909764198087007043321856 }, some { target := 137, numerator := 258337058445383941415239680 }, some { target := 138, numerator := 273099176070834452353253376 }, some { target := 139, numerator := 354290823010812262512328704 }, some { target := 140, numerator := 4746020816582339266571403264 }, some { target := 141, numerator := 8584171399199472110454964224 }, some { target := 142, numerator := 258337058445383941415239680 }, some { target := 143, numerator := 4746020816582339266571403264 }, some { target := 144, numerator := 280480234883559707822260224 }, some { target := 145, numerator := 280480234883559707822260224 }, some { target := 146, numerator := 273099176070834452353253376 }, some { target := 147, numerator := 273099176070834452353253376 }, some { target := 148, numerator := 8584171399199472110454964224 }, some { target := 149, numerator := 273099176070834452353253376 }, some { target := 150, numerator := 346909764198087007043321856 }, some { target := 151, numerator := 354290823010812262512328704 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 519365865786003580602286080 }, some { target := 172, numerator := 386761814947023943001702400 }, some { target := 173, numerator := 408862490086853882601799680 }, some { target := 174, numerator := 530416203355918550402334720 }, some { target := 175, numerator := 7105367057455325581431275520 }, some { target := 176, numerator := 12851542593811109877456568320 }, some { target := 177, numerator := 386761814947023943001702400 }, some { target := 178, numerator := 7105367057455325581431275520 }, some { target := 179, numerator := 419912827656768852401848320 }, some { target := 180, numerator := 419912827656768852401848320 }, some { target := 181, numerator := 408862490086853882601799680 }, some { target := 182, numerator := 408862490086853882601799680 }, some { target := 183, numerator := 12851542593811109877456568320 }, some { target := 184, numerator := 408862490086853882601799680 }, some { target := 185, numerator := 519365865786003580602286080 }, some { target := 186, numerator := 530416203355918550402334720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 18643902874369359303671808 }, some { target := 268, numerator := 13883757459636756928266240 }, some { target := 269, numerator := 14677115028758857324167168 }, some { target := 270, numerator := 19040581658930409501622272 }, some { target := 271, numerator := 255064458472755277282148352 }, some { target := 272, numerator := 461337426444501380216389632 }, some { target := 273, numerator := 13883757459636756928266240 }, some { target := 274, numerator := 255064458472755277282148352 }, some { target := 275, numerator := 15073793813319907522117632 }, some { target := 276, numerator := 15073793813319907522117632 }, some { target := 277, numerator := 14677115028758857324167168 }, some { target := 278, numerator := 14677115028758857324167168 }, some { target := 279, numerator := 461337426444501380216389632 }, some { target := 280, numerator := 14677115028758857324167168 }, some { target := 281, numerator := 18643902874369359303671808 }, some { target := 282, numerator := 19040581658930409501622272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 403, numerator := 520031719460088200577417216 }, some { target := 404, numerator := 387257663427725255749140480 }, some { target := 405, numerator := 409386672766452413220519936 }, some { target := 406, numerator := 531096224129451779313106944 }, some { target := 407, numerator := 7114476502400781127048495104 }, some { target := 408, numerator := 12868018930469842069607153664 }, some { target := 409, numerator := 387257663427725255749140480 }, some { target := 410, numerator := 7114476502400781127048495104 }, some { target := 411, numerator := 420451177435815991956209664 }, some { target := 412, numerator := 420451177435815991956209664 }, some { target := 413, numerator := 409386672766452413220519936 }, some { target := 414, numerator := 409386672766452413220519936 }, some { target := 415, numerator := 12868018930469842069607153664 }, some { target := 416, numerator := 409386672766452413220519936 }, some { target := 417, numerator := 520031719460088200577417216 }, some { target := 418, numerator := 531096224129451779313106944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 438, numerator := 520031719460088200577417216 }, some { target := 439, numerator := 387257663427725255749140480 }, some { target := 440, numerator := 409386672766452413220519936 }, some { target := 441, numerator := 531096224129451779313106944 }, some { target := 442, numerator := 7114476502400781127048495104 }, some { target := 443, numerator := 12868018930469842069607153664 }, some { target := 444, numerator := 387257663427725255749140480 }, some { target := 445, numerator := 7114476502400781127048495104 }, some { target := 446, numerator := 420451177435815991956209664 }, some { target := 447, numerator := 420451177435815991956209664 }, some { target := 448, numerator := 409386672766452413220519936 }, some { target := 449, numerator := 409386672766452413220519936 }, some { target := 450, numerator := 12868018930469842069607153664 }, some { target := 451, numerator := 409386672766452413220519936 }, some { target := 452, numerator := 520031719460088200577417216 }, some { target := 453, numerator := 531096224129451779313106944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 534, numerator := 372212203813302566098305024 }, some { target := 535, numerator := 277179300712033825817886720 }, some { target := 536, numerator := 293018117895578615864623104 }, some { target := 537, numerator := 380131612405074961121673216 }, some { target := 538, numerator := 5092179724509650000025747456 }, some { target := 539, numerator := 9210272192231295412177207296 }, some { target := 540, numerator := 277179300712033825817886720 }, some { target := 541, numerator := 5092179724509650000025747456 }, some { target := 542, numerator := 300937526487351010887991296 }, some { target := 543, numerator := 300937526487351010887991296 }, some { target := 544, numerator := 293018117895578615864623104 }, some { target := 545, numerator := 293018117895578615864623104 }, some { target := 546, numerator := 9210272192231295412177207296 }, some { target := 547, numerator := 293018117895578615864623104 }, some { target := 548, numerator := 372212203813302566098305024 }, some { target := 549, numerator := 380131612405074961121673216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 750, numerator := 19309756548453979278802944 }, some { target := 751, numerator := 14379605940338069675704320 }, some { target := 752, numerator := 15201297708357387942887424 }, some { target := 753, numerator := 19720602432463638412394496 }, some { target := 754, numerator := 264173903418210822899367936 }, some { target := 755, numerator := 477813763103233572366974976 }, some { target := 756, numerator := 14379605940338069675704320 }, some { target := 757, numerator := 264173903418210822899367936 }, some { target := 758, numerator := 15612143592367047076478976 }, some { target := 759, numerator := 15612143592367047076478976 }, some { target := 760, numerator := 15201297708357387942887424 }, some { target := 761, numerator := 15201297708357387942887424 }, some { target := 762, numerator := 477813763103233572366974976 }, some { target := 763, numerator := 15201297708357387942887424 }, some { target := 764, numerator := 19309756548453979278802944 }, some { target := 765, numerator := 19720602432463638412394496 }]

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

end Slot25

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0
