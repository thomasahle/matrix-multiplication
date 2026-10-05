import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 97, #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 5, numerator := 121047825458300583947072962560 }, some { target := 7, numerator := 1172478084242101483505786552320 }, some { target := 12, numerator := 121047825458300583947072962560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 415536019499123573957263884288 }, some { target := 96, numerator := 4024912254567988295859370459136 }, some { target := 101, numerator := 415536019499123573957263884288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 121047825458300583947072962560 }, some { target := 218, numerator := 1172478084242101483505786552320 }, some { target := 223, numerator := 121047825458300583947072962560 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 4, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 39614081257132168796771975168 }, some { target := 2, numerator := 39614081257132168796771975168 }, some { target := 3, numerator := 39614081257132168796771975168 }, some { target := 4, numerator := 39614081257132168796771975168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 39614081257132168796771975168 }, some { target := 91, numerator := 39614081257132168796771975168 }, some { target := 92, numerator := 39614081257132168796771975168 }, some { target := 93, numerator := 39614081257132168796771975168 }]

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

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 156, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 71, numerator := 22100675139829939600097280 }, some { target := 72, numerator := 589351337062131722669260800 }, some { target := 73, numerator := 563567216065663459802480640 }, some { target := 74, numerator := 18417229283191616333414400 }, some { target := 75, numerator := 578300999492216752869212160 }, some { target := 76, numerator := 18417229283191616333414400 }, some { target := 77, numerator := 563567216065663459802480640 }, some { target := 78, numerator := 320459789527534124201410560 }, some { target := 79, numerator := 578300999492216752869212160 }, some { target := 80, numerator := 9028125794620530326639738880 }, some { target := 81, numerator := 353610802237279033601556480 }, some { target := 82, numerator := 589351337062131722669260800 }, some { target := 83, numerator := 563567216065663459802480640 }, some { target := 84, numerator := 18417229283191616333414400 }, some { target := 85, numerator := 353610802237279033601556480 }, some { target := 86, numerator := 18417229283191616333414400 }, some { target := 87, numerator := 567250661922301783069163520 }, some { target := 88, numerator := 320459789527534124201410560 }, some { target := 89, numerator := 22100675139829939600097280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 371291342349142985281634304 }, some { target := 147, numerator := 9901102462643812940843581440 }, some { target := 148, numerator := 9467929229903146124681674752 }, some { target := 149, numerator := 309409451957619154401361920 }, some { target := 150, numerator := 9715456791469241448202764288 }, some { target := 151, numerator := 309409451957619154401361920 }, some { target := 152, numerator := 9467929229903146124681674752 }, some { target := 153, numerator := 5383724464062573286583697408 }, some { target := 154, numerator := 9715456791469241448202764288 }, some { target := 155, numerator := 151672513349624909487547613184 }, some { target := 156, numerator := 5940661477586287764506148864 }, some { target := 157, numerator := 9901102462643812940843581440 }, some { target := 158, numerator := 9467929229903146124681674752 }, some { target := 159, numerator := 309409451957619154401361920 }, some { target := 160, numerator := 5940661477586287764506148864 }, some { target := 161, numerator := 309409451957619154401361920 }, some { target := 162, numerator := 9529811120294669955561947136 }, some { target := 163, numerator := 5383724464062573286583697408 }, some { target := 164, numerator := 371291342349142985281634304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 804464575089809801443540992 }, some { target := 182, numerator := 21452388669061594705161093120 }, some { target := 183, numerator := 20513846664790149936810295296 }, some { target := 184, numerator := 670387145908174834536284160 }, some { target := 185, numerator := 21050156381516689804439322624 }, some { target := 186, numerator := 670387145908174834536284160 }, some { target := 187, numerator := 20513846664790149936810295296 }, some { target := 188, numerator := 11664736338802242120931344384 }, some { target := 189, numerator := 21050156381516689804439322624 }, some { target := 190, numerator := 328623778924187303889686495232 }, some { target := 191, numerator := 12871433201436956823096655872 }, some { target := 192, numerator := 21452388669061594705161093120 }, some { target := 193, numerator := 20513846664790149936810295296 }, some { target := 194, numerator := 670387145908174834536284160 }, some { target := 195, numerator := 12871433201436956823096655872 }, some { target := 196, numerator := 670387145908174834536284160 }, some { target := 197, numerator := 20647924093971784903717552128 }, some { target := 198, numerator := 11664736338802242120931344384 }, some { target := 199, numerator := 804464575089809801443540992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 26520810167795927520116736 }, some { target := 243, numerator := 707221604474558067203112960 }, some { target := 244, numerator := 676280659278796151762976768 }, some { target := 245, numerator := 22100675139829939600097280 }, some { target := 246, numerator := 693961199390660103443054592 }, some { target := 247, numerator := 22100675139829939600097280 }, some { target := 248, numerator := 676280659278796151762976768 }, some { target := 249, numerator := 384551747433040949041692672 }, some { target := 250, numerator := 693961199390660103443054592 }, some { target := 251, numerator := 10833750953544636391967686656 }, some { target := 252, numerator := 424332962684734840321867776 }, some { target := 253, numerator := 707221604474558067203112960 }, some { target := 254, numerator := 676280659278796151762976768 }, some { target := 255, numerator := 22100675139829939600097280 }, some { target := 256, numerator := 424332962684734840321867776 }, some { target := 257, numerator := 22100675139829939600097280 }, some { target := 258, numerator := 680700794306762139682996224 }, some { target := 259, numerator := 384551747433040949041692672 }, some { target := 260, numerator := 26520810167795927520116736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 277, numerator := 424332962684734840321867776 }, some { target := 278, numerator := 11315545671592929075249807360 }, some { target := 279, numerator := 10820490548460738428207628288 }, some { target := 280, numerator := 353610802237279033601556480 }, some { target := 281, numerator := 11103379190250561655088873472 }, some { target := 282, numerator := 353610802237279033601556480 }, some { target := 283, numerator := 10820490548460738428207628288 }, some { target := 284, numerator := 6152827958928655184667082752 }, some { target := 285, numerator := 11103379190250561655088873472 }, some { target := 286, numerator := 173340015256714182271482986496 }, some { target := 287, numerator := 6789327402955757445149884416 }, some { target := 288, numerator := 11315545671592929075249807360 }, some { target := 289, numerator := 10820490548460738428207628288 }, some { target := 290, numerator := 353610802237279033601556480 }, some { target := 291, numerator := 6789327402955757445149884416 }, some { target := 292, numerator := 353610802237279033601556480 }, some { target := 293, numerator := 10891212708908194234927939584 }, some { target := 294, numerator := 6152827958928655184667082752 }, some { target := 295, numerator := 424332962684734840321867776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 312, numerator := 30940945195761915440136192 }, some { target := 313, numerator := 825091871886984411736965120 }, some { target := 314, numerator := 788994102491928843723472896 }, some { target := 315, numerator := 25784120996468262866780160 }, some { target := 316, numerator := 809621399289103454016897024 }, some { target := 317, numerator := 25784120996468262866780160 }, some { target := 318, numerator := 788994102491928843723472896 }, some { target := 319, numerator := 448643705338547773881974784 }, some { target := 320, numerator := 809621399289103454016897024 }, some { target := 321, numerator := 12639376112468742457295634432 }, some { target := 322, numerator := 495055123132190647042179072 }, some { target := 323, numerator := 825091871886984411736965120 }, some { target := 324, numerator := 788994102491928843723472896 }, some { target := 325, numerator := 25784120996468262866780160 }, some { target := 326, numerator := 495055123132190647042179072 }, some { target := 327, numerator := 25784120996468262866780160 }, some { target := 328, numerator := 794150926691222496296828928 }, some { target := 329, numerator := 448643705338547773881974784 }, some { target := 330, numerator := 30940945195761915440136192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 413, numerator := 804464575089809801443540992 }, some { target := 414, numerator := 21452388669061594705161093120 }, some { target := 415, numerator := 20513846664790149936810295296 }, some { target := 416, numerator := 670387145908174834536284160 }, some { target := 417, numerator := 21050156381516689804439322624 }, some { target := 418, numerator := 670387145908174834536284160 }, some { target := 419, numerator := 20513846664790149936810295296 }, some { target := 420, numerator := 11664736338802242120931344384 }, some { target := 421, numerator := 21050156381516689804439322624 }, some { target := 422, numerator := 328623778924187303889686495232 }, some { target := 423, numerator := 12871433201436956823096655872 }, some { target := 424, numerator := 21452388669061594705161093120 }, some { target := 425, numerator := 20513846664790149936810295296 }, some { target := 426, numerator := 670387145908174834536284160 }, some { target := 427, numerator := 12871433201436956823096655872 }, some { target := 428, numerator := 670387145908174834536284160 }, some { target := 429, numerator := 20647924093971784903717552128 }, some { target := 430, numerator := 11664736338802242120931344384 }, some { target := 431, numerator := 804464575089809801443540992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 448, numerator := 804464575089809801443540992 }, some { target := 449, numerator := 21452388669061594705161093120 }, some { target := 450, numerator := 20513846664790149936810295296 }, some { target := 451, numerator := 670387145908174834536284160 }, some { target := 452, numerator := 21050156381516689804439322624 }, some { target := 453, numerator := 670387145908174834536284160 }, some { target := 454, numerator := 20513846664790149936810295296 }, some { target := 455, numerator := 11664736338802242120931344384 }, some { target := 456, numerator := 21050156381516689804439322624 }, some { target := 457, numerator := 328623778924187303889686495232 }, some { target := 458, numerator := 12871433201436956823096655872 }, some { target := 459, numerator := 21452388669061594705161093120 }, some { target := 460, numerator := 20513846664790149936810295296 }, some { target := 461, numerator := 670387145908174834536284160 }, some { target := 462, numerator := 12871433201436956823096655872 }, some { target := 463, numerator := 670387145908174834536284160 }, some { target := 464, numerator := 20647924093971784903717552128 }, some { target := 465, numerator := 11664736338802242120931344384 }, some { target := 466, numerator := 804464575089809801443540992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 509, numerator := 424332962684734840321867776 }, some { target := 510, numerator := 11315545671592929075249807360 }, some { target := 511, numerator := 10820490548460738428207628288 }, some { target := 512, numerator := 353610802237279033601556480 }, some { target := 513, numerator := 11103379190250561655088873472 }, some { target := 514, numerator := 353610802237279033601556480 }, some { target := 515, numerator := 10820490548460738428207628288 }, some { target := 516, numerator := 6152827958928655184667082752 }, some { target := 517, numerator := 11103379190250561655088873472 }, some { target := 518, numerator := 173340015256714182271482986496 }, some { target := 519, numerator := 6789327402955757445149884416 }, some { target := 520, numerator := 11315545671592929075249807360 }, some { target := 521, numerator := 10820490548460738428207628288 }, some { target := 522, numerator := 353610802237279033601556480 }, some { target := 523, numerator := 6789327402955757445149884416 }, some { target := 524, numerator := 353610802237279033601556480 }, some { target := 525, numerator := 10891212708908194234927939584 }, some { target := 526, numerator := 6152827958928655184667082752 }, some { target := 527, numerator := 424332962684734840321867776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 9927623272811608868363698176 }, some { target := 545, numerator := 264736620608309569823031951360 }, some { target := 546, numerator := 253154393456696026143274303488 }, some { target := 547, numerator := 8273019394009674056969748480 }, some { target := 548, numerator := 259772808971903765388850102272 }, some { target := 549, numerator := 8273019394009674056969748480 }, some { target := 550, numerator := 253154393456696026143274303488 }, some { target := 551, numerator := 143950537455768328591273623552 }, some { target := 552, numerator := 259772808971903765388850102272 }, some { target := 553, numerator := 4055434106943542222726570704896 }, some { target := 554, numerator := 158841972364985741893819170816 }, some { target := 555, numerator := 264736620608309569823031951360 }, some { target := 556, numerator := 253154393456696026143274303488 }, some { target := 557, numerator := 8273019394009674056969748480 }, some { target := 558, numerator := 158841972364985741893819170816 }, some { target := 559, numerator := 8273019394009674056969748480 }, some { target := 560, numerator := 254808997335497960954668253184 }, some { target := 561, numerator := 143950537455768328591273623552 }, some { target := 562, numerator := 9927623272811608868363698176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 579, numerator := 795624305033877825603502080 }, some { target := 580, numerator := 21216648134236742016093388800 }, some { target := 581, numerator := 20288419778363884552889303040 }, some { target := 582, numerator := 663020254194898188002918400 }, some { target := 583, numerator := 20818835981719803103291637760 }, some { target := 584, numerator := 663020254194898188002918400 }, some { target := 585, numerator := 20288419778363884552889303040 }, some { target := 586, numerator := 11536552422991228471250780160 }, some { target := 587, numerator := 20818835981719803103291637760 }, some { target := 588, numerator := 325012528606339091759030599680 }, some { target := 589, numerator := 12729988880542045209656033280 }, some { target := 590, numerator := 21216648134236742016093388800 }, some { target := 591, numerator := 20288419778363884552889303040 }, some { target := 592, numerator := 663020254194898188002918400 }, some { target := 593, numerator := 12729988880542045209656033280 }, some { target := 594, numerator := 663020254194898188002918400 }, some { target := 595, numerator := 20421023829202864190489886720 }, some { target := 596, numerator := 11536552422991228471250780160 }, some { target := 597, numerator := 795624305033877825603502080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 371291342349142985281634304 }, some { target := 641, numerator := 9901102462643812940843581440 }, some { target := 642, numerator := 9467929229903146124681674752 }, some { target := 643, numerator := 309409451957619154401361920 }, some { target := 644, numerator := 9715456791469241448202764288 }, some { target := 645, numerator := 309409451957619154401361920 }, some { target := 646, numerator := 9467929229903146124681674752 }, some { target := 647, numerator := 5383724464062573286583697408 }, some { target := 648, numerator := 9715456791469241448202764288 }, some { target := 649, numerator := 151672513349624909487547613184 }, some { target := 650, numerator := 5940661477586287764506148864 }, some { target := 651, numerator := 9901102462643812940843581440 }, some { target := 652, numerator := 9467929229903146124681674752 }, some { target := 653, numerator := 309409451957619154401361920 }, some { target := 654, numerator := 5940661477586287764506148864 }, some { target := 655, numerator := 309409451957619154401361920 }, some { target := 656, numerator := 9529811120294669955561947136 }, some { target := 657, numerator := 5383724464062573286583697408 }, some { target := 658, numerator := 371291342349142985281634304 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 675, numerator := 804464575089809801443540992 }, some { target := 676, numerator := 21452388669061594705161093120 }, some { target := 677, numerator := 20513846664790149936810295296 }, some { target := 678, numerator := 670387145908174834536284160 }, some { target := 679, numerator := 21050156381516689804439322624 }, some { target := 680, numerator := 670387145908174834536284160 }, some { target := 681, numerator := 20513846664790149936810295296 }, some { target := 682, numerator := 11664736338802242120931344384 }, some { target := 683, numerator := 21050156381516689804439322624 }, some { target := 684, numerator := 328623778924187303889686495232 }, some { target := 685, numerator := 12871433201436956823096655872 }, some { target := 686, numerator := 21452388669061594705161093120 }, some { target := 687, numerator := 20513846664790149936810295296 }, some { target := 688, numerator := 670387145908174834536284160 }, some { target := 689, numerator := 12871433201436956823096655872 }, some { target := 690, numerator := 670387145908174834536284160 }, some { target := 691, numerator := 20647924093971784903717552128 }, some { target := 692, numerator := 11664736338802242120931344384 }, some { target := 693, numerator := 804464575089809801443540992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 776, numerator := 30940945195761915440136192 }, some { target := 777, numerator := 825091871886984411736965120 }, some { target := 778, numerator := 788994102491928843723472896 }, some { target := 779, numerator := 25784120996468262866780160 }, some { target := 780, numerator := 809621399289103454016897024 }, some { target := 781, numerator := 25784120996468262866780160 }, some { target := 782, numerator := 788994102491928843723472896 }, some { target := 783, numerator := 448643705338547773881974784 }, some { target := 784, numerator := 809621399289103454016897024 }, some { target := 785, numerator := 12639376112468742457295634432 }, some { target := 786, numerator := 495055123132190647042179072 }, some { target := 787, numerator := 825091871886984411736965120 }, some { target := 788, numerator := 788994102491928843723472896 }, some { target := 789, numerator := 25784120996468262866780160 }, some { target := 790, numerator := 495055123132190647042179072 }, some { target := 791, numerator := 25784120996468262866780160 }, some { target := 792, numerator := 794150926691222496296828928 }, some { target := 793, numerator := 448643705338547773881974784 }, some { target := 794, numerator := 30940945195761915440136192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 811, numerator := 795624305033877825603502080 }, some { target := 812, numerator := 21216648134236742016093388800 }, some { target := 813, numerator := 20288419778363884552889303040 }, some { target := 814, numerator := 663020254194898188002918400 }, some { target := 815, numerator := 20818835981719803103291637760 }, some { target := 816, numerator := 663020254194898188002918400 }, some { target := 817, numerator := 20288419778363884552889303040 }, some { target := 818, numerator := 11536552422991228471250780160 }, some { target := 819, numerator := 20818835981719803103291637760 }, some { target := 820, numerator := 325012528606339091759030599680 }, some { target := 821, numerator := 12729988880542045209656033280 }, some { target := 822, numerator := 21216648134236742016093388800 }, some { target := 823, numerator := 20288419778363884552889303040 }, some { target := 824, numerator := 663020254194898188002918400 }, some { target := 825, numerator := 12729988880542045209656033280 }, some { target := 826, numerator := 663020254194898188002918400 }, some { target := 827, numerator := 20421023829202864190489886720 }, some { target := 828, numerator := 11536552422991228471250780160 }, some { target := 829, numerator := 795624305033877825603502080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 30940945195761915440136192 }, some { target := 847, numerator := 825091871886984411736965120 }, some { target := 848, numerator := 788994102491928843723472896 }, some { target := 849, numerator := 25784120996468262866780160 }, some { target := 850, numerator := 809621399289103454016897024 }, some { target := 851, numerator := 25784120996468262866780160 }, some { target := 852, numerator := 788994102491928843723472896 }, some { target := 853, numerator := 448643705338547773881974784 }, some { target := 854, numerator := 809621399289103454016897024 }, some { target := 855, numerator := 12639376112468742457295634432 }, some { target := 856, numerator := 495055123132190647042179072 }, some { target := 857, numerator := 825091871886984411736965120 }, some { target := 858, numerator := 788994102491928843723472896 }, some { target := 859, numerator := 25784120996468262866780160 }, some { target := 860, numerator := 495055123132190647042179072 }, some { target := 861, numerator := 25784120996468262866780160 }, some { target := 862, numerator := 794150926691222496296828928 }, some { target := 863, numerator := 448643705338547773881974784 }, some { target := 864, numerator := 30940945195761915440136192 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 907, numerator := 804464575089809801443540992 }, some { target := 908, numerator := 21452388669061594705161093120 }, some { target := 909, numerator := 20513846664790149936810295296 }, some { target := 910, numerator := 670387145908174834536284160 }, some { target := 911, numerator := 21050156381516689804439322624 }, some { target := 912, numerator := 670387145908174834536284160 }, some { target := 913, numerator := 20513846664790149936810295296 }, some { target := 914, numerator := 11664736338802242120931344384 }, some { target := 915, numerator := 21050156381516689804439322624 }, some { target := 916, numerator := 328623778924187303889686495232 }, some { target := 917, numerator := 12871433201436956823096655872 }, some { target := 918, numerator := 21452388669061594705161093120 }, some { target := 919, numerator := 20513846664790149936810295296 }, some { target := 920, numerator := 670387145908174834536284160 }, some { target := 921, numerator := 12871433201436956823096655872 }, some { target := 922, numerator := 670387145908174834536284160 }, some { target := 923, numerator := 20647924093971784903717552128 }, some { target := 924, numerator := 11664736338802242120931344384 }, some { target := 925, numerator := 804464575089809801443540992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 942, numerator := 804464575089809801443540992 }, some { target := 943, numerator := 21452388669061594705161093120 }, some { target := 944, numerator := 20513846664790149936810295296 }, some { target := 945, numerator := 670387145908174834536284160 }, some { target := 946, numerator := 21050156381516689804439322624 }, some { target := 947, numerator := 670387145908174834536284160 }, some { target := 948, numerator := 20513846664790149936810295296 }, some { target := 949, numerator := 11664736338802242120931344384 }, some { target := 950, numerator := 21050156381516689804439322624 }, some { target := 951, numerator := 328623778924187303889686495232 }, some { target := 952, numerator := 12871433201436956823096655872 }, some { target := 953, numerator := 21452388669061594705161093120 }, some { target := 954, numerator := 20513846664790149936810295296 }, some { target := 955, numerator := 670387145908174834536284160 }, some { target := 956, numerator := 12871433201436956823096655872 }, some { target := 957, numerator := 670387145908174834536284160 }, some { target := 958, numerator := 20647924093971784903717552128 }, some { target := 959, numerator := 11664736338802242120931344384 }, some { target := 960, numerator := 804464575089809801443540992 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 26520810167795927520116736 }, some { target := 1018, numerator := 707221604474558067203112960 }, some { target := 1019, numerator := 676280659278796151762976768 }, some { target := 1020, numerator := 22100675139829939600097280 }, some { target := 1021, numerator := 693961199390660103443054592 }, some { target := 1022, numerator := 22100675139829939600097280 }, some { target := 1023, numerator := 676280659278796151762976768 }, some { target := 1024, numerator := 384551747433040949041692672 }, some { target := 1025, numerator := 693961199390660103443054592 }, some { target := 1026, numerator := 10833750953544636391967686656 }, some { target := 1027, numerator := 424332962684734840321867776 }, some { target := 1028, numerator := 707221604474558067203112960 }, some { target := 1029, numerator := 676280659278796151762976768 }, some { target := 1030, numerator := 22100675139829939600097280 }, some { target := 1031, numerator := 424332962684734840321867776 }, some { target := 1032, numerator := 22100675139829939600097280 }, some { target := 1033, numerator := 680700794306762139682996224 }, some { target := 1034, numerator := 384551747433040949041692672 }, some { target := 1035, numerator := 26520810167795927520116736 }]

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

end Slot20

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 291, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 2597066461825085439297454080 }, some { target := 30, numerator := 2671268360734373594705952768 }, some { target := 31, numerator := 2597066461825085439297454080 }, some { target := 32, numerator := 2300258866187932817663459328 }, some { target := 33, numerator := 107666955317377113497731596288 }, some { target := 34, numerator := 29309750069168821386356981760 }, some { target := 35, numerator := 2671268360734373594705952768 }, some { target := 36, numerator := 107666955317377113497731596288 }, some { target := 37, numerator := 2597066461825085439297454080 }, some { target := 38, numerator := 2597066461825085439297454080 }, some { target := 39, numerator := 2226056967278644662254960640 }, some { target := 40, numerator := 2597066461825085439297454080 }, some { target := 41, numerator := 29309750069168821386356981760 }, some { target := 42, numerator := 2226056967278644662254960640 }, some { target := 43, numerator := 2597066461825085439297454080 }, some { target := 44, numerator := 2300258866187932817663459328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 95906209320374899715761766400 }, some { target := 105, numerator := 98646386729528468279069245440 }, some { target := 106, numerator := 95906209320374899715761766400 }, some { target := 107, numerator := 84945499683760625462531850240 }, some { target := 108, numerator := 3975997420681827985359152087040 }, some { target := 109, numerator := 1082370076615659582506454220800 }, some { target := 110, numerator := 98646386729528468279069245440 }, some { target := 111, numerator := 3975997420681827985359152087040 }, some { target := 112, numerator := 95906209320374899715761766400 }, some { target := 113, numerator := 95906209320374899715761766400 }, some { target := 114, numerator := 82205322274607056899224371200 }, some { target := 115, numerator := 95906209320374899715761766400 }, some { target := 116, numerator := 1082370076615659582506454220800 }, some { target := 117, numerator := 82205322274607056899224371200 }, some { target := 118, numerator := 95906209320374899715761766400 }, some { target := 119, numerator := 84945499683760625462531850240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 95906185835363850874288865280 }, some { target := 227, numerator := 98646362573517103756411404288 }, some { target := 228, numerator := 95906185835363850874288865280 }, some { target := 229, numerator := 84945478882750839345798709248 }, some { target := 230, numerator := 3975996447060369931959804100608 }, some { target := 231, numerator := 1082369811570534888438402908160 }, some { target := 232, numerator := 98646362573517103756411404288 }, some { target := 233, numerator := 3975996447060369931959804100608 }, some { target := 234, numerator := 95906185835363850874288865280 }, some { target := 235, numerator := 95906185835363850874288865280 }, some { target := 236, numerator := 82205302144597586463676170240 }, some { target := 237, numerator := 95906185835363850874288865280 }, some { target := 238, numerator := 1082369811570534888438402908160 }, some { target := 239, numerator := 82205302144597586463676170240 }, some { target := 240, numerator := 95906185835363850874288865280 }, some { target := 241, numerator := 84945478882750839345798709248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 2597089946836134280770355200 }, some { target := 625, numerator := 2671292516745738117363793920 }, some { target := 626, numerator := 2597089946836134280770355200 }, some { target := 627, numerator := 2300279667197718934396600320 }, some { target := 628, numerator := 107667928938835166897079582720 }, some { target := 629, numerator := 29310015114293515454408294400 }, some { target := 630, numerator := 2671292516745738117363793920 }, some { target := 631, numerator := 107667928938835166897079582720 }, some { target := 632, numerator := 2597089946836134280770355200 }, some { target := 633, numerator := 2597089946836134280770355200 }, some { target := 634, numerator := 2226077097288115097803161600 }, some { target := 635, numerator := 2597089946836134280770355200 }, some { target := 636, numerator := 29310015114293515454408294400 }, some { target := 637, numerator := 2226077097288115097803161600 }, some { target := 638, numerator := 2597089946836134280770355200 }, some { target := 639, numerator := 2300279667197718934396600320 }]

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

end Slot21

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
