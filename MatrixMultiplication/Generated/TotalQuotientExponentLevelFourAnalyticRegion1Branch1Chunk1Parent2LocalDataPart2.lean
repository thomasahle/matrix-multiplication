import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 6, #[49882488373248, 0, 0, 181709966409728, 0, 49882521927680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 5, numerator := 637589120869652394261086208 }, some { target := 6, numerator := 15631217156804381278658887680 }, some { target := 7, numerator := 11558873739636924050797756416 }, some { target := 8, numerator := 12895754154363614554893582336 }, some { target := 9, numerator := 637589120869652394261086208 }, some { target := 10, numerator := 12875186763367819316369031168 }, some { target := 11, numerator := 13101428064321566940139094016 }, some { target := 12, numerator := 637589120869652394261086208 }, some { target := 13, numerator := 15631217156804381278658887680 }, some { target := 14, numerator := 637589120869652394261086208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 2322584568547031921656332288 }, some { target := 95, numerator := 56940782970830460014800404480 }, some { target := 96, numerator := 42106210565271998063576088576 }, some { target := 97, numerator := 46976145950935129512210333696 }, some { target := 98, numerator := 2322584568547031921656332288 }, some { target := 99, numerator := 46901223868078773643769806848 }, some { target := 100, numerator := 47725366779498688196615602176 }, some { target := 101, numerator := 2322584568547031921656332288 }, some { target := 102, numerator := 56940782970830460014800404480 }, some { target := 103, numerator := 2322584568547031921656332288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 637589549756452108008161280 }, some { target := 217, numerator := 15631227671448503293103308800 }, some { target := 218, numerator := 11558881514939551119373762560 }, some { target := 219, numerator := 12895762828945015216810229760 }, some { target := 220, numerator := 637589549756452108008161280 }, some { target := 221, numerator := 12875195424114161923003514880 }, some { target := 222, numerator := 13101436877253548154877378560 }, some { target := 223, numerator := 637589549756452108008161280 }, some { target := 224, numerator := 15631227671448503293103308800 }, some { target := 225, numerator := 637589549756452108008161280 }]

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
def data : BetaFourLocalSlotData := ⟨11, 222, #[3434312892416, 0, 137303192240128, 0, 0, 137303158685696, 0, 0, 0, 0, 0, 0, 3434312892416, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 29, numerator := 2462467665398166191691792384 }, some { target := 30, numerator := 1833752516785868440621547520 }, some { target := 31, numerator := 1938538374887918065799921664 }, some { target := 32, numerator := 2514860594449191004280979456 }, some { target := 33, numerator := 33688653379808954494847287296 }, some { target := 34, numerator := 60932976486341857041224564736 }, some { target := 35, numerator := 1833752516785868440621547520 }, some { target := 36, numerator := 33688653379808954494847287296 }, some { target := 37, numerator := 1990931303938942878389108736 }, some { target := 38, numerator := 1990931303938942878389108736 }, some { target := 39, numerator := 1938538374887918065799921664 }, some { target := 40, numerator := 1938538374887918065799921664 }, some { target := 41, numerator := 60932976486341857041224564736 }, some { target := 42, numerator := 1938538374887918065799921664 }, some { target := 43, numerator := 2462467665398166191691792384 }, some { target := 44, numerator := 2514860594449191004280979456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 98449000379057139347223478272 }, some { target := 105, numerator := 73313085388659571854315356160 }, some { target := 106, numerator := 77502404553725833103133376512 }, some { target := 107, numerator := 100543659961590269971632488448 }, some { target := 108, numerator := 1346866111568802991494993543168 }, some { target := 109, numerator := 2436089094486030916187678834688 }, some { target := 110, numerator := 73313085388659571854315356160 }, some { target := 111, numerator := 1346866111568802991494993543168 }, some { target := 112, numerator := 79597064136258963727542386688 }, some { target := 113, numerator := 79597064136258963727542386688 }, some { target := 114, numerator := 77502404553725833103133376512 }, some { target := 115, numerator := 77502404553725833103133376512 }, some { target := 116, numerator := 2436089094486030916187678834688 }, some { target := 117, numerator := 77502404553725833103133376512 }, some { target := 118, numerator := 98449000379057139347223478272 }, some { target := 119, numerator := 100543659961590269971632488448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 98448976319891181211540783104 }, some { target := 227, numerator := 73313067472259390263913349120 }, some { target := 228, numerator := 77502385613531355421851254784 }, some { target := 229, numerator := 100543635390527163790509735936 }, some { target := 230, numerator := 1346865782418936798277036670976 }, some { target := 231, numerator := 2436088499149647739340892143616 }, some { target := 232, numerator := 73313067472259390263913349120 }, some { target := 233, numerator := 1346865782418936798277036670976 }, some { target := 234, numerator := 79597044684167338000820207616 }, some { target := 235, numerator := 79597044684167338000820207616 }, some { target := 236, numerator := 77502385613531355421851254784 }, some { target := 237, numerator := 77502385613531355421851254784 }, some { target := 238, numerator := 2436088499149647739340892143616 }, some { target := 239, numerator := 77502385613531355421851254784 }, some { target := 240, numerator := 98448976319891181211540783104 }, some { target := 241, numerator := 100543635390527163790509735936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 2462467665398166191691792384 }, some { target := 625, numerator := 1833752516785868440621547520 }, some { target := 626, numerator := 1938538374887918065799921664 }, some { target := 627, numerator := 2514860594449191004280979456 }, some { target := 628, numerator := 33688653379808954494847287296 }, some { target := 629, numerator := 60932976486341857041224564736 }, some { target := 630, numerator := 1833752516785868440621547520 }, some { target := 631, numerator := 33688653379808954494847287296 }, some { target := 632, numerator := 1990931303938942878389108736 }, some { target := 633, numerator := 1990931303938942878389108736 }, some { target := 634, numerator := 1938538374887918065799921664 }, some { target := 635, numerator := 1938538374887918065799921664 }, some { target := 636, numerator := 60932976486341857041224564736 }, some { target := 637, numerator := 1938538374887918065799921664 }, some { target := 638, numerator := 2462467665398166191691792384 }, some { target := 639, numerator := 2514860594449191004280979456 }]

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
def data : BetaFourLocalSlotData := ⟨12, 574, #[139552882688, 22870029762560, 0, 235455811420160, 0, 0, 0, 0, 0, 0, 0, 22870029762560, 0, 0, 0, 0, 0, 0, 139552882688], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 71, numerator := 33027963703401229836091392 }, some { target := 72, numerator := 478905473699317832623325184 }, some { target := 73, numerator := 847717735053964899126345728 }, some { target := 74, numerator := 27523303086167691530076160 }, some { target := 75, numerator := 528447419254419677377462272 }, some { target := 76, numerator := 27523303086167691530076160 }, some { target := 77, numerator := 842213074436731360820330496 }, some { target := 78, numerator := 880745698757366128962437120 }, some { target := 79, numerator := 528447419254419677377462272 }, some { target := 80, numerator := 13491923172839402388043333632 }, some { target := 81, numerator := 864231716905665514044391424 }, some { target := 82, numerator := 478905473699317832623325184 }, some { target := 83, numerator := 842213074436731360820330496 }, some { target := 84, numerator := 27523303086167691530076160 }, some { target := 85, numerator := 864231716905665514044391424 }, some { target := 86, numerator := 27523303086167691530076160 }, some { target := 87, numerator := 842213074436731360820330496 }, some { target := 88, numerator := 880745698757366128962437120 }, some { target := 89, numerator := 33027963703401229836091392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 5412647150989230639981527040 }, some { target := 147, numerator := 78483383689343844279732142080 }, some { target := 148, numerator := 138924610208723586426192527360 }, some { target := 149, numerator := 4510539292491025533317939200 }, some { target := 150, numerator := 86602354415827690239704432640 }, some { target := 151, numerator := 4510539292491025533317939200 }, some { target := 152, numerator := 138022502350225381319528939520 }, some { target := 153, numerator := 144337257359712817066174054400 }, some { target := 154, numerator := 86602354415827690239704432640 }, some { target := 155, numerator := 2211066361179100716432453795840 }, some { target := 156, numerator := 141630933784218201746183290880 }, some { target := 157, numerator := 78483383689343844279732142080 }, some { target := 158, numerator := 138022502350225381319528939520 }, some { target := 159, numerator := 4510539292491025533317939200 }, some { target := 160, numerator := 141630933784218201746183290880 }, some { target := 161, numerator := 4510539292491025533317939200 }, some { target := 162, numerator := 138022502350225381319528939520 }, some { target := 163, numerator := 144337257359712817066174054400 }, some { target := 164, numerator := 5412647150989230639981527040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 55725298134659262303373885440 }, some { target := 243, numerator := 808016822952559303398921338880 }, some { target := 244, numerator := 1430282652122921065786596392960 }, some { target := 245, numerator := 46437748445549385252811571200 }, some { target := 246, numerator := 891604770154548196853982167040 }, some { target := 247, numerator := 46437748445549385252811571200 }, some { target := 248, numerator := 1420995102433811188736034078720 }, some { target := 249, numerator := 1486007950257580328089970278400 }, some { target := 250, numerator := 891604770154548196853982167040 }, some { target := 251, numerator := 22763784288008308650928232202240 }, some { target := 252, numerator := 1458145301190250696938283335680 }, some { target := 253, numerator := 808016822952559303398921338880 }, some { target := 254, numerator := 1420995102433811188736034078720 }, some { target := 255, numerator := 46437748445549385252811571200 }, some { target := 256, numerator := 1458145301190250696938283335680 }, some { target := 257, numerator := 46437748445549385252811571200 }, some { target := 258, numerator := 1420995102433811188736034078720 }, some { target := 259, numerator := 1486007950257580328089970278400 }, some { target := 260, numerator := 55725298134659262303373885440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 5412647150989230639981527040 }, some { target := 641, numerator := 78483383689343844279732142080 }, some { target := 642, numerator := 138924610208723586426192527360 }, some { target := 643, numerator := 4510539292491025533317939200 }, some { target := 644, numerator := 86602354415827690239704432640 }, some { target := 645, numerator := 4510539292491025533317939200 }, some { target := 646, numerator := 138022502350225381319528939520 }, some { target := 647, numerator := 144337257359712817066174054400 }, some { target := 648, numerator := 86602354415827690239704432640 }, some { target := 649, numerator := 2211066361179100716432453795840 }, some { target := 650, numerator := 141630933784218201746183290880 }, some { target := 651, numerator := 78483383689343844279732142080 }, some { target := 652, numerator := 138022502350225381319528939520 }, some { target := 653, numerator := 4510539292491025533317939200 }, some { target := 654, numerator := 141630933784218201746183290880 }, some { target := 655, numerator := 4510539292491025533317939200 }, some { target := 656, numerator := 138022502350225381319528939520 }, some { target := 657, numerator := 144337257359712817066174054400 }, some { target := 658, numerator := 5412647150989230639981527040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 33027963703401229836091392 }, some { target := 1018, numerator := 478905473699317832623325184 }, some { target := 1019, numerator := 847717735053964899126345728 }, some { target := 1020, numerator := 27523303086167691530076160 }, some { target := 1021, numerator := 528447419254419677377462272 }, some { target := 1022, numerator := 27523303086167691530076160 }, some { target := 1023, numerator := 842213074436731360820330496 }, some { target := 1024, numerator := 880745698757366128962437120 }, some { target := 1025, numerator := 528447419254419677377462272 }, some { target := 1026, numerator := 13491923172839402388043333632 }, some { target := 1027, numerator := 864231716905665514044391424 }, some { target := 1028, numerator := 478905473699317832623325184 }, some { target := 1029, numerator := 842213074436731360820330496 }, some { target := 1030, numerator := 27523303086167691530076160 }, some { target := 1031, numerator := 864231716905665514044391424 }, some { target := 1032, numerator := 27523303086167691530076160 }, some { target := 1033, numerator := 842213074436731360820330496 }, some { target := 1034, numerator := 880745698757366128962437120 }, some { target := 1035, numerator := 33027963703401229836091392 }]

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
def data : BetaFourLocalSlotData := ⟨13, 52, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 200, numerator := 78211653833532345361104896 }, some { target := 201, numerator := 88303480134633293149634560 }, some { target := 202, numerator := 75688697258257108413972480 }, some { target := 203, numerator := 996567847233718594117304320 }, some { target := 204, numerator := 88303480134633293149634560 }, some { target := 205, numerator := 75688697258257108413972480 }, some { target := 206, numerator := 88303480134633293149634560 }, some { target := 207, numerator := 88303480134633293149634560 }, some { target := 208, numerator := 3660809990724368810289135616 }, some { target := 209, numerator := 90826436709908530096766976 }, some { target := 210, numerator := 996567847233718594117304320 }, some { target := 211, numerator := 3660809990724368810289135616 }, some { target := 212, numerator := 78211653833532345361104896 }, some { target := 213, numerator := 88303480134633293149634560 }, some { target := 214, numerator := 90826436709908530096766976 }, some { target := 215, numerator := 88303480134633293149634560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 15512095715916725491649740800 }, some { target := 297, numerator := 17513656453454367490572288000 }, some { target := 298, numerator := 15011705531532314991919104000 }, some { target := 299, numerator := 197654122831842147393601536000 }, some { target := 300, numerator := 17513656453454367490572288000 }, some { target := 301, numerator := 15011705531532314991919104000 }, some { target := 302, numerator := 17513656453454367490572288000 }, some { target := 303, numerator := 17513656453454367490572288000 }, some { target := 304, numerator := 726066157541779635109153996800 }, some { target := 305, numerator := 18014046637838777990302924800 }, some { target := 306, numerator := 197654122831842147393601536000 }, some { target := 307, numerator := 726066157541779635109153996800 }, some { target := 308, numerator := 15512095715916725491649740800 }, some { target := 309, numerator := 17513656453454367490572288000 }, some { target := 310, numerator := 18014046637838777990302924800 }, some { target := 311, numerator := 17513656453454367490572288000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 15512095715916725491649740800 }, some { target := 660, numerator := 17513656453454367490572288000 }, some { target := 661, numerator := 15011705531532314991919104000 }, some { target := 662, numerator := 197654122831842147393601536000 }, some { target := 663, numerator := 17513656453454367490572288000 }, some { target := 664, numerator := 15011705531532314991919104000 }, some { target := 665, numerator := 17513656453454367490572288000 }, some { target := 666, numerator := 17513656453454367490572288000 }, some { target := 667, numerator := 726066157541779635109153996800 }, some { target := 668, numerator := 18014046637838777990302924800 }, some { target := 669, numerator := 197654122831842147393601536000 }, some { target := 670, numerator := 726066157541779635109153996800 }, some { target := 671, numerator := 15512095715916725491649740800 }, some { target := 672, numerator := 17513656453454367490572288000 }, some { target := 673, numerator := 18014046637838777990302924800 }, some { target := 674, numerator := 17513656453454367490572288000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 78211653833532345361104896 }, some { target := 1037, numerator := 88303480134633293149634560 }, some { target := 1038, numerator := 75688697258257108413972480 }, some { target := 1039, numerator := 996567847233718594117304320 }, some { target := 1040, numerator := 88303480134633293149634560 }, some { target := 1041, numerator := 75688697258257108413972480 }, some { target := 1042, numerator := 88303480134633293149634560 }, some { target := 1043, numerator := 88303480134633293149634560 }, some { target := 1044, numerator := 3660809990724368810289135616 }, some { target := 1045, numerator := 90826436709908530096766976 }, some { target := 1046, numerator := 996567847233718594117304320 }, some { target := 1047, numerator := 3660809990724368810289135616 }, some { target := 1048, numerator := 78211653833532345361104896 }, some { target := 1049, numerator := 88303480134633293149634560 }, some { target := 1050, numerator := 90826436709908530096766976 }, some { target := 1051, numerator := 88303480134633293149634560 }]

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
def data : BetaFourLocalSlotData := ⟨14, 0, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
def data : BetaFourLocalSlotData := ⟨15, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[67207648247808, 73529840107520, 67207648247808, 73529840107520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2
