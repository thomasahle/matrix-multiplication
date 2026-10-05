import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 67, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 60748522435635116028985344 }, some { target := 111, numerator := 72138870392316700284420096 }, some { target := 112, numerator := 55053348457294323901267968 }, some { target := 113, numerator := 567619006507965615395831808 }, some { target := 114, numerator := 68342087740089505532608512 }, some { target := 115, numerator := 55053348457294323901267968 }, some { target := 116, numerator := 68342087740089505532608512 }, some { target := 117, numerator := 68342087740089505532608512 }, some { target := 118, numerator := 2927319424867167153646731264 }, some { target := 119, numerator := 68342087740089505532608512 }, some { target := 120, numerator := 567619006507965615395831808 }, some { target := 121, numerator := 2927319424867167153646731264 }, some { target := 122, numerator := 60748522435635116028985344 }, some { target := 123, numerator := 68342087740089505532608512 }, some { target := 124, numerator := 68342087740089505532608512 }, some { target := 125, numerator := 72138870392316700284420096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 1619960598283603094106275840 }, some { target := 207, numerator := 1923703210461778674251202560 }, some { target := 208, numerator := 1468089292194515304033812480 }, some { target := 209, numerator := 15136506840212416410555514880 }, some { target := 210, numerator := 1822455673069053480869560320 }, some { target := 211, numerator := 1468089292194515304033812480 }, some { target := 212, numerator := 1822455673069053480869560320 }, some { target := 213, numerator := 1822455673069053480869560320 }, some { target := 214, numerator := 78061851329791124097246167040 }, some { target := 215, numerator := 1822455673069053480869560320 }, some { target := 216, numerator := 15136506840212416410555514880 }, some { target := 217, numerator := 78061851329791124097246167040 }, some { target := 218, numerator := 1619960598283603094106275840 }, some { target := 219, numerator := 1822455673069053480869560320 }, some { target := 220, numerator := 1822455673069053480869560320 }, some { target := 221, numerator := 1923703210461778674251202560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 1549087322108695458739126272 }, some { target := 242, numerator := 1839541195004075857252712448 }, some { target := 243, numerator := 1403860385661005259482333184 }, some { target := 244, numerator := 14474284665953123192593711104 }, some { target := 245, numerator := 1742723237372282391081517056 }, some { target := 246, numerator := 1403860385661005259482333184 }, some { target := 247, numerator := 1742723237372282391081517056 }, some { target := 248, numerator := 1742723237372282391081517056 }, some { target := 249, numerator := 74646645334112762417991647232 }, some { target := 250, numerator := 1742723237372282391081517056 }, some { target := 251, numerator := 14474284665953123192593711104 }, some { target := 252, numerator := 74646645334112762417991647232 }, some { target := 253, numerator := 1549087322108695458739126272 }, some { target := 254, numerator := 1742723237372282391081517056 }, some { target := 255, numerator := 1742723237372282391081517056 }, some { target := 256, numerator := 1839541195004075857252712448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 50623768696362596690821120 }, some { target := 303, numerator := 60115725326930583570350080 }, some { target := 304, numerator := 45877790381078603251056640 }, some { target := 305, numerator := 473015838756638012829859840 }, some { target := 306, numerator := 56951739783407921277173760 }, some { target := 307, numerator := 45877790381078603251056640 }, some { target := 308, numerator := 56951739783407921277173760 }, some { target := 309, numerator := 56951739783407921277173760 }, some { target := 310, numerator := 2439432854055972628038942720 }, some { target := 311, numerator := 56951739783407921277173760 }, some { target := 312, numerator := 473015838756638012829859840 }, some { target := 313, numerator := 2439432854055972628038942720 }, some { target := 314, numerator := 50623768696362596690821120 }, some { target := 315, numerator := 56951739783407921277173760 }, some { target := 316, numerator := 56951739783407921277173760 }, some { target := 317, numerator := 60115725326930583570350080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 1589586337065785536091783168 }, some { target := 338, numerator := 1887633775265620324108992512 }, some { target := 339, numerator := 1440562617965868142083178496 }, some { target := 340, numerator := 14852697336958433602857598976 }, some { target := 341, numerator := 1788284629199008728103256064 }, some { target := 342, numerator := 1440562617965868142083178496 }, some { target := 343, numerator := 1788284629199008728103256064 }, some { target := 344, numerator := 1788284629199008728103256064 }, some { target := 345, numerator := 76598191617357540520422801408 }, some { target := 346, numerator := 1788284629199008728103256064 }, some { target := 347, numerator := 14852697336958433602857598976 }, some { target := 348, numerator := 76598191617357540520422801408 }, some { target := 349, numerator := 1589586337065785536091783168 }, some { target := 350, numerator := 1788284629199008728103256064 }, some { target := 351, numerator := 1788284629199008728103256064 }, some { target := 352, numerator := 1887633775265620324108992512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 50623768696362596690821120 }, some { target := 364, numerator := 60115725326930583570350080 }, some { target := 365, numerator := 45877790381078603251056640 }, some { target := 366, numerator := 473015838756638012829859840 }, some { target := 367, numerator := 56951739783407921277173760 }, some { target := 368, numerator := 45877790381078603251056640 }, some { target := 369, numerator := 56951739783407921277173760 }, some { target := 370, numerator := 56951739783407921277173760 }, some { target := 371, numerator := 2439432854055972628038942720 }, some { target := 372, numerator := 56951739783407921277173760 }, some { target := 373, numerator := 473015838756638012829859840 }, some { target := 374, numerator := 2439432854055972628038942720 }, some { target := 375, numerator := 50623768696362596690821120 }, some { target := 376, numerator := 56951739783407921277173760 }, some { target := 377, numerator := 56951739783407921277173760 }, some { target := 378, numerator := 60115725326930583570350080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 1549087322108695458739126272 }, some { target := 474, numerator := 1839541195004075857252712448 }, some { target := 475, numerator := 1403860385661005259482333184 }, some { target := 476, numerator := 14474284665953123192593711104 }, some { target := 477, numerator := 1742723237372282391081517056 }, some { target := 478, numerator := 1403860385661005259482333184 }, some { target := 479, numerator := 1742723237372282391081517056 }, some { target := 480, numerator := 1742723237372282391081517056 }, some { target := 481, numerator := 74646645334112762417991647232 }, some { target := 482, numerator := 1742723237372282391081517056 }, some { target := 483, numerator := 14474284665953123192593711104 }, some { target := 484, numerator := 74646645334112762417991647232 }, some { target := 485, numerator := 1549087322108695458739126272 }, some { target := 486, numerator := 1742723237372282391081517056 }, some { target := 487, numerator := 1742723237372282391081517056 }, some { target := 488, numerator := 1839541195004075857252712448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 880853575316709182420287488 }, some { target := 509, numerator := 1046013620688592154124091392 }, some { target := 510, numerator := 798273552630767696568385536 }, some { target := 511, numerator := 8230475594365501423239561216 }, some { target := 512, numerator := 990960272231297830222823424 }, some { target := 513, numerator := 798273552630767696568385536 }, some { target := 514, numerator := 990960272231297830222823424 }, some { target := 515, numerator := 990960272231297830222823424 }, some { target := 516, numerator := 42446131660573923727877603328 }, some { target := 517, numerator := 990960272231297830222823424 }, some { target := 518, numerator := 8230475594365501423239561216 }, some { target := 519, numerator := 42446131660573923727877603328 }, some { target := 520, numerator := 880853575316709182420287488 }, some { target := 521, numerator := 990960272231297830222823424 }, some { target := 522, numerator := 990960272231297830222823424 }, some { target := 523, numerator := 1046013620688592154124091392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 1589586337065785536091783168 }, some { target := 570, numerator := 1887633775265620324108992512 }, some { target := 571, numerator := 1440562617965868142083178496 }, some { target := 572, numerator := 14852697336958433602857598976 }, some { target := 573, numerator := 1788284629199008728103256064 }, some { target := 574, numerator := 1440562617965868142083178496 }, some { target := 575, numerator := 1788284629199008728103256064 }, some { target := 576, numerator := 1788284629199008728103256064 }, some { target := 577, numerator := 76598191617357540520422801408 }, some { target := 578, numerator := 1788284629199008728103256064 }, some { target := 579, numerator := 14852697336958433602857598976 }, some { target := 580, numerator := 76598191617357540520422801408 }, some { target := 581, numerator := 1589586337065785536091783168 }, some { target := 582, numerator := 1788284629199008728103256064 }, some { target := 583, numerator := 1788284629199008728103256064 }, some { target := 584, numerator := 1887633775265620324108992512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 24815771414956944897840513024 }, some { target := 605, numerator := 29468728555261372066185609216 }, some { target := 606, numerator := 22489292844804731313667964928 }, some { target := 607, numerator := 231872364158503953889197293568 }, some { target := 608, numerator := 27917742841826563010070577152 }, some { target := 609, numerator := 22489292844804731313667964928 }, some { target := 610, numerator := 27917742841826563010070577152 }, some { target := 611, numerator := 27917742841826563010070577152 }, some { target := 612, numerator := 1195809985058237782264689721344 }, some { target := 613, numerator := 27917742841826563010070577152 }, some { target := 614, numerator := 231872364158503953889197293568 }, some { target := 615, numerator := 1195809985058237782264689721344 }, some { target := 616, numerator := 24815771414956944897840513024 }, some { target := 617, numerator := 27917742841826563010070577152 }, some { target := 618, numerator := 27917742841826563010070577152 }, some { target := 619, numerator := 29468728555261372066185609216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 971976358970161856463765504 }, some { target := 631, numerator := 1154221926277067204550721536 }, some { target := 632, numerator := 880853575316709182420287488 }, some { target := 633, numerator := 9081904104127449846333308928 }, some { target := 634, numerator := 1093473403841432088521736192 }, some { target := 635, numerator := 880853575316709182420287488 }, some { target := 636, numerator := 1093473403841432088521736192 }, some { target := 637, numerator := 1093473403841432088521736192 }, some { target := 638, numerator := 46837110797874674458347700224 }, some { target := 639, numerator := 1093473403841432088521736192 }, some { target := 640, numerator := 9081904104127449846333308928 }, some { target := 641, numerator := 46837110797874674458347700224 }, some { target := 642, numerator := 971976358970161856463765504 }, some { target := 643, numerator := 1093473403841432088521736192 }, some { target := 644, numerator := 1093473403841432088521736192 }, some { target := 645, numerator := 1154221926277067204550721536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 1619960598283603094106275840 }, some { target := 680, numerator := 1923703210461778674251202560 }, some { target := 681, numerator := 1468089292194515304033812480 }, some { target := 682, numerator := 15136506840212416410555514880 }, some { target := 683, numerator := 1822455673069053480869560320 }, some { target := 684, numerator := 1468089292194515304033812480 }, some { target := 685, numerator := 1822455673069053480869560320 }, some { target := 686, numerator := 1822455673069053480869560320 }, some { target := 687, numerator := 78061851329791124097246167040 }, some { target := 688, numerator := 1822455673069053480869560320 }, some { target := 689, numerator := 15136506840212416410555514880 }, some { target := 690, numerator := 78061851329791124097246167040 }, some { target := 691, numerator := 1619960598283603094106275840 }, some { target := 692, numerator := 1822455673069053480869560320 }, some { target := 693, numerator := 1822455673069053480869560320 }, some { target := 694, numerator := 1923703210461778674251202560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 1549087322108695458739126272 }, some { target := 706, numerator := 1839541195004075857252712448 }, some { target := 707, numerator := 1403860385661005259482333184 }, some { target := 708, numerator := 14474284665953123192593711104 }, some { target := 709, numerator := 1742723237372282391081517056 }, some { target := 710, numerator := 1403860385661005259482333184 }, some { target := 711, numerator := 1742723237372282391081517056 }, some { target := 712, numerator := 1742723237372282391081517056 }, some { target := 713, numerator := 74646645334112762417991647232 }, some { target := 714, numerator := 1742723237372282391081517056 }, some { target := 715, numerator := 14474284665953123192593711104 }, some { target := 716, numerator := 74646645334112762417991647232 }, some { target := 717, numerator := 1549087322108695458739126272 }, some { target := 718, numerator := 1742723237372282391081517056 }, some { target := 719, numerator := 1742723237372282391081517056 }, some { target := 720, numerator := 1839541195004075857252712448 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 50623768696362596690821120 }, some { target := 786, numerator := 60115725326930583570350080 }, some { target := 787, numerator := 45877790381078603251056640 }, some { target := 788, numerator := 473015838756638012829859840 }, some { target := 789, numerator := 56951739783407921277173760 }, some { target := 790, numerator := 45877790381078603251056640 }, some { target := 791, numerator := 56951739783407921277173760 }, some { target := 792, numerator := 56951739783407921277173760 }, some { target := 793, numerator := 2439432854055972628038942720 }, some { target := 794, numerator := 56951739783407921277173760 }, some { target := 795, numerator := 473015838756638012829859840 }, some { target := 796, numerator := 2439432854055972628038942720 }, some { target := 797, numerator := 50623768696362596690821120 }, some { target := 798, numerator := 56951739783407921277173760 }, some { target := 799, numerator := 56951739783407921277173760 }, some { target := 800, numerator := 60115725326930583570350080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 971976358970161856463765504 }, some { target := 821, numerator := 1154221926277067204550721536 }, some { target := 822, numerator := 880853575316709182420287488 }, some { target := 823, numerator := 9081904104127449846333308928 }, some { target := 824, numerator := 1093473403841432088521736192 }, some { target := 825, numerator := 880853575316709182420287488 }, some { target := 826, numerator := 1093473403841432088521736192 }, some { target := 827, numerator := 1093473403841432088521736192 }, some { target := 828, numerator := 46837110797874674458347700224 }, some { target := 829, numerator := 1093473403841432088521736192 }, some { target := 830, numerator := 9081904104127449846333308928 }, some { target := 831, numerator := 46837110797874674458347700224 }, some { target := 832, numerator := 971976358970161856463765504 }, some { target := 833, numerator := 1093473403841432088521736192 }, some { target := 834, numerator := 1093473403841432088521736192 }, some { target := 835, numerator := 1154221926277067204550721536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 50623768696362596690821120 }, some { target := 847, numerator := 60115725326930583570350080 }, some { target := 848, numerator := 45877790381078603251056640 }, some { target := 849, numerator := 473015838756638012829859840 }, some { target := 850, numerator := 56951739783407921277173760 }, some { target := 851, numerator := 45877790381078603251056640 }, some { target := 852, numerator := 56951739783407921277173760 }, some { target := 853, numerator := 56951739783407921277173760 }, some { target := 854, numerator := 2439432854055972628038942720 }, some { target := 855, numerator := 56951739783407921277173760 }, some { target := 856, numerator := 473015838756638012829859840 }, some { target := 857, numerator := 2439432854055972628038942720 }, some { target := 858, numerator := 50623768696362596690821120 }, some { target := 859, numerator := 56951739783407921277173760 }, some { target := 860, numerator := 56951739783407921277173760 }, some { target := 861, numerator := 60115725326930583570350080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 1559212075847967978077290496 }, some { target := 896, numerator := 1851564340069461973966782464 }, some { target := 897, numerator := 1413035943737220980132544512 }, some { target := 898, numerator := 14568887833704450795159683072 }, some { target := 899, numerator := 1754113585328963975336951808 }, some { target := 900, numerator := 1413035943737220980132544512 }, some { target := 901, numerator := 1754113585328963975336951808 }, some { target := 902, numerator := 1754113585328963975336951808 }, some { target := 903, numerator := 75134531904923956943599435776 }, some { target := 904, numerator := 1754113585328963975336951808 }, some { target := 905, numerator := 14568887833704450795159683072 }, some { target := 906, numerator := 75134531904923956943599435776 }, some { target := 907, numerator := 1559212075847967978077290496 }, some { target := 908, numerator := 1754113585328963975336951808 }, some { target := 909, numerator := 1754113585328963975336951808 }, some { target := 910, numerator := 1851564340069461973966782464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 880853575316709182420287488 }, some { target := 922, numerator := 1046013620688592154124091392 }, some { target := 923, numerator := 798273552630767696568385536 }, some { target := 924, numerator := 8230475594365501423239561216 }, some { target := 925, numerator := 990960272231297830222823424 }, some { target := 926, numerator := 798273552630767696568385536 }, some { target := 927, numerator := 990960272231297830222823424 }, some { target := 928, numerator := 990960272231297830222823424 }, some { target := 929, numerator := 42446131660573923727877603328 }, some { target := 930, numerator := 990960272231297830222823424 }, some { target := 931, numerator := 8230475594365501423239561216 }, some { target := 932, numerator := 42446131660573923727877603328 }, some { target := 933, numerator := 880853575316709182420287488 }, some { target := 934, numerator := 990960272231297830222823424 }, some { target := 935, numerator := 990960272231297830222823424 }, some { target := 936, numerator := 1046013620688592154124091392 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 60748522435635116028985344 }, some { target := 967, numerator := 72138870392316700284420096 }, some { target := 968, numerator := 55053348457294323901267968 }, some { target := 969, numerator := 567619006507965615395831808 }, some { target := 970, numerator := 68342087740089505532608512 }, some { target := 971, numerator := 55053348457294323901267968 }, some { target := 972, numerator := 68342087740089505532608512 }, some { target := 973, numerator := 68342087740089505532608512 }, some { target := 974, numerator := 2927319424867167153646731264 }, some { target := 975, numerator := 68342087740089505532608512 }, some { target := 976, numerator := 567619006507965615395831808 }, some { target := 977, numerator := 2927319424867167153646731264 }, some { target := 978, numerator := 60748522435635116028985344 }, some { target := 979, numerator := 68342087740089505532608512 }, some { target := 980, numerator := 68342087740089505532608512 }, some { target := 981, numerator := 72138870392316700284420096 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 1, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 749, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 965, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1010, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1015, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 38, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737521909760, 0, 140737454800896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 389, numerator := 128814481617931240376861982720 }, some { target := 391, numerator := 128814420194414534781422272512 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 731, numerator := 1247706483435012631616647331840 }, some { target := 733, numerator := 1247705888482340646621454270464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 992, numerator := 128814481617931240376861982720 }, some { target := 994, numerator := 128814420194414534781422272512 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3
