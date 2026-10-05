import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 690, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 110, numerator := 1055655881389872726430187520 }, some { target := 112, numerator := 38983967264246645539838361600 }, some { target := 115, numerator := 38983957718056587395145400320 }, some { target := 122, numerator := 1055665427579930871123148800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 28150823503729939371471667200 }, some { target := 208, numerator := 1039572460379910547729022976000 }, some { target := 211, numerator := 1039572205814842330537210675200 }, some { target := 218, numerator := 28151078068798156563283968000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 26919224975441754523969781760 }, some { target := 243, numerator := 994091165238289461265878220800 }, some { target := 246, numerator := 994090921810442978576207708160 }, some { target := 253, numerator := 26919468403288237213640294400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 879713234491560605358489600 }, some { target := 304, numerator := 32486639386872204616531968000 }, some { target := 307, numerator := 32486631431713822829287833600 }, some { target := 314, numerator := 879721189649942392602624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 27622995563035003008256573440 }, some { target := 339, numerator := 1020080476747787224959103795200 }, some { target := 342, numerator := 1020080226955814036839637975040 }, some { target := 349, numerator := 27623245355008191127722393600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 879713234491560605358489600 }, some { target := 365, numerator := 32486639386872204616531968000 }, some { target := 368, numerator := 32486631431713822829287833600 }, some { target := 375, numerator := 879721189649942392602624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 26919224975441754523969781760 }, some { target := 475, numerator := 994091165238289461265878220800 }, some { target := 478, numerator := 994090921810442978576207708160 }, some { target := 485, numerator := 26919468403288237213640294400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 15307010280153154533237719040 }, some { target := 510, numerator := 565267525331576360327656243200 }, some { target := 513, numerator := 565267386911820517229608304640 }, some { target := 520, numerator := 15307148699908997631285657600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 27622995563035003008256573440 }, some { target := 571, numerator := 1020080476747787224959103795200 }, some { target := 574, numerator := 1020080226955814036839637975040 }, some { target := 581, numerator := 27623245355008191127722393600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 431235427547763008746731601920 }, some { target := 606, numerator := 15924950627444754703023970713600 }, some { target := 609, numerator := 15924946727826115950916896030720 }, some { target := 616, numerator := 431239327166401760853806284800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 16890494102237963622883000320 }, some { target := 632, numerator := 623743476227946328637413785600 }, some { target := 635, numerator := 623743323488905398322326405120 }, some { target := 642, numerator := 16890646841278893937970380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 28150823503729939371471667200 }, some { target := 681, numerator := 1039572460379910547729022976000 }, some { target := 684, numerator := 1039572205814842330537210675200 }, some { target := 691, numerator := 28151078068798156563283968000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 26919224975441754523969781760 }, some { target := 707, numerator := 994091165238289461265878220800 }, some { target := 710, numerator := 994090921810442978576207708160 }, some { target := 717, numerator := 26919468403288237213640294400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 879713234491560605358489600 }, some { target := 787, numerator := 32486639386872204616531968000 }, some { target := 790, numerator := 32486631431713822829287833600 }, some { target := 797, numerator := 879721189649942392602624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 16890494102237963622883000320 }, some { target := 822, numerator := 623743476227946328637413785600 }, some { target := 825, numerator := 623743323488905398322326405120 }, some { target := 832, numerator := 16890646841278893937970380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 879713234491560605358489600 }, some { target := 848, numerator := 32486639386872204616531968000 }, some { target := 851, numerator := 32486631431713822829287833600 }, some { target := 858, numerator := 879721189649942392602624000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 27095167622340066645041479680 }, some { target := 897, numerator := 1000588493115663902189184614400 }, some { target := 900, numerator := 1000588248096785743142065274880 }, some { target := 907, numerator := 27095412641218225692160819200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 15307010280153154533237719040 }, some { target := 923, numerator := 565267525331576360327656243200 }, some { target := 926, numerator := 565267386911820517229608304640 }, some { target := 933, numerator := 15307148699908997631285657600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 1055655881389872726430187520 }, some { target := 968, numerator := 38983967264246645539838361600 }, some { target := 971, numerator := 38983957718056587395145400320 }, some { target := 978, numerator := 1055665427579930871123148800 }]

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
def data : BetaFourLocalSlotData := ⟨4, 57, #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 64601973485656746523361280 }, some { target := 57, numerator := 1085313154559033341592469504 }, some { target := 58, numerator := 2351511834877905573450350592 }, some { target := 59, numerator := 77522368182788095828033536 }, some { target := 60, numerator := 1240357890924609533248536576 }, some { target := 61, numerator := 90442762879919445132705792 }, some { target := 62, numerator := 2351511834877905573450350592 }, some { target := 63, numerator := 2351511834877905573450350592 }, some { target := 64, numerator := 1240357890924609533248536576 }, some { target := 65, numerator := 29019206489757010538293886976 }, some { target := 66, numerator := 2325671045483642874841006080 }, some { target := 67, numerator := 1085313154559033341592469504 }, some { target := 68, numerator := 2351511834877905573450350592 }, some { target := 69, numerator := 90442762879919445132705792 }, some { target := 70, numerator := 2325671045483642874841006080 }, some { target := 71, numerator := 90442762879919445132705792 }, some { target := 72, numerator := 2351511834877905573450350592 }, some { target := 73, numerator := 2351511834877905573450350592 }, some { target := 74, numerator := 77522368182788095828033536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 91, numerator := 63256099038038897637457920 }, some { target := 92, numerator := 1062702463839053480309293056 }, some { target := 93, numerator := 2302522004984615874003468288 }, some { target := 94, numerator := 75907318845646677164949504 }, some { target := 95, numerator := 1214517101530346834639192064 }, some { target := 96, numerator := 88558538653254456692441088 }, some { target := 97, numerator := 2302522004984615874003468288 }, some { target := 98, numerator := 2302522004984615874003468288 }, some { target := 99, numerator := 1214517101530346834639192064 }, some { target := 100, numerator := 28414639687887072818746097664 }, some { target := 101, numerator := 2277219565369400314948485120 }, some { target := 102, numerator := 1062702463839053480309293056 }, some { target := 103, numerator := 2302522004984615874003468288 }, some { target := 104, numerator := 88558538653254456692441088 }, some { target := 105, numerator := 2277219565369400314948485120 }, some { target := 106, numerator := 88558538653254456692441088 }, some { target := 107, numerator := 2302522004984615874003468288 }, some { target := 108, numerator := 2302522004984615874003468288 }, some { target := 109, numerator := 75907318845646677164949504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 49797354561860408778424320 }, some { target := 153, numerator := 836595556639254867477528576 }, some { target := 154, numerator := 1812623706051718879534645248 }, some { target := 155, numerator := 59756825474232490534109184 }, some { target := 156, numerator := 956109207587719848545746944 }, some { target := 157, numerator := 69716296386604572289794048 }, some { target := 158, numerator := 1812623706051718879534645248 }, some { target := 159, numerator := 1812623706051718879534645248 }, some { target := 160, numerator := 956109207587719848545746944 }, some { target := 161, numerator := 22368971669187695623268204544 }, some { target := 162, numerator := 1792704764226974716023275520 }, some { target := 163, numerator := 836595556639254867477528576 }, some { target := 164, numerator := 1812623706051718879534645248 }, some { target := 165, numerator := 69716296386604572289794048 }, some { target := 166, numerator := 1792704764226974716023275520 }, some { target := 167, numerator := 69716296386604572289794048 }, some { target := 168, numerator := 1812623706051718879534645248 }, some { target := 169, numerator := 1812623706051718879534645248 }, some { target := 170, numerator := 59756825474232490534109184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 1565251982579558254305607680 }, some { target := 188, numerator := 26296233307336578672334209024 }, some { target := 189, numerator := 56975172165895920456724119552 }, some { target := 190, numerator := 1878302379095469905166729216 }, some { target := 191, numerator := 30052838065527518482667667456 }, some { target := 192, numerator := 2191352775611381556027850752 }, some { target := 193, numerator := 56975172165895920456724119552 }, some { target := 194, numerator := 56975172165895920456724119552 }, some { target := 195, numerator := 30052838065527518482667667456 }, some { target := 196, numerator := 703111190574737567834078969856 }, some { target := 197, numerator := 56349071372864097155001876480 }, some { target := 198, numerator := 26296233307336578672334209024 }, some { target := 199, numerator := 56975172165895920456724119552 }, some { target := 200, numerator := 2191352775611381556027850752 }, some { target := 201, numerator := 56349071372864097155001876480 }, some { target := 202, numerator := 2191352775611381556027850752 }, some { target := 203, numerator := 56975172165895920456724119552 }, some { target := 204, numerator := 56975172165895920456724119552 }, some { target := 205, numerator := 1878302379095469905166729216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 222, numerator := 49797354561860408778424320 }, some { target := 223, numerator := 836595556639254867477528576 }, some { target := 224, numerator := 1812623706051718879534645248 }, some { target := 225, numerator := 59756825474232490534109184 }, some { target := 226, numerator := 956109207587719848545746944 }, some { target := 227, numerator := 69716296386604572289794048 }, some { target := 228, numerator := 1812623706051718879534645248 }, some { target := 229, numerator := 1812623706051718879534645248 }, some { target := 230, numerator := 956109207587719848545746944 }, some { target := 231, numerator := 22368971669187695623268204544 }, some { target := 232, numerator := 1792704764226974716023275520 }, some { target := 233, numerator := 836595556639254867477528576 }, some { target := 234, numerator := 1812623706051718879534645248 }, some { target := 235, numerator := 69716296386604572289794048 }, some { target := 236, numerator := 1792704764226974716023275520 }, some { target := 237, numerator := 69716296386604572289794048 }, some { target := 238, numerator := 1812623706051718879534645248 }, some { target := 239, numerator := 1812623706051718879534645248 }, some { target := 240, numerator := 59756825474232490534109184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 49797354561860408778424320 }, some { target := 284, numerator := 836595556639254867477528576 }, some { target := 285, numerator := 1812623706051718879534645248 }, some { target := 286, numerator := 59756825474232490534109184 }, some { target := 287, numerator := 956109207587719848545746944 }, some { target := 288, numerator := 69716296386604572289794048 }, some { target := 289, numerator := 1812623706051718879534645248 }, some { target := 290, numerator := 1812623706051718879534645248 }, some { target := 291, numerator := 956109207587719848545746944 }, some { target := 292, numerator := 22368971669187695623268204544 }, some { target := 293, numerator := 1792704764226974716023275520 }, some { target := 294, numerator := 836595556639254867477528576 }, some { target := 295, numerator := 1812623706051718879534645248 }, some { target := 296, numerator := 69716296386604572289794048 }, some { target := 297, numerator := 1792704764226974716023275520 }, some { target := 298, numerator := 69716296386604572289794048 }, some { target := 299, numerator := 1812623706051718879534645248 }, some { target := 300, numerator := 1812623706051718879534645248 }, some { target := 301, numerator := 59756825474232490534109184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 318, numerator := 51143229009478257664327680 }, some { target := 319, numerator := 859206247359234728760705024 }, some { target := 320, numerator := 1861613535945008578981527552 }, some { target := 321, numerator := 61371874811373909197193216 }, some { target := 322, numerator := 981949996981982547155091456 }, some { target := 323, numerator := 71600520613269560730058752 }, some { target := 324, numerator := 1861613535945008578981527552 }, some { target := 325, numerator := 1861613535945008578981527552 }, some { target := 326, numerator := 981949996981982547155091456 }, some { target := 327, numerator := 22973538471057633342815993856 }, some { target := 328, numerator := 1841156244341217275915796480 }, some { target := 329, numerator := 859206247359234728760705024 }, some { target := 330, numerator := 1861613535945008578981527552 }, some { target := 331, numerator := 71600520613269560730058752 }, some { target := 332, numerator := 1841156244341217275915796480 }, some { target := 333, numerator := 71600520613269560730058752 }, some { target := 334, numerator := 1861613535945008578981527552 }, some { target := 335, numerator := 1861613535945008578981527552 }, some { target := 336, numerator := 61371874811373909197193216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 419, numerator := 51143229009478257664327680 }, some { target := 420, numerator := 859206247359234728760705024 }, some { target := 421, numerator := 1861613535945008578981527552 }, some { target := 422, numerator := 61371874811373909197193216 }, some { target := 423, numerator := 981949996981982547155091456 }, some { target := 424, numerator := 71600520613269560730058752 }, some { target := 425, numerator := 1861613535945008578981527552 }, some { target := 426, numerator := 1861613535945008578981527552 }, some { target := 427, numerator := 981949996981982547155091456 }, some { target := 428, numerator := 22973538471057633342815993856 }, some { target := 429, numerator := 1841156244341217275915796480 }, some { target := 430, numerator := 859206247359234728760705024 }, some { target := 431, numerator := 1861613535945008578981527552 }, some { target := 432, numerator := 71600520613269560730058752 }, some { target := 433, numerator := 1841156244341217275915796480 }, some { target := 434, numerator := 71600520613269560730058752 }, some { target := 435, numerator := 1861613535945008578981527552 }, some { target := 436, numerator := 1861613535945008578981527552 }, some { target := 437, numerator := 61371874811373909197193216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 454, numerator := 865397269818276833635860480 }, some { target := 455, numerator := 14538674132947050805082456064 }, some { target := 456, numerator := 31500460621385276744345321472 }, some { target := 457, numerator := 1038476723781932200363032576 }, some { target := 458, numerator := 16615627580510915205808521216 }, some { target := 459, numerator := 1211556177745587567090204672 }, some { target := 460, numerator := 31500460621385276744345321472 }, some { target := 461, numerator := 31500460621385276744345321472 }, some { target := 462, numerator := 16615627580510915205808521216 }, some { target := 463, numerator := 388736453602369953669228527616 }, some { target := 464, numerator := 31154301713457966010890977280 }, some { target := 465, numerator := 14538674132947050805082456064 }, some { target := 466, numerator := 31500460621385276744345321472 }, some { target := 467, numerator := 1211556177745587567090204672 }, some { target := 468, numerator := 31154301713457966010890977280 }, some { target := 469, numerator := 1211556177745587567090204672 }, some { target := 470, numerator := 31500460621385276744345321472 }, some { target := 471, numerator := 31500460621385276744345321472 }, some { target := 472, numerator := 1038476723781932200363032576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 489, numerator := 47105605666624711006617600 }, some { target := 490, numerator := 791374175199295144911175680 }, some { target := 491, numerator := 1714644046265139480640880640 }, some { target := 492, numerator := 56526726799949653207941120 }, some { target := 493, numerator := 904427628799194451327057920 }, some { target := 494, numerator := 65947847933274595409264640 }, some { target := 495, numerator := 1714644046265139480640880640 }, some { target := 496, numerator := 1714644046265139480640880640 }, some { target := 497, numerator := 904427628799194451327057920 }, some { target := 498, numerator := 21159838065447820184172625920 }, some { target := 499, numerator := 1695801803998489596238233600 }, some { target := 500, numerator := 791374175199295144911175680 }, some { target := 501, numerator := 1714644046265139480640880640 }, some { target := 502, numerator := 65947847933274595409264640 }, some { target := 503, numerator := 1695801803998489596238233600 }, some { target := 504, numerator := 65947847933274595409264640 }, some { target := 505, numerator := 1714644046265139480640880640 }, some { target := 506, numerator := 1714644046265139480640880640 }, some { target := 507, numerator := 56526726799949653207941120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 550, numerator := 1565251982579558254305607680 }, some { target := 551, numerator := 26296233307336578672334209024 }, some { target := 552, numerator := 56975172165895920456724119552 }, some { target := 553, numerator := 1878302379095469905166729216 }, some { target := 554, numerator := 30052838065527518482667667456 }, some { target := 555, numerator := 2191352775611381556027850752 }, some { target := 556, numerator := 56975172165895920456724119552 }, some { target := 557, numerator := 56975172165895920456724119552 }, some { target := 558, numerator := 30052838065527518482667667456 }, some { target := 559, numerator := 703111190574737567834078969856 }, some { target := 560, numerator := 56349071372864097155001876480 }, some { target := 561, numerator := 26296233307336578672334209024 }, some { target := 562, numerator := 56975172165895920456724119552 }, some { target := 563, numerator := 2191352775611381556027850752 }, some { target := 564, numerator := 56349071372864097155001876480 }, some { target := 565, numerator := 2191352775611381556027850752 }, some { target := 566, numerator := 56975172165895920456724119552 }, some { target := 567, numerator := 56975172165895920456724119552 }, some { target := 568, numerator := 1878302379095469905166729216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 585, numerator := 865397269818276833635860480 }, some { target := 586, numerator := 14538674132947050805082456064 }, some { target := 587, numerator := 31500460621385276744345321472 }, some { target := 588, numerator := 1038476723781932200363032576 }, some { target := 589, numerator := 16615627580510915205808521216 }, some { target := 590, numerator := 1211556177745587567090204672 }, some { target := 591, numerator := 31500460621385276744345321472 }, some { target := 592, numerator := 31500460621385276744345321472 }, some { target := 593, numerator := 16615627580510915205808521216 }, some { target := 594, numerator := 388736453602369953669228527616 }, some { target := 595, numerator := 31154301713457966010890977280 }, some { target := 596, numerator := 14538674132947050805082456064 }, some { target := 597, numerator := 31500460621385276744345321472 }, some { target := 598, numerator := 1211556177745587567090204672 }, some { target := 599, numerator := 31154301713457966010890977280 }, some { target := 600, numerator := 1211556177745587567090204672 }, some { target := 601, numerator := 31500460621385276744345321472 }, some { target := 602, numerator := 31500460621385276744345321472 }, some { target := 603, numerator := 1038476723781932200363032576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 64601973485656746523361280 }, some { target := 661, numerator := 1085313154559033341592469504 }, some { target := 662, numerator := 2351511834877905573450350592 }, some { target := 663, numerator := 77522368182788095828033536 }, some { target := 664, numerator := 1240357890924609533248536576 }, some { target := 665, numerator := 90442762879919445132705792 }, some { target := 666, numerator := 2351511834877905573450350592 }, some { target := 667, numerator := 2351511834877905573450350592 }, some { target := 668, numerator := 1240357890924609533248536576 }, some { target := 669, numerator := 29019206489757010538293886976 }, some { target := 670, numerator := 2325671045483642874841006080 }, some { target := 671, numerator := 1085313154559033341592469504 }, some { target := 672, numerator := 2351511834877905573450350592 }, some { target := 673, numerator := 90442762879919445132705792 }, some { target := 674, numerator := 2325671045483642874841006080 }, some { target := 675, numerator := 90442762879919445132705792 }, some { target := 676, numerator := 2351511834877905573450350592 }, some { target := 677, numerator := 2351511834877905573450350592 }, some { target := 678, numerator := 77522368182788095828033536 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 766, numerator := 49797354561860408778424320 }, some { target := 767, numerator := 836595556639254867477528576 }, some { target := 768, numerator := 1812623706051718879534645248 }, some { target := 769, numerator := 59756825474232490534109184 }, some { target := 770, numerator := 956109207587719848545746944 }, some { target := 771, numerator := 69716296386604572289794048 }, some { target := 772, numerator := 1812623706051718879534645248 }, some { target := 773, numerator := 1812623706051718879534645248 }, some { target := 774, numerator := 956109207587719848545746944 }, some { target := 775, numerator := 22368971669187695623268204544 }, some { target := 776, numerator := 1792704764226974716023275520 }, some { target := 777, numerator := 836595556639254867477528576 }, some { target := 778, numerator := 1812623706051718879534645248 }, some { target := 779, numerator := 69716296386604572289794048 }, some { target := 780, numerator := 1792704764226974716023275520 }, some { target := 781, numerator := 69716296386604572289794048 }, some { target := 782, numerator := 1812623706051718879534645248 }, some { target := 783, numerator := 1812623706051718879534645248 }, some { target := 784, numerator := 59756825474232490534109184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 801, numerator := 47105605666624711006617600 }, some { target := 802, numerator := 791374175199295144911175680 }, some { target := 803, numerator := 1714644046265139480640880640 }, some { target := 804, numerator := 56526726799949653207941120 }, some { target := 805, numerator := 904427628799194451327057920 }, some { target := 806, numerator := 65947847933274595409264640 }, some { target := 807, numerator := 1714644046265139480640880640 }, some { target := 808, numerator := 1714644046265139480640880640 }, some { target := 809, numerator := 904427628799194451327057920 }, some { target := 810, numerator := 21159838065447820184172625920 }, some { target := 811, numerator := 1695801803998489596238233600 }, some { target := 812, numerator := 791374175199295144911175680 }, some { target := 813, numerator := 1714644046265139480640880640 }, some { target := 814, numerator := 65947847933274595409264640 }, some { target := 815, numerator := 1695801803998489596238233600 }, some { target := 816, numerator := 65947847933274595409264640 }, some { target := 817, numerator := 1714644046265139480640880640 }, some { target := 818, numerator := 1714644046265139480640880640 }, some { target := 819, numerator := 56526726799949653207941120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 876, numerator := 63256099038038897637457920 }, some { target := 877, numerator := 1062702463839053480309293056 }, some { target := 878, numerator := 2302522004984615874003468288 }, some { target := 879, numerator := 75907318845646677164949504 }, some { target := 880, numerator := 1214517101530346834639192064 }, some { target := 881, numerator := 88558538653254456692441088 }, some { target := 882, numerator := 2302522004984615874003468288 }, some { target := 883, numerator := 2302522004984615874003468288 }, some { target := 884, numerator := 1214517101530346834639192064 }, some { target := 885, numerator := 28414639687887072818746097664 }, some { target := 886, numerator := 2277219565369400314948485120 }, some { target := 887, numerator := 1062702463839053480309293056 }, some { target := 888, numerator := 2302522004984615874003468288 }, some { target := 889, numerator := 88558538653254456692441088 }, some { target := 890, numerator := 2277219565369400314948485120 }, some { target := 891, numerator := 88558538653254456692441088 }, some { target := 892, numerator := 2302522004984615874003468288 }, some { target := 893, numerator := 2302522004984615874003468288 }, some { target := 894, numerator := 75907318845646677164949504 }]

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

end Slot4

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot5

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1
