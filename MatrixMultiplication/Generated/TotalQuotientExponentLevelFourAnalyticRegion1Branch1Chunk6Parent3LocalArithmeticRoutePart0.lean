import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 29; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20727118179889508853951234048 }, { target := 2, numerator := 811168418214692652571032551424 }, { target := 5, numerator := 811168588219886035878260244480 }, { target := 12, numerator := 20727288185082892161178927104 }, { target := 16, numerator := 464852401240450658347094376448 }, { target := 19, numerator := 1672255927004463087022933803008 }, { target := 21, numerator := 464964263080500256200749744128 }, { target := 26, numerator := 814069663989327675118187446272 }, { target := 28, numerator := 814070243047799027805437558784 }, { target := 30, numerator := 50704925561966623521620623360 }, { target := 33, numerator := 188356162653538982081173913600 }, { target := 35, numerator := 50694252229728714990781726720 }, { target := 40, numerator := 140515849114651037801568534528 }, { target := 42, numerator := 140515882616244118667327963136 }, { target := 44, numerator := 14391052956692545695702319104 }, { target := 45, numerator := 7292239674612628708265033728 }, { target := 47, numerator := 7292241413218257655390273536 }, { target := 49, numerator := 16247963015620616108051005440 }, { target := 50, numerator := 464852401240450658347094376448 }, { target := 53, numerator := 1672255927004463087022933803008 }, { target := 55, numerator := 464964263080500256200749744128 }, { target := 60, numerator := 151173737869854110529032814592 }, { target := 62, numerator := 151173773912486187548282978304 }, { target := 64, numerator := 13926825441960528092615147520 }, { target := 65, numerator := 226339900669707360291149316096 }, { target := 67, numerator := 226339954633351304919228874752 }, { target := 69, numerator := 183369868319146953219432775680 }, { target := 70, numerator := 16247963015620616108051005440 }, { target := 71, numerator := 7011768917896758373331763200 }, { target := 73, numerator := 7011770589632940053259878400 }, { target := 75, numerator := 13926825441960528092615147520 }, { target := 76, numerator := 16247963015620616108051005440 }, { target := 77, numerator := 50704925561966623521620623360 }, { target := 80, numerator := 188356162653538982081173913600 }, { target := 82, numerator := 50694252229728714990781726720 }, { target := 87, numerator := 226339900669707360291149316096 }, { target := 89, numerator := 226339954633351304919228874752 }, { target := 91, numerator := 16247963015620616108051005440 }, { target := 92, numerator := 235875906398046951678880514048 }, { target := 94, numerator := 235875962635252103391662309376 }, { target := 96, numerator := 673594123876157542079485968384 }, { target := 97, numerator := 16712190530352633711138177024 }, { target := 98, numerator := 140515849114651037801568534528 }, { target := 100, numerator := 140515882616244118667327963136 }, { target := 102, numerator := 183369868319146953219432775680 }, { target := 103, numerator := 673594123876157542079485968384 }, { target := 104, numerator := 14391052956692545695702319104 }, { target := 105, numerator := 7011768917896758373331763200 }, { target := 107, numerator := 7011770589632940053259878400 }, { target := 109, numerator := 16247963015620616108051005440 }, { target := 110, numerator := 16712190530352633711138177024 }, { target := 111, numerator := 16247963015620616108051005440 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 40491227774759825307699511296 }, { target := 1, numerator := 16247963015620616108051005440 }, { target := 2, numerator := 1057406972070356843473882054656 }, { target := 3, numerator := 183369868319146953219432775680 }, { target := 4, numerator := 16247963015620616108051005440 }, { target := 5, numerator := 1057406717062566768513040515072 }, { target := 6, numerator := 16247963015620616108051005440 }, { target := 7, numerator := 16247963015620616108051005440 }, { target := 8, numerator := 673594123876157542079485968384 }, { target := 9, numerator := 16712190530352633711138177024 }, { target := 10, numerator := 183369868319146953219432775680 }, { target := 11, numerator := 673594123876157542079485968384 }, { target := 12, numerator := 40491227774759825307699511296 }, { target := 13, numerator := 16247963015620616108051005440 }, { target := 14, numerator := 16712190530352633711138177024 }, { target := 15, numerator := 16247963015620616108051005440 }, { target := 16, numerator := 806817216643734853843905675264 }, { target := 17, numerator := 135670475007249277877376516096 }, { target := 18, numerator := 7040783134108744959704170496 }, { target := 19, numerator := 3061327895846744386675675234304 }, { target := 20, numerator := 218535076508682968556971753472 }, { target := 21, numerator := 807088554344633246905532416000 }, { target := 22, numerator := 218535076508682968556971753472 }, { target := 23, numerator := 227742254453286711965815668736 }, { target := 24, numerator := 135670475007249277877376516096 }, { target := 25, numerator := 6769983782796870153561702400 }, { target := 26, numerator := 425600493072401881793675919360 }, { target := 28, numerator := 425600493072401881793675919360 }, { target := 44, numerator := 37944096630695527550917017600 }, { target := 50, numerator := 806817790625530281977205227520 }, { target := 51, numerator := 135670507353615011127075274752 }, { target := 52, numerator := 7040784812762455667273367552 }, { target := 53, numerator := 3061330015880278454914535915520 }, { target := 54, numerator := 218535128611511604749600292864 }, { target := 55, numerator := 807089128391377337064955576320 }, { target := 56, numerator := 218535128611511604749600292864 }, { target := 57, numerator := 227742308751277892929880850432 }, { target := 58, numerator := 135670507353615011127075274752 }, { target := 59, numerator := 6769985396886976603147468800 }, { target := 60, numerator := 4466460651130457943377151262720 }, { target := 62, numerator := 4466462754655733451415449763840 }, { target := 64, numerator := 1507005029896160709696383090688 }, { target := 71, numerator := 1233063080750686337156880793600 }, { target := 73, numerator := 1233063658204679390899260620800 }, { target := 75, numerator := 1507004944893564018042769244160 }, { target := 104, numerator := 37944266635888910858144710656 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 43034874739308654970219266048 }, { target := 27, numerator := 47083145164683293270076293120 }, { target := 28, numerator := 43034874739308654970219266048 }, { target := 29, numerator := 47083145164683293270076293120 }, { target := 44, numerator := 8883196367261260915031408640 }, { target := 60, numerator := 159863835245466930452606484480 }, { target := 61, numerator := 174902151035429054789661491200 }, { target := 62, numerator := 159863835245466930452606484480 }, { target := 63, numerator := 174902151035429054789661491200 }, { target := 64, numerator := 347643534946928258255916367872 }, { target := 71, numerator := 43025815944510739812603396096 }, { target := 72, numerator := 47073234213319521062868746240 }, { target := 73, numerator := 43025815944510739812603396096 }, { target := 74, numerator := 47073234213319521062868746240 }, { target := 75, numerator := 347643534946928258255916367872 }, { target := 104, numerator := 8883196367261260915031408640 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6.Parent3
