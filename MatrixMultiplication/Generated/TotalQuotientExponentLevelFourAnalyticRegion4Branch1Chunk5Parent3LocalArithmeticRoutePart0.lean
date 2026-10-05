import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 11799531355466148033331200 }, { target := 57, numerator := 401023802395476935332331520 }, { target := 59, numerator := 4415632370265072113675141120 }, { target := 67, numerator := 401030050492567465461022720 }, { target := 74, numerator := 11797969331193515501158400 }, { target := 110, numerator := 20449977754900228636409856 }, { target := 112, numerator := 710508516193248172157435904 }, { target := 115, numerator := 710542879726321070682144768 }, { target := 122, numerator := 20415785526935206263521280 }, { target := 152, numerator := 434109923789500101269913600 }, { target := 153, numerator := 14753841237519095220991426560 }, { target := 155, numerator := 162453047836533587447235215360 }, { target := 163, numerator := 14754071107746148173123420160 }, { target := 170, numerator := 434052456232736863236915200 }, { target := 206, numerator := 937418984537035137815150592 }, { target := 208, numerator := 32205422130230988362372612096 }, { target := 211, numerator := 32206585926105863359918243840 }, { target := 218, numerator := 936258990585202967746445312 }, { target := 257, numerator := 121724428716419483351121920 }, { target := 260, numerator := 421871406019703327021858816 }, { target := 262, numerator := 121752546134830112720289792 }, { target := 283, numerator := 434110402198444267536384000 }, { target := 284, numerator := 14753857496925347036685926400 }, { target := 286, numerator := 162453226867204929008068198400 }, { target := 294, numerator := 14754087367405727467857510400 }, { target := 301, numerator := 434052934578349159743488000 }, { target := 302, numerator := 10416342136309839838266261504 }, { target := 304, numerator := 357591023310170635572107804672 }, { target := 307, numerator := 357603653571355418125863485440 }, { target := 314, numerator := 10403751152410145767370522624 }, { target := 353, numerator := 7125608771130174807316889600 }, { target := 356, numerator := 24695869372501099599185838080 }, { target := 358, numerator := 7127254732629941467175976960 }, { target := 660, numerator := 11799052946521981766860800 }, { target := 661, numerator := 401007542989225119637831680 }, { target := 663, numerator := 4415453339593730552842158080 }, { target := 671, numerator := 401013790832988170726932480 }, { target := 678, numerator := 11797490985581218994585600 }, { target := 679, numerator := 149062930322828842877583360 }, { target := 681, numerator := 5987080509786957418804019200 }, { target := 684, numerator := 5988244303870525664563036160 }, { target := 691, numerator := 147909377042007269299978240 }, { target := 695, numerator := 7127974264702073741582008320 }, { target := 698, numerator := 24704067678376352079503425536 }, { target := 700, numerator := 7129620772612887141188370432 }, { target := 966, numerator := 4400372394005655585816576 }, { target := 968, numerator := 176740010000468002178334720 }, { target := 971, numerator := 176774365472660517663277056 }, { target := 978, numerator := 4366319232693526786473984 }, { target := 982, numerator := 119358935144520549086003200 }, { target := 985, numerator := 413673100144450846704271360 }, { target := 987, numerator := 119386506151884438707896320 }]

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
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 139756168636600457596239872 }, { target := 15, numerator := 7183979205709078244880285696 }, { target := 20, numerator := 7185649372071317535438405632 }, { target := 28, numerator := 138154101059648498278858752 }, { target := 56, numerator := 16048572894354449715167232 }, { target := 57, numerator := 788355824777197378640805888 }, { target := 59, numerator := 8798612875155739532240879616 }, { target := 67, numerator := 788357065438392875873206272 }, { target := 74, numerator := 16046091571963455250366464 }, { target := 110, numerator := 11799531355466148033331200 }, { target := 112, numerator := 434109923789500101269913600 }, { target := 115, numerator := 434110402198444267536384000 }, { target := 122, numerator := 11799052946521981766860800 }, { target := 136, numerator := 476424974551698552360271872 }, { target := 137, numerator := 24489989555734961369640861696 }, { target := 142, numerator := 24495683107399904267580997632 }, { target := 150, numerator := 470963569792069583348170752 }, { target := 152, numerator := 533727037396440313573146624 }, { target := 153, numerator := 26218332405155955419922825216 }, { target := 155, numerator := 292615275761187642718197645312 }, { target := 163, numerator := 26218373665798172299078139904 }, { target := 170, numerator := 533644516112006555262517248 }, { target := 206, numerator := 401023802395476935332331520 }, { target := 208, numerator := 14753841237519095220991426560 }, { target := 211, numerator := 14753857496925347036685926400 }, { target := 218, numerator := 401007542989225119637831680 }, { target := 257, numerator := 139756168636600457596239872 }, { target := 260, numerator := 476424974551698552360271872 }, { target := 262, numerator := 139756393923542317271089152 }, { target := 267, numerator := 139756393923542317271089152 }, { target := 268, numerator := 7183990786283455938859892736 }, { target := 273, numerator := 7185660955338003381655437312 }, { target := 281, numerator := 138154323764057446633439232 }, { target := 283, numerator := 533727037396440313573146624 }, { target := 284, numerator := 26218332405155955419922825216 }, { target := 286, numerator := 292615275761187642718197645312 }, { target := 294, numerator := 26218373665798172299078139904 }, { target := 301, numerator := 533644516112006555262517248 }, { target := 302, numerator := 4415632370265072113675141120 }, { target := 304, numerator := 162453047836533587447235215360 }, { target := 307, numerator := 162453226867204929008068198400 }, { target := 314, numerator := 4415453339593730552842158080 }, { target := 353, numerator := 7183979205709078244880285696 }, { target := 356, numerator := 24489989555734961369640861696 }, { target := 358, numerator := 7183990786283455938859892736 }, { target := 660, numerator := 16048441817650245050302464 }, { target := 661, numerator := 788349385881730935240523776 }, { target := 663, numerator := 8798541012493256075595743232 }, { target := 671, numerator := 788350626532793333311340544 }, { target := 678, numerator := 16045960515525448908668928 }, { target := 679, numerator := 788357065438392875873206272 }, { target := 681, numerator := 26218373665798172299078139904 }, { target := 684, numerator := 26218373665798172299078139904 }, { target := 691, numerator := 788350626532793333311340544 }, { target := 695, numerator := 7185649372071317535438405632 }, { target := 698, numerator := 24495683107399904267580997632 }, { target := 700, numerator := 7185660955338003381655437312 }, { target := 966, numerator := 16046091571963455250366464 }, { target := 968, numerator := 533644516112006555262517248 }, { target := 971, numerator := 533644516112006555262517248 }, { target := 978, numerator := 16045960515525448908668928 }, { target := 982, numerator := 138154101059648498278858752 }, { target := 985, numerator := 470963569792069583348170752 }, { target := 987, numerator := 138154323764057446633439232 }]

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
    Slot17.Left11.expected,
    Slot17.Left18.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 121724428716419483351121920 }, { target := 15, numerator := 7125608771130174807316889600 }, { target := 20, numerator := 7127974264702073741582008320 }, { target := 28, numerator := 119358935144520549086003200 }, { target := 56, numerator := 4401404860545778921242624 }, { target := 57, numerator := 149063159759837759174344704 }, { target := 59, numerator := 1617729261154100306025381888 }, { target := 67, numerator := 149062930322828842877583360 }, { target := 74, numerator := 4400372394005655585816576 }, { target := 136, numerator := 421871406019703327021858816 }, { target := 137, numerator := 24695869372501099599185838080 }, { target := 142, numerator := 24704067678376352079503425536 }, { target := 150, numerator := 413673100144450846704271360 }, { target := 152, numerator := 176781478796807858584289280 }, { target := 153, numerator := 5987089725075032942449786880 }, { target := 155, numerator := 64975747548982992853910159360 }, { target := 163, numerator := 5987080509786957418804019200 }, { target := 170, numerator := 176740010000468002178334720 }, { target := 267, numerator := 121752546134830112720289792 }, { target := 268, numerator := 7127254732629941467175976960 }, { target := 273, numerator := 7129620772612887141188370432 }, { target := 281, numerator := 119386506151884438707896320 }, { target := 283, numerator := 176815842329880757108998144 }, { target := 284, numerator := 5988253520949907939995418624 }, { target := 286, numerator := 64988377810167775407665840128 }, { target := 294, numerator := 5988244303870525664563036160 }, { target := 301, numerator := 176774365472660517663277056 }, { target := 660, numerator := 4367343709284961213218816 }, { target := 661, numerator := 147909604703472032505921536 }, { target := 663, numerator := 1605210139916889691774779392 }, { target := 671, numerator := 147909377042007269299978240 }, { target := 678, numerator := 4366319232693526786473984 }, { target := 679, numerator := 401030050492567465461022720 }, { target := 681, numerator := 14754071107746148173123420160 }, { target := 684, numerator := 14754087367405727467857510400 }, { target := 691, numerator := 401013790832988170726932480 }, { target := 966, numerator := 11797969331193515501158400 }, { target := 968, numerator := 434052456232736863236915200 }, { target := 971, numerator := 434052934578349159743488000 }, { target := 978, numerator := 11797490985581218994585600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent3
