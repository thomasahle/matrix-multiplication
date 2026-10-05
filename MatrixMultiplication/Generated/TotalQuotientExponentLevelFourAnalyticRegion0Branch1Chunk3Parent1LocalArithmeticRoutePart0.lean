import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 165904737643817831843758080 }, { target := 15, numerator := 7401524510697445726032494592 }, { target := 20, numerator := 7401773496356289660246294528 }, { target := 28, numerator := 165892107936485168514072576 }, { target := 56, numerator := 2896021161343284689240064 }, { target := 57, numerator := 86285305608274952201437184 }, { target := 59, numerator := 919123677183714955771248640 }, { target := 67, numerator := 86526329853800166706905088 }, { target := 74, numerator := 3109428727093413525061632 }, { target := 110, numerator := 6769852006796233348743168 }, { target := 112, numerator := 232569240203721282567536640 }, { target := 115, numerator := 232568897826566810980319232 }, { target := 122, numerator := 6769966132514390544482304 }, { target := 136, numerator := 536561412837694513013063680 }, { target := 137, numerator := 23937667513382392789867692032 }, { target := 142, numerator := 23938472771259792554341695488 }, { target := 150, numerator := 536520566423623510467280896 }, { target := 152, numerator := 101593296260750476365004800 }, { target := 153, numerator := 3026914558712983929539788800 }, { target := 155, numerator := 32243135955914018833563648000 }, { target := 163, numerator := 3035369761978939774441881600 }, { target := 170, numerator := 109079698066420313515622400 }, { target := 206, numerator := 288645187016655289140117504 }, { target := 208, numerator := 9916020581474006504224849920 }, { target := 211, numerator := 9916005983589490938605469696 }, { target := 218, numerator := 288650052978160477679910912 }, { target := 257, numerator := 138492817396453407908167680 }, { target := 260, numerator := 472699387078950442045014016 }, { target := 262, numerator := 138511808879049545592340480 }, { target := 267, numerator := 166000657550629758167941120 }, { target := 268, numerator := 7405803795010932254324031488 }, { target := 273, numerator := 7406052924623960577715208192 }, { target := 281, numerator := 165988020541273249010417664 }, { target := 283, numerator := 101592959945722578195185664 }, { target := 284, numerator := 3026904538397749289139830784 }, { target := 286, numerator := 32243029218052686863809904640 }, { target := 294, numerator := 3035359713673551974957580288 }, { target := 301, numerator := 109079336968365140902674432 }, { target := 302, numerator := 2770694974557152054825975808 }, { target := 304, numerator := 95183531991856872114974883840 }, { target := 307, numerator := 95183391867278026774614638592 }, { target := 314, numerator := 2770741682750100501612724224 }, { target := 353, numerator := 7179378637939283078959595520 }, { target := 356, numerator := 24504432399889327386026573824 }, { target := 358, numerator := 7180363144190341541496094720 }, { target := 660, numerator := 2896606598614070392258560 }, { target := 661, numerator := 86302748379238955860623360 }, { target := 663, numerator := 919309480127515051268505600 }, { target := 671, numerator := 86543821348364113957355520 }, { target := 678, numerator := 3110057305189454740193280 }, { target := 679, numerator := 288647591368025052215771136 }, { target := 681, numerator := 9916103179759860791409377280 }, { target := 684, numerator := 9916088581753748035850993664 }, { target := 691, numerator := 288652457370062637401899008 }, { target := 695, numerator := 7180706374012737953653063680 }, { target := 698, numerator := 24508964187457256551367049216 }, { target := 700, numerator := 7181691062335885101477396480 }, { target := 966, numerator := 6769250918953792579829760 }, { target := 968, numerator := 232548590632257710771404800 }, { target := 971, numerator := 232548248285502536668938240 }, { target := 978, numerator := 6769365034538850613985280 }, { target := 982, numerator := 137240104517687836252569600 }, { target := 985, numerator := 468423666351259061342699520 }, { target := 987, numerator := 137258924216105687423385600 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left6.expected,
    Slot15.Left14.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 138492817396453407908167680 }, { target := 15, numerator := 7179378637939283078959595520 }, { target := 20, numerator := 7180706374012737953653063680 }, { target := 28, numerator := 137240104517687836252569600 }, { target := 56, numerator := 8071857501807515648655360 }, { target := 57, numerator := 406874741948820900995399680 }, { target := 59, numerator := 4468977889172463463138590720 }, { target := 67, numerator := 406877584485797708431360000 }, { target := 74, numerator := 8070909989481913170001920 }, { target := 110, numerator := 8071857501807515648655360 }, { target := 112, numerator := 293515083699925705839083520 }, { target := 115, numerator := 293651799131821695282708480 }, { target := 122, numerator := 8208860679942696861696000 }, { target := 136, numerator := 472699387078950442045014016 }, { target := 137, numerator := 24504432399889327386026573824 }, { target := 142, numerator := 24508964187457256551367049216 }, { target := 150, numerator := 468423666351259061342699520 }, { target := 152, numerator := 293515083699925705839083520 }, { target := 153, numerator := 14795091949003247298816245760 }, { target := 155, numerator := 162504407306477308224775127040 }, { target := 163, numerator := 14795195311516582171115520000 }, { target := 170, numerator := 293480629528814081739325440 }, { target := 206, numerator := 406874741948820900995399680 }, { target := 208, numerator := 14795091949003247298816245760 }, { target := 211, numerator := 14801983306545256194103050240 }, { target := 218, numerator := 413780603795048704770048000 }, { target := 257, numerator := 165904737643817831843758080 }, { target := 260, numerator := 536561412837694513013063680 }, { target := 262, numerator := 166000657550629758167941120 }, { target := 267, numerator := 138511808879049545592340480 }, { target := 268, numerator := 7180363144190341541496094720 }, { target := 273, numerator := 7181691062335885101477396480 }, { target := 281, numerator := 137258924216105687423385600 }, { target := 283, numerator := 293651799131821695282708480 }, { target := 284, numerator := 14801983306545256194103050240 }, { target := 286, numerator := 162580099703439844468284456960 }, { target := 294, numerator := 14802086717203478457876480000 }, { target := 301, numerator := 293617328912414274024898560 }, { target := 302, numerator := 4468977889172463463138590720 }, { target := 304, numerator := 162504407306477308224775127040 }, { target := 307, numerator := 162580099703439844468284456960 }, { target := 314, numerator := 4544829596625844297531392000 }, { target := 353, numerator := 7401524510697445726032494592 }, { target := 356, numerator := 23937667513382392789867692032 }, { target := 358, numerator := 7405803795010932254324031488 }, { target := 660, numerator := 8208860679942696861696000 }, { target := 661, numerator := 413780603795048704770048000 }, { target := 663, numerator := 4544829596625844297531392000 }, { target := 671, numerator := 413783494578243895296000000 }, { target := 678, numerator := 8207897085544300019712000 }, { target := 679, numerator := 406877584485797708431360000 }, { target := 681, numerator := 14795195311516582171115520000 }, { target := 684, numerator := 14802086717203478457876480000 }, { target := 691, numerator := 413783494578243895296000000 }, { target := 695, numerator := 7401773496356289660246294528 }, { target := 698, numerator := 23938472771259792554341695488 }, { target := 700, numerator := 7406052924623960577715208192 }, { target := 966, numerator := 8070909989481913170001920 }, { target := 968, numerator := 293480629528814081739325440 }, { target := 971, numerator := 293617328912414274024898560 }, { target := 978, numerator := 8207897085544300019712000 }, { target := 982, numerator := 165892107936485168514072576 }, { target := 985, numerator := 536520566423623510467280896 }, { target := 987, numerator := 165988020541273249010417664 }]

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
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left3.expected,
    Slot21.Left11.expected,
    Slot21.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6769852006796233348743168 }, { target := 57, numerator := 288645187016655289140117504 }, { target := 59, numerator := 2770694974557152054825975808 }, { target := 67, numerator := 288647591368025052215771136 }, { target := 74, numerator := 6769250918953792579829760 }, { target := 110, numerator := 2896021161343284689240064 }, { target := 112, numerator := 101593296260750476365004800 }, { target := 115, numerator := 101592959945722578195185664 }, { target := 122, numerator := 2896606598614070392258560 }, { target := 152, numerator := 232569240203721282567536640 }, { target := 153, numerator := 9916020581474006504224849920 }, { target := 155, numerator := 95183531991856872114974883840 }, { target := 163, numerator := 9916103179759860791409377280 }, { target := 170, numerator := 232548590632257710771404800 }, { target := 206, numerator := 86285305608274952201437184 }, { target := 208, numerator := 3026914558712983929539788800 }, { target := 211, numerator := 3026904538397749289139830784 }, { target := 218, numerator := 86302748379238955860623360 }, { target := 283, numerator := 232568897826566810980319232 }, { target := 284, numerator := 9916005983589490938605469696 }, { target := 286, numerator := 95183391867278026774614638592 }, { target := 294, numerator := 9916088581753748035850993664 }, { target := 301, numerator := 232548248285502536668938240 }, { target := 302, numerator := 919123677183714955771248640 }, { target := 304, numerator := 32243135955914018833563648000 }, { target := 307, numerator := 32243029218052686863809904640 }, { target := 314, numerator := 919309480127515051268505600 }, { target := 660, numerator := 6769966132514390544482304 }, { target := 661, numerator := 288650052978160477679910912 }, { target := 663, numerator := 2770741682750100501612724224 }, { target := 671, numerator := 288652457370062637401899008 }, { target := 678, numerator := 6769365034538850613985280 }, { target := 679, numerator := 86526329853800166706905088 }, { target := 681, numerator := 3035369761978939774441881600 }, { target := 684, numerator := 3035359713673551974957580288 }, { target := 691, numerator := 86543821348364113957355520 }, { target := 966, numerator := 3109428727093413525061632 }, { target := 968, numerator := 109079698066420313515622400 }, { target := 971, numerator := 109079336968365140902674432 }, { target := 978, numerator := 3110057305189454740193280 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent1
