import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 34427058918886822643761152 }, { target := 27, numerator := 904925211228802696498642944 }, { target := 29, numerator := 12436882728300252238257848320 }, { target := 37, numerator := 901432944839300413193715712 }, { target := 44, numerator := 33643132975566696029880320 }, { target := 80, numerator := 28619696727524999883128832 }, { target := 82, numerator := 997935168118592181828059136 }, { target := 85, numerator := 998401538882689166783545344 }, { target := 92, numerator := 28153815463049213547380736 }, { target := 131, numerator := 116242761665902973804347392 }, { target := 134, numerator := 412255376667871513130565632 }, { target := 136, numerator := 116241835205935304445788160 }, { target := 157, numerator := 121737041129366627624681472 }, { target := 158, numerator := 3199893372184799627899305984 }, { target := 160, numerator := 43977886922707611634127339520 }, { target := 168, numerator := 3187544417890004737701445632 }, { target := 175, numerator := 118965011574672806400491520 }, { target := 176, numerator := 1628002598776208614773227520 }, { target := 178, numerator := 56766536087880407880522792960 }, { target := 181, numerator := 56793065118679428404965539840 }, { target := 188, numerator := 1601501412669708710140968960 }, { target := 227, numerator := 2777522198991739547214151680 }, { target := 230, numerator := 9849274135942245470393335808 }, { target := 232, numerator := 2777497019056037494435872768 }, { target := 267, numerator := 34425888833882560911114240 }, { target := 268, numerator := 904894455205695061261025280 }, { target := 270, numerator := 12436460031432232458937958400 }, { target := 278, numerator := 901402307509123907258941440 }, { target := 285, numerator := 33641989534139304797798400 }, { target := 286, numerator := 1628009510744698090936074240 }, { target := 288, numerator := 56766777100093159315624427520 }, { target := 291, numerator := 56793306243525799145719726080 }, { target := 298, numerator := 1601508212122798370869739520 }, { target := 302, numerator := 37074210255069719197250486272 }, { target := 305, numerator := 131462259052666427528852799488 }, { target := 307, numerator := 37073860921500170461397385216 }, { target := 573, numerator := 28613574698291463853178880 }, { target := 575, numerator := 997721700158726625023754240 }, { target := 578, numerator := 998187971161617939258408960 }, { target := 585, numerator := 28147793090312656901898240 }, { target := 589, numerator := 2773985694102259673809813504 }, { target := 592, numerator := 9836768095722026827943772160 }, { target := 594, numerator := 2773960632727758461233790976 }, { target := 763, numerator := 115460537203351216040443904 }, { target := 766, numerator := 409489388879540143916056576 }, { target := 768, numerator := 115459637392026966763241472 }]

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
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 81815702747016151160586240 }, { target := 27, numerator := 1872596987762936850715508736 }, { target := 29, numerator := 24637327526769466958992637952 }, { target := 37, numerator := 1872552749262959260616097792 }, { target := 44, numerator := 81817404227784520010563584 }, { target := 80, numerator := 28619696727524999883128832 }, { target := 82, numerator := 1628002598776208614773227520 }, { target := 85, numerator := 1628009510744698090936074240 }, { target := 92, numerator := 28613574698291463853178880 }, { target := 157, numerator := 290518335538504885505884160 }, { target := 158, numerator := 6649380763757445842494029824 }, { target := 160, numerator := 87484372129958815894725459968 }, { target := 168, numerator := 6649223677832022090242326528 }, { target := 175, numerator := 290524377304867337515565056 }, { target := 176, numerator := 997935168118592181828059136 }, { target := 178, numerator := 56766536087880407880522792960 }, { target := 181, numerator := 56766777100093159315624427520 }, { target := 188, numerator := 997721700158726625023754240 }, { target := 267, numerator := 81815946372052743534673920 }, { target := 268, numerator := 1872602563850342433174847488 }, { target := 270, numerator := 24637400890067938002459426816 }, { target := 278, numerator := 1872558325218634553974849536 }, { target := 285, numerator := 81817647857887661965443072 }, { target := 286, numerator := 998401538882689166783545344 }, { target := 288, numerator := 56793065118679428404965539840 }, { target := 291, numerator := 56793306243525799145719726080 }, { target := 298, numerator := 998187971161617939258408960 }, { target := 573, numerator := 28153815463049213547380736 }, { target := 575, numerator := 1601501412669708710140968960 }, { target := 578, numerator := 1601508212122798370869739520 }, { target := 585, numerator := 28147793090312656901898240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent2
