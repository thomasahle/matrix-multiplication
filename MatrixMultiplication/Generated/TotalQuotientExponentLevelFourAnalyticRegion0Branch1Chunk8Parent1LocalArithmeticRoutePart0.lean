import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 76312520525869339813871616 }, { target := 27, numerator := 2273688204770638001021648896 }, { target := 29, numerator := 24219658826098099257249628160 }, { target := 37, numerator := 2280039390296970154288873472 }, { target := 44, numerator := 81935984007099085077086208 }, { target := 80, numerator := 33771118614463866784972800 }, { target := 82, numerator := 1647302671008640927952535552 }, { target := 85, numerator := 1646688559596280609046003712 }, { target := 92, numerator := 33764506648197018326925312 }, { target := 131, numerator := 98239431381320350769872896 }, { target := 134, numerator := 342067374971041713211047936 }, { target := 136, numerator := 98340481783198278028886016 }, { target := 157, numerator := 265230935532678293590376448 }, { target := 158, numerator := 7902405077244200423719436288 }, { target := 160, numerator := 84177573017663196715527700480 }, { target := 168, numerator := 7924479186017997774301167616 }, { target := 175, numerator := 284775781775239564360679424 }, { target := 176, numerator := 1160161756728342079340544000 }, { target := 178, numerator := 56590887097300708026702888960 }, { target := 181, numerator := 56569790118455425508321525760 }, { target := 188, numerator := 1159934611442242789583093760 }, { target := 227, numerator := 3378948820935957318819905536 }, { target := 230, numerator := 11775467313755400097216069632 }, { target := 232, numerator := 3381944287763611457184333824 }, { target := 267, numerator := 76414311874313185879130112 }, { target := 268, numerator := 2276721020181655828742275072 }, { target := 270, numerator := 24251964818794575436049285120 }, { target := 278, numerator := 2283080677394344131537403904 }, { target := 285, numerator := 82045276351797995929337856 }, { target := 286, numerator := 1160160048794478394422067200 }, { target := 288, numerator := 56590803786941709456714498048 }, { target := 291, numerator := 56569706839154375868586917888 }, { target := 298, numerator := 1159932903842771376996876288 }, { target := 302, numerator := 36359476677060324907255070720 }, { target := 305, numerator := 126718010439395762327787667456 }, { target := 307, numerator := 36391372445242876264529788928 }, { target := 573, numerator := 33771687925751761757798400 }, { target := 575, numerator := 1647330441128307117948665856 }, { target := 578, numerator := 1646716319363297155624206336 }, { target := 585, numerator := 33765075848020822522331136 }, { target := 589, numerator := 3385307728111845329938153472 }, { target := 592, numerator := 11797568480789358862313455616 }, { target := 594, numerator := 3388311666364928314419707904 }, { target := 763, numerator := 103860320979364810082746368 }, { target := 766, numerator := 361603201793549179142799360 }, { target := 768, numerator := 103968872464473569932345344 }]

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
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 21926910855451010956001280 }, { target := 27, numerator := 1105260616165319317798256640 }, { target := 29, numerator := 12139817850962225650005442560 }, { target := 37, numerator := 1105268337814875175649280000 }, { target := 44, numerator := 21924336972265725005660160 }, { target := 80, numerator := 33771118614463866784972800 }, { target := 82, numerator := 1160161756728342079340544000 }, { target := 85, numerator := 1160160048794478394422067200 }, { target := 92, numerator := 33771687925751761757798400 }, { target := 157, numerator := 76836439438363419620671488 }, { target := 158, numerator := 3873062236511199673496633344 }, { target := 160, numerator := 42540437421732565612259966976 }, { target := 168, numerator := 3873089294771361088012288000 }, { target := 175, numerator := 76827420018309614782119936 }, { target := 176, numerator := 1647302671008640927952535552 }, { target := 178, numerator := 56590887097300708026702888960 }, { target := 181, numerator := 56590803786941709456714498048 }, { target := 188, numerator := 1647330441128307117948665856 }, { target := 267, numerator := 21926169908885092149755904 }, { target := 268, numerator := 1105223267581955628442058752 }, { target := 270, numerator := 12139407626448300828480503808 }, { target := 278, numerator := 1105230988970584182882304000 }, { target := 285, numerator := 21923596112675574003007488 }, { target := 286, numerator := 1646688559596280609046003712 }, { target := 288, numerator := 56569790118455425508321525760 }, { target := 291, numerator := 56569706839154375868586917888 }, { target := 298, numerator := 1646716319363297155624206336 }, { target := 573, numerator := 33764506648197018326925312 }, { target := 575, numerator := 1159934611442242789583093760 }, { target := 578, numerator := 1159932903842771376996876288 }, { target := 585, numerator := 33765075848020822522331136 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8.Parent1
