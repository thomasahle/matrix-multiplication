import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4.Parent1

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
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 2663556836135169201012736 }, { target := 35, numerator := 147604221832492599547527168 }, { target := 40, numerator := 147647260899758956154454016 }, { target := 48, numerator := 2621085767920366141833216 }, { target := 79, numerator := 57261812815910763531075584 }, { target := 80, numerator := 2943467015186736339864256512 }, { target := 85, numerator := 2944151326688253352349794304 }, { target := 93, numerator := 56605403194748339113426944 }, { target := 121, numerator := 2663556836135169201012736 }, { target := 122, numerator := 108169291150067844534763520 }, { target := 124, numerator := 1199619717257356561302421504 }, { target := 132, numerator := 108170174421922462293819392 }, { target := 139, numerator := 2663178317312212988854272 }, { target := 154, numerator := 639082642205655884825100288 }, { target := 155, numerator := 32851189733693645572678877184 }, { target := 160, numerator := 32858827137767581826131427328 }, { target := 168, numerator := 631756643002481276834807808 }, { target := 196, numerator := 147604221832492599547527168 }, { target := 197, numerator := 5923532544835493690125320192 }, { target := 199, numerator := 65664388700001676808383627264 }, { target := 207, numerator := 5923583607572995590280183808 }, { target := 214, numerator := 147583349746052738723086336 }, { target := 492, numerator := 57261902930687507401015296 }, { target := 493, numerator := 2943471647416487417456099328 }, { target := 498, numerator := 2944155959994927690836606976 }, { target := 506, numerator := 56605492276511918455259136 }, { target := 508, numerator := 147647260899758956154454016 }, { target := 509, numerator := 5925206150877398955311759360 }, { target := 511, numerator := 65682919125811906252074123264 }, { target := 519, numerator := 5925257230105393841037115392 }, { target := 526, numerator := 147626382806080142371192832 }, { target := 890, numerator := 1165499465016841865265152 }, { target := 891, numerator := 59910943485562034099060736 }, { target := 896, numerator := 59924871872556819191693312 }, { target := 904, numerator := 1152138989253417586655232 }, { target := 906, numerator := 2621085767920366141833216 }, { target := 907, numerator := 106523586988517167416213504 }, { target := 909, numerator := 1181400696317888763074183168 }, { target := 917, numerator := 106524453813788895971639296 }, { target := 924, numerator := 2620713168516170154770432 }]

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
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 79, numerator := 50907478334157081003687936 }, { target := 80, numerator := 2980065529648757350261063680 }, { target := 85, numerator := 2981054824189145602961965056 }, { target := 93, numerator := 49918183793768828302786560 }, { target := 154, numerator := 560537075051700676477321216 }, { target := 155, numerator := 32813198966308031235704750080 }, { target := 160, numerator := 32824091988044324425942695936 }, { target := 168, numerator := 549644053315407486239375360 }, { target := 492, numerator := 50908271491234954892804096 }, { target := 493, numerator := 2980111960156508172824084480 }, { target := 498, numerator := 2981101270110466150200508416 }, { target := 506, numerator := 49918961537276977516380160 }, { target := 890, numerator := 1497678852295371123589120 }, { target := 891, numerator := 87672406260490704624025600 }, { target := 896, numerator := 87701510933523323179499520 }, { target := 904, numerator := 1468574179262752568115200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4.Parent1
