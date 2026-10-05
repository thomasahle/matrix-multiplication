import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7.Parent3

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
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 431182861337197159510966272 }, { target := 37, numerator := 20681495315269660123638792192 }, { target := 40, numerator := 20693274740425061166124892160 }, { target := 47, numerator := 439870124438123537573609472 }, { target := 86, numerator := 1585602007108810449914691584 }, { target := 89, numerator := 5630997708396072187281276928 }, { target := 91, numerator := 1585112218094462549673115648 }, { target := 122, numerator := 199335485511487300495736832 }, { target := 124, numerator := 199336137705333887734906880 }, { target := 145, numerator := 1563048084495757824403439616 }, { target := 147, numerator := 74970910339036535383576805376 }, { target := 150, numerator := 75013611034209139173076500480 }, { target := 157, numerator := 1594539618986027827347849216 }, { target := 161, numerator := 62566142992736479223845224448 }, { target := 164, numerator := 222557139909270448860500590592 }, { target := 166, numerator := 62554139746802402745624035328 }, { target := 197, numerator := 5337819505406557146480377856 }, { target := 199, numerator := 5337836063024569263023194112 }, { target := 216, numerator := 431700662448493328458579968 }, { target := 218, numerator := 20706331416649715856281960448 }, { target := 221, numerator := 20718124987542303625225175040 }, { target := 228, numerator := 440398357954997775413280768 }, { target := 232, numerator := 41887923352165132860395618304 }, { target := 235, numerator := 147597840616317967016241659904 }, { target := 237, numerator := 41851083830863436245326888960 }, { target := 242, numerator := 68165556838780355099731427328 }, { target := 244, numerator := 68165815363829947641215582208 }, { target := 406, numerator := 1147527039463663623288651776 }, { target := 409, numerator := 4043610935386807630116683776 }, { target := 411, numerator := 1146523408217701844925808640 }, { target := 416, numerator := 5328169414080150208002392064 }, { target := 418, numerator := 5328185842535487961512804352 }, { target := 498, numerator := 197134877124818879832391680 }, { target := 500, numerator := 197135500529967799059087360 }]

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
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 199335485511487300495736832 }, { target := 17, numerator := 5337819505406557146480377856 }, { target := 19, numerator := 68165556838780355099731427328 }, { target := 27, numerator := 5328169414080150208002392064 }, { target := 34, numerator := 197134877124818879832391680 }, { target := 35, numerator := 1154419145771613290403725312 }, { target := 37, numerator := 41884647677466819100206432256 }, { target := 40, numerator := 41887923352165132860395618304 }, { target := 47, numerator := 1147527039463663623288651776 }, { target := 126, numerator := 199336137705333887734906880 }, { target := 127, numerator := 5337836063024569263023194112 }, { target := 129, numerator := 68165815363829947641215582208 }, { target := 137, numerator := 5328185842535487961512804352 }, { target := 144, numerator := 197135500529967799059087360 }, { target := 145, numerator := 4067949623900314362877837312 }, { target := 147, numerator := 147586229570233913476923785216 }, { target := 150, numerator := 147597840616317967016241659904 }, { target := 157, numerator := 4043610935386807630116683776 }, { target := 216, numerator := 1153411555645969221214535680 }, { target := 218, numerator := 41847808330152686889342074880 }, { target := 221, numerator := 41851083830863436245326888960 }, { target := 228, numerator := 1146523408217701844925808640 }, { target := 232, numerator := 20693274740425061166124892160 }, { target := 235, numerator := 75013611034209139173076500480 }, { target := 237, numerator := 20718124987542303625225175040 }, { target := 406, numerator := 439870124438123537573609472 }, { target := 409, numerator := 1594539618986027827347849216 }, { target := 411, numerator := 440398357954997775413280768 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7.Parent3
