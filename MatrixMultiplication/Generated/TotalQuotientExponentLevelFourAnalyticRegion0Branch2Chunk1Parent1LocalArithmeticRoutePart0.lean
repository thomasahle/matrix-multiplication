import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent1

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
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 3292619201992515668410368 }, { target := 57, numerator := 86547449024885558656106496 }, { target := 59, numerator := 1189468986607659006170234880 }, { target := 67, numerator := 86213447116687700454801408 }, { target := 74, numerator := 3217644176678927078522880 }, { target := 110, numerator := 12788676482462838253682688 }, { target := 112, numerator := 518413674244313637023907840 }, { target := 115, numerator := 518569211950123514540851200 }, { target := 122, numerator := 12633392073732702842388480 }, { target := 152, numerator := 187297324239949155249684480 }, { target := 153, numerator := 4923164395185747452818882560 }, { target := 155, numerator := 67661744280420087042460876800 }, { target := 163, numerator := 4904165033322511202129018880 }, { target := 170, numerator := 183032445502207554276556800 }, { target := 206, numerator := 303893113267579589171871744 }, { target := 208, numerator := 12501752108775295406271627264 }, { target := 211, numerator := 12505314755777367746581364736 }, { target := 218, numerator := 300336572474439718869663744 }, { target := 257, numerator := 144243882878853441254326272 }, { target := 260, numerator := 512193764260050346702798848 }, { target := 262, numerator := 144244312398127427670245376 }, { target := 283, numerator := 187298119443350109825269760 }, { target := 284, numerator := 4923185297337374001038622720 }, { target := 286, numerator := 67662031550136216989571481600 }, { target := 294, numerator := 4904185854809038924608962560 }, { target := 301, numerator := 183033222598323257055641600 }, { target := 302, numerator := 4049035861628403095244374016 }, { target := 304, numerator := 167371478361063684914364284928 }, { target := 307, numerator := 167418363552525339303463616512 }, { target := 314, numerator := 4002232409857096633840304128 }, { target := 353, numerator := 6992254784640625223669907456 }, { target := 356, numerator := 24828708346809701981753442304 }, { target := 358, numerator := 6992275605684392807783989248 }, { target := 660, numerator := 3291914878980241615749120 }, { target := 661, numerator := 86528935690587758804336640 }, { target := 663, numerator := 1189214547716229624443699200 }, { target := 671, numerator := 86195005228620289115422720 }, { target := 678, numerator := 3216955891547876045619200 }, { target := 679, numerator := 217340529637530419651936256 }, { target := 681, numerator := 7578408675945789744520101888 }, { target := 684, numerator := 7581950337125546909553917952 }, { target := 691, numerator := 213802585761556783523954688 }, { target := 695, numerator := 6993230583861284759131914240 }, { target := 698, numerator := 24832173299818568209305436160 }, { target := 700, numerator := 6993251407810718527830097920 }, { target := 966, numerator := 9496254765284307618496512 }, { target := 968, numerator := 331123236067585951348555776 }, { target := 971, numerator := 331277981788098283022843904 }, { target := 978, numerator := 9341671464840737247461376 }, { target := 982, numerator := 143325934004318446691549184 }, { target := 985, numerator := 508934231307507487479955456 }, { target := 987, numerator := 143326360790188934270287872 }]

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
    Slot15.Left11.expected,
    Slot15.Left18.expected,
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
  [{ target := 14, numerator := 144243882878853441254326272 }, { target := 15, numerator := 6992254784640625223669907456 }, { target := 20, numerator := 6993230583861284759131914240 }, { target := 28, numerator := 143325934004318446691549184 }, { target := 56, numerator := 9496057280470322585272320 }, { target := 57, numerator := 217345664242694030515765248 }, { target := 59, numerator := 2859566875020744089074139136 }, { target := 67, numerator := 217340529637530419651936256 }, { target := 74, numerator := 9496254765284307618496512 }, { target := 136, numerator := 512193764260050346702798848 }, { target := 137, numerator := 24828708346809701981753442304 }, { target := 142, numerator := 24832173299818568209305436160 }, { target := 150, numerator := 508934231307507487479955456 }, { target := 152, numerator := 331116350004364481774223360 }, { target := 153, numerator := 7578587713589547953452744704 }, { target := 155, numerator := 99709734080643597871903408128 }, { target := 163, numerator := 7578408675945789744520101888 }, { target := 170, numerator := 331123236067585951348555776 }, { target := 267, numerator := 144244312398127427670245376 }, { target := 268, numerator := 6992275605684392807783989248 }, { target := 273, numerator := 6993251407810718527830097920 }, { target := 281, numerator := 143326360790188934270287872 }, { target := 283, numerator := 331271092506773404715581440 }, { target := 284, numerator := 7582129458439993745542742016 }, { target := 286, numerator := 99756332002389122313892134912 }, { target := 294, numerator := 7581950337125546909553917952 }, { target := 301, numerator := 331277981788098283022843904 }, { target := 660, numerator := 9341477194752461226639360 }, { target := 661, numerator := 213807636783851960065327104 }, { target := 663, numerator := 2813017862140867009396604928 }, { target := 671, numerator := 213802585761556783523954688 }, { target := 678, numerator := 9341671464840737247461376 }, { target := 679, numerator := 86213447116687700454801408 }, { target := 681, numerator := 4904165033322511202129018880 }, { target := 684, numerator := 4904185854809038924608962560 }, { target := 691, numerator := 86195005228620289115422720 }, { target := 966, numerator := 3217644176678927078522880 }, { target := 968, numerator := 183032445502207554276556800 }, { target := 971, numerator := 183033222598323257055641600 }, { target := 978, numerator := 3216955891547876045619200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1.Parent1
