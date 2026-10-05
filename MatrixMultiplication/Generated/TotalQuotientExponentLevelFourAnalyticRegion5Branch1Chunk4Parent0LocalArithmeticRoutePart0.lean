import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4.Parent0

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6215036998831532943605760 }, { target := 57, numerator := 170294467751836409120423936 }, { target := 59, numerator := 1813877275880488096829014016 }, { target := 67, numerator := 170752716947012100701552640 }, { target := 74, numerator := 5756142018431523871522816 }, { target := 110, numerator := 9503070626957735694958592 }, { target := 112, numerator := 323095118416509234222989312 }, { target := 115, numerator := 323095701728925420737265664 }, { target := 122, numerator := 9503374371108703791218688 }, { target := 152, numerator := 221025563226676898341847040 }, { target := 153, numerator := 6056187703518621720740102144 }, { target := 155, numerator := 64506976644053696591339454464 }, { target := 163, numerator := 6072484434572824747242946560 }, { target := 170, numerator := 204705866091506843898609664 }, { target := 206, numerator := 345739776138029378196996096 }, { target := 208, numerator := 11725753215278814724054056960 }, { target := 211, numerator := 11725774077473942428289335296 }, { target := 218, numerator := 345751294550065840511778816 }, { target := 257, numerator := 164955047352947233844625408 }, { target := 260, numerator := 563802164927143853837778944 }, { target := 262, numerator := 164955366969472138654777344 }, { target := 283, numerator := 221024669284668863435243520 }, { target := 284, numerator := 6056163209154631943504003072 }, { target := 286, numerator := 64506715744384936076726239232 }, { target := 294, numerator := 6072459874296402623625953280 }, { target := 301, numerator := 204705038154817897687416832 }, { target := 302, numerator := 3828577150164933846713237504 }, { target := 304, numerator := 129848386078587965024510148608 }, { target := 307, numerator := 129848617126468039937194196992 }, { target := 314, numerator := 3828704662941069792308625408 }, { target := 660, numerator := 6215280801197360645406720 }, { target := 661, numerator := 170301148032924530184814592 }, { target := 663, numerator := 1813948430335604600814436352 }, { target := 671, numerator := 170759415204218134415278080 }, { target := 678, numerator := 5756367819346691020029952 }, { target := 679, numerator := 344886714406912547314728960 }, { target := 681, numerator := 11697627516529644273169072128 }, { target := 684, numerator := 11697648337228042060859179008 }, { target := 691, numerator := 344898191431994334001496064 }, { target := 966, numerator := 9501645800344151377575936 }, { target := 968, numerator := 323042236086835137799520256 }, { target := 971, numerator := 323042819256824986098204672 }, { target := 978, numerator := 9501949570390817331216384 }]

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
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 164955047352947233844625408 }, { target := 15, numerator := 7148743537541396026475151360 }, { target := 20, numerator := 7144794225149090549005811712 }, { target := 28, numerator := 164872243407401213019291648 }, { target := 56, numerator := 7136557519760583158661120 }, { target := 57, numerator := 266645730399484741423202304 }, { target := 59, numerator := 2952164441679724245097119744 }, { target := 67, numerator := 265793597903115900313141248 }, { target := 74, numerator := 7136557519760583158661120 }, { target := 110, numerator := 6215036998831532943605760 }, { target := 112, numerator := 221025563226676898341847040 }, { target := 115, numerator := 221024669284668863435243520 }, { target := 122, numerator := 6215280801197360645406720 }, { target := 136, numerator := 563802164927143853837778944 }, { target := 137, numerator := 24433790585085457575947796480 }, { target := 142, numerator := 24420292174988364885279113216 }, { target := 150, numerator := 563519148162804015918219264 }, { target := 152, numerator := 235262167291284996269015040 }, { target := 153, numerator := 8790183818886248475150778368 }, { target := 155, numerator := 97320396119099506127271886848 }, { target := 163, numerator := 8762092608612952434976751616 }, { target := 170, numerator := 235262167291284996269015040 }, { target := 206, numerator := 170294467751836409120423936 }, { target := 208, numerator := 6056187703518621720740102144 }, { target := 211, numerator := 6056163209154631943504003072 }, { target := 218, numerator := 170301148032924530184814592 }, { target := 267, numerator := 164955366969472138654777344 }, { target := 268, numerator := 7148757388930629457391124480 }, { target := 273, numerator := 7144808068886145263065890816 }, { target := 281, numerator := 164872562863485381104369664 }, { target := 283, numerator := 235262514045938305660354560 }, { target := 284, numerator := 8790196774803375897761021952 }, { target := 286, numerator := 97320539560353171144727068672 }, { target := 294, numerator := 8762105523126236683356340224 }, { target := 301, numerator := 235262514045938305660354560 }, { target := 302, numerator := 1813877275880488096829014016 }, { target := 304, numerator := 64506976644053696591339454464 }, { target := 307, numerator := 64506715744384936076726239232 }, { target := 314, numerator := 1813948430335604600814436352 }, { target := 353, numerator := 7148743537541396026475151360 }, { target := 356, numerator := 24433790585085457575947796480 }, { target := 358, numerator := 7148757388930629457391124480 }, { target := 660, numerator := 7136904274413892550000640 }, { target := 661, numerator := 266658686316612164033445888 }, { target := 663, numerator := 2952307882933389262552301568 }, { target := 671, numerator := 265806512416400148692729856 }, { target := 678, numerator := 7136904274413892550000640 }, { target := 679, numerator := 170752716947012100701552640 }, { target := 681, numerator := 6072484434572824747242946560 }, { target := 684, numerator := 6072459874296402623625953280 }, { target := 691, numerator := 170759415204218134415278080 }, { target := 695, numerator := 7144794225149090549005811712 }, { target := 698, numerator := 24420292174988364885279113216 }, { target := 700, numerator := 7144808068886145263065890816 }, { target := 966, numerator := 5756142018431523871522816 }, { target := 968, numerator := 204705866091506843898609664 }, { target := 971, numerator := 204705038154817897687416832 }, { target := 978, numerator := 5756367819346691020029952 }, { target := 982, numerator := 164872243407401213019291648 }, { target := 985, numerator := 563519148162804015918219264 }, { target := 987, numerator := 164872562863485381104369664 }]

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
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2366513107197152536297472 }, { target := 57, numerator := 79094045738544636773793792 }, { target := 59, numerator := 876412708485209601616117760 }, { target := 67, numerator := 79093116503796647001587712 }, { target := 74, numerator := 2365088280583568218914816 }, { target := 152, numerator := 87832951125224237953974272 }, { target := 153, numerator := 2935569396392566248903278592 }, { target := 155, numerator := 32527989959488458897238261760 }, { target := 163, numerator := 2935534907916691838192320512 }, { target := 170, numerator := 87780068795550141530505216 }, { target := 283, numerator := 87833187682987115076911104 }, { target := 284, numerator := 2935577302670566530528313344 }, { target := 286, numerator := 32528077566114868792467128320 }, { target := 294, numerator := 2935542814101805377502838784 }, { target := 301, numerator := 87780305210886680437850112 }, { target := 660, numerator := 2366470096694811241218048 }, { target := 661, numerator := 79092608233453676478332928 }, { target := 663, numerator := 876396780007680529756323840 }, { target := 671, numerator := 79091679015594185308766208 }, { target := 678, numerator := 2365045295976924781215744 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4.Parent0
