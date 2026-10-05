import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left3.expected,
    Slot1.Left11.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left3.expected,
    Slot3.Left11.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 5275577005059425367113072640 }, { target := 36, numerator := 93905270690057771534612692992 }, { target := 37, numerator := 5275577005059425367113072640 }, { target := 38, numerator := 83529969246774234979290316800 }, { target := 39, numerator := 142616431703439799090956730368 }, { target := 40, numerator := 5275577005059425367113072640 }, { target := 41, numerator := 142616431703439799090956730368 }, { target := 42, numerator := 142616431703439799090956730368 }, { target := 43, numerator := 93905270690057771534612692992 }, { target := 44, numerator := 5275577005059425367113072640 }, { target := 71, numerator := 57948300145875231963640496128 }, { target := 72, numerator := 1162798380222629023238324224 }, { target := 73, numerator := 57948300145875231963640496128 }, { target := 74, numerator := 1162798380222629023238324224 }, { target := 89, numerator := 2567980392086167240400961536 }, { target := 116, numerator := 2098775357591734521911320772608 }, { target := 117, numerator := 40695044208270019583354601472 }, { target := 118, numerator := 2098775357591734521911320772608 }, { target := 119, numerator := 40695044208270019583354601472 }, { target := 134, numerator := 352582011087153467043526737920 }, { target := 139, numerator := 2959450406416612219680718848 }, { target := 150, numerator := 2098776133351109797692804431872 }, { target := 151, numerator := 40695064167647107337089449984 }, { target := 152, numerator := 2098776133351109797692804431872 }, { target := 153, numerator := 40695064167647107337089449984 }, { target := 154, numerator := 3653767459733588965238851502080 }, { target := 159, numerator := 3036821658871948486861914112 }, { target := 160, numerator := 96714065569170333976494080 }, { target := 205, numerator := 2959450406416612219680718848 }, { target := 210, numerator := 1682824740903563811190996992 }, { target := 225, numerator := 3036821658871948486861914112 }, { target := 230, numerator := 47409234942007297715277398016 }, { target := 231, numerator := 1856910058928070412348686336 }, { target := 232, numerator := 57947533296277343783870267392 }, { target := 233, numerator := 1162788400534085146370899968 }, { target := 234, numerator := 57947533296277343783870267392 }, { target := 235, numerator := 1162788400534085146370899968 }, { target := 236, numerator := 352582034698985881391752806400 }, { target := 237, numerator := 2959450406416612219680718848 }, { target := 252, numerator := 96714065569170333976494080 }, { target := 257, numerator := 1856910058928070412348686336 }, { target := 258, numerator := 96714065569170333976494080 }, { target := 263, numerator := 2978793219530446286476017664 }, { target := 264, numerator := 1682824740903563811190996992 }, { target := 265, numerator := 2567980392086167240400961536 }]

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
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 79847132533907027730993512448 }, { target := 20, numerator := 94818469884014595430554796032 }, { target := 21, numerator := 72361463858853243881212870656 }, { target := 22, numerator := 746071644613693790361470631936 }, { target := 23, numerator := 89828024100645406197367701504 }, { target := 24, numerator := 72361463858853243881212870656 }, { target := 25, numerator := 89828024100645406197367701504 }, { target := 26, numerator := 89828024100645406197367701504 }, { target := 27, numerator := 3847633698977644898787249881088 }, { target := 28, numerator := 89828024100645406197367701504 }, { target := 29, numerator := 746071644613693790361470631936 }, { target := 30, numerator := 3847633698977644898787249881088 }, { target := 31, numerator := 79847132533907027730993512448 }, { target := 32, numerator := 89828024100645406197367701504 }, { target := 33, numerator := 89828024100645406197367701504 }, { target := 34, numerator := 94818469884014595430554796032 }, { target := 35, numerator := 3613495239923726187263814533120 }, { target := 38, numerator := 12927040638842084575887690301440 }, { target := 40, numerator := 3613494038649932167103203246080 }, { target := 71, numerator := 833411614374975598063679176704 }, { target := 73, numerator := 833411614374975598063679176704 }, { target := 89, numerator := 10801959982381957940389085184 }, { target := 106, numerator := 12422380117687324976426795401216 }, { target := 107, numerator := 318313506556466648696563433472 }, { target := 108, numerator := 17882781267217227454863114240 }, { target := 109, numerator := 44659414247535443916054920691712 }, { target := 110, numerator := 483431186923772382196466188288 }, { target := 111, numerator := 12422375993924433690898332647424 }, { target := 112, numerator := 483431186923772382196466188288 }, { target := 113, numerator := 483431186923772382196466188288 }, { target := 114, numerator := 318313506556466648696563433472 }, { target := 115, numerator := 17882781267217227454863114240 }, { target := 116, numerator := 31313415325787779380516778672128 }, { target := 118, numerator := 31313415325787779380516778672128 }, { target := 134, numerator := 1724502590761039672339058393088 }, { target := 140, numerator := 3618770816928785612630927605760 }, { target := 141, numerator := 93905270690057771534612692992 }, { target := 142, numerator := 5275577005059425367113072640 }, { target := 143, numerator := 13010570608088858810866980618240 }, { target := 144, numerator := 142616431703439799090956730368 }, { target := 145, numerator := 3618769615654991592470316318720 }, { target := 146, numerator := 142616431703439799090956730368 }, { target := 147, numerator := 142616431703439799090956730368 }, { target := 148, numerator := 93905270690057771534612692992 }, { target := 149, numerator := 5275577005059425367113072640 }, { target := 150, numerator := 31311047025940054873354593632256 }, { target := 152, numerator := 31311047025940054873354593632256 }, { target := 154, numerator := 17207942547273800880333476855808 }, { target := 232, numerator := 835779914222700105225864216576 }, { target := 234, numerator := 835779914222700105225864216576 }, { target := 236, numerator := 1724502590761039672339058393088 }, { target := 265, numerator := 10800727444729928962988310528 }]

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
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot10.Left16.expected,
    Slot10.Left17.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 987514804634693525431207854080 }, { target := 21, numerator := 36467607953978791178415793766400 }, { target := 24, numerator := 36467599023981642995192855265280 }, { target := 31, numerator := 987523734631841708654146355200 }, { target := 35, numerator := 12979395420509098482832584474624 }, { target := 38, numerator := 47208858980510459394325248737280 }, { target := 40, numerator := 12979395420509098482832584474624 }, { target := 71, numerator := 989081459533638041864996126720 }, { target := 73, numerator := 989080987902958091962429734912 }, { target := 89, numerator := 11895830065007951079108771840 }, { target := 90, numerator := 1067361466284959695049343369216 }, { target := 91, numerator := 94818469884014595430554796032 }, { target := 92, numerator := 36539952028731247067411666436096 }, { target := 93, numerator := 746071644613693790361470631936 }, { target := 94, numerator := 89828024100645406197367701504 }, { target := 95, numerator := 36539943098738357037636406738944 }, { target := 96, numerator := 89828024100645406197367701504 }, { target := 97, numerator := 89828024100645406197367701504 }, { target := 98, numerator := 3847633698977644898787249881088 }, { target := 99, numerator := 89828024100645406197367701504 }, { target := 100, numerator := 746071644613693790361470631936 }, { target := 101, numerator := 3847633698977644898787249881088 }, { target := 102, numerator := 1067370396277849724824603066368 }, { target := 103, numerator := 89828024100645406197367701504 }, { target := 104, numerator := 89828024100645406197367701504 }, { target := 105, numerator := 94818469884014595430554796032 }, { target := 106, numerator := 47208858980510459394325248737280 }, { target := 109, numerator := 171708796445181910003358472601600 }, { target := 111, numerator := 47208858980510459394325248737280 }, { target := 116, numerator := 36525462435132644363786099097600 }, { target := 118, numerator := 36525445018439087203472596008960 }, { target := 134, numerator := 199849945092133578129027366912 }, { target := 139, numerator := 433008214366289419279559294976 }, { target := 140, numerator := 12979395420509098482832584474624 }, { target := 143, numerator := 47208858980510459394325248737280 }, { target := 145, numerator := 12979395420509098482832584474624 }, { target := 150, numerator := 36525453490968393354254504427520 }, { target := 152, numerator := 36525436074279101102788121198592 }, { target := 154, numerator := 14274996078009541294930526208 }, { target := 159, numerator := 228399937248152660718888419328 }, { target := 160, numerator := 16654162091011131510752280576 }, { target := 205, numerator := 433008214366289419279559294976 }, { target := 210, numerator := 433008214366289419279559294976 }, { target := 225, numerator := 228399937248152660718888419328 }, { target := 230, numerator := 5343606865201571624735660310528 }, { target := 231, numerator := 428249882340286238847915786240 }, { target := 232, numerator := 989090403697889051396590796800 }, { target := 234, numerator := 989089932062944192646904545280 }, { target := 236, numerator := 199849945092133578129027366912 }, { target := 237, numerator := 433008214366289419279559294976 }, { target := 252, numerator := 16654162091011131510752280576 }, { target := 257, numerator := 428249882340286238847915786240 }, { target := 258, numerator := 16654162091011131510752280576 }, { target := 263, numerator := 433008214366289419279559294976 }, { target := 264, numerator := 433008214366289419279559294976 }, { target := 265, numerator := 14274996078009541294930526208 }]

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

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 11992544130577121413085265920 }, { target := 1, numerator := 201474741393695639739832467456 }, { target := 2, numerator := 436528606353007219436303679488 }, { target := 3, numerator := 14391052956692545695702319104 }, { target := 4, numerator := 230256847307080731131237105664 }, { target := 5, numerator := 16789561782807969978319372288 }, { target := 6, numerator := 436528606353007219436303679488 }, { target := 7, numerator := 436528606353007219436303679488 }, { target := 8, numerator := 230256847307080731131237105664 }, { target := 9, numerator := 5387050823455242938757901451264 }, { target := 10, numerator := 431731588700776370871069573120 }, { target := 11, numerator := 201474741393695639739832467456 }, { target := 12, numerator := 436528606353007219436303679488 }, { target := 13, numerator := 16789561782807969978319372288 }, { target := 14, numerator := 431731588700776370871069573120 }, { target := 15, numerator := 16789561782807969978319372288 }, { target := 16, numerator := 436528606353007219436303679488 }, { target := 17, numerator := 436528606353007219436303679488 }, { target := 18, numerator := 14391052956692545695702319104 }, { target := 19, numerator := 828276607508832803251210420224 }, { target := 21, numerator := 31120479926368261331345387552768 }, { target := 24, numerator := 31118126218632968891386912833536 }, { target := 31, numerator := 830630315244125243209685139456 }, { target := 35, numerator := 3613495239923726187263814533120 }, { target := 38, numerator := 12404497336420107748971932286976 }, { target := 40, numerator := 3613495239923726187263814533120 }, { target := 71, numerator := 79228162514264337593543950336 }, { target := 73, numerator := 79228162514264337593543950336 }, { target := 85, numerator := 94083442985688900892333441024 }, { target := 87, numerator := 94083442985688900892333441024 }, { target := 106, numerator := 12927040638842084575887690301440 }, { target := 109, numerator := 44376270210804504481352921382912 }, { target := 111, numerator := 12927040638842084575887690301440 }, { target := 116, numerator := 71800522278552055944149204992 }, { target := 118, numerator := 71800522278552055944149204992 }, { target := 130, numerator := 740288143492657404389676285952 }, { target := 132, numerator := 740288143492657404389676285952 }, { target := 135, numerator := 89131682828547379792736944128 }, { target := 137, numerator := 89131682828547379792736944128 }, { target := 140, numerator := 3613494038649932167103203246080 }, { target := 143, numerator := 12404493212657216463443469533184 }, { target := 145, numerator := 3613494038649932167103203246080 }, { target := 150, numerator := 71800522278552055944149204992 }, { target := 152, numerator := 71800522278552055944149204992 }, { target := 155, numerator := 89131682828547379792736944128 }, { target := 157, numerator := 89131682828547379792736944128 }, { target := 187, numerator := 89131682828547379792736944128 }, { target := 189, numerator := 89131682828547379792736944128 }, { target := 201, numerator := 3817807081156112767788899106816 }, { target := 203, numerator := 3817807081156112767788899106816 }, { target := 206, numerator := 89131682828547379792736944128 }, { target := 208, numerator := 89131682828547379792736944128 }, { target := 221, numerator := 740288143492657404389676285952 }, { target := 223, numerator := 740288143492657404389676285952 }, { target := 226, numerator := 3817807081156112767788899106816 }, { target := 228, numerator := 3817807081156112767788899106816 }, { target := 232, numerator := 79228162514264337593543950336 }, { target := 234, numerator := 79228162514264337593543950336 }, { target := 248, numerator := 89131682828547379792736944128 }, { target := 250, numerator := 89131682828547379792736944128 }, { target := 253, numerator := 89131682828547379792736944128 }, { target := 255, numerator := 89131682828547379792736944128 }, { target := 259, numerator := 94083442985688900892333441024 }, { target := 261, numerator := 94083442985688900892333441024 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left2.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 12875891115396785768178384896 }, { target := 1, numerator := 2029822019997311358499419062272 }, { target := 3, numerator := 20396107617775183091107996106752 }, { target := 11, numerator := 2029822019997311358499419062272 }, { target := 18, numerator := 12874668022477722530068037632 }, { target := 19, numerator := 58480170838107874364768649216 }, { target := 21, numerator := 2118050527528067963908578607104 }, { target := 24, numerator := 2118051310370992963994530086912 }, { target := 31, numerator := 58479396904960261880530599936 }, { target := 35, numerator := 4952582494545582997697986560 }, { target := 38, numerator := 16787917107999846182116392960 }, { target := 40, numerator := 4952582494545582997697986560 }, { target := 45, numerator := 1162798380222629023238324224 }, { target := 47, numerator := 40695044208270019583354601472 }, { target := 50, numerator := 40695064167647107337089449984 }, { target := 57, numerator := 1162788400534085146370899968 }, { target := 61, numerator := 88155968402911377359024160768 }, { target := 64, numerator := 298824924522397262041671794688 }, { target := 66, numerator := 88155968402911377359024160768 }, { target := 75, numerator := 4952582494545582997697986560 }, { target := 78, numerator := 16787917107999846182116392960 }, { target := 80, numerator := 4952582494545582997697986560 }, { target := 90, numerator := 886756778346940677615979069440 }, { target := 92, numerator := 33238530453896329295253966159872 }, { target := 95, numerator := 33236177529003961855381442920448 }, { target := 102, numerator := 889109712149085505090215739392 }, { target := 106, numerator := 78415889496971730796884787200 }, { target := 109, numerator := 265808687543330897883509555200 }, { target := 111, numerator := 78415889496971730796884787200 }, { target := 120, numerator := 133884813435882260371102236672 }, { target := 123, numerator := 453833359152929175123213156352 }, { target := 125, numerator := 133884813435882260371102236672 }, { target := 140, numerator := 4952582494545582997697986560 }, { target := 143, numerator := 16787917107999846182116392960 }, { target := 145, numerator := 4952582494545582997697986560 }, { target := 177, numerator := 133884813435882260371102236672 }, { target := 180, numerator := 453833359152929175123213156352 }, { target := 182, numerator := 133884813435882260371102236672 }, { target := 191, numerator := 133884813435882260371102236672 }, { target := 194, numerator := 453833359152929175123213156352 }, { target := 196, numerator := 133884813435882260371102236672 }, { target := 211, numerator := 88155968402911377359024160768 }, { target := 214, numerator := 298824924522397262041671794688 }, { target := 216, numerator := 88155968402911377359024160768 }, { target := 238, numerator := 4952582494545582997697986560 }, { target := 241, numerator := 16787917107999846182116392960 }, { target := 243, numerator := 4952582494545582997697986560 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot22.Left3.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 411275619359600271305998336 }, { target := 1, numerator := 34048002611333584160261406720 }, { target := 2, numerator := 2959450406416612219680718848 }, { target := 3, numerator := 333740760517464985266374574080 }, { target := 4, numerator := 3036821658871948486861914112 }, { target := 5, numerator := 96714065569170333976494080 }, { target := 6, numerator := 2959450406416612219680718848 }, { target := 7, numerator := 1682824740903563811190996992 }, { target := 8, numerator := 3036821658871948486861914112 }, { target := 9, numerator := 47409234942007297715277398016 }, { target := 10, numerator := 1856910058928070412348686336 }, { target := 11, numerator := 34048026223165998508487475200 }, { target := 12, numerator := 2959450406416612219680718848 }, { target := 13, numerator := 96714065569170333976494080 }, { target := 14, numerator := 1856910058928070412348686336 }, { target := 15, numerator := 96714065569170333976494080 }, { target := 16, numerator := 2978793219530446286476017664 }, { target := 17, numerator := 1682824740903563811190996992 }, { target := 18, numerator := 411275619359600271305998336 }, { target := 161, numerator := 1162798380222629023238324224 }, { target := 163, numerator := 40695044208270019583354601472 }, { target := 166, numerator := 40695064167647107337089449984 }, { target := 173, numerator := 1162788400534085146370899968 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19.Parent2
