import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5.Parent0

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
  [{ target := 56, numerator := 8386052588977297570136064 }, { target := 57, numerator := 249857673744117777442013184 }, { target := 59, numerator := 2661520432075036028452208640 }, { target := 67, numerator := 250555611323156563218137088 }, { target := 74, numerator := 9004020127735234147909632 }, { target := 110, numerator := 10137436365871129108152320 }, { target := 112, numerator := 371380899103715851182800896 }, { target := 115, numerator := 371351317873844413116973056 }, { target := 122, numerator := 10137266393265792704577536 }, { target := 152, numerator := 304940086840540257318862848 }, { target := 153, numerator := 9085516686295718832466034688 }, { target := 155, numerator := 96780250669023184760057364480 }, { target := 163, numerator := 9110895628736541144347836416 }, { target := 170, numerator := 327411097239541495181082624 }, { target := 206, numerator := 498538708327037690613596160 }, { target := 208, numerator := 18112515593178605268592754688 }, { target := 211, numerator := 18111250989054493332988755968 }, { target := 218, numerator := 498532579085007876373086208 }, { target := 257, numerator := 136884171791798442043375616 }, { target := 260, numerator := 475753083422885173629288448 }, { target := 262, numerator := 137066758139769779872858112 }, { target := 283, numerator := 305082123887322584372477952 }, { target := 284, numerator := 9089748599429815294714970112 }, { target := 286, numerator := 96825329625792386652721643520 }, { target := 294, numerator := 9115139363045321793217757184 }, { target := 301, numerator := 327563600984842728716107776 }, { target := 302, numerator := 5381144910471557707716362240 }, { target := 304, numerator := 194325514661278382061650968576 }, { target := 307, numerator := 194313345644593199391877103616 }, { target := 314, numerator := 5381096118186371774494539776 }, { target := 353, numerator := 7095987483746686389897396224 }, { target := 356, numerator := 24662734055603638337454211072 }, { target := 358, numerator := 7105452642668627279130656768 }, { target := 660, numerator := 8528388582451089663590400 }, { target := 661, numerator := 254098493825089475602022400 }, { target := 663, numerator := 2706694266943199672008704000 }, { target := 671, numerator := 254808277458948589407436800 }, { target := 678, numerator := 9156844849085510005555200 }, { target := 679, numerator := 68347053619581926821068800 }, { target := 681, numerator := 3333863034518719113767944192 }, { target := 684, numerator := 3332620176498285897477783552 }, { target := 691, numerator := 68333672113978567559217152 }, { target := 695, numerator := 7097299797671622248880930816 }, { target := 698, numerator := 24667295119078213353417474048 }, { target := 700, numerator := 7106766707056044004199104512 }, { target := 966, numerator := 1602848488460971409408000 }, { target := 968, numerator := 78184457743519084938526720 }, { target := 971, numerator := 78155310721168845381304320 }, { target := 978, numerator := 1602534670602061815480320 }, { target := 982, numerator := 135646009639230837903851520 }, { target := 985, numerator := 471449741011919521248706560 }, { target := 987, numerator := 135826944433902225866096640 }]

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
  [{ target := 14, numerator := 160431867666700874180198400 }, { target := 15, numerator := 7157362819748888418881372160 }, { target := 20, numerator := 7157603591862077344909885440 }, { target := 28, numerator := 160419654588495638801940480 }, { target := 56, numerator := 8534445549588183955537920 }, { target := 57, numerator := 430192224018743658765352960 }, { target := 59, numerator := 4725089417016498882179235840 }, { target := 67, numerator := 430195229457955862609920000 }, { target := 74, numerator := 8533443736517449340682240 }, { target := 110, numerator := 8386052588977297570136064 }, { target := 112, numerator := 304940086840540257318862848 }, { target := 115, numerator := 305082123887322584372477952 }, { target := 122, numerator := 8528388582451089663590400 }, { target := 136, numerator := 547581072720113766057902080 }, { target := 137, numerator := 24429288692365130049825800192 }, { target := 142, numerator := 24430110488271009451687804928 }, { target := 150, numerator := 547539387420540173209829376 }, { target := 152, numerator := 293189498830280218745241600 }, { target := 153, numerator := 14778680328779552344820940800 }, { target := 155, numerator := 162324147486086653640127283200 }, { target := 163, numerator := 14778783576636870203801600000 }, { target := 170, numerator := 293155082877840932418355200 }, { target := 206, numerator := 249857673744117777442013184 }, { target := 208, numerator := 9085516686295718832466034688 }, { target := 211, numerator := 9089748599429815294714970112 }, { target := 218, numerator := 254098493825089475602022400 }, { target := 257, numerator := 160431867666700874180198400 }, { target := 260, numerator := 547581072720113766057902080 }, { target := 262, numerator := 160453867645327462786662400 }, { target := 267, numerator := 160453867645327462786662400 }, { target := 268, numerator := 7158344306976752301517045760 }, { target := 273, numerator := 7158585112106955995705507840 }, { target := 281, numerator := 160441652892346115980001280 }, { target := 283, numerator := 293189067210921431091118080 }, { target := 284, numerator := 14778658572323223982089175040 }, { target := 286, numerator := 162323908520350386753802076160 }, { target := 294, numerator := 14778761820028545353646080000 }, { target := 301, numerator := 293154651309147640572149760 }, { target := 302, numerator := 2661520432075036028452208640 }, { target := 304, numerator := 96780250669023184760057364480 }, { target := 307, numerator := 96825329625792386652721643520 }, { target := 314, numerator := 2706694266943199672008704000 }, { target := 353, numerator := 7157362819748888418881372160 }, { target := 356, numerator := 24429288692365130049825800192 }, { target := 358, numerator := 7158344306976752301517045760 }, { target := 660, numerator := 8534589422707779840245760 }, { target := 661, numerator := 430199476170853113009274880 }, { target := 663, numerator := 4725169072261921177620971520 }, { target := 671, numerator := 430202481660730812661760000 }, { target := 678, numerator := 8533587592748546622750720 }, { target := 679, numerator := 430195229457955862609920000 }, { target := 681, numerator := 14778783576636870203801600000 }, { target := 684, numerator := 14778761820028545353646080000 }, { target := 691, numerator := 430202481660730812661760000 }, { target := 695, numerator := 7157603591862077344909885440 }, { target := 698, numerator := 24430110488271009451687804928 }, { target := 700, numerator := 7158585112106955995705507840 }, { target := 966, numerator := 8533443736517449340682240 }, { target := 968, numerator := 293155082877840932418355200 }, { target := 971, numerator := 293154651309147640572149760 }, { target := 978, numerator := 8533587592748546622750720 }, { target := 982, numerator := 160419654588495638801940480 }, { target := 985, numerator := 547539387420540173209829376 }, { target := 987, numerator := 160441652892346115980001280 }]

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
  [{ target := 14, numerator := 136884171791798442043375616 }, { target := 15, numerator := 7095987483746686389897396224 }, { target := 20, numerator := 7097299797671622248880930816 }, { target := 28, numerator := 135646009639230837903851520 }, { target := 56, numerator := 1602990816282945152614400 }, { target := 57, numerator := 68346484308294031848243200 }, { target := 59, numerator := 656055493455058825537126400 }, { target := 67, numerator := 68347053619581926821068800 }, { target := 74, numerator := 1602848488460971409408000 }, { target := 136, numerator := 475753083422885173629288448 }, { target := 137, numerator := 24662734055603638337454211072 }, { target := 142, numerator := 24667295119078213353417474048 }, { target := 150, numerator := 471449741011919521248706560 }, { target := 152, numerator := 78191400273435632437559296 }, { target := 153, numerator := 3333835264399052923771813888 }, { target := 155, numerator := 32001367175191728421523685376 }, { target := 163, numerator := 3333863034518719113767944192 }, { target := 170, numerator := 78184457743519084938526720 }, { target := 267, numerator := 137066758139769779872858112 }, { target := 268, numerator := 7105452642668627279130656768 }, { target := 273, numerator := 7106766707056044004199104512 }, { target := 281, numerator := 135826944433902225866096640 }, { target := 283, numerator := 78162250662922982025854976 }, { target := 284, numerator := 3332592416731269350899580928 }, { target := 286, numerator := 31989437124242812638075027456 }, { target := 294, numerator := 3332620176498285897477783552 }, { target := 301, numerator := 78155310721168845381304320 }, { target := 660, numerator := 1602676970558012864331776 }, { target := 661, numerator := 68333102914154763363811328 }, { target := 663, numerator := 655927045924450596873568256 }, { target := 671, numerator := 68333672113978567559217152 }, { target := 678, numerator := 1602534670602061815480320 }, { target := 679, numerator := 250555611323156563218137088 }, { target := 681, numerator := 9110895628736541144347836416 }, { target := 684, numerator := 9115139363045321793217757184 }, { target := 691, numerator := 254808277458948589407436800 }, { target := 966, numerator := 9004020127735234147909632 }, { target := 968, numerator := 327411097239541495181082624 }, { target := 971, numerator := 327563600984842728716107776 }, { target := 978, numerator := 9156844849085510005555200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5.Parent0
