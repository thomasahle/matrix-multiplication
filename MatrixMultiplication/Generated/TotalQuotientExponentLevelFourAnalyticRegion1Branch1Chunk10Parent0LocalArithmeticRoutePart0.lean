import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 1740853180245066011576893440 }, { target := 2, numerator := 3056164471985782553657212928 }, { target := 3, numerator := 116056878683004400771792896 }, { target := 4, numerator := 1934281311383406679529881600 }, { target := 5, numerator := 116056878683004400771792896 }, { target := 6, numerator := 3056164471985782553657212928 }, { target := 7, numerator := 3036821658871948486861914112 }, { target := 8, numerator := 1934281311383406679529881600 }, { target := 9, numerator := 46867636174819943845009031168 }, { target := 10, numerator := 2998136032644280353271316480 }, { target := 11, numerator := 1740853180245066011576893440 }, { target := 12, numerator := 3056164471985782553657212928 }, { target := 13, numerator := 116056878683004400771792896 }, { target := 14, numerator := 2998136032644280353271316480 }, { target := 15, numerator := 116056878683004400771792896 }, { target := 16, numerator := 3056164471985782553657212928 }, { target := 17, numerator := 3056164471985782553657212928 }, { target := 18, numerator := 116056878683004400771792896 }, { target := 19, numerator := 1182170466013465057878343680 }, { target := 21, numerator := 46111013235096985784108974080 }, { target := 24, numerator := 46110996321738513201663836160 }, { target := 31, numerator := 1182176103799622585360056320 }, { target := 35, numerator := 4064189338320951136776880128 }, { target := 38, numerator := 14618768189391270860065603584 }, { target := 40, numerator := 4064190694156640554428923904 }, { target := 45, numerator := 1293376685720253181932339200 }, { target := 47, numerator := 50448654561915925142123315200 }, { target := 50, numerator := 50448636057525776202229350400 }, { target := 57, numerator := 1293382853850302828563660800 }, { target := 61, numerator := 84839952437449854980217372672 }, { target := 64, numerator := 305166785953542779203869474816 }, { target := 66, numerator := 84839980740519871573703786496 }, { target := 75, numerator := 4402871783181030398174953472 }, { target := 78, numerator := 15836998871840543431737737216 }, { target := 80, numerator := 4402873252003027267298000896 }, { target := 90, numerator := 1182170466013465057878343680 }, { target := 92, numerator := 46111013235096985784108974080 }, { target := 95, numerator := 46110996321738513201663836160 }, { target := 102, numerator := 1182176103799622585360056320 }, { target := 106, numerator := 91274918889791360946780766208 }, { target := 109, numerator := 328313168920078958065640013824 }, { target := 111, numerator := 91274949339601219118216249344 }, { target := 120, numerator := 136658366501041981974122594304 }, { target := 123, numerator := 491556080368281482669705920512 }, { target := 125, numerator := 136658412091017038642672566272 }, { target := 140, numerator := 4233530560750990767475916800 }, { target := 143, numerator := 15227883530615907145901670400 }, { target := 145, numerator := 4233531973079833910863462400 }, { target := 161, numerator := 1293376685720253181932339200 }, { target := 163, numerator := 50448654561915925142123315200 }, { target := 166, numerator := 50448636057525776202229350400 }, { target := 173, numerator := 1293382853850302828563660800 }, { target := 177, numerator := 136658366501041981974122594304 }, { target := 180, numerator := 491556080368281482669705920512 }, { target := 182, numerator := 136658412091017038642672566272 }, { target := 191, numerator := 142415968063663329417889841152 }, { target := 194, numerator := 512266001969919116388132192256 }, { target := 196, numerator := 142416015574405612761446875136 }, { target := 211, numerator := 84839952437449854980217372672 }, { target := 214, numerator := 305166785953542779203869474816 }, { target := 216, numerator := 84839980740519871573703786496 }]

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
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 233020451730719773424615424 }, { target := 1, numerator := 27541521348869304115185844224 }, { target := 3, numerator := 261363547566391371118374027264 }, { target := 11, numerator := 27541540238335235593766699008 }, { target := 18, numerator := 233020451730719773424615424 }, { target := 19, numerator := 48364069110644642759615447040 }, { target := 21, numerator := 1892725912488831628282211336192 }, { target := 24, numerator := 1892725912488831628282211336192 }, { target := 31, numerator := 48364069110644642759615447040 }, { target := 71, numerator := 87245768950453451338561880064 }, { target := 73, numerator := 87245748149443665221828739072 }, { target := 85, numerator := 98503287524705509575795671040 }, { target := 87, numerator := 98503264039694460734322769920 }, { target := 89, numerator := 17408531802450660115768934400 }, { target := 116, numerator := 84431389306890436779253432320 }, { target := 118, numerator := 84431369176880966343705231360 }, { target := 130, numerator := 1111679959207390750926836858880 }, { target := 132, numerator := 1111679694162266056858785546240 }, { target := 134, numerator := 252423711135534571678649548800 }, { target := 135, numerator := 98503287524705509575795671040 }, { target := 137, numerator := 98503264039694460734322769920 }, { target := 139, numerator := 446818982929566942971402649600 }, { target := 150, numerator := 84431389306890436779253432320 }, { target := 152, numerator := 84431369176880966343705231360 }, { target := 154, numerator := 14507109835375550096474112000 }, { target := 155, numerator := 98503287524705509575795671040 }, { target := 157, numerator := 98503264039694460734322769920 }, { target := 159, numerator := 278536508839210561852302950400 }, { target := 160, numerator := 14507109835375550096474112000 }, { target := 187, numerator := 98503287524705509575795671040 }, { target := 189, numerator := 98503264039694460734322769920 }, { target := 201, numerator := 4083664862809934125556557676544 }, { target := 203, numerator := 4083663889188476072157209690112 }, { target := 205, numerator := 443917560962491832952107827200 }, { target := 206, numerator := 101317667168268524135104118784 }, { target := 208, numerator := 101317643012257159612446277632 }, { target := 210, numerator := 464227514732017603087171584000 }, { target := 221, numerator := 1111679959207390750926836858880 }, { target := 223, numerator := 1111679694162266056858785546240 }, { target := 225, numerator := 278536508839210561852302950400 }, { target := 226, numerator := 4083664862809934125556557676544 }, { target := 228, numerator := 4083663889188476072157209690112 }, { target := 230, numerator := 7111385241301094657291609702400 }, { target := 231, numerator := 455523248830792273029287116800 }, { target := 232, numerator := 87245768950453451338561880064 }, { target := 234, numerator := 87245748149443665221828739072 }, { target := 236, numerator := 252423711135534571678649548800 }, { target := 237, numerator := 443917560962491832952107827200 }, { target := 238, numerator := 4233530560750990767475916800 }, { target := 241, numerator := 15227883530615907145901670400 }, { target := 243, numerator := 4233531973079833910863462400 }, { target := 248, numerator := 98503287524705509575795671040 }, { target := 250, numerator := 98503264039694460734322769920 }, { target := 252, numerator := 14507109835375550096474112000 }, { target := 253, numerator := 101317667168268524135104118784 }, { target := 255, numerator := 101317643012257159612446277632 }, { target := 257, numerator := 455523248830792273029287116800 }, { target := 258, numerator := 14507109835375550096474112000 }, { target := 259, numerator := 98503287524705509575795671040 }, { target := 261, numerator := 98503264039694460734322769920 }, { target := 263, numerator := 443917560962491832952107827200 }, { target := 264, numerator := 464227514732017603087171584000 }, { target := 265, numerator := 17408531802450660115768934400 }]

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
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 778245996376917531217100800 }, { target := 1, numerator := 250689658163024837956180377600 }, { target := 3, numerator := 2666189936673132733623728865280 }, { target := 11, numerator := 250690413741662097099414568960 }, { target := 18, numerator := 778245996376917531217100800 }, { target := 19, numerator := 556664126114851479372756418560 }, { target := 21, numerator := 21785661722422371225090801008640 }, { target := 24, numerator := 21785669712663602706566936002560 }, { target := 31, numerator := 556672116356082960848891412480 }, { target := 35, numerator := 17433775267504034896275132383232 }, { target := 38, numerator := 62969001708455611888402106941440 }, { target := 40, numerator := 17436998386543828479723379359744 }, { target := 71, numerator := 1664329173373009697957774098432 }, { target := 73, numerator := 1664329832323873644418820997120 }, { target := 89, numerator := 10303618092177690020278173696 }, { target := 90, numerator := 605028593382848469645322616832 }, { target := 92, numerator := 23678403217236313468812331581440 }, { target := 95, numerator := 23678411207483260018215599734784 }, { target := 102, numerator := 605036583629795019048590770176 }, { target := 106, numerator := 62704211826002319672093035200512 }, { target := 109, numerator := 226503239021541037808675884892160 }, { target := 111, numerator := 62715719567816906465817378422784 }, { target := 116, numerator := 66075733994176386180988205531136 }, { target := 118, numerator := 66075760007147071508642913058816 }, { target := 134, numerator := 1814793444555938166724530012160 }, { target := 140, numerator := 17437775105489253790116866949120 }, { target := 143, numerator := 62983339029606758693848114790400 }, { target := 145, numerator := 17440999385635349751623885783040 }, { target := 150, numerator := 66075730995472145653239583342592 }, { target := 152, numerator := 66075757008445878791942113853440 }, { target := 154, numerator := 18771375091772472634861506527232 }, { target := 232, numerator := 1664337064444580505018425147392 }, { target := 234, numerator := 1664337723401088587712474120192 }, { target := 236, numerator := 1814794219024041357346345058304 }, { target := 265, numerator := 10303618092177690020278173696 }]

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
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 27257263220799448691192627200 }, { target := 1, numerator := 1762421134666696392239724101632 }, { target := 2, numerator := 464691742246749620690258755584 }, { target := 3, numerator := 15457143529588398831666630492160 }, { target := 4, numerator := 289677969192778984326395068416 }, { target := 5, numerator := 15087394228790572100333076480 }, { target := 6, numerator := 461674263400991506270192140288 }, { target := 7, numerator := 482796615321298307210658447360 }, { target := 8, numerator := 289677969192778984326395068416 }, { target := 9, numerator := 7395840650953138443583274090496 }, { target := 10, numerator := 473744178784023963950458601472 }, { target := 11, numerator := 1762421134666696392239724101632 }, { target := 12, numerator := 461674263400991506270192140288 }, { target := 13, numerator := 15087394228790572100333076480 }, { target := 14, numerator := 473744178784023963950458601472 }, { target := 15, numerator := 15087394228790572100333076480 }, { target := 16, numerator := 461674263400991506270192140288 }, { target := 17, numerator := 482796615321298307210658447360 }, { target := 18, numerator := 27257263220799448691192627200 }, { target := 19, numerator := 1119890700821977541083255537664 }, { target := 21, numerator := 44773022435564987832456039104512 }, { target := 24, numerator := 44773011493843151378530156150784 }, { target := 31, numerator := 1119890700821977541083255537664 }, { target := 35, numerator := 3670770219694289990481969414144 }, { target := 38, numerator := 13371737358559682899775097667584 }, { target := 40, numerator := 3670772688909714905281635287040 }, { target := 71, numerator := 47870558201352350486558146560 }, { target := 73, numerator := 47870558201352350486558146560 }, { target := 89, numerator := 233020451730719773424615424 }, { target := 90, numerator := 1119890967824759009324059066368 }, { target := 92, numerator := 44773033110286651528225272889344 }, { target := 95, numerator := 44773022168562206364215235575808 }, { target := 102, numerator := 1119890967824759009324059066368 }, { target := 106, numerator := 13635996599965974530480343613440 }, { target := 109, numerator := 49672672012726329219890376867840 }, { target := 111, numerator := 13636005772485942703775180390400 }, { target := 116, numerator := 1873412382769557836156882649088 }, { target := 118, numerator := 1873412382769557836156882649088 }, { target := 134, numerator := 27541521348869304115185844224 }, { target := 140, numerator := 3669997526515282431181521420288 }, { target := 143, numerator := 13368922622242763526301619847168 }, { target := 145, numerator := 3669999995210940157586917294080 }, { target := 150, numerator := 1873412382769557836156882649088 }, { target := 152, numerator := 1873412382769557836156882649088 }, { target := 154, numerator := 261363547566391371118374027264 }, { target := 232, numerator := 47870558201352350486558146560 }, { target := 234, numerator := 47870558201352350486558146560 }, { target := 236, numerator := 27541540238335235593766699008 }, { target := 265, numerator := 233020451730719773424615424 }]

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
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected,
    Slot22.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 87245768950453451338561880064 }, { target := 20, numerator := 98503287524705509575795671040 }, { target := 21, numerator := 84431389306890436779253432320 }, { target := 22, numerator := 1111679959207390750926836858880 }, { target := 23, numerator := 98503287524705509575795671040 }, { target := 24, numerator := 84431389306890436779253432320 }, { target := 25, numerator := 98503287524705509575795671040 }, { target := 26, numerator := 98503287524705509575795671040 }, { target := 27, numerator := 4083664862809934125556557676544 }, { target := 28, numerator := 101317667168268524135104118784 }, { target := 29, numerator := 1111679959207390750926836858880 }, { target := 30, numerator := 4083664862809934125556557676544 }, { target := 31, numerator := 87245768950453451338561880064 }, { target := 32, numerator := 98503287524705509575795671040 }, { target := 33, numerator := 101317667168268524135104118784 }, { target := 34, numerator := 98503287524705509575795671040 }, { target := 35, numerator := 3981246698763380705414086656 }, { target := 36, numerator := 83108524836685572225519058944 }, { target := 37, numerator := 4313017256993662430865260544 }, { target := 38, numerator := 89412165443060925009091362816 }, { target := 39, numerator := 133869420245918676219548663808 }, { target := 40, numerator := 4147131977878521568139673600 }, { target := 41, numerator := 133869420245918676219548663808 }, { target := 42, numerator := 139509519735833465552218619904 }, { target := 43, numerator := 83108524836685572225519058944 }, { target := 44, numerator := 4147131977878521568139673600 }, { target := 90, numerator := 87245748149443665221828739072 }, { target := 91, numerator := 98503264039694460734322769920 }, { target := 92, numerator := 84431369176880966343705231360 }, { target := 93, numerator := 1111679694162266056858785546240 }, { target := 94, numerator := 98503264039694460734322769920 }, { target := 95, numerator := 84431369176880966343705231360 }, { target := 96, numerator := 98503264039694460734322769920 }, { target := 97, numerator := 98503264039694460734322769920 }, { target := 98, numerator := 4083663889188476072157209690112 }, { target := 99, numerator := 101317643012257159612446277632 }, { target := 100, numerator := 1111679694162266056858785546240 }, { target := 101, numerator := 4083663889188476072157209690112 }, { target := 102, numerator := 87245748149443665221828739072 }, { target := 103, numerator := 98503264039694460734322769920 }, { target := 104, numerator := 101317643012257159612446277632 }, { target := 105, numerator := 98503264039694460734322769920 }, { target := 106, numerator := 14320425981444510230268346368 }, { target := 107, numerator := 298938892362654151056851730432 }, { target := 108, numerator := 15513794813231552749457375232 }, { target := 109, numerator := 321612900166607958921443278848 }, { target := 110, numerator := 481524323626071656492773146624 }, { target := 111, numerator := 14917110397338031489862860800 }, { target := 112, numerator := 481524323626071656492773146624 }, { target := 113, numerator := 501811593766451379318986637312 }, { target := 114, numerator := 298938892362654151056851730432 }, { target := 115, numerator := 14917110397338031489862860800 }, { target := 140, numerator := 3981248026928954012501803008 }, { target := 141, numerator := 83108552562141915010975137792 }, { target := 142, numerator := 4313018695839700180210286592 }, { target := 143, numerator := 89412195271446092197436325888 }, { target := 144, numerator := 133869464905486078670373126144 }, { target := 145, numerator := 4147133361384327096356044800 }, { target := 146, numerator := 133869464905486078670373126144 }, { target := 147, numerator := 139509566276968763521417347072 }, { target := 148, numerator := 83108552562141915010975137792 }, { target := 149, numerator := 4147133361384327096356044800 }]

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
    Slot23.Left0.expected,
    Slot23.Left2.expected,
    Slot23.Left5.expected,
    Slot23.Left12.expected,
    Slot24.Left0.expected,
    Slot24.Left1.expected,
    Slot24.Left2.expected,
    Slot24.Left3.expected,
    Slot24.Left4.expected,
    Slot24.Left5.expected,
    Slot24.Left6.expected,
    Slot24.Left7.expected,
    Slot24.Left8.expected,
    Slot24.Left9.expected,
    Slot24.Left10.expected,
    Slot24.Left11.expected,
    Slot24.Left12.expected,
    Slot24.Left13.expected,
    Slot24.Left14.expected,
    Slot24.Left15.expected,
    Slot24.Left16.expected,
    Slot24.Left17.expected,
    Slot24.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1182170466013465057878343680 }, { target := 72, numerator := 1293376685720253181932339200 }, { target := 73, numerator := 1182170466013465057878343680 }, { target := 74, numerator := 1293376685720253181932339200 }, { target := 89, numerator := 116056878683004400771792896 }, { target := 116, numerator := 46111013235096985784108974080 }, { target := 117, numerator := 50448654561915925142123315200 }, { target := 118, numerator := 46111013235096985784108974080 }, { target := 119, numerator := 50448654561915925142123315200 }, { target := 134, numerator := 1740853180245066011576893440 }, { target := 139, numerator := 3056164471985782553657212928 }, { target := 150, numerator := 46110996321738513201663836160 }, { target := 151, numerator := 50448636057525776202229350400 }, { target := 152, numerator := 46110996321738513201663836160 }, { target := 153, numerator := 50448636057525776202229350400 }, { target := 154, numerator := 116056878683004400771792896 }, { target := 159, numerator := 1934281311383406679529881600 }, { target := 160, numerator := 116056878683004400771792896 }, { target := 205, numerator := 3056164471985782553657212928 }, { target := 210, numerator := 3036821658871948486861914112 }, { target := 225, numerator := 1934281311383406679529881600 }, { target := 230, numerator := 46867636174819943845009031168 }, { target := 231, numerator := 2998136032644280353271316480 }, { target := 232, numerator := 1182176103799622585360056320 }, { target := 233, numerator := 1293382853850302828563660800 }, { target := 234, numerator := 1182176103799622585360056320 }, { target := 235, numerator := 1293382853850302828563660800 }, { target := 236, numerator := 1740853180245066011576893440 }, { target := 237, numerator := 3056164471985782553657212928 }, { target := 252, numerator := 116056878683004400771792896 }, { target := 257, numerator := 2998136032644280353271316480 }, { target := 258, numerator := 116056878683004400771792896 }, { target := 263, numerator := 3056164471985782553657212928 }, { target := 264, numerator := 3056164471985782553657212928 }, { target := 265, numerator := 116056878683004400771792896 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent0
