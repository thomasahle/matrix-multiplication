import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent3

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
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left3.expected,
    Slot3.Left11.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 367848269668849209825973764096 }, { target := 73, numerator := 367848269668849209825973764096 }, { target := 85, numerator := 1363668324525301709068566528 }, { target := 87, numerator := 1363668324525301709068566528 }, { target := 89, numerator := 24604998031727024023017619456 }, { target := 116, numerator := 12826105425080138047423638405120 }, { target := 118, numerator := 12826105425080138047423638405120 }, { target := 130, numerator := 33743537477083529524398784512 }, { target := 132, numerator := 33743537477083529524398784512 }, { target := 134, numerator := 2507201632337942310033672896512 }, { target := 135, numerator := 1073526127817790707139084288 }, { target := 137, numerator := 1073526127817790707139084288 }, { target := 139, numerator := 23675603251332897757445750784 }, { target := 150, numerator := 12826111715272293229791063048192 }, { target := 152, numerator := 12826111715272293229791063048192 }, { target := 154, numerator := 26759026237966597720250137968640 }, { target := 155, numerator := 1102540347488541807332032512 }, { target := 157, numerator := 1102540347488541807332032512 }, { target := 159, numerator := 24294573270975587894895312896 }, { target := 160, numerator := 773712524553362671811952640 }, { target := 187, numerator := 1102540347488541807332032512 }, { target := 189, numerator := 1102540347488541807332032512 }, { target := 201, numerator := 18656143248292957424065708032 }, { target := 203, numerator := 18656143248292957424065708032 }, { target := 205, numerator := 23675603251332897757445750784 }, { target := 206, numerator := 1015497688476288506753187840 }, { target := 208, numerator := 1015497688476288506753187840 }, { target := 210, numerator := 13462597927228510489527975936 }, { target := 221, numerator := 33743537477083529524398784512 }, { target := 223, numerator := 33743537477083529524398784512 }, { target := 225, numerator := 24294573270975587894895312896 }, { target := 226, numerator := 18656143248292957424065708032 }, { target := 228, numerator := 18656143248292957424065708032 }, { target := 230, numerator := 379273879536058381722219184128 }, { target := 231, numerator := 14855280471424563298789490688 }, { target := 232, numerator := 367845124572771618642261442560 }, { target := 234, numerator := 367845124572771618642261442560 }, { target := 236, numerator := 2507203526006901940761403588608 }, { target := 237, numerator := 23675603251332897757445750784 }, { target := 248, numerator := 1073526127817790707139084288 }, { target := 250, numerator := 1073526127817790707139084288 }, { target := 252, numerator := 773712524553362671811952640 }, { target := 253, numerator := 1015497688476288506753187840 }, { target := 255, numerator := 1015497688476288506753187840 }, { target := 257, numerator := 14855280471424563298789490688 }, { target := 258, numerator := 773712524553362671811952640 }, { target := 259, numerator := 1363668324525301709068566528 }, { target := 261, numerator := 1363668324525301709068566528 }, { target := 263, numerator := 23830345756243570291808141312 }, { target := 264, numerator := 13462597927228510489527975936 }, { target := 265, numerator := 24604998031727024023017619456 }]

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
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 928664990305082168290836480 }, { target := 20, numerator := 1102789675987285074845368320 }, { target := 21, numerator := 841602647463980715013570560 }, { target := 22, numerator := 8677213503163111509967503360 }, { target := 23, numerator := 1044748114093217439327191040 }, { target := 24, numerator := 841602647463980715013570560 }, { target := 25, numerator := 1044748114093217439327191040 }, { target := 26, numerator := 1044748114093217439327191040 }, { target := 27, numerator := 44750044220326146984514682880 }, { target := 28, numerator := 1044748114093217439327191040 }, { target := 29, numerator := 8677213503163111509967503360 }, { target := 30, numerator := 44750044220326146984514682880 }, { target := 31, numerator := 928664990305082168290836480 }, { target := 32, numerator := 1044748114093217439327191040 }, { target := 33, numerator := 1044748114093217439327191040 }, { target := 34, numerator := 1102789675987285074845368320 }, { target := 35, numerator := 13728158898750699730103164731392 }, { target := 38, numerator := 49914721984491365662731911823360 }, { target := 40, numerator := 13728158801149949613625439158272 }, { target := 71, numerator := 3739051857854694676264438988800 }, { target := 73, numerator := 3739050074936257483597393428480 }, { target := 89, numerator := 39165758672714456158764531712 }, { target := 90, numerator := 928245068622988244057849856 }, { target := 91, numerator := 1102291018989798539818696704 }, { target := 92, numerator := 841222093439583096177426432 }, { target := 93, numerator := 8673289859946046405415534592 }, { target := 94, numerator := 1044275702200861774565081088 }, { target := 95, numerator := 841222093439583096177426432 }, { target := 96, numerator := 1044275702200861774565081088 }, { target := 97, numerator := 1044275702200861774565081088 }, { target := 98, numerator := 44729809244270246010537639936 }, { target := 99, numerator := 1044275702200861774565081088 }, { target := 100, numerator := 8673289859946046405415534592 }, { target := 101, numerator := 44729809244270246010537639936 }, { target := 102, numerator := 928245068622988244057849856 }, { target := 103, numerator := 1044275702200861774565081088 }, { target := 104, numerator := 1044275702200861774565081088 }, { target := 105, numerator := 1102291018989798539818696704 }, { target := 106, numerator := 46543364329982050863855765028864 }, { target := 109, numerator := 169228240308947964806825261400064 }, { target := 111, numerator := 46543363996278473490213560647680 }, { target := 116, numerator := 135504476959201253217994906009600 }, { target := 118, numerator := 135504412345646941263450247004160 }, { target := 134, numerator := 5784577593920889073160098414592 }, { target := 140, numerator := 13728158803921235140728246501376 }, { target := 143, numerator := 49914721645245217234884092755968 }, { target := 145, numerator := 13728158706320516549447912521728 }, { target := 150, numerator := 135504526756567687692921339904000 }, { target := 152, numerator := 135504462142989630509341369958400 }, { target := 154, numerator := 60291684857764811476300181012480 }, { target := 232, numerator := 3739002060488260201338005094400 }, { target := 234, numerator := 3739000277593568237706270474240 }, { target := 236, numerator := 5784577593920889073160098414592 }, { target := 265, numerator := 39165758672714456158764531712 }]

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8554434657456841954544320512 }, { target := 1, numerator := 1255168818930026984839479033856 }, { target := 2, numerator := 28163135893742401253955076096 }, { target := 3, numerator := 12395921554215190339814195986432 }, { target := 4, numerator := 14855280471424563298789490688 }, { target := 5, numerator := 1083197534374707740536733696 }, { target := 6, numerator := 28163135893742401253955076096 }, { target := 7, numerator := 28163135893742401253955076096 }, { target := 8, numerator := 14855280471424563298789490688 }, { target := 9, numerator := 347551666029370512177929125888 }, { target := 10, numerator := 27853650883921056185230295040 }, { target := 11, numerator := 1255168818930026984839479033856 }, { target := 12, numerator := 28163135893742401253955076096 }, { target := 13, numerator := 1083197534374707740536733696 }, { target := 14, numerator := 27853650883921056185230295040 }, { target := 15, numerator := 1083197534374707740536733696 }, { target := 16, numerator := 28163135893742401253955076096 }, { target := 17, numerator := 28163135893742401253955076096 }, { target := 18, numerator := 8708289357468734995606536192 }, { target := 19, numerator := 2438837684763403600913370185728 }, { target := 21, numerator := 91505956016525534700631368925184 }, { target := 24, numerator := 91499586228883283565336649007104 }, { target := 31, numerator := 2445207472405654736208090103808 }, { target := 35, numerator := 42368706000589054919875074457600 }, { target := 38, numerator := 145444359501347278301451234836480 }, { target := 40, numerator := 42368706000589054919875074457600 }, { target := 71, numerator := 2242970999131172774086352830464 }, { target := 73, numerator := 2242970999131172774086352830464 }, { target := 89, numerator := 8388887378033363671932993536 }, { target := 90, numerator := 2438837684763403600913370185728 }, { target := 92, numerator := 91505956016525534700631368925184 }, { target := 95, numerator := 91499586228883283565336649007104 }, { target := 102, numerator := 2445207472405654736208090103808 }, { target := 106, numerator := 145444359501347278301451234836480 }, { target := 109, numerator := 499285055117402971691192474927104 }, { target := 111, numerator := 145444359501347278301451234836480 }, { target := 116, numerator := 84274182466445483878063640936448 }, { target := 118, numerator := 84274182466445483878063640936448 }, { target := 134, numerator := 1228739660450930591393669709824 }, { target := 140, numerator := 42368706000589054919875074457600 }, { target := 143, numerator := 145444359501347278301451234836480 }, { target := 145, numerator := 42368706000589054919875074457600 }, { target := 150, numerator := 84267808631735156923482972880896 }, { target := 152, numerator := 84267808631735156923482972880896 }, { target := 154, numerator := 12131269841756242766212106289152 }, { target := 232, numerator := 2249344833841499728667020886016 }, { target := 234, numerator := 2249344833841499728667020886016 }, { target := 236, numerator := 1215741290038434098507228905472 }, { target := 265, numerator := 7614305938047152985401720832 }]

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
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected,
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot17.Left16.expected,
    Slot17.Left17.expected,
    Slot17.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected,
    Slot22.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 39165758672714456158764531712 }, { target := 1, numerator := 5784577593920889073160098414592 }, { target := 3, numerator := 60291684857764811476300181012480 }, { target := 11, numerator := 5784577593920889073160098414592 }, { target := 18, numerator := 39165758672714456158764531712 }, { target := 19, numerator := 3736924374578532687828442152960 }, { target := 21, numerator := 135427376261073684937358778040320 }, { target := 24, numerator := 135427426030105913759667899596800 }, { target := 31, numerator := 3736874605546303865519320596480 }, { target := 35, numerator := 13447608878673117939624535130112 }, { target := 38, numerator := 45583762290602915263369174843392 }, { target := 40, numerator := 13447608878673117939624535130112 }, { target := 71, numerator := 202504880594984624844475203584 }, { target := 73, numerator := 202504460673302530920242216960 }, { target := 85, numerator := 1102789675987285074845368320 }, { target := 87, numerator := 1102291018989798539818696704 }, { target := 90, numerator := 3736922592674558332824365039616 }, { target := 92, numerator := 135427311684283842008108312297472 }, { target := 95, numerator := 135427361453292339112181005025280 }, { target := 102, numerator := 3736872823666061228751672311808 }, { target := 106, numerator := 48911852255860979296367164784640 }, { target := 109, numerator := 165797969478440928091935332106240 }, { target := 111, numerator := 48911852255860979296367164784640 }, { target := 116, numerator := 7444783069669293015815820410880 }, { target := 118, numerator := 7444782689115268618196984266752 }, { target := 130, numerator := 8677213503163111509967503360 }, { target := 132, numerator := 8673289859946046405415534592 }, { target := 135, numerator := 1044748114093217439327191040 }, { target := 137, numerator := 1044275702200861774565081088 }, { target := 139, numerator := 28163135893742401253955076096 }, { target := 140, numerator := 13447608878673117939624535130112 }, { target := 143, numerator := 45583762290602915263369174843392 }, { target := 145, numerator := 13447608878673117939624535130112 }, { target := 150, numerator := 7444781246835830628132767924224 }, { target := 152, numerator := 7444780866281806230513931780096 }, { target := 154, numerator := 928455029464035206174343168 }, { target := 155, numerator := 1044748114093217439327191040 }, { target := 157, numerator := 1044275702200861774565081088 }, { target := 159, numerator := 14855280471424563298789490688 }, { target := 160, numerator := 1083197534374707740536733696 }, { target := 187, numerator := 1044748114093217439327191040 }, { target := 189, numerator := 1044275702200861774565081088 }, { target := 205, numerator := 28163135893742401253955076096 }, { target := 210, numerator := 28163135893742401253955076096 }, { target := 225, numerator := 14855280471424563298789490688 }, { target := 230, numerator := 347551666029370512177929125888 }, { target := 231, numerator := 27853650883921056185230295040 }, { target := 232, numerator := 201578038438141930359236853760 }, { target := 234, numerator := 201578038438141930359236853760 }, { target := 236, numerator := 12998370412496492886440804352 }, { target := 237, numerator := 28163135893742401253955076096 }, { target := 252, numerator := 1083197534374707740536733696 }, { target := 257, numerator := 27853650883921056185230295040 }, { target := 258, numerator := 1083197534374707740536733696 }, { target := 263, numerator := 28163135893742401253955076096 }, { target := 264, numerator := 28163135893742401253955076096 }, { target := 265, numerator := 928455029464035206174343168 }]

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
    Slot22.Left8.expected,
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected,
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 22790886780233201205240659968 }, { target := 1, numerator := 2389583374012874304116649623552 }, { target := 3, numerator := 25757320386086356912781131776000 }, { target := 11, numerator := 2389585196846336691799702110208 }, { target := 18, numerator := 22790886780233201205240659968 }, { target := 19, numerator := 360695232682932556610932834304 }, { target := 20, numerator := 1363668324525301709068566528 }, { target := 21, numerator := 12575766964590077742112355385344 }, { target := 22, numerator := 33743537477083529524398784512 }, { target := 23, numerator := 1073526127817790707139084288 }, { target := 24, numerator := 12575773132000704369869004472320 }, { target := 25, numerator := 1102540347488541807332032512 }, { target := 26, numerator := 1102540347488541807332032512 }, { target := 27, numerator := 18656143248292957424065708032 }, { target := 28, numerator := 1015497688476288506753187840 }, { target := 29, numerator := 33743537477083529524398784512 }, { target := 30, numerator := 18656143248292957424065708032 }, { target := 31, numerator := 360692148977619242732608290816 }, { target := 32, numerator := 1073526127817790707139084288 }, { target := 33, numerator := 1015497688476288506753187840 }, { target := 34, numerator := 1363668324525301709068566528 }, { target := 35, numerator := 304073523089768356552093204480 }, { target := 38, numerator := 1039647977280570716451699163136 }, { target := 40, numerator := 304073424873537174699499323392 }, { target := 90, numerator := 359302550138736503801671319552 }, { target := 92, numerator := 12574693438462259951405216301056 }, { target := 95, numerator := 12574699605872886579161865388032 }, { target := 102, numerator := 359299466433423189923346776064 }, { target := 106, numerator := 1087802952318346867274164469760 }, { target := 109, numerator := 3719271995686811244045986168832 }, { target := 111, numerator := 1087802600956264567003209007104 }, { target := 140, numerator := 304073422003277164485877432320 }, { target := 143, numerator := 1039647631659008436607987482624 }, { target := 145, numerator := 304073323787078633730581987328 }, { target := 201, numerator := 44750044220326146984514682880 }, { target := 203, numerator := 44729809244270246010537639936 }, { target := 206, numerator := 1044748114093217439327191040 }, { target := 208, numerator := 1044275702200861774565081088 }, { target := 221, numerator := 8677213503163111509967503360 }, { target := 223, numerator := 8673289859946046405415534592 }, { target := 226, numerator := 44750044220326146984514682880 }, { target := 228, numerator := 44729809244270246010537639936 }, { target := 232, numerator := 928664990305082168290836480 }, { target := 234, numerator := 928245068622988244057849856 }, { target := 248, numerator := 1044748114093217439327191040 }, { target := 250, numerator := 1044275702200861774565081088 }, { target := 253, numerator := 1044748114093217439327191040 }, { target := 255, numerator := 1044275702200861774565081088 }, { target := 259, numerator := 1102789675987285074845368320 }, { target := 261, numerator := 1102291018989798539818696704 }]

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
    Slot27.Left2.expected,
    Slot28.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 928455029464035206174343168 }, { target := 1, numerator := 24758800785707605497982484480 }, { target := 2, numerator := 23675603251332897757445750784 }, { target := 3, numerator := 773712524553362671811952640 }, { target := 4, numerator := 24294573270975587894895312896 }, { target := 5, numerator := 773712524553362671811952640 }, { target := 6, numerator := 23675603251332897757445750784 }, { target := 7, numerator := 13462597927228510489527975936 }, { target := 8, numerator := 24294573270975587894895312896 }, { target := 9, numerator := 379273879536058381722219184128 }, { target := 10, numerator := 14855280471424563298789490688 }, { target := 11, numerator := 24758800785707605497982484480 }, { target := 12, numerator := 23675603251332897757445750784 }, { target := 13, numerator := 773712524553362671811952640 }, { target := 14, numerator := 14855280471424563298789490688 }, { target := 15, numerator := 773712524553362671811952640 }, { target := 16, numerator := 23830345756243570291808141312 }, { target := 17, numerator := 13462597927228510489527975936 }, { target := 18, numerator := 928455029464035206174343168 }, { target := 90, numerator := 1392682544196052809261514752 }, { target := 91, numerator := 1363668324525301709068566528 }, { target := 92, numerator := 1073526127817790707139084288 }, { target := 93, numerator := 33743537477083529524398784512 }, { target := 94, numerator := 1073526127817790707139084288 }, { target := 95, numerator := 1073526127817790707139084288 }, { target := 96, numerator := 1102540347488541807332032512 }, { target := 97, numerator := 1102540347488541807332032512 }, { target := 98, numerator := 18656143248292957424065708032 }, { target := 99, numerator := 1015497688476288506753187840 }, { target := 100, numerator := 33743537477083529524398784512 }, { target := 101, numerator := 18656143248292957424065708032 }, { target := 102, numerator := 1392682544196052809261514752 }, { target := 103, numerator := 1073526127817790707139084288 }, { target := 104, numerator := 1015497688476288506753187840 }, { target := 105, numerator := 1363668324525301709068566528 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent3
