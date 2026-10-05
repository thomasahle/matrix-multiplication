import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 22; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent0

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
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 66666066970057065047273766912 }, { target := 89, numerator := 225979962462467494694923272192 }, { target := 91, numerator := 66666066970057065047273766912 }, { target := 112, numerator := 65277190574847542858788896768 }, { target := 115, numerator := 221272046577832755222112370688 }, { target := 117, numerator := 65277190574847542858788896768 }, { target := 122, numerator := 7253554917687775048237056000 }, { target := 124, numerator := 7253554917687775048237056000 }, { target := 161, numerator := 51388426622752320973940195328 }, { target := 164, numerator := 174192887731485360494003355648 }, { target := 166, numerator := 51388426622752320973940195328 }, { target := 197, numerator := 193428131138340667952988160000 }, { target := 199, numerator := 193428131138340667952988160000 }, { target := 211, numerator := 184965650401038263730044928000 }, { target := 213, numerator := 184965650401038263730044928000 }, { target := 215, numerator := 2030995376952577013506375680 }, { target := 242, numerator := 6044629098073145873530880000 }, { target := 244, numerator := 6044629098073145873530880000 }, { target := 256, numerator := 189801353679496780428869632000 }, { target := 258, numerator := 189801353679496780428869632000 }, { target := 260, numerator := 2089023816294079213892272128 }, { target := 261, numerator := 6044629098073145873530880000 }, { target := 263, numerator := 6044629098073145873530880000 }, { target := 265, numerator := 2030995376952577013506375680 }, { target := 337, numerator := 184965650401038263730044928000 }, { target := 339, numerator := 184965650401038263730044928000 }, { target := 351, numerator := 105176546306472738199437312000 }, { target := 353, numerator := 105176546306472738199437312000 }, { target := 355, numerator := 1798881619586568211962789888 }, { target := 382, numerator := 189801353679496780428869632000 }, { target := 384, numerator := 189801353679496780428869632000 }, { target := 396, numerator := 2963077183875456107204837376000 }, { target := 398, numerator := 2963077183875456107204837376000 }, { target := 400, numerator := 84199265484519692759935746048 }, { target := 401, numerator := 116056878683004400771792896000 }, { target := 403, numerator := 116056878683004400771792896000 }, { target := 405, numerator := 22921233539893369152429096960 }, { target := 416, numerator := 193428131138340667952988160000 }, { target := 418, numerator := 193428131138340667952988160000 }, { target := 420, numerator := 2089023816294079213892272128 }, { target := 421, numerator := 184965650401038263730044928000 }, { target := 423, numerator := 184965650401038263730044928000 }, { target := 425, numerator := 84199265484519692759935746048 }, { target := 426, numerator := 2030995376952577013506375680 }, { target := 453, numerator := 6044629098073145873530880000 }, { target := 455, numerator := 6044629098073145873530880000 }, { target := 467, numerator := 116056878683004400771792896000 }, { target := 469, numerator := 116056878683004400771792896000 }, { target := 471, numerator := 2030995376952577013506375680 }, { target := 472, numerator := 6044629098073145873530880000 }, { target := 474, numerator := 6044629098073145873530880000 }, { target := 476, numerator := 1740853180245066011576893440 }, { target := 487, numerator := 186174576220652892904751104000 }, { target := 489, numerator := 186174576220652892904751104000 }, { target := 491, numerator := 2030995376952577013506375680 }, { target := 492, numerator := 105176546306472738199437312000 }, { target := 494, numerator := 105176546306472738199437312000 }, { target := 496, numerator := 22921233539893369152429096960 }, { target := 497, numerator := 1740853180245066011576893440 }, { target := 498, numerator := 7253554917687775048237056000 }, { target := 500, numerator := 7253554917687775048237056000 }, { target := 502, numerator := 2030995376952577013506375680 }, { target := 503, numerator := 1798881619586568211962789888 }]

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
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 563554395578532231664107520 }, { target := 37, numerator := 20423397832931430241235107840 }, { target := 40, numerator := 20423405338450425231808921600 }, { target := 47, numerator := 563546890059537241090293760 }, { target := 70, numerator := 13816172278699499873055539200 }, { target := 72, numerator := 500702656549286676881892966400 }, { target := 75, numerator := 500702840555558812134670336000 }, { target := 82, numerator := 13815988272427364620278169600 }, { target := 96, numerator := 563554395578532231664107520 }, { target := 98, numerator := 20423397832931430241235107840 }, { target := 101, numerator := 20423405338450425231808921600 }, { target := 108, numerator := 563546890059537241090293760 }, { target := 145, numerator := 11580133870436291340968919040 }, { target := 147, numerator := 419667884502494227860218183680 }, { target := 150, numerator := 419668038728803899118138163200 }, { target := 157, numerator := 11579979644126620083048939520 }, { target := 171, numerator := 11380162955876167000701009920 }, { target := 173, numerator := 412420872368228236484296048640 }, { target := 176, numerator := 412421023931289232100399513600 }, { target := 183, numerator := 11380011392815171384597544960 }, { target := 187, numerator := 1615263247628674305207903977472 }, { target := 190, numerator := 5475306173830202006879078449152 }, { target := 192, numerator := 1615263247628674305207903977472 }, { target := 201, numerator := 51388426622752320973940195328 }, { target := 204, numerator := 174192887731485360494003355648 }, { target := 206, numerator := 51388426622752320973940195328 }, { target := 216, numerator := 563554395578532231664107520 }, { target := 218, numerator := 20423397832931430241235107840 }, { target := 221, numerator := 20423405338450425231808921600 }, { target := 228, numerator := 563546890059537241090293760 }, { target := 232, numerator := 51388426622752320973940195328 }, { target := 235, numerator := 174192887731485360494003355648 }, { target := 237, numerator := 51388426622752320973940195328 }, { target := 246, numerator := 52777303017961843162425065472 }, { target := 249, numerator := 178900803616120099966814257152 }, { target := 251, numerator := 52777303017961843162425065472 }, { target := 301, numerator := 52777303017961843162425065472 }, { target := 304, numerator := 178900803616120099966814257152 }, { target := 306, numerator := 52777303017961843162425065472 }, { target := 327, numerator := 893047522119722767195771502592 }, { target := 330, numerator := 3027189913820137481017409667072 }, { target := 332, numerator := 893047522119722767195771502592 }, { target := 341, numerator := 48610673832333276596970455040 }, { target := 344, numerator := 164777055962215881548381552640 }, { target := 346, numerator := 48610673832333276596970455040 }, { target := 372, numerator := 1615263247628674305207903977472 }, { target := 375, numerator := 5475306173830202006879078449152 }, { target := 377, numerator := 1615263247628674305207903977472 }, { target := 386, numerator := 893047522119722767195771502592 }, { target := 389, numerator := 3027189913820137481017409667072 }, { target := 391, numerator := 893047522119722767195771502592 }, { target := 406, numerator := 66666066970057065047273766912 }, { target := 409, numerator := 225979962462467494694923272192 }, { target := 411, numerator := 66666066970057065047273766912 }, { target := 443, numerator := 51388426622752320973940195328 }, { target := 446, numerator := 174192887731485360494003355648 }, { target := 448, numerator := 51388426622752320973940195328 }, { target := 457, numerator := 48610673832333276596970455040 }, { target := 460, numerator := 164777055962215881548381552640 }, { target := 462, numerator := 48610673832333276596970455040 }, { target := 477, numerator := 65277190574847542858788896768 }, { target := 480, numerator := 221272046577832755222112370688 }, { target := 482, numerator := 65277190574847542858788896768 }]

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
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 465559222080186843037433856 }, { target := 1, numerator := 39148522035051981953734541312 }, { target := 6, numerator := 39148512590319016214444113920 }, { target := 14, numerator := 465568666813152582327861248 }, { target := 16, numerator := 75558382540591396500275200 }, { target := 17, numerator := 11159577689521521775817523200 }, { target := 19, numerator := 116314411947635202911633408000 }, { target := 27, numerator := 11159577689521521775817523200 }, { target := 34, numerator := 75558382540591396500275200 }, { target := 51, numerator := 75042374074460528426614784 }, { target := 52, numerator := 11083365939446740651494866944 }, { target := 54, numerator := 115520069622139157623456399360 }, { target := 62, numerator := 11083365939446740651494866944 }, { target := 69, numerator := 75042374074460528426614784 }, { target := 86, numerator := 104379611958688223797046149120 }, { target := 89, numerator := 356880965299120976787232784384 }, { target := 91, numerator := 104379578243907684420496130048 }, { target := 122, numerator := 1003970704927243652101570560 }, { target := 124, numerator := 1003516731673608267531026432 }, { target := 126, numerator := 75558382540591396500275200 }, { target := 127, numerator := 11159577689521521775817523200 }, { target := 129, numerator := 116314411947635202911633408000 }, { target := 137, numerator := 11159577689521521775817523200 }, { target := 144, numerator := 75558382540591396500275200 }, { target := 161, numerator := 3653026178353996009601090191360 }, { target := 164, numerator := 12489944006593114542320440573952 }, { target := 166, numerator := 3653024998420735129616849567744 }, { target := 197, numerator := 105264517683044666614575267840 }, { target := 199, numerator := 105216919406172241001917186048 }, { target := 215, numerator := 467537893636509224381972480 }, { target := 232, numerator := 3653027970024908862085052497920 }, { target := 235, numerator := 12489950132437356329895192428544 }, { target := 237, numerator := 3653026790091069269548694765568 }, { target := 242, numerator := 1134646288861577263102033920000 }, { target := 244, numerator := 1134133227011314278438273024000 }, { target := 260, numerator := 39146543363495659572390002688 }, { target := 266, numerator := 75779529026076054246129664 }, { target := 267, numerator := 11192239868124999400527233024 }, { target := 269, numerator := 116654844372847793749423554560 }, { target := 277, numerator := 11192239868124999400527233024 }, { target := 284, numerator := 75779529026076054246129664 }, { target := 285, numerator := 11398342129927087395270819840 }, { target := 287, numerator := 413079691653161508427561697280 }, { target := 290, numerator := 413079843458336020011103027200 }, { target := 297, numerator := 11398190324752575811729489920 }, { target := 311, numerator := 10216695816617261748233175040 }, { target := 313, numerator := 370256438132498832115294535680 }, { target := 316, numerator := 370256574200294805815374643200 }, { target := 323, numerator := 10216559748821288048153067520 }, { target := 356, numerator := 13816172278699499873055539200 }, { target := 358, numerator := 500702656549286676881892966400 }, { target := 361, numerator := 500702840555558812134670336000 }, { target := 368, numerator := 13815988272427364620278169600 }, { target := 416, numerator := 105264597981429448446427791360 }, { target := 418, numerator := 105216999668247876738001928192 }, { target := 420, numerator := 39146557530595108181325643776 }, { target := 427, numerator := 563554395578532231664107520 }, { target := 429, numerator := 20423397832931430241235107840 }, { target := 432, numerator := 20423405338450425231808921600 }, { target := 439, numerator := 563546890059537241090293760 }, { target := 498, numerator := 1003970704927243652101570560 }, { target := 500, numerator := 1003516731673608267531026432 }, { target := 502, numerator := 467523726537060615446331392 }]

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
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 467537893636509224381972480 }, { target := 1, numerator := 39146543363495659572390002688 }, { target := 6, numerator := 39146557530595108181325643776 }, { target := 14, numerator := 467523726537060615446331392 }, { target := 16, numerator := 1033499255072162583045734400 }, { target := 17, numerator := 108360532909016568573827481600 }, { target := 19, numerator := 1168018238533976594369740800000 }, { target := 27, numerator := 108360615569118549871322726400 }, { target := 34, numerator := 1033499255072162583045734400 }, { target := 35, numerator := 102755026558552998523940372480 }, { target := 37, numerator := 3596169739780392958867999293440 }, { target := 40, numerator := 3596171503565377206644040007680 }, { target := 47, numerator := 102754144666060874635920015360 }, { target := 86, numerator := 579655949737918866854510592 }, { target := 87, numerator := 14210920058090914155142840320 }, { target := 88, numerator := 579655949737918866854510592 }, { target := 89, numerator := 11910994838163042522139459584 }, { target := 90, numerator := 11705310468901200343578181632 }, { target := 91, numerator := 579655949737918866854510592 }, { target := 92, numerator := 11724009047925004177992843264 }, { target := 93, numerator := 10508601411377754941039837184 }, { target := 94, numerator := 14210920058090914155142840320 }, { target := 95, numerator := 579655949737918866854510592 }, { target := 122, numerator := 75558382540591396500275200 }, { target := 123, numerator := 75042374074460528426614784 }, { target := 124, numerator := 75558382540591396500275200 }, { target := 125, numerator := 75779529026076054246129664 }, { target := 126, numerator := 1033031929664008510693703680 }, { target := 127, numerator := 108311534682824365737267691520 }, { target := 129, numerator := 1167490086629294110157045760000 }, { target := 137, numerator := 108311617305549284877354926080 }, { target := 144, numerator := 1033031929664008510693703680 }, { target := 145, numerator := 351326397745827265086264180736 }, { target := 147, numerator := 12295547990926295638938021265408 }, { target := 150, numerator := 12295554021426658176900714725376 }, { target := 157, numerator := 351323382495645996104917450752 }, { target := 197, numerator := 11159577689521521775817523200 }, { target := 198, numerator := 11083365939446740651494866944 }, { target := 199, numerator := 11159577689521521775817523200 }, { target := 200, numerator := 11192239868124999400527233024 }, { target := 215, numerator := 465559222080186843037433856 }, { target := 216, numerator := 102754993368516125129904750592 }, { target := 218, numerator := 3596168578211852092580011442176 }, { target := 221, numerator := 3596170341996266635003189788672 }, { target := 228, numerator := 102754111476308853918315577344 }, { target := 242, numerator := 116314411947635202911633408000 }, { target := 243, numerator := 115520069622139157623456399360 }, { target := 244, numerator := 116314411947635202911633408000 }, { target := 245, numerator := 116654844372847793749423554560 }, { target := 260, numerator := 39148522035051981953734541312 }, { target := 406, numerator := 104378716123231797555064995840 }, { target := 409, numerator := 356877902377000082999856857088 }, { target := 411, numerator := 104378682408740614454573531136 }, { target := 416, numerator := 11159577689521521775817523200 }, { target := 417, numerator := 11083365939446740651494866944 }, { target := 418, numerator := 11159577689521521775817523200 }, { target := 419, numerator := 11192239868124999400527233024 }, { target := 420, numerator := 39148512590319016214444113920 }, { target := 498, numerator := 75558382540591396500275200 }, { target := 499, numerator := 75042374074460528426614784 }, { target := 500, numerator := 75558382540591396500275200 }, { target := 501, numerator := 75779529026076054246129664 }, { target := 502, numerator := 465568666813152582327861248 }]

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
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 64771165841709189813371928576 }, { target := 36, numerator := 63421766553340248358926680064 }, { target := 37, numerator := 49927773669650833814474194944 }, { target := 38, numerator := 1569351372373078911519824019456 }, { target := 39, numerator := 49927773669650833814474194944 }, { target := 40, numerator := 49927773669650833814474194944 }, { target := 41, numerator := 51277172958019775268919443456 }, { target := 42, numerator := 51277172958019775268919443456 }, { target := 43, numerator := 867663742421229355208294793216 }, { target := 44, numerator := 47228975092912950905583697920 }, { target := 45, numerator := 1569351372373078911519824019456 }, { target := 46, numerator := 867663742421229355208294793216 }, { target := 47, numerator := 64771165841709189813371928576 }, { target := 48, numerator := 49927773669650833814474194944 }, { target := 49, numerator := 47228975092912950905583697920 }, { target := 50, numerator := 63421766553340248358926680064 }, { target := 145, numerator := 219556759395058857894809174016 }, { target := 146, numerator := 214982660240995131688667316224 }, { target := 147, numerator := 169241668700357869627248738304 }, { target := 148, numerator := 5319677316176113577742980612096 }, { target := 149, numerator := 169241668700357869627248738304 }, { target := 150, numerator := 169241668700357869627248738304 }, { target := 151, numerator := 173815767854421595833390596096 }, { target := 152, numerator := 173815767854421595833390596096 }, { target := 153, numerator := 2941145756062975950549214560256 }, { target := 154, numerator := 160093470392230417214965022720 }, { target := 155, numerator := 5319677316176113577742980612096 }, { target := 156, numerator := 2941145756062975950549214560256 }, { target := 157, numerator := 219556759395058857894809174016 }, { target := 158, numerator := 169241668700357869627248738304 }, { target := 159, numerator := 160093470392230417214965022720 }, { target := 160, numerator := 214982660240995131688667316224 }, { target := 161, numerator := 21006923485300899676698968064 }, { target := 162, numerator := 515008446736409153364232765440 }, { target := 163, numerator := 21006923485300899676698968064 }, { target := 164, numerator := 431658395488279777227652988928 }, { target := 165, numerator := 424204325864463328955275935744 }, { target := 166, numerator := 21006923485300899676698968064 }, { target := 167, numerator := 424881968557537551525492031488 }, { target := 168, numerator := 380835193507713084461445808128 }, { target := 169, numerator := 515008446736409153364232765440 }, { target := 170, numerator := 21006923485300899676698968064 }, { target := 232, numerator := 21006931205263294524146319360 }, { target := 233, numerator := 515008636000003349624232345600 }, { target := 234, numerator := 21006931205263294524146319360 }, { target := 235, numerator := 431658554121055439092942110720 }, { target := 236, numerator := 424204481757897495874696642560 }, { target := 237, numerator := 21006931205263294524146319360 }, { target := 238, numerator := 424882124700002763439991685120 }, { target := 239, numerator := 380835333463160371695813918720 }, { target := 240, numerator := 515008636000003349624232345600 }, { target := 241, numerator := 21006931205263294524146319360 }, { target := 406, numerator := 579648229775524019407159296 }, { target := 407, numerator := 14210730794496717895143260160 }, { target := 408, numerator := 579648229775524019407159296 }, { target := 409, numerator := 11910836205387380656850337792 }, { target := 410, numerator := 11705154575467033424157474816 }, { target := 411, numerator := 579648229775524019407159296 }, { target := 412, numerator := 11723852905459792263493189632 }, { target := 413, numerator := 10508461455930467706671726592 }, { target := 414, numerator := 14210730794496717895143260160 }, { target := 415, numerator := 579648229775524019407159296 }]

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
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 7369611796370779449008848896 }, { target := 17, numerator := 196522981236554118640235970560 }, { target := 18, numerator := 187925100807454875949725646848 }, { target := 19, numerator := 6141343163642316207507374080 }, { target := 20, numerator := 192838175338368728915731546112 }, { target := 21, numerator := 6141343163642316207507374080 }, { target := 22, numerator := 187925100807454875949725646848 }, { target := 23, numerator := 106859371047376302010628308992 }, { target := 24, numerator := 192838175338368728915731546112 }, { target := 25, numerator := 3010486418817463404920114774016 }, { target := 26, numerator := 117913788741932471184141582336 }, { target := 27, numerator := 196522981236554118640235970560 }, { target := 28, numerator := 187925100807454875949725646848 }, { target := 29, numerator := 6141343163642316207507374080 }, { target := 30, numerator := 117913788741932471184141582336 }, { target := 31, numerator := 6141343163642316207507374080 }, { target := 32, numerator := 189153369440183339191227121664 }, { target := 33, numerator := 106859371047376302010628308992 }, { target := 34, numerator := 7369611796370779449008848896 }, { target := 126, numerator := 7369611796370779449008848896 }, { target := 127, numerator := 196522981236554118640235970560 }, { target := 128, numerator := 187925100807454875949725646848 }, { target := 129, numerator := 6141343163642316207507374080 }, { target := 130, numerator := 192838175338368728915731546112 }, { target := 131, numerator := 6141343163642316207507374080 }, { target := 132, numerator := 187925100807454875949725646848 }, { target := 133, numerator := 106859371047376302010628308992 }, { target := 134, numerator := 192838175338368728915731546112 }, { target := 135, numerator := 3010486418817463404920114774016 }, { target := 136, numerator := 117913788741932471184141582336 }, { target := 137, numerator := 196522981236554118640235970560 }, { target := 138, numerator := 187925100807454875949725646848 }, { target := 139, numerator := 6141343163642316207507374080 }, { target := 140, numerator := 117913788741932471184141582336 }, { target := 141, numerator := 6141343163642316207507374080 }, { target := 142, numerator := 189153369440183339191227121664 }, { target := 143, numerator := 106859371047376302010628308992 }, { target := 144, numerator := 7369611796370779449008848896 }, { target := 216, numerator := 64771165841709189813371928576 }, { target := 217, numerator := 63421766553340248358926680064 }, { target := 218, numerator := 49927773669650833814474194944 }, { target := 219, numerator := 1569351372373078911519824019456 }, { target := 220, numerator := 49927773669650833814474194944 }, { target := 221, numerator := 49927773669650833814474194944 }, { target := 222, numerator := 51277172958019775268919443456 }, { target := 223, numerator := 51277172958019775268919443456 }, { target := 224, numerator := 867663742421229355208294793216 }, { target := 225, numerator := 47228975092912950905583697920 }, { target := 226, numerator := 1569351372373078911519824019456 }, { target := 227, numerator := 867663742421229355208294793216 }, { target := 228, numerator := 64771165841709189813371928576 }, { target := 229, numerator := 49927773669650833814474194944 }, { target := 230, numerator := 47228975092912950905583697920 }, { target := 231, numerator := 63421766553340248358926680064 }]

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

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2030995376952577013506375680 }, { target := 1, numerator := 2089023816294079213892272128 }, { target := 2, numerator := 2030995376952577013506375680 }, { target := 3, numerator := 1798881619586568211962789888 }, { target := 4, numerator := 84199265484519692759935746048 }, { target := 5, numerator := 22921233539893369152429096960 }, { target := 6, numerator := 2089023816294079213892272128 }, { target := 7, numerator := 84199265484519692759935746048 }, { target := 8, numerator := 2030995376952577013506375680 }, { target := 9, numerator := 2030995376952577013506375680 }, { target := 10, numerator := 1740853180245066011576893440 }, { target := 11, numerator := 2030995376952577013506375680 }, { target := 12, numerator := 22921233539893369152429096960 }, { target := 13, numerator := 1740853180245066011576893440 }, { target := 14, numerator := 2030995376952577013506375680 }, { target := 15, numerator := 1798881619586568211962789888 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent0
