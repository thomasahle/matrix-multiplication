import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left7.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 12541030487726484734607360 }, { target := 132, numerator := 223230342681531428276011008 }, { target := 133, numerator := 12541030487726484734607360 }, { target := 134, numerator := 198566316055669341631283200 }, { target := 135, numerator := 339025857518205970658885632 }, { target := 136, numerator := 12541030487726484734607360 }, { target := 137, numerator := 339025857518205970658885632 }, { target := 138, numerator := 339025857518205970658885632 }, { target := 139, numerator := 223230342681531428276011008 }, { target := 140, numerator := 12541030487726484734607360 }, { target := 227, numerator := 1314904428047583794996183040 }, { target := 228, numerator := 23405298819246991550932058112 }, { target := 229, numerator := 1314904428047583794996183040 }, { target := 230, numerator := 20819320110753410087439564800 }, { target := 231, numerator := 35546249704886348591396814848 }, { target := 232, numerator := 1314904428047583794996183040 }, { target := 233, numerator := 35546249704886348591396814848 }, { target := 234, numerator := 35546249704886348591396814848 }, { target := 235, numerator := 23405298819246991550932058112 }, { target := 236, numerator := 1314904428047583794996183040 }, { target := 263, numerator := 2103920521364291509718876160 }, { target := 265, numerator := 2103920521364291509718876160 }, { target := 302, numerator := 14173355488923308544491520000 }, { target := 303, numerator := 252285727702834892091949056000 }, { target := 304, numerator := 14173355488923308544491520000 }, { target := 305, numerator := 224411461907952385287782400000 }, { target := 306, numerator := 383153043383893440986087424000 }, { target := 307, numerator := 14173355488923308544491520000 }, { target := 308, numerator := 383153043383893440986087424000 }, { target := 309, numerator := 383153043383893440986087424000 }, { target := 310, numerator := 252285727702834892091949056000 }, { target := 311, numerator := 14173355488923308544491520000 }, { target := 338, numerator := 176159445135730468075755012096 }, { target := 340, numerator := 176159445135730468075755012096 }, { target := 356, numerator := 8578589562016720189812375552 }, { target := 572, numerator := 43057101991394632686335164416 }, { target := 589, numerator := 1314905431089292802953052160 }, { target := 590, numerator := 23405316673389411892564328448 }, { target := 591, numerator := 1314905431089292802953052160 }, { target := 592, numerator := 20819335992247136046756659200 }, { target := 593, numerator := 35546276820447215439830843392 }, { target := 594, numerator := 1314905431089292802953052160 }, { target := 595, numerator := 35546276820447215439830843392 }, { target := 596, numerator := 35546276820447215439830843392 }, { target := 597, numerator := 23405316673389411892564328448 }, { target := 598, numerator := 1314905431089292802953052160 }, { target := 599, numerator := 176159508887677986815965396992 }, { target := 601, numerator := 176159508887677986815965396992 }, { target := 617, numerator := 97874530463937754852017307648 }, { target := 763, numerator := 12541030487726484734607360 }, { target := 764, numerator := 223230342681531428276011008 }, { target := 765, numerator := 12541030487726484734607360 }, { target := 766, numerator := 198566316055669341631283200 }, { target := 767, numerator := 339025857518205970658885632 }, { target := 768, numerator := 12541030487726484734607360 }, { target := 769, numerator := 339025857518205970658885632 }, { target := 770, numerator := 339025857518205970658885632 }, { target := 771, numerator := 223230342681531428276011008 }, { target := 772, numerator := 12541030487726484734607360 }, { target := 773, numerator := 2103856769416772769508491264 }, { target := 775, numerator := 2103856769416772769508491264 }, { target := 777, numerator := 6779707942430151977849585664 }]

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
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
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
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 9548741021489158107753873408 }, { target := 81, numerator := 11339129963018375252957724672 }, { target := 82, numerator := 8653546550724549535151947776 }, { target := 83, numerator := 89221048919539321069325254656 }, { target := 84, numerator := 10742333649175302871223107584 }, { target := 85, numerator := 8653546550724549535151947776 }, { target := 86, numerator := 10742333649175302871223107584 }, { target := 87, numerator := 10742333649175302871223107584 }, { target := 88, numerator := 460129957973008806317389774848 }, { target := 89, numerator := 10742333649175302871223107584 }, { target := 90, numerator := 89221048919539321069325254656 }, { target := 91, numerator := 460129957973008806317389774848 }, { target := 92, numerator := 9548741021489158107753873408 }, { target := 93, numerator := 10742333649175302871223107584 }, { target := 94, numerator := 10742333649175302871223107584 }, { target := 95, numerator := 11339129963018375252957724672 }, { target := 131, numerator := 7695013106353158487476797440 }, { target := 134, numerator := 27528401322689840798792417280 }, { target := 136, numerator := 7695010548215683398720552960 }, { target := 176, numerator := 346049535263236325857019559936 }, { target := 177, numerator := 410933823125093136955210727424 }, { target := 178, numerator := 313607391332307920307923976192 }, { target := 179, numerator := 3233400345115864419726526513152 }, { target := 180, numerator := 389305727171140866589147004928 }, { target := 181, numerator := 313607391332307920307923976192 }, { target := 182, numerator := 389305727171140866589147004928 }, { target := 183, numerator := 389305727171140866589147004928 }, { target := 184, numerator := 16675261980497200452235130044416 }, { target := 185, numerator := 389305727171140866589147004928 }, { target := 186, numerator := 3233400345115864419726526513152 }, { target := 187, numerator := 16675261980497200452235130044416 }, { target := 188, numerator := 346049535263236325857019559936 }, { target := 189, numerator := 389305727171140866589147004928 }, { target := 190, numerator := 389305727171140866589147004928 }, { target := 191, numerator := 410933823125093136955210727424 }, { target := 227, numerator := 1136513166306885300917412823040 }, { target := 230, numerator := 4065800813878562906784116244480 }, { target := 232, numerator := 1136512788483367461675451023360 }, { target := 263, numerator := 27002434880650836896171163648 }, { target := 265, numerator := 27002434880650836896171163648 }, { target := 302, numerator := 11845686663739530550714145177600 }, { target := 305, numerator := 42377161924913145926659552051200 }, { target := 307, numerator := 11845682725748190724078593638400 }, { target := 338, numerator := 2270614278033014953316603396096 }, { target := 340, numerator := 2270614278033014953316603396096 }, { target := 589, numerator := 1136513166306885300917412823040 }, { target := 592, numerator := 4065800813878562906784116244480 }, { target := 594, numerator := 1136512788483367461675451023360 }, { target := 599, numerator := 2270613730238502940437758607360 }, { target := 601, numerator := 2270613730238502940437758607360 }, { target := 622, numerator := 37370314935927417048517312512 }, { target := 712, numerator := 1798881619586568211962789888 }, { target := 757, numerator := 37312286496585914848131416064 }, { target := 762, numerator := 37486371814610421449289105408 }, { target := 763, numerator := 7695013106353158487476797440 }, { target := 766, numerator := 27528401322689840798792417280 }, { target := 768, numerator := 7695010548215683398720552960 }, { target := 773, numerator := 27002982675162849775015952384 }, { target := 775, numerator := 27002982675162849775015952384 }, { target := 777, numerator := 1798881619586568211962789888 }, { target := 782, numerator := 43057101991394632686335164416 }, { target := 783, numerator := 1798881619586568211962789888 }]

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
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 94876520943676018017278361600 }, { target := 265, numerator := 94876475703036177244603023360 }, { target := 286, numerator := 346049662435089970010668400640 }, { target := 287, numerator := 410933974141669339387668725760 }, { target := 288, numerator := 313607506581800285322168238080 }, { target := 289, numerator := 3233401533377871907287182868480 }, { target := 290, numerator := 389305870239476216262001950720 }, { target := 291, numerator := 313607506581800285322168238080 }, { target := 292, numerator := 389305870239476216262001950720 }, { target := 293, numerator := 389305870239476216262001950720 }, { target := 294, numerator := 16675268108590897929889083555840 }, { target := 295, numerator := 389305870239476216262001950720 }, { target := 296, numerator := 3233401533377871907287182868480 }, { target := 297, numerator := 16675268108590897929889083555840 }, { target := 298, numerator := 346049662435089970010668400640 }, { target := 299, numerator := 389305870239476216262001950720 }, { target := 300, numerator := 389305870239476216262001950720 }, { target := 301, numerator := 410933974141669339387668725760 }, { target := 338, numerator := 73792849622859125124549836800 }, { target := 340, numerator := 73792814435694804523580129280 }, { target := 352, numerator := 84334685283267571570914099200 }, { target := 354, numerator := 84334645069365490884091576320 }, { target := 479, numerator := 99093255207839396595824066560 }, { target := 481, numerator := 99093207956504451788807602176 }, { target := 554, numerator := 1170143758305337555546433126400 }, { target := 556, numerator := 1170143200337446186016770621440 }, { target := 568, numerator := 2631242180837948233012519895040 }, { target := 570, numerator := 2631240926164203315583657181184 }, { target := 573, numerator := 9548613849635513954105032704 }, { target := 574, numerator := 11338978946442172820499726336 }, { target := 575, numerator := 8653431301232184520907685888 }, { target := 576, numerator := 89219860657531833508668899328 }, { target := 577, numerator := 10742190580839953198368161792 }, { target := 578, numerator := 8653431301232184520907685888 }, { target := 579, numerator := 10742190580839953198368161792 }, { target := 580, numerator := 10742190580839953198368161792 }, { target := 581, numerator := 460123829879311328663436263424 }, { target := 582, numerator := 10742190580839953198368161792 }, { target := 583, numerator := 89219860657531833508668899328 }, { target := 584, numerator := 460123829879311328663436263424 }, { target := 585, numerator := 9548613849635513954105032704 }, { target := 586, numerator := 10742190580839953198368161792 }, { target := 587, numerator := 10742190580839953198368161792 }, { target := 588, numerator := 11338978946442172820499726336 }, { target := 599, numerator := 73792849622859125124549836800 }, { target := 601, numerator := 73792814435694804523580129280 }, { target := 613, numerator := 1170143758305337555546433126400 }, { target := 615, numerator := 1170143200337446186016770621440 }, { target := 618, numerator := 84334685283267571570914099200 }, { target := 620, numerator := 84334645069365490884091576320 }, { target := 694, numerator := 82226318151185882281641246720 }, { target := 696, numerator := 82226278942631353611989286912 }, { target := 708, numerator := 82226318151185882281641246720 }, { target := 710, numerator := 82226278942631353611989286912 }, { target := 739, numerator := 82226318151185882281641246720 }, { target := 741, numerator := 82226278942631353611989286912 }, { target := 753, numerator := 2631242180837948233012519895040 }, { target := 755, numerator := 2631240926164203315583657181184 }, { target := 758, numerator := 82226318151185882281641246720 }, { target := 760, numerator := 82226278942631353611989286912 }, { target := 773, numerator := 94876520943676018017278361600 }, { target := 775, numerator := 94876475703036177244603023360 }, { target := 778, numerator := 99093255207839396595824066560 }, { target := 780, numerator := 99093207956504451788807602176 }]

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
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 22412465928096894104790630400 }, { target := 27, numerator := 376529427592027820960482590720 }, { target := 28, numerator := 815813759782726945414378946560 }, { target := 29, numerator := 26894959113716272925748756480 }, { target := 30, numerator := 430319345819460366811980103680 }, { target := 31, numerator := 31377452299335651746706882560 }, { target := 32, numerator := 815813759782726945414378946560 }, { target := 33, numerator := 815813759782726945414378946560 }, { target := 34, numerator := 430319345819460366811980103680 }, { target := 35, numerator := 10067679694901124831871951175680 }, { target := 36, numerator := 806848773411488187772462694400 }, { target := 37, numerator := 376529427592027820960482590720 }, { target := 38, numerator := 815813759782726945414378946560 }, { target := 39, numerator := 31377452299335651746706882560 }, { target := 40, numerator := 806848773411488187772462694400 }, { target := 41, numerator := 31377452299335651746706882560 }, { target := 42, numerator := 815813759782726945414378946560 }, { target := 43, numerator := 815813759782726945414378946560 }, { target := 44, numerator := 26894959113716272925748756480 }, { target := 80, numerator := 85997120253127031002880802816 }, { target := 82, numerator := 3175759241120776233877273313280 }, { target := 85, numerator := 3175758463457459179628638765056 }, { target := 92, numerator := 85997897916444085251515351040 }, { target := 131, numerator := 25593212196095418036620623872 }, { target := 134, numerator := 93088029625370487222530211840 }, { target := 136, numerator := 25593212196095418036620623872 }, { target := 176, numerator := 3231132728246677256766868160512 }, { target := 178, numerator := 119321432983031187576900770856960 }, { target := 181, numerator := 119321403764222605443163008008192 }, { target := 188, numerator := 3231161947055259390504631009280 }, { target := 227, numerator := 4085884488560304878491747221504 }, { target := 230, numerator := 14861242637411897131039331450880 }, { target := 232, numerator := 4085884488560304878491747221504 }, { target := 286, numerator := 3230888350842658273039193473024 }, { target := 288, numerator := 119312408450618357472831649873920 }, { target := 291, numerator := 119312379234019655647447570448384 }, { target := 298, numerator := 3230917567441360098423272898560 }, { target := 302, numerator := 40770982839123824361997823115264 }, { target := 305, numerator := 148292853171547254988044584878080 }, { target := 307, numerator := 40770982839123824361997823115264 }, { target := 573, numerator := 86241497657146014730555490304 }, { target := 575, numerator := 3184783773533606337946394296320 }, { target := 578, numerator := 3184782993660408975344076324864 }, { target := 585, numerator := 86242277530343377332873461760 }, { target := 589, numerator := 4085884488560304878491747221504 }, { target := 592, numerator := 14861242637411897131039331450880 }, { target := 594, numerator := 4085884488560304878491747221504 }, { target := 763, numerator := 25590291929984498888054145024 }, { target := 766, numerator := 93077407988033041936448225280 }, { target := 768, numerator := 25590291929984498888054145024 }]

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
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 22519276726801088993296384000 }, { target := 134, numerator := 77304739491398294493672243200 }, { target := 136, numerator := 22519276726801088993296384000 }, { target := 157, numerator := 76938076695391662266824785920 }, { target := 158, numerator := 1292559688482579926082656403456 }, { target := 159, numerator := 2800545991712256506512422207488 }, { target := 160, numerator := 92325692034469994720189743104 }, { target := 161, numerator := 1477211072551519915523035889664 }, { target := 162, numerator := 107713307373548327173554700288 }, { target := 163, numerator := 2800545991712256506512422207488 }, { target := 164, numerator := 2800545991712256506512422207488 }, { target := 165, numerator := 1477211072551519915523035889664 }, { target := 166, numerator := 34560584051569934690257693835264 }, { target := 167, numerator := 2769770761034099841605692293120 }, { target := 168, numerator := 1292559688482579926082656403456 }, { target := 169, numerator := 2800545991712256506512422207488 }, { target := 170, numerator := 107713307373548327173554700288 }, { target := 171, numerator := 2769770761034099841605692293120 }, { target := 172, numerator := 107713307373548327173554700288 }, { target := 173, numerator := 2800545991712256506512422207488 }, { target := 174, numerator := 2800545991712256506512422207488 }, { target := 175, numerator := 92325692034469994720189743104 }, { target := 227, numerator := 378323849010258295087379251200 }, { target := 230, numerator := 1298719623455491347493693685760 }, { target := 232, numerator := 378323849010258295087379251200 }, { target := 253, numerator := 819701672855559639355988377600 }, { target := 256, numerator := 2813892517486897919569669652480 }, { target := 258, numerator := 819701672855559639355988377600 }, { target := 267, numerator := 22412465928096894104790630400 }, { target := 268, numerator := 376529427592027820960482590720 }, { target := 269, numerator := 815813759782726945414378946560 }, { target := 270, numerator := 26894959113716272925748756480 }, { target := 271, numerator := 430319345819460366811980103680 }, { target := 272, numerator := 31377452299335651746706882560 }, { target := 273, numerator := 815813759782726945414378946560 }, { target := 274, numerator := 815813759782726945414378946560 }, { target := 275, numerator := 430319345819460366811980103680 }, { target := 276, numerator := 10067679694901124831871951175680 }, { target := 277, numerator := 806848773411488187772462694400 }, { target := 278, numerator := 376529427592027820960482590720 }, { target := 279, numerator := 815813759782726945414378946560 }, { target := 280, numerator := 31377452299335651746706882560 }, { target := 281, numerator := 806848773411488187772462694400 }, { target := 282, numerator := 31377452299335651746706882560 }, { target := 283, numerator := 815813759782726945414378946560 }, { target := 284, numerator := 815813759782726945414378946560 }, { target := 285, numerator := 26894959113716272925748756480 }, { target := 302, numerator := 27023132072161306791955660800 }, { target := 305, numerator := 92765687389677953392406691840 }, { target := 307, numerator := 27023132072161306791955660800 }, { target := 328, numerator := 432370113154580908671290572800 }, { target := 331, numerator := 1484250998234847254278507069440 }, { target := 333, numerator := 432370113154580908671290572800 }, { target := 342, numerator := 31526987417521524590614937600 }, { target := 345, numerator := 108226635287957612291141140480 }, { target := 347, numerator := 31526987417521524590614937600 }, { target := 443, numerator := 819701672855559639355988377600 }, { target := 446, numerator := 2813892517486897919569669652480 }, { target := 448, numerator := 819701672855559639355988377600 }, { target := 469, numerator := 819701672855559639355988377600 }, { target := 472, numerator := 2813892517486897919569669652480 }, { target := 474, numerator := 819701672855559639355988377600 }]

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
    Slot13.Left8.expected,
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot13.Left16.expected,
    Slot13.Left17.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 25585870482900898410104094720 }, { target := 27, numerator := 4084712404656529690632168407040 }, { target := 29, numerator := 40759287204344959237395987824640 }, { target := 37, numerator := 4084712404656529690632168407040 }, { target := 44, numerator := 25582951054502575623886602240 }, { target := 80, numerator := 86294969221258138478016724992 }, { target := 82, numerator := 3242323679131662599910582124544 }, { target := 85, numerator := 3242078455332352618443296473088 }, { target := 92, numerator := 86540193020568119945302376448 }, { target := 157, numerator := 93061326231903656904910438400 }, { target := 158, numerator := 14856979515599673408397036748800 }, { target := 160, numerator := 148250313626747614352649276620800 }, { target := 168, numerator := 14856979515599673408397036748800 }, { target := 175, numerator := 93050707641507501763775692800 }, { target := 176, numerator := 3186758407258159274989568655360 }, { target := 178, numerator := 119734699910869141941934117355520 }, { target := 181, numerator := 119725644122204252287756444631040 }, { target := 188, numerator := 3195814195923048929167241379840 }, { target := 267, numerator := 25585870482900898410104094720 }, { target := 268, numerator := 4084712404656529690632168407040 }, { target := 270, numerator := 40759287204344959237395987824640 }, { target := 278, numerator := 4084712404656529690632168407040 }, { target := 285, numerator := 25582951054502575623886602240 }, { target := 286, numerator := 3186757626901423931195362639872 }, { target := 288, numerator := 119734670590861915474609731272704 }, { target := 291, numerator := 119725614804414559996352458129408 }, { target := 298, numerator := 3195813413348779409452635783168 }, { target := 518, numerator := 432370113154580908671290572800 }, { target := 521, numerator := 1484250998234847254278507069440 }, { target := 523, numerator := 432370113154580908671290572800 }, { target := 544, numerator := 10115659105679049175788735692800 }, { target := 547, numerator := 34725288979536113886557571645440 }, { target := 549, numerator := 10115659105679049175788735692800 }, { target := 558, numerator := 810693962164839203758669824000 }, { target := 561, numerator := 2782970621690338601772200755200 }, { target := 563, numerator := 810693962164839203758669824000 }, { target := 573, numerator := 86295749577993482272222740480 }, { target := 575, numerator := 3242352999138889067234968207360 }, { target := 578, numerator := 3242107773122044909847282974720 }, { target := 585, numerator := 86540975594837639659907973120 }, { target := 589, numerator := 378323849010258295087379251200 }, { target := 592, numerator := 1298719623455491347493693685760 }, { target := 594, numerator := 378323849010258295087379251200 }, { target := 603, numerator := 819701672855559639355988377600 }, { target := 606, numerator := 2813892517486897919569669652480 }, { target := 608, numerator := 819701672855559639355988377600 }, { target := 658, numerator := 31526987417521524590614937600 }, { target := 661, numerator := 108226635287957612291141140480 }, { target := 663, numerator := 31526987417521524590614937600 }, { target := 684, numerator := 810693962164839203758669824000 }, { target := 687, numerator := 2782970621690338601772200755200 }, { target := 689, numerator := 810693962164839203758669824000 }, { target := 698, numerator := 31526987417521524590614937600 }, { target := 701, numerator := 108226635287957612291141140480 }, { target := 703, numerator := 31526987417521524590614937600 }, { target := 729, numerator := 819701672855559639355988377600 }, { target := 732, numerator := 2813892517486897919569669652480 }, { target := 734, numerator := 819701672855559639355988377600 }, { target := 743, numerator := 819701672855559639355988377600 }, { target := 746, numerator := 2813892517486897919569669652480 }, { target := 748, numerator := 819701672855559639355988377600 }, { target := 763, numerator := 27023132072161306791955660800 }, { target := 766, numerator := 92765687389677953392406691840 }, { target := 768, numerator := 27023132072161306791955660800 }]

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
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 93570880747203412264747008000 }, { target := 11, numerator := 72777351692269320650358784000 }, { target := 12, numerator := 83174116219736366457552896000 }, { target := 13, numerator := 97729586558190230587624652800 }, { target := 14, numerator := 1154040862548842084598546432000 }, { target := 15, numerator := 2595032426055774633475650355200 }, { target := 16, numerator := 72777351692269320650358784000 }, { target := 17, numerator := 1154040862548842084598546432000 }, { target := 18, numerator := 83174116219736366457552896000 }, { target := 19, numerator := 81094763314242957296114073600 }, { target := 20, numerator := 81094763314242957296114073600 }, { target := 21, numerator := 81094763314242957296114073600 }, { target := 22, numerator := 2595032426055774633475650355200 }, { target := 23, numerator := 81094763314242957296114073600 }, { target := 24, numerator := 93570880747203412264747008000 }, { target := 25, numerator := 97729586558190230587624652800 }, { target := 80, numerator := 9631845817150508482930147328 }, { target := 82, numerator := 349061280565788426169091096576 }, { target := 85, numerator := 349061408844446714745313034240 }, { target := 92, numerator := 9631717538492219906708209664 }, { target := 115, numerator := 11437816907866228823479549952 }, { target := 117, numerator := 414510270671873756075795677184 }, { target := 120, numerator := 414510423002780473760059228160 }, { target := 127, numerator := 11437664576959511139215998976 }, { target := 141, numerator := 93570836129141183979769036800 }, { target := 142, numerator := 72777316989332031984264806400 }, { target := 143, numerator := 83174076559236607982016921600 }, { target := 144, numerator := 97729539957103014378869882880 }, { target := 145, numerator := 1154040312259407935750484787200 }, { target := 146, numerator := 2595031188648182169038927953920 }, { target := 147, numerator := 72777316989332031984264806400 }, { target := 148, numerator := 1154040312259407935750484787200 }, { target := 149, numerator := 83174076559236607982016921600 }, { target := 150, numerator := 81094724645255692782466498560 }, { target := 151, numerator := 81094724645255692782466498560 }, { target := 152, numerator := 81094724645255692782466498560 }, { target := 153, numerator := 2595031188648182169038927953920 }, { target := 154, numerator := 81094724645255692782466498560 }, { target := 155, numerator := 93570836129141183979769036800 }, { target := 156, numerator := 97729539957103014378869882880 }, { target := 176, numerator := 8728860271792648312655446016 }, { target := 178, numerator := 316336785512745761215738806272 }, { target := 181, numerator := 316336901765279835237939937280 }, { target := 188, numerator := 8728744019258574290454315008 }, { target := 211, numerator := 89997559354000063637378564096 }, { target := 213, numerator := 3261541340286585607017444933632 }, { target := 216, numerator := 3261542538890298990901518663680 }, { target := 223, numerator := 89996360750286679753304834048 }, { target := 237, numerator := 10835826544294322043296415744 }, { target := 239, numerator := 392693940636511979440227483648 }, { target := 242, numerator := 392694084950002554088477163520 }, { target := 249, numerator := 10835682230803747395046735872 }, { target := 286, numerator := 8728860271792648312655446016 }, { target := 288, numerator := 316336785512745761215738806272 }, { target := 291, numerator := 316336901765279835237939937280 }, { target := 298, numerator := 8728744019258574290454315008 }, { target := 312, numerator := 10835826544294322043296415744 }, { target := 314, numerator := 392693940636511979440227483648 }, { target := 317, numerator := 392694084950002554088477163520 }, { target := 324, numerator := 10835682230803747395046735872 }, { target := 392, numerator := 10835826544294322043296415744 }, { target := 394, numerator := 392693940636511979440227483648 }, { target := 397, numerator := 392694084950002554088477163520 }, { target := 404, numerator := 10835682230803747395046735872 }]

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

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected,
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 28864671768971584268320899072 }, { target := 11, numerator := 2427208366173222881131541561344 }, { target := 16, numerator := 2427207780599779005295535063040 }, { target := 24, numerator := 28865257342415460104327397376 }, { target := 26, numerator := 7826485692089845617413586944 }, { target := 27, numerator := 1155930979198560728169268117504 }, { target := 29, numerator := 12048075280104929565148457205760 }, { target := 37, numerator := 1155930979198560728169268117504 }, { target := 44, numerator := 7826485692089845617413586944 }, { target := 141, numerator := 28864671768971584268320899072 }, { target := 142, numerator := 2427208366173222881131541561344 }, { target := 147, numerator := 2427207780599779005295535063040 }, { target := 155, numerator := 28865257342415460104327397376 }, { target := 157, numerator := 27998735817650370742088368128 }, { target := 158, numerator := 4135266757432266996648769486848 }, { target := 160, numerator := 43101193837198094148522077061120 }, { target := 168, numerator := 4135266757432266996648769486848 }, { target := 175, numerator := 27998735817650370742088368128 }, { target := 267, numerator := 7826483090245499094980100096 }, { target := 268, numerator := 1155930594919766704739252699136 }, { target := 270, numerator := 12048071274831325640972398755840 }, { target := 278, numerator := 1155930594919766704739252699136 }, { target := 285, numerator := 7826483090245499094980100096 }, { target := 427, numerator := 464134570313940127521196474368 }, { target := 429, numerator := 16820390457263929786023077216256 }, { target := 432, numerator := 16820396638691776066789771837440 }, { target := 439, numerator := 464128388886093846754501853184 }, { target := 453, numerator := 10835826544294322043296415744 }, { target := 455, numerator := 392693940636511979440227483648 }, { target := 458, numerator := 392694084950002554088477163520 }, { target := 465, numerator := 10835682230803747395046735872 }, { target := 502, numerator := 89997559354000063637378564096 }, { target := 504, numerator := 3261541340286585607017444933632 }, { target := 507, numerator := 3261542538890298990901518663680 }, { target := 514, numerator := 89996360750286679753304834048 }, { target := 528, numerator := 464134570313940127521196474368 }, { target := 530, numerator := 16820390457263929786023077216256 }, { target := 533, numerator := 16820396638691776066789771837440 }, { target := 540, numerator := 464128388886093846754501853184 }, { target := 573, numerator := 9631845817150508482930147328 }, { target := 575, numerator := 349061280565788426169091096576 }, { target := 578, numerator := 349061408844446714745313034240 }, { target := 585, numerator := 9631717538492219906708209664 }, { target := 642, numerator := 10835826544294322043296415744 }, { target := 644, numerator := 392693940636511979440227483648 }, { target := 647, numerator := 392694084950002554088477163520 }, { target := 654, numerator := 10835682230803747395046735872 }, { target := 668, numerator := 10835826544294322043296415744 }, { target := 670, numerator := 392693940636511979440227483648 }, { target := 673, numerator := 392694084950002554088477163520 }, { target := 680, numerator := 10835682230803747395046735872 }, { target := 713, numerator := 11437816907866228823479549952 }, { target := 715, numerator := 414510270671873756075795677184 }, { target := 718, numerator := 414510423002780473760059228160 }, { target := 725, numerator := 11437664576959511139215998976 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left0.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left2.expected,
    Slot21.Left3.expected,
    Slot21.Left4.expected,
    Slot21.Left5.expected,
    Slot21.Left6.expected,
    Slot21.Left7.expected,
    Slot21.Left8.expected,
    Slot21.Left9.expected,
    Slot22.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1798881619586568211962789888 }, { target := 1, numerator := 43057101991394632686335164416 }, { target := 2, numerator := 32205783834533721214172528640 }, { target := 3, numerator := 37370314935927417048517312512 }, { target := 4, numerator := 1798881619586568211962789888 }, { target := 5, numerator := 37312286496585914848131416064 }, { target := 6, numerator := 37486371814610421449289105408 }, { target := 7, numerator := 1798881619586568211962789888 }, { target := 8, numerator := 43057101991394632686335164416 }, { target := 9, numerator := 1798881619586568211962789888 }, { target := 10, numerator := 2103920521364291509718876160 }, { target := 11, numerator := 176159445135730468075755012096 }, { target := 16, numerator := 176159508887677986815965396992 }, { target := 24, numerator := 2103856769416772769508491264 }, { target := 26, numerator := 13405929142052449199063040 }, { target := 27, numerator := 1405587492050865436030402560 }, { target := 29, numerator := 15150828281262847064801280000 }, { target := 37, numerator := 1405588564267864720398090240 }, { target := 44, numerator := 13405929142052449199063040 }, { target := 61, numerator := 238625538728533595743322112 }, { target := 62, numerator := 25019457358505404761341165568 }, { target := 64, numerator := 269684743406478677753462784000 }, { target := 72, numerator := 25019476443967992023086006272 }, { target := 79, numerator := 238625538728533595743322112 }, { target := 96, numerator := 13405929142052449199063040 }, { target := 97, numerator := 1405587492050865436030402560 }, { target := 99, numerator := 15150828281262847064801280000 }, { target := 107, numerator := 1405588564267864720398090240 }, { target := 114, numerator := 13405929142052449199063040 }, { target := 157, numerator := 212260544749163778985164800 }, { target := 158, numerator := 22255135290805369403814707200 }, { target := 160, numerator := 239888114453328411859353600000 }, { target := 168, numerator := 22255152267574524739636428800 }, { target := 175, numerator := 212260544749163778985164800 }, { target := 192, numerator := 362406951140151210014670848 }, { target := 193, numerator := 37997715201775062287355215872 }, { target := 195, numerator := 409577391203472298985127936000 }, { target := 203, numerator := 37997744187374609608095039488 }, { target := 210, numerator := 362406951140151210014670848 }, { target := 267, numerator := 13405929142052449199063040 }, { target := 268, numerator := 1405587492050865436030402560 }, { target := 270, numerator := 15150828281262847064801280000 }, { target := 278, numerator := 1405588564267864720398090240 }, { target := 285, numerator := 13405929142052449199063040 }, { target := 373, numerator := 362406951140151210014670848 }, { target := 374, numerator := 37997715201775062287355215872 }, { target := 376, numerator := 409577391203472298985127936000 }, { target := 384, numerator := 37997744187374609608095039488 }, { target := 391, numerator := 362406951140151210014670848 }, { target := 408, numerator := 362406951140151210014670848 }, { target := 409, numerator := 37997715201775062287355215872 }, { target := 411, numerator := 409577391203472298985127936000 }, { target := 419, numerator := 37997744187374609608095039488 }, { target := 426, numerator := 362406951140151210014670848 }, { target := 483, numerator := 238625538728533595743322112 }, { target := 484, numerator := 25019457358505404761341165568 }, { target := 486, numerator := 269684743406478677753462784000 }, { target := 494, numerator := 25019476443967992023086006272 }, { target := 501, numerator := 238625538728533595743322112 }, { target := 623, numerator := 13405929142052449199063040 }, { target := 624, numerator := 1405587492050865436030402560 }, { target := 626, numerator := 15150828281262847064801280000 }, { target := 634, numerator := 1405588564267864720398090240 }, { target := 641, numerator := 13405929142052449199063040 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot22.Left2.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 6779707942430151977849585664 }, { target := 2, numerator := 65668746629404033637844779008 }, { target := 7, numerator := 6779707942430151977849585664 }, { target := 141, numerator := 2103920521364291509718876160 }, { target := 142, numerator := 176159445135730468075755012096 }, { target := 147, numerator := 176159508887677986815965396992 }, { target := 155, numerator := 2103856769416772769508491264 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent1
