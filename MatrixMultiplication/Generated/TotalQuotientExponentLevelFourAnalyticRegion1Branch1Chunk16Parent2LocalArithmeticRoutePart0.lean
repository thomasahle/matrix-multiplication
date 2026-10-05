import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 68; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2

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
    Slot3.Left2.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 44255680552642972257091584 }, { target := 251, numerator := 50402302851621162848354304 }, { target := 252, numerator := 39338382713460419784081408 }, { target := 253, numerator := 527380193252328752730341376 }, { target := 254, numerator := 46714329472234248493596672 }, { target := 255, numerator := 39338382713460419784081408 }, { target := 256, numerator := 46714329472234248493596672 }, { target := 257, numerator := 45485005012438610375344128 }, { target := 258, numerator := 1718595594794302089317056512 }, { target := 259, numerator := 45485005012438610375344128 }, { target := 260, numerator := 527380193252328752730341376 }, { target := 261, numerator := 1718595594794302089317056512 }, { target := 262, numerator := 44255680552642972257091584 }, { target := 263, numerator := 45485005012438610375344128 }, { target := 264, numerator := 45485005012438610375344128 }, { target := 265, numerator := 50402302851621162848354304 }, { target := 562, numerator := 2000276249242615436997033984 }, { target := 563, numerator := 2278092394970756469913288704 }, { target := 564, numerator := 1778023332660102610664030208 }, { target := 565, numerator := 23836625303474500624214654976 }, { target := 566, numerator := 2111402707533871850163535872 }, { target := 567, numerator := 1778023332660102610664030208 }, { target := 568, numerator := 2111402707533871850163535872 }, { target := 569, numerator := 2055839478388243643580284928 }, { target := 570, numerator := 77677394345588232803384819712 }, { target := 571, numerator := 2055839478388243643580284928 }, { target := 572, numerator := 23836625303474500624214654976 }, { target := 573, numerator := 77677394345588232803384819712 }, { target := 574, numerator := 2000276249242615436997033984 }, { target := 575, numerator := 2055839478388243643580284928 }, { target := 576, numerator := 2055839478388243643580284928 }, { target := 577, numerator := 2278092394970756469913288704 }, { target := 613, numerator := 3504109267084865620047560704 }, { target := 616, numerator := 12798823274987973875702169600 }, { target := 618, numerator := 3504108086493244902636257280 }, { target := 880, numerator := 3504109267084865620047560704 }, { target := 883, numerator := 12798823274987973875702169600 }, { target := 885, numerator := 3504108086493244902636257280 }, { target := 925, numerator := 44491886498820804638146560 }, { target := 926, numerator := 50671315179212583060111360 }, { target := 927, numerator := 39548343554507381900574720 }, { target := 928, numerator := 530194980777614588604579840 }, { target := 929, numerator := 46963657970977516006932480 }, { target := 930, numerator := 39548343554507381900574720 }, { target := 931, numerator := 46963657970977516006932480 }, { target := 932, numerator := 45727772234899160322539520 }, { target := 933, numerator := 1727768259037541246781358080 }, { target := 934, numerator := 45727772234899160322539520 }, { target := 935, numerator := 530194980777614588604579840 }, { target := 936, numerator := 1727768259037541246781358080 }, { target := 937, numerator := 44491886498820804638146560 }, { target := 938, numerator := 45727772234899160322539520 }, { target := 939, numerator := 45727772234899160322539520 }, { target := 940, numerator := 50671315179212583060111360 }, { target := 976, numerator := 3504109267084865620047560704 }, { target := 979, numerator := 12798823274987973875702169600 }, { target := 981, numerator := 3504108086493244902636257280 }, { target := 1002, numerator := 3504109267084865620047560704 }, { target := 1005, numerator := 12798823274987973875702169600 }, { target := 1007, numerator := 3504108086493244902636257280 }]

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
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 42438023707810973947527168 }, { target := 122, numerator := 636570355617164609212907520 }, { target := 123, numerator := 1117534624305688980618215424 }, { target := 124, numerator := 42438023707810973947527168 }, { target := 125, numerator := 707300395130182899125452800 }, { target := 126, numerator := 42438023707810973947527168 }, { target := 127, numerator := 1117534624305688980618215424 }, { target := 128, numerator := 1110461620354387151626960896 }, { target := 129, numerator := 707300395130182899125452800 }, { target := 130, numerator := 17137888574004331645809721344 }, { target := 131, numerator := 1096315612451783493644451840 }, { target := 132, numerator := 636570355617164609212907520 }, { target := 133, numerator := 1117534624305688980618215424 }, { target := 134, numerator := 42438023707810973947527168 }, { target := 135, numerator := 1096315612451783493644451840 }, { target := 136, numerator := 42438023707810973947527168 }, { target := 137, numerator := 1117534624305688980618215424 }, { target := 138, numerator := 1117534624305688980618215424 }, { target := 139, numerator := 42438023707810973947527168 }, { target := 196, numerator := 7443230651345972875833114624 }, { target := 197, numerator := 111648459770189593137496719360 }, { target := 198, numerator := 196005073818777285730272018432 }, { target := 199, numerator := 7443230651345972875833114624 }, { target := 200, numerator := 124053844189099547930551910400 }, { target := 201, numerator := 7443230651345972875833114624 }, { target := 202, numerator := 196005073818777285730272018432 }, { target := 203, numerator := 194764535376886290250966499328 }, { target := 204, numerator := 124053844189099547930551910400 }, { target := 205, numerator := 3005824644701882046357272788992 }, { target := 206, numerator := 192283458493104299292355461120 }, { target := 207, numerator := 111648459770189593137496719360 }, { target := 208, numerator := 196005073818777285730272018432 }, { target := 209, numerator := 7443230651345972875833114624 }, { target := 210, numerator := 192283458493104299292355461120 }, { target := 211, numerator := 7443230651345972875833114624 }, { target := 212, numerator := 196005073818777285730272018432 }, { target := 213, numerator := 196005073818777285730272018432 }, { target := 214, numerator := 7443230651345972875833114624 }, { target := 508, numerator := 7443231543707217441532674048 }, { target := 509, numerator := 111648473155608261622990110720 }, { target := 510, numerator := 196005097317623392627027083264 }, { target := 511, numerator := 7443231543707217441532674048 }, { target := 512, numerator := 124053859061786957358877900800 }, { target := 513, numerator := 7443231543707217441532674048 }, { target := 514, numerator := 196005097317623392627027083264 }, { target := 515, numerator := 194764558727005523053438304256 }, { target := 516, numerator := 124053859061786957358877900800 }, { target := 517, numerator := 3005825005067097976805611536384 }, { target := 518, numerator := 192283481545769783906260746240 }, { target := 519, numerator := 111648473155608261622990110720 }, { target := 520, numerator := 196005097317623392627027083264 }, { target := 521, numerator := 7443231543707217441532674048 }, { target := 522, numerator := 192283481545769783906260746240 }, { target := 523, numerator := 7443231543707217441532674048 }, { target := 524, numerator := 196005097317623392627027083264 }, { target := 525, numerator := 196005097317623392627027083264 }, { target := 526, numerator := 7443231543707217441532674048 }]

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
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 217335633731309833749004288 }, { target := 252, numerator := 8477259897413535832293244928 }, { target := 255, numerator := 8477256787984237907626950656 }, { target := 262, numerator := 217336670207742475304435712 }, { target := 466, numerator := 5265130997813344682112974848 }, { target := 468, numerator := 205368457514760174517813772288 }, { target := 471, numerator := 205368382186327828020252901376 }, { target := 478, numerator := 5265156107290793514633265152 }, { target := 562, numerator := 3989160503003719206554304512 }, { target := 564, numerator := 155598738117041996405640527872 }, { target := 567, numerator := 155598681043968753852894674944 }, { target := 574, numerator := 3989179527361466724136255488 }, { target := 597, numerator := 4444864251150014019253829632 }, { target := 599, numerator := 173373637901941345731416686592 }, { target := 602, numerator := 173373574309096994626951184384 }, { target := 609, numerator := 4444885448764797720742330368 }, { target := 733, numerator := 217335633731309833749004288 }, { target := 735, numerator := 8477259897413535832293244928 }, { target := 738, numerator := 8477256787984237907626950656 }, { target := 745, numerator := 217336670207742475304435712 }, { target := 829, numerator := 4444864251150014019253829632 }, { target := 831, numerator := 173373637901941345731416686592 }, { target := 834, numerator := 173373574309096994626951184384 }, { target := 841, numerator := 4444885448764797720742330368 }, { target := 864, numerator := 4437853424255455637519990784 }, { target := 866, numerator := 173100177905250586511020130304 }, { target := 869, numerator := 173100114412710406307350315008 }, { target := 876, numerator := 4437874588435515705409929216 }, { target := 906, numerator := 42437131346566408247967744 }, { target := 907, numerator := 636556970198496123719516160 }, { target := 908, numerator := 1117511125459582083863150592 }, { target := 909, numerator := 42437131346566408247967744 }, { target := 910, numerator := 707285522442773470799462400 }, { target := 911, numerator := 42437131346566408247967744 }, { target := 912, numerator := 1117511125459582083863150592 }, { target := 913, numerator := 1110438270235154349155155968 }, { target := 914, numerator := 707285522442773470799462400 }, { target := 915, numerator := 17137528208788401197470973952 }, { target := 916, numerator := 1096292559786298879739166720 }, { target := 917, numerator := 636556970198496123719516160 }, { target := 918, numerator := 1117511125459582083863150592 }, { target := 919, numerator := 42437131346566408247967744 }, { target := 920, numerator := 1096292559786298879739166720 }, { target := 921, numerator := 42437131346566408247967744 }, { target := 922, numerator := 1117511125459582083863150592 }, { target := 923, numerator := 1117511125459582083863150592 }, { target := 924, numerator := 42437131346566408247967744 }, { target := 925, numerator := 217335633731309833749004288 }, { target := 927, numerator := 8477259897413535832293244928 }, { target := 930, numerator := 8477256787984237907626950656 }, { target := 937, numerator := 217336670207742475304435712 }, { target := 960, numerator := 5265130997813344682112974848 }, { target := 962, numerator := 205368457514760174517813772288 }, { target := 965, numerator := 205368382186327828020252901376 }, { target := 972, numerator := 5265156107290793514633265152 }, { target := 986, numerator := 217335633731309833749004288 }, { target := 988, numerator := 8477259897413535832293244928 }, { target := 991, numerator := 8477256787984237907626950656 }, { target := 998, numerator := 217336670207742475304435712 }]

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 148823608820205792792674304 }, { target := 35, numerator := 111617706615154344594505728 }, { target := 36, numerator := 117818690315996252627533824 }, { target := 37, numerator := 151924100670626746809188352 }, { target := 38, numerator := 2033922653876145834833215488 }, { target := 39, numerator := 3556264152432834256941613056 }, { target := 40, numerator := 108517214764733390577991680 }, { target := 41, numerator := 2033922653876145834833215488 }, { target := 42, numerator := 114718198465575298611019776 }, { target := 43, numerator := 117818690315996252627533824 }, { target := 44, numerator := 117818690315996252627533824 }, { target := 45, numerator := 114718198465575298611019776 }, { target := 46, numerator := 3556264152432834256941613056 }, { target := 47, numerator := 114718198465575298611019776 }, { target := 48, numerator := 148823608820205792792674304 }, { target := 49, numerator := 151924100670626746809188352 }, { target := 79, numerator := 17589995080234887589190959104 }, { target := 80, numerator := 13192496310176165691893219328 }, { target := 81, numerator := 13925412771852619341442842624 }, { target := 82, numerator := 17956453311073114413965770752 }, { target := 83, numerator := 240396599429876797052276441088 }, { target := 84, numerator := 420327590771446168016708960256 }, { target := 85, numerator := 12826038079337938867118407680 }, { target := 86, numerator := 240396599429876797052276441088 }, { target := 87, numerator := 13558954541014392516668030976 }, { target := 88, numerator := 13925412771852619341442842624 }, { target := 89, numerator := 13925412771852619341442842624 }, { target := 90, numerator := 13558954541014392516668030976 }, { target := 91, numerator := 420327590771446168016708960256 }, { target := 92, numerator := 13558954541014392516668030976 }, { target := 93, numerator := 17589995080234887589190959104 }, { target := 94, numerator := 17956453311073114413965770752 }, { target := 154, numerator := 166925546980878863975992786944 }, { target := 155, numerator := 125194160235659147981994590208 }, { target := 156, numerator := 132149391359862433980994289664 }, { target := 157, numerator := 170403162542980506975492636672 }, { target := 158, numerator := 2281315808738677807671901421568 }, { target := 159, numerator := 3988825049730584520426327638016 }, { target := 160, numerator := 121716544673557504982494740480 }, { target := 161, numerator := 2281315808738677807671901421568 }, { target := 162, numerator := 128671775797760790981494439936 }, { target := 163, numerator := 132149391359862433980994289664 }, { target := 164, numerator := 132149391359862433980994289664 }, { target := 165, numerator := 128671775797760790981494439936 }, { target := 166, numerator := 3988825049730584520426327638016 }, { target := 167, numerator := 128671775797760790981494439936 }, { target := 168, numerator := 166925546980878863975992786944 }, { target := 169, numerator := 170403162542980506975492636672 }, { target := 492, numerator := 17590007144405511795237715968 }, { target := 493, numerator := 13192505358304133846428286976 }, { target := 494, numerator := 13925422322654363504563191808 }, { target := 495, numerator := 17956465626580626624305168384 }, { target := 496, numerator := 240396764306875327868248784896 }, { target := 497, numerator := 420327879054856708940367921152 }, { target := 498, numerator := 12826046876129019017360834560 }, { target := 499, numerator := 240396764306875327868248784896 }, { target := 500, numerator := 13558963840479248675495739392 }, { target := 501, numerator := 13925422322654363504563191808 }, { target := 502, numerator := 13925422322654363504563191808 }, { target := 503, numerator := 13558963840479248675495739392 }, { target := 504, numerator := 420327879054856708940367921152 }, { target := 505, numerator := 13558963840479248675495739392 }, { target := 506, numerator := 17590007144405511795237715968 }, { target := 507, numerator := 17956465626580626624305168384 }]

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
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 146092900401486420447854592 }, { target := 122, numerator := 17267242876927825431591124992 }, { target := 124, numerator := 163862692907835215095699341312 }, { target := 132, numerator := 17267254719737520753123262464 }, { target := 139, numerator := 146092900401486420447854592 }, { target := 196, numerator := 109569675301114815335890944 }, { target := 197, numerator := 12950432157695869073693343744 }, { target := 199, numerator := 122897019680876411321774505984 }, { target := 207, numerator := 12950441039803140564842446848 }, { target := 214, numerator := 109569675301114815335890944 }, { target := 231, numerator := 115656879484510082854551552 }, { target := 232, numerator := 13669900610901195133342973952 }, { target := 234, numerator := 129724631885369545284095311872 }, { target := 242, numerator := 13669909986458870596222582784 }, { target := 249, numerator := 115656879484510082854551552 }, { target := 337, numerator := 149136502493184054207184896 }, { target := 338, numerator := 17626977103530488461415940096 }, { target := 340, numerator := 167276499010081782076859744256 }, { target := 348, numerator := 17626989193065385768813330432 }, { target := 355, numerator := 149136502493184054207184896 }, { target := 412, numerator := 1996602972153647746120679424 }, { target := 413, numerator := 235985652651346947565078708224 }, { target := 415, numerator := 2239456803073747939641224331264 }, { target := 423, numerator := 235985814503079450292684587008 }, { target := 430, numerator := 1996602972153647746120679424 }, { target := 447, numerator := 3491011599177185921951858688 }, { target := 448, numerator := 412615157913254495209062924288 }, { target := 450, numerator := 3915635599276812327390982176768 }, { target := 458, numerator := 412615440907061172996507959296 }, { target := 465, numerator := 3491011599177185921951858688 }, { target := 508, numerator := 106526073209417181576560640 }, { target := 509, numerator := 12590697931093206043868528640 }, { target := 511, numerator := 119483213578629844340614103040 }, { target := 519, numerator := 12590706566475275549152378880 }, { target := 526, numerator := 106526073209417181576560640 }, { target := 543, numerator := 1996602972153647746120679424 }, { target := 544, numerator := 235985652651346947565078708224 }, { target := 546, numerator := 2239456803073747939641224331264 }, { target := 554, numerator := 235985814503079450292684587008 }, { target := 561, numerator := 1996602972153647746120679424 }, { target := 578, numerator := 112613277392812449095221248 }, { target := 579, numerator := 13310166384298532103518158848 }, { target := 581, numerator := 126310825783122978302934908928 }, { target := 589, numerator := 13310175513131005580532514816 }, { target := 596, numerator := 112613277392812449095221248 }, { target := 890, numerator := 148823608820205792792674304 }, { target := 891, numerator := 111617706615154344594505728 }, { target := 892, numerator := 117818690315996252627533824 }, { target := 893, numerator := 151924100670626746809188352 }, { target := 894, numerator := 2033922653876145834833215488 }, { target := 895, numerator := 3556264152432834256941613056 }, { target := 896, numerator := 108517214764733390577991680 }, { target := 897, numerator := 2033922653876145834833215488 }, { target := 898, numerator := 114718198465575298611019776 }, { target := 899, numerator := 117818690315996252627533824 }, { target := 900, numerator := 117818690315996252627533824 }, { target := 901, numerator := 114718198465575298611019776 }, { target := 902, numerator := 3556264152432834256941613056 }, { target := 903, numerator := 114718198465575298611019776 }, { target := 904, numerator := 148823608820205792792674304 }, { target := 905, numerator := 151924100670626746809188352 }]

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
    Slot7.Left9.expected,
    Slot7.Left10.expected,
    Slot7.Left11.expected,
    Slot7.Left12.expected,
    Slot7.Left13.expected,
    Slot7.Left14.expected,
    Slot7.Left15.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 224829965928941207326556160 }, { target := 11, numerator := 5446687239117253119427215360 }, { target := 12, numerator := 4126717761727985386090659840 }, { target := 13, numerator := 4598135432224152433710858240 }, { target := 14, numerator := 224829965928941207326556160 }, { target := 15, numerator := 4598135432224152433710858240 }, { target := 16, numerator := 4590882852678057556055162880 }, { target := 17, numerator := 224829965928941207326556160 }, { target := 18, numerator := 5446687239117253119427215360 }, { target := 19, numerator := 224829965928941207326556160 }, { target := 55, numerator := 8769579204220899136855080960 }, { target := 56, numerator := 212450128463545008121876316160 }, { target := 57, numerator := 160964211845215858350662615040 }, { target := 58, numerator := 179352039208904840411810365440 }, { target := 59, numerator := 8769579204220899136855080960 }, { target := 60, numerator := 179352039208904840411810365440 }, { target := 61, numerator := 179069149557155779149331169280 }, { target := 62, numerator := 8769579204220899136855080960 }, { target := 63, numerator := 212450128463545008121876316160 }, { target := 64, numerator := 8769579204220899136855080960 }, { target := 679, numerator := 115656879484510082854551552 }, { target := 680, numerator := 13669900610901195133342973952 }, { target := 682, numerator := 129724631885369545284095311872 }, { target := 690, numerator := 13669909986458870596222582784 }, { target := 697, numerator := 115656879484510082854551552 }, { target := 714, numerator := 115656879484510082854551552 }, { target := 715, numerator := 13669900610901195133342973952 }, { target := 717, numerator := 129724631885369545284095311872 }, { target := 725, numerator := 13669909986458870596222582784 }, { target := 732, numerator := 115656879484510082854551552 }, { target := 775, numerator := 112613277392812449095221248 }, { target := 776, numerator := 13310166384298532103518158848 }, { target := 778, numerator := 126310825783122978302934908928 }, { target := 786, numerator := 13310175513131005580532514816 }, { target := 793, numerator := 112613277392812449095221248 }, { target := 810, numerator := 3491011599177185921951858688 }, { target := 811, numerator := 412615157913254495209062924288 }, { target := 813, numerator := 3915635599276812327390982176768 }, { target := 821, numerator := 412615440907061172996507959296 }, { target := 828, numerator := 3491011599177185921951858688 }, { target := 845, numerator := 112613277392812449095221248 }, { target := 846, numerator := 13310166384298532103518158848 }, { target := 848, numerator := 126310825783122978302934908928 }, { target := 856, numerator := 13310175513131005580532514816 }, { target := 863, numerator := 112613277392812449095221248 }, { target := 906, numerator := 146092900401486420447854592 }, { target := 907, numerator := 17267242876927825431591124992 }, { target := 909, numerator := 163862692907835215095699341312 }, { target := 917, numerator := 17267254719737520753123262464 }, { target := 924, numerator := 146092900401486420447854592 }, { target := 941, numerator := 149136502493184054207184896 }, { target := 942, numerator := 17626977103530488461415940096 }, { target := 944, numerator := 167276499010081782076859744256 }, { target := 952, numerator := 17626989193065385768813330432 }, { target := 959, numerator := 149136502493184054207184896 }]

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
    Slot9.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 42438023707810973947527168 }, { target := 35, numerator := 7443230651345972875833114624 }, { target := 40, numerator := 7443231543707217441532674048 }, { target := 48, numerator := 42437131346566408247967744 }, { target := 79, numerator := 636570355617164609212907520 }, { target := 80, numerator := 111648459770189593137496719360 }, { target := 85, numerator := 111648473155608261622990110720 }, { target := 93, numerator := 636556970198496123719516160 }, { target := 105, numerator := 1117534624305688980618215424 }, { target := 106, numerator := 196005073818777285730272018432 }, { target := 111, numerator := 196005097317623392627027083264 }, { target := 119, numerator := 1117511125459582083863150592 }, { target := 144, numerator := 8769575987569901283752017920 }, { target := 145, numerator := 212450050537580511745089208320 }, { target := 146, numerator := 160964152804105607434028974080 }, { target := 147, numerator := 179351973423203787545121914880 }, { target := 148, numerator := 8769575987569901283752017920 }, { target := 149, numerator := 179351973423203787545121914880 }, { target := 150, numerator := 179069083875217661697258946560 }, { target := 151, numerator := 8769575987569901283752017920 }, { target := 152, numerator := 212450050537580511745089208320 }, { target := 153, numerator := 8769575987569901283752017920 }, { target := 154, numerator := 42438023707810973947527168 }, { target := 155, numerator := 7443230651345972875833114624 }, { target := 160, numerator := 7443231543707217441532674048 }, { target := 168, numerator := 42437131346566408247967744 }, { target := 180, numerator := 707300395130182899125452800 }, { target := 181, numerator := 124053844189099547930551910400 }, { target := 186, numerator := 124053859061786957358877900800 }, { target := 194, numerator := 707285522442773470799462400 }, { target := 215, numerator := 42438023707810973947527168 }, { target := 216, numerator := 7443230651345972875833114624 }, { target := 221, numerator := 7443231543707217441532674048 }, { target := 229, numerator := 42437131346566408247967744 }, { target := 295, numerator := 1117534624305688980618215424 }, { target := 296, numerator := 196005073818777285730272018432 }, { target := 301, numerator := 196005097317623392627027083264 }, { target := 309, numerator := 1117511125459582083863150592 }, { target := 321, numerator := 1110461620354387151626960896 }, { target := 322, numerator := 194764535376886290250966499328 }, { target := 327, numerator := 194764558727005523053438304256 }, { target := 335, numerator := 1110438270235154349155155968 }, { target := 370, numerator := 707300395130182899125452800 }, { target := 371, numerator := 124053844189099547930551910400 }, { target := 376, numerator := 124053859061786957358877900800 }, { target := 384, numerator := 707285522442773470799462400 }, { target := 396, numerator := 17137888574004331645809721344 }, { target := 397, numerator := 3005824644701882046357272788992 }, { target := 402, numerator := 3005825005067097976805611536384 }, { target := 410, numerator := 17137528208788401197470973952 }, { target := 431, numerator := 1096315612451783493644451840 }, { target := 432, numerator := 192283458493104299292355461120 }, { target := 437, numerator := 192283481545769783906260746240 }, { target := 445, numerator := 1096292559786298879739166720 }, { target := 482, numerator := 224831038145940491694243840 }, { target := 483, numerator := 5446713214438751911689584640 }, { target := 484, numerator := 4126737442098069024968540160 }, { target := 485, numerator := 4598157360791170055940341760 }, { target := 486, numerator := 224831038145940491694243840 }, { target := 487, numerator := 4598157360791170055940341760 }, { target := 488, numerator := 4590904746657430040079237120 }, { target := 489, numerator := 224831038145940491694243840 }, { target := 490, numerator := 5446713214438751911689584640 }, { target := 491, numerator := 224831038145940491694243840 }]

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
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot9.Left16.expected,
    Slot9.Left17.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 3504109267084865620047560704 }, { target := 2, numerator := 3504109267084865620047560704 }, { target := 3, numerator := 3504109267084865620047560704 }, { target := 4, numerator := 3504109267084865620047560704 }, { target := 10, numerator := 44255680552642972257091584 }, { target := 12, numerator := 2000276249242615436997033984 }, { target := 17, numerator := 44491886498820804638146560 }, { target := 24, numerator := 50402302851621162848354304 }, { target := 26, numerator := 2278092394970756469913288704 }, { target := 31, numerator := 50671315179212583060111360 }, { target := 51, numerator := 12798823274987973875702169600 }, { target := 52, numerator := 12798823274987973875702169600 }, { target := 53, numerator := 12798823274987973875702169600 }, { target := 54, numerator := 12798823274987973875702169600 }, { target := 55, numerator := 39338382713460419784081408 }, { target := 57, numerator := 1778023332660102610664030208 }, { target := 62, numerator := 39548343554507381900574720 }, { target := 69, numerator := 527380193252328752730341376 }, { target := 71, numerator := 23836625303474500624214654976 }, { target := 76, numerator := 530194980777614588604579840 }, { target := 95, numerator := 46714329472234248493596672 }, { target := 97, numerator := 2111402707533871850163535872 }, { target := 102, numerator := 46963657970977516006932480 }, { target := 140, numerator := 3504108086493244902636257280 }, { target := 141, numerator := 3504108086493244902636257280 }, { target := 142, numerator := 3504108086493244902636257280 }, { target := 143, numerator := 3504108086493244902636257280 }, { target := 144, numerator := 39338382713460419784081408 }, { target := 146, numerator := 1778023332660102610664030208 }, { target := 151, numerator := 39548343554507381900574720 }, { target := 492, numerator := 636570355617164609212907520 }, { target := 493, numerator := 111648459770189593137496719360 }, { target := 498, numerator := 111648473155608261622990110720 }, { target := 506, numerator := 636556970198496123719516160 }, { target := 527, numerator := 1117534624305688980618215424 }, { target := 528, numerator := 196005073818777285730272018432 }, { target := 533, numerator := 196005097317623392627027083264 }, { target := 541, numerator := 1117511125459582083863150592 }, { target := 637, numerator := 42438023707810973947527168 }, { target := 638, numerator := 7443230651345972875833114624 }, { target := 643, numerator := 7443231543707217441532674048 }, { target := 651, numerator := 42437131346566408247967744 }, { target := 663, numerator := 1096315612451783493644451840 }, { target := 664, numerator := 192283458493104299292355461120 }, { target := 669, numerator := 192283481545769783906260746240 }, { target := 677, numerator := 1096292559786298879739166720 }, { target := 698, numerator := 42438023707810973947527168 }, { target := 699, numerator := 7443230651345972875833114624 }, { target := 704, numerator := 7443231543707217441532674048 }, { target := 712, numerator := 42437131346566408247967744 }, { target := 759, numerator := 1117534624305688980618215424 }, { target := 760, numerator := 196005073818777285730272018432 }, { target := 765, numerator := 196005097317623392627027083264 }, { target := 773, numerator := 1117511125459582083863150592 }, { target := 794, numerator := 1117534624305688980618215424 }, { target := 795, numerator := 196005073818777285730272018432 }, { target := 800, numerator := 196005097317623392627027083264 }, { target := 808, numerator := 1117511125459582083863150592 }, { target := 890, numerator := 42438023707810973947527168 }, { target := 891, numerator := 7443230651345972875833114624 }, { target := 896, numerator := 7443231543707217441532674048 }, { target := 904, numerator := 42437131346566408247967744 }]

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
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 170, numerator := 46714329472234248493596672 }, { target := 172, numerator := 2111402707533871850163535872 }, { target := 177, numerator := 46963657970977516006932480 }, { target := 271, numerator := 45485005012438610375344128 }, { target := 273, numerator := 2055839478388243643580284928 }, { target := 278, numerator := 45727772234899160322539520 }, { target := 285, numerator := 1718595594794302089317056512 }, { target := 287, numerator := 77677394345588232803384819712 }, { target := 292, numerator := 1727768259037541246781358080 }, { target := 311, numerator := 45485005012438610375344128 }, { target := 313, numerator := 2055839478388243643580284928 }, { target := 318, numerator := 45727772234899160322539520 }, { target := 360, numerator := 527380193252328752730341376 }, { target := 362, numerator := 23836625303474500624214654976 }, { target := 367, numerator := 530194980777614588604579840 }, { target := 386, numerator := 1718595594794302089317056512 }, { target := 388, numerator := 77677394345588232803384819712 }, { target := 393, numerator := 1727768259037541246781358080 }, { target := 482, numerator := 44255680552642972257091584 }, { target := 484, numerator := 2000276249242615436997033984 }, { target := 489, numerator := 44491886498820804638146560 }, { target := 627, numerator := 45485005012438610375344128 }, { target := 629, numerator := 2055839478388243643580284928 }, { target := 634, numerator := 45727772234899160322539520 }, { target := 653, numerator := 45485005012438610375344128 }, { target := 655, numerator := 2055839478388243643580284928 }, { target := 660, numerator := 45727772234899160322539520 }, { target := 749, numerator := 50402302851621162848354304 }, { target := 751, numerator := 2278092394970756469913288704 }, { target := 756, numerator := 50671315179212583060111360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2
