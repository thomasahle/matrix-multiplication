import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 145422902435761340700583526400 }, { target := 260, numerator := 499211396763029776852813086720 }, { target := 262, numerator := 145422902435761340700583526400 }, { target := 353, numerator := 149577842505354521863457341440 }, { target := 356, numerator := 513474579527687770477179174912 }, { target := 358, numerator := 149577842505354521863457341440 }, { target := 379, numerator := 145422902435761340700583526400 }, { target := 382, numerator := 499211396763029776852813086720 }, { target := 384, numerator := 145422902435761340700583526400 }, { target := 389, numerator := 7011769753764849213295820800 }, { target := 391, numerator := 7011769753764849213295820800 }, { target := 524, numerator := 128803142157388616049088266240 }, { target := 527, numerator := 442158665704397802355348733952 }, { target := 529, numerator := 128803142157388616049088266240 }, { target := 620, numerator := 6028818040979705867329905623040 }, { target := 623, numerator := 20695878191518748748955193966592 }, { target := 625, numerator := 6028818040979705867329905623040 }, { target := 646, numerator := 1641201327489306559335156940800 }, { target := 649, numerator := 5633957192039907481624604835840 }, { target := 651, numerator := 1641201327489306559335156940800 }, { target := 656, numerator := 140515865865447578234448248832 }, { target := 658, numerator := 140515865865447578234448248832 }, { target := 695, numerator := 149577842505354521863457341440 }, { target := 698, numerator := 513474579527687770477179174912 }, { target := 700, numerator := 149577842505354521863457341440 }, { target := 721, numerator := 6028818040979705867329905623040 }, { target := 724, numerator := 20695878191518748748955193966592 }, { target := 726, numerator := 6028818040979705867329905623040 }, { target := 731, numerator := 235875934516649527535271411712 }, { target := 733, numerator := 235875934516649527535271411712 }, { target := 735, numerator := 145422902435761340700583526400 }, { target := 738, numerator := 499211396763029776852813086720 }, { target := 740, numerator := 145422902435761340700583526400 }, { target := 745, numerator := 226339927651529332605189095424 }, { target := 747, numerator := 226339927651529332605189095424 }, { target := 749, numerator := 20696810031802451470969733120 }, { target := 836, numerator := 145422902435761340700583526400 }, { target := 839, numerator := 499211396763029776852813086720 }, { target := 841, numerator := 145422902435761340700583526400 }, { target := 862, numerator := 124648202087795434886214451200 }, { target := 865, numerator := 427895482939739808730982645760 }, { target := 867, numerator := 124648202087795434886214451200 }, { target := 872, numerator := 7011769753764849213295820800 }, { target := 874, numerator := 7011769753764849213295820800 }, { target := 911, numerator := 145422902435761340700583526400 }, { target := 914, numerator := 499211396763029776852813086720 }, { target := 916, numerator := 145422902435761340700583526400 }, { target := 937, numerator := 1641201327489306559335156940800 }, { target := 940, numerator := 5633957192039907481624604835840 }, { target := 942, numerator := 1641201327489306559335156940800 }, { target := 947, numerator := 226339927651529332605189095424 }, { target := 949, numerator := 226339927651529332605189095424 }, { target := 961, numerator := 151173755891170149038657896448 }, { target := 963, numerator := 151173755891170149038657896448 }, { target := 965, numerator := 18917271225329717325802242048 }, { target := 992, numerator := 7292240543915443181827653632 }, { target := 994, numerator := 7292240543915443181827653632 }, { target := 1006, numerator := 140515865865447578234448248832 }, { target := 1008, numerator := 140515865865447578234448248832 }, { target := 1010, numerator := 20696810031802451470969733120 }, { target := 1011, numerator := 6731298963614255244763987968 }, { target := 1013, numerator := 6731298963614255244763987968 }, { target := 1015, numerator := 18917271225329717325802242048 }]

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
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
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
    Slot3.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2876406189862799906671951872 }, { target := 112, numerator := 108073969831089407231162056704 }, { target := 115, numerator := 108065795968109882086583697408 }, { target := 122, numerator := 2884580052842325051250311168 }, { target := 206, numerator := 76704165063007997511252049920 }, { target := 208, numerator := 2881972528829050859497654845440 }, { target := 211, numerator := 2881754559149596855642231930880 }, { target := 218, numerator := 76922134742462001366674964480 }, { target := 241, numerator := 73348357841501397620134772736 }, { target := 243, numerator := 2755886230692779884394632445952 }, { target := 246, numerator := 2755677797186801993207884283904 }, { target := 253, numerator := 73556791347479288806882934784 }, { target := 302, numerator := 2397005158218999922226626560 }, { target := 304, numerator := 90061641525907839359301713920 }, { target := 307, numerator := 90054829973424901738819747840 }, { target := 314, numerator := 2403816710701937542708592640 }, { target := 337, numerator := 75265961968076597557916073984 }, { target := 339, numerator := 2827935543913506155882073817088 }, { target := 342, numerator := 2827721661165541914598940082176 }, { target := 349, numerator := 75479844716040838841049808896 }, { target := 363, numerator := 2397005158218999922226626560 }, { target := 365, numerator := 90061641525907839359301713920 }, { target := 368, numerator := 90054829973424901738819747840 }, { target := 375, numerator := 2403816710701937542708592640 }, { target := 473, numerator := 73348357841501397620134772736 }, { target := 475, numerator := 2755886230692779884394632445952 }, { target := 478, numerator := 2755677797186801993207884283904 }, { target := 485, numerator := 73556791347479288806882934784 }, { target := 508, numerator := 41707889753010598646743302144 }, { target := 510, numerator := 1567072562550796404851849822208 }, { target := 513, numerator := 1566954041537593290255463612416 }, { target := 520, numerator := 41826410766213713243129511936 }, { target := 569, numerator := 75265961968076597557916073984 }, { target := 571, numerator := 2827935543913506155882073817088 }, { target := 574, numerator := 2827721661165541914598940082176 }, { target := 581, numerator := 75479844716040838841049808896 }, { target := 604, numerator := 1175011928558953761875492339712 }, { target := 606, numerator := 44148216676000022853929700163584 }, { target := 609, numerator := 44144877652972886832369440391168 }, { target := 616, numerator := 1178350951586089783435752112128 }, { target := 630, numerator := 46022499037804798506751229952 }, { target := 632, numerator := 1729183517297430515698592907264 }, { target := 635, numerator := 1729052735489758113385339158528 }, { target := 642, numerator := 46153280845477200820004978688 }, { target := 679, numerator := 76704165063007997511252049920 }, { target := 681, numerator := 2881972528829050859497654845440 }, { target := 684, numerator := 2881754559149596855642231930880 }, { target := 691, numerator := 76922134742462001366674964480 }, { target := 705, numerator := 73348357841501397620134772736 }, { target := 707, numerator := 2755886230692779884394632445952 }, { target := 710, numerator := 2755677797186801993207884283904 }, { target := 717, numerator := 73556791347479288806882934784 }, { target := 951, numerator := 124648202087795434886214451200 }, { target := 954, numerator := 427895482939739808730982645760 }, { target := 956, numerator := 124648202087795434886214451200 }, { target := 982, numerator := 145422902435761340700583526400 }, { target := 985, numerator := 499211396763029776852813086720 }, { target := 987, numerator := 145422902435761340700583526400 }, { target := 996, numerator := 128803142157388616049088266240 }, { target := 999, numerator := 442158665704397802355348733952 }, { target := 1001, numerator := 128803142157388616049088266240 }]

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
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 101850376989054021528453120 }, { target := 57, numerator := 16260126798662820186386595840 }, { target := 59, numerator := 162251613457592411317799485440 }, { target := 67, numerator := 16260126798662820186386595840 }, { target := 74, numerator := 101838755540287584510935040 }, { target := 91, numerator := 99728494135115396079943680 }, { target := 92, numerator := 15921374157024011432503541760 }, { target := 94, numerator := 158871371510559236082011996160 }, { target := 102, numerator := 15921374157024011432503541760 }, { target := 109, numerator := 99717114799864926500290560 }, { target := 152, numerator := 78509665595729141594849280 }, { target := 153, numerator := 12533847740635923893673000960 }, { target := 155, numerator := 125068952040227483724137103360 }, { target := 163, numerator := 12533847740635923893673000960 }, { target := 170, numerator := 78500707395638346393845760 }, { target := 187, numerator := 2467749759130621396616478720 }, { target := 188, numerator := 393969322225934580765991895040 }, { target := 190, numerator := 3931221384399582799220850032640 }, { target := 198, numerator := 393969322225934580765991895040 }, { target := 205, numerator := 2467468181111551266379530240 }, { target := 222, numerator := 78509665595729141594849280 }, { target := 223, numerator := 12533847740635923893673000960 }, { target := 225, numerator := 125068952040227483724137103360 }, { target := 233, numerator := 12533847740635923893673000960 }, { target := 240, numerator := 78500707395638346393845760 }, { target := 283, numerator := 78509665595729141594849280 }, { target := 284, numerator := 12533847740635923893673000960 }, { target := 286, numerator := 125068952040227483724137103360 }, { target := 294, numerator := 12533847740635923893673000960 }, { target := 301, numerator := 78500707395638346393845760 }, { target := 318, numerator := 80631548449667767043358720 }, { target := 319, numerator := 12872600382274732647556055040 }, { target := 321, numerator := 128449193987260658959924592640 }, { target := 329, numerator := 12872600382274732647556055040 }, { target := 336, numerator := 80622348136061004404490240 }, { target := 419, numerator := 80631548449667767043358720 }, { target := 420, numerator := 12872600382274732647556055040 }, { target := 422, numerator := 128449193987260658959924592640 }, { target := 430, numerator := 12872600382274732647556055040 }, { target := 437, numerator := 80622348136061004404490240 }, { target := 785, numerator := 2397005158218999922226626560 }, { target := 787, numerator := 90061641525907839359301713920 }, { target := 790, numerator := 90054829973424901738819747840 }, { target := 797, numerator := 2403816710701937542708592640 }, { target := 820, numerator := 46022499037804798506751229952 }, { target := 822, numerator := 1729183517297430515698592907264 }, { target := 825, numerator := 1729052735489758113385339158528 }, { target := 832, numerator := 46153280845477200820004978688 }, { target := 846, numerator := 2397005158218999922226626560 }, { target := 848, numerator := 90061641525907839359301713920 }, { target := 851, numerator := 90054829973424901738819747840 }, { target := 858, numerator := 2403816710701937542708592640 }, { target := 895, numerator := 73827758873145197604580098048 }, { target := 897, numerator := 2773898558997961452266492788736 }, { target := 900, numerator := 2773688763181486973555648233472 }, { target := 907, numerator := 74037554689619676315424653312 }, { target := 921, numerator := 41707889753010598646743302144 }, { target := 923, numerator := 1567072562550796404851849822208 }, { target := 926, numerator := 1566954041537593290255463612416 }, { target := 933, numerator := 41826410766213713243129511936 }, { target := 966, numerator := 2876406189862799906671951872 }, { target := 968, numerator := 108073969831089407231162056704 }, { target := 971, numerator := 108065795968109882086583697408 }, { target := 978, numerator := 2884580052842325051250311168 }]

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
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 19763103730809465219317760 }, { target := 15, numerator := 15371302901740695170580480 }, { target := 16, numerator := 17567203316275080194949120 }, { target := 17, numerator := 20641463896623219229065216 }, { target := 18, numerator := 243744946013316737704919040 }, { target := 19, numerator := 548096743467782502082412544 }, { target := 20, numerator := 15371302901740695170580480 }, { target := 21, numerator := 243744946013316737704919040 }, { target := 22, numerator := 17567203316275080194949120 }, { target := 23, numerator := 17128023233368203190075392 }, { target := 24, numerator := 17128023233368203190075392 }, { target := 25, numerator := 17128023233368203190075392 }, { target := 26, numerator := 548096743467782502082412544 }, { target := 27, numerator := 17128023233368203190075392 }, { target := 28, numerator := 19763103730809465219317760 }, { target := 29, numerator := 20641463896623219229065216 }, { target := 454, numerator := 1364370675082536163391569920 }, { target := 455, numerator := 217817948573754028746803773440 }, { target := 457, numerator := 2173495571942331676611355607040 }, { target := 465, numerator := 217817948573754028746803773440 }, { target := 472, numerator := 1364214996091769100844400640 }, { target := 489, numerator := 74265899887851890697830400 }, { target := 490, numerator := 11856342457358306385906892800 }, { target := 492, numerator := 118308468146161133252562124800 }, { target := 500, numerator := 11856342457358306385906892800 }, { target := 507, numerator := 74257425914793030372556800 }, { target := 550, numerator := 2467749759130621396616478720 }, { target := 551, numerator := 393969322225934580765991895040 }, { target := 553, numerator := 3931221384399582799220850032640 }, { target := 561, numerator := 393969322225934580765991895040 }, { target := 568, numerator := 2467468181111551266379530240 }, { target := 585, numerator := 1364370675082536163391569920 }, { target := 586, numerator := 217817948573754028746803773440 }, { target := 588, numerator := 2173495571942331676611355607040 }, { target := 596, numerator := 217817948573754028746803773440 }, { target := 603, numerator := 1364214996091769100844400640 }, { target := 660, numerator := 101850376989054021528453120 }, { target := 661, numerator := 16260126798662820186386595840 }, { target := 663, numerator := 162251613457592411317799485440 }, { target := 671, numerator := 16260126798662820186386595840 }, { target := 678, numerator := 101838755540287584510935040 }, { target := 766, numerator := 78509665595729141594849280 }, { target := 767, numerator := 12533847740635923893673000960 }, { target := 769, numerator := 125068952040227483724137103360 }, { target := 777, numerator := 12533847740635923893673000960 }, { target := 784, numerator := 78500707395638346393845760 }, { target := 801, numerator := 74265899887851890697830400 }, { target := 802, numerator := 11856342457358306385906892800 }, { target := 804, numerator := 118308468146161133252562124800 }, { target := 812, numerator := 11856342457358306385906892800 }, { target := 819, numerator := 74257425914793030372556800 }, { target := 876, numerator := 99728494135115396079943680 }, { target := 877, numerator := 15921374157024011432503541760 }, { target := 879, numerator := 158871371510559236082011996160 }, { target := 887, numerator := 15921374157024011432503541760 }, { target := 894, numerator := 99717114799864926500290560 }]

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
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 40, numerator := 484514801142425598925209600 }, { target := 41, numerator := 376844845332997688052940800 }, { target := 42, numerator := 430679823237711643489075200 }, { target := 43, numerator := 506048792304311181099663360 }, { target := 44, numerator := 5975682547423249053410918400 }, { target := 45, numerator := 13437210485016603276859146240 }, { target := 46, numerator := 376844845332997688052940800 }, { target := 47, numerator := 5975682547423249053410918400 }, { target := 48, numerator := 430679823237711643489075200 }, { target := 49, numerator := 419912827656768852401848320 }, { target := 50, numerator := 419912827656768852401848320 }, { target := 51, numerator := 419912827656768852401848320 }, { target := 52, numerator := 13437210485016603276859146240 }, { target := 53, numerator := 419912827656768852401848320 }, { target := 54, numerator := 484514801142425598925209600 }, { target := 55, numerator := 506048792304311181099663360 }, { target := 75, numerator := 19763103730809465219317760 }, { target := 76, numerator := 15371302901740695170580480 }, { target := 77, numerator := 17567203316275080194949120 }, { target := 78, numerator := 20641463896623219229065216 }, { target := 79, numerator := 243744946013316737704919040 }, { target := 80, numerator := 548096743467782502082412544 }, { target := 81, numerator := 15371302901740695170580480 }, { target := 82, numerator := 243744946013316737704919040 }, { target := 83, numerator := 17567203316275080194949120 }, { target := 84, numerator := 17128023233368203190075392 }, { target := 85, numerator := 17128023233368203190075392 }, { target := 86, numerator := 17128023233368203190075392 }, { target := 87, numerator := 548096743467782502082412544 }, { target := 88, numerator := 17128023233368203190075392 }, { target := 89, numerator := 19763103730809465219317760 }, { target := 90, numerator := 20641463896623219229065216 }, { target := 136, numerator := 406099905694375140151787520 }, { target := 137, numerator := 315855482206736220118056960 }, { target := 138, numerator := 360977693950555680134922240 }, { target := 139, numerator := 424148790391902924158533632 }, { target := 140, numerator := 5008565503563960061872046080 }, { target := 141, numerator := 11262504051257337220209573888 }, { target := 142, numerator := 315855482206736220118056960 }, { target := 143, numerator := 5008565503563960061872046080 }, { target := 144, numerator := 360977693950555680134922240 }, { target := 145, numerator := 351953251601791788131549184 }, { target := 146, numerator := 351953251601791788131549184 }, { target := 147, numerator := 351953251601791788131549184 }, { target := 148, numerator := 11262504051257337220209573888 }, { target := 149, numerator := 351953251601791788131549184 }, { target := 150, numerator := 406099905694375140151787520 }, { target := 151, numerator := 424148790391902924158533632 }, { target := 171, numerator := 399087191467313717009448960 }, { target := 172, numerator := 310401148919021779896238080 }, { target := 173, numerator := 354744170193167748452843520 }, { target := 174, numerator := 416824399976972104432091136 }, { target := 175, numerator := 4922075361430202509783203840 }, { target := 176, numerator := 11068018110026833751728717824 }, { target := 177, numerator := 310401148919021779896238080 }, { target := 178, numerator := 4922075361430202509783203840 }, { target := 179, numerator := 354744170193167748452843520 }, { target := 180, numerator := 345875565938338554741522432 }, { target := 181, numerator := 345875565938338554741522432 }, { target := 182, numerator := 345875565938338554741522432 }, { target := 183, numerator := 11068018110026833751728717824 }, { target := 184, numerator := 345875565938338554741522432 }, { target := 185, numerator := 399087191467313717009448960 }, { target := 186, numerator := 416824399976972104432091136 }]

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
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 267, numerator := 19763103730809465219317760 }, { target := 268, numerator := 15371302901740695170580480 }, { target := 269, numerator := 17567203316275080194949120 }, { target := 270, numerator := 20641463896623219229065216 }, { target := 271, numerator := 243744946013316737704919040 }, { target := 272, numerator := 548096743467782502082412544 }, { target := 273, numerator := 15371302901740695170580480 }, { target := 274, numerator := 243744946013316737704919040 }, { target := 275, numerator := 17567203316275080194949120 }, { target := 276, numerator := 17128023233368203190075392 }, { target := 277, numerator := 17128023233368203190075392 }, { target := 278, numerator := 17128023233368203190075392 }, { target := 279, numerator := 548096743467782502082412544 }, { target := 280, numerator := 17128023233368203190075392 }, { target := 281, numerator := 19763103730809465219317760 }, { target := 282, numerator := 20641463896623219229065216 }, { target := 403, numerator := 399724710942501119113297920 }, { target := 404, numerator := 310896997399723092643676160 }, { target := 405, numerator := 355310854171112105878487040 }, { target := 406, numerator := 417490253651056724407222272 }, { target := 407, numerator := 4929938101624180469064007680 }, { target := 408, numerator := 11085698650138697703408795648 }, { target := 409, numerator := 310896997399723092643676160 }, { target := 410, numerator := 4929938101624180469064007680 }, { target := 411, numerator := 355310854171112105878487040 }, { target := 412, numerator := 346428082816834303231524864 }, { target := 413, numerator := 346428082816834303231524864 }, { target := 414, numerator := 346428082816834303231524864 }, { target := 415, numerator := 11085698650138697703408795648 }, { target := 416, numerator := 346428082816834303231524864 }, { target := 417, numerator := 399724710942501119113297920 }, { target := 418, numerator := 417490253651056724407222272 }, { target := 438, numerator := 358285945055319982363115520 }, { target := 439, numerator := 278666846154137764060200960 }, { target := 440, numerator := 318476395604728873211658240 }, { target := 441, numerator := 374209764835556426023698432 }, { target := 442, numerator := 4418859989015613115811758080 }, { target := 443, numerator := 9936463542867540844203737088 }, { target := 444, numerator := 278666846154137764060200960 }, { target := 445, numerator := 4418859989015613115811758080 }, { target := 446, numerator := 318476395604728873211658240 }, { target := 447, numerator := 310514485714610651381366784 }, { target := 448, numerator := 310514485714610651381366784 }, { target := 449, numerator := 310514485714610651381366784 }, { target := 450, numerator := 9936463542867540844203737088 }, { target := 451, numerator := 310514485714610651381366784 }, { target := 452, numerator := 358285945055319982363115520 }, { target := 453, numerator := 374209764835556426023698432 }, { target := 534, numerator := 484514801142425598925209600 }, { target := 535, numerator := 376844845332997688052940800 }, { target := 536, numerator := 430679823237711643489075200 }, { target := 537, numerator := 506048792304311181099663360 }, { target := 538, numerator := 5975682547423249053410918400 }, { target := 539, numerator := 13437210485016603276859146240 }, { target := 540, numerator := 376844845332997688052940800 }, { target := 541, numerator := 5975682547423249053410918400 }, { target := 542, numerator := 430679823237711643489075200 }, { target := 543, numerator := 419912827656768852401848320 }, { target := 544, numerator := 419912827656768852401848320 }, { target := 545, numerator := 419912827656768852401848320 }, { target := 546, numerator := 13437210485016603276859146240 }, { target := 547, numerator := 419912827656768852401848320 }, { target := 548, numerator := 484514801142425598925209600 }, { target := 549, numerator := 506048792304311181099663360 }]

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
    Slot5.Left9.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left7.expected,
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
    Slot10.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1842911824034908160741343232 }, { target := 57, numerator := 272188432093644476111139110912 }, { target := 59, numerator := 2836974507346122045220223713280 }, { target := 67, numerator := 272188432093644476111139110912 }, { target := 74, numerator := 1842911824034908160741343232 }, { target := 110, numerator := 5226530229335345186832646144 }, { target := 112, numerator := 189411185498744312256369000448 }, { target := 115, numerator := 189411255106615747450261995520 }, { target := 122, numerator := 5226460621463909992939651072 }, { target := 152, numerator := 64497319076661554750313988096 }, { target := 153, numerator := 9525916500597307911822047707136 }, { target := 155, numerator := 99287034586409830164933210275840 }, { target := 163, numerator := 9525916500597307911822047707136 }, { target := 170, numerator := 64497319076661554750313988096 }, { target := 206, numerator := 547992268147612789433503318016 }, { target := 208, numerator := 19859421183752491209324360630272 }, { target := 211, numerator := 19859428482012268719527721697280 }, { target := 218, numerator := 547984969887835279230142251008 }, { target := 257, numerator := 59334312378421514833483530240 }, { target := 260, numerator := 201127294490529279810302115840 }, { target := 262, numerator := 59334312378421514833483530240 }, { target := 302, numerator := 5906808933003633387538219008000 }, { target := 304, numerator := 214064710892731277397391835136000 }, { target := 307, numerator := 214064789560677076891745648640000 }, { target := 314, numerator := 5906730265057833893184405504000 }, { target := 353, numerator := 4968010644867432196638448287744 }, { target := 356, numerator := 16840214370896166754237865263104 }, { target := 358, numerator := 4968010644867432196638448287744 }, { target := 389, numerator := 30508685740935683900323135488 }, { target := 391, numerator := 30508685740935683900323135488 }, { target := 679, numerator := 547992686169705833930439000064 }, { target := 681, numerator := 19859436333011508944612871897088 }, { target := 684, numerator := 19859443631276853748380593029120 }, { target := 691, numerator := 547985387904361030162717868032 }, { target := 695, numerator := 4968012442786094236581324914688 }, { target := 698, numerator := 16840220465354865522864090513408 }, { target := 700, numerator := 4968012442786094236581324914688 }, { target := 731, numerator := 295509359832318151370301505536 }, { target := 733, numerator := 295509359832318151370301505536 }, { target := 750, numerator := 19763103730809465219317760 }, { target := 751, numerator := 15371302901740695170580480 }, { target := 752, numerator := 17567203316275080194949120 }, { target := 753, numerator := 20641463896623219229065216 }, { target := 754, numerator := 243744946013316737704919040 }, { target := 755, numerator := 548096743467782502082412544 }, { target := 756, numerator := 15371302901740695170580480 }, { target := 757, numerator := 243744946013316737704919040 }, { target := 758, numerator := 17567203316275080194949120 }, { target := 759, numerator := 17128023233368203190075392 }, { target := 760, numerator := 17128023233368203190075392 }, { target := 761, numerator := 17128023233368203190075392 }, { target := 762, numerator := 548096743467782502082412544 }, { target := 763, numerator := 17128023233368203190075392 }, { target := 764, numerator := 19763103730809465219317760 }, { target := 765, numerator := 20641463896623219229065216 }, { target := 966, numerator := 5226530229335345186832646144 }, { target := 968, numerator := 189411185498744312256369000448 }, { target := 971, numerator := 189411255106615747450261995520 }, { target := 978, numerator := 5226460621463909992939651072 }, { target := 982, numerator := 59332514459759474890606903296 }, { target := 985, numerator := 201121200031830511184076865536 }, { target := 987, numerator := 59332514459759474890606903296 }, { target := 992, numerator := 30508685740935683900323135488 }, { target := 994, numerator := 30508685740935683900323135488 }]

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
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left6.expected,
    Slot14.Left14.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 8762954376788155816445214720 }, { target := 15, numerator := 736870190174772290769062461440 }, { target := 20, numerator := 736870012401977435756062310400 }, { target := 28, numerator := 8763132149583010829445365760 }, { target := 56, numerator := 5247141451231707840383025152 }, { target := 57, numerator := 550153317589723806045860528128 }, { target := 59, numerator := 5930102886023213922662744064000 }, { target := 67, numerator := 550153737260318961745119936512 }, { target := 74, numerator := 5247141451231707840383025152 }, { target := 110, numerator := 1841114445793001553302388736 }, { target := 112, numerator := 64434415319434641660505489408 }, { target := 115, numerator := 64434446922073680646426853376 }, { target := 122, numerator := 1841098644473482060341706752 }, { target := 136, numerator := 29961134729050935864594530304 }, { target := 137, numerator := 2519409105236000014587037483008 }, { target := 142, numerator := 2519408497418769798310165217280 }, { target := 150, numerator := 29961742546281152141466796032 }, { target := 152, numerator := 190158143002607098866207555584 }, { target := 153, numerator := 19937738330844492539741838770176 }, { target := 155, numerator := 214908891460486625981091545088000 }, { target := 163, numerator := 19937753539845772441133414088704 }, { target := 170, numerator := 190158143002607098866207555584 }, { target := 206, numerator := 271922968733345082928976101376 }, { target := 208, numerator := 9516625944842499093962663395328 }, { target := 211, numerator := 9516630612386902390407079919616 }, { target := 218, numerator := 271920634961143434706767839232 }, { target := 257, numerator := 8762954376788155816445214720 }, { target := 260, numerator := 29961134729050935864594530304 }, { target := 262, numerator := 8762951546339966308778508288 }, { target := 267, numerator := 8762951546339966308778508288 }, { target := 268, numerator := 736869952164529853924823269376 }, { target := 273, numerator := 736869774391792419807072092160 }, { target := 281, numerator := 8763129319077400426529685504 }, { target := 283, numerator := 64497350710152502983536934912 }, { target := 284, numerator := 9525921172698376750046266785792 }, { target := 286, numerator := 99287083282937915820133035540480 }, { target := 294, numerator := 9525921172698376750046266785792 }, { target := 301, numerator := 64497350710152502983536934912 }, { target := 302, numerator := 2834207627137396958700177981440 }, { target := 304, numerator := 99190200677515412255149465272320 }, { target := 307, numerator := 99190249326550135017967756247040 }, { target := 314, numerator := 2834183302620035577291032494080 }, { target := 353, numerator := 736870190174772290769062461440 }, { target := 356, numerator := 2519409105236000014587037483008 }, { target := 358, numerator := 736869952164529853924823269376 }, { target := 660, numerator := 1842896007289434044129869824 }, { target := 661, numerator := 272186096043110056999029571584 }, { target := 663, numerator := 2836950159082079217620311080960 }, { target := 671, numerator := 272186096043110056999029571584 }, { target := 678, numerator := 1842896007289434044129869824 }, { target := 679, numerator := 271922968733345082928976101376 }, { target := 681, numerator := 9516625944842499093962663395328 }, { target := 684, numerator := 9516630612386902390407079919616 }, { target := 691, numerator := 271920634961143434706767839232 }, { target := 695, numerator := 736870012401977435756062310400 }, { target := 698, numerator := 2519408497418769798310165217280 }, { target := 700, numerator := 736869774391792419807072092160 }, { target := 966, numerator := 1841114445793001553302388736 }, { target := 968, numerator := 64434415319434641660505489408 }, { target := 971, numerator := 64434446922073680646426853376 }, { target := 978, numerator := 1841098644473482060341706752 }, { target := 982, numerator := 8763132149583010829445365760 }, { target := 985, numerator := 29961742546281152141466796032 }, { target := 987, numerator := 8763129319077400426529685504 }]

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
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 27118831769720607911398342656 }, { target := 6, numerator := 262674986517616134551379116032 }, { target := 11, numerator := 27118831769720607911398342656 }, { target := 14, numerator := 59941534873522319809849589760 }, { target := 15, numerator := 5018852859069291882861356384256 }, { target := 20, numerator := 5018854675387706312101894029312 }, { target := 28, numerator := 59939718555107890569311944704 }, { target := 126, numerator := 27118831769720607911398342656 }, { target := 128, numerator := 262674986517616134551379116032 }, { target := 133, numerator := 27118831769720607911398342656 }, { target := 136, numerator := 203185614755783234428243804160 }, { target := 137, numerator := 17012555746036916998798779088896 }, { target := 142, numerator := 17012561902865807129092231790592 }, { target := 150, numerator := 203179457926893104134791102464 }, { target := 257, numerator := 19763103730809465219317760 }, { target := 258, numerator := 484514801142425598925209600 }, { target := 259, numerator := 19763103730809465219317760 }, { target := 260, numerator := 406099905694375140151787520 }, { target := 261, numerator := 399087191467313717009448960 }, { target := 262, numerator := 19763103730809465219317760 }, { target := 263, numerator := 399724710942501119113297920 }, { target := 264, numerator := 358285945055319982363115520 }, { target := 265, numerator := 484514801142425598925209600 }, { target := 266, numerator := 19763103730809465219317760 }, { target := 267, numerator := 59941534873522319809849589760 }, { target := 268, numerator := 5018852859069291882861356384256 }, { target := 273, numerator := 5018854675387706312101894029312 }, { target := 281, numerator := 59939718555107890569311944704 }, { target := 283, numerator := 190158212884982501497540444160 }, { target := 284, numerator := 19937745657885515949424236298240 }, { target := 286, numerator := 214908970438665489450396549120000 }, { target := 294, numerator := 19937760866892385099428355112960 }, { target := 301, numerator := 190158212884982501497540444160 }, { target := 353, numerator := 15371302901740695170580480 }, { target := 354, numerator := 376844845332997688052940800 }, { target := 355, numerator := 15371302901740695170580480 }, { target := 356, numerator := 315855482206736220118056960 }, { target := 357, numerator := 310401148919021779896238080 }, { target := 358, numerator := 15371302901740695170580480 }, { target := 359, numerator := 310896997399723092643676160 }, { target := 360, numerator := 278666846154137764060200960 }, { target := 361, numerator := 376844845332997688052940800 }, { target := 362, numerator := 15371302901740695170580480 }, { target := 379, numerator := 17567203316275080194949120 }, { target := 380, numerator := 430679823237711643489075200 }, { target := 381, numerator := 17567203316275080194949120 }, { target := 382, numerator := 360977693950555680134922240 }, { target := 383, numerator := 354744170193167748452843520 }, { target := 384, numerator := 17567203316275080194949120 }, { target := 385, numerator := 355310854171112105878487040 }, { target := 386, numerator := 318476395604728873211658240 }, { target := 387, numerator := 430679823237711643489075200 }, { target := 388, numerator := 17567203316275080194949120 }, { target := 660, numerator := 5247071568856305209050136576 }, { target := 661, numerator := 550145990548700396363463000064 }, { target := 663, numerator := 5930023907844350453357740032000 }, { target := 671, numerator := 550146410213706303450178912256 }, { target := 678, numerator := 5247071568856305209050136576 }]

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
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 524, numerator := 20641463896623219229065216 }, { target := 525, numerator := 506048792304311181099663360 }, { target := 526, numerator := 20641463896623219229065216 }, { target := 527, numerator := 424148790391902924158533632 }, { target := 528, numerator := 416824399976972104432091136 }, { target := 529, numerator := 20641463896623219229065216 }, { target := 530, numerator := 417490253651056724407222272 }, { target := 531, numerator := 374209764835556426023698432 }, { target := 532, numerator := 506048792304311181099663360 }, { target := 533, numerator := 20641463896623219229065216 }, { target := 620, numerator := 243744946013316737704919040 }, { target := 621, numerator := 5975682547423249053410918400 }, { target := 622, numerator := 243744946013316737704919040 }, { target := 623, numerator := 5008565503563960061872046080 }, { target := 624, numerator := 4922075361430202509783203840 }, { target := 625, numerator := 243744946013316737704919040 }, { target := 626, numerator := 4929938101624180469064007680 }, { target := 627, numerator := 4418859989015613115811758080 }, { target := 628, numerator := 5975682547423249053410918400 }, { target := 629, numerator := 243744946013316737704919040 }, { target := 646, numerator := 548096743467782502082412544 }, { target := 647, numerator := 13437210485016603276859146240 }, { target := 648, numerator := 548096743467782502082412544 }, { target := 649, numerator := 11262504051257337220209573888 }, { target := 650, numerator := 11068018110026833751728717824 }, { target := 651, numerator := 548096743467782502082412544 }, { target := 652, numerator := 11085698650138697703408795648 }, { target := 653, numerator := 9936463542867540844203737088 }, { target := 654, numerator := 13437210485016603276859146240 }, { target := 655, numerator := 548096743467782502082412544 }, { target := 695, numerator := 15371302901740695170580480 }, { target := 696, numerator := 376844845332997688052940800 }, { target := 697, numerator := 15371302901740695170580480 }, { target := 698, numerator := 315855482206736220118056960 }, { target := 699, numerator := 310401148919021779896238080 }, { target := 700, numerator := 15371302901740695170580480 }, { target := 701, numerator := 310896997399723092643676160 }, { target := 702, numerator := 278666846154137764060200960 }, { target := 703, numerator := 376844845332997688052940800 }, { target := 704, numerator := 15371302901740695170580480 }, { target := 721, numerator := 243744946013316737704919040 }, { target := 722, numerator := 5975682547423249053410918400 }, { target := 723, numerator := 243744946013316737704919040 }, { target := 724, numerator := 5008565503563960061872046080 }, { target := 725, numerator := 4922075361430202509783203840 }, { target := 726, numerator := 243744946013316737704919040 }, { target := 727, numerator := 4929938101624180469064007680 }, { target := 728, numerator := 4418859989015613115811758080 }, { target := 729, numerator := 5975682547423249053410918400 }, { target := 730, numerator := 243744946013316737704919040 }, { target := 735, numerator := 17567203316275080194949120 }, { target := 736, numerator := 430679823237711643489075200 }, { target := 737, numerator := 17567203316275080194949120 }, { target := 738, numerator := 360977693950555680134922240 }, { target := 739, numerator := 354744170193167748452843520 }, { target := 740, numerator := 17567203316275080194949120 }, { target := 741, numerator := 355310854171112105878487040 }, { target := 742, numerator := 318476395604728873211658240 }, { target := 743, numerator := 430679823237711643489075200 }, { target := 744, numerator := 17567203316275080194949120 }]

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

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 836, numerator := 17128023233368203190075392 }, { target := 837, numerator := 419912827656768852401848320 }, { target := 838, numerator := 17128023233368203190075392 }, { target := 839, numerator := 351953251601791788131549184 }, { target := 840, numerator := 345875565938338554741522432 }, { target := 841, numerator := 17128023233368203190075392 }, { target := 842, numerator := 346428082816834303231524864 }, { target := 843, numerator := 310514485714610651381366784 }, { target := 844, numerator := 419912827656768852401848320 }, { target := 845, numerator := 17128023233368203190075392 }, { target := 862, numerator := 17128023233368203190075392 }, { target := 863, numerator := 419912827656768852401848320 }, { target := 864, numerator := 17128023233368203190075392 }, { target := 865, numerator := 351953251601791788131549184 }, { target := 866, numerator := 345875565938338554741522432 }, { target := 867, numerator := 17128023233368203190075392 }, { target := 868, numerator := 346428082816834303231524864 }, { target := 869, numerator := 310514485714610651381366784 }, { target := 870, numerator := 419912827656768852401848320 }, { target := 871, numerator := 17128023233368203190075392 }, { target := 911, numerator := 17128023233368203190075392 }, { target := 912, numerator := 419912827656768852401848320 }, { target := 913, numerator := 17128023233368203190075392 }, { target := 914, numerator := 351953251601791788131549184 }, { target := 915, numerator := 345875565938338554741522432 }, { target := 916, numerator := 17128023233368203190075392 }, { target := 917, numerator := 346428082816834303231524864 }, { target := 918, numerator := 310514485714610651381366784 }, { target := 919, numerator := 419912827656768852401848320 }, { target := 920, numerator := 17128023233368203190075392 }, { target := 937, numerator := 548096743467782502082412544 }, { target := 938, numerator := 13437210485016603276859146240 }, { target := 939, numerator := 548096743467782502082412544 }, { target := 940, numerator := 11262504051257337220209573888 }, { target := 941, numerator := 11068018110026833751728717824 }, { target := 942, numerator := 548096743467782502082412544 }, { target := 943, numerator := 11085698650138697703408795648 }, { target := 944, numerator := 9936463542867540844203737088 }, { target := 945, numerator := 13437210485016603276859146240 }, { target := 946, numerator := 548096743467782502082412544 }, { target := 951, numerator := 17128023233368203190075392 }, { target := 952, numerator := 419912827656768852401848320 }, { target := 953, numerator := 17128023233368203190075392 }, { target := 954, numerator := 351953251601791788131549184 }, { target := 955, numerator := 345875565938338554741522432 }, { target := 956, numerator := 17128023233368203190075392 }, { target := 957, numerator := 346428082816834303231524864 }, { target := 958, numerator := 310514485714610651381366784 }, { target := 959, numerator := 419912827656768852401848320 }, { target := 960, numerator := 17128023233368203190075392 }, { target := 982, numerator := 19763103730809465219317760 }, { target := 983, numerator := 484514801142425598925209600 }, { target := 984, numerator := 19763103730809465219317760 }, { target := 985, numerator := 406099905694375140151787520 }, { target := 986, numerator := 399087191467313717009448960 }, { target := 987, numerator := 19763103730809465219317760 }, { target := 988, numerator := 399724710942501119113297920 }, { target := 989, numerator := 358285945055319982363115520 }, { target := 990, numerator := 484514801142425598925209600 }, { target := 991, numerator := 19763103730809465219317760 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left15.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 99910369808310135404101632 }, { target := 111, numerator := 97828903770637007583182848 }, { target := 112, numerator := 77014243393905729373995008 }, { target := 113, numerator := 2420745001813847655728545792 }, { target := 114, numerator := 77014243393905729373995008 }, { target := 115, numerator := 77014243393905729373995008 }, { target := 116, numerator := 79095709431578857194913792 }, { target := 117, numerator := 79095709431578857194913792 }, { target := 118, numerator := 1338382662223821188850778112 }, { target := 119, numerator := 72851311318559473732157440 }, { target := 120, numerator := 2420745001813847655728545792 }, { target := 121, numerator := 1338382662223821188850778112 }, { target := 122, numerator := 99910369808310135404101632 }, { target := 123, numerator := 77014243393905729373995008 }, { target := 124, numerator := 72851311318559473732157440 }, { target := 125, numerator := 97828903770637007583182848 }, { target := 206, numerator := 15950410097735909325693517824 }, { target := 207, numerator := 15618109887366411214741569536 }, { target := 208, numerator := 12295107783671430105222086656 }, { target := 209, numerator := 386465144659726303037115858944 }, { target := 210, numerator := 12295107783671430105222086656 }, { target := 211, numerator := 12295107783671430105222086656 }, { target := 212, numerator := 12627407994040928216174034944 }, { target := 213, numerator := 12627407994040928216174034944 }, { target := 214, numerator := 213669035267587285342102749184 }, { target := 215, numerator := 11630507362932433883318190080 }, { target := 216, numerator := 386465144659726303037115858944 }, { target := 217, numerator := 213669035267587285342102749184 }, { target := 218, numerator := 15950410097735909325693517824 }, { target := 219, numerator := 12295107783671430105222086656 }, { target := 220, numerator := 11630507362932433883318190080 }, { target := 221, numerator := 15618109887366411214741569536 }, { target := 302, numerator := 159161106534590651102222352384 }, { target := 303, numerator := 155845250148453345870926053376 }, { target := 304, numerator := 122686686287080293557963063296 }, { target := 305, numerator := 3856340977077685983997595746304 }, { target := 306, numerator := 122686686287080293557963063296 }, { target := 307, numerator := 122686686287080293557963063296 }, { target := 308, numerator := 126002542673217598789259362304 }, { target := 309, numerator := 126002542673217598789259362304 }, { target := 310, numerator := 2132095656286287263723520262144 }, { target := 311, numerator := 116054973514805683095370465280 }, { target := 312, numerator := 3856340977077685983997595746304 }, { target := 313, numerator := 2132095656286287263723520262144 }, { target := 314, numerator := 159161106534590651102222352384 }, { target := 315, numerator := 122686686287080293557963063296 }, { target := 316, numerator := 116054973514805683095370465280 }, { target := 317, numerator := 155845250148453345870926053376 }, { target := 996, numerator := 20641463896623219229065216 }, { target := 997, numerator := 506048792304311181099663360 }, { target := 998, numerator := 20641463896623219229065216 }, { target := 999, numerator := 424148790391902924158533632 }, { target := 1000, numerator := 416824399976972104432091136 }, { target := 1001, numerator := 20641463896623219229065216 }, { target := 1002, numerator := 417490253651056724407222272 }, { target := 1003, numerator := 374209764835556426023698432 }, { target := 1004, numerator := 506048792304311181099663360 }, { target := 1005, numerator := 20641463896623219229065216 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot21.Left11.expected,
    Slot21.Left18.expected,
    Slot22.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2892954551833767897766821888 }, { target := 57, numerator := 77145454715567143940448583680 }, { target := 58, numerator := 73770341071761081393053958144 }, { target := 59, numerator := 2410795459861473248139018240 }, { target := 60, numerator := 75698977439650259991565172736 }, { target := 61, numerator := 2410795459861473248139018240 }, { target := 62, numerator := 73770341071761081393053958144 }, { target := 63, numerator := 41947841001589634517618917376 }, { target := 64, numerator := 75698977439650259991565172736 }, { target := 65, numerator := 1181771934424094186237746741248 }, { target := 66, numerator := 46287272829340286364269150208 }, { target := 67, numerator := 77145454715567143940448583680 }, { target := 68, numerator := 73770341071761081393053958144 }, { target := 69, numerator := 2410795459861473248139018240 }, { target := 70, numerator := 46287272829340286364269150208 }, { target := 71, numerator := 2410795459861473248139018240 }, { target := 72, numerator := 74252500163733376042681761792 }, { target := 73, numerator := 41947841001589634517618917376 }, { target := 74, numerator := 2892954551833767897766821888 }, { target := 679, numerator := 15950410097735909325693517824 }, { target := 680, numerator := 15618109887366411214741569536 }, { target := 681, numerator := 12295107783671430105222086656 }, { target := 682, numerator := 386465144659726303037115858944 }, { target := 683, numerator := 12295107783671430105222086656 }, { target := 684, numerator := 12295107783671430105222086656 }, { target := 685, numerator := 12627407994040928216174034944 }, { target := 686, numerator := 12627407994040928216174034944 }, { target := 687, numerator := 213669035267587285342102749184 }, { target := 688, numerator := 11630507362932433883318190080 }, { target := 689, numerator := 386465144659726303037115858944 }, { target := 690, numerator := 213669035267587285342102749184 }, { target := 691, numerator := 15950410097735909325693517824 }, { target := 692, numerator := 12295107783671430105222086656 }, { target := 693, numerator := 11630507362932433883318190080 }, { target := 694, numerator := 15618109887366411214741569536 }, { target := 966, numerator := 99898969720472582901202944 }, { target := 967, numerator := 97817741184629404090761216 }, { target := 968, numerator := 77005455826197615986343936 }, { target := 969, numerator := 2420468787185616956543729664 }, { target := 970, numerator := 77005455826197615986343936 }, { target := 971, numerator := 77005455826197615986343936 }, { target := 972, numerator := 79086684362040794796785664 }, { target := 973, numerator := 79086684362040794796785664 }, { target := 974, numerator := 1338229948547163975114031104 }, { target := 975, numerator := 72842998754511258365460480 }, { target := 976, numerator := 2420468787185616956543729664 }, { target := 977, numerator := 1338229948547163975114031104 }, { target := 978, numerator := 99898969720472582901202944 }, { target := 979, numerator := 77005455826197615986343936 }, { target := 980, numerator := 72842998754511258365460480 }, { target := 981, numerator := 97817741184629404090761216 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 108695734301874963444312047616 }, { target := 153, numerator := 2898552914716665691848321269760 }, { target := 154, numerator := 2771741224697811567829957214208 }, { target := 155, numerator := 90579778584895802870260039680 }, { target := 156, numerator := 2844205047565728210126165245952 }, { target := 157, numerator := 90579778584895802870260039680 }, { target := 158, numerator := 2771741224697811567829957214208 }, { target := 159, numerator := 1576088147377186969942524690432 }, { target := 160, numerator := 2844205047565728210126165245952 }, { target := 161, numerator := 44402207462315922567001471451136 }, { target := 162, numerator := 1739131748829999415108992761856 }, { target := 163, numerator := 2898552914716665691848321269760 }, { target := 164, numerator := 2771741224697811567829957214208 }, { target := 165, numerator := 90579778584895802870260039680 }, { target := 166, numerator := 1739131748829999415108992761856 }, { target := 167, numerator := 90579778584895802870260039680 }, { target := 168, numerator := 2789857180414790728404009222144 }, { target := 169, numerator := 1576088147377186969942524690432 }, { target := 170, numerator := 108695734301874963444312047616 }, { target := 283, numerator := 108687513413533108395659231232 }, { target := 284, numerator := 2898333691027549557217579499520 }, { target := 285, numerator := 2771531592045094264089310396416 }, { target := 286, numerator := 90572927844610923663049359360 }, { target := 287, numerator := 2843989934320783003019749883904 }, { target := 288, numerator := 90572927844610923663049359360 }, { target := 289, numerator := 2771531592045094264089310396416 }, { target := 290, numerator := 1575968944496230071737058852864 }, { target := 291, numerator := 2843989934320783003019749883904 }, { target := 292, numerator := 44398849229428274779626795958272 }, { target := 293, numerator := 1739000214616529734330547699712 }, { target := 294, numerator := 2898333691027549557217579499520 }, { target := 295, numerator := 2771531592045094264089310396416 }, { target := 296, numerator := 90572927844610923663049359360 }, { target := 297, numerator := 1739000214616529734330547699712 }, { target := 298, numerator := 90572927844610923663049359360 }, { target := 299, numerator := 2789646177614016448821920268288 }, { target := 300, numerator := 1575968944496230071737058852864 }, { target := 301, numerator := 108687513413533108395659231232 }, { target := 660, numerator := 2901175440175622946419638272 }, { target := 661, numerator := 77364678404683278571190353920 }, { target := 662, numerator := 73979973724478385133700775936 }, { target := 663, numerator := 2417646200146352455349698560 }, { target := 664, numerator := 75914090684595467097980534784 }, { target := 665, numerator := 2417646200146352455349698560 }, { target := 666, numerator := 73979973724478385133700775936 }, { target := 667, numerator := 42067043882546532723084754944 }, { target := 668, numerator := 75914090684595467097980534784 }, { target := 669, numerator := 1185130167311741973612422234112 }, { target := 670, numerator := 46418807042809967142714212352 }, { target := 671, numerator := 77364678404683278571190353920 }, { target := 672, numerator := 73979973724478385133700775936 }, { target := 673, numerator := 2417646200146352455349698560 }, { target := 674, numerator := 46418807042809967142714212352 }, { target := 675, numerator := 2417646200146352455349698560 }, { target := 676, numerator := 74463502964507655624770715648 }, { target := 677, numerator := 42067043882546532723084754944 }, { target := 678, numerator := 2901175440175622946419638272 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 7253554917687775048237056000 }, { target := 5, numerator := 145361240550463011966670602240 }, { target := 6, numerator := 244009587431016752622694563840 }, { target := 7, numerator := 234144752742961378557092167680 }, { target := 8, numerator := 7253554917687775048237056000 }, { target := 9, numerator := 234144752742961378557092167680 }, { target := 10, numerator := 156386644025348430039990927360 }, { target := 11, numerator := 7543697114395286050166538240 }, { target := 12, numerator := 145361240550463011966670602240 }, { target := 13, numerator := 6963412720980264046307573760 }, { target := 14, numerator := 142556812670532111192345804800 }, { target := 15, numerator := 146629864461118742940698542080 }, { target := 16, numerator := 142556812670532111192345804800 }, { target := 17, numerator := 126264605508185584198934855680 }, { target := 18, numerator := 5909998148141202666859821793280 }, { target := 19, numerator := 1608855457281719540599331225600 }, { target := 20, numerator := 146629864461118742940698542080 }, { target := 21, numerator := 5909998148141202666859821793280 }, { target := 22, numerator := 142556812670532111192345804800 }, { target := 23, numerator := 142556812670532111192345804800 }, { target := 24, numerator := 122191553717598952450582118400 }, { target := 25, numerator := 142556812670532111192345804800 }, { target := 26, numerator := 1608855457281719540599331225600 }, { target := 27, numerator := 122191553717598952450582118400 }, { target := 28, numerator := 142556812670532111192345804800 }, { target := 29, numerator := 126264605508185584198934855680 }, { target := 136, numerator := 489372611736851812099072983040 }, { target := 137, numerator := 503354686357904721016189353984 }, { target := 138, numerator := 489372611736851812099072983040 }, { target := 139, numerator := 433444313252640176430607499264 }, { target := 140, numerator := 20287990275147770838735854239744 }, { target := 141, numerator := 5522919475315899022260966522880 }, { target := 142, numerator := 503354686357904721016189353984 }, { target := 143, numerator := 20287990275147770838735854239744 }, { target := 144, numerator := 489372611736851812099072983040 }, { target := 145, numerator := 489372611736851812099072983040 }, { target := 146, numerator := 419462238631587267513491128320 }, { target := 147, numerator := 489372611736851812099072983040 }, { target := 148, numerator := 5522919475315899022260966522880 }, { target := 149, numerator := 419462238631587267513491128320 }, { target := 150, numerator := 489372611736851812099072983040 }, { target := 151, numerator := 433444313252640176430607499264 }, { target := 267, numerator := 142556812670532111192345804800 }, { target := 268, numerator := 146629864461118742940698542080 }, { target := 269, numerator := 142556812670532111192345804800 }, { target := 270, numerator := 126264605508185584198934855680 }, { target := 271, numerator := 5909998148141202666859821793280 }, { target := 272, numerator := 1608855457281719540599331225600 }, { target := 273, numerator := 146629864461118742940698542080 }, { target := 274, numerator := 5909998148141202666859821793280 }, { target := 275, numerator := 142556812670532111192345804800 }, { target := 276, numerator := 142556812670532111192345804800 }, { target := 277, numerator := 122191553717598952450582118400 }, { target := 278, numerator := 142556812670532111192345804800 }, { target := 279, numerator := 1608855457281719540599331225600 }, { target := 280, numerator := 122191553717598952450582118400 }, { target := 281, numerator := 142556812670532111192345804800 }, { target := 282, numerator := 126264605508185584198934855680 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left2.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20696810031802451470969733120 }, { target := 1, numerator := 18917271225329717325802242048 }, { target := 2, numerator := 20696810031802451470969733120 }, { target := 3, numerator := 18917271225329717325802242048 }, { target := 126, numerator := 7253554917687775048237056000 }, { target := 127, numerator := 145361240550463011966670602240 }, { target := 128, numerator := 244009587431016752622694563840 }, { target := 129, numerator := 234144752742961378557092167680 }, { target := 130, numerator := 7253554917687775048237056000 }, { target := 131, numerator := 234144752742961378557092167680 }, { target := 132, numerator := 156386644025348430039990927360 }, { target := 133, numerator := 7543697114395286050166538240 }, { target := 134, numerator := 145361240550463011966670602240 }, { target := 135, numerator := 6963412720980264046307573760 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent2
