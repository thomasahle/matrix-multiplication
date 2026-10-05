import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 4; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent3

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
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 198731348698603279527968768 }, { target := 1, numerator := 39415349908433565517244006400 }, { target := 6, numerator := 39415349908433565517244006400 }, { target := 14, numerator := 198731348698603279527968768 }, { target := 16, numerator := 46895105258313592885739520 }, { target := 17, numerator := 7685204578495161971402342400 }, { target := 19, numerator := 79122156759141635500435046400 }, { target := 27, numerator := 7685204578495161971402342400 }, { target := 34, numerator := 46895105258313592885739520 }, { target := 35, numerator := 158594812262561594864566272 }, { target := 37, numerator := 6340591168748935944157003776 }, { target := 40, numerator := 6340589619222433752554668032 }, { target := 47, numerator := 158594812262561594864566272 }, { target := 51, numerator := 51306505752960679333068800 }, { target := 52, numerator := 8408148158476301952352256000 }, { target := 54, numerator := 86565140830553732091478016000 }, { target := 62, numerator := 8408148158476301952352256000 }, { target := 69, numerator := 51306505752960679333068800 }, { target := 70, numerator := 3310666705980973292797820928 }, { target := 72, numerator := 132359840647634037834277453824 }, { target := 75, numerator := 132359808301268304584578695168 }, { target := 82, numerator := 3310666705980973292797820928 }, { target := 96, numerator := 171811046617775061103280128 }, { target := 98, numerator := 6868973766144680606170087424 }, { target := 101, numerator := 6868972087490969898600890368 }, { target := 108, numerator := 171811046617775061103280128 }, { target := 126, numerator := 46895105258313592885739520 }, { target := 127, numerator := 7685204578495161971402342400 }, { target := 129, numerator := 79122156759141635500435046400 }, { target := 137, numerator := 7685204578495161971402342400 }, { target := 144, numerator := 46895105258313592885739520 }, { target := 145, numerator := 3561775158730029151333384192 }, { target := 147, numerator := 142399109998153186412526043136 }, { target := 150, numerator := 142399075198370491359456919552 }, { target := 157, numerator := 3561775158730029151333384192 }, { target := 171, numerator := 5332750562328633627321040896 }, { target := 173, numerator := 213202378049182971122279251968 }, { target := 176, numerator := 213202325946354334929650712576 }, { target := 183, numerator := 5332750562328633627321040896 }, { target := 216, numerator := 165202929440168327983923200 }, { target := 218, numerator := 6604782467446808275163545600 }, { target := 221, numerator := 6604780853356701825577779200 }, { target := 228, numerator := 165202929440168327983923200 }, { target := 266, numerator := 51306505752960679333068800 }, { target := 267, numerator := 8408148158476301952352256000 }, { target := 269, numerator := 86565140830553732091478016000 }, { target := 277, numerator := 8408148158476301952352256000 }, { target := 284, numerator := 51306505752960679333068800 }, { target := 285, numerator := 5332750562328633627321040896 }, { target := 287, numerator := 213202378049182971122279251968 }, { target := 290, numerator := 213202325946354334929650712576 }, { target := 297, numerator := 5332750562328633627321040896 }, { target := 311, numerator := 5557426546367262553379176448 }, { target := 313, numerator := 222184882204910630376501673984 }, { target := 316, numerator := 222184827906919449412436492288 }, { target := 323, numerator := 5557426546367262553379176448 }, { target := 356, numerator := 3310666705980973292797820928 }, { target := 358, numerator := 132359840647634037834277453824 }, { target := 361, numerator := 132359808301268304584578695168 }, { target := 368, numerator := 3310666705980973292797820928 }, { target := 427, numerator := 165202929440168327983923200 }, { target := 429, numerator := 6604782467446808275163545600 }, { target := 432, numerator := 6604780853356701825577779200 }, { target := 439, numerator := 165202929440168327983923200 }]

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
    Slot4.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 5525772380870320750262747136 }, { target := 89, numerator := 20129066260740943321021546496 }, { target := 91, numerator := 5525776097889251602737397760 }, { target := 112, numerator := 6238775268724555685780520960 }, { target := 115, numerator := 22726365133094613426959810560 }, { target := 117, numerator := 6238779465358832454703513600 }, { target := 122, numerator := 522255954073519803473068032 }, { target := 124, numerator := 522255954073519803473068032 }, { target := 161, numerator := 5347521658906762016383303680 }, { target := 164, numerator := 19479741542652525794536980480 }, { target := 166, numerator := 5347525256021856389745868800 }, { target := 187, numerator := 70409035175605699882380165120 }, { target := 190, numerator := 256483263644924922961403576320 }, { target := 192, numerator := 70409082537621109131653939200 }, { target := 197, numerator := 7572711334066037150359486464 }, { target := 199, numerator := 7572711334066037150359486464 }, { target := 201, numerator := 6238775268724555685780520960 }, { target := 204, numerator := 22726365133094613426959810560 }, { target := 206, numerator := 6238779465358832454703513600 }, { target := 211, numerator := 13404569487887008289142079488 }, { target := 213, numerator := 13404569487887008289142079488 }, { target := 232, numerator := 5347521658906762016383303680 }, { target := 235, numerator := 19479741542652525794536980480 }, { target := 237, numerator := 5347525256021856389745868800 }, { target := 242, numerator := 435213295061266502894223360 }, { target := 244, numerator := 435213295061266502894223360 }, { target := 246, numerator := 6238775268724555685780520960 }, { target := 249, numerator := 22726365133094613426959810560 }, { target := 251, numerator := 6238779465358832454703513600 }, { target := 256, numerator := 8356095265176316855569088512 }, { target := 258, numerator := 8356095265176316855569088512 }, { target := 261, numerator := 435213295061266502894223360 }, { target := 263, numerator := 435213295061266502894223360 }, { target := 301, numerator := 6238775268724555685780520960 }, { target := 304, numerator := 22726365133094613426959810560 }, { target := 306, numerator := 6238779465358832454703513600 }, { target := 327, numerator := 258641797569123722859072454656 }, { target := 330, numerator := 942170165946293830929105289216 }, { target := 332, numerator := 258641971549590454050708520960 }, { target := 337, numerator := 13317526828874754988563234816 }, { target := 339, numerator := 13317526828874754988563234816 }, { target := 341, numerator := 6417025990688114419659964416 }, { target := 344, numerator := 23375689851183030953444376576 }, { target := 346, numerator := 6417030307226227667695042560 }, { target := 351, numerator := 13926825441960528092615147520 }, { target := 353, numerator := 13926825441960528092615147520 }, { target := 372, numerator := 70409035175605699882380165120 }, { target := 375, numerator := 256483263644924922961403576320 }, { target := 377, numerator := 70409082537621109131653939200 }, { target := 386, numerator := 258641797569123722859072454656 }, { target := 389, numerator := 942170165946293830929105289216 }, { target := 391, numerator := 258641971549590454050708520960 }, { target := 406, numerator := 5525772380870320750262747136 }, { target := 409, numerator := 20129066260740943321021546496 }, { target := 411, numerator := 5525776097889251602737397760 }, { target := 443, numerator := 6238775268724555685780520960 }, { target := 446, numerator := 22726365133094613426959810560 }, { target := 448, numerator := 6238779465358832454703513600 }, { target := 457, numerator := 6417025990688114419659964416 }, { target := 460, numerator := 23375689851183030953444376576 }, { target := 462, numerator := 6417030307226227667695042560 }, { target := 477, numerator := 6238775268724555685780520960 }, { target := 480, numerator := 22726365133094613426959810560 }, { target := 482, numerator := 6238779465358832454703513600 }]

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
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 580284393415022003858964480 }, { target := 17, numerator := 8414123704517819055954984960 }, { target := 18, numerator := 14893966097652231432380088320 }, { target := 19, numerator := 483570327845851669882470400 }, { target := 20, numerator := 9284550294640352061743431680 }, { target := 21, numerator := 483570327845851669882470400 }, { target := 22, numerator := 14797252032083061098403594240 }, { target := 23, numerator := 15474250491067253436239052800 }, { target := 24, numerator := 9284550294640352061743431680 }, { target := 25, numerator := 237046174710036488576386990080 }, { target := 26, numerator := 15184108294359742434309570560 }, { target := 27, numerator := 8414123704517819055954984960 }, { target := 28, numerator := 14797252032083061098403594240 }, { target := 29, numerator := 483570327845851669882470400 }, { target := 30, numerator := 15184108294359742434309570560 }, { target := 31, numerator := 483570327845851669882470400 }, { target := 32, numerator := 14797252032083061098403594240 }, { target := 33, numerator := 15474250491067253436239052800 }, { target := 34, numerator := 580284393415022003858964480 }, { target := 215, numerator := 909112216350201139379044352 }, { target := 260, numerator := 676998458984192337835458560 }, { target := 265, numerator := 715684085211860471426056192 }, { target := 355, numerator := 928455029464035206174343168 }, { target := 382, numerator := 8356095265176316855569088512 }, { target := 384, numerator := 8356095265176316855569088512 }, { target := 396, numerator := 213341557239032839718748291072 }, { target := 398, numerator := 213341557239032839718748291072 }, { target := 400, numerator := 12437428832195304949377138688 }, { target := 401, numerator := 13665697464923768190878613504 }, { target := 403, numerator := 13665697464923768190878613504 }, { target := 405, numerator := 22495691651389019682932523008 }, { target := 416, numerator := 7572711334066037150359486464 }, { target := 418, numerator := 7572711334066037150359486464 }, { target := 420, numerator := 676998458984192337835458560 }, { target := 421, numerator := 13317526828874754988563234816 }, { target := 423, numerator := 13317526828874754988563234816 }, { target := 425, numerator := 12437428832195304949377138688 }, { target := 426, numerator := 735026898325694538221355008 }, { target := 453, numerator := 435213295061266502894223360 }, { target := 455, numerator := 435213295061266502894223360 }, { target := 467, numerator := 13665697464923768190878613504 }, { target := 469, numerator := 13665697464923768190878613504 }, { target := 471, numerator := 735026898325694538221355008 }, { target := 472, numerator := 435213295061266502894223360 }, { target := 474, numerator := 435213295061266502894223360 }, { target := 476, numerator := 715684085211860471426056192 }, { target := 487, numerator := 13317526828874754988563234816 }, { target := 489, numerator := 13317526828874754988563234816 }, { target := 491, numerator := 715684085211860471426056192 }, { target := 492, numerator := 13926825441960528092615147520 }, { target := 494, numerator := 13926825441960528092615147520 }, { target := 496, numerator := 22495691651389019682932523008 }, { target := 497, numerator := 715684085211860471426056192 }, { target := 498, numerator := 522255954073519803473068032 }, { target := 500, numerator := 522255954073519803473068032 }, { target := 502, numerator := 909112216350201139379044352 }, { target := 503, numerator := 928455029464035206174343168 }]

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
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 5525772380870320750262747136 }, { target := 36, numerator := 6238775268724555685780520960 }, { target := 37, numerator := 5347521658906762016383303680 }, { target := 38, numerator := 70409035175605699882380165120 }, { target := 39, numerator := 6238775268724555685780520960 }, { target := 40, numerator := 5347521658906762016383303680 }, { target := 41, numerator := 6238775268724555685780520960 }, { target := 42, numerator := 6238775268724555685780520960 }, { target := 43, numerator := 258641797569123722859072454656 }, { target := 44, numerator := 6417025990688114419659964416 }, { target := 45, numerator := 70409035175605699882380165120 }, { target := 46, numerator := 258641797569123722859072454656 }, { target := 47, numerator := 5525772380870320750262747136 }, { target := 48, numerator := 6238775268724555685780520960 }, { target := 49, numerator := 6417025990688114419659964416 }, { target := 50, numerator := 6238775268724555685780520960 }, { target := 126, numerator := 580284393415022003858964480 }, { target := 127, numerator := 8414123704517819055954984960 }, { target := 128, numerator := 14893966097652231432380088320 }, { target := 129, numerator := 483570327845851669882470400 }, { target := 130, numerator := 9284550294640352061743431680 }, { target := 131, numerator := 483570327845851669882470400 }, { target := 132, numerator := 14797252032083061098403594240 }, { target := 133, numerator := 15474250491067253436239052800 }, { target := 134, numerator := 9284550294640352061743431680 }, { target := 135, numerator := 237046174710036488576386990080 }, { target := 136, numerator := 15184108294359742434309570560 }, { target := 137, numerator := 8414123704517819055954984960 }, { target := 138, numerator := 14797252032083061098403594240 }, { target := 139, numerator := 483570327845851669882470400 }, { target := 140, numerator := 15184108294359742434309570560 }, { target := 141, numerator := 483570327845851669882470400 }, { target := 142, numerator := 14797252032083061098403594240 }, { target := 143, numerator := 15474250491067253436239052800 }, { target := 144, numerator := 580284393415022003858964480 }, { target := 145, numerator := 20129066260740943321021546496 }, { target := 146, numerator := 22726365133094613426959810560 }, { target := 147, numerator := 19479741542652525794536980480 }, { target := 148, numerator := 256483263644924922961403576320 }, { target := 149, numerator := 22726365133094613426959810560 }, { target := 150, numerator := 19479741542652525794536980480 }, { target := 151, numerator := 22726365133094613426959810560 }, { target := 152, numerator := 22726365133094613426959810560 }, { target := 153, numerator := 942170165946293830929105289216 }, { target := 154, numerator := 23375689851183030953444376576 }, { target := 155, numerator := 256483263644924922961403576320 }, { target := 156, numerator := 942170165946293830929105289216 }, { target := 157, numerator := 20129066260740943321021546496 }, { target := 158, numerator := 22726365133094613426959810560 }, { target := 159, numerator := 23375689851183030953444376576 }, { target := 160, numerator := 22726365133094613426959810560 }]

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
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 164258912700510223252586496 }, { target := 87, numerator := 3428904802623150910397743104 }, { target := 88, numerator := 177947155425552741856968704 }, { target := 89, numerator := 3688981414398958763881005056 }, { target := 90, numerator := 5523205939554656256868220928 }, { target := 91, numerator := 171103034063031482554777600 }, { target := 92, numerator := 5523205939554656256868220928 }, { target := 93, numerator := 5755906065880379073142718464 }, { target := 94, numerator := 3428904802623150910397743104 }, { target := 95, numerator := 171103034063031482554777600 }, { target := 122, numerator := 46895105258313592885739520 }, { target := 123, numerator := 51306505752960679333068800 }, { target := 124, numerator := 46895105258313592885739520 }, { target := 125, numerator := 51306505752960679333068800 }, { target := 161, numerator := 6567040853347112227876896768 }, { target := 162, numerator := 137086977813620967756930220032 }, { target := 163, numerator := 7114294257792704913533304832 }, { target := 164, numerator := 147484792498087228784401973248 }, { target := 165, numerator := 220816748693796648662360653824 }, { target := 166, numerator := 6840667555569908570705100800 }, { target := 167, numerator := 220816748693796648662360653824 }, { target := 168, numerator := 230120056569371724318519590912 }, { target := 169, numerator := 137086977813620967756930220032 }, { target := 170, numerator := 6840667555569908570705100800 }, { target := 197, numerator := 7685204578495161971402342400 }, { target := 198, numerator := 8408148158476301952352256000 }, { target := 199, numerator := 7685204578495161971402342400 }, { target := 200, numerator := 8408148158476301952352256000 }, { target := 216, numerator := 5525776097889251602737397760 }, { target := 217, numerator := 6238779465358832454703513600 }, { target := 218, numerator := 5347525256021856389745868800 }, { target := 219, numerator := 70409082537621109131653939200 }, { target := 220, numerator := 6238779465358832454703513600 }, { target := 221, numerator := 5347525256021856389745868800 }, { target := 222, numerator := 6238779465358832454703513600 }, { target := 223, numerator := 6238779465358832454703513600 }, { target := 224, numerator := 258641971549590454050708520960 }, { target := 225, numerator := 6417030307226227667695042560 }, { target := 226, numerator := 70409082537621109131653939200 }, { target := 227, numerator := 258641971549590454050708520960 }, { target := 228, numerator := 5525776097889251602737397760 }, { target := 229, numerator := 6238779465358832454703513600 }, { target := 230, numerator := 6417030307226227667695042560 }, { target := 231, numerator := 6238779465358832454703513600 }, { target := 232, numerator := 6567039248480377815145906176 }, { target := 233, numerator := 137086944312027886891170791424 }, { target := 234, numerator := 7114292519187075966408065024 }, { target := 235, numerator := 147484756455455151765151809536 }, { target := 236, numerator := 220816694730152704034281095168 }, { target := 237, numerator := 6840665883833726890776985600 }, { target := 238, numerator := 220816694730152704034281095168 }, { target := 239, numerator := 230120000332166572605737795584 }, { target := 240, numerator := 137086944312027886891170791424 }, { target := 241, numerator := 6840665883833726890776985600 }, { target := 406, numerator := 164258912700510223252586496 }, { target := 407, numerator := 3428904802623150910397743104 }, { target := 408, numerator := 177947155425552741856968704 }, { target := 409, numerator := 3688981414398958763881005056 }, { target := 410, numerator := 5523205939554656256868220928 }, { target := 411, numerator := 171103034063031482554777600 }, { target := 412, numerator := 5523205939554656256868220928 }, { target := 413, numerator := 5755906065880379073142718464 }, { target := 414, numerator := 3428904802623150910397743104 }, { target := 415, numerator := 171103034063031482554777600 }]

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
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 215, numerator := 198731348698603279527968768 }, { target := 242, numerator := 79122156759141635500435046400 }, { target := 243, numerator := 86565140830553732091478016000 }, { target := 244, numerator := 79122156759141635500435046400 }, { target := 245, numerator := 86565140830553732091478016000 }, { target := 260, numerator := 39415349908433565517244006400 }, { target := 416, numerator := 7685204578495161971402342400 }, { target := 417, numerator := 8408148158476301952352256000 }, { target := 418, numerator := 7685204578495161971402342400 }, { target := 419, numerator := 8408148158476301952352256000 }, { target := 420, numerator := 39415349908433565517244006400 }, { target := 498, numerator := 46895105258313592885739520 }, { target := 499, numerator := 51306505752960679333068800 }, { target := 500, numerator := 46895105258313592885739520 }, { target := 501, numerator := 51306505752960679333068800 }, { target := 502, numerator := 198731348698603279527968768 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0.Parent3
