import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent2

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
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 221686772171832624911745024 }, { target := 11, numerator := 166265079128874468683808768 }, { target := 12, numerator := 175502027969367494721798144 }, { target := 13, numerator := 226305246592079137930739712 }, { target := 14, numerator := 3029719219681712540460515328 }, { target := 15, numerator := 5297390160022750432786907136 }, { target := 16, numerator := 161646604708627955664814080 }, { target := 17, numerator := 3029719219681712540460515328 }, { target := 18, numerator := 170883553549120981702803456 }, { target := 19, numerator := 175502027969367494721798144 }, { target := 20, numerator := 175502027969367494721798144 }, { target := 21, numerator := 170883553549120981702803456 }, { target := 22, numerator := 5297390160022750432786907136 }, { target := 23, numerator := 170883553549120981702803456 }, { target := 24, numerator := 221686772171832624911745024 }, { target := 25, numerator := 226305246592079137930739712 }, { target := 45, numerator := 242540742560184978175426560 }, { target := 46, numerator := 181905556920138733631569920 }, { target := 47, numerator := 192011421193479774388879360 }, { target := 48, numerator := 247593674696855498554081280 }, { target := 49, numerator := 3314723481655861368397496320 }, { target := 50, numerator := 5795713160761086874316963840 }, { target := 51, numerator := 176852624783468213252915200 }, { target := 52, numerator := 3314723481655861368397496320 }, { target := 53, numerator := 186958489056809254010224640 }, { target := 54, numerator := 192011421193479774388879360 }, { target := 55, numerator := 192011421193479774388879360 }, { target := 56, numerator := 186958489056809254010224640 }, { target := 57, numerator := 5795713160761086874316963840 }, { target := 58, numerator := 186958489056809254010224640 }, { target := 59, numerator := 242540742560184978175426560 }, { target := 60, numerator := 247593674696855498554081280 }, { target := 141, numerator := 221686772171832624911745024 }, { target := 142, numerator := 166265079128874468683808768 }, { target := 143, numerator := 175502027969367494721798144 }, { target := 144, numerator := 226305246592079137930739712 }, { target := 145, numerator := 3029719219681712540460515328 }, { target := 146, numerator := 5297390160022750432786907136 }, { target := 147, numerator := 161646604708627955664814080 }, { target := 148, numerator := 3029719219681712540460515328 }, { target := 149, numerator := 170883553549120981702803456 }, { target := 150, numerator := 175502027969367494721798144 }, { target := 151, numerator := 175502027969367494721798144 }, { target := 152, numerator := 170883553549120981702803456 }, { target := 153, numerator := 5297390160022750432786907136 }, { target := 154, numerator := 170883553549120981702803456 }, { target := 155, numerator := 221686772171832624911745024 }, { target := 156, numerator := 226305246592079137930739712 }, { target := 357, numerator := 242540742560184978175426560 }, { target := 358, numerator := 181905556920138733631569920 }, { target := 359, numerator := 192011421193479774388879360 }, { target := 360, numerator := 247593674696855498554081280 }, { target := 361, numerator := 3314723481655861368397496320 }, { target := 362, numerator := 5795713160761086874316963840 }, { target := 363, numerator := 176852624783468213252915200 }, { target := 364, numerator := 3314723481655861368397496320 }, { target := 365, numerator := 186958489056809254010224640 }, { target := 366, numerator := 192011421193479774388879360 }, { target := 367, numerator := 192011421193479774388879360 }, { target := 368, numerator := 186958489056809254010224640 }, { target := 369, numerator := 5795713160761086874316963840 }, { target := 370, numerator := 186958489056809254010224640 }, { target := 371, numerator := 242540742560184978175426560 }, { target := 372, numerator := 247593674696855498554081280 }]

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
    Slot2.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 9898818017857724749971456 }, { target := 27, numerator := 1169976736988100321299398656 }, { target := 29, numerator := 11102846014783227191063740416 }, { target := 37, numerator := 1169977539421467527664893952 }, { target := 44, numerator := 9898818017857724749971456 }, { target := 61, numerator := 206637826122780004155654144 }, { target := 62, numerator := 24423264384626594207124946944 }, { target := 64, numerator := 231771910558599867613455581184 }, { target := 72, numerator := 24423281135423134640004661248 }, { target := 79, numerator := 206637826122780004155654144 }, { target := 80, numerator := 8717648518294559356637675520 }, { target := 82, numerator := 341164826491292957870124957696 }, { target := 85, numerator := 341164826491292957870124957696 }, { target := 92, numerator := 8717648518294559356637675520 }, { target := 96, numerator := 10723719519345868479135744 }, { target := 97, numerator := 1267474798403775348074348544 }, { target := 99, numerator := 12028083182681829456985718784 }, { target := 107, numerator := 1267475667706589821636968448 }, { target := 114, numerator := 10723719519345868479135744 }, { target := 115, numerator := 9842506391622889596203827200 }, { target := 117, numerator := 385186094425653339530786242560 }, { target := 120, numerator := 385186094425653339530786242560 }, { target := 127, numerator := 9842506391622889596203827200 }, { target := 157, numerator := 222310954651054735009775616 }, { target := 158, numerator := 26275727551524419715848994816 }, { target := 160, numerator := 249351416748673310665973170176 }, { target := 168, numerator := 26275745572840458225474076672 }, { target := 175, numerator := 222310954651054735009775616 }, { target := 176, numerator := 8436434049962476796746137600 }, { target := 178, numerator := 330159509507702862454959636480 }, { target := 181, numerator := 330159509507702862454959636480 }, { target := 188, numerator := 8436434049962476796746137600 }, { target := 192, numerator := 332847755850465994717790208 }, { target := 193, numerator := 39340467781224873303692279808 }, { target := 195, numerator := 373333197247086014299518271488 }, { target := 203, numerator := 39340494763046845617732059136 }, { target := 210, numerator := 332847755850465994717790208 }, { target := 267, numerator := 10311268768601796614553600 }, { target := 268, numerator := 1218725767695937834686873600 }, { target := 270, numerator := 11565464598732528324024729600 }, { target := 278, numerator := 1218726603564028674650931200 }, { target := 285, numerator := 10311268768601796614553600 }, { target := 373, numerator := 332847755850465994717790208 }, { target := 374, numerator := 39340467781224873303692279808 }, { target := 376, numerator := 373333197247086014299518271488 }, { target := 384, numerator := 39340494763046845617732059136 }, { target := 391, numerator := 332847755850465994717790208 }, { target := 408, numerator := 346871081375764438113583104 }, { target := 409, numerator := 40997934825291348758866427904 }, { target := 411, numerator := 389062229101362252820191903744 }, { target := 419, numerator := 40997962943893924615257325568 }, { target := 426, numerator := 346871081375764438113583104 }, { target := 483, numerator := 206637826122780004155654144 }, { target := 484, numerator := 24423264384626594207124946944 }, { target := 486, numerator := 231771910558599867613455581184 }, { target := 494, numerator := 24423281135423134640004661248 }, { target := 501, numerator := 206637826122780004155654144 }, { target := 623, numerator := 10311268768601796614553600 }, { target := 624, numerator := 1218725767695937834686873600 }, { target := 626, numerator := 11565464598732528324024729600 }, { target := 634, numerator := 1218726603564028674650931200 }, { target := 641, numerator := 10311268768601796614553600 }]

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
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 38830901605265761351136968704 }, { target := 134, numerator := 144247122694352416717972439040 }, { target := 136, numerator := 38822727742286236206558609408 }, { target := 211, numerator := 111079714991172611157157478400 }, { target := 213, numerator := 4347100208518087688990301880320 }, { target := 216, numerator := 4347100208518087688990301880320 }, { target := 223, numerator := 111079714991172611157157478400 }, { target := 227, numerator := 563048073276353539591486046208 }, { target := 230, numerator := 2091583279068110042410600366080 }, { target := 232, numerator := 562929552263150424995099836416 }, { target := 237, numerator := 9842506391622889596203827200 }, { target := 239, numerator := 385186094425653339530786242560 }, { target := 242, numerator := 385186094425653339530786242560 }, { target := 249, numerator := 9842506391622889596203827200 }, { target := 253, numerator := 996659807868487874679182196736 }, { target := 256, numerator := 3702342815821712029094625935360 }, { target := 258, numerator := 996450012052013395968337641472 }, { target := 286, numerator := 8436434049962476796746137600 }, { target := 288, numerator := 330159509507702862454959636480 }, { target := 291, numerator := 330159509507702862454959636480 }, { target := 298, numerator := 8436434049962476796746137600 }, { target := 302, numerator := 32359084671054801125947473920 }, { target := 305, numerator := 120205935578627013931643699200 }, { target := 307, numerator := 32352273118571863505465507840 }, { target := 312, numerator := 9842506391622889596203827200 }, { target := 314, numerator := 385186094425653339530786242560 }, { target := 317, numerator := 385186094425653339530786242560 }, { target := 324, numerator := 9842506391622889596203827200 }, { target := 392, numerator := 9842506391622889596203827200 }, { target := 394, numerator := 385186094425653339530786242560 }, { target := 397, numerator := 385186094425653339530786242560 }, { target := 404, numerator := 9842506391622889596203827200 }, { target := 427, numerator := 408042193549851794402621521920 }, { target := 429, numerator := 15968714943189228447404881084416 }, { target := 432, numerator := 15968714943189228447404881084416 }, { target := 439, numerator := 408042193549851794402621521920 }, { target := 453, numerator := 10123720859954972156095365120 }, { target := 455, numerator := 396191411409243434945951563776 }, { target := 458, numerator := 396191411409243434945951563776 }, { target := 465, numerator := 10123720859954972156095365120 }, { target := 502, numerator := 111079714991172611157157478400 }, { target := 504, numerator := 4347100208518087688990301880320 }, { target := 507, numerator := 4347100208518087688990301880320 }, { target := 514, numerator := 111079714991172611157157478400 }, { target := 528, numerator := 408042193549851794402621521920 }, { target := 530, numerator := 15968714943189228447404881084416 }, { target := 533, numerator := 15968714943189228447404881084416 }, { target := 540, numerator := 408042193549851794402621521920 }, { target := 573, numerator := 8717648518294559356637675520 }, { target := 575, numerator := 341164826491292957870124957696 }, { target := 578, numerator := 341164826491292957870124957696 }, { target := 585, numerator := 8717648518294559356637675520 }, { target := 642, numerator := 9842506391622889596203827200 }, { target := 644, numerator := 385186094425653339530786242560 }, { target := 647, numerator := 385186094425653339530786242560 }, { target := 654, numerator := 9842506391622889596203827200 }, { target := 668, numerator := 10123720859954972156095365120 }, { target := 670, numerator := 396191411409243434945951563776 }, { target := 673, numerator := 396191411409243434945951563776 }, { target := 680, numerator := 10123720859954972156095365120 }, { target := 713, numerator := 9842506391622889596203827200 }, { target := 715, numerator := 385186094425653339530786242560 }, { target := 718, numerator := 385186094425653339530786242560 }, { target := 725, numerator := 9842506391622889596203827200 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 95456771337435869165220003840 }, { target := 265, numerator := 95456794096106370104379310080 }, { target := 328, numerator := 621294425684252181618191499264 }, { target := 331, numerator := 2307953963109638667487559024640 }, { target := 333, numerator := 621163643876579779304937750528 }, { target := 338, numerator := 71084829719367136612397875200 }, { target := 340, numerator := 71084846667313254333048422400 }, { target := 342, numerator := 32359084671054801125947473920 }, { target := 345, numerator := 120205935578627013931643699200 }, { target := 347, numerator := 32352273118571863505465507840 }, { target := 352, numerator := 75146819989045258704534896640 }, { target := 354, numerator := 75146837905445440294936903680 }, { target := 443, numerator := 990187990934276914453992701952 }, { target := 446, numerator := 3678301628705986626308297195520 }, { target := 448, numerator := 989979557428299023267244539904 }, { target := 469, numerator := 1035490709473753636030319165440 }, { target := 472, numerator := 3846589938516064445812598374400 }, { target := 474, numerator := 1035272739794299632174896250880 }, { target := 479, numerator := 97487766472274930211288514560 }, { target := 481, numerator := 97487789715172463085323550720 }, { target := 518, numerator := 621294425684252181618191499264 }, { target := 521, numerator := 2307953963109638667487559024640 }, { target := 523, numerator := 621163643876579779304937750528 }, { target := 544, numerator := 15862423305751063511939451715584 }, { target := 547, numerator := 58924949620642962229291741347840 }, { target := 549, numerator := 15859084282723927490379191943168 }, { target := 554, numerator := 1305929871701516252622052392960 }, { target := 556, numerator := 1305930183059497786747146731520 }, { target := 558, numerator := 1016075258671120755354750681088 }, { target := 561, numerator := 3774466377168888237453612154880 }, { target := 563, numerator := 1015861375923156514071616946176 }, { target := 568, numerator := 2362047341817827996577677967360 }, { target := 570, numerator := 2362047904973866136838151864320 }, { target := 589, numerator := 563048073276353539591486046208 }, { target := 592, numerator := 2091583279068110042410600366080 }, { target := 594, numerator := 562929552263150424995099836416 }, { target := 599, numerator := 71084829719367136612397875200 }, { target := 601, numerator := 71084846667313254333048422400 }, { target := 603, numerator := 990187990934276914453992701952 }, { target := 606, numerator := 3678301628705986626308297195520 }, { target := 608, numerator := 989979557428299023267244539904 }, { target := 613, numerator := 1305929871701516252622052392960 }, { target := 615, numerator := 1305930183059497786747146731520 }, { target := 618, numerator := 77177815123884319750603407360 }, { target := 620, numerator := 77177833524511533275881144320 }, { target := 658, numerator := 32359084671054801125947473920 }, { target := 661, numerator := 120205935578627013931643699200 }, { target := 663, numerator := 32352273118571863505465507840 }, { target := 684, numerator := 1016075258671120755354750681088 }, { target := 687, numerator := 3774466377168888237453612154880 }, { target := 689, numerator := 1015861375923156514071616946176 }, { target := 698, numerator := 32359084671054801125947473920 }, { target := 701, numerator := 120205935578627013931643699200 }, { target := 703, numerator := 32352273118571863505465507840 }, { target := 729, numerator := 990187990934276914453992701952 }, { target := 732, numerator := 3678301628705986626308297195520 }, { target := 734, numerator := 989979557428299023267244539904 }, { target := 743, numerator := 1035490709473753636030319165440 }, { target := 746, numerator := 3846589938516064445812598374400 }, { target := 748, numerator := 1035272739794299632174896250880 }, { target := 763, numerator := 38830901605265761351136968704 }, { target := 766, numerator := 144247122694352416717972439040 }, { target := 768, numerator := 38822727742286236206558609408 }]

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
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
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
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1010617122716242728424833024 }, { target := 11, numerator := 177252748534378516857049055232 }, { target := 16, numerator := 177252769785027689770452516864 }, { target := 24, numerator := 1010595872067069815021371392 }, { target := 26, numerator := 2358420947974879792532029440 }, { target := 27, numerator := 759697761382374264043921735680 }, { target := 29, numerator := 8079705166750837866168324194304 }, { target := 37, numerator := 759700051111449967810710601728 }, { target := 44, numerator := 2358420947974879792532029440 }, { target := 80, numerator := 79395781848372077802849042432 }, { target := 82, numerator := 3107241089178800864903359889408 }, { target := 85, numerator := 3107242228809360782973030367232 }, { target := 92, numerator := 79396921478931995872519520256 }, { target := 141, numerator := 1010617122716242728424833024 }, { target := 142, numerator := 177252748534378516857049055232 }, { target := 147, numerator := 177252769785027689770452516864 }, { target := 155, numerator := 1010595872067069815021371392 }, { target := 157, numerator := 8591163055657525461217443840 }, { target := 158, numerator := 2767397120797409791407795732480 }, { target := 160, numerator := 29432432148637094506612175929344 }, { target := 168, numerator := 2767405461732415284150961963008 }, { target := 175, numerator := 8591163055657525461217443840 }, { target := 176, numerator := 3174228627291254241588261421056 }, { target := 178, numerator := 124226922231249978401129091825664 }, { target := 181, numerator := 124226967793468318115980122259456 }, { target := 188, numerator := 3174274189509593956439291854848 }, { target := 267, numerator := 2358422534412884530062950400 }, { target := 268, numerator := 759698272407940673598966988800 }, { target := 270, numerator := 8079710601722637372185263472640 }, { target := 278, numerator := 759700562138556608438316564480 }, { target := 285, numerator := 2358422534412884530062950400 }, { target := 286, numerator := 3174227851566838157914241236992 }, { target := 288, numerator := 124226891872423307512360938242048 }, { target := 291, numerator := 124226937434630512640083248545792 }, { target := 298, numerator := 3174273413774043285636551540736 }, { target := 356, numerator := 1798881619586568211962789888 }, { target := 572, numerator := 44101613899541672293281300480 }, { target := 573, numerator := 79395781848372077802849042432 }, { target := 575, numerator := 3107241089178800864903359889408 }, { target := 578, numerator := 3107242228809360782973030367232 }, { target := 585, numerator := 79396921478931995872519520256 }, { target := 617, numerator := 32611982909924236616873803776 }, { target := 622, numerator := 36383831467121879641957072896 }, { target := 694, numerator := 77177815123884319750603407360 }, { target := 696, numerator := 77177833524511533275881144320 }, { target := 708, numerator := 75146819989045258704534896640 }, { target := 710, numerator := 75146837905445440294936903680 }, { target := 712, numerator := 1798881619586568211962789888 }, { target := 739, numerator := 75146819989045258704534896640 }, { target := 741, numerator := 75146837905445440294936903680 }, { target := 753, numerator := 2362047341817827996577677967360 }, { target := 755, numerator := 2362047904973866136838151864320 }, { target := 757, numerator := 36325803027780377441571176448 }, { target := 758, numerator := 75146819989045258704534896640 }, { target := 760, numerator := 75146837905445440294936903680 }, { target := 762, numerator := 36964115860536901645816037376 }, { target := 773, numerator := 95456771337435869165220003840 }, { target := 775, numerator := 95456794096106370104379310080 }, { target := 777, numerator := 1798881619586568211962789888 }, { target := 778, numerator := 97487766472274930211288514560 }, { target := 780, numerator := 97487789715172463085323550720 }, { target := 782, numerator := 44101613899541672293281300480 }, { target := 783, numerator := 1798881619586568211962789888 }]

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
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 10135295158963465112078254080 }, { target := 11, numerator := 2010182126432705264467574784000 }, { target := 16, numerator := 2010182126432705264467574784000 }, { target := 24, numerator := 10135295158963465112078254080 }, { target := 26, numerator := 21614363356290622541369704448 }, { target := 27, numerator := 3542177873618793583011965173760 }, { target := 29, numerator := 36468092699766197680625533583360 }, { target := 37, numerator := 3542177873618793583011965173760 }, { target := 44, numerator := 21614363356290622541369704448 }, { target := 80, numerator := 79708885189500194596853907456 }, { target := 82, numerator := 3186746440776704356904702312448 }, { target := 85, numerator := 3186745661993159679544116903936 }, { target := 92, numerator := 79708885189500194596853907456 }, { target := 131, numerator := 21635464264220616640824344576 }, { target := 134, numerator := 77550046430776039520906248192 }, { target := 136, numerator := 21641751493275208376291164160 }, { target := 141, numerator := 10135302408294069399774560256 }, { target := 142, numerator := 2010183564227518418291313868800 }, { target := 147, numerator := 2010183564227518418291313868800 }, { target := 155, numerator := 10135302408294069399774560256 }, { target := 157, numerator := 77474412445310393188473634816 }, { target := 158, numerator := 12696564086192512091704703057920 }, { target := 160, numerator := 130716043232113709871275305861120 }, { target := 168, numerator := 12696564086192512091704703057920 }, { target := 175, numerator := 77474412445310393188473634816 }, { target := 176, numerator := 3119494732181781120096365707264 }, { target := 178, numerator := 124716820604981587598524716941312 }, { target := 181, numerator := 124716790126432560658928719888384 }, { target := 188, numerator := 3119494732181781120096365707264 }, { target := 227, numerator := 3545635906036904998810545029120 }, { target := 230, numerator := 12708959039742325803476624343040 }, { target := 232, numerator := 3546666261790458409500488499200 }, { target := 263, numerator := 10135295158963465112078254080 }, { target := 265, numerator := 10135302408294069399774560256 }, { target := 267, numerator := 21620644453457319681515847680 }, { target := 268, numerator := 3543207224474017780362484121600 }, { target := 270, numerator := 36478690265373638292078696857600 }, { target := 278, numerator := 3543207224474017780362484121600 }, { target := 285, numerator := 21620644453457319681515847680 }, { target := 286, numerator := 3119495876306561356362579705856 }, { target := 288, numerator := 124716866346878021782143550619648 }, { target := 291, numerator := 124716835868317816345322466574336 }, { target := 298, numerator := 3119495876306561356362579705856 }, { target := 302, numerator := 36503694482421355049008832184320 }, { target := 305, numerator := 130843654078093645155887680061440 }, { target := 307, numerator := 36514302393846180080193319731200 }, { target := 338, numerator := 2010182126432705264467574784000 }, { target := 340, numerator := 2010183564227518418291313868800 }, { target := 573, numerator := 79710029314280430863067906048 }, { target := 575, numerator := 3186792182673138540523535990784 }, { target := 578, numerator := 3186791403878415365937863589888 }, { target := 585, numerator := 79710029314280430863067906048 }, { target := 589, numerator := 3545635906036904998810545029120 }, { target := 592, numerator := 12708959039742325803476624343040 }, { target := 594, numerator := 3546666261790458409500488499200 }, { target := 599, numerator := 2010182126432705264467574784000 }, { target := 601, numerator := 2010183564227518418291313868800 }, { target := 763, numerator := 21635464264220616640824344576 }, { target := 766, numerator := 77550046430776039520906248192 }, { target := 768, numerator := 21641751493275208376291164160 }, { target := 773, numerator := 10135295158963465112078254080 }, { target := 775, numerator := 10135302408294069399774560256 }]

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
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left6.expected,
    Slot18.Left14.expected,
    Slot20.Left0.expected,
    Slot21.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1798881619586568211962789888 }, { target := 1, numerator := 44101613899541672293281300480 }, { target := 2, numerator := 32611982909924236616873803776 }, { target := 3, numerator := 36383831467121879641957072896 }, { target := 4, numerator := 1798881619586568211962789888 }, { target := 5, numerator := 36325803027780377441571176448 }, { target := 6, numerator := 36964115860536901645816037376 }, { target := 7, numerator := 1798881619586568211962789888 }, { target := 8, numerator := 44101613899541672293281300480 }, { target := 9, numerator := 1798881619586568211962789888 }, { target := 10, numerator := 93638547121484709752549146624 }, { target := 11, numerator := 69730832962807762581685534720 }, { target := 12, numerator := 73715451989253920443496136704 }, { target := 13, numerator := 95630856634707788683454447616 }, { target := 14, numerator := 1281055017002439752572108537856 }, { target := 15, numerator := 2317055963878440796642865053696 }, { target := 16, numerator := 69730832962807762581685534720 }, { target := 17, numerator := 1281055017002439752572108537856 }, { target := 18, numerator := 75707761502476999374401437696 }, { target := 19, numerator := 75707761502476999374401437696 }, { target := 20, numerator := 73715451989253920443496136704 }, { target := 21, numerator := 73715451989253920443496136704 }, { target := 22, numerator := 2317055963878440796642865053696 }, { target := 23, numerator := 73715451989253920443496136704 }, { target := 24, numerator := 93638547121484709752549146624 }, { target := 25, numerator := 95630856634707788683454447616 }, { target := 131, numerator := 2382556834869359556490690560 }, { target := 134, numerator := 8679084314999049844592476160 }, { target := 136, numerator := 2382558437542840950692249600 }, { target := 227, numerator := 767472446074883942184722104320 }, { target := 230, numerator := 2795718436361125973483606507520 }, { target := 232, numerator := 767472962330244160024687411200 }, { target := 263, numerator := 898326331303326869710962688 }, { target := 265, numerator := 898326331303326869710962688 }, { target := 302, numerator := 8162392207931036499301625757696 }, { target := 305, numerator := 29733641249573439041036569542656 }, { target := 307, numerator := 8162397698523892433011720847360 }, { target := 338, numerator := 157557998697225348317376937984 }, { target := 340, numerator := 157557998697225348317376937984 }, { target := 589, numerator := 767474759236859543504679862272 }, { target := 592, numerator := 2795726862656577428871805140992 }, { target := 594, numerator := 767475275493775755015901675520 }, { target := 599, numerator := 157558017586691279795957792768 }, { target := 601, numerator := 157558017586691279795957792768 }, { target := 763, numerator := 2382556834869359556490690560 }, { target := 766, numerator := 8679084314999049844592476160 }, { target := 768, numerator := 2382558437542840950692249600 }, { target := 773, numerator := 898307441837395391130107904 }, { target := 775, numerator := 898307441837395391130107904 }]

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
    Slot21.Left2.expected,
    Slot22.Left0.expected,
    Slot22.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 39054301143789779852634095616 }, { target := 27, numerator := 566287366584951807863194386432 }, { target := 28, numerator := 1002393729357271016217608454144 }, { target := 29, numerator := 32545250953158149877195079680 }, { target := 30, numerator := 624868818300636477642145529856 }, { target := 31, numerator := 32545250953158149877195079680 }, { target := 32, numerator := 995884679166639386242169438208 }, { target := 33, numerator := 1041448030501060796070242549760 }, { target := 34, numerator := 624868818300636477642145529856 }, { target := 35, numerator := 15953682017238125069801028059136 }, { target := 36, numerator := 1021920879929165906143925501952 }, { target := 37, numerator := 566287366584951807863194386432 }, { target := 38, numerator := 995884679166639386242169438208 }, { target := 39, numerator := 32545250953158149877195079680 }, { target := 40, numerator := 1021920879929165906143925501952 }, { target := 41, numerator := 32545250953158149877195079680 }, { target := 42, numerator := 995884679166639386242169438208 }, { target := 43, numerator := 1041448030501060796070242549760 }, { target := 44, numerator := 39054301143789779852634095616 }, { target := 141, numerator := 93638569446656724959533989888 }, { target := 142, numerator := 69730849587935859012418928640 }, { target := 143, numerator := 73715469564389336670271438848 }, { target := 144, numerator := 95630879434883463788460244992 }, { target := 145, numerator := 1281055322429793066999582031872 }, { target := 146, numerator := 2317056516307697258041234685952 }, { target := 147, numerator := 69730849587935859012418928640 }, { target := 148, numerator := 1281055322429793066999582031872 }, { target := 149, numerator := 75707779552616075499197693952 }, { target := 150, numerator := 75707779552616075499197693952 }, { target := 151, numerator := 73715469564389336670271438848 }, { target := 152, numerator := 73715469564389336670271438848 }, { target := 153, numerator := 2317056516307697258041234685952 }, { target := 154, numerator := 73715469564389336670271438848 }, { target := 155, numerator := 93638569446656724959533989888 }, { target := 156, numerator := 95630879434883463788460244992 }, { target := 157, numerator := 145076996308179758027542364160 }, { target := 158, numerator := 2103616446468606491399364280320 }, { target := 159, numerator := 3723642905243280456040254013440 }, { target := 160, numerator := 120897496923483131689618636800 }, { target := 161, numerator := 2321231940930876128440677826560 }, { target := 162, numerator := 120897496923483131689618636800 }, { target := 163, numerator := 3699463405858583829702330286080 }, { target := 164, numerator := 3868719901551460214067796377600 }, { target := 165, numerator := 2321231940930876128440677826560 }, { target := 166, numerator := 59263952991891431154251055759360 }, { target := 167, numerator := 3796181403397370335054025195520 }, { target := 168, numerator := 2103616446468606491399364280320 }, { target := 169, numerator := 3699463405858583829702330286080 }, { target := 170, numerator := 120897496923483131689618636800 }, { target := 171, numerator := 3796181403397370335054025195520 }, { target := 172, numerator := 120897496923483131689618636800 }, { target := 173, numerator := 3699463405858583829702330286080 }, { target := 174, numerator := 3868719901551460214067796377600 }, { target := 175, numerator := 145076996308179758027542364160 }]

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
    Slot22.Left5.expected,
    Slot23.Left0.expected,
    Slot23.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 8545835394112232993996144640 }, { target := 81, numerator := 9648523832062198541608550400 }, { target := 82, numerator := 8270163284624741607093043200 }, { target := 83, numerator := 108890483247559097826725068800 }, { target := 84, numerator := 9648523832062198541608550400 }, { target := 85, numerator := 8270163284624741607093043200 }, { target := 86, numerator := 9648523832062198541608550400 }, { target := 87, numerator := 9648523832062198541608550400 }, { target := 88, numerator := 400000230866350002396400189440 }, { target := 89, numerator := 9924195941549689928511651840 }, { target := 90, numerator := 108890483247559097826725068800 }, { target := 91, numerator := 400000230866350002396400189440 }, { target := 92, numerator := 8545835394112232993996144640 }, { target := 93, numerator := 9648523832062198541608550400 }, { target := 94, numerator := 9924195941549689928511651840 }, { target := 95, numerator := 9648523832062198541608550400 }, { target := 176, numerator := 334440926740393439420242460672 }, { target := 177, numerator := 377594594706895818700273745920 }, { target := 178, numerator := 323652509748767844600234639360 }, { target := 179, numerator := 4261424711692109953903089418240 }, { target := 180, numerator := 377594594706895818700273745920 }, { target := 181, numerator := 323652509748767844600234639360 }, { target := 182, numerator := 377594594706895818700273745920 }, { target := 183, numerator := 377594594706895818700273745920 }, { target := 184, numerator := 15653993054848738083831348723712 }, { target := 185, numerator := 388383011698521413520281567232 }, { target := 186, numerator := 4261424711692109953903089418240 }, { target := 187, numerator := 15653993054848738083831348723712 }, { target := 188, numerator := 334440926740393439420242460672 }, { target := 189, numerator := 377594594706895818700273745920 }, { target := 190, numerator := 388383011698521413520281567232 }, { target := 191, numerator := 377594594706895818700273745920 }, { target := 267, numerator := 39046080255447924803981279232 }, { target := 268, numerator := 566168163703994909657728548864 }, { target := 269, numerator := 1002182726556496736635519500288 }, { target := 270, numerator := 32538400212873270669984399360 }, { target := 271, numerator := 624737284087166796863700467712 }, { target := 272, numerator := 32538400212873270669984399360 }, { target := 273, numerator := 995675046513922082501522620416 }, { target := 274, numerator := 1041228806811944661439500779520 }, { target := 275, numerator := 624737284087166796863700467712 }, { target := 276, numerator := 15950323784350477282426352566272 }, { target := 277, numerator := 1021705766684220699037510139904 }, { target := 278, numerator := 566168163703994909657728548864 }, { target := 279, numerator := 995675046513922082501522620416 }, { target := 280, numerator := 32538400212873270669984399360 }, { target := 281, numerator := 1021705766684220699037510139904 }, { target := 282, numerator := 32538400212873270669984399360 }, { target := 283, numerator := 995675046513922082501522620416 }, { target := 284, numerator := 1041228806811944661439500779520 }, { target := 285, numerator := 39046080255447924803981279232 }]

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
    Slot23.Left5.expected,
    Slot23.Left12.expected,
    Slot24.Left0.expected,
    Slot24.Left1.expected,
    Slot24.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 10240156570197646293073920 }, { target := 132, numerator := 213763268402875866367918080 }, { target := 133, numerator := 11093502951047450150830080 }, { target := 134, numerator := 229976849639022139665285120 }, { target := 135, numerator := 344325264672895856604610560 }, { target := 136, numerator := 10666829760622548221952000 }, { target := 137, numerator := 344325264672895856604610560 }, { target := 138, numerator := 358832153147342522186465280 }, { target := 139, numerator := 213763268402875866367918080 }, { target := 140, numerator := 10666829760622548221952000 }, { target := 227, numerator := 1210320762401483090999377920 }, { target := 228, numerator := 25265445915130959524612014080 }, { target := 229, numerator := 1311180825934940015249326080 }, { target := 230, numerator := 27181787122266641085361029120 }, { target := 231, numerator := 40697035635749868934854082560 }, { target := 232, numerator := 1260750794168211553124352000 }, { target := 233, numerator := 40697035635749868934854082560 }, { target := 234, numerator := 42411656715818636647103201280 }, { target := 235, numerator := 25265445915130959524612014080 }, { target := 236, numerator := 1260750794168211553124352000 }, { target := 286, numerator := 334440926740393439420242460672 }, { target := 287, numerator := 377594594706895818700273745920 }, { target := 288, numerator := 323652509748767844600234639360 }, { target := 289, numerator := 4261424711692109953903089418240 }, { target := 290, numerator := 377594594706895818700273745920 }, { target := 291, numerator := 323652509748767844600234639360 }, { target := 292, numerator := 377594594706895818700273745920 }, { target := 293, numerator := 377594594706895818700273745920 }, { target := 294, numerator := 15653993054848738083831348723712 }, { target := 295, numerator := 388383011698521413520281567232 }, { target := 296, numerator := 4261424711692109953903089418240 }, { target := 297, numerator := 15653993054848738083831348723712 }, { target := 298, numerator := 334440926740393439420242460672 }, { target := 299, numerator := 377594594706895818700273745920 }, { target := 300, numerator := 388383011698521413520281567232 }, { target := 301, numerator := 377594594706895818700273745920 }, { target := 302, numerator := 11485702773913683301100421120 }, { target := 303, numerator := 239764045405448138910471290880 }, { target := 304, numerator := 12442844671739823576192122880 }, { target := 305, numerator := 257949741464144804137213624320 }, { target := 306, numerator := 386206755772847600999501660160 }, { target := 307, numerator := 11964273722826753438646272000 }, { target := 308, numerator := 386206755772847600999501660160 }, { target := 309, numerator := 402478168035891985676060590080 }, { target := 310, numerator := 239764045405448138910471290880 }, { target := 311, numerator := 11964273722826753438646272000 }, { target := 573, numerator := 8545835394112232993996144640 }, { target := 574, numerator := 9648523832062198541608550400 }, { target := 575, numerator := 8270163284624741607093043200 }, { target := 576, numerator := 108890483247559097826725068800 }, { target := 577, numerator := 9648523832062198541608550400 }, { target := 578, numerator := 8270163284624741607093043200 }, { target := 579, numerator := 9648523832062198541608550400 }, { target := 580, numerator := 9648523832062198541608550400 }, { target := 581, numerator := 400000230866350002396400189440 }, { target := 582, numerator := 9924195941549689928511651840 }, { target := 583, numerator := 108890483247559097826725068800 }, { target := 584, numerator := 400000230866350002396400189440 }, { target := 585, numerator := 8545835394112232993996144640 }, { target := 586, numerator := 9648523832062198541608550400 }, { target := 587, numerator := 9924195941549689928511651840 }, { target := 588, numerator := 9648523832062198541608550400 }]

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
    Slot24.Left11.expected,
    Slot24.Left18.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected,
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected,
    Slot25.Left8.expected,
    Slot25.Left9.expected,
    Slot25.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 221686772171832624911745024 }, { target := 264, numerator := 242540742560184978175426560 }, { target := 265, numerator := 221686772171832624911745024 }, { target := 266, numerator := 242540742560184978175426560 }, { target := 338, numerator := 166265079128874468683808768 }, { target := 339, numerator := 181905556920138733631569920 }, { target := 340, numerator := 166265079128874468683808768 }, { target := 341, numerator := 181905556920138733631569920 }, { target := 352, numerator := 175502027969367494721798144 }, { target := 353, numerator := 192011421193479774388879360 }, { target := 354, numerator := 175502027969367494721798144 }, { target := 355, numerator := 192011421193479774388879360 }, { target := 479, numerator := 226305246592079137930739712 }, { target := 480, numerator := 247593674696855498554081280 }, { target := 481, numerator := 226305246592079137930739712 }, { target := 482, numerator := 247593674696855498554081280 }, { target := 554, numerator := 3029719219681712540460515328 }, { target := 555, numerator := 3314723481655861368397496320 }, { target := 556, numerator := 3029719219681712540460515328 }, { target := 557, numerator := 3314723481655861368397496320 }, { target := 568, numerator := 5297390160022750432786907136 }, { target := 569, numerator := 5795713160761086874316963840 }, { target := 570, numerator := 5297390160022750432786907136 }, { target := 571, numerator := 5795713160761086874316963840 }, { target := 589, numerator := 1210321592504966407929200640 }, { target := 590, numerator := 25265463243541173765522063360 }, { target := 591, numerator := 1311181725213713608589967360 }, { target := 592, numerator := 27181805765007370578076631040 }, { target := 593, numerator := 40697063547979495466619371520 }, { target := 594, numerator := 1260751658859340008259584000 }, { target := 595, numerator := 40697063547979495466619371520 }, { target := 596, numerator := 42411685804028197877852405760 }, { target := 597, numerator := 25265463243541173765522063360 }, { target := 598, numerator := 1260751658859340008259584000 }, { target := 599, numerator := 161646604708627955664814080 }, { target := 600, numerator := 176852624783468213252915200 }, { target := 601, numerator := 161646604708627955664814080 }, { target := 602, numerator := 176852624783468213252915200 }, { target := 613, numerator := 3029719219681712540460515328 }, { target := 614, numerator := 3314723481655861368397496320 }, { target := 615, numerator := 3029719219681712540460515328 }, { target := 616, numerator := 3314723481655861368397496320 }, { target := 618, numerator := 170883553549120981702803456 }, { target := 619, numerator := 186958489056809254010224640 }, { target := 620, numerator := 170883553549120981702803456 }, { target := 621, numerator := 186958489056809254010224640 }, { target := 694, numerator := 175502027969367494721798144 }, { target := 695, numerator := 192011421193479774388879360 }, { target := 696, numerator := 175502027969367494721798144 }, { target := 697, numerator := 192011421193479774388879360 }, { target := 708, numerator := 175502027969367494721798144 }, { target := 709, numerator := 192011421193479774388879360 }, { target := 710, numerator := 175502027969367494721798144 }, { target := 711, numerator := 192011421193479774388879360 }, { target := 763, numerator := 10240156570197646293073920 }, { target := 764, numerator := 213763268402875866367918080 }, { target := 765, numerator := 11093502951047450150830080 }, { target := 766, numerator := 229976849639022139665285120 }, { target := 767, numerator := 344325264672895856604610560 }, { target := 768, numerator := 10666829760622548221952000 }, { target := 769, numerator := 344325264672895856604610560 }, { target := 770, numerator := 358832153147342522186465280 }, { target := 771, numerator := 213763268402875866367918080 }, { target := 772, numerator := 10666829760622548221952000 }]

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
    Slot25.Left11.expected,
    Slot25.Left12.expected,
    Slot25.Left13.expected,
    Slot25.Left14.expected,
    Slot25.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 739, numerator := 170883553549120981702803456 }, { target := 740, numerator := 186958489056809254010224640 }, { target := 741, numerator := 170883553549120981702803456 }, { target := 742, numerator := 186958489056809254010224640 }, { target := 753, numerator := 5297390160022750432786907136 }, { target := 754, numerator := 5795713160761086874316963840 }, { target := 755, numerator := 5297390160022750432786907136 }, { target := 756, numerator := 5795713160761086874316963840 }, { target := 758, numerator := 170883553549120981702803456 }, { target := 759, numerator := 186958489056809254010224640 }, { target := 760, numerator := 170883553549120981702803456 }, { target := 761, numerator := 186958489056809254010224640 }, { target := 773, numerator := 221686772171832624911745024 }, { target := 774, numerator := 242540742560184978175426560 }, { target := 775, numerator := 221686772171832624911745024 }, { target := 776, numerator := 242540742560184978175426560 }, { target := 778, numerator := 226305246592079137930739712 }, { target := 779, numerator := 247593674696855498554081280 }, { target := 780, numerator := 226305246592079137930739712 }, { target := 781, numerator := 247593674696855498554081280 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent2
