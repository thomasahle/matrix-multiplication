import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
  [{ target := 10, numerator := 53623239258706889561604096 }, { target := 11, numerator := 9405012373406151773339516928 }, { target := 16, numerator := 9405013500963383278835859456 }, { target := 24, numerator := 53622111701475384065261568 }, { target := 26, numerator := 5016038648523101275422720 }, { target := 27, numerator := 1615773187378871025889443840 }, { target := 29, numerator := 17184427326213550822184189952 }, { target := 37, numerator := 1615778057319306485211070464 }, { target := 44, numerator := 5016038648523101275422720 }, { target := 45, numerator := 58667552154208969152266240 }, { target := 46, numerator := 10289737463747016766332600320 }, { target := 51, numerator := 10289738697373026695658864640 }, { target := 59, numerator := 58666318528199039826001920 }, { target := 61, numerator := 104709806787919739124449280 }, { target := 62, numerator := 33729265286533932665442140160 }, { target := 64, numerator := 358724920434707873413094965248 }, { target := 72, numerator := 33729366946540522878781095936 }, { target := 79, numerator := 104709806787919739124449280 }, { target := 96, numerator := 5434041869233359715041280 }, { target := 97, numerator := 1750420952993776944713564160 }, { target := 99, numerator := 18616462936731346724032872448 }, { target := 107, numerator := 1750426228762582025645326336 }, { target := 114, numerator := 5434041869233359715041280 }, { target := 141, numerator := 53623239258706889561604096 }, { target := 142, numerator := 9405012373406151773339516928 }, { target := 147, numerator := 9405013500963383278835859456 }, { target := 155, numerator := 53622111701475384065261568 }, { target := 157, numerator := 112651867981414649477201920 }, { target := 158, numerator := 36287572833217145123100426240 }, { target := 160, numerator := 385933597034545995548219932672 }, { target := 168, numerator := 36287682203962758147031957504 }, { target := 175, numerator := 112651867981414649477201920 }, { target := 192, numerator := 168664299556589280386088960 }, { target := 193, numerator := 54330373425614538245532549120 }, { target := 195, numerator := 577826368843930646395943387136 }, { target := 203, numerator := 54330537177361680565222244352 }, { target := 210, numerator := 168664299556589280386088960 }, { target := 267, numerator := 5225040258878230495232000 }, { target := 268, numerator := 1683097070186323985301504000 }, { target := 270, numerator := 17900445131472448773108531200 }, { target := 278, numerator := 1683102143040944255428198400 }, { target := 285, numerator := 5225040258878230495232000 }, { target := 357, numerator := 58667552154208969152266240 }, { target := 358, numerator := 10289737463747016766332600320 }, { target := 363, numerator := 10289738697373026695658864640 }, { target := 371, numerator := 58666318528199039826001920 }, { target := 373, numerator := 168664299556589280386088960 }, { target := 374, numerator := 54330373425614538245532549120 }, { target := 376, numerator := 577826368843930646395943387136 }, { target := 384, numerator := 54330537177361680565222244352 }, { target := 391, numerator := 168664299556589280386088960 }, { target := 408, numerator := 175770354308663673859604480 }, { target := 409, numerator := 56619385441067938865542594560 }, { target := 411, numerator := 602170974222733176727370989568 }, { target := 419, numerator := 56619556091897364752604594176 }, { target := 426, numerator := 175770354308663673859604480 }, { target := 483, numerator := 104709806787919739124449280 }, { target := 484, numerator := 33729265286533932665442140160 }, { target := 486, numerator := 358724920434707873413094965248 }, { target := 494, numerator := 33729366946540522878781095936 }, { target := 501, numerator := 104709806787919739124449280 }]

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
    Slot3.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 5931117584147780248384045056 }, { target := 82, numerator := 232120798273778336622564081664 }, { target := 85, numerator := 232120883407808079801358483456 }, { target := 92, numerator := 5931202718177523427178446848 }, { target := 115, numerator := 6696423078876526086885212160 }, { target := 117, numerator := 262071869018781992960959447040 }, { target := 120, numerator := 262071965137847832033791836160 }, { target := 127, numerator := 6696519197942365159717601280 }, { target := 176, numerator := 5739791210465593788758753280 }, { target := 178, numerator := 224633030587527422537965240320 }, { target := 181, numerator := 224633112975298141743250145280 }, { target := 188, numerator := 5739873598236312994043658240 }, { target := 211, numerator := 75573917604463651551990251520 }, { target := 213, numerator := 2957668236069111063416542330880 }, { target := 216, numerator := 2957669320841425532952793579520 }, { target := 223, numerator := 75575002376778121088241500160 }, { target := 237, numerator := 6696423078876526086885212160 }, { target := 239, numerator := 262071869018781992960959447040 }, { target := 242, numerator := 262071965137847832033791836160 }, { target := 249, numerator := 6696519197942365159717601280 }, { target := 286, numerator := 5739791210465593788758753280 }, { target := 288, numerator := 224633030587527422537965240320 }, { target := 291, numerator := 224633112975298141743250145280 }, { target := 298, numerator := 5739873598236312994043658240 }, { target := 312, numerator := 6696423078876526086885212160 }, { target := 314, numerator := 262071869018781992960959447040 }, { target := 317, numerator := 262071965137847832033791836160 }, { target := 324, numerator := 6696519197942365159717601280 }, { target := 392, numerator := 6696423078876526086885212160 }, { target := 394, numerator := 262071869018781992960959447040 }, { target := 397, numerator := 262071965137847832033791836160 }, { target := 404, numerator := 6696519197942365159717601280 }, { target := 427, numerator := 277614568212852552916298366976 }, { target := 429, numerator := 10864750912750076336752918790144 }, { target := 432, numerator := 10864754897571920122315198693376 }, { target := 439, numerator := 277618553034696338478578270208 }, { target := 453, numerator := 6887749452558712546510503936 }, { target := 455, numerator := 269559636705032907045558288384 }, { target := 458, numerator := 269559735570357770091900174336 }, { target := 465, numerator := 6887848317883575592852389888 }, { target := 502, numerator := 75573917604463651551990251520 }, { target := 504, numerator := 2957668236069111063416542330880 }, { target := 507, numerator := 2957669320841425532952793579520 }, { target := 514, numerator := 75575002376778121088241500160 }, { target := 528, numerator := 277614568212852552916298366976 }, { target := 530, numerator := 10864750912750076336752918790144 }, { target := 533, numerator := 10864754897571920122315198693376 }, { target := 540, numerator := 277618553034696338478578270208 }, { target := 573, numerator := 5931117584147780248384045056 }, { target := 575, numerator := 232120798273778336622564081664 }, { target := 578, numerator := 232120883407808079801358483456 }, { target := 585, numerator := 5931202718177523427178446848 }, { target := 623, numerator := 5225040258878230495232000 }, { target := 624, numerator := 1683097070186323985301504000 }, { target := 626, numerator := 17900445131472448773108531200 }, { target := 634, numerator := 1683102143040944255428198400 }, { target := 641, numerator := 5225040258878230495232000 }, { target := 642, numerator := 6696423078876526086885212160 }, { target := 644, numerator := 262071869018781992960959447040 }, { target := 647, numerator := 262071965137847832033791836160 }, { target := 654, numerator := 6696519197942365159717601280 }]

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
    Slot4.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 18703146668220785821011148800 }, { target := 134, numerator := 67039462375705371454577049600 }, { target := 136, numerator := 18708581770777803419025408000 }, { target := 227, numerator := 271195626689201394404661657600 }, { target := 230, numerator := 972072204447727886091367219200 }, { target := 232, numerator := 271274435676278149575868416000 }, { target := 253, numerator := 480047431151000169405952819200 }, { target := 256, numerator := 1720679534309771200667477606400 }, { target := 258, numerator := 480186932116630287754985472000 }, { target := 302, numerator := 15585955556850654850842624000 }, { target := 305, numerator := 55866218646421142878814208000 }, { target := 307, numerator := 15590484808981502849187840000 }, { target := 328, numerator := 299250346691532573136178380800 }, { target := 331, numerator := 1072631398011285943273232793600 }, { target := 333, numerator := 299337308332444854704406528000 }, { target := 342, numerator := 15585955556850654850842624000 }, { target := 345, numerator := 55866218646421142878814208000 }, { target := 347, numerator := 15590484808981502849187840000 }, { target := 443, numerator := 476930240039630038435784294400 }, { target := 446, numerator := 1709506290580486972091714764800 }, { target := 448, numerator := 477068835154833987185147904000 }, { target := 469, numerator := 498750577819220955226963968000 }, { target := 472, numerator := 1787718996685476572122054656000 }, { target := 474, numerator := 498895513887408091174010880000 }, { target := 518, numerator := 299250346691532573136178380800 }, { target := 521, numerator := 1072631398011285943273232793600 }, { target := 523, numerator := 299337308332444854704406528000 }, { target := 544, numerator := 7640235413968191007883054284800 }, { target := 547, numerator := 27385620380475644239194724761600 }, { target := 549, numerator := 7642455653362732696671879168000 }, { target := 558, numerator := 489399004485110562316458393600 }, { target := 561, numerator := 1754199265497623886394766131200 }, { target := 563, numerator := 489541223002019189464498176000 }, { target := 589, numerator := 271195626689201394404661657600 }, { target := 592, numerator := 972072204447727886091367219200 }, { target := 594, numerator := 271274435676278149575868416000 }, { target := 603, numerator := 476930240039630038435784294400 }, { target := 606, numerator := 1709506290580486972091714764800 }, { target := 608, numerator := 477068835154833987185147904000 }, { target := 658, numerator := 15585955556850654850842624000 }, { target := 661, numerator := 55866218646421142878814208000 }, { target := 663, numerator := 15590484808981502849187840000 }, { target := 668, numerator := 6887749452558712546510503936 }, { target := 670, numerator := 269559636705032907045558288384 }, { target := 673, numerator := 269559735570357770091900174336 }, { target := 680, numerator := 6887848317883575592852389888 }, { target := 684, numerator := 489399004485110562316458393600 }, { target := 687, numerator := 1754199265497623886394766131200 }, { target := 689, numerator := 489541223002019189464498176000 }, { target := 698, numerator := 15585955556850654850842624000 }, { target := 701, numerator := 55866218646421142878814208000 }, { target := 703, numerator := 15590484808981502849187840000 }, { target := 713, numerator := 6696423078876526086885212160 }, { target := 715, numerator := 262071869018781992960959447040 }, { target := 718, numerator := 262071965137847832033791836160 }, { target := 725, numerator := 6696519197942365159717601280 }, { target := 729, numerator := 476930240039630038435784294400 }, { target := 732, numerator := 1709506290580486972091714764800 }, { target := 734, numerator := 477068835154833987185147904000 }, { target := 743, numerator := 498750577819220955226963968000 }, { target := 746, numerator := 1787718996685476572122054656000 }, { target := 748, numerator := 498895513887408091174010880000 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 794925394794413118111875072 }, { target := 11, numerator := 157661399633734262068976025600 }, { target := 16, numerator := 157661399633734262068976025600 }, { target := 24, numerator := 794925394794413118111875072 }, { target := 26, numerator := 3424932563683601833953067008 }, { target := 27, numerator := 561280484913553579703229480960 }, { target := 29, numerator := 5778599913585263990643684802560 }, { target := 37, numerator := 561280484913553579703229480960 }, { target := 44, numerator := 3424932563683601833953067008 }, { target := 80, numerator := 30264699940375853607153565696 }, { target := 82, numerator := 1209977088336849704409909690368 }, { target := 85, numerator := 1209976792640200050760405221376 }, { target := 92, numerator := 30264699940375853607153565696 }, { target := 141, numerator := 794925394794413118111875072 }, { target := 142, numerator := 157661399633734262068976025600 }, { target := 147, numerator := 157661399633734262068976025600 }, { target := 155, numerator := 794925394794413118111875072 }, { target := 157, numerator := 12476209615803658525986521088 }, { target := 158, numerator := 2044610471252574555936978370560 }, { target := 160, numerator := 21050056451393201815930703708160 }, { target := 168, numerator := 2044610471252574555936978370560 }, { target := 175, numerator := 12476209615803658525986521088 }, { target := 263, numerator := 21364129443818915745832632320 }, { target := 265, numerator := 21364144724640537804982452224 }, { target := 267, numerator := 3424934867531516412721889280 }, { target := 268, numerator := 561280862469855964554697113600 }, { target := 270, numerator := 5778603800673582535514102169600 }, { target := 278, numerator := 561280862469855964554697113600 }, { target := 285, numerator := 3424934867531516412721889280 }, { target := 338, numerator := 15909458096460894704343449600 }, { target := 340, numerator := 15909469475796145173923102720 }, { target := 352, numerator := 16818569987687231544591646720 }, { target := 354, numerator := 16818582017270210612432994304 }, { target := 479, numerator := 21818685389432084165956730880 }, { target := 481, numerator := 21818700995377570524237398016 }, { target := 554, numerator := 292279473029267294139795374080 }, { target := 556, numerator := 292279682083912038480930144256 }, { target := 568, numerator := 528648564748114872604326625280 }, { target := 570, numerator := 528648942867169052493501956096 }, { target := 599, numerator := 15909458096460894704343449600 }, { target := 601, numerator := 15909469475796145173923102720 }, { target := 613, numerator := 292279473029267294139795374080 }, { target := 615, numerator := 292279682083912038480930144256 }, { target := 618, numerator := 17273125933300399964715745280 }, { target := 620, numerator := 17273138288007243331687940096 }, { target := 694, numerator := 17273125933300399964715745280 }, { target := 696, numerator := 17273138288007243331687940096 }, { target := 708, numerator := 16818569987687231544591646720 }, { target := 710, numerator := 16818582017270210612432994304 }, { target := 739, numerator := 16818569987687231544591646720 }, { target := 741, numerator := 16818582017270210612432994304 }, { target := 753, numerator := 528648564748114872604326625280 }, { target := 755, numerator := 528648942867169052493501956096 }, { target := 758, numerator := 16818569987687231544591646720 }, { target := 760, numerator := 16818582017270210612432994304 }, { target := 763, numerator := 18703146668220785821011148800 }, { target := 766, numerator := 67039462375705371454577049600 }, { target := 768, numerator := 18708581770777803419025408000 }, { target := 773, numerator := 21364129443818915745832632320 }, { target := 775, numerator := 21364144724640537804982452224 }, { target := 778, numerator := 21818685389432084165956730880 }, { target := 780, numerator := 21818700995377570524237398016 }]

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
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 22273241335045252586080829440 }, { target := 11, numerator := 16586456313331571074741043200 }, { target := 12, numerator := 17534253816950517993297674240 }, { target := 13, numerator := 22747140086854726045359144960 }, { target := 14, numerator := 304716897413491434315956879360 }, { target := 15, numerator := 551144248354417633140680949760 }, { target := 16, numerator := 16586456313331571074741043200 }, { target := 17, numerator := 304716897413491434315956879360 }, { target := 18, numerator := 18008152568759991452575989760 }, { target := 19, numerator := 18008152568759991452575989760 }, { target := 20, numerator := 17534253816950517993297674240 }, { target := 21, numerator := 17534253816950517993297674240 }, { target := 22, numerator := 551144248354417633140680949760 }, { target := 23, numerator := 17534253816950517993297674240 }, { target := 24, numerator := 22273241335045252586080829440 }, { target := 25, numerator := 22747140086854726045359144960 }, { target := 131, numerator := 3431893808731739236054597632 }, { target := 134, numerator := 12501567765429275718112509952 }, { target := 136, numerator := 3431896117262271527381893120 }, { target := 176, numerator := 1209977088336849704409909690368 }, { target := 178, numerator := 48374659493879614612131329081344 }, { target := 181, numerator := 48374647671982424692690736119808 }, { target := 188, numerator := 1209977088336849704409909690368 }, { target := 227, numerator := 562421298907280314621325475840 }, { target := 230, numerator := 2048766183592518813164492554240 }, { target := 232, numerator := 562421677230973557978588774400 }, { target := 263, numerator := 894291069143714757875859456 }, { target := 265, numerator := 894291069143714757875859456 }, { target := 286, numerator := 1209976792640200050760405221376 }, { target := 288, numerator := 48374647671982424692690736119808 }, { target := 291, numerator := 48374635850088123832411101331456 }, { target := 298, numerator := 1209976792640200050760405221376 }, { target := 302, numerator := 5790345035360843795502716682240 }, { target := 305, numerator := 21092841118977334339946823024640 }, { target := 307, numerator := 5790348930349748353675716198400 }, { target := 338, numerator := 177369074587951044827598028800 }, { target := 340, numerator := 177369074587951044827598028800 }, { target := 573, numerator := 30264699940375853607153565696 }, { target := 575, numerator := 1209977088336849704409909690368 }, { target := 578, numerator := 1209976792640200050760405221376 }, { target := 585, numerator := 30264699940375853607153565696 }, { target := 589, numerator := 562421298907280314621325475840 }, { target := 592, numerator := 2048766183592518813164492554240 }, { target := 594, numerator := 562421677230973557978588774400 }, { target := 599, numerator := 177369074587951044827598028800 }, { target := 601, numerator := 177369074587951044827598028800 }, { target := 763, numerator := 3431893808731739236054597632 }, { target := 766, numerator := 12501567765429275718112509952 }, { target := 768, numerator := 3431896117262271527381893120 }, { target := 773, numerator := 894291069143714757875859456 }, { target := 775, numerator := 894291069143714757875859456 }]

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
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 18661584120069184074742235136 }, { target := 27, numerator := 270592969741003169083762409472 }, { target := 28, numerator := 478980659081775724585050701824 }, { target := 29, numerator := 15551320100057653395618529280 }, { target := 30, numerator := 298585345921106945195875762176 }, { target := 31, numerator := 15551320100057653395618529280 }, { target := 32, numerator := 475870395061764193905926995968 }, { target := 33, numerator := 497642243201844908659792936960 }, { target := 34, numerator := 298585345921106945195875762176 }, { target := 35, numerator := 7623257113048261694532203053056 }, { target := 36, numerator := 488311451141810316622421819392 }, { target := 37, numerator := 270592969741003169083762409472 }, { target := 38, numerator := 475870395061764193905926995968 }, { target := 39, numerator := 15551320100057653395618529280 }, { target := 40, numerator := 488311451141810316622421819392 }, { target := 41, numerator := 15551320100057653395618529280 }, { target := 42, numerator := 475870395061764193905926995968 }, { target := 43, numerator := 497642243201844908659792936960 }, { target := 44, numerator := 18661584120069184074742235136 }, { target := 141, numerator := 22273257266114603243492343808 }, { target := 142, numerator := 16586468176893853479196426240 }, { target := 143, numerator := 17534266358430645106579079168 }, { target := 144, numerator := 22747156356882999057183670272 }, { target := 145, numerator := 304717115364078508203522916352 }, { target := 146, numerator := 551144642563644331323012677632 }, { target := 147, numerator := 16586468176893853479196426240 }, { target := 148, numerator := 304717115364078508203522916352 }, { target := 149, numerator := 18008165449199040920270405632 }, { target := 150, numerator := 18008165449199040920270405632 }, { target := 151, numerator := 17534266358430645106579079168 }, { target := 152, numerator := 17534266358430645106579079168 }, { target := 153, numerator := 551144642563644331323012677632 }, { target := 154, numerator := 17534266358430645106579079168 }, { target := 155, numerator := 22273257266114603243492343808 }, { target := 156, numerator := 22747156356882999057183670272 }, { target := 157, numerator := 66890485792648248406900211712 }, { target := 158, numerator := 969912043993399601900053069824 }, { target := 159, numerator := 1716855802011305042443772100608 }, { target := 160, numerator := 55742071493873540339083509760 }, { target := 161, numerator := 1070247772682371974510403387392 }, { target := 162, numerator := 55742071493873540339083509760 }, { target := 163, numerator := 1705707387712530334375955398656 }, { target := 164, numerator := 1783746287803953290850672312320 }, { target := 165, numerator := 1070247772682371974510403387392 }, { target := 166, numerator := 27324763446296809474218736484352 }, { target := 167, numerator := 1750301044907629166647222206464 }, { target := 168, numerator := 969912043993399601900053069824 }, { target := 169, numerator := 1705707387712530334375955398656 }, { target := 170, numerator := 55742071493873540339083509760 }, { target := 171, numerator := 1750301044907629166647222206464 }, { target := 172, numerator := 55742071493873540339083509760 }, { target := 173, numerator := 1705707387712530334375955398656 }, { target := 174, numerator := 1783746287803953290850672312320 }, { target := 175, numerator := 66890485792648248406900211712 }]

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
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 5901237898585322917157928960 }, { target := 81, numerator := 6662687950015687164533145600 }, { target := 82, numerator := 5710875385727731855314124800 }, { target := 83, numerator := 75193192578748469428302643200 }, { target := 84, numerator := 6662687950015687164533145600 }, { target := 85, numerator := 5710875385727731855314124800 }, { target := 86, numerator := 6662687950015687164533145600 }, { target := 87, numerator := 6662687950015687164533145600 }, { target := 88, numerator := 276216006156364630735359836160 }, { target := 89, numerator := 6853050462873278226376949760 }, { target := 90, numerator := 75193192578748469428302643200 }, { target := 91, numerator := 276216006156364630735359836160 }, { target := 92, numerator := 5901237898585322917157928960 }, { target := 93, numerator := 6662687950015687164533145600 }, { target := 94, numerator := 6853050462873278226376949760 }, { target := 95, numerator := 6662687950015687164533145600 }, { target := 176, numerator := 230951423975169881526228746240 }, { target := 177, numerator := 260751607713901479142516326400 }, { target := 178, numerator := 223501378040486982122156851200 }, { target := 179, numerator := 2942768144199745264608398540800 }, { target := 180, numerator := 260751607713901479142516326400 }, { target := 181, numerator := 223501378040486982122156851200 }, { target := 182, numerator := 260751607713901479142516326400 }, { target := 183, numerator := 260751607713901479142516326400 }, { target := 184, numerator := 10810016651224887035308319703040 }, { target := 185, numerator := 268201653648584378546588221440 }, { target := 186, numerator := 2942768144199745264608398540800 }, { target := 187, numerator := 10810016651224887035308319703040 }, { target := 188, numerator := 230951423975169881526228746240 }, { target := 189, numerator := 260751607713901479142516326400 }, { target := 190, numerator := 268201653648584378546588221440 }, { target := 191, numerator := 260751607713901479142516326400 }, { target := 267, numerator := 18667007144620519411427573760 }, { target := 268, numerator := 270671603596997531465699819520 }, { target := 269, numerator := 479119850045259998226641059840 }, { target := 270, numerator := 15555839287183766176189644800 }, { target := 271, numerator := 298672114313928310582841180160 }, { target := 272, numerator := 15555839287183766176189644800 }, { target := 273, numerator := 476008682187823244991403130880 }, { target := 274, numerator := 497786857189880517638068633600 }, { target := 275, numerator := 298672114313928310582841180160 }, { target := 276, numerator := 7625472418577482179568163880960 }, { target := 277, numerator := 488453353617570257932354846720 }, { target := 278, numerator := 270671603596997531465699819520 }, { target := 279, numerator := 476008682187823244991403130880 }, { target := 280, numerator := 15555839287183766176189644800 }, { target := 281, numerator := 488453353617570257932354846720 }, { target := 282, numerator := 15555839287183766176189644800 }, { target := 283, numerator := 476008682187823244991403130880 }, { target := 284, numerator := 497786857189880517638068633600 }, { target := 285, numerator := 18667007144620519411427573760 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 5016038648523101275422720 }, { target := 132, numerator := 104709806787919739124449280 }, { target := 133, numerator := 5434041869233359715041280 }, { target := 134, numerator := 112651867981414649477201920 }, { target := 135, numerator := 168664299556589280386088960 }, { target := 136, numerator := 5225040258878230495232000 }, { target := 137, numerator := 168664299556589280386088960 }, { target := 138, numerator := 175770354308663673859604480 }, { target := 139, numerator := 104709806787919739124449280 }, { target := 140, numerator := 5225040258878230495232000 }, { target := 227, numerator := 1615773187378871025889443840 }, { target := 228, numerator := 33729265286533932665442140160 }, { target := 229, numerator := 1750420952993776944713564160 }, { target := 230, numerator := 36287572833217145123100426240 }, { target := 231, numerator := 54330373425614538245532549120 }, { target := 232, numerator := 1683097070186323985301504000 }, { target := 233, numerator := 54330373425614538245532549120 }, { target := 234, numerator := 56619385441067938865542594560 }, { target := 235, numerator := 33729265286533932665442140160 }, { target := 236, numerator := 1683097070186323985301504000 }, { target := 286, numerator := 230951508680312824991276072960 }, { target := 287, numerator := 260751703348740286280472985600 }, { target := 288, numerator := 223501460013205959668976844800 }, { target := 289, numerator := 2942769223507211802308195123200 }, { target := 290, numerator := 260751703348740286280472985600 }, { target := 291, numerator := 223501460013205959668976844800 }, { target := 292, numerator := 260751703348740286280472985600 }, { target := 293, numerator := 260751703348740286280472985600 }, { target := 294, numerator := 10810020615972061582656180060160 }, { target := 295, numerator := 268201752015847151602772213760 }, { target := 296, numerator := 2942769223507211802308195123200 }, { target := 297, numerator := 10810020615972061582656180060160 }, { target := 298, numerator := 230951508680312824991276072960 }, { target := 299, numerator := 260751703348740286280472985600 }, { target := 300, numerator := 268201752015847151602772213760 }, { target := 301, numerator := 260751703348740286280472985600 }, { target := 302, numerator := 17184427326213550822184189952 }, { target := 303, numerator := 358724920434707873413094965248 }, { target := 304, numerator := 18616462936731346724032872448 }, { target := 305, numerator := 385933597034545995548219932672 }, { target := 306, numerator := 577826368843930646395943387136 }, { target := 307, numerator := 17900445131472448773108531200 }, { target := 308, numerator := 577826368843930646395943387136 }, { target := 309, numerator := 602170974222733176727370989568 }, { target := 310, numerator := 358724920434707873413094965248 }, { target := 311, numerator := 17900445131472448773108531200 }, { target := 573, numerator := 5901322603728266382205255680 }, { target := 574, numerator := 6662783584854494302489804800 }, { target := 575, numerator := 5710957358446709402134118400 }, { target := 576, numerator := 75194271886215007128099225600 }, { target := 577, numerator := 6662783584854494302489804800 }, { target := 578, numerator := 5710957358446709402134118400 }, { target := 579, numerator := 6662783584854494302489804800 }, { target := 580, numerator := 6662783584854494302489804800 }, { target := 581, numerator := 276219970903539178083220193280 }, { target := 582, numerator := 6853148830136051282560942080 }, { target := 583, numerator := 75194271886215007128099225600 }, { target := 584, numerator := 276219970903539178083220193280 }, { target := 585, numerator := 5901322603728266382205255680 }, { target := 586, numerator := 6662783584854494302489804800 }, { target := 587, numerator := 6853148830136051282560942080 }, { target := 588, numerator := 6662783584854494302489804800 }]

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
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left6.expected,
    Slot19.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 53623239258706889561604096 }, { target := 264, numerator := 58667552154208969152266240 }, { target := 265, numerator := 53623239258706889561604096 }, { target := 266, numerator := 58667552154208969152266240 }, { target := 338, numerator := 9405012373406151773339516928 }, { target := 339, numerator := 10289737463747016766332600320 }, { target := 340, numerator := 9405012373406151773339516928 }, { target := 341, numerator := 10289737463747016766332600320 }, { target := 589, numerator := 1615778057319306485211070464 }, { target := 590, numerator := 33729366946540522878781095936 }, { target := 591, numerator := 1750426228762582025645326336 }, { target := 592, numerator := 36287682203962758147031957504 }, { target := 593, numerator := 54330537177361680565222244352 }, { target := 594, numerator := 1683102143040944255428198400 }, { target := 595, numerator := 54330537177361680565222244352 }, { target := 596, numerator := 56619556091897364752604594176 }, { target := 597, numerator := 33729366946540522878781095936 }, { target := 598, numerator := 1683102143040944255428198400 }, { target := 599, numerator := 9405013500963383278835859456 }, { target := 600, numerator := 10289738697373026695658864640 }, { target := 601, numerator := 9405013500963383278835859456 }, { target := 602, numerator := 10289738697373026695658864640 }, { target := 763, numerator := 5016038648523101275422720 }, { target := 764, numerator := 104709806787919739124449280 }, { target := 765, numerator := 5434041869233359715041280 }, { target := 766, numerator := 112651867981414649477201920 }, { target := 767, numerator := 168664299556589280386088960 }, { target := 768, numerator := 5225040258878230495232000 }, { target := 769, numerator := 168664299556589280386088960 }, { target := 770, numerator := 175770354308663673859604480 }, { target := 771, numerator := 104709806787919739124449280 }, { target := 772, numerator := 5225040258878230495232000 }, { target := 773, numerator := 53622111701475384065261568 }, { target := 774, numerator := 58666318528199039826001920 }, { target := 775, numerator := 53622111701475384065261568 }, { target := 776, numerator := 58666318528199039826001920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent1
