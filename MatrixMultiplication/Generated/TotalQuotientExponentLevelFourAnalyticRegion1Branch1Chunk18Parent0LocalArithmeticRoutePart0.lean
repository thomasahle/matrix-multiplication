import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent0

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
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 263, numerator := 216624395302196365242662912 }, { target := 264, numerator := 237931712872904204446859264 }, { target := 265, numerator := 216624395302196365242662912 }, { target := 266, numerator := 237931712872904204446859264 }, { target := 338, numerator := 161316039054827080499855360 }, { target := 339, numerator := 177183190437269088417873920 }, { target := 340, numerator := 161316039054827080499855360 }, { target := 341, numerator := 177183190437269088417873920 }, { target := 352, numerator := 170534098429388627956989952 }, { target := 353, numerator := 187307944176541607756038144 }, { target := 354, numerator := 170534098429388627956989952 }, { target := 355, numerator := 187307944176541607756038144 }, { target := 479, numerator := 221233424989477138971230208 }, { target := 480, numerator := 242994089742540464115941376 }, { target := 481, numerator := 221233424989477138971230208 }, { target := 482, numerator := 242994089742540464115941376 }, { target := 554, numerator := 2963606088921537507468771328 }, { target := 555, numerator := 3255108327176114967219798016 }, { target := 556, numerator := 2963606088921537507468771328 }, { target := 557, numerator := 3255108327176114967219798016 }, { target := 568, numerator := 5360301526307539846323765248 }, { target := 569, numerator := 5887544299386969995142496256 }, { target := 570, numerator := 5360301526307539846323765248 }, { target := 571, numerator := 5887544299386969995142496256 }, { target := 599, numerator := 161316039054827080499855360 }, { target := 600, numerator := 177183190437269088417873920 }, { target := 601, numerator := 161316039054827080499855360 }, { target := 602, numerator := 177183190437269088417873920 }, { target := 613, numerator := 2963606088921537507468771328 }, { target := 614, numerator := 3255108327176114967219798016 }, { target := 615, numerator := 2963606088921537507468771328 }, { target := 616, numerator := 3255108327176114967219798016 }, { target := 618, numerator := 175143128116669401685557248 }, { target := 619, numerator := 192370321046177867425120256 }, { target := 620, numerator := 175143128116669401685557248 }, { target := 621, numerator := 192370321046177867425120256 }, { target := 694, numerator := 175143128116669401685557248 }, { target := 695, numerator := 192370321046177867425120256 }, { target := 696, numerator := 175143128116669401685557248 }, { target := 697, numerator := 192370321046177867425120256 }, { target := 708, numerator := 170534098429388627956989952 }, { target := 709, numerator := 187307944176541607756038144 }, { target := 710, numerator := 170534098429388627956989952 }, { target := 711, numerator := 187307944176541607756038144 }, { target := 739, numerator := 170534098429388627956989952 }, { target := 740, numerator := 187307944176541607756038144 }, { target := 741, numerator := 170534098429388627956989952 }, { target := 742, numerator := 187307944176541607756038144 }, { target := 753, numerator := 5360301526307539846323765248 }, { target := 754, numerator := 5887544299386969995142496256 }, { target := 755, numerator := 5360301526307539846323765248 }, { target := 756, numerator := 5887544299386969995142496256 }, { target := 758, numerator := 170534098429388627956989952 }, { target := 759, numerator := 187307944176541607756038144 }, { target := 760, numerator := 170534098429388627956989952 }, { target := 761, numerator := 187307944176541607756038144 }, { target := 773, numerator := 216624395302196365242662912 }, { target := 774, numerator := 237931712872904204446859264 }, { target := 775, numerator := 216624395302196365242662912 }, { target := 776, numerator := 237931712872904204446859264 }, { target := 778, numerator := 221233424989477138971230208 }, { target := 779, numerator := 242994089742540464115941376 }, { target := 780, numerator := 221233424989477138971230208 }, { target := 781, numerator := 242994089742540464115941376 }]

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 8592640963486498819145728 }, { target := 132, numerator := 171852819269729976382914560 }, { target := 133, numerator := 8899520997896730919829504 }, { target := 134, numerator := 159884497927730924456247296 }, { target := 135, numerator := 239366426839981038533345280 }, { target := 136, numerator := 8592640963486498819145728 }, { target := 137, numerator := 239673306874391270634029056 }, { target := 138, numerator := 239673306874391270634029056 }, { target := 139, numerator := 171545939235319744282230784 }, { target := 140, numerator := 8899520997896730919829504 }, { target := 227, numerator := 1408168364485003093328527360 }, { target := 228, numerator := 28163367289700061866570547200 }, { target := 229, numerator := 1458460091788038918090260480 }, { target := 230, numerator := 26201989924881664700862955520 }, { target := 231, numerator := 39227547296367943314151833600 }, { target := 232, numerator := 1408168364485003093328527360 }, { target := 233, numerator := 39277839023670979138913566720 }, { target := 234, numerator := 39277839023670979138913566720 }, { target := 235, numerator := 28113075562397026041808814080 }, { target := 236, numerator := 1458460091788038918090260480 }, { target := 263, numerator := 894291069143714757875859456 }, { target := 265, numerator := 894291069143714757875859456 }, { target := 302, numerator := 14497638539098344664292392960 }, { target := 303, numerator := 289952770781966893285847859200 }, { target := 304, numerator := 15015411344066142688017121280 }, { target := 305, numerator := 269759631388222770360583454720 }, { target := 306, numerator := 403862787874882458505288089600 }, { target := 307, numerator := 14497638539098344664292392960 }, { target := 308, numerator := 404380560679850256529012817920 }, { target := 309, numerator := 404380560679850256529012817920 }, { target := 310, numerator := 289434997976999095262123130880 }, { target := 311, numerator := 15015411344066142688017121280 }, { target := 338, numerator := 177369074587951044827598028800 }, { target := 340, numerator := 177369074587951044827598028800 }, { target := 589, numerator := 1408168364485003093328527360 }, { target := 590, numerator := 28163367289700061866570547200 }, { target := 591, numerator := 1458460091788038918090260480 }, { target := 592, numerator := 26201989924881664700862955520 }, { target := 593, numerator := 39227547296367943314151833600 }, { target := 594, numerator := 1408168364485003093328527360 }, { target := 595, numerator := 39277839023670979138913566720 }, { target := 596, numerator := 39277839023670979138913566720 }, { target := 597, numerator := 28113075562397026041808814080 }, { target := 598, numerator := 1458460091788038918090260480 }, { target := 599, numerator := 177369074587951044827598028800 }, { target := 601, numerator := 177369074587951044827598028800 }, { target := 763, numerator := 8592640963486498819145728 }, { target := 764, numerator := 171852819269729976382914560 }, { target := 765, numerator := 8899520997896730919829504 }, { target := 766, numerator := 159884497927730924456247296 }, { target := 767, numerator := 239366426839981038533345280 }, { target := 768, numerator := 8592640963486498819145728 }, { target := 769, numerator := 239673306874391270634029056 }, { target := 770, numerator := 239673306874391270634029056 }, { target := 771, numerator := 171545939235319744282230784 }, { target := 772, numerator := 8899520997896730919829504 }, { target := 773, numerator := 894291069143714757875859456 }, { target := 775, numerator := 894291069143714757875859456 }]

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
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 10713313065377846341234851840 }, { target := 81, numerator := 12201273213346991666406359040 }, { target := 82, numerator := 9522944947002530081097646080 }, { target := 83, numerator := 127666980695752668899715317760 }, { target := 84, numerator := 11308497124565504471303454720 }, { target := 85, numerator := 9522944947002530081097646080 }, { target := 86, numerator := 11308497124565504471303454720 }, { target := 87, numerator := 11010905094971675406269153280 }, { target := 88, numerator := 416033657372173032917953413120 }, { target := 89, numerator := 11010905094971675406269153280 }, { target := 90, numerator := 127666980695752668899715317760 }, { target := 91, numerator := 416033657372173032917953413120 }, { target := 92, numerator := 10713313065377846341234851840 }, { target := 93, numerator := 11010905094971675406269153280 }, { target := 94, numerator := 11010905094971675406269153280 }, { target := 95, numerator := 12201273213346991666406359040 }, { target := 176, numerator := 419277268678483174057008168960 }, { target := 177, numerator := 477510222661605837120481525760 }, { target := 178, numerator := 372690905491985043606229483520 }, { target := 179, numerator := 4996387451751924490846014013440 }, { target := 180, numerator := 442570450271732239282397511680 }, { target := 181, numerator := 372690905491985043606229483520 }, { target := 182, numerator := 442570450271732239282397511680 }, { target := 183, numerator := 430923859475107706669702840320 }, { target := 184, numerator := 16281933933681096592547150561280 }, { target := 185, numerator := 430923859475107706669702840320 }, { target := 186, numerator := 4996387451751924490846014013440 }, { target := 187, numerator := 16281933933681096592547150561280 }, { target := 188, numerator := 419277268678483174057008168960 }, { target := 189, numerator := 430923859475107706669702840320 }, { target := 190, numerator := 430923859475107706669702840320 }, { target := 191, numerator := 477510222661605837120481525760 }, { target := 286, numerator := 419277422455153458518257827840 }, { target := 287, numerator := 477510397796146994423571415040 }, { target := 288, numerator := 372691042182358629794006958080 }, { target := 289, numerator := 4996389284257245380675905781760 }, { target := 290, numerator := 442570612591550872880383262720 }, { target := 291, numerator := 372691042182358629794006958080 }, { target := 292, numerator := 442570612591550872880383262720 }, { target := 293, numerator := 430924017523352165699320545280 }, { target := 294, numerator := 16281939905341792639125678981120 }, { target := 295, numerator := 430924017523352165699320545280 }, { target := 296, numerator := 4996389284257245380675905781760 }, { target := 297, numerator := 16281939905341792639125678981120 }, { target := 298, numerator := 419277422455153458518257827840 }, { target := 299, numerator := 430924017523352165699320545280 }, { target := 300, numerator := 430924017523352165699320545280 }, { target := 301, numerator := 477510397796146994423571415040 }, { target := 573, numerator := 10713466842048130802484510720 }, { target := 574, numerator := 12201448347888148969496248320 }, { target := 575, numerator := 9523081637376116268875120640 }, { target := 576, numerator := 127668813201073558729607086080 }, { target := 577, numerator := 11308659444384138069289205760 }, { target := 578, numerator := 9523081637376116268875120640 }, { target := 579, numerator := 11308659444384138069289205760 }, { target := 580, numerator := 11011063143216134435886858240 }, { target := 581, numerator := 416039629032869079496481832960 }, { target := 582, numerator := 11011063143216134435886858240 }, { target := 583, numerator := 127668813201073558729607086080 }, { target := 584, numerator := 416039629032869079496481832960 }, { target := 585, numerator := 10713466842048130802484510720 }, { target := 586, numerator := 11011063143216134435886858240 }, { target := 587, numerator := 11011063143216134435886858240 }, { target := 588, numerator := 12201448347888148969496248320 }]

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
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 27782778972805210004369965056 }, { target := 27, numerator := 416741684592078150065549475840 }, { target := 28, numerator := 731613179617203863448409079808 }, { target := 29, numerator := 27782778972805210004369965056 }, { target := 30, numerator := 463046316213420166739499417600 }, { target := 31, numerator := 27782778972805210004369965056 }, { target := 32, numerator := 731613179617203863448409079808 }, { target := 33, numerator := 726982716455069661781014085632 }, { target := 34, numerator := 463046316213420166739499417600 }, { target := 35, numerator := 11219612241851170640098070888448 }, { target := 36, numerator := 717721790130801258446224097280 }, { target := 37, numerator := 416741684592078150065549475840 }, { target := 38, numerator := 731613179617203863448409079808 }, { target := 39, numerator := 27782778972805210004369965056 }, { target := 40, numerator := 717721790130801258446224097280 }, { target := 41, numerator := 27782778972805210004369965056 }, { target := 42, numerator := 731613179617203863448409079808 }, { target := 43, numerator := 731613179617203863448409079808 }, { target := 44, numerator := 27782778972805210004369965056 }, { target := 131, numerator := 3201090113583176400607641600 }, { target := 134, numerator := 11692040267096500564131840000 }, { target := 136, numerator := 3201089035083655636058112000 }, { target := 227, numerator := 1031139498383683671918064435200 }, { target := 230, numerator := 3766255902930691689000468480000 }, { target := 232, numerator := 1031139150975952121562660864000 }, { target := 263, numerator := 12464276360975953432657526784 }, { target := 265, numerator := 12464279332691367201821687808 }, { target := 302, numerator := 10966602188706687202972202434560 }, { target := 305, numerator := 40055715345064281490424070144000 }, { target := 307, numerator := 10966598493879367363355423539200 }, { target := 338, numerator := 2186116971318519615522877734912 }, { target := 340, numerator := 2186117492529483800284332294144 }, { target := 356, numerator := 1798881619586568211962789888 }, { target := 572, numerator := 43579357945468152489808232448 }, { target := 589, numerator := 1031142606238162878885443665920 }, { target := 592, numerator := 3766267254426096637059268608000 }, { target := 594, numerator := 1031142258829384241616676454400 }, { target := 599, numerator := 2186117233409828171065772212224 }, { target := 601, numerator := 2186117754620854843272056537088 }, { target := 617, numerator := 33018181985314752019575078912 }, { target := 622, numerator := 36790030542512395044658348032 }, { target := 712, numerator := 1798881619586568211962789888 }, { target := 757, numerator := 36790030542512395044658348032 }, { target := 762, numerator := 36732002103170892844272451584 }, { target := 763, numerator := 3201090113583176400607641600 }, { target := 766, numerator := 11692040267096500564131840000 }, { target := 768, numerator := 3201089035083655636058112000 }, { target := 773, numerator := 12464014269667397889763049472 }, { target := 775, numerator := 12464017241320324214097444864 }, { target := 777, numerator := 1798881619586568211962789888 }, { target := 782, numerator := 43579357945468152489808232448 }, { target := 783, numerator := 1798881619586568211962789888 }]

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
    Slot9.Left3.expected,
    Slot9.Left5.expected,
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
  [{ target := 80, numerator := 81270317027361368942428815360 }, { target := 82, numerator := 3169979940969447330513325916160 }, { target := 85, numerator := 3169978778231885716850548408320 }, { target := 92, numerator := 81270704606548573496687984640 }, { target := 131, numerator := 30964779609242877226175692800 }, { target := 134, numerator := 111379391426218021741815398400 }, { target := 136, numerator := 30964789939261932516566630400 }, { target := 157, numerator := 103206100337800264681059778560 }, { target := 158, numerator := 1548091505067003970215896678400 }, { target := 159, numerator := 2717760642228740303267907502080 }, { target := 160, numerator := 103206100337800264681059778560 }, { target := 161, numerator := 1720101672296671078017662976000 }, { target := 162, numerator := 103206100337800264681059778560 }, { target := 163, numerator := 2717760642228740303267907502080 }, { target := 164, numerator := 2700559625505773592487730872320 }, { target := 165, numerator := 1720101672296671078017662976000 }, { target := 166, numerator := 41678063519748340220367973908480 }, { target := 167, numerator := 2666157592059840170927377612800 }, { target := 168, numerator := 1548091505067003970215896678400 }, { target := 169, numerator := 2717760642228740303267907502080 }, { target := 170, numerator := 103206100337800264681059778560 }, { target := 171, numerator := 2666157592059840170927377612800 }, { target := 172, numerator := 103206100337800264681059778560 }, { target := 173, numerator := 2717760642228740303267907502080 }, { target := 174, numerator := 2717760642228740303267907502080 }, { target := 175, numerator := 103206100337800264681059778560 }, { target := 176, numerator := 3180510610096985783832126947328 }, { target := 178, numerator := 124057038348374764105890338439168 }, { target := 181, numerator := 124056992844686742001719114203136 }, { target := 188, numerator := 3180525777992993151889201692672 }, { target := 227, numerator := 3659838148698285322579791052800 }, { target := 230, numerator := 13164328984883043089198245478400 }, { target := 232, numerator := 3659839369640216523891435110400 }, { target := 267, numerator := 27776930727744545570382938112 }, { target := 268, numerator := 416653960916168183555744071680 }, { target := 269, numerator := 731459175830606366686750703616 }, { target := 270, numerator := 27776930727744545570382938112 }, { target := 271, numerator := 462948845462409092839715635200 }, { target := 272, numerator := 27776930727744545570382938112 }, { target := 273, numerator := 731459175830606366686750703616 }, { target := 274, numerator := 726829687375982275758353547264 }, { target := 275, numerator := 462948845462409092839715635200 }, { target := 276, numerator := 11217250525554172319506309840896 }, { target := 277, numerator := 717570710466734093901559234560 }, { target := 278, numerator := 416653960916168183555744071680 }, { target := 279, numerator := 731459175830606366686750703616 }, { target := 280, numerator := 27776930727744545570382938112 }, { target := 281, numerator := 717570710466734093901559234560 }, { target := 282, numerator := 27776930727744545570382938112 }, { target := 283, numerator := 731459175830606366686750703616 }, { target := 284, numerator := 731459175830606366686750703616 }, { target := 285, numerator := 27776930727744545570382938112 }, { target := 286, numerator := 3180510610096985783832126947328 }, { target := 288, numerator := 124057038348374764105890338439168 }, { target := 291, numerator := 124056992844686742001719114203136 }, { target := 298, numerator := 3180525777992993151889201692672 }, { target := 302, numerator := 34731134491300292047384923340800 }, { target := 305, numerator := 124926857933407449538586109542400 }, { target := 307, numerator := 34731146077795840683319649894400 }, { target := 573, numerator := 81270317027361368942428815360 }, { target := 575, numerator := 3169979940969447330513325916160 }, { target := 578, numerator := 3169978778231885716850548408320 }, { target := 585, numerator := 81270704606548573496687984640 }]

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
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected,
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected,
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 89131693453871966249438674944 }, { target := 11, numerator := 66848770090403974687079006208 }, { target := 12, numerator := 70562590650981973280805617664 }, { target := 13, numerator := 90988603734160965546301980672 }, { target := 14, numerator := 1218133143869583538742328557568 }, { target := 15, numerator := 2129876091491482193502211670016 }, { target := 16, numerator := 64991859810114975390215700480 }, { target := 17, numerator := 1218133143869583538742328557568 }, { target := 18, numerator := 68705680370692973983942311936 }, { target := 19, numerator := 70562590650981973280805617664 }, { target := 20, numerator := 70562590650981973280805617664 }, { target := 21, numerator := 68705680370692973983942311936 }, { target := 22, numerator := 2129876091491482193502211670016 }, { target := 23, numerator := 68705680370692973983942311936 }, { target := 24, numerator := 89131693453871966249438674944 }, { target := 25, numerator := 90988603734160965546301980672 }, { target := 263, numerator := 87739010743655216776791195648 }, { target := 265, numerator := 87738989825047437190159663104 }, { target := 338, numerator := 65804258057741412582593396736 }, { target := 340, numerator := 65804242368785577892619747328 }, { target := 352, numerator := 69460050172060379948293029888 }, { target := 354, numerator := 69460033611495887775543066624 }, { target := 479, numerator := 89566906800814700459641012224 }, { target := 481, numerator := 89566885446402592131621322752 }, { target := 554, numerator := 1199099813496621295949479673856 }, { target := 556, numerator := 1199099527608981641598848729088 }, { target := 568, numerator := 2096596777561927784228739612672 }, { target := 570, numerator := 2096596277694362717856523616256 }, { target := 589, numerator := 3659840658813363892851939737600 }, { target := 592, numerator := 13164338013692335097792744652800 }, { target := 594, numerator := 3659841879756132482219297996800 }, { target := 599, numerator := 63976362000581928899743580160 }, { target := 601, numerator := 63976346747430422951158087680 }, { target := 613, numerator := 1199099813496621295949479673856 }, { target := 615, numerator := 1199099527608981641598848729088 }, { target := 618, numerator := 67632154114900896265443213312 }, { target := 620, numerator := 67632137990140732834081406976 }, { target := 694, numerator := 69460050172060379948293029888 }, { target := 696, numerator := 69460033611495887775543066624 }, { target := 708, numerator := 69460050172060379948293029888 }, { target := 710, numerator := 69460033611495887775543066624 }, { target := 739, numerator := 67632154114900896265443213312 }, { target := 741, numerator := 67632137990140732834081406976 }, { target := 753, numerator := 2096596777561927784228739612672 }, { target := 755, numerator := 2096596277694362717856523616256 }, { target := 758, numerator := 67632154114900896265443213312 }, { target := 760, numerator := 67632137990140732834081406976 }, { target := 763, numerator := 30964779609242877226175692800 }, { target := 766, numerator := 111379391426218021741815398400 }, { target := 768, numerator := 30964789939261932516566630400 }, { target := 773, numerator := 87739010743655216776791195648 }, { target := 775, numerator := 87738989825047437190159663104 }, { target := 778, numerator := 89566906800814700459641012224 }, { target := 780, numerator := 89566885446402592131621322752 }]

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
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot16.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 30964779609242877226175692800 }, { target := 27, numerator := 3659838148698285322579791052800 }, { target := 29, numerator := 34731134491300292047384923340800 }, { target := 37, numerator := 3659840658813363892851939737600 }, { target := 44, numerator := 30964779609242877226175692800 }, { target := 80, numerator := 81554047642362782343411793920 }, { target := 82, numerator := 3191614396379959474334273110016 }, { target := 85, numerator := 3191614396379959474334273110016 }, { target := 92, numerator := 81554047642362782343411793920 }, { target := 131, numerator := 27599997532194649412235952128 }, { target := 134, numerator := 102527112835577894518684385280 }, { target := 136, numerator := 27594187762430436717946208256 }, { target := 141, numerator := 89131672203222793336035213312 }, { target := 142, numerator := 66848754152417095002026409984 }, { target := 143, numerator := 70562573827551378057694543872 }, { target := 144, numerator := 90988582040789934863869280256 }, { target := 145, numerator := 1218132853444044842259147915264 }, { target := 146, numerator := 2129875583689511332425674784768 }, { target := 147, numerator := 64991844314849953474192343040 }, { target := 148, numerator := 1218132853444044842259147915264 }, { target := 149, numerator := 68705663989984236529860476928 }, { target := 150, numerator := 70562573827551378057694543872 }, { target := 151, numerator := 70562573827551378057694543872 }, { target := 152, numerator := 68705663989984236529860476928 }, { target := 153, numerator := 2129875583689511332425674784768 }, { target := 154, numerator := 68705663989984236529860476928 }, { target := 155, numerator := 89131672203222793336035213312 }, { target := 156, numerator := 90988582040789934863869280256 }, { target := 157, numerator := 111379391426218021741815398400 }, { target := 158, numerator := 13164328984883043089198245478400 }, { target := 160, numerator := 124926857933407449538586109542400 }, { target := 168, numerator := 13164338013692335097792744652800 }, { target := 175, numerator := 111379391426218021741815398400 }, { target := 176, numerator := 3181046962621283591685427691520 }, { target := 178, numerator := 124490145798589187234978905194496 }, { target := 181, numerator := 124490145798589187234978905194496 }, { target := 188, numerator := 3181046962621283591685427691520 }, { target := 227, numerator := 413999962982919741183539281920 }, { target := 230, numerator := 1537906692533668417780265779200 }, { target := 232, numerator := 413912816436456550769193123840 }, { target := 253, numerator := 726799935014459101188880072704 }, { target := 256, numerator := 2699880638003551222325355479040 }, { target := 258, numerator := 726646944410668166905916817408 }, { target := 267, numerator := 30964789939261932516566630400 }, { target := 268, numerator := 3659839369640216523891435110400 }, { target := 270, numerator := 34731146077795840683319649894400 }, { target := 278, numerator := 3659841879756132482219297996800 }, { target := 285, numerator := 30964789939261932516566630400 }, { target := 286, numerator := 3181045795824377121144349655040 }, { target := 288, numerator := 124490100136038866328683221614592 }, { target := 291, numerator := 124490100136038866328683221614592 }, { target := 298, numerator := 3181045795824377121144349655040 }, { target := 302, numerator := 27599997532194649412235952128 }, { target := 305, numerator := 102527112835577894518684385280 }, { target := 307, numerator := 27594187762430436717946208256 }, { target := 328, numerator := 459999958869910823537265868800 }, { target := 331, numerator := 1708785213926298241978073088000 }, { target := 333, numerator := 459903129373840611965770137600 }, { target := 573, numerator := 81554436574664939190437806080 }, { target := 575, numerator := 3191629617230066443099500969984 }, { target := 578, numerator := 3191629617230066443099500969984 }, { target := 585, numerator := 81554436574664939190437806080 }]

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
    Slot16.Left5.expected,
    Slot16.Left6.expected,
    Slot16.Left7.expected,
    Slot16.Left8.expected,
    Slot16.Left9.expected,
    Slot16.Left10.expected,
    Slot16.Left11.expected,
    Slot16.Left12.expected,
    Slot16.Left13.expected,
    Slot16.Left14.expected,
    Slot16.Left15.expected,
    Slot16.Left16.expected,
    Slot16.Left17.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1798881619586568211962789888 }, { target := 1, numerator := 43579357945468152489808232448 }, { target := 2, numerator := 33018181985314752019575078912 }, { target := 3, numerator := 36790030542512395044658348032 }, { target := 4, numerator := 1798881619586568211962789888 }, { target := 5, numerator := 36790030542512395044658348032 }, { target := 6, numerator := 36732002103170892844272451584 }, { target := 7, numerator := 1798881619586568211962789888 }, { target := 8, numerator := 43579357945468152489808232448 }, { target := 9, numerator := 1798881619586568211962789888 }, { target := 10, numerator := 11902822470841901476231512064 }, { target := 11, numerator := 2087643233871739452661486845952 }, { target := 16, numerator := 2087643484157133208405151842304 }, { target := 24, numerator := 11902572185448145732566515712 }, { target := 141, numerator := 11902825308696260571108999168 }, { target := 142, numerator := 2087643731604732277749002010624 }, { target := 147, numerator := 2087643981890185706187729666048 }, { target := 155, numerator := 11902575023242832132381343744 }, { target := 342, numerator := 27599997532194649412235952128 }, { target := 345, numerator := 102527112835577894518684385280 }, { target := 347, numerator := 27594187762430436717946208256 }, { target := 443, numerator := 726799935014459101188880072704 }, { target := 446, numerator := 2699880638003551222325355479040 }, { target := 448, numerator := 726646944410668166905916817408 }, { target := 469, numerator := 722199935425759992953507414016 }, { target := 472, numerator := 2682792785864288239905574748160 }, { target := 474, numerator := 722047913116929760786259116032 }, { target := 518, numerator := 459999958869910823537265868800 }, { target := 521, numerator := 1708785213926298241978073088000 }, { target := 523, numerator := 459903129373840611965770137600 }, { target := 544, numerator := 11145799003417939254307952001024 }, { target := 547, numerator := 41403865733434206403128710922240 }, { target := 549, numerator := 11143452824728158027930610434048 }, { target := 558, numerator := 712999936248361776482762096640 }, { target := 561, numerator := 2648617081585762275066013286400 }, { target := 563, numerator := 712849850529452948546943713280 }, { target := 589, numerator := 413999962982919741183539281920 }, { target := 592, numerator := 1537906692533668417780265779200 }, { target := 594, numerator := 413912816436456550769193123840 }, { target := 603, numerator := 726799935014459101188880072704 }, { target := 606, numerator := 2699880638003551222325355479040 }, { target := 608, numerator := 726646944410668166905916817408 }, { target := 658, numerator := 27599997532194649412235952128 }, { target := 661, numerator := 102527112835577894518684385280 }, { target := 663, numerator := 27594187762430436717946208256 }, { target := 684, numerator := 712999936248361776482762096640 }, { target := 687, numerator := 2648617081585762275066013286400 }, { target := 689, numerator := 712849850529452948546943713280 }, { target := 698, numerator := 27599997532194649412235952128 }, { target := 701, numerator := 102527112835577894518684385280 }, { target := 703, numerator := 27594187762430436717946208256 }, { target := 729, numerator := 726799935014459101188880072704 }, { target := 732, numerator := 2699880638003551222325355479040 }, { target := 734, numerator := 726646944410668166905916817408 }, { target := 743, numerator := 726799935014459101188880072704 }, { target := 746, numerator := 2699880638003551222325355479040 }, { target := 748, numerator := 726646944410668166905916817408 }, { target := 763, numerator := 27599997532194649412235952128 }, { target := 766, numerator := 102527112835577894518684385280 }, { target := 768, numerator := 27594187762430436717946208256 }]

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
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 3225184340244555147708989440 }, { target := 27, numerator := 1038900763425281290954006855680 }, { target := 29, numerator := 11049146506256092375467692130304 }, { target := 37, numerator := 1038903894672213567221140553728 }, { target := 44, numerator := 3225184340244555147708989440 }, { target := 80, numerator := 10826084781855507881668902912 }, { target := 82, numerator := 423690713611940891678660886528 }, { target := 85, numerator := 423690869007312968607923699712 }, { target := 92, numerator := 10826240177227584810931716096 }, { target := 115, numerator := 12329707668224328420789583872 }, { target := 117, numerator := 482536646058043793300697120768 }, { target := 120, numerator := 482536823036106436470135324672 }, { target := 127, numerator := 12329884646286971590227787776 }, { target := 157, numerator := 11780044871257441966227456000 }, { target := 158, numerator := 3794604065640922701713375232000 }, { target := 160, numerator := 40357209976693797587663821209600 }, { target := 168, numerator := 3794615502577690912822080307200 }, { target := 175, numerator := 11780044871257441966227456000 }, { target := 176, numerator := 9623186472760451450372358144 }, { target := 178, numerator := 376613967655058570381031899136 }, { target := 181, numerator := 376614105784278194318154399744 }, { target := 188, numerator := 9623324601980075387494858752 }, { target := 211, numerator := 129010843650444802256554426368 }, { target := 213, numerator := 5048981003875628959170708897792 }, { target := 216, numerator := 5048982855670479542577757421568 }, { target := 223, numerator := 129012695445295385663602950144 }, { target := 237, numerator := 11427533936403036097317175296 }, { target := 239, numerator := 447229086590382052327475380224 }, { target := 242, numerator := 447229250618830355752808349696 }, { target := 249, numerator := 11427697964851339522650144768 }, { target := 267, numerator := 3225183253627296054824140800 }, { target := 268, numerator := 1038900413402652836456143257600 }, { target := 270, numerator := 11049142783618244322004335329280 }, { target := 278, numerator := 1038903544648530144510565416960 }, { target := 285, numerator := 3225183253627296054824140800 }, { target := 286, numerator := 9623186472760451450372358144 }, { target := 288, numerator := 376613967655058570381031899136 }, { target := 291, numerator := 376614105784278194318154399744 }, { target := 298, numerator := 9623324601980075387494858752 }, { target := 312, numerator := 11427533936403036097317175296 }, { target := 314, numerator := 447229086590382052327475380224 }, { target := 317, numerator := 447229250618830355752808349696 }, { target := 324, numerator := 11427697964851339522650144768 }, { target := 392, numerator := 11126809359129271989493039104 }, { target := 394, numerator := 435459900101161472003068133376 }, { target := 397, numerator := 435460059813071662180366024704 }, { target := 404, numerator := 11126969071039462166790930432 }, { target := 427, numerator := 420412959028722222738142396416 }, { target := 429, numerator := 16453322711930371293521331093504 }, { target := 432, numerator := 16453328746450653614274370338816 }, { target := 439, numerator := 420418993549004543491181641728 }, { target := 453, numerator := 11126809359129271989493039104 }, { target := 455, numerator := 435459900101161472003068133376 }, { target := 458, numerator := 435460059813071662180366024704 }, { target := 465, numerator := 11126969071039462166790930432 }, { target := 502, numerator := 129010843650444802256554426368 }, { target := 504, numerator := 5048981003875628959170708897792 }, { target := 507, numerator := 5048982855670479542577757421568 }, { target := 514, numerator := 129012695445295385663602950144 }, { target := 528, numerator := 420412959028722222738142396416 }, { target := 530, numerator := 16453322711930371293521331093504 }, { target := 533, numerator := 16453328746450653614274370338816 }, { target := 540, numerator := 420418993549004543491181641728 }]

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
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 894291069143714757875859456 }, { target := 11, numerator := 177369074587951044827598028800 }, { target := 16, numerator := 177369074587951044827598028800 }, { target := 24, numerator := 894291069143714757875859456 }, { target := 26, numerator := 8861160993595451907244032 }, { target := 27, numerator := 1452173625875159439995043840 }, { target := 29, numerator := 14950689743445167935051530240 }, { target := 37, numerator := 1452173625875159439995043840 }, { target := 44, numerator := 8861160993595451907244032 }, { target := 61, numerator := 177223219871909038144880640 }, { target := 62, numerator := 29043472517503188799900876800 }, { target := 64, numerator := 299013794868903358701030604800 }, { target := 72, numerator := 29043472517503188799900876800 }, { target := 79, numerator := 177223219871909038144880640 }, { target := 96, numerator := 9177631029081003761074176 }, { target := 97, numerator := 1504036969656415134280581120 }, { target := 99, numerator := 15484642948568209647017656320 }, { target := 107, numerator := 1504036969656415134280581120 }, { target := 114, numerator := 9177631029081003761074176 }, { target := 141, numerator := 894291069143714757875859456 }, { target := 142, numerator := 177369074587951044827598028800 }, { target := 147, numerator := 177369074587951044827598028800 }, { target := 155, numerator := 894291069143714757875859456 }, { target := 157, numerator := 164880888487972515845505024 }, { target := 158, numerator := 27020802110034216722764922880 }, { target := 160, numerator := 278189619869104731934351687680 }, { target := 168, numerator := 27020802110034216722764922880 }, { target := 175, numerator := 164880888487972515845505024 }, { target := 192, numerator := 246846627678730445987512320 }, { target := 193, numerator := 40453408149379441542719078400 }, { target := 195, numerator := 416483499995972535333578342400 }, { target := 203, numerator := 40453408149379441542719078400 }, { target := 210, numerator := 246846627678730445987512320 }, { target := 267, numerator := 8861160993595451907244032 }, { target := 268, numerator := 1452173625875159439995043840 }, { target := 270, numerator := 14950689743445167935051530240 }, { target := 278, numerator := 1452173625875159439995043840 }, { target := 285, numerator := 8861160993595451907244032 }, { target := 373, numerator := 247163097714215997841342464 }, { target := 374, numerator := 40505271493160697237004615680 }, { target := 376, numerator := 417017453201095577045544468480 }, { target := 384, numerator := 40505271493160697237004615680 }, { target := 391, numerator := 247163097714215997841342464 }, { target := 408, numerator := 247163097714215997841342464 }, { target := 409, numerator := 40505271493160697237004615680 }, { target := 411, numerator := 417017453201095577045544468480 }, { target := 419, numerator := 40505271493160697237004615680 }, { target := 426, numerator := 247163097714215997841342464 }, { target := 573, numerator := 10826084781855507881668902912 }, { target := 575, numerator := 423690713611940891678660886528 }, { target := 578, numerator := 423690869007312968607923699712 }, { target := 585, numerator := 10826240177227584810931716096 }, { target := 642, numerator := 11126809359129271989493039104 }, { target := 644, numerator := 435459900101161472003068133376 }, { target := 647, numerator := 435460059813071662180366024704 }, { target := 654, numerator := 11126969071039462166790930432 }, { target := 668, numerator := 11126809359129271989493039104 }, { target := 670, numerator := 435459900101161472003068133376 }, { target := 673, numerator := 435460059813071662180366024704 }, { target := 680, numerator := 11126969071039462166790930432 }, { target := 713, numerator := 12329707668224328420789583872 }, { target := 715, numerator := 482536646058043793300697120768 }, { target := 718, numerator := 482536823036106436470135324672 }, { target := 725, numerator := 12329884646286971590227787776 }]

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
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 216624395302196365242662912 }, { target := 11, numerator := 161316039054827080499855360 }, { target := 12, numerator := 170534098429388627956989952 }, { target := 13, numerator := 221233424989477138971230208 }, { target := 14, numerator := 2963606088921537507468771328 }, { target := 15, numerator := 5360301526307539846323765248 }, { target := 16, numerator := 161316039054827080499855360 }, { target := 17, numerator := 2963606088921537507468771328 }, { target := 18, numerator := 175143128116669401685557248 }, { target := 19, numerator := 175143128116669401685557248 }, { target := 20, numerator := 170534098429388627956989952 }, { target := 21, numerator := 170534098429388627956989952 }, { target := 22, numerator := 5360301526307539846323765248 }, { target := 23, numerator := 170534098429388627956989952 }, { target := 24, numerator := 216624395302196365242662912 }, { target := 25, numerator := 221233424989477138971230208 }, { target := 45, numerator := 237931712872904204446859264 }, { target := 46, numerator := 177183190437269088417873920 }, { target := 47, numerator := 187307944176541607756038144 }, { target := 48, numerator := 242994089742540464115941376 }, { target := 49, numerator := 3255108327176114967219798016 }, { target := 50, numerator := 5887544299386969995142496256 }, { target := 51, numerator := 177183190437269088417873920 }, { target := 52, numerator := 3255108327176114967219798016 }, { target := 53, numerator := 192370321046177867425120256 }, { target := 54, numerator := 192370321046177867425120256 }, { target := 55, numerator := 187307944176541607756038144 }, { target := 56, numerator := 187307944176541607756038144 }, { target := 57, numerator := 5887544299386969995142496256 }, { target := 58, numerator := 187307944176541607756038144 }, { target := 59, numerator := 237931712872904204446859264 }, { target := 60, numerator := 242994089742540464115941376 }, { target := 141, numerator := 216624395302196365242662912 }, { target := 142, numerator := 161316039054827080499855360 }, { target := 143, numerator := 170534098429388627956989952 }, { target := 144, numerator := 221233424989477138971230208 }, { target := 145, numerator := 2963606088921537507468771328 }, { target := 146, numerator := 5360301526307539846323765248 }, { target := 147, numerator := 161316039054827080499855360 }, { target := 148, numerator := 2963606088921537507468771328 }, { target := 149, numerator := 175143128116669401685557248 }, { target := 150, numerator := 175143128116669401685557248 }, { target := 151, numerator := 170534098429388627956989952 }, { target := 152, numerator := 170534098429388627956989952 }, { target := 153, numerator := 5360301526307539846323765248 }, { target := 154, numerator := 170534098429388627956989952 }, { target := 155, numerator := 216624395302196365242662912 }, { target := 156, numerator := 221233424989477138971230208 }, { target := 483, numerator := 176906749836423486291050496 }, { target := 484, numerator := 28991609173721933105615339520 }, { target := 486, numerator := 298479841663780316989064478720 }, { target := 494, numerator := 28991609173721933105615339520 }, { target := 501, numerator := 176906749836423486291050496 }, { target := 623, numerator := 9177631029081003761074176 }, { target := 624, numerator := 1504036969656415134280581120 }, { target := 626, numerator := 15484642948568209647017656320 }, { target := 634, numerator := 1504036969656415134280581120 }, { target := 641, numerator := 9177631029081003761074176 }]

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
    Slot25.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 357, numerator := 237931712872904204446859264 }, { target := 358, numerator := 177183190437269088417873920 }, { target := 359, numerator := 187307944176541607756038144 }, { target := 360, numerator := 242994089742540464115941376 }, { target := 361, numerator := 3255108327176114967219798016 }, { target := 362, numerator := 5887544299386969995142496256 }, { target := 363, numerator := 177183190437269088417873920 }, { target := 364, numerator := 3255108327176114967219798016 }, { target := 365, numerator := 192370321046177867425120256 }, { target := 366, numerator := 192370321046177867425120256 }, { target := 367, numerator := 187307944176541607756038144 }, { target := 368, numerator := 187307944176541607756038144 }, { target := 369, numerator := 5887544299386969995142496256 }, { target := 370, numerator := 187307944176541607756038144 }, { target := 371, numerator := 237931712872904204446859264 }, { target := 372, numerator := 242994089742540464115941376 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent0
