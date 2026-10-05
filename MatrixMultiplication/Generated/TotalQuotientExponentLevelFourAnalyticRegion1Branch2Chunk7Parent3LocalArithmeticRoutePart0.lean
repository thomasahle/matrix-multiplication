import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent3

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 48769810688335386091727093760 }, { target := 134, numerator := 167418232656628274778548994048 }, { target := 136, numerator := 48769810688335386091727093760 }, { target := 227, numerator := 1300528285022276962446055833600 }, { target := 230, numerator := 4464486204176753994094639841280 }, { target := 232, numerator := 1300528285022276962446055833600 }, { target := 253, numerator := 1243630172552552345339040890880 }, { target := 256, numerator := 4269164932744021006852999348224 }, { target := 258, numerator := 1243630172552552345339040890880 }, { target := 263, numerator := 107304255748994485546920181760 }, { target := 265, numerator := 107304255748994485546920181760 }, { target := 302, numerator := 40641508906946155076439244800 }, { target := 305, numerator := 139515193880523562315457495040 }, { target := 307, numerator := 40641508906946155076439244800 }, { target := 328, numerator := 1276143379678109269400192286720 }, { target := 331, numerator := 4380777087848439856705365344256 }, { target := 333, numerator := 1276143379678109269400192286720 }, { target := 338, numerator := 110370091627537185133975044096 }, { target := 340, numerator := 110370091627537185133975044096 }, { target := 342, numerator := 40641508906946155076439244800 }, { target := 345, numerator := 139515193880523562315457495040 }, { target := 347, numerator := 40641508906946155076439244800 }, { target := 352, numerator := 107304255748994485546920181760 }, { target := 354, numerator := 107304255748994485546920181760 }, { target := 356, numerator := 1450710983537555009647411200 }, { target := 443, numerator := 1243630172552552345339040890880 }, { target := 446, numerator := 4269164932744021006852999348224 }, { target := 448, numerator := 1243630172552552345339040890880 }, { target := 479, numerator := 95040912234823687198700732416 }, { target := 481, numerator := 95040912234823687198700732416 }, { target := 554, numerator := 4448527859765457100816605249536 }, { target := 556, numerator := 4448527859765457100816605249536 }, { target := 568, numerator := 1211005172024366336886670622720 }, { target := 570, numerator := 1211005172024366336886670622720 }, { target := 572, numerator := 29072248110092602393334120448 }, { target := 599, numerator := 110370091627537185133975044096 }, { target := 601, numerator := 110370091627537185133975044096 }, { target := 613, numerator := 4448527859765457100816605249536 }, { target := 615, numerator := 4448527859765457100816605249536 }, { target := 617, numerator := 48801917486203350524538912768 }, { target := 618, numerator := 107304255748994485546920181760 }, { target := 620, numerator := 107304255748994485546920181760 }, { target := 622, numerator := 46828950548592275711418433536 }, { target := 694, numerator := 107304255748994485546920181760 }, { target := 696, numerator := 107304255748994485546920181760 }, { target := 708, numerator := 91975076356280987611645870080 }, { target := 710, numerator := 91975076356280987611645870080 }, { target := 712, numerator := 1450710983537555009647411200 }, { target := 739, numerator := 107304255748994485546920181760 }, { target := 741, numerator := 107304255748994485546920181760 }, { target := 753, numerator := 1211005172024366336886670622720 }, { target := 755, numerator := 1211005172024366336886670622720 }, { target := 757, numerator := 46828950548592275711418433536 }, { target := 758, numerator := 91975076356280987611645870080 }, { target := 760, numerator := 91975076356280987611645870080 }, { target := 762, numerator := 31277328805069686007998185472 }, { target := 773, numerator := 107304255748994485546920181760 }, { target := 775, numerator := 107304255748994485546920181760 }, { target := 777, numerator := 1508739422879057210033307648 }, { target := 778, numerator := 95040912234823687198700732416 }, { target := 780, numerator := 95040912234823687198700732416 }, { target := 782, numerator := 29072248110092602393334120448 }, { target := 783, numerator := 1392682544196052809261514752 }]

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
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 7293314439568438257084530688 }, { target := 82, numerator := 274028559488034229213741449216 }, { target := 85, numerator := 274007834128345558763471634432 }, { target := 92, numerator := 7314039799257108707354345472 }, { target := 115, numerator := 7141370388744095793395269632 }, { target := 117, numerator := 268319631165366849438455169024 }, { target := 120, numerator := 268299337584005026289232642048 }, { target := 127, numerator := 7161663970105918942617796608 }, { target := 176, numerator := 5621929880500671156502659072 }, { target := 178, numerator := 211230347938693051685592367104 }, { target := 181, numerator := 211214372140599701546842718208 }, { target := 188, numerator := 5637905678594021295252307968 }, { target := 211, numerator := 176710931108710285270610608128 }, { target := 213, numerator := 6639483639262162678657943863296 }, { target := 216, numerator := 6638981481068039267539948142592 }, { target := 223, numerator := 177213089302833696388606328832 }, { target := 237, numerator := 5621929880500671156502659072 }, { target := 239, numerator := 211230347938693051685592367104 }, { target := 242, numerator := 211214372140599701546842718208 }, { target := 249, numerator := 5637905678594021295252307968 }, { target := 286, numerator := 5621929880500671156502659072 }, { target := 288, numerator := 211230347938693051685592367104 }, { target := 291, numerator := 211214372140599701546842718208 }, { target := 298, numerator := 5637905678594021295252307968 }, { target := 312, numerator := 5773873931325013620191920128 }, { target := 314, numerator := 216939276261360431460878647296 }, { target := 317, numerator := 216922868684940234021081710592 }, { target := 324, numerator := 5790281507745211059988856832 }, { target := 469, numerator := 707162254980863098330042859520 }, { target := 472, numerator := 2427564373521109984288960413696 }, { target := 474, numerator := 707162254980863098330042859520 }, { target := 518, numerator := 1276143379678109269400192286720 }, { target := 521, numerator := 4380777087848439856705365344256 }, { target := 523, numerator := 1276143379678109269400192286720 }, { target := 544, numerator := 19922467666185005218470517800960 }, { target := 547, numerator := 68390348040232650247037264068608 }, { target := 549, numerator := 19922467666185005218470517800960 }, { target := 558, numerator := 780316971013366177467633500160 }, { target := 561, numerator := 2678691722506052396456783904768 }, { target := 563, numerator := 780316971013366177467633500160 }, { target := 589, numerator := 1300528285022276962446055833600 }, { target := 592, numerator := 4464486204176753994094639841280 }, { target := 594, numerator := 1300528285022276962446055833600 }, { target := 603, numerator := 1243630172552552345339040890880 }, { target := 606, numerator := 4269164932744021006852999348224 }, { target := 608, numerator := 1243630172552552345339040890880 }, { target := 658, numerator := 40641508906946155076439244800 }, { target := 661, numerator := 139515193880523562315457495040 }, { target := 663, numerator := 40641508906946155076439244800 }, { target := 684, numerator := 780316971013366177467633500160 }, { target := 687, numerator := 2678691722506052396456783904768 }, { target := 689, numerator := 780316971013366177467633500160 }, { target := 698, numerator := 40641508906946155076439244800 }, { target := 701, numerator := 139515193880523562315457495040 }, { target := 703, numerator := 40641508906946155076439244800 }, { target := 729, numerator := 1251758474333941576354328739840 }, { target := 732, numerator := 4297067971520125719316090847232 }, { target := 734, numerator := 1251758474333941576354328739840 }, { target := 743, numerator := 707162254980863098330042859520 }, { target := 746, numerator := 2427564373521109984288960413696 }, { target := 748, numerator := 707162254980863098330042859520 }, { target := 763, numerator := 48769810688335386091727093760 }, { target := 766, numerator := 167418232656628274778548994048 }, { target := 768, numerator := 48769810688335386091727093760 }]

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
    Slot4.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 8457218803555378573344768 }, { target := 27, numerator := 1350171243103252033333886976 }, { target := 29, numerator := 13472678617460798439781564416 }, { target := 37, numerator := 1350171243103252033333886976 }, { target := 44, numerator := 8456253808256022642425856 }, { target := 61, numerator := 207338267442002829540065280 }, { target := 62, numerator := 33100972411563598236572712960 }, { target := 64, numerator := 330297927395813123039806095360 }, { target := 72, numerator := 33100972411563598236572712960 }, { target := 79, numerator := 207314609492728297040117760 }, { target := 96, numerator := 8457218803555378573344768 }, { target := 97, numerator := 1350171243103252033333886976 }, { target := 99, numerator := 13472678617460798439781564416 }, { target := 107, numerator := 1350171243103252033333886976 }, { target := 114, numerator := 8456253808256022642425856 }, { target := 157, numerator := 173782205737573424232923136 }, { target := 158, numerator := 27743841350218436943022129152 }, { target := 160, numerator := 276841815462017051810995372032 }, { target := 168, numerator := 27743841350218436943022129152 }, { target := 175, numerator := 173762376640615691071782912 }, { target := 192, numerator := 170781257129860225384316928 }, { target := 193, numerator := 27264748328472121705387524096 }, { target := 195, numerator := 272061187565498703977524494336 }, { target := 203, numerator := 27264748328472121705387524096 }, { target := 210, numerator := 170761770450589360456728576 }, { target := 392, numerator := 5773873931325013620191920128 }, { target := 394, numerator := 216939276261360431460878647296 }, { target := 397, numerator := 216922868684940234021081710592 }, { target := 404, numerator := 5790281507745211059988856832 }, { target := 427, numerator := 97700024680052204152194859008 }, { target := 429, numerator := 3670840911475125195509078163456 }, { target := 432, numerator := 3670563278010962380935672102912 }, { target := 439, numerator := 97977658144215018725600919552 }, { target := 453, numerator := 5318041778851986229124136960 }, { target := 455, numerator := 199812491293358292135019806720 }, { target := 458, numerator := 199797379051918636598364733440 }, { target := 465, numerator := 5333154020291641765779210240 }, { target := 502, numerator := 176710931108710285270610608128 }, { target := 504, numerator := 6639483639262162678657943863296 }, { target := 507, numerator := 6638981481068039267539948142592 }, { target := 514, numerator := 177213089302833696388606328832 }, { target := 528, numerator := 97700024680052204152194859008 }, { target := 530, numerator := 3670840911475125195509078163456 }, { target := 533, numerator := 3670563278010962380935672102912 }, { target := 540, numerator := 97977658144215018725600919552 }, { target := 573, numerator := 7293314439568438257084530688 }, { target := 575, numerator := 274028559488034229213741449216 }, { target := 578, numerator := 274007834128345558763471634432 }, { target := 585, numerator := 7314039799257108707354345472 }, { target := 642, numerator := 5621929880500671156502659072 }, { target := 644, numerator := 211230347938693051685592367104 }, { target := 647, numerator := 211214372140599701546842718208 }, { target := 654, numerator := 5637905678594021295252307968 }, { target := 668, numerator := 5318041778851986229124136960 }, { target := 670, numerator := 199812491293358292135019806720 }, { target := 673, numerator := 199797379051918636598364733440 }, { target := 680, numerator := 5333154020291641765779210240 }, { target := 713, numerator := 7141370388744095793395269632 }, { target := 715, numerator := 268319631165366849438455169024 }, { target := 718, numerator := 268299337584005026289232642048 }, { target := 725, numerator := 7161663970105918942617796608 }]

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
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 217819154022362385481728000 }, { target := 11, numerator := 169414897572948522041344000 }, { target := 12, numerator := 193617025797655453761536000 }, { target := 13, numerator := 227500005312245158169804800 }, { target := 14, numerator := 2686436232942469420941312000 }, { target := 15, numerator := 6040851204886850157359923200 }, { target := 16, numerator := 169414897572948522041344000 }, { target := 17, numerator := 2686436232942469420941312000 }, { target := 18, numerator := 193617025797655453761536000 }, { target := 19, numerator := 188776600152714067417497600 }, { target := 20, numerator := 188776600152714067417497600 }, { target := 21, numerator := 188776600152714067417497600 }, { target := 22, numerator := 6040851204886850157359923200 }, { target := 23, numerator := 188776600152714067417497600 }, { target := 24, numerator := 217819154022362385481728000 }, { target := 25, numerator := 227500005312245158169804800 }, { target := 45, numerator := 216331608580258447239413760 }, { target := 46, numerator := 168257917784645458963988480 }, { target := 47, numerator := 192294763182451953101701120 }, { target := 48, numerator := 225946346739381044894498816 }, { target := 49, numerator := 2668089839156520849286103040 }, { target := 50, numerator := 5999596611292500936773074944 }, { target := 51, numerator := 168257917784645458963988480 }, { target := 52, numerator := 2668089839156520849286103040 }, { target := 53, numerator := 192294763182451953101701120 }, { target := 54, numerator := 187487394102890654274158592 }, { target := 55, numerator := 187487394102890654274158592 }, { target := 56, numerator := 187487394102890654274158592 }, { target := 57, numerator := 5999596611292500936773074944 }, { target := 58, numerator := 187487394102890654274158592 }, { target := 59, numerator := 216331608580258447239413760 }, { target := 60, numerator := 225946346739381044894498816 }, { target := 267, numerator := 8457218803555378573344768 }, { target := 268, numerator := 1350171243103252033333886976 }, { target := 270, numerator := 13472678617460798439781564416 }, { target := 278, numerator := 1350171243103252033333886976 }, { target := 285, numerator := 8456253808256022642425856 }, { target := 373, numerator := 171054070639652334370553856 }, { target := 374, numerator := 27308302239539968545172488192 }, { target := 376, numerator := 272495790101545826507840028672 }, { target := 384, numerator := 27308302239539968545172488192 }, { target := 391, numerator := 171034552831500845058097152 }, { target := 408, numerator := 153321192503165250265153536 }, { target := 409, numerator := 24477298020129923959149821952 }, { target := 411, numerator := 244246625258482862037330296832 }, { target := 419, numerator := 24477298020129923959149821952 }, { target := 426, numerator := 153303698072254345969139712 }, { target := 483, numerator := 207338267442002829540065280 }, { target := 484, numerator := 33100972411563598236572712960 }, { target := 486, numerator := 330297927395813123039806095360 }, { target := 494, numerator := 33100972411563598236572712960 }, { target := 501, numerator := 207314609492728297040117760 }, { target := 623, numerator := 8457218803555378573344768 }, { target := 624, numerator := 1350171243103252033333886976 }, { target := 626, numerator := 13472678617460798439781564416 }, { target := 634, numerator := 1350171243103252033333886976 }, { target := 641, numerator := 8456253808256022642425856 }]

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
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 89877586632872728893224648704 }, { target := 82, numerator := 3257193489161819694729388883968 }, { target := 85, numerator := 3257194686167714759092543160320 }, { target := 92, numerator := 89876389626977664530070372352 }, { target := 131, numerator := 37827138835145763245940277248 }, { target := 134, numerator := 128223784640965581699041722368 }, { target := 136, numerator := 37827138835145763245940277248 }, { target := 141, numerator := 217819154022362385481728000 }, { target := 142, numerator := 169414897572948522041344000 }, { target := 143, numerator := 193617025797655453761536000 }, { target := 144, numerator := 227500005312245158169804800 }, { target := 145, numerator := 2686436232942469420941312000 }, { target := 146, numerator := 6040851204886850157359923200 }, { target := 147, numerator := 169414897572948522041344000 }, { target := 148, numerator := 2686436232942469420941312000 }, { target := 149, numerator := 193617025797655453761536000 }, { target := 150, numerator := 188776600152714067417497600 }, { target := 151, numerator := 188776600152714067417497600 }, { target := 152, numerator := 188776600152714067417497600 }, { target := 153, numerator := 6040851204886850157359923200 }, { target := 154, numerator := 188776600152714067417497600 }, { target := 155, numerator := 217819154022362385481728000 }, { target := 156, numerator := 227500005312245158169804800 }, { target := 176, numerator := 3145491448532200903179514150912 }, { target := 178, numerator := 113993651256162940420553917333504 }, { target := 181, numerator := 113993693148384881663418522664960 }, { target := 188, numerator := 3145449556310259660314908819456 }, { target := 227, numerator := 3966107283080283013443036905472 }, { target := 230, numerator := 13444032559400198149577115697152 }, { target := 232, numerator := 3966107283080283013443036905472 }, { target := 263, numerator := 24779508362734988892244541440 }, { target := 265, numerator := 24779508362734988892244541440 }, { target := 302, numerator := 42750672392039735609561972736000 }, { target := 305, numerator := 144913233695599778573190168576000 }, { target := 307, numerator := 42750672392039735609561972736000 }, { target := 338, numerator := 2074766798265269957336670142464 }, { target := 340, numerator := 2074766798265269957336670142464 }, { target := 357, numerator := 218456673497549787585576960 }, { target := 358, numerator := 169910746053649834788782080 }, { target := 359, numerator := 194183709775599811187179520 }, { target := 360, numerator := 228165858986329778144935936 }, { target := 361, numerator := 2694298973136447380222115840 }, { target := 362, numerator := 6058531744998714109040001024 }, { target := 363, numerator := 169910746053649834788782080 }, { target := 364, numerator := 2694298973136447380222115840 }, { target := 365, numerator := 194183709775599811187179520 }, { target := 366, numerator := 189329117031209815907500032 }, { target := 367, numerator := 189329117031209815907500032 }, { target := 368, numerator := 189329117031209815907500032 }, { target := 369, numerator := 6058531744998714109040001024 }, { target := 370, numerator := 189329117031209815907500032 }, { target := 371, numerator := 218456673497549787585576960 }, { target := 372, numerator := 228165858986329778144935936 }, { target := 589, numerator := 3966110308525283025101298597888 }, { target := 592, numerator := 13444042814841663475145515204608 }, { target := 594, numerator := 3966110308525283025101298597888 }, { target := 599, numerator := 2074767549121540733610259120128 }, { target := 601, numerator := 2074767549121540733610259120128 }, { target := 763, numerator := 37827138835145763245940277248 }, { target := 766, numerator := 128223784640965581699041722368 }, { target := 768, numerator := 37827138835145763245940277248 }, { target := 773, numerator := 24778757506464212618655563776 }, { target := 775, numerator := 24778757506464212618655563776 }]

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
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
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
  [{ target := 10, numerator := 1862658014612158826560880640 }, { target := 11, numerator := 156629500330788531228408545280 }, { target := 16, numerator := 156629462543313339778125004800 }, { target := 24, numerator := 1862695802087350276844421120 }, { target := 26, numerator := 5054402988777511529637478400 }, { target := 27, numerator := 746508870767721618566702694400 }, { target := 29, numerator := 7780737115040744555136679936000 }, { target := 37, numerator := 746508870767721618566702694400 }, { target := 44, numerator := 5054402988777511529637478400 }, { target := 80, numerator := 89670733729229753682883510272 }, { target := 82, numerator := 3138252112632241867729158537216 }, { target := 85, numerator := 3138253651825982311868034711552 }, { target := 92, numerator := 89669964132359531613445423104 }, { target := 131, numerator := 4998685160554767308050923520 }, { target := 134, numerator := 17090843238919397124513726464 }, { target := 136, numerator := 4998683545971516699268087808 }, { target := 141, numerator := 1861815762029335917738590208 }, { target := 142, numerator := 156558675949627324401467785216 }, { target := 147, numerator := 156558638179238789937427906560 }, { target := 155, numerator := 1861853532417870381778468864 }, { target := 157, numerator := 17281346268652575117939834880 }, { target := 158, numerator := 2552364407231020861331949486080 }, { target := 160, numerator := 26602867363153738490566619955200 }, { target := 168, numerator := 2552364407231020861331949486080 }, { target := 175, numerator := 17281346268652575117939834880 }, { target := 176, numerator := 3249697071465244735708147482624 }, { target := 178, numerator := 113731295326919757588745968156672 }, { target := 181, numerator := 113731351107810386216360695824384 }, { target := 188, numerator := 3249669181019930421900783648768 }, { target := 227, numerator := 738279639121463270015573688320 }, { target := 230, numerator := 2524228106678867875458998861824 }, { target := 232, numerator := 738279400655966583539240009728 }, { target := 263, numerator := 1862658014612158826560880640 }, { target := 265, numerator := 1861815762029335917738590208 }, { target := 267, numerator := 5054401356197313859928719360 }, { target := 268, numerator := 746508629644170032718817525760 }, { target := 270, numerator := 7780734601850291499947157094400 }, { target := 278, numerator := 746508629644170032718817525760 }, { target := 285, numerator := 5054401356197313859928719360 }, { target := 286, numerator := 3145492991276561279138779889664 }, { target := 288, numerator := 113993707165729210636698321420288 }, { target := 291, numerator := 113993749057971698426962897797120 }, { target := 298, numerator := 3145451099034073488874203512832 }, { target := 302, numerator := 7694965209835570993111551180800 }, { target := 305, numerator := 26309607407969366570198169026560 }, { target := 307, numerator := 7694962724349579625144590008320 }, { target := 338, numerator := 156629500330788531228408545280 }, { target := 340, numerator := 156558675949627324401467785216 }, { target := 573, numerator := 89876815260692540913591779328 }, { target := 575, numerator := 3257165534378684586657186840576 }, { target := 578, numerator := 3257166731374306377320355594240 }, { target := 585, numerator := 89875618265070750250423025664 }, { target := 589, numerator := 738279639121463270015573688320 }, { target := 592, numerator := 2524228106678867875458998861824 }, { target := 594, numerator := 738279400655966583539240009728 }, { target := 599, numerator := 156629462543313339778125004800 }, { target := 601, numerator := 156558638179238789937427906560 }, { target := 763, numerator := 4998685160554767308050923520 }, { target := 766, numerator := 17090843238919397124513726464 }, { target := 768, numerator := 4998683545971516699268087808 }, { target := 773, numerator := 1862695802087350276844421120 }, { target := 775, numerator := 1861853532417870381778468864 }]

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
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 24545739415916734280053555200 }, { target := 11, numerator := 2055193526583522127550475141120 }, { target := 16, numerator := 2055194270356243179519596298240 }, { target := 24, numerator := 24544995643195682310932398080 }, { target := 26, numerator := 37761409662539080772880433152 }, { target := 27, numerator := 3959215697879448464331928240128 }, { target := 29, numerator := 42676387991706043627616600064000 }, { target := 37, numerator := 3959218718067376364762286784512 }, { target := 44, numerator := 37761409662539080772880433152 }, { target := 141, numerator := 24545739415916734280053555200 }, { target := 142, numerator := 2055193526583522127550475141120 }, { target := 147, numerator := 2055194270356243179519596298240 }, { target := 155, numerator := 24544995643195682310932398080 }, { target := 157, numerator := 128000980497367031600520364032 }, { target := 158, numerator := 13420671946786123087631716712448 }, { target := 160, numerator := 144661429640524887559162036224000 }, { target := 168, numerator := 13420682184407533738438051233792 }, { target := 175, numerator := 128000980497367031600520364032 }, { target := 263, numerator := 217819154022362385481728000 }, { target := 264, numerator := 216331608580258447239413760 }, { target := 265, numerator := 217819154022362385481728000 }, { target := 266, numerator := 218456673497549787585576960 }, { target := 267, numerator := 37761409662539080772880433152 }, { target := 268, numerator := 3959215697879448464331928240128 }, { target := 270, numerator := 42676387991706043627616600064000 }, { target := 278, numerator := 3959218718067376364762286784512 }, { target := 285, numerator := 37761409662539080772880433152 }, { target := 286, numerator := 3249698265716235553663101173760 }, { target := 288, numerator := 113731337122726918759705246433280 }, { target := 291, numerator := 113731392903638046646923857756160 }, { target := 298, numerator := 3249670375260671610053795512320 }, { target := 338, numerator := 169414897572948522041344000 }, { target := 339, numerator := 168257917784645458963988480 }, { target := 340, numerator := 169414897572948522041344000 }, { target := 341, numerator := 169910746053649834788782080 }, { target := 352, numerator := 193617025797655453761536000 }, { target := 353, numerator := 192294763182451953101701120 }, { target := 354, numerator := 193617025797655453761536000 }, { target := 355, numerator := 194183709775599811187179520 }, { target := 479, numerator := 227500005312245158169804800 }, { target := 480, numerator := 225946346739381044894498816 }, { target := 481, numerator := 227500005312245158169804800 }, { target := 482, numerator := 228165858986329778144935936 }, { target := 554, numerator := 2686436232942469420941312000 }, { target := 555, numerator := 2668089839156520849286103040 }, { target := 556, numerator := 2686436232942469420941312000 }, { target := 557, numerator := 2694298973136447380222115840 }, { target := 568, numerator := 6040851204886850157359923200 }, { target := 569, numerator := 5999596611292500936773074944 }, { target := 570, numerator := 6040851204886850157359923200 }, { target := 571, numerator := 6058531744998714109040001024 }, { target := 573, numerator := 89669539478238935727929819136 }, { target := 575, numerator := 3138210316825080696769880260608 }, { target := 578, numerator := 3138211855998321881304872779776 }, { target := 585, numerator := 89668769891618343460433559552 }, { target := 599, numerator := 169414897572948522041344000 }, { target := 600, numerator := 168257917784645458963988480 }, { target := 601, numerator := 169414897572948522041344000 }, { target := 602, numerator := 169910746053649834788782080 }, { target := 613, numerator := 2686436232942469420941312000 }, { target := 614, numerator := 2668089839156520849286103040 }, { target := 615, numerator := 2686436232942469420941312000 }, { target := 616, numerator := 2694298973136447380222115840 }]

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
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 8143988477497771959517184 }, { target := 132, numerator := 199659072351558280297840640 }, { target := 133, numerator := 8143988477497771959517184 }, { target := 134, numerator := 167345827747292927039111168 }, { target := 135, numerator := 164456025384309846666379264 }, { target := 136, numerator := 8143988477497771959517184 }, { target := 137, numerator := 164718734690035581245718528 }, { target := 138, numerator := 147642629817862833588666368 }, { target := 139, numerator := 199659072351558280297840640 }, { target := 140, numerator := 8143988477497771959517184 }, { target := 227, numerator := 1300164900766094550617817088 }, { target := 228, numerator := 31875010470394576079662612480 }, { target := 229, numerator := 1300164900766094550617817088 }, { target := 230, numerator := 26716291670580717056243531776 }, { target := 231, numerator := 26254942834825006086669467648 }, { target := 232, numerator := 1300164900766094550617817088 }, { target := 233, numerator := 26296883638075525265721655296 }, { target := 234, numerator := 23570731426791778627329458176 }, { target := 235, numerator := 31875010470394576079662612480 }, { target := 236, numerator := 1300164900766094550617817088 }, { target := 302, numerator := 12973690520517805904974839808 }, { target := 303, numerator := 318064670825597822186479943680 }, { target := 304, numerator := 12973690520517805904974839808 }, { target := 305, numerator := 266588414889349753595773321216 }, { target := 306, numerator := 261984847285295048274653216768 }, { target := 307, numerator := 12973690520517805904974839808 }, { target := 308, numerator := 262403353431118203303845953536 }, { target := 309, numerator := 235200453952613126406318063616 }, { target := 310, numerator := 318064670825597822186479943680 }, { target := 311, numerator := 12973690520517805904974839808 }, { target := 618, numerator := 193617025797655453761536000 }, { target := 619, numerator := 192294763182451953101701120 }, { target := 620, numerator := 193617025797655453761536000 }, { target := 621, numerator := 194183709775599811187179520 }, { target := 694, numerator := 188776600152714067417497600 }, { target := 695, numerator := 187487394102890654274158592 }, { target := 696, numerator := 188776600152714067417497600 }, { target := 697, numerator := 189329117031209815907500032 }, { target := 708, numerator := 188776600152714067417497600 }, { target := 709, numerator := 187487394102890654274158592 }, { target := 710, numerator := 188776600152714067417497600 }, { target := 711, numerator := 189329117031209815907500032 }, { target := 739, numerator := 188776600152714067417497600 }, { target := 740, numerator := 187487394102890654274158592 }, { target := 741, numerator := 188776600152714067417497600 }, { target := 742, numerator := 189329117031209815907500032 }, { target := 753, numerator := 6040851204886850157359923200 }, { target := 754, numerator := 5999596611292500936773074944 }, { target := 755, numerator := 6040851204886850157359923200 }, { target := 756, numerator := 6058531744998714109040001024 }, { target := 758, numerator := 188776600152714067417497600 }, { target := 759, numerator := 187487394102890654274158592 }, { target := 760, numerator := 188776600152714067417497600 }, { target := 761, numerator := 189329117031209815907500032 }, { target := 773, numerator := 217819154022362385481728000 }, { target := 774, numerator := 216331608580258447239413760 }, { target := 775, numerator := 217819154022362385481728000 }, { target := 776, numerator := 218456673497549787585576960 }, { target := 778, numerator := 227500005312245158169804800 }, { target := 779, numerator := 225946346739381044894498816 }, { target := 780, numerator := 227500005312245158169804800 }, { target := 781, numerator := 228165858986329778144935936 }]

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
    Slot21.Left11.expected,
    Slot21.Left18.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 7233138577855827380375912448 }, { target := 81, numerator := 7082448190817164309951414272 }, { target := 82, numerator := 5575544320430533605706432512 }, { target := 83, numerator := 175252920125965150903691378688 }, { target := 84, numerator := 5575544320430533605706432512 }, { target := 85, numerator := 5575544320430533605706432512 }, { target := 86, numerator := 5726234707469196676130930688 }, { target := 87, numerator := 5726234707469196676130930688 }, { target := 88, numerator := 96893918865860354282952327168 }, { target := 89, numerator := 5274163546353207464857436160 }, { target := 90, numerator := 175252920125965150903691378688 }, { target := 91, numerator := 96893918865860354282952327168 }, { target := 92, numerator := 7233138577855827380375912448 }, { target := 93, numerator := 5575544320430533605706432512 }, { target := 94, numerator := 5274163546353207464857436160 }, { target := 95, numerator := 7082448190817164309951414272 }, { target := 176, numerator := 271767597776086752075014209536 }, { target := 177, numerator := 266105772822418278073451413504 }, { target := 178, numerator := 209487523285733538057823453184 }, { target := 179, numerator := 6584702421116435263817531785216 }, { target := 180, numerator := 209487523285733538057823453184 }, { target := 181, numerator := 209487523285733538057823453184 }, { target := 182, numerator := 215149348239402012059386249216 }, { target := 183, numerator := 215149348239402012059386249216 }, { target := 184, numerator := 3640553445208828783004877848576 }, { target := 185, numerator := 198163873378396590054697861120 }, { target := 186, numerator := 6584702421116435263817531785216 }, { target := 187, numerator := 3640553445208828783004877848576 }, { target := 188, numerator := 271767597776086752075014209536 }, { target := 189, numerator := 209487523285733538057823453184 }, { target := 190, numerator := 198163873378396590054697861120 }, { target := 191, numerator := 266105772822418278073451413504 }, { target := 589, numerator := 1300164900766094550617817088 }, { target := 590, numerator := 31875010470394576079662612480 }, { target := 591, numerator := 1300164900766094550617817088 }, { target := 592, numerator := 26716291670580717056243531776 }, { target := 593, numerator := 26254942834825006086669467648 }, { target := 594, numerator := 1300164900766094550617817088 }, { target := 595, numerator := 26296883638075525265721655296 }, { target := 596, numerator := 23570731426791778627329458176 }, { target := 597, numerator := 31875010470394576079662612480 }, { target := 598, numerator := 1300164900766094550617817088 }, { target := 763, numerator := 8143059222765058840854528 }, { target := 764, numerator := 199636290622627249001594880 }, { target := 765, numerator := 8143059222765058840854528 }, { target := 766, numerator := 167326733061333628439494656 }, { target := 767, numerator := 164437260433900865624997888 }, { target := 768, numerator := 8143059222765058840854528 }, { target := 769, numerator := 164699939763667480426315776 }, { target := 770, numerator := 147625783328837518340653056 }, { target := 771, numerator := 199636290622627249001594880 }, { target := 772, numerator := 8143059222765058840854528 }]

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
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 49047518764966292801842053120 }, { target := 27, numerator := 1307933833732434474715788083200 }, { target := 28, numerator := 1250711728506640466446972354560 }, { target := 29, numerator := 40872932304138577334868377600 }, { target := 30, numerator := 1283410074349951328314867056640 }, { target := 31, numerator := 40872932304138577334868377600 }, { target := 32, numerator := 1250711728506640466446972354560 }, { target := 33, numerator := 711189022092011245626709770240 }, { target := 34, numerator := 1283410074349951328314867056640 }, { target := 35, numerator := 20035911415488730609552478699520 }, { target := 36, numerator := 784760300239460684829472849920 }, { target := 37, numerator := 1307933833732434474715788083200 }, { target := 38, numerator := 1250711728506640466446972354560 }, { target := 39, numerator := 40872932304138577334868377600 }, { target := 40, numerator := 784760300239460684829472849920 }, { target := 41, numerator := 40872932304138577334868377600 }, { target := 42, numerator := 1258886314967468181913946030080 }, { target := 43, numerator := 711189022092011245626709770240 }, { target := 44, numerator := 49047518764966292801842053120 }, { target := 286, numerator := 271747043417715644912287875072 }, { target := 287, numerator := 266085646679846568976615211008 }, { target := 288, numerator := 209471679301155809619888570368 }, { target := 289, numerator := 6584204406141735313187308306432 }, { target := 290, numerator := 209471679301155809619888570368 }, { target := 291, numerator := 209471679301155809619888570368 }, { target := 292, numerator := 215133076039024885555561234432 }, { target := 293, numerator := 215133076039024885555561234432 }, { target := 294, numerator := 3640278102449815826637522993152 }, { target := 295, numerator := 198148885825417657748543242240 }, { target := 296, numerator := 6584204406141735313187308306432 }, { target := 297, numerator := 3640278102449815826637522993152 }, { target := 298, numerator := 271747043417715644912287875072 }, { target := 299, numerator := 209471679301155809619888570368 }, { target := 300, numerator := 198148885825417657748543242240 }, { target := 301, numerator := 266085646679846568976615211008 }, { target := 573, numerator := 7253692936226934543102246912 }, { target := 574, numerator := 7102574333388873406787616768 }, { target := 575, numerator := 5591388305008262043641315328 }, { target := 576, numerator := 175750935100665101533914857472 }, { target := 577, numerator := 5591388305008262043641315328 }, { target := 578, numerator := 5591388305008262043641315328 }, { target := 579, numerator := 5742506907846323179955945472 }, { target := 580, numerator := 5742506907846323179955945472 }, { target := 581, numerator := 97169261624873310650307182592 }, { target := 582, numerator := 5289151099332139771012055040 }, { target := 583, numerator := 175750935100665101533914857472 }, { target := 584, numerator := 97169261624873310650307182592 }, { target := 585, numerator := 7253692936226934543102246912 }, { target := 586, numerator := 5591388305008262043641315328 }, { target := 587, numerator := 5289151099332139771012055040 }, { target := 588, numerator := 7102574333388873406787616768 }]

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
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 108658252666962870222591098880 }, { target := 11, numerator := 111762774171733237943236558848 }, { target := 12, numerator := 108658252666962870222591098880 }, { target := 13, numerator := 96240166647881399340009259008 }, { target := 14, numerator := 4504660703421803562656562413568 }, { target := 15, numerator := 1226285994384295249654956687360 }, { target := 16, numerator := 111762774171733237943236558848 }, { target := 17, numerator := 4504660703421803562656562413568 }, { target := 18, numerator := 108658252666962870222591098880 }, { target := 19, numerator := 108658252666962870222591098880 }, { target := 20, numerator := 93135645143111031619363799040 }, { target := 21, numerator := 108658252666962870222591098880 }, { target := 22, numerator := 1226285994384295249654956687360 }, { target := 23, numerator := 93135645143111031619363799040 }, { target := 24, numerator := 108658252666962870222591098880 }, { target := 25, numerator := 96240166647881399340009259008 }, { target := 157, numerator := 168371555926245518568352382976 }, { target := 158, numerator := 4489908158033213828489396879360 }, { target := 159, numerator := 4293474676119260723492985765888 }, { target := 160, numerator := 140309629938537932140293652480 }, { target := 161, numerator := 4405722380070091069205220687872 }, { target := 162, numerator := 140309629938537932140293652480 }, { target := 163, numerator := 4293474676119260723492985765888 }, { target := 164, numerator := 2441387560930560019241109553152 }, { target := 165, numerator := 4405722380070091069205220687872 }, { target := 166, numerator := 68779780595871294335171948445696 }, { target := 167, numerator := 2693944894819928297093638127616 }, { target := 168, numerator := 4489908158033213828489396879360 }, { target := 169, numerator := 4293474676119260723492985765888 }, { target := 170, numerator := 140309629938537932140293652480 }, { target := 171, numerator := 2693944894819928297093638127616 }, { target := 172, numerator := 140309629938537932140293652480 }, { target := 173, numerator := 4321536602106968309921044496384 }, { target := 174, numerator := 2441387560930560019241109553152 }, { target := 175, numerator := 168371555926245518568352382976 }, { target := 267, numerator := 49047518764966292801842053120 }, { target := 268, numerator := 1307933833732434474715788083200 }, { target := 269, numerator := 1250711728506640466446972354560 }, { target := 270, numerator := 40872932304138577334868377600 }, { target := 271, numerator := 1283410074349951328314867056640 }, { target := 272, numerator := 40872932304138577334868377600 }, { target := 273, numerator := 1250711728506640466446972354560 }, { target := 274, numerator := 711189022092011245626709770240 }, { target := 275, numerator := 1283410074349951328314867056640 }, { target := 276, numerator := 20035911415488730609552478699520 }, { target := 277, numerator := 784760300239460684829472849920 }, { target := 278, numerator := 1307933833732434474715788083200 }, { target := 279, numerator := 1250711728506640466446972354560 }, { target := 280, numerator := 40872932304138577334868377600 }, { target := 281, numerator := 784760300239460684829472849920 }, { target := 282, numerator := 40872932304138577334868377600 }, { target := 283, numerator := 1258886314967468181913946030080 }, { target := 284, numerator := 711189022092011245626709770240 }, { target := 285, numerator := 49047518764966292801842053120 }]

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
    Slot24.Left2.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1450710983537555009647411200 }, { target := 1, numerator := 29072248110092602393334120448 }, { target := 2, numerator := 48801917486203350524538912768 }, { target := 3, numerator := 46828950548592275711418433536 }, { target := 4, numerator := 1450710983537555009647411200 }, { target := 5, numerator := 46828950548592275711418433536 }, { target := 6, numerator := 31277328805069686007998185472 }, { target := 7, numerator := 1508739422879057210033307648 }, { target := 8, numerator := 29072248110092602393334120448 }, { target := 9, numerator := 1392682544196052809261514752 }, { target := 141, numerator := 108658252666962870222591098880 }, { target := 142, numerator := 111762774171733237943236558848 }, { target := 143, numerator := 108658252666962870222591098880 }, { target := 144, numerator := 96240166647881399340009259008 }, { target := 145, numerator := 4504660703421803562656562413568 }, { target := 146, numerator := 1226285994384295249654956687360 }, { target := 147, numerator := 111762774171733237943236558848 }, { target := 148, numerator := 4504660703421803562656562413568 }, { target := 149, numerator := 108658252666962870222591098880 }, { target := 150, numerator := 108658252666962870222591098880 }, { target := 151, numerator := 93135645143111031619363799040 }, { target := 152, numerator := 108658252666962870222591098880 }, { target := 153, numerator := 1226285994384295249654956687360 }, { target := 154, numerator := 93135645143111031619363799040 }, { target := 155, numerator := 108658252666962870222591098880 }, { target := 156, numerator := 96240166647881399340009259008 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent3
