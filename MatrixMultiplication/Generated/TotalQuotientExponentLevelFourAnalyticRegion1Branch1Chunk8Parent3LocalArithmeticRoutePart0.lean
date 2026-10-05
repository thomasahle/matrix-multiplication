import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 37; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent3

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
  [{ target := 61, numerator := 21080643979530096233938944 }, { target := 62, numerator := 15810482984647572175454208 }, { target := 63, numerator := 16688843150461326185201664 }, { target := 64, numerator := 21519824062436973238812672 }, { target := 65, numerator := 288102134386911315197165568 }, { target := 66, numerator := 503739555094187924590166016 }, { target := 67, numerator := 15371302901740695170580480 }, { target := 68, numerator := 288102134386911315197165568 }, { target := 69, numerator := 16249663067554449180327936 }, { target := 70, numerator := 16688843150461326185201664 }, { target := 71, numerator := 16688843150461326185201664 }, { target := 72, numerator := 16249663067554449180327936 }, { target := 73, numerator := 503739555094187924590166016 }, { target := 74, numerator := 16249663067554449180327936 }, { target := 75, numerator := 21080643979530096233938944 }, { target := 76, numerator := 21519824062436973238812672 }, { target := 132, numerator := 516815787885253972186890240 }, { target := 133, numerator := 387611840913940479140167680 }, { target := 134, numerator := 409145832075826061314621440 }, { target := 135, numerator := 527582783466196763274117120 }, { target := 136, numerator := 7063149101098470953220833280 }, { target := 137, numerator := 12349743931341381377049231360 }, { target := 138, numerator := 376844845332997688052940800 }, { target := 139, numerator := 7063149101098470953220833280 }, { target := 140, numerator := 398378836494883270227394560 }, { target := 141, numerator := 409145832075826061314621440 }, { target := 142, numerator := 409145832075826061314621440 }, { target := 143, numerator := 398378836494883270227394560 }, { target := 144, numerator := 12349743931341381377049231360 }, { target := 145, numerator := 398378836494883270227394560 }, { target := 146, numerator := 516815787885253972186890240 }, { target := 147, numerator := 527582783466196763274117120 }, { target := 177, numerator := 382171674725674647853989888 }, { target := 178, numerator := 286628756044255985890492416 }, { target := 179, numerator := 302552575824492429551075328 }, { target := 180, numerator := 390133584615792869684281344 }, { target := 181, numerator := 5223012887917553520671195136 }, { target := 182, numerator := 9132310643965600439344300032 }, { target := 183, numerator := 278666846154137764060200960 }, { target := 184, numerator := 5223012887917553520671195136 }, { target := 185, numerator := 294590665934374207720783872 }, { target := 186, numerator := 302552575824492429551075328 }, { target := 187, numerator := 302552575824492429551075328 }, { target := 188, numerator := 294590665934374207720783872 }, { target := 189, numerator := 9132310643965600439344300032 }, { target := 190, numerator := 294590665934374207720783872 }, { target := 191, numerator := 382171674725674647853989888 }, { target := 192, numerator := 390133584615792869684281344 }, { target := 203, numerator := 426373025005334527054184448 }, { target := 204, numerator := 319779768754000895290638336 }, { target := 205, numerator := 337545311462556500584562688 }, { target := 206, numerator := 435255796359612329701146624 }, { target := 207, numerator := 5827098008406238536407187456 }, { target := 208, numerator := 10188538743356639636065615872 }, { target := 209, numerator := 310896997399723092643676160 }, { target := 210, numerator := 5827098008406238536407187456 }, { target := 211, numerator := 328662540108278697937600512 }, { target := 212, numerator := 337545311462556500584562688 }, { target := 213, numerator := 337545311462556500584562688 }, { target := 214, numerator := 328662540108278697937600512 }, { target := 215, numerator := 10188538743356639636065615872 }, { target := 216, numerator := 328662540108278697937600512 }, { target := 217, numerator := 426373025005334527054184448 }, { target := 218, numerator := 435255796359612329701146624 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 272, numerator := 21080643979530096233938944 }, { target := 273, numerator := 15810482984647572175454208 }, { target := 274, numerator := 16688843150461326185201664 }, { target := 275, numerator := 21519824062436973238812672 }, { target := 276, numerator := 288102134386911315197165568 }, { target := 277, numerator := 503739555094187924590166016 }, { target := 278, numerator := 15371302901740695170580480 }, { target := 279, numerator := 288102134386911315197165568 }, { target := 280, numerator := 16249663067554449180327936 }, { target := 281, numerator := 16688843150461326185201664 }, { target := 282, numerator := 16688843150461326185201664 }, { target := 283, numerator := 16249663067554449180327936 }, { target := 284, numerator := 503739555094187924590166016 }, { target := 285, numerator := 16249663067554449180327936 }, { target := 286, numerator := 21080643979530096233938944 }, { target := 287, numerator := 21519824062436973238812672 }, { target := 317, numerator := 425693004231801298143412224 }, { target := 318, numerator := 319269753173850973607559168 }, { target := 319, numerator := 337006961683509361030201344 }, { target := 320, numerator := 434561608486630491854733312 }, { target := 321, numerator := 5817804391167951074626633728 }, { target := 322, numerator := 10172289080289085186885287936 }, { target := 323, numerator := 310401148919021779896238080 }, { target := 324, numerator := 5817804391167951074626633728 }, { target := 325, numerator := 328138357428680167318880256 }, { target := 326, numerator := 337006961683509361030201344 }, { target := 327, numerator := 337006961683509361030201344 }, { target := 328, numerator := 328138357428680167318880256 }, { target := 329, numerator := 10172289080289085186885287936 }, { target := 330, numerator := 328138357428680167318880256 }, { target := 331, numerator := 425693004231801298143412224 }, { target := 332, numerator := 434561608486630491854733312 }, { target := 343, numerator := 433173232740666816161906688 }, { target := 344, numerator := 324879924555500112121430016 }, { target := 345, numerator := 342928809253027896128176128 }, { target := 346, numerator := 442197675089430708165279744 }, { target := 347, numerator := 5920034180789113154212724736 }, { target := 348, numerator := 10351035374032184127868895232 }, { target := 349, numerator := 315855482206736220118056960 }, { target := 350, numerator := 5920034180789113154212724736 }, { target := 351, numerator := 333904366904264004124803072 }, { target := 352, numerator := 342928809253027896128176128 }, { target := 353, numerator := 342928809253027896128176128 }, { target := 354, numerator := 333904366904264004124803072 }, { target := 355, numerator := 10351035374032184127868895232 }, { target := 356, numerator := 333904366904264004124803072 }, { target := 357, numerator := 433173232740666816161906688 }, { target := 358, numerator := 442197675089430708165279744 }, { target := 392, numerator := 21080643979530096233938944 }, { target := 393, numerator := 15810482984647572175454208 }, { target := 394, numerator := 16688843150461326185201664 }, { target := 395, numerator := 21519824062436973238812672 }, { target := 396, numerator := 288102134386911315197165568 }, { target := 397, numerator := 503739555094187924590166016 }, { target := 398, numerator := 15371302901740695170580480 }, { target := 399, numerator := 288102134386911315197165568 }, { target := 400, numerator := 16249663067554449180327936 }, { target := 401, numerator := 16688843150461326185201664 }, { target := 402, numerator := 16688843150461326185201664 }, { target := 403, numerator := 16249663067554449180327936 }, { target := 404, numerator := 503739555094187924590166016 }, { target := 405, numerator := 16249663067554449180327936 }, { target := 406, numerator := 21080643979530096233938944 }, { target := 407, numerator := 21519824062436973238812672 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 219, numerator := 73103339959466530481111040 }, { target := 220, numerator := 8640345442699476510745559040 }, { target := 222, numerator := 81995155913772683566189117440 }, { target := 230, numerator := 8640351368716010189939015680 }, { target := 237, numerator := 73103339959466530481111040 }, { target := 359, numerator := 72890003364254079516672000 }, { target := 360, numerator := 8615130426816112279683072000 }, { target := 362, numerator := 81755870439316148497416192000 }, { target := 370, numerator := 8615136335538823389773824000 }, { target := 377, numerator := 72890003364254079516672000 }, { target := 418, numerator := 516815787885253972186890240 }, { target := 419, numerator := 387611840913940479140167680 }, { target := 420, numerator := 409145832075826061314621440 }, { target := 421, numerator := 527582783466196763274117120 }, { target := 422, numerator := 7063149101098470953220833280 }, { target := 423, numerator := 12349743931341381377049231360 }, { target := 424, numerator := 376844845332997688052940800 }, { target := 425, numerator := 7063149101098470953220833280 }, { target := 426, numerator := 398378836494883270227394560 }, { target := 427, numerator := 409145832075826061314621440 }, { target := 428, numerator := 409145832075826061314621440 }, { target := 429, numerator := 398378836494883270227394560 }, { target := 430, numerator := 12349743931341381377049231360 }, { target := 431, numerator := 398378836494883270227394560 }, { target := 432, numerator := 516815787885253972186890240 }, { target := 433, numerator := 527582783466196763274117120 }, { target := 434, numerator := 72392217975425027266314240 }, { target := 435, numerator := 8556295389754929073870602240 }, { target := 437, numerator := 81197537665584233336946032640 }, { target := 445, numerator := 8556301258125387522721710080 }, { target := 452, numerator := 72392217975425027266314240 }, { target := 453, numerator := 21080643979530096233938944 }, { target := 454, numerator := 15810482984647572175454208 }, { target := 455, numerator := 16688843150461326185201664 }, { target := 456, numerator := 21519824062436973238812672 }, { target := 457, numerator := 288102134386911315197165568 }, { target := 458, numerator := 503739555094187924590166016 }, { target := 459, numerator := 15371302901740695170580480 }, { target := 460, numerator := 288102134386911315197165568 }, { target := 461, numerator := 16249663067554449180327936 }, { target := 462, numerator := 16688843150461326185201664 }, { target := 463, numerator := 16688843150461326185201664 }, { target := 464, numerator := 16249663067554449180327936 }, { target := 465, numerator := 503739555094187924590166016 }, { target := 466, numerator := 16249663067554449180327936 }, { target := 467, numerator := 21080643979530096233938944 }, { target := 468, numerator := 21519824062436973238812672 }, { target := 469, numerator := 72890003364254079516672000 }, { target := 470, numerator := 8615130426816112279683072000 }, { target := 472, numerator := 81755870439316148497416192000 }, { target := 480, numerator := 8615136335538823389773824000 }, { target := 487, numerator := 72890003364254079516672000 }, { target := 488, numerator := 8883196367261260915031408640 }, { target := 490, numerator := 347643534946928258255916367872 }, { target := 493, numerator := 347643534946928258255916367872 }, { target := 500, numerator := 8883196367261260915031408640 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left6.expected,
    Slot3.Left14.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 10528491862206277260148736 }, { target := 18, numerator := 255061206081190781366829056 }, { target := 19, numerator := 193248769986947476162084864 }, { target := 20, numerator := 215324640020605799449493504 }, { target := 21, numerator := 10528491862206277260148736 }, { target := 22, numerator := 215324640020605799449493504 }, { target := 23, numerator := 214985011250857209860456448 }, { target := 24, numerator := 10528491862206277260148736 }, { target := 25, numerator := 255061206081190781366829056 }, { target := 26, numerator := 10528491862206277260148736 }, { target := 37, numerator := 2088166730988789970029772800 }, { target := 38, numerator := 50587523063631653790076108800 }, { target := 39, numerator := 38327963546213596546675507200 }, { target := 40, numerator := 42706377659577188419318579200 }, { target := 41, numerator := 2088166730988789970029772800 }, { target := 42, numerator := 42706377659577188419318579200 }, { target := 43, numerator := 42639017442448517775124070400 }, { target := 44, numerator := 2088166730988789970029772800 }, { target := 45, numerator := 50587523063631653790076108800 }, { target := 46, numerator := 2088166730988789970029772800 }, { target := 61, numerator := 38061838108399194003734528 }, { target := 62, numerator := 6675688811655512449146159104 }, { target := 67, numerator := 6675689611996957628598059008 }, { target := 75, numerator := 38061037766954014551834624 }, { target := 153, numerator := 2088166730988789970029772800 }, { target := 154, numerator := 50587523063631653790076108800 }, { target := 155, numerator := 38327963546213596546675507200 }, { target := 156, numerator := 42706377659577188419318579200 }, { target := 157, numerator := 2088166730988789970029772800 }, { target := 158, numerator := 42706377659577188419318579200 }, { target := 159, numerator := 42639017442448517775124070400 }, { target := 160, numerator := 2088166730988789970029772800 }, { target := 161, numerator := 50587523063631653790076108800 }, { target := 162, numerator := 2088166730988789970029772800 }, { target := 177, numerator := 1720325838853281653958115328 }, { target := 178, numerator := 301728989601804230566036373504 }, { target := 183, numerator := 301729025775781538917733367808 }, { target := 191, numerator := 1720289664875973302261121024 }, { target := 219, numerator := 43776337296201611130961920 }, { target := 220, numerator := 14101293271670147135035146240 }, { target := 222, numerator := 149973183937863716266334748672 }, { target := 230, numerator := 14101335772968492961842069504 }, { target := 237, numerator := 43776337296201611130961920 }, { target := 359, numerator := 43776337296201611130961920 }, { target := 360, numerator := 14101293271670147135035146240 }, { target := 362, numerator := 149973183937863716266334748672 }, { target := 370, numerator := 14101335772968492961842069504 }, { target := 377, numerator := 43776337296201611130961920 }, { target := 382, numerator := 10528491862206277260148736 }, { target := 383, numerator := 255061206081190781366829056 }, { target := 384, numerator := 193248769986947476162084864 }, { target := 385, numerator := 215324640020605799449493504 }, { target := 386, numerator := 10528491862206277260148736 }, { target := 387, numerator := 215324640020605799449493504 }, { target := 388, numerator := 214985011250857209860456448 }, { target := 389, numerator := 10528491862206277260148736 }, { target := 390, numerator := 255061206081190781366829056 }, { target := 391, numerator := 10528491862206277260148736 }, { target := 392, numerator := 38264985644972891460075520 }, { target := 393, numerator := 6711318980990953619571343360 }, { target := 398, numerator := 6711319785604063045584158720 }, { target := 406, numerator := 38264181031863465447260160 }]

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
    Slot8.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 43776337296201611130961920 }, { target := 3, numerator := 43776337296201611130961920 }, { target := 4, numerator := 43776337296201611130961920 }, { target := 5, numerator := 43776337296201611130961920 }, { target := 8, numerator := 14101293271670147135035146240 }, { target := 9, numerator := 14101293271670147135035146240 }, { target := 10, numerator := 14101293271670147135035146240 }, { target := 11, numerator := 14101293271670147135035146240 }, { target := 17, numerator := 38061838108399194003734528 }, { target := 19, numerator := 1720325838853281653958115328 }, { target := 24, numerator := 38264985644972891460075520 }, { target := 28, numerator := 149973183937863716266334748672 }, { target := 29, numerator := 149973183937863716266334748672 }, { target := 30, numerator := 149973183937863716266334748672 }, { target := 31, numerator := 149973183937863716266334748672 }, { target := 37, numerator := 6675688811655512449146159104 }, { target := 39, numerator := 301728989601804230566036373504 }, { target := 44, numerator := 6711318980990953619571343360 }, { target := 61, numerator := 10528491862206277260148736 }, { target := 62, numerator := 2088166730988789970029772800 }, { target := 67, numerator := 2088166730988789970029772800 }, { target := 75, numerator := 10528491862206277260148736 }, { target := 132, numerator := 255061206081190781366829056 }, { target := 133, numerator := 50587523063631653790076108800 }, { target := 138, numerator := 50587523063631653790076108800 }, { target := 146, numerator := 255061206081190781366829056 }, { target := 149, numerator := 14101335772968492961842069504 }, { target := 150, numerator := 14101335772968492961842069504 }, { target := 151, numerator := 14101335772968492961842069504 }, { target := 152, numerator := 14101335772968492961842069504 }, { target := 153, numerator := 6675689611996957628598059008 }, { target := 155, numerator := 301729025775781538917733367808 }, { target := 160, numerator := 6711319785604063045584158720 }, { target := 177, numerator := 193248769986947476162084864 }, { target := 178, numerator := 38327963546213596546675507200 }, { target := 183, numerator := 38327963546213596546675507200 }, { target := 191, numerator := 193248769986947476162084864 }, { target := 203, numerator := 215324640020605799449493504 }, { target := 204, numerator := 42706377659577188419318579200 }, { target := 209, numerator := 42706377659577188419318579200 }, { target := 217, numerator := 215324640020605799449493504 }, { target := 272, numerator := 10528491862206277260148736 }, { target := 273, numerator := 2088166730988789970029772800 }, { target := 278, numerator := 2088166730988789970029772800 }, { target := 286, numerator := 10528491862206277260148736 }, { target := 378, numerator := 43776337296201611130961920 }, { target := 379, numerator := 43776337296201611130961920 }, { target := 380, numerator := 43776337296201611130961920 }, { target := 381, numerator := 43776337296201611130961920 }, { target := 382, numerator := 38061037766954014551834624 }, { target := 384, numerator := 1720289664875973302261121024 }, { target := 389, numerator := 38264181031863465447260160 }, { target := 434, numerator := 43776337296201611130961920 }, { target := 435, numerator := 14101293271670147135035146240 }, { target := 437, numerator := 149973183937863716266334748672 }, { target := 445, numerator := 14101335772968492961842069504 }, { target := 452, numerator := 43776337296201611130961920 }, { target := 469, numerator := 43776337296201611130961920 }, { target := 470, numerator := 14101293271670147135035146240 }, { target := 472, numerator := 149973183937863716266334748672 }, { target := 480, numerator := 14101335772968492961842069504 }, { target := 487, numerator := 43776337296201611130961920 }]

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
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8883196367261260915031408640 }, { target := 2, numerator := 73103339959466530481111040 }, { target := 3, numerator := 72890003364254079516672000 }, { target := 4, numerator := 72392217975425027266314240 }, { target := 5, numerator := 72890003364254079516672000 }, { target := 6, numerator := 347643534946928258255916367872 }, { target := 8, numerator := 8640345442699476510745559040 }, { target := 9, numerator := 8615130426816112279683072000 }, { target := 10, numerator := 8556295389754929073870602240 }, { target := 11, numerator := 8615130426816112279683072000 }, { target := 17, numerator := 21080643979530096233938944 }, { target := 18, numerator := 516815787885253972186890240 }, { target := 19, numerator := 382171674725674647853989888 }, { target := 20, numerator := 426373025005334527054184448 }, { target := 21, numerator := 21080643979530096233938944 }, { target := 22, numerator := 425693004231801298143412224 }, { target := 23, numerator := 433173232740666816161906688 }, { target := 24, numerator := 21080643979530096233938944 }, { target := 25, numerator := 516815787885253972186890240 }, { target := 26, numerator := 21080643979530096233938944 }, { target := 27, numerator := 347643534946928258255916367872 }, { target := 28, numerator := 81995155913772683566189117440 }, { target := 29, numerator := 81755870439316148497416192000 }, { target := 30, numerator := 81197537665584233336946032640 }, { target := 31, numerator := 81755870439316148497416192000 }, { target := 37, numerator := 15810482984647572175454208 }, { target := 38, numerator := 387611840913940479140167680 }, { target := 39, numerator := 286628756044255985890492416 }, { target := 40, numerator := 319779768754000895290638336 }, { target := 41, numerator := 15810482984647572175454208 }, { target := 42, numerator := 319269753173850973607559168 }, { target := 43, numerator := 324879924555500112121430016 }, { target := 44, numerator := 15810482984647572175454208 }, { target := 45, numerator := 387611840913940479140167680 }, { target := 46, numerator := 15810482984647572175454208 }, { target := 148, numerator := 8883196367261260915031408640 }, { target := 149, numerator := 8640351368716010189939015680 }, { target := 150, numerator := 8615136335538823389773824000 }, { target := 151, numerator := 8556301258125387522721710080 }, { target := 152, numerator := 8615136335538823389773824000 }, { target := 317, numerator := 215324640020605799449493504 }, { target := 318, numerator := 42706377659577188419318579200 }, { target := 323, numerator := 42706377659577188419318579200 }, { target := 331, numerator := 215324640020605799449493504 }, { target := 343, numerator := 214985011250857209860456448 }, { target := 344, numerator := 42639017442448517775124070400 }, { target := 349, numerator := 42639017442448517775124070400 }, { target := 357, numerator := 214985011250857209860456448 }, { target := 378, numerator := 73103339959466530481111040 }, { target := 379, numerator := 72890003364254079516672000 }, { target := 380, numerator := 72392217975425027266314240 }, { target := 381, numerator := 72890003364254079516672000 }, { target := 392, numerator := 10528491862206277260148736 }, { target := 393, numerator := 2088166730988789970029772800 }, { target := 398, numerator := 2088166730988789970029772800 }, { target := 406, numerator := 10528491862206277260148736 }, { target := 418, numerator := 255061206081190781366829056 }, { target := 419, numerator := 50587523063631653790076108800 }, { target := 424, numerator := 50587523063631653790076108800 }, { target := 432, numerator := 255061206081190781366829056 }, { target := 453, numerator := 10528491862206277260148736 }, { target := 454, numerator := 2088166730988789970029772800 }, { target := 459, numerator := 2088166730988789970029772800 }, { target := 467, numerator := 10528491862206277260148736 }]

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
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 51, numerator := 16688843150461326185201664 }, { target := 52, numerator := 409145832075826061314621440 }, { target := 53, numerator := 302552575824492429551075328 }, { target := 54, numerator := 337545311462556500584562688 }, { target := 55, numerator := 16688843150461326185201664 }, { target := 56, numerator := 337006961683509361030201344 }, { target := 57, numerator := 342928809253027896128176128 }, { target := 58, numerator := 16688843150461326185201664 }, { target := 59, numerator := 409145832075826061314621440 }, { target := 60, numerator := 16688843150461326185201664 }, { target := 88, numerator := 21519824062436973238812672 }, { target := 89, numerator := 527582783466196763274117120 }, { target := 90, numerator := 390133584615792869684281344 }, { target := 91, numerator := 435255796359612329701146624 }, { target := 92, numerator := 21519824062436973238812672 }, { target := 93, numerator := 434561608486630491854733312 }, { target := 94, numerator := 442197675089430708165279744 }, { target := 95, numerator := 21519824062436973238812672 }, { target := 96, numerator := 527582783466196763274117120 }, { target := 97, numerator := 21519824062436973238812672 }, { target := 108, numerator := 288102134386911315197165568 }, { target := 109, numerator := 7063149101098470953220833280 }, { target := 110, numerator := 5223012887917553520671195136 }, { target := 111, numerator := 5827098008406238536407187456 }, { target := 112, numerator := 288102134386911315197165568 }, { target := 113, numerator := 5817804391167951074626633728 }, { target := 114, numerator := 5920034180789113154212724736 }, { target := 115, numerator := 288102134386911315197165568 }, { target := 116, numerator := 7063149101098470953220833280 }, { target := 117, numerator := 288102134386911315197165568 }, { target := 122, numerator := 503739555094187924590166016 }, { target := 123, numerator := 12349743931341381377049231360 }, { target := 124, numerator := 9132310643965600439344300032 }, { target := 125, numerator := 10188538743356639636065615872 }, { target := 126, numerator := 503739555094187924590166016 }, { target := 127, numerator := 10172289080289085186885287936 }, { target := 128, numerator := 10351035374032184127868895232 }, { target := 129, numerator := 503739555094187924590166016 }, { target := 130, numerator := 12349743931341381377049231360 }, { target := 131, numerator := 503739555094187924590166016 }, { target := 153, numerator := 15371302901740695170580480 }, { target := 154, numerator := 376844845332997688052940800 }, { target := 155, numerator := 278666846154137764060200960 }, { target := 156, numerator := 310896997399723092643676160 }, { target := 157, numerator := 15371302901740695170580480 }, { target := 158, numerator := 310401148919021779896238080 }, { target := 159, numerator := 315855482206736220118056960 }, { target := 160, numerator := 15371302901740695170580480 }, { target := 161, numerator := 376844845332997688052940800 }, { target := 162, numerator := 15371302901740695170580480 }, { target := 167, numerator := 288102134386911315197165568 }, { target := 168, numerator := 7063149101098470953220833280 }, { target := 169, numerator := 5223012887917553520671195136 }, { target := 170, numerator := 5827098008406238536407187456 }, { target := 171, numerator := 288102134386911315197165568 }, { target := 172, numerator := 5817804391167951074626633728 }, { target := 173, numerator := 5920034180789113154212724736 }, { target := 174, numerator := 288102134386911315197165568 }, { target := 175, numerator := 7063149101098470953220833280 }, { target := 176, numerator := 288102134386911315197165568 }]

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
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 193, numerator := 16249663067554449180327936 }, { target := 194, numerator := 398378836494883270227394560 }, { target := 195, numerator := 294590665934374207720783872 }, { target := 196, numerator := 328662540108278697937600512 }, { target := 197, numerator := 16249663067554449180327936 }, { target := 198, numerator := 328138357428680167318880256 }, { target := 199, numerator := 333904366904264004124803072 }, { target := 200, numerator := 16249663067554449180327936 }, { target := 201, numerator := 398378836494883270227394560 }, { target := 202, numerator := 16249663067554449180327936 }, { target := 248, numerator := 16688843150461326185201664 }, { target := 249, numerator := 409145832075826061314621440 }, { target := 250, numerator := 302552575824492429551075328 }, { target := 251, numerator := 337545311462556500584562688 }, { target := 252, numerator := 16688843150461326185201664 }, { target := 253, numerator := 337006961683509361030201344 }, { target := 254, numerator := 342928809253027896128176128 }, { target := 255, numerator := 16688843150461326185201664 }, { target := 256, numerator := 409145832075826061314621440 }, { target := 257, numerator := 16688843150461326185201664 }, { target := 262, numerator := 16688843150461326185201664 }, { target := 263, numerator := 409145832075826061314621440 }, { target := 264, numerator := 302552575824492429551075328 }, { target := 265, numerator := 337545311462556500584562688 }, { target := 266, numerator := 16688843150461326185201664 }, { target := 267, numerator := 337006961683509361030201344 }, { target := 268, numerator := 342928809253027896128176128 }, { target := 269, numerator := 16688843150461326185201664 }, { target := 270, numerator := 409145832075826061314621440 }, { target := 271, numerator := 16688843150461326185201664 }, { target := 293, numerator := 16249663067554449180327936 }, { target := 294, numerator := 398378836494883270227394560 }, { target := 295, numerator := 294590665934374207720783872 }, { target := 296, numerator := 328662540108278697937600512 }, { target := 297, numerator := 16249663067554449180327936 }, { target := 298, numerator := 328138357428680167318880256 }, { target := 299, numerator := 333904366904264004124803072 }, { target := 300, numerator := 16249663067554449180327936 }, { target := 301, numerator := 398378836494883270227394560 }, { target := 302, numerator := 16249663067554449180327936 }, { target := 307, numerator := 503739555094187924590166016 }, { target := 308, numerator := 12349743931341381377049231360 }, { target := 309, numerator := 9132310643965600439344300032 }, { target := 310, numerator := 10188538743356639636065615872 }, { target := 311, numerator := 503739555094187924590166016 }, { target := 312, numerator := 10172289080289085186885287936 }, { target := 313, numerator := 10351035374032184127868895232 }, { target := 314, numerator := 503739555094187924590166016 }, { target := 315, numerator := 12349743931341381377049231360 }, { target := 316, numerator := 503739555094187924590166016 }, { target := 333, numerator := 16249663067554449180327936 }, { target := 334, numerator := 398378836494883270227394560 }, { target := 335, numerator := 294590665934374207720783872 }, { target := 336, numerator := 328662540108278697937600512 }, { target := 337, numerator := 16249663067554449180327936 }, { target := 338, numerator := 328138357428680167318880256 }, { target := 339, numerator := 333904366904264004124803072 }, { target := 340, numerator := 16249663067554449180327936 }, { target := 341, numerator := 398378836494883270227394560 }, { target := 342, numerator := 16249663067554449180327936 }]

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
    Slot11.Left14.expected,
    Slot11.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 382, numerator := 21080643979530096233938944 }, { target := 383, numerator := 516815787885253972186890240 }, { target := 384, numerator := 382171674725674647853989888 }, { target := 385, numerator := 426373025005334527054184448 }, { target := 386, numerator := 21080643979530096233938944 }, { target := 387, numerator := 425693004231801298143412224 }, { target := 388, numerator := 433173232740666816161906688 }, { target := 389, numerator := 21080643979530096233938944 }, { target := 390, numerator := 516815787885253972186890240 }, { target := 391, numerator := 21080643979530096233938944 }, { target := 408, numerator := 21519824062436973238812672 }, { target := 409, numerator := 527582783466196763274117120 }, { target := 410, numerator := 390133584615792869684281344 }, { target := 411, numerator := 435255796359612329701146624 }, { target := 412, numerator := 21519824062436973238812672 }, { target := 413, numerator := 434561608486630491854733312 }, { target := 414, numerator := 442197675089430708165279744 }, { target := 415, numerator := 21519824062436973238812672 }, { target := 416, numerator := 527582783466196763274117120 }, { target := 417, numerator := 21519824062436973238812672 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent3
