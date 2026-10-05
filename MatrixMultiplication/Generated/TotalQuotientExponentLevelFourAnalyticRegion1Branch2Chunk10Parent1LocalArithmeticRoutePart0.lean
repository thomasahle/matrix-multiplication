import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1

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
  [{ target := 257, numerator := 78661882968501659699144294400 }, { target := 260, numerator := 286110224697642661883936768000 }, { target := 262, numerator := 78661882968501659699144294400 }, { target := 353, numerator := 80909365339030278547691274240 }, { target := 356, numerator := 294284802546146737937763532800 }, { target := 358, numerator := 80909365339030278547691274240 }, { target := 379, numerator := 78661882968501659699144294400 }, { target := 382, numerator := 286110224697642661883936768000 }, { target := 384, numerator := 78661882968501659699144294400 }, { target := 389, numerator := 7495341868639033023791104000 }, { target := 391, numerator := 7495338294582368742565478400 }, { target := 524, numerator := 69671953486387184304956375040 }, { target := 527, numerator := 253411913303626357668629708800 }, { target := 529, numerator := 69671953486387184304956375040 }, { target := 620, numerator := 3261096919637025949241667747840 }, { target := 623, numerator := 11861312458179414354102635724800 }, { target := 625, numerator := 3261096919637025949241667747840 }, { target := 646, numerator := 887755536358804445176057036800 }, { target := 649, numerator := 3228958250159110041261572096000 }, { target := 651, numerator := 887755536358804445176057036800 }, { target := 656, numerator := 150206651047526221796773724160 }, { target := 658, numerator := 150206579423430669601012187136 }, { target := 695, numerator := 80909365339030278547691274240 }, { target := 698, numerator := 294284802546146737937763532800 }, { target := 700, numerator := 80909365339030278547691274240 }, { target := 721, numerator := 3261096919637025949241667747840 }, { target := 724, numerator := 11861312458179414354102635724800 }, { target := 726, numerator := 3261096919637025949241667747840 }, { target := 731, numerator := 252143300461017070920332738560 }, { target := 733, numerator := 252143180229750884499902693376 }, { target := 735, numerator := 78661882968501659699144294400 }, { target := 738, numerator := 286110224697642661883936768000 }, { target := 740, numerator := 78661882968501659699144294400 }, { target := 745, numerator := 241949635519667986007976837120 }, { target := 747, numerator := 241949520149118863010013642752 }, { target := 749, numerator := 20696810031802451470969733120 }, { target := 836, numerator := 78661882968501659699144294400 }, { target := 839, numerator := 286110224697642661883936768000 }, { target := 841, numerator := 78661882968501659699144294400 }, { target := 862, numerator := 67424471115858565456409395200 }, { target := 865, numerator := 245237335455122281614802944000 }, { target := 867, numerator := 67424471115858565456409395200 }, { target := 872, numerator := 7495341868639033023791104000 }, { target := 874, numerator := 7495338294582368742565478400 }, { target := 911, numerator := 78661882968501659699144294400 }, { target := 914, numerator := 286110224697642661883936768000 }, { target := 916, numerator := 78661882968501659699144294400 }, { target := 937, numerator := 887755536358804445176057036800 }, { target := 940, numerator := 3228958250159110041261572096000 }, { target := 942, numerator := 887755536358804445176057036800 }, { target := 947, numerator := 241949635519667986007976837120 }, { target := 949, numerator := 241949520149118863010013642752 }, { target := 961, numerator := 161599570687857551992936202240 }, { target := 963, numerator := 161599493631195870089711714304 }, { target := 965, numerator := 18917271225329717325802242048 }, { target := 992, numerator := 7795155543384594344742748160 }, { target := 994, numerator := 7795151826365663492268097536 }, { target := 1006, numerator := 150206651047526221796773724160 }, { target := 1008, numerator := 150206579423430669601012187136 }, { target := 1010, numerator := 20696810031802451470969733120 }, { target := 1011, numerator := 7195528193893471702839459840 }, { target := 1013, numerator := 7195524762799073992862859264 }, { target := 1015, numerator := 18917271225329717325802242048 }]

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
  [{ target := 110, numerator := 1055655881389872726430187520 }, { target := 112, numerator := 38983967264246645539838361600 }, { target := 115, numerator := 38983957718056587395145400320 }, { target := 122, numerator := 1055665427579930871123148800 }, { target := 206, numerator := 28150823503729939371471667200 }, { target := 208, numerator := 1039572460379910547729022976000 }, { target := 211, numerator := 1039572205814842330537210675200 }, { target := 218, numerator := 28151078068798156563283968000 }, { target := 241, numerator := 26919224975441754523969781760 }, { target := 243, numerator := 994091165238289461265878220800 }, { target := 246, numerator := 994090921810442978576207708160 }, { target := 253, numerator := 26919468403288237213640294400 }, { target := 302, numerator := 879713234491560605358489600 }, { target := 304, numerator := 32486639386872204616531968000 }, { target := 307, numerator := 32486631431713822829287833600 }, { target := 314, numerator := 879721189649942392602624000 }, { target := 337, numerator := 27622995563035003008256573440 }, { target := 339, numerator := 1020080476747787224959103795200 }, { target := 342, numerator := 1020080226955814036839637975040 }, { target := 349, numerator := 27623245355008191127722393600 }, { target := 363, numerator := 879713234491560605358489600 }, { target := 365, numerator := 32486639386872204616531968000 }, { target := 368, numerator := 32486631431713822829287833600 }, { target := 375, numerator := 879721189649942392602624000 }, { target := 473, numerator := 26919224975441754523969781760 }, { target := 475, numerator := 994091165238289461265878220800 }, { target := 478, numerator := 994090921810442978576207708160 }, { target := 485, numerator := 26919468403288237213640294400 }, { target := 508, numerator := 15307010280153154533237719040 }, { target := 510, numerator := 565267525331576360327656243200 }, { target := 513, numerator := 565267386911820517229608304640 }, { target := 520, numerator := 15307148699908997631285657600 }, { target := 569, numerator := 27622995563035003008256573440 }, { target := 571, numerator := 1020080476747787224959103795200 }, { target := 574, numerator := 1020080226955814036839637975040 }, { target := 581, numerator := 27623245355008191127722393600 }, { target := 604, numerator := 431235427547763008746731601920 }, { target := 606, numerator := 15924950627444754703023970713600 }, { target := 609, numerator := 15924946727826115950916896030720 }, { target := 616, numerator := 431239327166401760853806284800 }, { target := 630, numerator := 16890494102237963622883000320 }, { target := 632, numerator := 623743476227946328637413785600 }, { target := 635, numerator := 623743323488905398322326405120 }, { target := 642, numerator := 16890646841278893937970380800 }, { target := 679, numerator := 28150823503729939371471667200 }, { target := 681, numerator := 1039572460379910547729022976000 }, { target := 684, numerator := 1039572205814842330537210675200 }, { target := 691, numerator := 28151078068798156563283968000 }, { target := 705, numerator := 26919224975441754523969781760 }, { target := 707, numerator := 994091165238289461265878220800 }, { target := 710, numerator := 994090921810442978576207708160 }, { target := 717, numerator := 26919468403288237213640294400 }, { target := 951, numerator := 67424471115858565456409395200 }, { target := 954, numerator := 245237335455122281614802944000 }, { target := 956, numerator := 67424471115858565456409395200 }, { target := 982, numerator := 78661882968501659699144294400 }, { target := 985, numerator := 286110224697642661883936768000 }, { target := 987, numerator := 78661882968501659699144294400 }, { target := 996, numerator := 69671953486387184304956375040 }, { target := 999, numerator := 253411913303626357668629708800 }, { target := 1001, numerator := 69671953486387184304956375040 }]

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
    Slot4.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 64601973485656746523361280 }, { target := 57, numerator := 1085313154559033341592469504 }, { target := 58, numerator := 2351511834877905573450350592 }, { target := 59, numerator := 77522368182788095828033536 }, { target := 60, numerator := 1240357890924609533248536576 }, { target := 61, numerator := 90442762879919445132705792 }, { target := 62, numerator := 2351511834877905573450350592 }, { target := 63, numerator := 2351511834877905573450350592 }, { target := 64, numerator := 1240357890924609533248536576 }, { target := 65, numerator := 29019206489757010538293886976 }, { target := 66, numerator := 2325671045483642874841006080 }, { target := 67, numerator := 1085313154559033341592469504 }, { target := 68, numerator := 2351511834877905573450350592 }, { target := 69, numerator := 90442762879919445132705792 }, { target := 70, numerator := 2325671045483642874841006080 }, { target := 71, numerator := 90442762879919445132705792 }, { target := 72, numerator := 2351511834877905573450350592 }, { target := 73, numerator := 2351511834877905573450350592 }, { target := 74, numerator := 77522368182788095828033536 }, { target := 91, numerator := 63256099038038897637457920 }, { target := 92, numerator := 1062702463839053480309293056 }, { target := 93, numerator := 2302522004984615874003468288 }, { target := 94, numerator := 75907318845646677164949504 }, { target := 95, numerator := 1214517101530346834639192064 }, { target := 96, numerator := 88558538653254456692441088 }, { target := 97, numerator := 2302522004984615874003468288 }, { target := 98, numerator := 2302522004984615874003468288 }, { target := 99, numerator := 1214517101530346834639192064 }, { target := 100, numerator := 28414639687887072818746097664 }, { target := 101, numerator := 2277219565369400314948485120 }, { target := 102, numerator := 1062702463839053480309293056 }, { target := 103, numerator := 2302522004984615874003468288 }, { target := 104, numerator := 88558538653254456692441088 }, { target := 105, numerator := 2277219565369400314948485120 }, { target := 106, numerator := 88558538653254456692441088 }, { target := 107, numerator := 2302522004984615874003468288 }, { target := 108, numerator := 2302522004984615874003468288 }, { target := 109, numerator := 75907318845646677164949504 }, { target := 785, numerator := 879713234491560605358489600 }, { target := 787, numerator := 32486639386872204616531968000 }, { target := 790, numerator := 32486631431713822829287833600 }, { target := 797, numerator := 879721189649942392602624000 }, { target := 820, numerator := 16890494102237963622883000320 }, { target := 822, numerator := 623743476227946328637413785600 }, { target := 825, numerator := 623743323488905398322326405120 }, { target := 832, numerator := 16890646841278893937970380800 }, { target := 846, numerator := 879713234491560605358489600 }, { target := 848, numerator := 32486639386872204616531968000 }, { target := 851, numerator := 32486631431713822829287833600 }, { target := 858, numerator := 879721189649942392602624000 }, { target := 895, numerator := 27095167622340066645041479680 }, { target := 897, numerator := 1000588493115663902189184614400 }, { target := 900, numerator := 1000588248096785743142065274880 }, { target := 907, numerator := 27095412641218225692160819200 }, { target := 921, numerator := 15307010280153154533237719040 }, { target := 923, numerator := 565267525331576360327656243200 }, { target := 926, numerator := 565267386911820517229608304640 }, { target := 933, numerator := 15307148699908997631285657600 }, { target := 966, numerator := 1055655881389872726430187520 }, { target := 968, numerator := 38983967264246645539838361600 }, { target := 971, numerator := 38983957718056587395145400320 }, { target := 978, numerator := 1055665427579930871123148800 }]

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
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 49797354561860408778424320 }, { target := 153, numerator := 836595556639254867477528576 }, { target := 154, numerator := 1812623706051718879534645248 }, { target := 155, numerator := 59756825474232490534109184 }, { target := 156, numerator := 956109207587719848545746944 }, { target := 157, numerator := 69716296386604572289794048 }, { target := 158, numerator := 1812623706051718879534645248 }, { target := 159, numerator := 1812623706051718879534645248 }, { target := 160, numerator := 956109207587719848545746944 }, { target := 161, numerator := 22368971669187695623268204544 }, { target := 162, numerator := 1792704764226974716023275520 }, { target := 163, numerator := 836595556639254867477528576 }, { target := 164, numerator := 1812623706051718879534645248 }, { target := 165, numerator := 69716296386604572289794048 }, { target := 166, numerator := 1792704764226974716023275520 }, { target := 167, numerator := 69716296386604572289794048 }, { target := 168, numerator := 1812623706051718879534645248 }, { target := 169, numerator := 1812623706051718879534645248 }, { target := 170, numerator := 59756825474232490534109184 }, { target := 187, numerator := 1565251982579558254305607680 }, { target := 188, numerator := 26296233307336578672334209024 }, { target := 189, numerator := 56975172165895920456724119552 }, { target := 190, numerator := 1878302379095469905166729216 }, { target := 191, numerator := 30052838065527518482667667456 }, { target := 192, numerator := 2191352775611381556027850752 }, { target := 193, numerator := 56975172165895920456724119552 }, { target := 194, numerator := 56975172165895920456724119552 }, { target := 195, numerator := 30052838065527518482667667456 }, { target := 196, numerator := 703111190574737567834078969856 }, { target := 197, numerator := 56349071372864097155001876480 }, { target := 198, numerator := 26296233307336578672334209024 }, { target := 199, numerator := 56975172165895920456724119552 }, { target := 200, numerator := 2191352775611381556027850752 }, { target := 201, numerator := 56349071372864097155001876480 }, { target := 202, numerator := 2191352775611381556027850752 }, { target := 203, numerator := 56975172165895920456724119552 }, { target := 204, numerator := 56975172165895920456724119552 }, { target := 205, numerator := 1878302379095469905166729216 }, { target := 222, numerator := 49797354561860408778424320 }, { target := 223, numerator := 836595556639254867477528576 }, { target := 224, numerator := 1812623706051718879534645248 }, { target := 225, numerator := 59756825474232490534109184 }, { target := 226, numerator := 956109207587719848545746944 }, { target := 227, numerator := 69716296386604572289794048 }, { target := 228, numerator := 1812623706051718879534645248 }, { target := 229, numerator := 1812623706051718879534645248 }, { target := 230, numerator := 956109207587719848545746944 }, { target := 231, numerator := 22368971669187695623268204544 }, { target := 232, numerator := 1792704764226974716023275520 }, { target := 233, numerator := 836595556639254867477528576 }, { target := 234, numerator := 1812623706051718879534645248 }, { target := 235, numerator := 69716296386604572289794048 }, { target := 236, numerator := 1792704764226974716023275520 }, { target := 237, numerator := 69716296386604572289794048 }, { target := 238, numerator := 1812623706051718879534645248 }, { target := 239, numerator := 1812623706051718879534645248 }, { target := 240, numerator := 59756825474232490534109184 }]

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
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 283, numerator := 49797354561860408778424320 }, { target := 284, numerator := 836595556639254867477528576 }, { target := 285, numerator := 1812623706051718879534645248 }, { target := 286, numerator := 59756825474232490534109184 }, { target := 287, numerator := 956109207587719848545746944 }, { target := 288, numerator := 69716296386604572289794048 }, { target := 289, numerator := 1812623706051718879534645248 }, { target := 290, numerator := 1812623706051718879534645248 }, { target := 291, numerator := 956109207587719848545746944 }, { target := 292, numerator := 22368971669187695623268204544 }, { target := 293, numerator := 1792704764226974716023275520 }, { target := 294, numerator := 836595556639254867477528576 }, { target := 295, numerator := 1812623706051718879534645248 }, { target := 296, numerator := 69716296386604572289794048 }, { target := 297, numerator := 1792704764226974716023275520 }, { target := 298, numerator := 69716296386604572289794048 }, { target := 299, numerator := 1812623706051718879534645248 }, { target := 300, numerator := 1812623706051718879534645248 }, { target := 301, numerator := 59756825474232490534109184 }, { target := 318, numerator := 51143229009478257664327680 }, { target := 319, numerator := 859206247359234728760705024 }, { target := 320, numerator := 1861613535945008578981527552 }, { target := 321, numerator := 61371874811373909197193216 }, { target := 322, numerator := 981949996981982547155091456 }, { target := 323, numerator := 71600520613269560730058752 }, { target := 324, numerator := 1861613535945008578981527552 }, { target := 325, numerator := 1861613535945008578981527552 }, { target := 326, numerator := 981949996981982547155091456 }, { target := 327, numerator := 22973538471057633342815993856 }, { target := 328, numerator := 1841156244341217275915796480 }, { target := 329, numerator := 859206247359234728760705024 }, { target := 330, numerator := 1861613535945008578981527552 }, { target := 331, numerator := 71600520613269560730058752 }, { target := 332, numerator := 1841156244341217275915796480 }, { target := 333, numerator := 71600520613269560730058752 }, { target := 334, numerator := 1861613535945008578981527552 }, { target := 335, numerator := 1861613535945008578981527552 }, { target := 336, numerator := 61371874811373909197193216 }, { target := 419, numerator := 51143229009478257664327680 }, { target := 420, numerator := 859206247359234728760705024 }, { target := 421, numerator := 1861613535945008578981527552 }, { target := 422, numerator := 61371874811373909197193216 }, { target := 423, numerator := 981949996981982547155091456 }, { target := 424, numerator := 71600520613269560730058752 }, { target := 425, numerator := 1861613535945008578981527552 }, { target := 426, numerator := 1861613535945008578981527552 }, { target := 427, numerator := 981949996981982547155091456 }, { target := 428, numerator := 22973538471057633342815993856 }, { target := 429, numerator := 1841156244341217275915796480 }, { target := 430, numerator := 859206247359234728760705024 }, { target := 431, numerator := 1861613535945008578981527552 }, { target := 432, numerator := 71600520613269560730058752 }, { target := 433, numerator := 1841156244341217275915796480 }, { target := 434, numerator := 71600520613269560730058752 }, { target := 435, numerator := 1861613535945008578981527552 }, { target := 436, numerator := 1861613535945008578981527552 }, { target := 437, numerator := 61371874811373909197193216 }]

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
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 454, numerator := 865397269818276833635860480 }, { target := 455, numerator := 14538674132947050805082456064 }, { target := 456, numerator := 31500460621385276744345321472 }, { target := 457, numerator := 1038476723781932200363032576 }, { target := 458, numerator := 16615627580510915205808521216 }, { target := 459, numerator := 1211556177745587567090204672 }, { target := 460, numerator := 31500460621385276744345321472 }, { target := 461, numerator := 31500460621385276744345321472 }, { target := 462, numerator := 16615627580510915205808521216 }, { target := 463, numerator := 388736453602369953669228527616 }, { target := 464, numerator := 31154301713457966010890977280 }, { target := 465, numerator := 14538674132947050805082456064 }, { target := 466, numerator := 31500460621385276744345321472 }, { target := 467, numerator := 1211556177745587567090204672 }, { target := 468, numerator := 31154301713457966010890977280 }, { target := 469, numerator := 1211556177745587567090204672 }, { target := 470, numerator := 31500460621385276744345321472 }, { target := 471, numerator := 31500460621385276744345321472 }, { target := 472, numerator := 1038476723781932200363032576 }, { target := 489, numerator := 47105605666624711006617600 }, { target := 490, numerator := 791374175199295144911175680 }, { target := 491, numerator := 1714644046265139480640880640 }, { target := 492, numerator := 56526726799949653207941120 }, { target := 493, numerator := 904427628799194451327057920 }, { target := 494, numerator := 65947847933274595409264640 }, { target := 495, numerator := 1714644046265139480640880640 }, { target := 496, numerator := 1714644046265139480640880640 }, { target := 497, numerator := 904427628799194451327057920 }, { target := 498, numerator := 21159838065447820184172625920 }, { target := 499, numerator := 1695801803998489596238233600 }, { target := 500, numerator := 791374175199295144911175680 }, { target := 501, numerator := 1714644046265139480640880640 }, { target := 502, numerator := 65947847933274595409264640 }, { target := 503, numerator := 1695801803998489596238233600 }, { target := 504, numerator := 65947847933274595409264640 }, { target := 505, numerator := 1714644046265139480640880640 }, { target := 506, numerator := 1714644046265139480640880640 }, { target := 507, numerator := 56526726799949653207941120 }, { target := 550, numerator := 1565251982579558254305607680 }, { target := 551, numerator := 26296233307336578672334209024 }, { target := 552, numerator := 56975172165895920456724119552 }, { target := 553, numerator := 1878302379095469905166729216 }, { target := 554, numerator := 30052838065527518482667667456 }, { target := 555, numerator := 2191352775611381556027850752 }, { target := 556, numerator := 56975172165895920456724119552 }, { target := 557, numerator := 56975172165895920456724119552 }, { target := 558, numerator := 30052838065527518482667667456 }, { target := 559, numerator := 703111190574737567834078969856 }, { target := 560, numerator := 56349071372864097155001876480 }, { target := 561, numerator := 26296233307336578672334209024 }, { target := 562, numerator := 56975172165895920456724119552 }, { target := 563, numerator := 2191352775611381556027850752 }, { target := 564, numerator := 56349071372864097155001876480 }, { target := 565, numerator := 2191352775611381556027850752 }, { target := 566, numerator := 56975172165895920456724119552 }, { target := 567, numerator := 56975172165895920456724119552 }, { target := 568, numerator := 1878302379095469905166729216 }]

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
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 585, numerator := 865397269818276833635860480 }, { target := 586, numerator := 14538674132947050805082456064 }, { target := 587, numerator := 31500460621385276744345321472 }, { target := 588, numerator := 1038476723781932200363032576 }, { target := 589, numerator := 16615627580510915205808521216 }, { target := 590, numerator := 1211556177745587567090204672 }, { target := 591, numerator := 31500460621385276744345321472 }, { target := 592, numerator := 31500460621385276744345321472 }, { target := 593, numerator := 16615627580510915205808521216 }, { target := 594, numerator := 388736453602369953669228527616 }, { target := 595, numerator := 31154301713457966010890977280 }, { target := 596, numerator := 14538674132947050805082456064 }, { target := 597, numerator := 31500460621385276744345321472 }, { target := 598, numerator := 1211556177745587567090204672 }, { target := 599, numerator := 31154301713457966010890977280 }, { target := 600, numerator := 1211556177745587567090204672 }, { target := 601, numerator := 31500460621385276744345321472 }, { target := 602, numerator := 31500460621385276744345321472 }, { target := 603, numerator := 1038476723781932200363032576 }, { target := 660, numerator := 64601973485656746523361280 }, { target := 661, numerator := 1085313154559033341592469504 }, { target := 662, numerator := 2351511834877905573450350592 }, { target := 663, numerator := 77522368182788095828033536 }, { target := 664, numerator := 1240357890924609533248536576 }, { target := 665, numerator := 90442762879919445132705792 }, { target := 666, numerator := 2351511834877905573450350592 }, { target := 667, numerator := 2351511834877905573450350592 }, { target := 668, numerator := 1240357890924609533248536576 }, { target := 669, numerator := 29019206489757010538293886976 }, { target := 670, numerator := 2325671045483642874841006080 }, { target := 671, numerator := 1085313154559033341592469504 }, { target := 672, numerator := 2351511834877905573450350592 }, { target := 673, numerator := 90442762879919445132705792 }, { target := 674, numerator := 2325671045483642874841006080 }, { target := 675, numerator := 90442762879919445132705792 }, { target := 676, numerator := 2351511834877905573450350592 }, { target := 677, numerator := 2351511834877905573450350592 }, { target := 678, numerator := 77522368182788095828033536 }, { target := 766, numerator := 49797354561860408778424320 }, { target := 767, numerator := 836595556639254867477528576 }, { target := 768, numerator := 1812623706051718879534645248 }, { target := 769, numerator := 59756825474232490534109184 }, { target := 770, numerator := 956109207587719848545746944 }, { target := 771, numerator := 69716296386604572289794048 }, { target := 772, numerator := 1812623706051718879534645248 }, { target := 773, numerator := 1812623706051718879534645248 }, { target := 774, numerator := 956109207587719848545746944 }, { target := 775, numerator := 22368971669187695623268204544 }, { target := 776, numerator := 1792704764226974716023275520 }, { target := 777, numerator := 836595556639254867477528576 }, { target := 778, numerator := 1812623706051718879534645248 }, { target := 779, numerator := 69716296386604572289794048 }, { target := 780, numerator := 1792704764226974716023275520 }, { target := 781, numerator := 69716296386604572289794048 }, { target := 782, numerator := 1812623706051718879534645248 }, { target := 783, numerator := 1812623706051718879534645248 }, { target := 784, numerator := 59756825474232490534109184 }]

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
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 5300878460514273355961991168 }, { target := 112, numerator := 199167621332096026576028696576 }, { target := 115, numerator := 199152557863535827653232689152 }, { target := 122, numerator := 5315941929074472278757998592 }, { target := 206, numerator := 555787546094696447650773860352 }, { target := 208, numerator := 20882365884492307995758442840064 }, { target := 211, numerator := 20880786506981748106829787824128 }, { target := 218, numerator := 557366923605256336579428876288 }, { target := 257, numerator := 117555184486639332708948377600 }, { target := 260, numerator := 403546393734192935087877652480 }, { target := 262, numerator := 117555184486639332708948377600 }, { target := 353, numerator := 9842793899156596862199854530560 }, { target := 356, numerator := 33788590436221877251485034610688 }, { target := 358, numerator := 9842793899156596862199854530560 }, { target := 389, numerator := 122034742963742735601292541952 }, { target := 391, numerator := 122034742963742735601292541952 }, { target := 695, numerator := 9842797461255010678855560069120 }, { target := 698, numerator := 33788602664282896417979709259776 }, { target := 700, numerator := 9842797461255010678855560069120 }, { target := 731, numerator := 1182037439329272605481206022144 }, { target := 733, numerator := 1182037439329272605481206022144 }, { target := 801, numerator := 47105605666624711006617600 }, { target := 802, numerator := 791374175199295144911175680 }, { target := 803, numerator := 1714644046265139480640880640 }, { target := 804, numerator := 56526726799949653207941120 }, { target := 805, numerator := 904427628799194451327057920 }, { target := 806, numerator := 65947847933274595409264640 }, { target := 807, numerator := 1714644046265139480640880640 }, { target := 808, numerator := 1714644046265139480640880640 }, { target := 809, numerator := 904427628799194451327057920 }, { target := 810, numerator := 21159838065447820184172625920 }, { target := 811, numerator := 1695801803998489596238233600 }, { target := 812, numerator := 791374175199295144911175680 }, { target := 813, numerator := 1714644046265139480640880640 }, { target := 814, numerator := 65947847933274595409264640 }, { target := 815, numerator := 1695801803998489596238233600 }, { target := 816, numerator := 65947847933274595409264640 }, { target := 817, numerator := 1714644046265139480640880640 }, { target := 818, numerator := 1714644046265139480640880640 }, { target := 819, numerator := 56526726799949653207941120 }, { target := 876, numerator := 63256099038038897637457920 }, { target := 877, numerator := 1062702463839053480309293056 }, { target := 878, numerator := 2302522004984615874003468288 }, { target := 879, numerator := 75907318845646677164949504 }, { target := 880, numerator := 1214517101530346834639192064 }, { target := 881, numerator := 88558538653254456692441088 }, { target := 882, numerator := 2302522004984615874003468288 }, { target := 883, numerator := 2302522004984615874003468288 }, { target := 884, numerator := 1214517101530346834639192064 }, { target := 885, numerator := 28414639687887072818746097664 }, { target := 886, numerator := 2277219565369400314948485120 }, { target := 887, numerator := 1062702463839053480309293056 }, { target := 888, numerator := 2302522004984615874003468288 }, { target := 889, numerator := 88558538653254456692441088 }, { target := 890, numerator := 2277219565369400314948485120 }, { target := 891, numerator := 88558538653254456692441088 }, { target := 892, numerator := 2302522004984615874003468288 }, { target := 893, numerator := 2302522004984615874003468288 }, { target := 894, numerator := 75907318845646677164949504 }, { target := 982, numerator := 117551622388225516053242839040 }, { target := 985, numerator := 403534165673173768593203003392 }, { target := 987, numerator := 117551622388225516053242839040 }, { target := 992, numerator := 122034742963742735601292541952 }, { target := 994, numerator := 122034742963742735601292541952 }]

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
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 7870524489392763790216396800 }, { target := 15, numerator := 6121519047305482947946086400 }, { target := 16, numerator := 6996021768349123369081241600 }, { target := 17, numerator := 8220325577810219958670458880 }, { target := 18, numerator := 97069802035844086746002227200 }, { target := 19, numerator := 218275879172492649115334737920 }, { target := 20, numerator := 6121519047305482947946086400 }, { target := 21, numerator := 97069802035844086746002227200 }, { target := 22, numerator := 6996021768349123369081241600 }, { target := 23, numerator := 6821121224140395284854210560 }, { target := 24, numerator := 6821121224140395284854210560 }, { target := 25, numerator := 6821121224140395284854210560 }, { target := 26, numerator := 218275879172492649115334737920 }, { target := 27, numerator := 6821121224140395284854210560 }, { target := 28, numerator := 7870524489392763790216396800 }, { target := 29, numerator := 8220325577810219958670458880 }, { target := 56, numerator := 1022095187857075560320598016 }, { target := 57, numerator := 163174627784099903705094029312 }, { target := 59, numerator := 1628237403135721100904960622592 }, { target := 67, numerator := 163174627784099903705094029312 }, { target := 74, numerator := 1021978563577310946495823872 }, { target := 136, numerator := 26909856479410507361298677760 }, { target := 137, numerator := 20929888372874839058787860480 }, { target := 138, numerator := 23919872426142673210043269120 }, { target := 139, numerator := 28105850100717641021800841216 }, { target := 140, numerator := 331888229912729590789350359040 }, { target := 141, numerator := 746300019695651404153349996544 }, { target := 142, numerator := 20929888372874839058787860480 }, { target := 143, numerator := 331888229912729590789350359040 }, { target := 144, numerator := 23919872426142673210043269120 }, { target := 145, numerator := 23321875615489106379792187392 }, { target := 146, numerator := 23321875615489106379792187392 }, { target := 147, numerator := 23321875615489106379792187392 }, { target := 148, numerator := 746300019695651404153349996544 }, { target := 149, numerator := 23321875615489106379792187392 }, { target := 150, numerator := 26909856479410507361298677760 }, { target := 151, numerator := 28105850100717641021800841216 }, { target := 152, numerator := 35770783277957547453734453248 }, { target := 153, numerator := 5710705143973955568781110542336 }, { target := 155, numerator := 56984249573413231095131905458176 }, { target := 163, numerator := 5710705143973955568781110542336 }, { target := 170, numerator := 35766701718934503461555798016 }, { target := 283, numerator := 35770800822171248638983929856 }, { target := 284, numerator := 5710707944858427452160781320192 }, { target := 286, numerator := 56984277522028287944953190940672 }, { target := 294, numerator := 5710707944858427452160781320192 }, { target := 301, numerator := 35766719261146354612439089152 }, { target := 302, numerator := 5990834237902053536931250176000 }, { target := 304, numerator := 225091032334680987885247660032000 }, { target := 307, numerator := 225074008223703116905986392064000 }, { target := 314, numerator := 6007858348879924516192518144000 }, { target := 660, numerator := 1022086415750224967695859712 }, { target := 661, numerator := 163173227341863962015258640384 }, { target := 663, numerator := 1628223428828192675994317881344 }, { target := 671, numerator := 163173227341863962015258640384 }, { target := 678, numerator := 1021969792471385371054178304 }, { target := 679, numerator := 555787970063220842937773457408 }, { target := 681, numerator := 20882381814078913778052818272256 }, { target := 684, numerator := 20880802435363565553508797120512 }, { target := 691, numerator := 557367348778569067481794609152 }, { target := 966, numerator := 5300878460514273355961991168 }, { target := 968, numerator := 199167621332096026576028696576 }, { target := 971, numerator := 199152557863535827653232689152 }, { target := 978, numerator := 5315941929074472278757998592 }]

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
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 5110835244378725764877516800 }, { target := 112, numerator := 185218360948740809257752985600 }, { target := 115, numerator := 185218429015765586116870144000 }, { target := 122, numerator := 5110767177353948905760358400 }, { target := 206, numerator := 754843619599042448078982348800 }, { target := 208, numerator := 27355782628392062216369183129600 }, { target := 211, numerator := 27355792681535413768058568704000 }, { target := 218, numerator := 754833566455690896389596774400 }, { target := 257, numerator := 49322381511823421353054175232 }, { target := 260, numerator := 167189552784139844668266381312 }, { target := 262, numerator := 49322381511823421353054175232 }, { target := 267, numerator := 7870521947200846132118814720 }, { target := 268, numerator := 6121517070045102547203522560 }, { target := 269, numerator := 6996019508622974339661168640 }, { target := 270, numerator := 8220322922631994849101873152 }, { target := 271, numerator := 97069770682143768962798714880 }, { target := 272, numerator := 218275808669036799397428461568 }, { target := 273, numerator := 6121517070045102547203522560 }, { target := 274, numerator := 97069770682143768962798714880 }, { target := 275, numerator := 6996019508622974339661168640 }, { target := 276, numerator := 6821119020907399981169639424 }, { target := 277, numerator := 6821119020907399981169639424 }, { target := 278, numerator := 6821119020907399981169639424 }, { target := 279, numerator := 218275808669036799397428461568 }, { target := 280, numerator := 6821119020907399981169639424 }, { target := 281, numerator := 7870521947200846132118814720 }, { target := 282, numerator := 8220322922631994849101873152 }, { target := 302, numerator := 7867608808219296032224182272000 }, { target := 304, numerator := 285124747397603645200346906624000 }, { target := 307, numerator := 285124852179835526517106933760000 }, { target := 314, numerator := 7867504025987414715464155136000 }, { target := 353, numerator := 4147481669054525217902023409664 }, { target := 356, numerator := 14058842743905631259778376269824 }, { target := 358, numerator := 4147481669054525217902023409664 }, { target := 389, numerator := 1499068016322140176635658240 }, { target := 391, numerator := 1499068016322140176635658240 }, { target := 656, numerator := 35880918326162193905279303680 }, { target := 658, numerator := 35880918326162193905279303680 }, { target := 679, numerator := 754843619599042448078982348800 }, { target := 681, numerator := 27355782628392062216369183129600 }, { target := 684, numerator := 27355792681535413768058568704000 }, { target := 691, numerator := 754833566455690896389596774400 }, { target := 695, numerator := 4147480668458466714191124234240 }, { target := 698, numerator := 14058839352155224830065340579840 }, { target := 700, numerator := 4147480668458466714191124234240 }, { target := 731, numerator := 26838153195444767678477107200 }, { target := 733, numerator := 26838153195444767678477107200 }, { target := 745, numerator := 31141929113272847540431093760 }, { target := 747, numerator := 31141929113272847540431093760 }, { target := 872, numerator := 1499068016322140176635658240 }, { target := 874, numerator := 1499068016322140176635658240 }, { target := 947, numerator := 31093572080488262373442846720 }, { target := 949, numerator := 31093572080488262373442846720 }, { target := 961, numerator := 31238643178842017874407587840 }, { target := 963, numerator := 31238643178842017874407587840 }, { target := 982, numerator := 49323382107881925063953350656 }, { target := 985, numerator := 167192944534546274381302071296 }, { target := 987, numerator := 49323382107881925063953350656 }, { target := 992, numerator := 1499068016322140176635658240 }, { target := 994, numerator := 1499068016322140176635658240 }, { target := 1006, numerator := 35880918326162193905279303680 }, { target := 1008, numerator := 35880918326162193905279303680 }, { target := 1011, numerator := 1499068016322140176635658240 }, { target := 1013, numerator := 1499068016322140176635658240 }]

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
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 1798881619586568211962789888 }, { target := 5, numerator := 43057101991394632686335164416 }, { target := 6, numerator := 32205783834533721214172528640 }, { target := 7, numerator := 37370314935927417048517312512 }, { target := 8, numerator := 1798881619586568211962789888 }, { target := 9, numerator := 37312286496585914848131416064 }, { target := 10, numerator := 37486371814610421449289105408 }, { target := 11, numerator := 1798881619586568211962789888 }, { target := 12, numerator := 43057101991394632686335164416 }, { target := 13, numerator := 1798881619586568211962789888 }, { target := 14, numerator := 48890486752525492969927606272 }, { target := 15, numerator := 4111163966173137081142811295744 }, { target := 20, numerator := 4111162974338865429478417367040 }, { target := 28, numerator := 48891478586797144634321534976 }, { target := 56, numerator := 5126471794134898636906037248 }, { target := 57, numerator := 757153056168920538288402464768 }, { target := 59, numerator := 7891679679360590195722205265920 }, { target := 67, numerator := 757153056168920538288402464768 }, { target := 74, numerator := 5126471794134898636906037248 }, { target := 126, numerator := 1798881619586568211962789888 }, { target := 127, numerator := 43057101991394632686335164416 }, { target := 128, numerator := 32205783834533721214172528640 }, { target := 129, numerator := 37370314935927417048517312512 }, { target := 130, numerator := 1798881619586568211962789888 }, { target := 131, numerator := 37312286496585914848131416064 }, { target := 132, numerator := 37486371814610421449289105408 }, { target := 133, numerator := 1798881619586568211962789888 }, { target := 134, numerator := 43057101991394632686335164416 }, { target := 135, numerator := 1798881619586568211962789888 }, { target := 136, numerator := 165725546192334767219332349952 }, { target := 137, numerator := 13935735539493147623528127791104 }, { target := 142, numerator := 13935732177442832318418533744640 }, { target := 150, numerator := 165728908242650072328926396416 }, { target := 152, numerator := 185785034687620809467380105216 }, { target := 153, numerator := 27439477374110655494538244653056 }, { target := 155, numerator := 285997083735250704511441452400640 }, { target := 163, numerator := 27439477374110655494538244653056 }, { target := 170, numerator := 185785034687620809467380105216 }, { target := 257, numerator := 7870524489392763790216396800 }, { target := 260, numerator := 26909856479410507361298677760 }, { target := 262, numerator := 7870521947200846132118814720 }, { target := 267, numerator := 48890486752525492969927606272 }, { target := 268, numerator := 4111163966173137081142811295744 }, { target := 273, numerator := 4111162974338865429478417367040 }, { target := 281, numerator := 48891478586797144634321534976 }, { target := 283, numerator := 185785102962895973745782947840 }, { target := 284, numerator := 27439487458011499453241297469440 }, { target := 286, numerator := 285997188838062785351776835993600 }, { target := 294, numerator := 27439487458011499453241297469440 }, { target := 301, numerator := 185785102962895973745782947840 }, { target := 353, numerator := 6121519047305482947946086400 }, { target := 356, numerator := 20929888372874839058787860480 }, { target := 358, numerator := 6121517070045102547203522560 }, { target := 660, numerator := 5126403518859734358503194624 }, { target := 661, numerator := 757142972268076579585349648384 }, { target := 663, numerator := 7891574576548509355386821672960 }, { target := 671, numerator := 757142972268076579585349648384 }, { target := 678, numerator := 5126403518859734358503194624 }, { target := 966, numerator := 5110835244378725764877516800 }, { target := 968, numerator := 185218360948740809257752985600 }, { target := 971, numerator := 185218429015765586116870144000 }, { target := 978, numerator := 5110767177353948905760358400 }]

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
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected,
    Slot17.Left11.expected,
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 1024969471287494782931173376 }, { target := 112, numerator := 35871376031832568678295011328 }, { target := 115, numerator := 35871393625383203781388271616 }, { target := 122, numerator := 1024960674512177231384543232 }, { target := 206, numerator := 163633499065832468113713528832 }, { target := 208, numerator := 5726764494772532496702317264896 }, { target := 211, numerator := 5726767303533507394377206464512 }, { target := 218, numerator := 163632094685345019276268929024 }, { target := 302, numerator := 1632816248476372735046988070912 }, { target := 304, numerator := 57144497744317092824870746587136 }, { target := 307, numerator := 57144525771527805065158346145792 }, { target := 314, numerator := 1632802234871016614903188291584 }, { target := 379, numerator := 6996021768349123369081241600 }, { target := 382, numerator := 23919872426142673210043269120 }, { target := 384, numerator := 6996019508622974339661168640 }, { target := 524, numerator := 8220325577810219958670458880 }, { target := 527, numerator := 28105850100717641021800841216 }, { target := 529, numerator := 8220322922631994849101873152 }, { target := 620, numerator := 97069802035844086746002227200 }, { target := 623, numerator := 331888229912729590789350359040 }, { target := 625, numerator := 97069770682143768962798714880 }, { target := 646, numerator := 218275879172492649115334737920 }, { target := 649, numerator := 746300019695651404153349996544 }, { target := 651, numerator := 218275808669036799397428461568 }, { target := 679, numerator := 163633499065832468113713528832 }, { target := 681, numerator := 5726764494772532496702317264896 }, { target := 684, numerator := 5726767303533507394377206464512 }, { target := 691, numerator := 163632094685345019276268929024 }, { target := 695, numerator := 6121519047305482947946086400 }, { target := 698, numerator := 20929888372874839058787860480 }, { target := 700, numerator := 6121517070045102547203522560 }, { target := 721, numerator := 97069802035844086746002227200 }, { target := 724, numerator := 331888229912729590789350359040 }, { target := 726, numerator := 97069770682143768962798714880 }, { target := 735, numerator := 6996021768349123369081241600 }, { target := 738, numerator := 23919872426142673210043269120 }, { target := 740, numerator := 6996019508622974339661168640 }, { target := 836, numerator := 6821121224140395284854210560 }, { target := 839, numerator := 23321875615489106379792187392 }, { target := 841, numerator := 6821119020907399981169639424 }, { target := 862, numerator := 6821121224140395284854210560 }, { target := 865, numerator := 23321875615489106379792187392 }, { target := 867, numerator := 6821119020907399981169639424 }, { target := 911, numerator := 6821121224140395284854210560 }, { target := 914, numerator := 23321875615489106379792187392 }, { target := 916, numerator := 6821119020907399981169639424 }, { target := 937, numerator := 218275879172492649115334737920 }, { target := 940, numerator := 746300019695651404153349996544 }, { target := 942, numerator := 218275808669036799397428461568 }, { target := 951, numerator := 6821121224140395284854210560 }, { target := 954, numerator := 23321875615489106379792187392 }, { target := 956, numerator := 6821119020907399981169639424 }, { target := 966, numerator := 1024852519042938930034900992 }, { target := 968, numerator := 35867282994859516125958373376 }, { target := 971, numerator := 35867300586402671695151235072 }, { target := 978, numerator := 1024843723271361145438470144 }, { target := 982, numerator := 7870524489392763790216396800 }, { target := 985, numerator := 26909856479410507361298677760 }, { target := 987, numerator := 7870521947200846132118814720 }, { target := 996, numerator := 8220325577810219958670458880 }, { target := 999, numerator := 28105850100717641021800841216 }, { target := 1001, numerator := 8220322922631994849101873152 }]

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
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot23.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 125424596934957811590217334784 }, { target := 6, numerator := 1214871812643974622300128411648 }, { target := 11, numerator := 125424596934957811590217334784 }, { target := 14, numerator := 117124894645912248767846809600 }, { target := 15, numerator := 9806766103039625424197658869760 }, { target := 20, numerator := 9806769652099611664657699307520 }, { target := 28, numerator := 117121345585926008307806371840 }, { target := 56, numerator := 5300878460514273355961991168 }, { target := 57, numerator := 555787546094696447650773860352 }, { target := 59, numerator := 5990834237902053536931250176000 }, { target := 67, numerator := 555787970063220842937773457408 }, { target := 74, numerator := 5300878460514273355961991168 }, { target := 110, numerator := 65735341441545461374648320 }, { target := 111, numerator := 64365855161513264262676480 }, { target := 112, numerator := 50670992361191293142958080 }, { target := 113, numerator := 1592712543677445241223249920 }, { target := 114, numerator := 50670992361191293142958080 }, { target := 115, numerator := 50670992361191293142958080 }, { target := 116, numerator := 52040478641223490254929920 }, { target := 117, numerator := 52040478641223490254929920 }, { target := 118, numerator := 880579678060702742997893120 }, { target := 119, numerator := 47932019801126898919014400 }, { target := 120, numerator := 1592712543677445241223249920 }, { target := 121, numerator := 880579678060702742997893120 }, { target := 122, numerator := 65735341441545461374648320 }, { target := 123, numerator := 50670992361191293142958080 }, { target := 124, numerator := 47932019801126898919014400 }, { target := 125, numerator := 64365855161513264262676480 }, { target := 126, numerator := 125424596934957811590217334784 }, { target := 128, numerator := 1214871812643974622300128411648 }, { target := 133, numerator := 125424596934957811590217334784 }, { target := 136, numerator := 402069283947464556848170926080 }, { target := 137, numerator := 33664913311638341829627475918848 }, { target := 142, numerator := 33664925494940718905468802564096 }, { target := 150, numerator := 402057100645087481006844280832 }, { target := 152, numerator := 199167621332096026576028696576 }, { target := 153, numerator := 20882365884492307995758442840064 }, { target := 155, numerator := 225091032334680987885247660032000 }, { target := 163, numerator := 20882381814078913778052818272256 }, { target := 170, numerator := 199167621332096026576028696576 }, { target := 267, numerator := 117124894645912248767846809600 }, { target := 268, numerator := 9806766103039625424197658869760 }, { target := 273, numerator := 9806769652099611664657699307520 }, { target := 281, numerator := 117121345585926008307806371840 }, { target := 283, numerator := 199152557863535827653232689152 }, { target := 284, numerator := 20880786506981748106829787824128 }, { target := 286, numerator := 225074008223703116905986392064000 }, { target := 294, numerator := 20880802435363565553508797120512 }, { target := 301, numerator := 199152557863535827653232689152 }, { target := 660, numerator := 5315941929074472278757998592 }, { target := 661, numerator := 557366923605256336579428876288 }, { target := 663, numerator := 6007858348879924516192518144000 }, { target := 671, numerator := 557367348778569067481794609152 }, { target := 678, numerator := 5315941929074472278757998592 }]

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
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 206, numerator := 1104353736217963751094091776 }, { target := 207, numerator := 1081346366713422839612964864 }, { target := 208, numerator := 851272671668013724801695744 }, { target := 209, numerator := 26757570733781080052550598656 }, { target := 210, numerator := 851272671668013724801695744 }, { target := 211, numerator := 851272671668013724801695744 }, { target := 212, numerator := 874280041172554636282822656 }, { target := 213, numerator := 874280041172554636282822656 }, { target := 214, numerator := 14793738591419806082364604416 }, { target := 215, numerator := 805257932658931901839441920 }, { target := 216, numerator := 26757570733781080052550598656 }, { target := 217, numerator := 14793738591419806082364604416 }, { target := 218, numerator := 1104353736217963751094091776 }, { target := 219, numerator := 851272671668013724801695744 }, { target := 220, numerator := 805257932658931901839441920 }, { target := 221, numerator := 1081346366713422839612964864 }, { target := 241, numerator := 2392766428472254794037198848 }, { target := 242, numerator := 2342917127879082819161423872 }, { target := 243, numerator := 1844424121947363070403674112 }, { target := 244, numerator := 57974736589859006780526297088 }, { target := 245, numerator := 1844424121947363070403674112 }, { target := 246, numerator := 1844424121947363070403674112 }, { target := 247, numerator := 1894273422540535045279449088 }, { target := 248, numerator := 1894273422540535045279449088 }, { target := 249, numerator := 32053100281409579845123309568 }, { target := 250, numerator := 1744725520761019120652124160 }, { target := 251, numerator := 57974736589859006780526297088 }, { target := 252, numerator := 32053100281409579845123309568 }, { target := 253, numerator := 2392766428472254794037198848 }, { target := 254, numerator := 1844424121947363070403674112 }, { target := 255, numerator := 1744725520761019120652124160 }, { target := 256, numerator := 2342917127879082819161423872 }, { target := 302, numerator := 78882409729854553649577984 }, { target := 303, numerator := 77239026193815917115211776 }, { target := 304, numerator := 60805190833429551771549696 }, { target := 305, numerator := 1911255052412934289467899904 }, { target := 306, numerator := 60805190833429551771549696 }, { target := 307, numerator := 60805190833429551771549696 }, { target := 308, numerator := 62448574369468188305915904 }, { target := 309, numerator := 62448574369468188305915904 }, { target := 310, numerator := 1056695613672843291597471744 }, { target := 311, numerator := 57518423761352278702817280 }, { target := 312, numerator := 1911255052412934289467899904 }, { target := 313, numerator := 1056695613672843291597471744 }, { target := 314, numerator := 78882409729854553649577984 }, { target := 315, numerator := 60805190833429551771549696 }, { target := 316, numerator := 57518423761352278702817280 }, { target := 317, numerator := 77239026193815917115211776 }, { target := 337, numerator := 1262118555677672858393247744 }, { target := 338, numerator := 1235824419101054673843388416 }, { target := 339, numerator := 972883053334872828344795136 }, { target := 340, numerator := 30580080838606948631486398464 }, { target := 341, numerator := 972883053334872828344795136 }, { target := 342, numerator := 972883053334872828344795136 }, { target := 343, numerator := 999177189911491012894654464 }, { target := 344, numerator := 999177189911491012894654464 }, { target := 345, numerator := 16907129818765492665559547904 }, { target := 346, numerator := 920294780181636459245076480 }, { target := 347, numerator := 30580080838606948631486398464 }, { target := 348, numerator := 16907129818765492665559547904 }, { target := 349, numerator := 1262118555677672858393247744 }, { target := 350, numerator := 972883053334872828344795136 }, { target := 351, numerator := 920294780181636459245076480 }, { target := 352, numerator := 1235824419101054673843388416 }]

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
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected,
    Slot23.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 363, numerator := 92029478018163645924507648 }, { target := 364, numerator := 90112197226118569967747072 }, { target := 365, numerator := 70939389305667810400141312 }, { target := 366, numerator := 2229797561148423337712549888 }, { target := 367, numerator := 70939389305667810400141312 }, { target := 368, numerator := 70939389305667810400141312 }, { target := 369, numerator := 72856670097712886356901888 }, { target := 370, numerator := 72856670097712886356901888 }, { target := 371, numerator := 1232811549284983840197050368 }, { target := 372, numerator := 67104827721577658486620160 }, { target := 373, numerator := 2229797561148423337712549888 }, { target := 374, numerator := 1232811549284983840197050368 }, { target := 375, numerator := 92029478018163645924507648 }, { target := 376, numerator := 70939389305667810400141312 }, { target := 377, numerator := 67104827721577658486620160 }, { target := 378, numerator := 90112197226118569967747072 }, { target := 473, numerator := 2392766428472254794037198848 }, { target := 474, numerator := 2342917127879082819161423872 }, { target := 475, numerator := 1844424121947363070403674112 }, { target := 476, numerator := 57974736589859006780526297088 }, { target := 477, numerator := 1844424121947363070403674112 }, { target := 478, numerator := 1844424121947363070403674112 }, { target := 479, numerator := 1894273422540535045279449088 }, { target := 480, numerator := 1894273422540535045279449088 }, { target := 481, numerator := 32053100281409579845123309568 }, { target := 482, numerator := 1744725520761019120652124160 }, { target := 483, numerator := 57974736589859006780526297088 }, { target := 484, numerator := 32053100281409579845123309568 }, { target := 485, numerator := 2392766428472254794037198848 }, { target := 486, numerator := 1844424121947363070403674112 }, { target := 487, numerator := 1744725520761019120652124160 }, { target := 488, numerator := 2342917127879082819161423872 }, { target := 508, numerator := 2392766428472254794037198848 }, { target := 509, numerator := 2342917127879082819161423872 }, { target := 510, numerator := 1844424121947363070403674112 }, { target := 511, numerator := 57974736589859006780526297088 }, { target := 512, numerator := 1844424121947363070403674112 }, { target := 513, numerator := 1844424121947363070403674112 }, { target := 514, numerator := 1894273422540535045279449088 }, { target := 515, numerator := 1894273422540535045279449088 }, { target := 516, numerator := 32053100281409579845123309568 }, { target := 517, numerator := 1744725520761019120652124160 }, { target := 518, numerator := 57974736589859006780526297088 }, { target := 519, numerator := 32053100281409579845123309568 }, { target := 520, numerator := 2392766428472254794037198848 }, { target := 521, numerator := 1844424121947363070403674112 }, { target := 522, numerator := 1744725520761019120652124160 }, { target := 523, numerator := 2342917127879082819161423872 }, { target := 569, numerator := 1262118555677672858393247744 }, { target := 570, numerator := 1235824419101054673843388416 }, { target := 571, numerator := 972883053334872828344795136 }, { target := 572, numerator := 30580080838606948631486398464 }, { target := 573, numerator := 972883053334872828344795136 }, { target := 574, numerator := 972883053334872828344795136 }, { target := 575, numerator := 999177189911491012894654464 }, { target := 576, numerator := 999177189911491012894654464 }, { target := 577, numerator := 16907129818765492665559547904 }, { target := 578, numerator := 920294780181636459245076480 }, { target := 579, numerator := 30580080838606948631486398464 }, { target := 580, numerator := 16907129818765492665559547904 }, { target := 581, numerator := 1262118555677672858393247744 }, { target := 582, numerator := 972883053334872828344795136 }, { target := 583, numerator := 920294780181636459245076480 }, { target := 584, numerator := 1235824419101054673843388416 }]

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
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected,
    Slot23.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 604, numerator := 29528315375542221249492025344 }, { target := 605, numerator := 28913142138551758306794274816 }, { target := 606, numerator := 22761409768647128879816769536 }, { target := 607, numerator := 715446474619908402357483864064 }, { target := 608, numerator := 22761409768647128879816769536 }, { target := 609, numerator := 22761409768647128879816769536 }, { target := 610, numerator := 23376583005637591822514520064 }, { target := 611, numerator := 23376583005637591822514520064 }, { target := 612, numerator := 395556391384867672154653589504 }, { target := 613, numerator := 21531063294666202994421268480 }, { target := 614, numerator := 715446474619908402357483864064 }, { target := 615, numerator := 395556391384867672154653589504 }, { target := 616, numerator := 29528315375542221249492025344 }, { target := 617, numerator := 22761409768647128879816769536 }, { target := 618, numerator := 21531063294666202994421268480 }, { target := 619, numerator := 28913142138551758306794274816 }, { target := 630, numerator := 2366472291895636609487339520 }, { target := 631, numerator := 2317170785814477513456353280 }, { target := 632, numerator := 1824155725002886553146490880 }, { target := 633, numerator := 57337651572388028684036997120 }, { target := 634, numerator := 1824155725002886553146490880 }, { target := 635, numerator := 1824155725002886553146490880 }, { target := 636, numerator := 1873457231084045649177477120 }, { target := 637, numerator := 1873457231084045649177477120 }, { target := 638, numerator := 31700868410185298747924152320 }, { target := 639, numerator := 1725552712840568361084518400 }, { target := 640, numerator := 57337651572388028684036997120 }, { target := 641, numerator := 31700868410185298747924152320 }, { target := 642, numerator := 2366472291895636609487339520 }, { target := 643, numerator := 1824155725002886553146490880 }, { target := 644, numerator := 1725552712840568361084518400 }, { target := 645, numerator := 2317170785814477513456353280 }, { target := 679, numerator := 1104353736217963751094091776 }, { target := 680, numerator := 1081346366713422839612964864 }, { target := 681, numerator := 851272671668013724801695744 }, { target := 682, numerator := 26757570733781080052550598656 }, { target := 683, numerator := 851272671668013724801695744 }, { target := 684, numerator := 851272671668013724801695744 }, { target := 685, numerator := 874280041172554636282822656 }, { target := 686, numerator := 874280041172554636282822656 }, { target := 687, numerator := 14793738591419806082364604416 }, { target := 688, numerator := 805257932658931901839441920 }, { target := 689, numerator := 26757570733781080052550598656 }, { target := 690, numerator := 14793738591419806082364604416 }, { target := 691, numerator := 1104353736217963751094091776 }, { target := 692, numerator := 851272671668013724801695744 }, { target := 693, numerator := 805257932658931901839441920 }, { target := 694, numerator := 1081346366713422839612964864 }, { target := 705, numerator := 2392766428472254794037198848 }, { target := 706, numerator := 2342917127879082819161423872 }, { target := 707, numerator := 1844424121947363070403674112 }, { target := 708, numerator := 57974736589859006780526297088 }, { target := 709, numerator := 1844424121947363070403674112 }, { target := 710, numerator := 1844424121947363070403674112 }, { target := 711, numerator := 1894273422540535045279449088 }, { target := 712, numerator := 1894273422540535045279449088 }, { target := 713, numerator := 32053100281409579845123309568 }, { target := 714, numerator := 1744725520761019120652124160 }, { target := 715, numerator := 57974736589859006780526297088 }, { target := 716, numerator := 32053100281409579845123309568 }, { target := 717, numerator := 2392766428472254794037198848 }, { target := 718, numerator := 1844424121947363070403674112 }, { target := 719, numerator := 1744725520761019120652124160 }, { target := 720, numerator := 2342917127879082819161423872 }]

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

namespace RouteChunk16

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected,
    Slot23.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 785, numerator := 92029478018163645924507648 }, { target := 786, numerator := 90112197226118569967747072 }, { target := 787, numerator := 70939389305667810400141312 }, { target := 788, numerator := 2229797561148423337712549888 }, { target := 789, numerator := 70939389305667810400141312 }, { target := 790, numerator := 70939389305667810400141312 }, { target := 791, numerator := 72856670097712886356901888 }, { target := 792, numerator := 72856670097712886356901888 }, { target := 793, numerator := 1232811549284983840197050368 }, { target := 794, numerator := 67104827721577658486620160 }, { target := 795, numerator := 2229797561148423337712549888 }, { target := 796, numerator := 1232811549284983840197050368 }, { target := 797, numerator := 92029478018163645924507648 }, { target := 798, numerator := 70939389305667810400141312 }, { target := 799, numerator := 67104827721577658486620160 }, { target := 800, numerator := 90112197226118569967747072 }, { target := 820, numerator := 2366472291895636609487339520 }, { target := 821, numerator := 2317170785814477513456353280 }, { target := 822, numerator := 1824155725002886553146490880 }, { target := 823, numerator := 57337651572388028684036997120 }, { target := 824, numerator := 1824155725002886553146490880 }, { target := 825, numerator := 1824155725002886553146490880 }, { target := 826, numerator := 1873457231084045649177477120 }, { target := 827, numerator := 1873457231084045649177477120 }, { target := 828, numerator := 31700868410185298747924152320 }, { target := 829, numerator := 1725552712840568361084518400 }, { target := 830, numerator := 57337651572388028684036997120 }, { target := 831, numerator := 31700868410185298747924152320 }, { target := 832, numerator := 2366472291895636609487339520 }, { target := 833, numerator := 1824155725002886553146490880 }, { target := 834, numerator := 1725552712840568361084518400 }, { target := 835, numerator := 2317170785814477513456353280 }, { target := 846, numerator := 92029478018163645924507648 }, { target := 847, numerator := 90112197226118569967747072 }, { target := 848, numerator := 70939389305667810400141312 }, { target := 849, numerator := 2229797561148423337712549888 }, { target := 850, numerator := 70939389305667810400141312 }, { target := 851, numerator := 70939389305667810400141312 }, { target := 852, numerator := 72856670097712886356901888 }, { target := 853, numerator := 72856670097712886356901888 }, { target := 854, numerator := 1232811549284983840197050368 }, { target := 855, numerator := 67104827721577658486620160 }, { target := 856, numerator := 2229797561148423337712549888 }, { target := 857, numerator := 1232811549284983840197050368 }, { target := 858, numerator := 92029478018163645924507648 }, { target := 859, numerator := 70939389305667810400141312 }, { target := 860, numerator := 67104827721577658486620160 }, { target := 861, numerator := 90112197226118569967747072 }, { target := 895, numerator := 2392766428472254794037198848 }, { target := 896, numerator := 2342917127879082819161423872 }, { target := 897, numerator := 1844424121947363070403674112 }, { target := 898, numerator := 57974736589859006780526297088 }, { target := 899, numerator := 1844424121947363070403674112 }, { target := 900, numerator := 1844424121947363070403674112 }, { target := 901, numerator := 1894273422540535045279449088 }, { target := 902, numerator := 1894273422540535045279449088 }, { target := 903, numerator := 32053100281409579845123309568 }, { target := 904, numerator := 1744725520761019120652124160 }, { target := 905, numerator := 57974736589859006780526297088 }, { target := 906, numerator := 32053100281409579845123309568 }, { target := 907, numerator := 2392766428472254794037198848 }, { target := 908, numerator := 1844424121947363070403674112 }, { target := 909, numerator := 1744725520761019120652124160 }, { target := 910, numerator := 2342917127879082819161423872 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk16

namespace RouteChunk17

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left17.expected,
    Slot23.Left18.expected,
    Slot24.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1063305561689799340389826560 }, { target := 57, numerator := 28354814978394649077062041600 }, { target := 58, numerator := 27114291823089883179940577280 }, { target := 59, numerator := 886087968074832783658188800 }, { target := 60, numerator := 27823162197549749406867128320 }, { target := 61, numerator := 886087968074832783658188800 }, { target := 62, numerator := 27114291823089883179940577280 }, { target := 63, numerator := 15417930644502090435652485120 }, { target := 64, numerator := 27823162197549749406867128320 }, { target := 65, numerator := 434360321950283030549244149760 }, { target := 66, numerator := 17012888987036789446237224960 }, { target := 67, numerator := 28354814978394649077062041600 }, { target := 68, numerator := 27114291823089883179940577280 }, { target := 69, numerator := 886087968074832783658188800 }, { target := 70, numerator := 17012888987036789446237224960 }, { target := 71, numerator := 886087968074832783658188800 }, { target := 72, numerator := 27291509416704849736672215040 }, { target := 73, numerator := 15417930644502090435652485120 }, { target := 74, numerator := 1063305561689799340389826560 }, { target := 921, numerator := 2392766428472254794037198848 }, { target := 922, numerator := 2342917127879082819161423872 }, { target := 923, numerator := 1844424121947363070403674112 }, { target := 924, numerator := 57974736589859006780526297088 }, { target := 925, numerator := 1844424121947363070403674112 }, { target := 926, numerator := 1844424121947363070403674112 }, { target := 927, numerator := 1894273422540535045279449088 }, { target := 928, numerator := 1894273422540535045279449088 }, { target := 929, numerator := 32053100281409579845123309568 }, { target := 930, numerator := 1744725520761019120652124160 }, { target := 931, numerator := 57974736589859006780526297088 }, { target := 932, numerator := 32053100281409579845123309568 }, { target := 933, numerator := 2392766428472254794037198848 }, { target := 934, numerator := 1844424121947363070403674112 }, { target := 935, numerator := 1744725520761019120652124160 }, { target := 936, numerator := 2342917127879082819161423872 }, { target := 966, numerator := 78882409729854553649577984 }, { target := 967, numerator := 77239026193815917115211776 }, { target := 968, numerator := 60805190833429551771549696 }, { target := 969, numerator := 1911255052412934289467899904 }, { target := 970, numerator := 60805190833429551771549696 }, { target := 971, numerator := 60805190833429551771549696 }, { target := 972, numerator := 62448574369468188305915904 }, { target := 973, numerator := 62448574369468188305915904 }, { target := 974, numerator := 1056695613672843291597471744 }, { target := 975, numerator := 57518423761352278702817280 }, { target := 976, numerator := 1911255052412934289467899904 }, { target := 977, numerator := 1056695613672843291597471744 }, { target := 978, numerator := 78882409729854553649577984 }, { target := 979, numerator := 60805190833429551771549696 }, { target := 980, numerator := 57518423761352278702817280 }, { target := 981, numerator := 77239026193815917115211776 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk17

namespace RouteChunk18

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot24.Left2.expected,
    Slot24.Left5.expected,
    Slot24.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 39266459780654229927808204800 }, { target := 153, numerator := 1047105594150779464741552128000 }, { target := 154, numerator := 1001294724406682863159109222400 }, { target := 155, numerator := 32722049817211858273173504000 }, { target := 156, numerator := 1027472364260452349777648025600 }, { target := 157, numerator := 32722049817211858273173504000 }, { target := 158, numerator := 1001294724406682863159109222400 }, { target := 159, numerator := 569363666819486333953218969600 }, { target := 160, numerator := 1027472364260452349777648025600 }, { target := 161, numerator := 16040348820397252925509651660800 }, { target := 162, numerator := 628263356490467678844931276800 }, { target := 163, numerator := 1047105594150779464741552128000 }, { target := 164, numerator := 1001294724406682863159109222400 }, { target := 165, numerator := 32722049817211858273173504000 }, { target := 166, numerator := 628263356490467678844931276800 }, { target := 167, numerator := 32722049817211858273173504000 }, { target := 168, numerator := 1007839134370125234813743923200 }, { target := 169, numerator := 569363666819486333953218969600 }, { target := 170, numerator := 39266459780654229927808204800 }, { target := 283, numerator := 39266450165288881506704424960 }, { target := 284, numerator := 1047105337741036840178784665600 }, { target := 285, numerator := 1001294479214866478420962836480 }, { target := 286, numerator := 32722041804407401255587020800 }, { target := 287, numerator := 1027472112658392399425432453120 }, { target := 288, numerator := 32722041804407401255587020800 }, { target := 289, numerator := 1001294479214866478420962836480 }, { target := 290, numerator := 569363527396688781847214161920 }, { target := 291, numerator := 1027472112658392399425432453120 }, { target := 292, numerator := 16040344892520508095488757596160 }, { target := 293, numerator := 628263202644622104107270799360 }, { target := 294, numerator := 1047105337741036840178784665600 }, { target := 295, numerator := 1001294479214866478420962836480 }, { target := 296, numerator := 32722041804407401255587020800 }, { target := 297, numerator := 628263202644622104107270799360 }, { target := 298, numerator := 32722041804407401255587020800 }, { target := 299, numerator := 1007838887575747958672080240640 }, { target := 300, numerator := 569363527396688781847214161920 }, { target := 301, numerator := 39266450165288881506704424960 }, { target := 660, numerator := 1063315177055147761493606400 }, { target := 661, numerator := 28355071388137273639829504000 }, { target := 662, numerator := 27114537014906267918086963200 }, { target := 663, numerator := 886095980879289801244672000 }, { target := 664, numerator := 27823413799609699759082700800 }, { target := 665, numerator := 886095980879289801244672000 }, { target := 666, numerator := 27114537014906267918086963200 }, { target := 667, numerator := 15418070067299642541657292800 }, { target := 668, numerator := 27823413799609699759082700800 }, { target := 669, numerator := 434364249827027860570138214400 }, { target := 670, numerator := 17013042832882364183897702400 }, { target := 671, numerator := 28355071388137273639829504000 }, { target := 672, numerator := 27114537014906267918086963200 }, { target := 673, numerator := 886095980879289801244672000 }, { target := 674, numerator := 17013042832882364183897702400 }, { target := 675, numerator := 886095980879289801244672000 }, { target := 676, numerator := 27291756211082125878335897600 }, { target := 677, numerator := 15418070067299642541657292800 }, { target := 678, numerator := 1063315177055147761493606400 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1
