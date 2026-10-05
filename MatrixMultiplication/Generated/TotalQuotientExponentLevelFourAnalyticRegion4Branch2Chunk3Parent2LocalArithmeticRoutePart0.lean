import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 28923265219248805254266880 }, { target := 27, numerator := 1010794647699402345456599040 }, { target := 29, numerator := 12195592245646038541617070080 }, { target := 37, numerator := 1010818471763949133517291520 }, { target := 44, numerator := 28924116078696904827863040 }, { target := 80, numerator := 54114495997017774777958400 }, { target := 82, numerator := 1930389656074254933609676800 }, { target := 85, numerator := 1930389656074254933609676800 }, { target := 92, numerator := 54113549711923070757765120 }, { target := 131, numerator := 316640606287138262425272320 }, { target := 134, numerator := 1122440543962261093141708800 }, { target := 136, numerator := 316836379076020824241602560 }, { target := 157, numerator := 102654340853646778102185984 }, { target := 158, numerator := 3587508447314620931817603072 }, { target := 160, numerator := 43284548746711492943878815744 }, { target := 168, numerator := 3587593003592204614040027136 }, { target := 175, numerator := 102657360720703338181558272 }, { target := 176, numerator := 2646427553303250542474035200 }, { target := 178, numerator := 94404212407855159622133350400 }, { target := 181, numerator := 94404212407855159622133350400 }, { target := 188, numerator := 2646381275962923046781583360 }, { target := 227, numerator := 10170520614384137486959902720 }, { target := 230, numerator := 36036564153218174680207196160 }, { target := 232, numerator := 10177050176397092103546470400 }, { target := 263, numerator := 409298821063720945697423360 }, { target := 265, numerator := 409299796909317703870709760 }, { target := 267, numerator := 28949797779292266392715264 }, { target := 268, numerator := 1011721893274146277595021312 }, { target := 270, numerator := 12206779788998088079100084224 }, { target := 278, numerator := 1011745739193536157377888256 }, { target := 285, numerator := 28950649419270476384960512 }, { target := 286, numerator := 2646428519093153757659136000 }, { target := 288, numerator := 94404246859822322178588672000 }, { target := 291, numerator := 94404246859822322178588672000 }, { target := 298, numerator := 2646382241735937763364044800 }, { target := 302, numerator := 121943073787895455645077340160 }, { target := 305, numerator := 431959969157026349942004776960 }, { target := 307, numerator := 122023037446508078865024286720 }, { target := 338, numerator := 19397678055602695458518990848 }, { target := 340, numerator := 19397724303326225904716218368 }, { target := 573, numerator := 54118037226662897123328000 }, { target := 575, numerator := 1930515979953850973945856000 }, { target := 578, numerator := 1930515979953850973945856000 }, { target := 585, numerator := 54117090879643698226790400 }, { target := 589, numerator := 5137552884103367966840586240 }, { target := 592, numerator := 18425941615651644588404244480 }, { target := 594, numerator := 5137561437684587115357143040 }, { target := 599, numerator := 19392504709287828501917859840 }, { target := 601, numerator := 19392550944677125468654141440 }, { target := 763, numerator := 165774550030399978277437440 }, { target := 766, numerator := 594553914894477752669306880 }, { target := 768, numerator := 165774826030688391911178240 }, { target := 773, numerator := 414552447513095194185564160 }, { target := 775, numerator := 414553435884328415983042560 }]

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
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 150887189109477869071892480 }, { target := 27, numerator := 5033005769415700772982620160 }, { target := 29, numerator := 61639582462533716445935697920 }, { target := 37, numerator := 5033010062203236961149255680 }, { target := 44, numerator := 164538253474556238972846080 }, { target := 80, numerator := 285745956839322894624358400 }, { target := 82, numerator := 10710514307628430095758131200 }, { target := 85, numerator := 10710524173762650018152448000 }, { target := 92, numerator := 285748509141821716168704000 }, { target := 131, numerator := 28923265219248805254266880 }, { target := 134, numerator := 102654340853646778102185984 }, { target := 136, numerator := 28949797779292266392715264 }, { target := 157, numerator := 527962422489191539665797120 }, { target := 158, numerator := 17610758965725064850351063040 }, { target := 160, numerator := 215680227527662243943001620480 }, { target := 168, numerator := 17610773986420461282441297920 }, { target := 175, numerator := 575728233849845586612715520 }, { target := 176, numerator := 9994476410399434486893772800 }, { target := 178, numerator := 375149733524932343187206307840 }, { target := 181, numerator := 375150077836140786250080583680 }, { target := 188, numerator := 9994568305474443804294512640 }, { target := 227, numerator := 1010794647699402345456599040 }, { target := 230, numerator := 3587508447314620931817603072 }, { target := 232, numerator := 1011721893274146277595021312 }, { target := 267, numerator := 151082685933256389343313920 }, { target := 268, numerator := 5039526777910768110812528640 }, { target := 270, numerator := 61719445721048766807204167680 }, { target := 278, numerator := 5039531076260249838781726720 }, { target := 285, numerator := 164751437285151331393208320 }, { target := 286, numerator := 9994485310743751194102988800 }, { target := 288, numerator := 375150043384173623693625262080 }, { target := 291, numerator := 375150387695724058853202984960 }, { target := 298, numerator := 9994577205780761389647790080 }, { target := 302, numerator := 12195592245646038541617070080 }, { target := 305, numerator := 43284548746711492943878815744 }, { target := 307, numerator := 12206779788998088079100084224 }, { target := 573, numerator := 231630471915158819045376000 }, { target := 575, numerator := 8064052325520592830348656640 }, { target := 578, numerator := 8064061225826910415701934080 }, { target := 585, numerator := 231629482992234642895011840 }, { target := 589, numerator := 6043828533967186094666547200 }, { target := 592, numerator := 21198366990012665896481325056 }, { target := 594, numerator := 6051276815453785996159614976 }, { target := 763, numerator := 193462369553253143800709120 }, { target := 766, numerator := 678385594570548924794273792 }, { target := 768, numerator := 193702086704421807778168832 }]

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
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 409298821063720945697423360 }, { target := 11, numerator := 19397678055602695458518990848 }, { target := 16, numerator := 19392504709287828501917859840 }, { target := 24, numerator := 414552447513095194185564160 }, { target := 26, numerator := 165753417177660393353379840 }, { target := 27, numerator := 5137514844968436713977282560 }, { target := 29, numerator := 60303491325361739199141642240 }, { target := 37, numerator := 5137552884103367966840586240 }, { target := 44, numerator := 165774550030399978277437440 }, { target := 141, numerator := 409299796909317703870709760 }, { target := 142, numerator := 19397724303326225904716218368 }, { target := 147, numerator := 19392550944677125468654141440 }, { target := 155, numerator := 414553435884328415983042560 }, { target := 157, numerator := 594478121473069553475911680 }, { target := 158, numerator := 18425805187493109829856133120 }, { target := 160, numerator := 216279741629364105999003156480 }, { target := 168, numerator := 18425941615651644588404244480 }, { target := 175, numerator := 594553914894477752669306880 }, { target := 267, numerator := 165753693142764434898288640 }, { target := 268, numerator := 5137523398486323992733941760 }, { target := 270, numerator := 60303591725459312057820119040 }, { target := 278, numerator := 5137561437684587115357143040 }, { target := 285, numerator := 165774826030688391911178240 }, { target := 573, numerator := 54113549711923070757765120 }, { target := 575, numerator := 2646381275962923046781583360 }, { target := 578, numerator := 2646382241735937763364044800 }, { target := 585, numerator := 54117090879643698226790400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent2
