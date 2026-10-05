import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 17; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent3

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
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 97280749547114691402137600 }, { target := 1, numerator := 31336207270378104744522547200 }, { target := 3, numerator := 333273742084141591702966108160 }, { target := 11, numerator := 31336301717707762137426821120 }, { target := 18, numerator := 97280749547114691402137600 }, { target := 19, numerator := 3063631630976471848458387456 }, { target := 21, numerator := 119898587358934662054898827264 }, { target := 24, numerator := 119898631333666690769256185856 }, { target := 31, numerator := 3063675605708500562815746048 }, { target := 35, numerator := 3823754429947360656740057088 }, { target := 38, numerator := 13705845641255320386269085696 }, { target := 40, numerator := 3824865606470128699000750080 }, { target := 45, numerator := 3351826017530495785123184640 }, { target := 47, numerator := 131177391077771051532455772160 }, { target := 50, numerator := 131177439189185438776180080640 }, { target := 57, numerator := 3351874128944883028847493120 }, { target := 61, numerator := 79820873725151153709448691712 }, { target := 64, numerator := 286109527761204813063367163904 }, { target := 66, numerator := 79844069535063936591640657920 }, { target := 71, numerator := 15290488298179133451408506880 }, { target := 73, numerator := 15290499234792526151958921216 }, { target := 75, numerator := 4142400632442974044801728512 }, { target := 78, numerator := 14847999444693263751791509504 }, { target := 80, numerator := 4143604407009306090584145920 }, { target := 85, numerator := 17263454530202247445138636800 }, { target := 87, numerator := 17263466877991561784469749760 }, { target := 90, numerator := 3063631630976471848458387456 }, { target := 92, numerator := 119898587358934662054898827264 }, { target := 95, numerator := 119898631333666690769256185856 }, { target := 102, numerator := 3063675605708500562815746048 }, { target := 106, numerator := 85875151572567808082620448768 }, { target := 109, numerator := 307810450026525737008293216256 }, { target := 111, numerator := 85900106745308307031725178880 }, { target := 116, numerator := 14797246740173354952975974400 }, { target := 118, numerator := 14797257323992767243831214080 }, { target := 120, numerator := 128573742706980002082884419584 }, { target := 123, numerator := 460859059687210147988298006528 }, { target := 125, numerator := 128611106017558077503900221440 }, { target := 130, numerator := 194830415412282506880850329600 }, { target := 132, numerator := 194830554765904768710444318720 }, { target := 135, numerator := 17263454530202247445138636800 }, { target := 137, numerator := 17263466877991561784469749760 }, { target := 140, numerator := 3983077531195167350770892800 }, { target := 143, numerator := 14276922542974292069030297600 }, { target := 145, numerator := 3984235006739717394792448000 }, { target := 150, numerator := 14797246740173354952975974400 }, { target := 152, numerator := 14797257323992767243831214080 }, { target := 161, numerator := 3351826017530495785123184640 }, { target := 163, numerator := 131177391077771051532455772160 }, { target := 166, numerator := 131177439189185438776180080640 }, { target := 173, numerator := 3351874128944883028847493120 }, { target := 177, numerator := 128573742706980002082884419584 }, { target := 180, numerator := 460859059687210147988298006528 }, { target := 182, numerator := 128611106017558077503900221440 }, { target := 191, numerator := 133990728149405429679932833792 }, { target := 194, numerator := 480275674345655185202179211264 }, { target := 196, numerator := 134029665626724093160817950720 }, { target := 211, numerator := 79820873725151153709448691712 }, { target := 214, numerator := 286109527761204813063367163904 }, { target := 216, numerator := 79844069535063936591640657920 }, { target := 238, numerator := 3983077531195167350770892800 }, { target := 241, numerator := 14276922542974292069030297600 }, { target := 243, numerator := 3984235006739717394792448000 }]

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
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 157122577618038835550093312 }, { target := 1, numerator := 25749364379154342278007357440 }, { target := 3, numerator := 265099676143512588147060899840 }, { target := 11, numerator := 25749364379154342278007357440 }, { target := 18, numerator := 157122577618038835550093312 }, { target := 19, numerator := 18366789686788085652886913024 }, { target := 21, numerator := 734300843923686296009039675392 }, { target := 24, numerator := 734300664473759946962521554944 }, { target := 31, numerator := 18366789686788085652886913024 }, { target := 35, numerator := 291126729617944962459362131968 }, { target := 38, numerator := 1060504998548175365534172315648 }, { target := 40, numerator := 291126925450036963439416442880 }, { target := 71, numerator := 18366789686788085652886913024 }, { target := 73, numerator := 18366789686788085652886913024 }, { target := 89, numerator := 696341272098026404630757376 }, { target := 90, numerator := 18366789686788085652886913024 }, { target := 92, numerator := 734300843923686296009039675392 }, { target := 95, numerator := 734300664473759946962521554944 }, { target := 102, numerator := 18366789686788085652886913024 }, { target := 106, numerator := 1060504998548175365534172315648 }, { target := 109, numerator := 3863165891437063933765644976128 }, { target := 111, numerator := 1060505711917616624781943111680 }, { target := 134, numerator := 10096948445421382867145981952 }, { target := 139, numerator := 17872759317182677718856105984 }, { target := 140, numerator := 291126925450036963439416442880 }, { target := 143, numerator := 1060505711917616624781943111680 }, { target := 145, numerator := 291127121282260694708571340800 }, { target := 154, numerator := 580284393415022003858964480 }, { target := 155, numerator := 17263454530202247445138636800 }, { target := 157, numerator := 17263466877991561784469749760 }, { target := 159, numerator := 11141460353568422474092118016 }, { target := 160, numerator := 580284393415022003858964480 }, { target := 187, numerator := 17263454530202247445138636800 }, { target := 189, numerator := 17263466877991561784469749760 }, { target := 201, numerator := 715693500666384601225604628480 }, { target := 203, numerator := 715694012570450175693303054336 }, { target := 205, numerator := 17756702438499673318084313088 }, { target := 206, numerator := 17756696088208025943571169280 }, { target := 208, numerator := 17756708788791320692597456896 }, { target := 210, numerator := 18569100589280704123486863360 }, { target := 221, numerator := 194830415412282506880850329600 }, { target := 223, numerator := 194830554765904768710444318720 }, { target := 225, numerator := 11141460353568422474092118016 }, { target := 226, numerator := 715693500666384601225604628480 }, { target := 228, numerator := 715694012570450175693303054336 }, { target := 230, numerator := 284455409652043786291664388096 }, { target := 231, numerator := 18220929953231690921171484672 }, { target := 232, numerator := 15290488298179133451408506880 }, { target := 234, numerator := 15290499234792526151958921216 }, { target := 236, numerator := 10096948445421382867145981952 }, { target := 237, numerator := 17756702438499673318084313088 }, { target := 248, numerator := 17263454530202247445138636800 }, { target := 250, numerator := 17263466877991561784469749760 }, { target := 252, numerator := 580284393415022003858964480 }, { target := 253, numerator := 17756696088208025943571169280 }, { target := 255, numerator := 17756708788791320692597456896 }, { target := 257, numerator := 18220929953231690921171484672 }, { target := 258, numerator := 580284393415022003858964480 }, { target := 259, numerator := 17263454530202247445138636800 }, { target := 261, numerator := 17263466877991561784469749760 }, { target := 263, numerator := 17756702438499673318084313088 }, { target := 264, numerator := 18569100589280704123486863360 }, { target := 265, numerator := 696341272098026404630757376 }]

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
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 696341272098026404630757376 }, { target := 1, numerator := 10096948445421382867145981952 }, { target := 2, numerator := 17872759317182677718856105984 }, { target := 3, numerator := 580284393415022003858964480 }, { target := 4, numerator := 11141460353568422474092118016 }, { target := 5, numerator := 580284393415022003858964480 }, { target := 6, numerator := 17756702438499673318084313088 }, { target := 7, numerator := 18569100589280704123486863360 }, { target := 8, numerator := 11141460353568422474092118016 }, { target := 9, numerator := 284455409652043786291664388096 }, { target := 10, numerator := 18220929953231690921171484672 }, { target := 11, numerator := 10096948445421382867145981952 }, { target := 12, numerator := 17756702438499673318084313088 }, { target := 13, numerator := 580284393415022003858964480 }, { target := 14, numerator := 18220929953231690921171484672 }, { target := 15, numerator := 580284393415022003858964480 }, { target := 16, numerator := 17756702438499673318084313088 }, { target := 17, numerator := 18569100589280704123486863360 }, { target := 18, numerator := 696341272098026404630757376 }, { target := 19, numerator := 14990674802136405344518144000 }, { target := 20, numerator := 16924955421766909259939840000 }, { target := 21, numerator := 14507104647228779365662720000 }, { target := 22, numerator := 191010211188512261647892480000 }, { target := 23, numerator := 16924955421766909259939840000 }, { target := 24, numerator := 14507104647228779365662720000 }, { target := 25, numerator := 16924955421766909259939840000 }, { target := 26, numerator := 16924955421766909259939840000 }, { target := 27, numerator := 701660294770965295319220224000 }, { target := 28, numerator := 17408525576674535238795264000 }, { target := 29, numerator := 191010211188512261647892480000 }, { target := 30, numerator := 701660294770965295319220224000 }, { target := 31, numerator := 14990674802136405344518144000 }, { target := 32, numerator := 16924955421766909259939840000 }, { target := 33, numerator := 17408525576674535238795264000 }, { target := 34, numerator := 16924955421766909259939840000 }, { target := 89, numerator := 157122577618038835550093312 }, { target := 90, numerator := 14990685524306398188195020800 }, { target := 91, numerator := 16924967527442707631833088000 }, { target := 92, numerator := 14507115023522320827285504000 }, { target := 93, numerator := 191010347809710557559259136000 }, { target := 94, numerator := 16924967527442707631833088000 }, { target := 95, numerator := 14507115023522320827285504000 }, { target := 96, numerator := 16924967527442707631833088000 }, { target := 97, numerator := 16924967527442707631833088000 }, { target := 98, numerator := 701660796637696250679708876800 }, { target := 99, numerator := 17408538028226784992742604800 }, { target := 100, numerator := 191010347809710557559259136000 }, { target := 101, numerator := 701660796637696250679708876800 }, { target := 102, numerator := 14990685524306398188195020800 }, { target := 103, numerator := 16924967527442707631833088000 }, { target := 104, numerator := 17408538028226784992742604800 }, { target := 105, numerator := 16924967527442707631833088000 }, { target := 116, numerator := 734300843923686296009039675392 }, { target := 118, numerator := 734300843923686296009039675392 }, { target := 134, numerator := 25749364379154342278007357440 }, { target := 150, numerator := 734300664473759946962521554944 }, { target := 152, numerator := 734300664473759946962521554944 }, { target := 154, numerator := 265099676143512588147060899840 }, { target := 232, numerator := 18366789686788085652886913024 }, { target := 234, numerator := 18366789686788085652886913024 }, { target := 236, numerator := 25749364379154342278007357440 }, { target := 265, numerator := 157122577618038835550093312 }]

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
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 3740629333644157164202229760 }, { target := 36, numerator := 78085637339821780802721546240 }, { target := 37, numerator := 4052348444781170261219082240 }, { target := 38, numerator := 84008300451425029646041743360 }, { target := 39, numerator := 125778661343784784646299975680 }, { target := 40, numerator := 3896488889212663712710656000 }, { target := 41, numerator := 125778661343784784646299975680 }, { target := 42, numerator := 131077886233114007295586467840 }, { target := 43, numerator := 78085637339821780802721546240 }, { target := 44, numerator := 3896488889212663712710656000 }, { target := 71, numerator := 3063631630976471848458387456 }, { target := 72, numerator := 3351826017530495785123184640 }, { target := 73, numerator := 3063631630976471848458387456 }, { target := 74, numerator := 3351826017530495785123184640 }, { target := 89, numerator := 97280749547114691402137600 }, { target := 106, numerator := 13407892475141074290915409920 }, { target := 107, numerator := 279889755418569925822859182080 }, { target := 108, numerator := 14525216848069497148491694080 }, { target := 109, numerator := 301118918504209960116808581120 }, { target := 110, numerator := 450840384476618623032030658560 }, { target := 111, numerator := 13966554661605285719703552000 }, { target := 112, numerator := 450840384476618623032030658560 }, { target := 113, numerator := 469834898816401811610827489280 }, { target := 114, numerator := 279889755418569925822859182080 }, { target := 115, numerator := 13966554661605285719703552000 }, { target := 116, numerator := 119898587358934662054898827264 }, { target := 117, numerator := 131177391077771051532455772160 }, { target := 118, numerator := 119898587358934662054898827264 }, { target := 119, numerator := 131177391077771051532455772160 }, { target := 134, numerator := 31336207270378104744522547200 }, { target := 140, numerator := 3741716354155560683805081600 }, { target := 141, numerator := 78108328892997329274431078400 }, { target := 142, numerator := 4053526050335190740788838400 }, { target := 143, numerator := 84032713120410300357122457600 }, { target := 144, numerator := 125815212408480727992945868800 }, { target := 145, numerator := 3897621202245375712296960000 }, { target := 146, numerator := 125815212408480727992945868800 }, { target := 147, numerator := 131115977243534438961669734400 }, { target := 148, numerator := 78108328892997329274431078400 }, { target := 149, numerator := 3897621202245375712296960000 }, { target := 150, numerator := 119898631333666690769256185856 }, { target := 151, numerator := 131177439189185438776180080640 }, { target := 152, numerator := 119898631333666690769256185856 }, { target := 153, numerator := 131177439189185438776180080640 }, { target := 154, numerator := 333273742084141591702966108160 }, { target := 232, numerator := 3063675605708500562815746048 }, { target := 233, numerator := 3351874128944883028847493120 }, { target := 234, numerator := 3063675605708500562815746048 }, { target := 235, numerator := 3351874128944883028847493120 }, { target := 236, numerator := 31336301717707762137426821120 }, { target := 265, numerator := 97280749547114691402137600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3.Parent3
