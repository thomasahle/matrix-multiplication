import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 86; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent0

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
    Slot0.Left3.expected,
    Slot0.Left11.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left3.expected,
    Slot1.Left11.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left3.expected,
    Slot3.Left11.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 8544863896335591080460288000 }, { target := 36, numerator := 152098577354773521232193126400 }, { target := 37, numerator := 8544863896335591080460288000 }, { target := 38, numerator := 135293678358646858773954560000 }, { target := 39, numerator := 230996153997605478875109785600 }, { target := 40, numerator := 8544863896335591080460288000 }, { target := 41, numerator := 230996153997605478875109785600 }, { target := 42, numerator := 230996153997605478875109785600 }, { target := 43, numerator := 152098577354773521232193126400 }, { target := 44, numerator := 8544863896335591080460288000 }, { target := 71, numerator := 58982046063788880796669968384 }, { target := 72, numerator := 3371977083959291472777314304 }, { target := 73, numerator := 58982046063788880796669968384 }, { target := 74, numerator := 3371977083959291472777314304 }, { target := 89, numerator := 1806942699172826696342568960 }, { target := 106, numerator := 29333023680530578147796582400 }, { target := 107, numerator := 522127821513444291030779166720 }, { target := 108, numerator := 29333023680530578147796582400 }, { target := 109, numerator := 464439541608400820673445888000 }, { target := 110, numerator := 792969406830343295928767610880 }, { target := 111, numerator := 29333023680530578147796582400 }, { target := 112, numerator := 792969406830343295928767610880 }, { target := 113, numerator := 792969406830343295928767610880 }, { target := 114, numerator := 522127821513444291030779166720 }, { target := 115, numerator := 29333023680530578147796582400 }, { target := 116, numerator := 2212096327257696569772954615808 }, { target := 117, numerator := 122201565651051470162302599168 }, { target := 118, numerator := 2212096327257696569772954615808 }, { target := 119, numerator := 122201565651051470162302599168 }, { target := 134, numerator := 274126701626742609846365847552 }, { target := 150, numerator := 2211937313326185281460222558208 }, { target := 151, numerator := 122201610559649917608206008320 }, { target := 152, numerator := 2211937313326185281460222558208 }, { target := 153, numerator := 122201610559649917608206008320 }, { target := 154, numerator := 2775715664451166343323849850880 }, { target := 232, numerator := 59141059995300169109402025984 }, { target := 233, numerator := 3371932175360844026873905152 }, { target := 234, numerator := 59141059995300169109402025984 }, { target := 235, numerator := 3371932175360844026873905152 }, { target := 236, numerator := 274126715793842058455301488640 }, { target := 265, numerator := 1806801028178340606986158080 }]

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
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot6.Left16.expected,
    Slot6.Left17.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 69634143811872306801672192000 }, { target := 20, numerator := 82690545776598364326985728000 }, { target := 21, numerator := 63105942829509278039015424000 }, { target := 22, numerator := 650644031242181866678124544000 }, { target := 23, numerator := 78338411788356345151881216000 }, { target := 24, numerator := 63105942829509278039015424000 }, { target := 25, numerator := 78338411788356345151881216000 }, { target := 26, numerator := 78338411788356345151881216000 }, { target := 27, numerator := 3355495304934596784005578752000 }, { target := 28, numerator := 78338411788356345151881216000 }, { target := 29, numerator := 650644031242181866678124544000 }, { target := 30, numerator := 3355495304934596784005578752000 }, { target := 31, numerator := 69634143811872306801672192000 }, { target := 32, numerator := 78338411788356345151881216000 }, { target := 33, numerator := 78338411788356345151881216000 }, { target := 34, numerator := 82690545776598364326985728000 }, { target := 35, numerator := 2036066182009446788036906975232 }, { target := 38, numerator := 7283892334327174399739176157184 }, { target := 40, numerator := 2036065505137668927258925989888 }, { target := 71, numerator := 281997814576494697008133570560 }, { target := 73, numerator := 281997814576494697008133570560 }, { target := 89, numerator := 5415987671873538702683668480 }, { target := 106, numerator := 7405611598024658218273252311040 }, { target := 109, numerator := 26493086534456250546084359700480 }, { target := 111, numerator := 7405609136096095781155881615360 }, { target := 116, numerator := 10413804124849190878120299724800 }, { target := 118, numerator := 10413804124849190878120299724800 }, { target := 134, numerator := 90988592887475450205085630464 }, { target := 139, numerator := 197141951256196808777685532672 }, { target := 140, numerator := 2044611045905782379117367263232 }, { target := 141, numerator := 152098577354773521232193126400 }, { target := 142, numerator := 8544863896335591080460288000 }, { target := 143, numerator := 7419186012685821258513130717184 }, { target := 144, numerator := 230996153997605478875109785600 }, { target := 145, numerator := 2044610369034004518339386277888 }, { target := 146, numerator := 230996153997605478875109785600 }, { target := 147, numerator := 230996153997605478875109785600 }, { target := 148, numerator := 152098577354773521232193126400 }, { target := 149, numerator := 8544863896335591080460288000 }, { target := 150, numerator := 10413801574771290128511884328960 }, { target := 152, numerator := 10413801574771290128511884328960 }, { target := 154, numerator := 6499185206248246443220402176 }, { target := 159, numerator := 103986963299971943091526434816 }, { target := 160, numerator := 7582382740622954183757135872 }, { target := 205, numerator := 197141951256196808777685532672 }, { target := 210, numerator := 197141951256196808777685532672 }, { target := 225, numerator := 103986963299971943091526434816 }, { target := 230, numerator := 2432861662205593585245503881216 }, { target := 231, numerator := 194975556187447393296612065280 }, { target := 232, numerator := 282000364654395446616548966400 }, { target := 234, numerator := 282000364654395446616548966400 }, { target := 236, numerator := 90988592887475450205085630464 }, { target := 237, numerator := 197141951256196808777685532672 }, { target := 252, numerator := 7582382740622954183757135872 }, { target := 257, numerator := 194975556187447393296612065280 }, { target := 258, numerator := 7582382740622954183757135872 }, { target := 263, numerator := 197141951256196808777685532672 }, { target := 264, numerator := 197141951256196808777685532672 }, { target := 265, numerator := 6499185206248246443220402176 }]

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
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected,
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 282520032751636353854444929024 }, { target := 21, numerator := 10433088947302615305672374353920 }, { target := 24, numerator := 10433086392502348073194313744384 }, { target := 31, numerator := 282522587551903586332505538560 }, { target := 35, numerator := 2048665601452574552814363082752 }, { target := 38, numerator := 7451438402467880113188309565440 }, { target := 40, numerator := 2048665601452574552814363082752 }, { target := 71, numerator := 71491054313522234983050117120 }, { target := 73, numerator := 71491020223939186767798730752 }, { target := 85, numerator := 84895626997307654042372014080 }, { target := 87, numerator := 84895586515927784286760992768 }, { target := 90, numerator := 69634110607732974124479283200 }, { target := 91, numerator := 82690506346682906772819148800 }, { target := 92, numerator := 63105912738258007800309350400 }, { target := 93, numerator := 650643720991004976975603302400 }, { target := 94, numerator := 78338374433699595890039193600 }, { target := 95, numerator := 63105912738258007800309350400 }, { target := 96, numerator := 78338374433699595890039193600 }, { target := 97, numerator := 78338374433699595890039193600 }, { target := 98, numerator := 3355493704910132690623345459200 }, { target := 99, numerator := 78338374433699595890039193600 }, { target := 100, numerator := 650643720991004976975603302400 }, { target := 101, numerator := 3355493704910132690623345459200 }, { target := 102, numerator := 69634110607732974124479283200 }, { target := 103, numerator := 78338374433699595890039193600 }, { target := 104, numerator := 78338374433699595890039193600 }, { target := 105, numerator := 82690506346682906772819148800 }, { target := 106, numerator := 7328965925504941568054393831424 }, { target := 109, numerator := 26657028901624915462829931233280 }, { target := 111, numerator := 7328965925504941568054393831424 }, { target := 116, numerator := 64788767971629525453389168640 }, { target := 118, numerator := 64788737077944888008317599744 }, { target := 130, numerator := 667994538741973383122874531840 }, { target := 132, numerator := 667994220217431776361619390464 }, { target := 135, numerator := 80427436102712514355931381760 }, { target := 137, numerator := 80427397751931585113773572096 }, { target := 140, numerator := 2048664920392233710224637165568 }, { target := 143, numerator := 7451435925304611225346202664960 }, { target := 145, numerator := 2048664920392233710224637165568 }, { target := 150, numerator := 64788767971629525453389168640 }, { target := 152, numerator := 64788737077944888008317599744 }, { target := 155, numerator := 80427436102712514355931381760 }, { target := 157, numerator := 80427397751931585113773572096 }, { target := 187, numerator := 80427436102712514355931381760 }, { target := 189, numerator := 80427397751931585113773572096 }, { target := 201, numerator := 3444975179732852698245727518720 }, { target := 203, numerator := 3444973537041069562373301338112 }, { target := 206, numerator := 80427436102712514355931381760 }, { target := 208, numerator := 80427397751931585113773572096 }, { target := 221, numerator := 667994538741973383122874531840 }, { target := 223, numerator := 667994220217431776361619390464 }, { target := 226, numerator := 3444975179732852698245727518720 }, { target := 228, numerator := 3444973537041069562373301338112 }, { target := 232, numerator := 71491054313522234983050117120 }, { target := 234, numerator := 71491020223939186767798730752 }, { target := 248, numerator := 80427436102712514355931381760 }, { target := 250, numerator := 80427397751931585113773572096 }, { target := 253, numerator := 80427436102712514355931381760 }, { target := 255, numerator := 80427397751931585113773572096 }, { target := 259, numerator := 84895626997307654042372014080 }, { target := 261, numerator := 84895586515927784286760992768 }]

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
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 5415987671873538702683668480 }, { target := 1, numerator := 90988592887475450205085630464 }, { target := 2, numerator := 197141951256196808777685532672 }, { target := 3, numerator := 6499185206248246443220402176 }, { target := 4, numerator := 103986963299971943091526434816 }, { target := 5, numerator := 7582382740622954183757135872 }, { target := 6, numerator := 197141951256196808777685532672 }, { target := 7, numerator := 197141951256196808777685532672 }, { target := 8, numerator := 103986963299971943091526434816 }, { target := 9, numerator := 2432861662205593585245503881216 }, { target := 10, numerator := 194975556187447393296612065280 }, { target := 11, numerator := 90988592887475450205085630464 }, { target := 12, numerator := 197141951256196808777685532672 }, { target := 13, numerator := 7582382740622954183757135872 }, { target := 14, numerator := 194975556187447393296612065280 }, { target := 15, numerator := 7582382740622954183757135872 }, { target := 16, numerator := 197141951256196808777685532672 }, { target := 17, numerator := 197141951256196808777685532672 }, { target := 18, numerator := 6499185206248246443220402176 }, { target := 19, numerator := 52377070034656507087181316096 }, { target := 21, numerator := 1967941074079084101548189417472 }, { target := 24, numerator := 1967792234532277016070344146944 }, { target := 31, numerator := 52525909581463592565026586624 }, { target := 35, numerator := 8758485493743980857471795200 }, { target := 38, numerator := 30066349272543842601491496960 }, { target := 40, numerator := 8758485493743980857471795200 }, { target := 61, numerator := 155901041788642859262997954560 }, { target := 64, numerator := 535181017051280398306548645888 }, { target := 66, numerator := 155901041788642859262997954560 }, { target := 75, numerator := 8758485493743980857471795200 }, { target := 78, numerator := 30066349272543842601491496960 }, { target := 80, numerator := 8758485493743980857471795200 }, { target := 90, numerator := 334897102786292860941626245120 }, { target := 92, numerator := 12401030021381699407220563771392 }, { target := 95, numerator := 12400878627034625089264657891328 }, { target := 102, numerator := 335048497133367178897532125184 }, { target := 106, numerator := 138676020317613030243303424000 }, { target := 109, numerator := 476050530148610841190282035200 }, { target := 111, numerator := 138676020317613030243303424000 }, { target := 120, numerator := 236771057847545615846987530240 }, { target := 123, numerator := 812793642001101878326986801152 }, { target := 125, numerator := 236771057847545615846987530240 }, { target := 140, numerator := 8758485493743980857471795200 }, { target := 143, numerator := 30066349272543842601491496960 }, { target := 145, numerator := 8758485493743980857471795200 }, { target := 177, numerator := 236771057847545615846987530240 }, { target := 180, numerator := 812793642001101878326986801152 }, { target := 182, numerator := 236771057847545615846987530240 }, { target := 191, numerator := 236771057847545615846987530240 }, { target := 194, numerator := 812793642001101878326986801152 }, { target := 196, numerator := 236771057847545615846987530240 }, { target := 211, numerator := 155901041788642859262997954560 }, { target := 214, numerator := 535181017051280398306548645888 }, { target := 216, numerator := 155901041788642859262997954560 }, { target := 238, numerator := 8758485493743980857471795200 }, { target := 241, numerator := 30066349272543842601491496960 }, { target := 243, numerator := 8758485493743980857471795200 }]

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
    Slot16.Left0.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1806942699172826696342568960 }, { target := 1, numerator := 274126701626742609846365847552 }, { target := 3, numerator := 2775715664451166343323849850880 }, { target := 11, numerator := 274126715793842058455301488640 }, { target := 18, numerator := 1806801028178340606986158080 }, { target := 19, numerator := 3010471222832417340760522752 }, { target := 21, numerator := 109100473584949833804791414784 }, { target := 24, numerator := 109100513678948078012501852160 }, { target := 31, numerator := 3010431128834173133050085376 }, { target := 45, numerator := 3371977083959291472777314304 }, { target := 47, numerator := 122201565651051470162302599168 }, { target := 50, numerator := 122201610559649917608206008320 }, { target := 57, numerator := 3371932175360844026873905152 }, { target := 90, numerator := 3010471222832417340760522752 }, { target := 92, numerator := 109100473584949833804791414784 }, { target := 95, numerator := 109100513678948078012501852160 }, { target := 102, numerator := 3010431128834173133050085376 }, { target := 161, numerator := 3371977083959291472777314304 }, { target := 163, numerator := 122201565651051470162302599168 }, { target := 166, numerator := 122201610559649917608206008320 }, { target := 173, numerator := 3371932175360844026873905152 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent0
