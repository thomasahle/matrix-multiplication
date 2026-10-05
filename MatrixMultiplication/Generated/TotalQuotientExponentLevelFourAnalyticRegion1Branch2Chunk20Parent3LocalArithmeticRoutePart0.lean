import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk20Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 85; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20.Parent3

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
    Slot0.Left6.expected,
    Slot0.Left14.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left6.expected,
    Slot1.Left14.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
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
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 601758617126108767086182400 }, { target := 87, numerator := 10711303384844736054134046720 }, { target := 88, numerator := 601758617126108767086182400 }, { target := 89, numerator := 9527844771163388812197888000 }, { target := 90, numerator := 16267541282975807003563130880 }, { target := 91, numerator := 601758617126108767086182400 }, { target := 92, numerator := 16267541282975807003563130880 }, { target := 93, numerator := 16267541282975807003563130880 }, { target := 94, numerator := 10711303384844736054134046720 }, { target := 95, numerator := 601758617126108767086182400 }, { target := 122, numerator := 847038073991941107551830016 }, { target := 123, numerator := 91154475159771307053154304 }, { target := 124, numerator := 847038073991941107551830016 }, { target := 125, numerator := 91154475159771307053154304 }, { target := 197, numerator := 134254539691900585580041338880 }, { target := 198, numerator := 13463038951985824737488011264 }, { target := 199, numerator := 134254539691900585580041338880 }, { target := 200, numerator := 13463038951985824737488011264 }, { target := 215, numerator := 3544376886084295084784746496 }, { target := 242, numerator := 1344999198089594793387882446848 }, { target := 243, numerator := 140323003459056490091024220160 }, { target := 244, numerator := 1344999198089594793387882446848 }, { target := 245, numerator := 140323003459056490091024220160 }, { target := 260, numerator := 80326060775500218539630919680 }, { target := 265, numerator := 2321137573660088015435857920 }, { target := 355, numerator := 2727336649050603418137133056 }, { target := 400, numerator := 32205783834533721214172528640 }, { target := 405, numerator := 72419492298194746081598767104 }, { target := 416, numerator := 134254539691900585580041338880 }, { target := 417, numerator := 13463038951985824737488011264 }, { target := 418, numerator := 134254539691900585580041338880 }, { target := 419, numerator := 13463038951985824737488011264 }, { target := 420, numerator := 80326065497866701409276133376 }, { target := 425, numerator := 32205783834533721214172528640 }, { target := 426, numerator := 2321137573660088015435857920 }, { target := 471, numerator := 2263109134318585815049961472 }, { target := 476, numerator := 2263109134318585815049961472 }, { target := 491, numerator := 2263109134318585815049961472 }, { target := 496, numerator := 72419492298194746081598767104 }, { target := 497, numerator := 2263109134318585815049961472 }, { target := 498, numerator := 846950710212008019115376640 }, { target := 499, numerator := 91154475159771307053154304 }, { target := 500, numerator := 846950710212008019115376640 }, { target := 501, numerator := 91154475159771307053154304 }, { target := 502, numerator := 3544372163717812215139532800 }, { target := 503, numerator := 2727336649050603418137133056 }]

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
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
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
    Slot6.Left16.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 122, numerator := 6141343163642316207507374080 }, { target := 124, numerator := 6141343163642316207507374080 }, { target := 161, numerator := 22609617119474771387272396800 }, { target := 162, numerator := 402451184726650930693448663040 }, { target := 163, numerator := 22609617119474771387272396800 }, { target := 164, numerator := 357985604391683880298479616000 }, { target := 165, numerator := 611213316129801319835930460160 }, { target := 166, numerator := 22609617119474771387272396800 }, { target := 167, numerator := 611213316129801319835930460160 }, { target := 168, numerator := 611213316129801319835930460160 }, { target := 169, numerator := 402451184726650930693448663040 }, { target := 170, numerator := 22609617119474771387272396800 }, { target := 197, numerator := 103174565149190912286123884544 }, { target := 199, numerator := 103174565149190912286123884544 }, { target := 211, numerator := 223544891156580309953268416512 }, { target := 213, numerator := 223544891156580309953268416512 }, { target := 232, numerator := 22607907106299138511837593600 }, { target := 233, numerator := 402420746492124665510709166080 }, { target := 234, numerator := 22607907106299138511837593600 }, { target := 235, numerator := 357958529183069693104095232000 }, { target := 236, numerator := 611167088773620044436676280320 }, { target := 237, numerator := 22607907106299138511837593600 }, { target := 238, numerator := 611167088773620044436676280320 }, { target := 239, numerator := 611167088773620044436676280320 }, { target := 240, numerator := 402420746492124665510709166080 }, { target := 241, numerator := 22607907106299138511837593600 }, { target := 242, numerator := 7369611796370779449008848896 }, { target := 244, numerator := 7369611796370779449008848896 }, { target := 256, numerator := 117913788741932471184141582336 }, { target := 258, numerator := 117913788741932471184141582336 }, { target := 261, numerator := 8597880429099242690510323712 }, { target := 263, numerator := 8597880429099242690510323712 }, { target := 337, numerator := 223544891156580309953268416512 }, { target := 339, numerator := 223544891156580309953268416512 }, { target := 351, numerator := 223544891156580309953268416512 }, { target := 353, numerator := 223544891156580309953268416512 }, { target := 382, numerator := 117913788741932471184141582336 }, { target := 384, numerator := 117913788741932471184141582336 }, { target := 396, numerator := 2758691349108128440412312436736 }, { target := 398, numerator := 2758691349108128440412312436736 }, { target := 401, numerator := 221088353891123383470265466880 }, { target := 403, numerator := 221088353891123383470265466880 }, { target := 406, numerator := 603468630301741642520985600 }, { target := 407, numerator := 10741741619371001236873543680 }, { target := 408, numerator := 603468630301741642520985600 }, { target := 409, numerator := 9554919979777576006582272000 }, { target := 410, numerator := 16313768639157082402817310720 }, { target := 411, numerator := 603468630301741642520985600 }, { target := 412, numerator := 16313768639157082402817310720 }, { target := 413, numerator := 16313768639157082402817310720 }, { target := 414, numerator := 10741741619371001236873543680 }, { target := 415, numerator := 603468630301741642520985600 }, { target := 416, numerator := 103174565149190912286123884544 }, { target := 418, numerator := 103174565149190912286123884544 }, { target := 421, numerator := 223544891156580309953268416512 }, { target := 423, numerator := 223544891156580309953268416512 }, { target := 453, numerator := 8597880429099242690510323712 }, { target := 455, numerator := 8597880429099242690510323712 }, { target := 467, numerator := 221088353891123383470265466880 }, { target := 469, numerator := 221088353891123383470265466880 }, { target := 472, numerator := 8597880429099242690510323712 }, { target := 474, numerator := 8597880429099242690510323712 }, { target := 487, numerator := 223544891156580309953268416512 }, { target := 489, numerator := 223544891156580309953268416512 }]

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
    Slot6.Left17.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 39747840885806901895523991552 }, { target := 36, numerator := 47200561051895696000934739968 }, { target := 37, numerator := 36021480802762504842818617344 }, { target := 38, numerator := 371393888276758239586302296064 }, { target := 39, numerator := 44716320996532764632464490496 }, { target := 40, numerator := 36021480802762504842818617344 }, { target := 41, numerator := 44716320996532764632464490496 }, { target := 42, numerator := 44716320996532764632464490496 }, { target := 43, numerator := 1915349082684820085090562342912 }, { target := 44, numerator := 44716320996532764632464490496 }, { target := 45, numerator := 371393888276758239586302296064 }, { target := 46, numerator := 1915349082684820085090562342912 }, { target := 47, numerator := 39747840885806901895523991552 }, { target := 48, numerator := 44716320996532764632464490496 }, { target := 49, numerator := 44716320996532764632464490496 }, { target := 50, numerator := 47200561051895696000934739968 }, { target := 86, numerator := 105989781712102013428075331584 }, { target := 89, numerator := 379171446071495352582886391808 }, { target := 91, numerator := 105989746476758184013496057856 }, { target := 145, numerator := 144571465339040025965693501440 }, { target := 146, numerator := 171678615090110030834261032960 }, { target := 147, numerator := 131017890463505023531409735680 }, { target := 148, numerator := 1350839629261655242616948654080 }, { target := 149, numerator := 162642898506420029211405189120 }, { target := 150, numerator := 131017890463505023531409735680 }, { target := 151, numerator := 162642898506420029211405189120 }, { target := 152, numerator := 162642898506420029211405189120 }, { target := 153, numerator := 6966537486024991251221855600640 }, { target := 154, numerator := 162642898506420029211405189120 }, { target := 155, numerator := 1350839629261655242616948654080 }, { target := 156, numerator := 6966537486024991251221855600640 }, { target := 157, numerator := 144571465339040025965693501440 }, { target := 158, numerator := 162642898506420029211405189120 }, { target := 159, numerator := 162642898506420029211405189120 }, { target := 160, numerator := 171678615090110030834261032960 }, { target := 161, numerator := 3914061630736320211572196638720 }, { target := 164, numerator := 14002297056998182388499103088640 }, { target := 166, numerator := 3914060329541949388877180436480 }, { target := 216, numerator := 39747840885806901895523991552 }, { target := 217, numerator := 47200561051895696000934739968 }, { target := 218, numerator := 36021480802762504842818617344 }, { target := 219, numerator := 371393888276758239586302296064 }, { target := 220, numerator := 44716320996532764632464490496 }, { target := 221, numerator := 36021480802762504842818617344 }, { target := 222, numerator := 44716320996532764632464490496 }, { target := 223, numerator := 44716320996532764632464490496 }, { target := 224, numerator := 1915349082684820085090562342912 }, { target := 225, numerator := 44716320996532764632464490496 }, { target := 226, numerator := 371393888276758239586302296064 }, { target := 227, numerator := 1915349082684820085090562342912 }, { target := 228, numerator := 39747840885806901895523991552 }, { target := 229, numerator := 44716320996532764632464490496 }, { target := 230, numerator := 44716320996532764632464490496 }, { target := 231, numerator := 47200561051895696000934739968 }, { target := 232, numerator := 3914060672281374540389987385344 }, { target := 235, numerator := 14002293628188896492751503228928 }, { target := 237, numerator := 3914059371087322347368607645696 }, { target := 406, numerator := 105990740167047684610284584960 }, { target := 409, numerator := 379174874880781248330486251520 }, { target := 411, numerator := 105990704931385225522068848640 }, { target := 492, numerator := 223544891156580309953268416512 }, { target := 494, numerator := 223544891156580309953268416512 }, { target := 498, numerator := 7369611796370779449008848896 }, { target := 500, numerator := 7369611796370779449008848896 }]

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
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 105615259515239462143877185536 }, { target := 37, numerator := 3900231024267287277962400890880 }, { target := 40, numerator := 3900230069199108199257867288576 }, { target := 47, numerator := 105616214583418540848410787840 }, { target := 86, numerator := 40077242882098119314547671040 }, { target := 89, numerator := 145769571405385661539994828800 }, { target := 91, numerator := 40077242882098119314547671040 }, { target := 112, numerator := 47591725922491516686025359360 }, { target := 115, numerator := 173101366043895473078743859200 }, { target := 117, numerator := 47591725922491516686025359360 }, { target := 145, numerator := 377831617640147312467752517632 }, { target := 147, numerator := 13952818975524690577939035586560 }, { target := 150, numerator := 13952815558831338554614572122112 }, { target := 157, numerator := 377835034333499335792215982080 }, { target := 161, numerator := 36320001361901420628808826880 }, { target := 164, numerator := 132103674086130755770620313600 }, { target := 166, numerator := 36320001361901420628808826880 }, { target := 187, numerator := 374471738179604302345304801280 }, { target := 190, numerator := 1362034432819072275014326681600 }, { target := 192, numerator := 374471738179604302345304801280 }, { target := 201, numerator := 45086898242360384228866129920 }, { target := 204, numerator := 163990767831058869232494182400 }, { target := 206, numerator := 45086898242360384228866129920 }, { target := 216, numerator := 105615224404402148027582644224 }, { target := 218, numerator := 3900229727670776422838745169920 }, { target := 221, numerator := 3900228772602914847907941187584 }, { target := 228, numerator := 105616179472263722958386626560 }, { target := 232, numerator := 36320001361901420628808826880 }, { target := 235, numerator := 132103674086130755770620313600 }, { target := 237, numerator := 36320001361901420628808826880 }, { target := 246, numerator := 45086898242360384228866129920 }, { target := 249, numerator := 163990767831058869232494182400 }, { target := 251, numerator := 45086898242360384228866129920 }, { target := 301, numerator := 45086898242360384228866129920 }, { target := 304, numerator := 163990767831058869232494182400 }, { target := 306, numerator := 45086898242360384228866129920 }, { target := 327, numerator := 1931222141381103124469765898240 }, { target := 330, numerator := 7024271222097021565458500812800 }, { target := 332, numerator := 1931222141381103124469765898240 }, { target := 341, numerator := 45086898242360384228866129920 }, { target := 344, numerator := 163990767831058869232494182400 }, { target := 346, numerator := 45086898242360384228866129920 }, { target := 372, numerator := 374471738179604302345304801280 }, { target := 375, numerator := 1362034432819072275014326681600 }, { target := 377, numerator := 374471738179604302345304801280 }, { target := 386, numerator := 1931222141381103124469765898240 }, { target := 389, numerator := 7024271222097021565458500812800 }, { target := 391, numerator := 1931222141381103124469765898240 }, { target := 406, numerator := 40077242882098119314547671040 }, { target := 409, numerator := 145769571405385661539994828800 }, { target := 411, numerator := 40077242882098119314547671040 }, { target := 443, numerator := 45086898242360384228866129920 }, { target := 446, numerator := 163990767831058869232494182400 }, { target := 448, numerator := 45086898242360384228866129920 }, { target := 457, numerator := 45086898242360384228866129920 }, { target := 460, numerator := 163990767831058869232494182400 }, { target := 462, numerator := 45086898242360384228866129920 }, { target := 477, numerator := 47591725922491516686025359360 }, { target := 480, numerator := 173101366043895473078743859200 }, { target := 482, numerator := 47591725922491516686025359360 }]

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
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 6238057229211486541483868160 }, { target := 17, numerator := 104799361450752973896928985088 }, { target := 18, numerator := 227065283143298110110012801024 }, { target := 19, numerator := 7485668675053783849780641792 }, { target := 20, numerator := 119770698800860541596490268672 }, { target := 21, numerator := 8733280120896081158077415424 }, { target := 22, numerator := 227065283143298110110012801024 }, { target := 23, numerator := 227065283143298110110012801024 }, { target := 24, numerator := 119770698800860541596490268672 }, { target := 25, numerator := 2802135307361799754434553577472 }, { target := 26, numerator := 224570060251613515493419253760 }, { target := 27, numerator := 104799361450752973896928985088 }, { target := 28, numerator := 227065283143298110110012801024 }, { target := 29, numerator := 8733280120896081158077415424 }, { target := 30, numerator := 224570060251613515493419253760 }, { target := 31, numerator := 8733280120896081158077415424 }, { target := 32, numerator := 227065283143298110110012801024 }, { target := 33, numerator := 227065283143298110110012801024 }, { target := 34, numerator := 7485668675053783849780641792 }, { target := 35, numerator := 616802582554261486263336960 }, { target := 37, numerator := 23174857547461640671954206720 }, { target := 40, numerator := 23173104783956616974633533440 }, { target := 47, numerator := 618555346059285183584010240 }, { target := 70, numerator := 10979085969465854455487397888 }, { target := 72, numerator := 412512464344817203960784879616 }, { target := 75, numerator := 412481265154427782148476895232 }, { target := 82, numerator := 11010285159855276267795382272 }, { target := 96, numerator := 616802582554261486263336960 }, { target := 98, numerator := 23174857547461640671954206720 }, { target := 101, numerator := 23173104783956616974633533440 }, { target := 108, numerator := 618555346059285183584010240 }, { target := 126, numerator := 6238057229211486541483868160 }, { target := 127, numerator := 104799361450752973896928985088 }, { target := 128, numerator := 227065283143298110110012801024 }, { target := 129, numerator := 7485668675053783849780641792 }, { target := 130, numerator := 119770698800860541596490268672 }, { target := 131, numerator := 8733280120896081158077415424 }, { target := 132, numerator := 227065283143298110110012801024 }, { target := 133, numerator := 227065283143298110110012801024 }, { target := 134, numerator := 119770698800860541596490268672 }, { target := 135, numerator := 2802135307361799754434553577472 }, { target := 136, numerator := 224570060251613515493419253760 }, { target := 137, numerator := 104799361450752973896928985088 }, { target := 138, numerator := 227065283143298110110012801024 }, { target := 139, numerator := 8733280120896081158077415424 }, { target := 140, numerator := 224570060251613515493419253760 }, { target := 141, numerator := 8733280120896081158077415424 }, { target := 142, numerator := 227065283143298110110012801024 }, { target := 143, numerator := 227065283143298110110012801024 }, { target := 144, numerator := 7485668675053783849780641792 }, { target := 145, numerator := 9766040890442473532502835200 }, { target := 147, numerator := 366935244501475977305941606400 }, { target := 150, numerator := 366907492412646435431697612800 }, { target := 157, numerator := 9793792979272015406746828800 }, { target := 171, numerator := 16674229815050202178652209152 }, { target := 173, numerator := 626493649033046352831828721664 }, { target := 176, numerator := 626446265992960545547593187328 }, { target := 183, numerator := 16721612855136009462887743488 }, { target := 216, numerator := 616802582554261486263336960 }, { target := 218, numerator := 23174857547461640671954206720 }, { target := 221, numerator := 23173104783956616974633533440 }, { target := 228, numerator := 618555346059285183584010240 }]

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
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2611279770367599017365340160 }, { target := 1, numerator := 2030995376952577013506375680 }, { target := 2, numerator := 2321137573660088015435857920 }, { target := 3, numerator := 2727336649050603418137133056 }, { target := 4, numerator := 32205783834533721214172528640 }, { target := 5, numerator := 72419492298194746081598767104 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 32205783834533721214172528640 }, { target := 8, numerator := 2321137573660088015435857920 }, { target := 9, numerator := 2263109134318585815049961472 }, { target := 10, numerator := 2263109134318585815049961472 }, { target := 11, numerator := 2263109134318585815049961472 }, { target := 12, numerator := 72419492298194746081598767104 }, { target := 13, numerator := 2263109134318585815049961472 }, { target := 14, numerator := 2611279770367599017365340160 }, { target := 15, numerator := 2727336649050603418137133056 }, { target := 16, numerator := 878252155515516421895356416 }, { target := 17, numerator := 139359369095914713204847017984 }, { target := 19, numerator := 1395270120887186499448514543616 }, { target := 27, numerator := 139359369095914713204847017984 }, { target := 34, numerator := 878160069369100463813689344 }, { target := 51, numerator := 79760165764799893671510016 }, { target := 52, numerator := 11780159082987596645302009856 }, { target := 54, numerator := 122782628026674428829646192640 }, { target := 62, numerator := 11780159082987596645302009856 }, { target := 69, numerator := 79760165764799893671510016 }, { target := 126, numerator := 878252155515516421895356416 }, { target := 127, numerator := 139359369095914713204847017984 }, { target := 129, numerator := 1395270120887186499448514543616 }, { target := 137, numerator := 139359369095914713204847017984 }, { target := 144, numerator := 878160069369100463813689344 }, { target := 266, numerator := 79760165764799893671510016 }, { target := 267, numerator := 11780159082987596645302009856 }, { target := 269, numerator := 122782628026674428829646192640 }, { target := 277, numerator := 11780159082987596645302009856 }, { target := 284, numerator := 79760165764799893671510016 }, { target := 285, numerator := 16674229815050202178652209152 }, { target := 287, numerator := 626493649033046352831828721664 }, { target := 290, numerator := 626446265992960545547593187328 }, { target := 297, numerator := 16721612855136009462887743488 }, { target := 311, numerator := 16674229815050202178652209152 }, { target := 313, numerator := 626493649033046352831828721664 }, { target := 316, numerator := 626446265992960545547593187328 }, { target := 323, numerator := 16721612855136009462887743488 }, { target := 356, numerator := 10979085969465854455487397888 }, { target := 358, numerator := 412512464344817203960784879616 }, { target := 361, numerator := 412481265154427782148476895232 }, { target := 368, numerator := 11010285159855276267795382272 }, { target := 427, numerator := 616802582554261486263336960 }, { target := 429, numerator := 23174857547461640671954206720 }, { target := 432, numerator := 23173104783956616974633533440 }, { target := 439, numerator := 618555346059285183584010240 }]

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
    Slot16.Left0.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 933097115716696067419406336 }, { target := 1, numerator := 78295065398547641526124544000 }, { target := 6, numerator := 78295070120914124395769757696 }, { target := 14, numerator := 933092393350213197774192640 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20.Parent3
