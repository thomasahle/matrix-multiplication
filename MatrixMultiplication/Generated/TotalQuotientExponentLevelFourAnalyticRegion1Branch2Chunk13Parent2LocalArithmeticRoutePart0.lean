import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 56; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent2

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
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
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
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 645057112269668015205777408 }, { target := 38, numerator := 2307649229077200250387562496 }, { target := 40, numerator := 645056897826268158332239872 }, { target := 61, numerator := 15814303397578957792141639680 }, { target := 64, numerator := 56574626261247490009501532160 }, { target := 66, numerator := 15814298140256896784919429120 }, { target := 71, numerator := 25532513310260968169794437120 }, { target := 73, numerator := 25532513310260968169794437120 }, { target := 75, numerator := 645057112269668015205777408 }, { target := 78, numerator := 2307649229077200250387562496 }, { target := 80, numerator := 645056897826268158332239872 }, { target := 85, numerator := 25000585949630531332923719680 }, { target := 87, numerator := 25000585949630531332923719680 }, { target := 89, numerator := 7659753993078290450938331136 }, { target := 106, numerator := 13254883242444468570518716416 }, { target := 109, numerator := 47418469642650856757963784192 }, { target := 111, numerator := 13254878835978477963149574144 }, { target := 116, numerator := 19681312343326162964216545280 }, { target := 118, numerator := 19681312343326162964216545280 }, { target := 130, numerator := 618631520413198041280644382720 }, { target := 132, numerator := 618631520413198041280644382720 }, { target := 134, numerator := 204260106482087745358355496960 }, { target := 135, numerator := 19681312343326162964216545280 }, { target := 137, numerator := 19681312343326162964216545280 }, { target := 139, numerator := 195323726823496406498927443968 }, { target := 150, numerator := 19681312343326162964216545280 }, { target := 152, numerator := 19681312343326162964216545280 }, { target := 154, numerator := 6383128327565242042448609280 }, { target := 155, numerator := 20213239703956599801087262720 }, { target := 157, numerator := 20213239703956599801087262720 }, { target := 159, numerator := 200430229485548600132886331392 }, { target := 160, numerator := 6383128327565242042448609280 }, { target := 187, numerator := 20213239703956599801087262720 }, { target := 189, numerator := 20213239703956599801087262720 }, { target := 201, numerator := 342029292885370886107871313920 }, { target := 203, numerator := 342029292885370886107871313920 }, { target := 205, numerator := 195323726823496406498927443968 }, { target := 206, numerator := 18617457622065289290475110400 }, { target := 208, numerator := 18617457622065289290475110400 }, { target := 210, numerator := 111066432899635211538605801472 }, { target := 221, numerator := 618631520413198041280644382720 }, { target := 223, numerator := 618631520413198041280644382720 }, { target := 225, numerator := 200430229485548600132886331392 }, { target := 226, numerator := 342029292885370886107871313920 }, { target := 228, numerator := 342029292885370886107871313920 }, { target := 230, numerator := 3129009506172481649208308269056 }, { target := 231, numerator := 122556063889252647215013298176 }, { target := 232, numerator := 25532513310260968169794437120 }, { target := 234, numerator := 25532513310260968169794437120 }, { target := 236, numerator := 204260106482087745358355496960 }, { target := 237, numerator := 195323726823496406498927443968 }, { target := 248, numerator := 19681312343326162964216545280 }, { target := 250, numerator := 19681312343326162964216545280 }, { target := 252, numerator := 6383128327565242042448609280 }, { target := 253, numerator := 18617457622065289290475110400 }, { target := 255, numerator := 18617457622065289290475110400 }, { target := 257, numerator := 122556063889252647215013298176 }, { target := 258, numerator := 6383128327565242042448609280 }, { target := 259, numerator := 25000585949630531332923719680 }, { target := 261, numerator := 25000585949630531332923719680 }, { target := 263, numerator := 196600352489009454907417165824 }, { target := 264, numerator := 111066432899635211538605801472 }, { target := 265, numerator := 7659753993078290450938331136 }]

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
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 154893620638124363009228800 }, { target := 20, numerator := 183936174507772681073459200 }, { target := 21, numerator := 140372343703300203977113600 }, { target := 22, numerator := 1447287267837474516867481600 }, { target := 23, numerator := 174255323217889908385382400 }, { target := 24, numerator := 140372343703300203977113600 }, { target := 25, numerator := 174255323217889908385382400 }, { target := 26, numerator := 174255323217889908385382400 }, { target := 27, numerator := 7463936344499617742507212800 }, { target := 28, numerator := 174255323217889908385382400 }, { target := 29, numerator := 1447287267837474516867481600 }, { target := 30, numerator := 7463936344499617742507212800 }, { target := 31, numerator := 154893620638124363009228800 }, { target := 32, numerator := 174255323217889908385382400 }, { target := 33, numerator := 174255323217889908385382400 }, { target := 34, numerator := 183936174507772681073459200 }, { target := 45, numerator := 153835810545961562481360896 }, { target := 46, numerator := 182680025023329355446616064 }, { target := 47, numerator := 139413703307277665998733312 }, { target := 48, numerator := 1437403354788828349435215872 }, { target := 49, numerator := 173065286864206757791531008 }, { target := 50, numerator := 139413703307277665998733312 }, { target := 51, numerator := 173065286864206757791531008 }, { target := 52, numerator := 173065286864206757791531008 }, { target := 53, numerator := 7412963120683522792070578176 }, { target := 54, numerator := 173065286864206757791531008 }, { target := 55, numerator := 1437403354788828349435215872 }, { target := 56, numerator := 7412963120683522792070578176 }, { target := 57, numerator := 153835810545961562481360896 }, { target := 58, numerator := 173065286864206757791531008 }, { target := 59, numerator := 173065286864206757791531008 }, { target := 60, numerator := 182680025023329355446616064 }, { target := 120, numerator := 13025992009058457339316666368 }, { target := 123, numerator := 46599626367817011507826262016 }, { target := 125, numerator := 13025987678685286035999424512 }, { target := 140, numerator := 645057112269668015205777408 }, { target := 143, numerator := 2307649229077200250387562496 }, { target := 145, numerator := 645056897826268158332239872 }, { target := 177, numerator := 13046800303002640178516852736 }, { target := 180, numerator := 46674066665529179257838764032 }, { target := 182, numerator := 13046795965711939847558529024 }, { target := 191, numerator := 11694261196630755630504738816 }, { target := 194, numerator := 41835447314238275507026132992 }, { target := 196, numerator := 11694257308979442096216735744 }, { target := 211, numerator := 15814303397578957792141639680 }, { target := 214, numerator := 56574626261247490009501532160 }, { target := 216, numerator := 15814298140256896784919429120 }, { target := 238, numerator := 645057112269668015205777408 }, { target := 241, numerator := 2307649229077200250387562496 }, { target := 243, numerator := 645056897826268158332239872 }]

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
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 17237096895856769889541816320 }, { target := 21, numerator := 636543056278921076587207065600 }, { target := 24, numerator := 636542900405585911854787461120 }, { target := 31, numerator := 17237252769191934621961420800 }, { target := 35, numerator := 1916614745787309718230710353920 }, { target := 38, numerator := 6971140975554854485630543462400 }, { target := 40, numerator := 1916614745787309718230710353920 }, { target := 71, numerator := 1676011988754003622070457466880 }, { target := 73, numerator := 1676011189569400330701030555648 }, { target := 89, numerator := 44341854849624699754237657088 }, { target := 90, numerator := 17384196284130706330017071104 }, { target := 91, numerator := 183936174507772681073459200 }, { target := 92, numerator := 636395597990794442053695569920 }, { target := 93, numerator := 1447287267837474516867481600 }, { target := 94, numerator := 174255323217889908385382400 }, { target := 95, numerator := 636395442187941737389531070464 }, { target := 96, numerator := 174255323217889908385382400 }, { target := 97, numerator := 174255323217889908385382400 }, { target := 98, numerator := 7463936344499617742507212800 }, { target := 99, numerator := 174255323217889908385382400 }, { target := 100, numerator := 1447287267837474516867481600 }, { target := 101, numerator := 7463936344499617742507212800 }, { target := 102, numerator := 17384352086983410994181570560 }, { target := 103, numerator := 174255323217889908385382400 }, { target := 104, numerator := 174255323217889908385382400 }, { target := 105, numerator := 183936174507772681073459200 }, { target := 106, numerator := 6553035671887935308743776927744 }, { target := 109, numerator := 23834803309835357860625310023680 }, { target := 111, numerator := 6553035671887935308743776927744 }, { target := 116, numerator := 58656240958020728120324799856640 }, { target := 118, numerator := 58656212988552147260931827564544 }, { target := 134, numerator := 4649163507470644047646642143232 }, { target := 140, numerator := 1916614126717701006454809427968 }, { target := 143, numerator := 6971138723865241068514532392960 }, { target := 145, numerator := 1916614126717701006454809427968 }, { target := 150, numerator := 58656269726684200744435926958080 }, { target := 152, numerator := 58656241757201901920577984135168 }, { target := 154, numerator := 50113335777074751402846191616000 }, { target := 161, numerator := 155346967820479848949743616 }, { target := 162, numerator := 184474524286819820627820544 }, { target := 163, numerator := 140783189587309863110705152 }, { target := 164, numerator := 1451523230572608588624166912 }, { target := 165, numerator := 174765338798039830068461568 }, { target := 166, numerator := 140783189587309863110705152 }, { target := 167, numerator := 174765338798039830068461568 }, { target := 168, numerator := 174765338798039830068461568 }, { target := 169, numerator := 7485782011849372721265770496 }, { target := 170, numerator := 174765338798039830068461568 }, { target := 171, numerator := 1451523230572608588624166912 }, { target := 172, numerator := 7485782011849372721265770496 }, { target := 173, numerator := 155346967820479848949743616 }, { target := 174, numerator := 174765338798039830068461568 }, { target := 175, numerator := 174765338798039830068461568 }, { target := 176, numerator := 184474524286819820627820544 }, { target := 232, numerator := 1675997604422267310014893916160 }, { target := 234, numerator := 1675996805244523000877952270336 }, { target := 236, numerator := 4649167053967872682750197628928 }, { target := 265, numerator := 44341854849624699754237657088 }]

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
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1172771381821779170950119424 }, { target := 1, numerator := 173414326415688619008565706752 }, { target := 2, numerator := 3520391986717800156744384512 }, { target := 3, numerator := 1714317230170326003974221594624 }, { target := 4, numerator := 1856910058928070412348686336 }, { target := 5, numerator := 135399691796838467567091712 }, { target := 6, numerator := 3520391986717800156744384512 }, { target := 7, numerator := 3520391986717800156744384512 }, { target := 8, numerator := 1856910058928070412348686336 }, { target := 9, numerator := 43443958253671314022241140736 }, { target := 10, numerator := 3481706360490132023153786880 }, { target := 11, numerator := 173414326415688619008565706752 }, { target := 12, numerator := 3520391986717800156744384512 }, { target := 13, numerator := 135399691796838467567091712 }, { target := 14, numerator := 3481706360490132023153786880 }, { target := 15, numerator := 135399691796838467567091712 }, { target := 16, numerator := 3520391986717800156744384512 }, { target := 17, numerator := 3520391986717800156744384512 }, { target := 18, numerator := 1191991413407058626969862144 }, { target := 19, numerator := 452394104907180222978497445888 }, { target := 21, numerator := 16997608688859540131999557615616 }, { target := 24, numerator := 16996323123754275011352678367232 }, { target := 31, numerator := 453679670012445343625376694272 }, { target := 35, numerator := 25087666910796006827134896046080 }, { target := 38, numerator := 86121573908184464745635914973184 }, { target := 40, numerator := 25087666910796006827134896046080 }, { target := 71, numerator := 3373959817341084932375442358272 }, { target := 73, numerator := 3373959817341084932375442358272 }, { target := 89, numerator := 14318224620793730027216699392 }, { target := 90, numerator := 452394104907180222978497445888 }, { target := 92, numerator := 16997608688859540131999557615616 }, { target := 95, numerator := 16996323123754275011352678367232 }, { target := 102, numerator := 453679670012445343625376694272 }, { target := 106, numerator := 85040415378320264529030970081280 }, { target := 109, numerator := 291928876616065452309466153222144 }, { target := 111, numerator := 85040415378320264529030970081280 }, { target := 116, numerator := 122876117149139137022936842502144 }, { target := 118, numerator := 122876117149139137022936842502144 }, { target := 134, numerator := 2127588342155660638301009739776 }, { target := 140, numerator := 25087666910796006827134896046080 }, { target := 143, numerator := 86121573908184464745635914973184 }, { target := 145, numerator := 25087666910796006827134896046080 }, { target := 150, numerator := 105878547370218232495379023134720 }, { target := 152, numerator := 105878547370218232495379023134720 }, { target := 154, numerator := 22099165106478644236604458139648 }, { target := 232, numerator := 2921526802495269104955206664192 }, { target := 234, numerator := 2921526802495269104955206664192 }, { target := 236, numerator := 2127588342155660638301009739776 }, { target := 265, numerator := 14318101839265175416441143296 }]

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
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected,
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected,
    Slot19.Left15.expected,
    Slot19.Left16.expected,
    Slot19.Left17.expected,
    Slot19.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 13328435495450183869006872576 }, { target := 1, numerator := 1968540172380566876218579746816 }, { target := 3, numerator := 20517765001155646196229907415040 }, { target := 11, numerator := 1968540172380566876218579746816 }, { target := 18, numerator := 13328435495450183869006872576 }, { target := 19, numerator := 2920501971049439424594688606208 }, { target := 21, numerator := 105839958120406930006942769217536 }, { target := 24, numerator := 105839997016178466162775571824640 }, { target := 31, numerator := 2920463075277903268761885999104 }, { target := 35, numerator := 27017922601421607679667271106560 }, { target := 38, numerator := 91639614080817289482261304967168 }, { target := 40, numerator := 27017921983189711564253719166976 }, { target := 71, numerator := 17237096895856769889541816320 }, { target := 73, numerator := 17229302663492581967007842304 }, { target := 89, numerator := 96714065569170333976494080 }, { target := 90, numerator := 2920501971049439424594688606208 }, { target := 92, numerator := 105839958120406930006942769217536 }, { target := 95, numerator := 105839997016178466162775571824640 }, { target := 102, numerator := 2920463075277903268761885999104 }, { target := 106, numerator := 93139011770664078412208947593216 }, { target := 109, numerator := 315920337119328903187124784726016 }, { target := 111, numerator := 93139009522021406285237883764736 }, { target := 116, numerator := 636543056278921076587207065600 }, { target := 118, numerator := 636255225647091141849718456320 }, { target := 134, numerator := 1624796301562061610805100544 }, { target := 139, numerator := 3520391986717800156744384512 }, { target := 140, numerator := 27017922601421607679667271106560 }, { target := 143, numerator := 91639614080817289482261304967168 }, { target := 145, numerator := 27017921983189711564253719166976 }, { target := 150, numerator := 17632866024159860923207465828352 }, { target := 152, numerator := 17632578193598513448538232324096 }, { target := 154, numerator := 116056878683004400771792896 }, { target := 159, numerator := 1856910058928070412348686336 }, { target := 160, numerator := 135399691796838467567091712 }, { target := 205, numerator := 3520391986717800156744384512 }, { target := 210, numerator := 3520391986717800156744384512 }, { target := 225, numerator := 1856910058928070412348686336 }, { target := 230, numerator := 43443958253671314022241140736 }, { target := 231, numerator := 3481706360490132023153786880 }, { target := 232, numerator := 470916922781637278247338115072 }, { target := 234, numerator := 470909128478790630256549036032 }, { target := 236, numerator := 1624796301562061610805100544 }, { target := 237, numerator := 3520391986717800156744384512 }, { target := 252, numerator := 135399691796838467567091712 }, { target := 257, numerator := 3481706360490132023153786880 }, { target := 258, numerator := 135399691796838467567091712 }, { target := 263, numerator := 3520391986717800156744384512 }, { target := 264, numerator := 3520391986717800156744384512 }, { target := 265, numerator := 116056878683004400771792896 }]

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
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left1.expected,
    Slot24.Left2.expected,
    Slot24.Left3.expected,
    Slot24.Left4.expected,
    Slot24.Left5.expected,
    Slot24.Left6.expected,
    Slot24.Left7.expected,
    Slot24.Left8.expected,
    Slot24.Left9.expected,
    Slot24.Left10.expected,
    Slot24.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 45522729812331083236374478848 }, { target := 1, numerator := 4772976117523124581538696527872 }, { target := 3, numerator := 51447911962882334662575783936000 }, { target := 11, numerator := 4772979758467682874035156287488 }, { target := 18, numerator := 45522729812331083236374478848 }, { target := 19, numerator := 1671610118790106041973095792640 }, { target := 21, numerator := 58502186484066635597356120145920 }, { target := 24, numerator := 58502215177172226481154414346240 }, { target := 31, numerator := 1671595772237310600073948692480 }, { target := 71, numerator := 154893620638124363009228800 }, { target := 72, numerator := 153835810545961562481360896 }, { target := 73, numerator := 154893620638124363009228800 }, { target := 74, numerator := 155346967820479848949743616 }, { target := 85, numerator := 183936174507772681073459200 }, { target := 86, numerator := 182680025023329355446616064 }, { target := 87, numerator := 183936174507772681073459200 }, { target := 88, numerator := 184474524286819820627820544 }, { target := 90, numerator := 1671609321704477414533726470144 }, { target := 92, numerator := 58502158588056934792748158943232 }, { target := 95, numerator := 58502187281148843740878501576704 }, { target := 102, numerator := 1671594975158522940468555153408 }, { target := 116, numerator := 140372343703300203977113600 }, { target := 117, numerator := 139413703307277665998733312 }, { target := 118, numerator := 140372343703300203977113600 }, { target := 119, numerator := 140783189587309863110705152 }, { target := 130, numerator := 1447287267837474516867481600 }, { target := 131, numerator := 1437403354788828349435215872 }, { target := 132, numerator := 1447287267837474516867481600 }, { target := 133, numerator := 1451523230572608588624166912 }, { target := 135, numerator := 174255323217889908385382400 }, { target := 136, numerator := 173065286864206757791531008 }, { target := 137, numerator := 174255323217889908385382400 }, { target := 138, numerator := 174765338798039830068461568 }, { target := 150, numerator := 140372343703300203977113600 }, { target := 151, numerator := 139413703307277665998733312 }, { target := 152, numerator := 140372343703300203977113600 }, { target := 153, numerator := 140783189587309863110705152 }, { target := 155, numerator := 174255323217889908385382400 }, { target := 156, numerator := 173065286864206757791531008 }, { target := 157, numerator := 174255323217889908385382400 }, { target := 158, numerator := 174765338798039830068461568 }, { target := 187, numerator := 174255323217889908385382400 }, { target := 188, numerator := 173065286864206757791531008 }, { target := 189, numerator := 174255323217889908385382400 }, { target := 190, numerator := 174765338798039830068461568 }, { target := 201, numerator := 7463936344499617742507212800 }, { target := 202, numerator := 7412963120683522792070578176 }, { target := 203, numerator := 7463936344499617742507212800 }, { target := 204, numerator := 7485782011849372721265770496 }, { target := 206, numerator := 174255323217889908385382400 }, { target := 207, numerator := 173065286864206757791531008 }, { target := 208, numerator := 174255323217889908385382400 }, { target := 209, numerator := 174765338798039830068461568 }, { target := 221, numerator := 1447287267837474516867481600 }, { target := 222, numerator := 1437403354788828349435215872 }, { target := 223, numerator := 1447287267837474516867481600 }, { target := 224, numerator := 1451523230572608588624166912 }, { target := 226, numerator := 7463936344499617742507212800 }, { target := 227, numerator := 7412963120683522792070578176 }, { target := 228, numerator := 7463936344499617742507212800 }, { target := 229, numerator := 7485782011849372721265770496 }]

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
    Slot24.Left12.expected,
    Slot24.Left13.expected,
    Slot24.Left14.expected,
    Slot24.Left15.expected,
    Slot25.Left0.expected,
    Slot25.Left3.expected,
    Slot25.Left5.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 25996740824992985772881608704 }, { target := 20, numerator := 25455142057805631902613241856 }, { target := 21, numerator := 20039154385932093199929573376 }, { target := 22, numerator := 629879366238892551122110644224 }, { target := 23, numerator := 20039154385932093199929573376 }, { target := 24, numerator := 20039154385932093199929573376 }, { target := 25, numerator := 20580753153119447070197940224 }, { target := 26, numerator := 20580753153119447070197940224 }, { target := 27, numerator := 348248007301468538582559883264 }, { target := 28, numerator := 18955956851557385459392839680 }, { target := 29, numerator := 629879366238892551122110644224 }, { target := 30, numerator := 348248007301468538582559883264 }, { target := 31, numerator := 25996740824992985772881608704 }, { target := 32, numerator := 20039154385932093199929573376 }, { target := 33, numerator := 18955956851557385459392839680 }, { target := 34, numerator := 25455142057805631902613241856 }, { target := 35, numerator := 645057112269668015205777408 }, { target := 36, numerator := 15814303397578957792141639680 }, { target := 37, numerator := 645057112269668015205777408 }, { target := 38, numerator := 13254883242444468570518716416 }, { target := 39, numerator := 13025992009058457339316666368 }, { target := 40, numerator := 645057112269668015205777408 }, { target := 41, numerator := 13046800303002640178516852736 }, { target := 42, numerator := 11694261196630755630504738816 }, { target := 43, numerator := 15814303397578957792141639680 }, { target := 44, numerator := 645057112269668015205777408 }, { target := 106, numerator := 2307649229077200250387562496 }, { target := 107, numerator := 56574626261247490009501532160 }, { target := 108, numerator := 2307649229077200250387562496 }, { target := 109, numerator := 47418469642650856757963784192 }, { target := 110, numerator := 46599626367817011507826262016 }, { target := 111, numerator := 2307649229077200250387562496 }, { target := 112, numerator := 46674066665529179257838764032 }, { target := 113, numerator := 41835447314238275507026132992 }, { target := 114, numerator := 56574626261247490009501532160 }, { target := 115, numerator := 2307649229077200250387562496 }, { target := 140, numerator := 645056897826268158332239872 }, { target := 141, numerator := 15814298140256896784919429120 }, { target := 142, numerator := 645056897826268158332239872 }, { target := 143, numerator := 13254878835978477963149574144 }, { target := 144, numerator := 13025987678685286035999424512 }, { target := 145, numerator := 645056897826268158332239872 }, { target := 146, numerator := 13046795965711939847558529024 }, { target := 147, numerator := 11694257308979442096216735744 }, { target := 148, numerator := 15814298140256896784919429120 }, { target := 149, numerator := 645056897826268158332239872 }, { target := 232, numerator := 154893620638124363009228800 }, { target := 233, numerator := 153835810545961562481360896 }, { target := 234, numerator := 154893620638124363009228800 }, { target := 235, numerator := 155346967820479848949743616 }, { target := 248, numerator := 174255323217889908385382400 }, { target := 249, numerator := 173065286864206757791531008 }, { target := 250, numerator := 174255323217889908385382400 }, { target := 251, numerator := 174765338798039830068461568 }, { target := 253, numerator := 174255323217889908385382400 }, { target := 254, numerator := 173065286864206757791531008 }, { target := 255, numerator := 174255323217889908385382400 }, { target := 256, numerator := 174765338798039830068461568 }, { target := 259, numerator := 183936174507772681073459200 }, { target := 260, numerator := 182680025023329355446616064 }, { target := 261, numerator := 183936174507772681073459200 }, { target := 262, numerator := 184474524286819820627820544 }]

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
    Slot26.Left2.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 7775810871761294851710124032 }, { target := 1, numerator := 207354956580301196045603307520 }, { target := 2, numerator := 198283177229913018718608162816 }, { target := 3, numerator := 6479842393134412376425103360 }, { target := 4, numerator := 203467051144420548619748245504 }, { target := 5, numerator := 6479842393134412376425103360 }, { target := 6, numerator := 198283177229913018718608162816 }, { target := 7, numerator := 112749257640538775349796798464 }, { target := 8, numerator := 203467051144420548619748245504 }, { target := 9, numerator := 3176418741114488946923585667072 }, { target := 10, numerator := 124412973948180717627361984512 }, { target := 11, numerator := 207354956580301196045603307520 }, { target := 12, numerator := 198283177229913018718608162816 }, { target := 13, numerator := 6479842393134412376425103360 }, { target := 14, numerator := 124412973948180717627361984512 }, { target := 15, numerator := 6479842393134412376425103360 }, { target := 16, numerator := 199579145708539901193893183488 }, { target := 17, numerator := 112749257640538775349796798464 }, { target := 18, numerator := 7775810871761294851710124032 }, { target := 90, numerator := 25996740824992985772881608704 }, { target := 91, numerator := 25455142057805631902613241856 }, { target := 92, numerator := 20039154385932093199929573376 }, { target := 93, numerator := 629879366238892551122110644224 }, { target := 94, numerator := 20039154385932093199929573376 }, { target := 95, numerator := 20039154385932093199929573376 }, { target := 96, numerator := 20580753153119447070197940224 }, { target := 97, numerator := 20580753153119447070197940224 }, { target := 98, numerator := 348248007301468538582559883264 }, { target := 99, numerator := 18955956851557385459392839680 }, { target := 100, numerator := 629879366238892551122110644224 }, { target := 101, numerator := 348248007301468538582559883264 }, { target := 102, numerator := 25996740824992985772881608704 }, { target := 103, numerator := 20039154385932093199929573376 }, { target := 104, numerator := 18955956851557385459392839680 }, { target := 105, numerator := 25455142057805631902613241856 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent2
