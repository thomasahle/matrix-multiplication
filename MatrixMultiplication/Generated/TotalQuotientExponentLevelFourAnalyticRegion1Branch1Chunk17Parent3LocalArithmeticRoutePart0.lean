import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk17Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent3

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
  [{ target := 122, numerator := 27654178123684642371403776 }, { target := 123, numerator := 30374261217817558014492672 }, { target := 124, numerator := 27654178123684642371403776 }, { target := 125, numerator := 30374261217817558014492672 }, { target := 197, numerator := 400985582793427314385354752 }, { target := 198, numerator := 440426787658354591210143744 }, { target := 199, numerator := 400985582793427314385354752 }, { target := 200, numerator := 440426787658354591210143744 }, { target := 211, numerator := 709790571841239154199363584 }, { target := 212, numerator := 779606037923983989038645248 }, { target := 213, numerator := 709790571841239154199363584 }, { target := 214, numerator := 779606037923983989038645248 }, { target := 242, numerator := 23045148436403868642836480 }, { target := 243, numerator := 25311884348181298345410560 }, { target := 244, numerator := 23045148436403868642836480 }, { target := 245, numerator := 25311884348181298345410560 }, { target := 256, numerator := 442466849978954277942460416 }, { target := 257, numerator := 485988179485080928231882752 }, { target := 258, numerator := 442466849978954277942460416 }, { target := 259, numerator := 485988179485080928231882752 }, { target := 261, numerator := 23045148436403868642836480 }, { target := 262, numerator := 25311884348181298345410560 }, { target := 263, numerator := 23045148436403868642836480 }, { target := 264, numerator := 25311884348181298345410560 }, { target := 337, numerator := 705181542153958380470796288 }, { target := 338, numerator := 774543661054347729369563136 }, { target := 339, numerator := 705181542153958380470796288 }, { target := 340, numerator := 774543661054347729369563136 }, { target := 351, numerator := 737444749964923796570767360 }, { target := 352, numerator := 809980299141801547053137920 }, { target := 353, numerator := 737444749964923796570767360 }, { target := 354, numerator := 809980299141801547053137920 }, { target := 382, numerator := 442466849978954277942460416 }, { target := 383, numerator := 485988179485080928231882752 }, { target := 384, numerator := 442466849978954277942460416 }, { target := 385, numerator := 485988179485080928231882752 }, { target := 396, numerator := 11296731763525176408718442496 }, { target := 397, numerator := 12407885707478472448920256512 }, { target := 398, numerator := 11296731763525176408718442496 }, { target := 399, numerator := 12407885707478472448920256512 }, { target := 401, numerator := 723617660903081475385065472 }, { target := 402, numerator := 794793168532892768045891584 }, { target := 403, numerator := 723617660903081475385065472 }, { target := 404, numerator := 794793168532892768045891584 }, { target := 416, numerator := 400985582793427314385354752 }, { target := 417, numerator := 440426787658354591210143744 }, { target := 418, numerator := 400985582793427314385354752 }, { target := 419, numerator := 440426787658354591210143744 }, { target := 421, numerator := 705181542153958380470796288 }, { target := 422, numerator := 774543661054347729369563136 }, { target := 423, numerator := 705181542153958380470796288 }, { target := 424, numerator := 774543661054347729369563136 }, { target := 453, numerator := 23045148436403868642836480 }, { target := 454, numerator := 25311884348181298345410560 }, { target := 455, numerator := 23045148436403868642836480 }, { target := 456, numerator := 25311884348181298345410560 }, { target := 467, numerator := 723617660903081475385065472 }, { target := 468, numerator := 794793168532892768045891584 }, { target := 469, numerator := 723617660903081475385065472 }, { target := 470, numerator := 794793168532892768045891584 }, { target := 472, numerator := 23045148436403868642836480 }, { target := 473, numerator := 25311884348181298345410560 }, { target := 474, numerator := 23045148436403868642836480 }, { target := 475, numerator := 25311884348181298345410560 }]

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
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
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
    Slot4.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 211459749683415459819421696 }, { target := 87, numerator := 4229194993668309196388433920 }, { target := 88, numerator := 219011883600680297670115328 }, { target := 89, numerator := 3934661770894980520211382272 }, { target := 90, numerator := 5890664455466573523541032960 }, { target := 91, numerator := 211459749683415459819421696 }, { target := 92, numerator := 5898216589383838361391726592 }, { target := 93, numerator := 5898216589383838361391726592 }, { target := 94, numerator := 4221642859751044358537740288 }, { target := 95, numerator := 219011883600680297670115328 }, { target := 122, numerator := 785612888090194177750466560 }, { target := 124, numerator := 785612888090194177750466560 }, { target := 161, numerator := 8454121558331914592209338368 }, { target := 162, numerator := 169082431166638291844186767360 }, { target := 163, numerator := 8756054471129482970502529024 }, { target := 164, numerator := 157307047567533125090752331776 }, { target := 165, numerator := 235507671982103335068688711680 }, { target := 166, numerator := 8454121558331914592209338368 }, { target := 167, numerator := 235809604894900903446981902336 }, { target := 168, numerator := 235809604894900903446981902336 }, { target := 169, numerator := 168780498253840723465893576704 }, { target := 170, numerator := 8756054471129482970502529024 }, { target := 197, numerator := 128746821895771711390036787200 }, { target := 199, numerator := 128746821895771711390036787200 }, { target := 215, numerator := 1391119440890222956695781376 }, { target := 232, numerator := 8454119492296578336739557376 }, { target := 233, numerator := 169082389845931566734791147520 }, { target := 234, numerator := 8756052331307170420194541568 }, { target := 235, numerator := 157307009124518475480046764032 }, { target := 236, numerator := 235507614428261825094887669760 }, { target := 237, numerator := 8454119492296578336739557376 }, { target := 238, numerator := 235809547267272417178342653952 }, { target := 239, numerator := 235809547267272417178342653952 }, { target := 240, numerator := 168780457006920974651336163328 }, { target := 241, numerator := 8756052331307170420194541568 }, { target := 242, numerator := 1325498380717562940735304499200 }, { target := 244, numerator := 1325498380717562940735304499200 }, { target := 260, numerator := 275907449359034958620708044800 }, { target := 406, numerator := 211459749683415459819421696 }, { target := 407, numerator := 4229194993668309196388433920 }, { target := 408, numerator := 219011883600680297670115328 }, { target := 409, numerator := 3934661770894980520211382272 }, { target := 410, numerator := 5890664455466573523541032960 }, { target := 411, numerator := 211459749683415459819421696 }, { target := 412, numerator := 5898216589383838361391726592 }, { target := 413, numerator := 5898216589383838361391726592 }, { target := 414, numerator := 4221642859751044358537740288 }, { target := 415, numerator := 219011883600680297670115328 }, { target := 416, numerator := 128746821895771711390036787200 }, { target := 418, numerator := 128746821895771711390036787200 }, { target := 487, numerator := 705181542153958380470796288 }, { target := 488, numerator := 774543661054347729369563136 }, { target := 489, numerator := 705181542153958380470796288 }, { target := 490, numerator := 774543661054347729369563136 }, { target := 492, numerator := 737444749964923796570767360 }, { target := 493, numerator := 809980299141801547053137920 }, { target := 494, numerator := 737444749964923796570767360 }, { target := 495, numerator := 809980299141801547053137920 }, { target := 498, numerator := 813267066213878820121870336 }, { target := 499, numerator := 30374261217817558014492672 }, { target := 500, numerator := 813267066213878820121870336 }, { target := 501, numerator := 30374261217817558014492672 }]

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
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 70822582050329375642228883456 }, { target := 36, numerator := 80659051779541788925871783936 }, { target := 37, numerator := 62953406266959445015314563072 }, { target := 38, numerator := 843969102766425059736560861184 }, { target := 39, numerator := 74757169942014340955686043648 }, { target := 40, numerator := 62953406266959445015314563072 }, { target := 41, numerator := 74757169942014340955686043648 }, { target := 42, numerator := 72789875996171858298957463552 }, { target := 43, numerator := 2750276936287790754106554974208 }, { target := 44, numerator := 72789875996171858298957463552 }, { target := 45, numerator := 843969102766425059736560861184 }, { target := 46, numerator := 2750276936287790754106554974208 }, { target := 47, numerator := 70822582050329375642228883456 }, { target := 48, numerator := 72789875996171858298957463552 }, { target := 49, numerator := 72789875996171858298957463552 }, { target := 50, numerator := 80659051779541788925871783936 }, { target := 86, numerator := 327570789506827034140191227904 }, { target := 89, numerator := 1196458308057842316350167449600 }, { target := 91, numerator := 327570679142880077294107361280 }, { target := 122, numerator := 7938108216748205115325808640 }, { target := 124, numerator := 7938110109340912521503047680 }, { target := 145, numerator := 253856097529337673241331761152 }, { target := 146, numerator := 289113888852856794524850061312 }, { target := 147, numerator := 225649864470522376214517121024 }, { target := 148, numerator := 3025118495557940606125870153728 }, { target := 149, numerator := 267959214058745321754739081216 }, { target := 150, numerator := 225649864470522376214517121024 }, { target := 151, numerator := 267959214058745321754739081216 }, { target := 152, numerator := 260907655794041497498035421184 }, { target := 153, numerator := 9858078454055946310871716724736 }, { target := 154, numerator := 260907655794041497498035421184 }, { target := 155, numerator := 3025118495557940606125870153728 }, { target := 156, numerator := 9858078454055946310871716724736 }, { target := 157, numerator := 253856097529337673241331761152 }, { target := 158, numerator := 260907655794041497498035421184 }, { target := 159, numerator := 260907655794041497498035421184 }, { target := 160, numerator := 289113888852856794524850061312 }, { target := 161, numerator := 12819842478712521843027608600576 }, { target := 164, numerator := 46824709445983019792253478502400 }, { target := 166, numerator := 12819838159498292009315409592320 }, { target := 216, numerator := 70843162972011948946709544960 }, { target := 217, numerator := 80682491162569164078196981760 }, { target := 218, numerator := 62971700419566176841519595520 }, { target := 219, numerator := 844214358749809058281622077440 }, { target := 220, numerator := 74778894248234834999304519680 }, { target := 221, numerator := 62971700419566176841519595520 }, { target := 222, numerator := 74778894248234834999304519680 }, { target := 223, numerator := 72811028610123391973007032320 }, { target := 224, numerator := 2751076162079797350763887329280 }, { target := 225, numerator := 72811028610123391973007032320 }, { target := 226, numerator := 844214358749809058281622077440 }, { target := 227, numerator := 2751076162079797350763887329280 }, { target := 228, numerator := 70843162972011948946709544960 }, { target := 229, numerator := 72811028610123391973007032320 }, { target := 230, numerator := 72811028610123391973007032320 }, { target := 231, numerator := 80682491162569164078196981760 }, { target := 232, numerator := 12819847180595588772278256533504 }, { target := 235, numerator := 46824726619697035665284372889600 }, { target := 237, numerator := 12819842861379774797397129953280 }, { target := 406, numerator := 327575491389893963390839160832 }, { target := 409, numerator := 1196475481771858189381061836800 }, { target := 411, numerator := 327575381024362865375827722240 }, { target := 420, numerator := 275907449359034958620708044800 }, { target := 502, numerator := 1391119440890222956695781376 }]

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
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 26751107347451632635359526912 }, { target := 17, numerator := 401266610211774489530392903680 }, { target := 18, numerator := 704445826816226326064467542016 }, { target := 19, numerator := 26751107347451632635359526912 }, { target := 20, numerator := 445851789124193877255992115200 }, { target := 21, numerator := 26751107347451632635359526912 }, { target := 22, numerator := 704445826816226326064467542016 }, { target := 23, numerator := 699987308924984387291907620864 }, { target := 24, numerator := 445851789124193877255992115200 }, { target := 25, numerator := 10802988850479217645912688951296 }, { target := 26, numerator := 691070273142500509746787778560 }, { target := 27, numerator := 401266610211774489530392903680 }, { target := 28, numerator := 704445826816226326064467542016 }, { target := 29, numerator := 26751107347451632635359526912 }, { target := 30, numerator := 691070273142500509746787778560 }, { target := 31, numerator := 26751107347451632635359526912 }, { target := 32, numerator := 704445826816226326064467542016 }, { target := 33, numerator := 704445826816226326064467542016 }, { target := 34, numerator := 26751107347451632635359526912 }, { target := 35, numerator := 994283971427704441322761879552 }, { target := 37, numerator := 38782428324871943728664372314112 }, { target := 40, numerator := 38782414099612798988583566311424 }, { target := 47, numerator := 994288713180752688016363880448 }, { target := 126, numerator := 26751113725413396120436998144 }, { target := 127, numerator := 401266705881200941806554972160 }, { target := 128, numerator := 704445994769219431171507617792 }, { target := 129, numerator := 26751113725413396120436998144 }, { target := 130, numerator := 445851895423556602007283302400 }, { target := 131, numerator := 26751113725413396120436998144 }, { target := 132, numerator := 704445994769219431171507617792 }, { target := 133, numerator := 699987475814983865151434784768 }, { target := 134, numerator := 445851895423556602007283302400 }, { target := 135, numerator := 10802991426112776466636474417152 }, { target := 136, numerator := 691070437906512733111289118720 }, { target := 137, numerator := 401266705881200941806554972160 }, { target := 138, numerator := 704445994769219431171507617792 }, { target := 139, numerator := 26751113725413396120436998144 }, { target := 140, numerator := 691070437906512733111289118720 }, { target := 141, numerator := 26751113725413396120436998144 }, { target := 142, numerator := 704445994769219431171507617792 }, { target := 143, numerator := 704445994769219431171507617792 }, { target := 144, numerator := 26751113725413396120436998144 }, { target := 145, numerator := 3693517175509282926349537771520 }, { target := 147, numerator := 144067056537366338068381035397120 }, { target := 150, numerator := 144067003694073589696527849226240 }, { target := 157, numerator := 3693534789940199050300599828480 }, { target := 197, numerator := 2557034208440585664260556718080 }, { target := 199, numerator := 2557034818085121030045522984960 }, { target := 215, numerator := 12127405472594912741097996288 }, { target := 216, numerator := 994074675722242736341179695104 }, { target := 218, numerator := 38774264665465751360842942644224 }, { target := 221, numerator := 38774250443201008354704226254848 }, { target := 228, numerator := 994079416477157071720751824896 }, { target := 242, numerator := 27195134112152950668846667137024 }, { target := 244, numerator := 27195140595978957097077401714688 }, { target := 260, numerator := 2127032982412542202284588662784 }, { target := 416, numerator := 2557041915341766973197561888768 }, { target := 418, numerator := 2557042524988139807630495318016 }, { target := 420, numerator := 2127033237420332277245430202368 }, { target := 498, numerator := 7938108216748205115325808640 }, { target := 500, numerator := 7938110109340912521503047680 }, { target := 502, numerator := 12127150464804837780256456704 }]

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
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot13.Left4.expected,
    Slot13.Left5.expected,
    Slot13.Left6.expected,
    Slot13.Left7.expected,
    Slot13.Left8.expected,
    Slot13.Left9.expected,
    Slot13.Left10.expected,
    Slot13.Left11.expected,
    Slot13.Left12.expected,
    Slot13.Left13.expected,
    Slot13.Left14.expected,
    Slot13.Left15.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 49208116561593865927240187904 }, { target := 1, numerator := 36906087421195399445430140928 }, { target := 2, numerator := 38956425611261810525731815424 }, { target := 3, numerator := 50233285656627071467391025152 }, { target := 4, numerator := 672510926341782834338949234688 }, { target := 5, numerator := 1175868952003086754553010323456 }, { target := 6, numerator := 35880918326162193905279303680 }, { target := 7, numerator := 672510926341782834338949234688 }, { target := 8, numerator := 37931256516228604985580978176 }, { target := 9, numerator := 38956425611261810525731815424 }, { target := 10, numerator := 38956425611261810525731815424 }, { target := 11, numerator := 37931256516228604985580978176 }, { target := 12, numerator := 1175868952003086754553010323456 }, { target := 13, numerator := 37931256516228604985580978176 }, { target := 14, numerator := 49208116561593865927240187904 }, { target := 15, numerator := 50233285656627071467391025152 }, { target := 16, numerator := 44244763546756616974327873536 }, { target := 17, numerator := 5229446989515145167540622196736 }, { target := 19, numerator := 49626409510096877012272646455296 }, { target := 27, numerator := 5229450576152916467525785485312 }, { target := 34, numerator := 44244763546756616974327873536 }, { target := 86, numerator := 1627351294095516969687098327040 }, { target := 89, numerator := 5853534210814260958360365957120 }, { target := 91, numerator := 1627351836988768263498073374720 }, { target := 122, numerator := 44186508426879386405566414848 }, { target := 124, numerator := 44186497891996087665718984704 }, { target := 126, numerator := 44244752997984216983669833728 }, { target := 127, numerator := 5229445742717973070201202147328 }, { target := 129, numerator := 49626397678240246169929890398208 }, { target := 137, numerator := 5229449329354889249207118462976 }, { target := 144, numerator := 44244752997984216983669833728 }, { target := 161, numerator := 63686327881350664629532797960192 }, { target := 164, numerator := 229077827490110077539268612325376 }, { target := 166, numerator := 63686349127456365296264838905856 }, { target := 197, numerator := 5222561608357126543225229672448 }, { target := 199, numerator := 5222560363201557042459001749504 }, { target := 215, numerator := 51065026620521936339588874240 }, { target := 232, numerator := 63686327881350664629532797960192 }, { target := 235, numerator := 229077827490110077539268612325376 }, { target := 237, numerator := 63686349127456365296264838905856 }, { target := 242, numerator := 49561068615416038464527718678528 }, { target := 244, numerator := 49561056799137889032115631161344 }, { target := 260, numerator := 38298769965391452254691655680 }, { target := 265, numerator := 40426479407913199602174525440 }, { target := 355, numerator := 52128881341782810013330309120 }, { target := 400, numerator := 697888697147133129974381281280 }, { target := 405, numerator := 1220241365286222103781425807360 }, { target := 406, numerator := 1627351294095516969687098327040 }, { target := 409, numerator := 5853534210814260958360365957120 }, { target := 411, numerator := 1627351836988768263498073374720 }, { target := 416, numerator := 5222565190272530797390794326016 }, { target := 418, numerator := 5222563945116107301545226272768 }, { target := 420, numerator := 37234915244130578580950220800 }, { target := 425, numerator := 697888697147133129974381281280 }, { target := 426, numerator := 39362624686652325928433090560 }, { target := 471, numerator := 40426479407913199602174525440 }, { target := 476, numerator := 40426479407913199602174525440 }, { target := 491, numerator := 39362624686652325928433090560 }, { target := 496, numerator := 1220241365286222103781425807360 }, { target := 497, numerator := 39362624686652325928433090560 }, { target := 498, numerator := 44186508426879386405566414848 }, { target := 500, numerator := 44186497891996087665718984704 }, { target := 502, numerator := 51065026620521936339588874240 }, { target := 503, numerator := 52128881341782810013330309120 }]

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
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected,
    Slot18.Left13.expected,
    Slot18.Left14.expected,
    Slot18.Left15.expected,
    Slot18.Left16.expected,
    Slot18.Left17.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 1635816060254661401258942791680 }, { target := 37, numerator := 64017596166819328684822955556864 }, { target := 40, numerator := 64017596166819328684822955556864 }, { target := 47, numerator := 1635816060254661401258942791680 }, { target := 86, numerator := 999135827684235588823116939264 }, { target := 89, numerator := 3711540612406156387823533424640 }, { target := 91, numerator := 998925510668255771652708630528 }, { target := 122, numerator := 26983221077147525326338785280 }, { target := 124, numerator := 26983227510449521032544911360 }, { target := 145, numerator := 5883981722964140079080055767040 }, { target := 147, numerator := 230269389661710129958198488072192 }, { target := 150, numerator := 230269389661710129958198488072192 }, { target := 157, numerator := 5883981722964140079080055767040 }, { target := 161, numerator := 38971676842316421669480441053184 }, { target := 164, numerator := 144770067618413089108101263523840 }, { target := 166, numerator := 38963473346301066982680447418368 }, { target := 197, numerator := 404748316157212879895081779200 }, { target := 199, numerator := 404748412656742815488173670400 }, { target := 211, numerator := 710558155031551500260254679040 }, { target := 213, numerator := 710558324441837387190349332480 }, { target := 216, numerator := 1635816605971804769420039946240 }, { target := 218, numerator := 64017617523437932866076359524352 }, { target := 221, numerator := 64017617523437932866076359524352 }, { target := 228, numerator := 1635816605971804769420039946240 }, { target := 232, numerator := 38971662547641582253079965728768 }, { target := 235, numerator := 144770014517258333598846214471680 }, { target := 237, numerator := 38963459054635241229213065281536 }, { target := 242, numerator := 26983221077147525326338785280 }, { target := 244, numerator := 26983227510449521032544911360 }, { target := 256, numerator := 449720351285792088772313088000 }, { target := 258, numerator := 449720458507492017209081856000 }, { target := 261, numerator := 26983221077147525326338785280 }, { target := 263, numerator := 26983227510449521032544911360 }, { target := 337, numerator := 710558155031551500260254679040 }, { target := 339, numerator := 710558324441837387190349332480 }, { target := 351, numerator := 706060951518693579372531548160 }, { target := 353, numerator := 706061119856762467018258513920 }, { target := 382, numerator := 449720351285792088772313088000 }, { target := 384, numerator := 449720458507492017209081856000 }, { target := 396, numerator := 10896724111654742310953146122240 }, { target := 398, numerator := 10896726709636531576976053370880 }, { target := 401, numerator := 697066544492977737597085286400 }, { target := 403, numerator := 697066710686612626674076876800 }, { target := 406, numerator := 999140592575848727623275380736 }, { target := 409, numerator := 3711558312791074890908549775360 }, { target := 411, numerator := 998930274556864356141836009472 }, { target := 416, numerator := 404748316157212879895081779200 }, { target := 418, numerator := 404748412656742815488173670400 }, { target := 421, numerator := 710558155031551500260254679040 }, { target := 423, numerator := 710558324441837387190349332480 }, { target := 453, numerator := 26983221077147525326338785280 }, { target := 455, numerator := 26983227510449521032544911360 }, { target := 467, numerator := 697066544492977737597085286400 }, { target := 469, numerator := 697066710686612626674076876800 }, { target := 472, numerator := 26983221077147525326338785280 }, { target := 474, numerator := 26983227510449521032544911360 }, { target := 487, numerator := 710558155031551500260254679040 }, { target := 489, numerator := 710558324441837387190349332480 }, { target := 492, numerator := 710558155031551500260254679040 }, { target := 494, numerator := 710558324441837387190349332480 }, { target := 498, numerator := 26983221077147525326338785280 }, { target := 500, numerator := 26983227510449521032544911360 }]

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
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected,
    Slot22.Left7.expected,
    Slot22.Left8.expected,
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 12127405472594912741097996288 }, { target := 1, numerator := 2127032982412542202284588662784 }, { target := 6, numerator := 2127033237420332277245430202368 }, { target := 14, numerator := 12127150464804837780256456704 }, { target := 16, numerator := 7792187109822686638941143040 }, { target := 17, numerator := 2510029903138369016020472954880 }, { target := 19, numerator := 26695223558620727310963456344064 }, { target := 27, numerator := 2510037468368572727366724354048 }, { target := 34, numerator := 7792187109822686638941143040 }, { target := 35, numerator := 323729341015808806660935254016 }, { target := 37, numerator := 12669503174591159646574193147904 }, { target := 40, numerator := 12669507821334872912475419836416 }, { target := 47, numerator := 323733987759522072562161942528 }, { target := 86, numerator := 72194146139332233269103034368 }, { target := 89, numerator := 258772324770222733814667411456 }, { target := 91, numerator := 72215125635202321197438074880 }, { target := 112, numerator := 82221110880906154556478455808 }, { target := 115, numerator := 294712925432753669066704551936 }, { target := 117, numerator := 82245004195647088030415585280 }, { target := 126, numerator := 7792188967625086923681300480 }, { target := 127, numerator := 2510030501576203364052039106560 }, { target := 129, numerator := 26695229923258755679851714183168 }, { target := 137, numerator := 2510038066808210767049052389376 }, { target := 144, numerator := 7792188967625086923681300480 }, { target := 145, numerator := 1182427347089146937373779558400 }, { target := 147, numerator := 46275592384249743440745175449600 }, { target := 150, numerator := 46275609356566260193729865318400 }, { target := 157, numerator := 1182444319405663690358469427200 }, { target := 161, numerator := 64172574346073096239202697216 }, { target := 164, numerator := 230019844240197985613037699072 }, { target := 166, numerator := 64191222786846507731056066560 }, { target := 187, numerator := 860313574827042446456811159552 }, { target := 190, numerator := 3083703536845154244624786653184 }, { target := 192, numerator := 860563580486160994269470392320 }, { target := 201, numerator := 76204932035961801784053202944 }, { target := 204, numerator := 273148565035235107915482267648 }, { target := 206, numerator := 76227077059380227930629079040 }, { target := 216, numerator := 323729231946108562528398213120 }, { target := 218, numerator := 12669498906028695834366081761280 }, { target := 221, numerator := 12669503552770843536446843781120 }, { target := 228, numerator := 323733878688256264609160232960 }, { target := 232, numerator := 64172574346073096239202697216 }, { target := 235, numerator := 230019844240197985613037699072 }, { target := 237, numerator := 64191222786846507731056066560 }, { target := 246, numerator := 76204932035961801784053202944 }, { target := 249, numerator := 273148565035235107915482267648 }, { target := 251, numerator := 76227077059380227930629079040 }, { target := 301, numerator := 74199539087647017526578118656 }, { target := 304, numerator := 265960444902728920865074839552 }, { target := 306, numerator := 74221101347291274564033576960 }, { target := 327, numerator := 2803539341744068391950167834624 }, { target := 330, numerator := 10048991945243649496469584478208 }, { target := 332, numerator := 2804354045500356806500511907840 }, { target := 341, numerator := 74199539087647017526578118656 }, { target := 344, numerator := 265960444902728920865074839552 }, { target := 346, numerator := 74221101347291274564033576960 }, { target := 372, numerator := 860313574827042446456811159552 }, { target := 375, numerator := 3083703536845154244624786653184 }, { target := 377, numerator := 860563580486160994269470392320 }, { target := 386, numerator := 2803539341744068391950167834624 }, { target := 389, numerator := 10048991945243649496469584478208 }, { target := 391, numerator := 2804354045500356806500511907840 }]

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
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected,
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected,
    Slot25.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1391119440890222956695781376 }, { target := 1, numerator := 275907449359034958620708044800 }, { target := 6, numerator := 275907449359034958620708044800 }, { target := 14, numerator := 1391119440890222956695781376 }, { target := 16, numerator := 785612888090194177750466560 }, { target := 17, numerator := 128746821895771711390036787200 }, { target := 19, numerator := 1325498380717562940735304499200 }, { target := 27, numerator := 128746821895771711390036787200 }, { target := 34, numerator := 785612888090194177750466560 }, { target := 35, numerator := 204851632505808726700064768 }, { target := 37, numerator := 8189930259634042261202796544 }, { target := 40, numerator := 8189928258162310263716446208 }, { target := 47, numerator := 204851632505808726700064768 }, { target := 70, numerator := 4097032650116174534001295360 }, { target := 72, numerator := 163798605192680845224055930880 }, { target := 75, numerator := 163798565163246205274328924160 }, { target := 82, numerator := 4097032650116174534001295360 }, { target := 96, numerator := 212167762238159038367924224 }, { target := 98, numerator := 8482427768906686627674324992 }, { target := 101, numerator := 8482425695953821344563462144 }, { target := 108, numerator := 212167762238159038367924224 }, { target := 126, numerator := 785612888090194177750466560 }, { target := 127, numerator := 128746821895771711390036787200 }, { target := 129, numerator := 1325498380717562940735304499200 }, { target := 137, numerator := 128746821895771711390036787200 }, { target := 144, numerator := 785612888090194177750466560 }, { target := 145, numerator := 3811703590554512378954776576 }, { target := 147, numerator := 152391202331047714931666321408 }, { target := 150, numerator := 152391165089377273121295302656 }, { target := 157, numerator := 3811703590554512378954776576 }, { target := 171, numerator := 5706581191233243100930375680 }, { target := 173, numerator := 228148057232662605847792189440 }, { target := 176, numerator := 228148001477378643060672430080 }, { target := 183, numerator := 5706581191233243100930375680 }, { target := 216, numerator := 204851632505808726700064768 }, { target := 218, numerator := 8189930259634042261202796544 }, { target := 221, numerator := 8189928258162310263716446208 }, { target := 228, numerator := 204851632505808726700064768 }, { target := 285, numerator := 5713897320965593412598235136 }, { target := 287, numerator := 228440554741935250214263717888 }, { target := 290, numerator := 228440498915170154141519446016 }, { target := 297, numerator := 5713897320965593412598235136 }, { target := 311, numerator := 5713897320965593412598235136 }, { target := 313, numerator := 228440554741935250214263717888 }, { target := 316, numerator := 228440498915170154141519446016 }, { target := 323, numerator := 5713897320965593412598235136 }, { target := 356, numerator := 4089716520383824222333435904 }, { target := 358, numerator := 163506107683408200857584402432 }, { target := 361, numerator := 163506067725454694193481908224 }, { target := 368, numerator := 4089716520383824222333435904 }, { target := 406, numerator := 72194146139332233269103034368 }, { target := 409, numerator := 258772324770222733814667411456 }, { target := 411, numerator := 72215125635202321197438074880 }, { target := 443, numerator := 74199539087647017526578118656 }, { target := 446, numerator := 265960444902728920865074839552 }, { target := 448, numerator := 74221101347291274564033576960 }, { target := 457, numerator := 74199539087647017526578118656 }, { target := 460, numerator := 265960444902728920865074839552 }, { target := 462, numerator := 74221101347291274564033576960 }, { target := 477, numerator := 82221110880906154556478455808 }, { target := 480, numerator := 294712925432753669066704551936 }, { target := 482, numerator := 82245004195647088030415585280 }]

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
    Slot25.Left9.expected,
    Slot27.Left0.expected,
    Slot27.Left1.expected,
    Slot27.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 27654178123684642371403776 }, { target := 17, numerator := 400985582793427314385354752 }, { target := 18, numerator := 709790571841239154199363584 }, { target := 19, numerator := 23045148436403868642836480 }, { target := 20, numerator := 442466849978954277942460416 }, { target := 21, numerator := 23045148436403868642836480 }, { target := 22, numerator := 705181542153958380470796288 }, { target := 23, numerator := 737444749964923796570767360 }, { target := 24, numerator := 442466849978954277942460416 }, { target := 25, numerator := 11296731763525176408718442496 }, { target := 26, numerator := 723617660903081475385065472 }, { target := 27, numerator := 400985582793427314385354752 }, { target := 28, numerator := 705181542153958380470796288 }, { target := 29, numerator := 23045148436403868642836480 }, { target := 30, numerator := 723617660903081475385065472 }, { target := 31, numerator := 23045148436403868642836480 }, { target := 32, numerator := 705181542153958380470796288 }, { target := 33, numerator := 737444749964923796570767360 }, { target := 34, numerator := 27654178123684642371403776 }, { target := 51, numerator := 30374261217817558014492672 }, { target := 52, numerator := 440426787658354591210143744 }, { target := 53, numerator := 779606037923983989038645248 }, { target := 54, numerator := 25311884348181298345410560 }, { target := 55, numerator := 485988179485080928231882752 }, { target := 56, numerator := 25311884348181298345410560 }, { target := 57, numerator := 774543661054347729369563136 }, { target := 58, numerator := 809980299141801547053137920 }, { target := 59, numerator := 485988179485080928231882752 }, { target := 60, numerator := 12407885707478472448920256512 }, { target := 61, numerator := 794793168532892768045891584 }, { target := 62, numerator := 440426787658354591210143744 }, { target := 63, numerator := 774543661054347729369563136 }, { target := 64, numerator := 25311884348181298345410560 }, { target := 65, numerator := 794793168532892768045891584 }, { target := 66, numerator := 25311884348181298345410560 }, { target := 67, numerator := 774543661054347729369563136 }, { target := 68, numerator := 809980299141801547053137920 }, { target := 69, numerator := 30374261217817558014492672 }, { target := 126, numerator := 27654178123684642371403776 }, { target := 127, numerator := 400985582793427314385354752 }, { target := 128, numerator := 709790571841239154199363584 }, { target := 129, numerator := 23045148436403868642836480 }, { target := 130, numerator := 442466849978954277942460416 }, { target := 131, numerator := 23045148436403868642836480 }, { target := 132, numerator := 705181542153958380470796288 }, { target := 133, numerator := 737444749964923796570767360 }, { target := 134, numerator := 442466849978954277942460416 }, { target := 135, numerator := 11296731763525176408718442496 }, { target := 136, numerator := 723617660903081475385065472 }, { target := 137, numerator := 400985582793427314385354752 }, { target := 138, numerator := 705181542153958380470796288 }, { target := 139, numerator := 23045148436403868642836480 }, { target := 140, numerator := 723617660903081475385065472 }, { target := 141, numerator := 23045148436403868642836480 }, { target := 142, numerator := 705181542153958380470796288 }, { target := 143, numerator := 737444749964923796570767360 }, { target := 144, numerator := 27654178123684642371403776 }, { target := 427, numerator := 212167762238159038367924224 }, { target := 429, numerator := 8482427768906686627674324992 }, { target := 432, numerator := 8482425695953821344563462144 }, { target := 439, numerator := 212167762238159038367924224 }]

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
    Slot27.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 266, numerator := 30374261217817558014492672 }, { target := 267, numerator := 440426787658354591210143744 }, { target := 268, numerator := 779606037923983989038645248 }, { target := 269, numerator := 25311884348181298345410560 }, { target := 270, numerator := 485988179485080928231882752 }, { target := 271, numerator := 25311884348181298345410560 }, { target := 272, numerator := 774543661054347729369563136 }, { target := 273, numerator := 809980299141801547053137920 }, { target := 274, numerator := 485988179485080928231882752 }, { target := 275, numerator := 12407885707478472448920256512 }, { target := 276, numerator := 794793168532892768045891584 }, { target := 277, numerator := 440426787658354591210143744 }, { target := 278, numerator := 774543661054347729369563136 }, { target := 279, numerator := 25311884348181298345410560 }, { target := 280, numerator := 794793168532892768045891584 }, { target := 281, numerator := 25311884348181298345410560 }, { target := 282, numerator := 774543661054347729369563136 }, { target := 283, numerator := 809980299141801547053137920 }, { target := 284, numerator := 30374261217817558014492672 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent3
