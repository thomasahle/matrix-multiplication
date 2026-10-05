import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk12Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent3

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
  [{ target := 19, numerator := 166265079128874468683808768 }, { target := 20, numerator := 189357451230107033778782208 }, { target := 21, numerator := 147791181447888416607830016 }, { target := 22, numerator := 1981325526285754085148721152 }, { target := 23, numerator := 175502027969367494721798144 }, { target := 24, numerator := 147791181447888416607830016 }, { target := 25, numerator := 175502027969367494721798144 }, { target := 26, numerator := 170883553549120981702803456 }, { target := 27, numerator := 6456627239504625200554573824 }, { target := 28, numerator := 170883553549120981702803456 }, { target := 29, numerator := 1981325526285754085148721152 }, { target := 30, numerator := 6456627239504625200554573824 }, { target := 31, numerator := 166265079128874468683808768 }, { target := 32, numerator := 170883553549120981702803456 }, { target := 33, numerator := 170883553549120981702803456 }, { target := 34, numerator := 189357451230107033778782208 }, { target := 45, numerator := 181905556920138733631569920 }, { target := 46, numerator := 207170217603491335524843520 }, { target := 47, numerator := 161693828373456652116951040 }, { target := 48, numerator := 2167707886631653242442874880 }, { target := 49, numerator := 192011421193479774388879360 }, { target := 50, numerator := 161693828373456652116951040 }, { target := 51, numerator := 192011421193479774388879360 }, { target := 52, numerator := 186958489056809254010224640 }, { target := 53, numerator := 7063999127065387489359298560 }, { target := 54, numerator := 186958489056809254010224640 }, { target := 55, numerator := 2167707886631653242442874880 }, { target := 56, numerator := 7063999127065387489359298560 }, { target := 57, numerator := 181905556920138733631569920 }, { target := 58, numerator := 186958489056809254010224640 }, { target := 59, numerator := 186958489056809254010224640 }, { target := 60, numerator := 207170217603491335524843520 }, { target := 90, numerator := 166265079128874468683808768 }, { target := 91, numerator := 189357451230107033778782208 }, { target := 92, numerator := 147791181447888416607830016 }, { target := 93, numerator := 1981325526285754085148721152 }, { target := 94, numerator := 175502027969367494721798144 }, { target := 95, numerator := 147791181447888416607830016 }, { target := 96, numerator := 175502027969367494721798144 }, { target := 97, numerator := 170883553549120981702803456 }, { target := 98, numerator := 6456627239504625200554573824 }, { target := 99, numerator := 170883553549120981702803456 }, { target := 100, numerator := 1981325526285754085148721152 }, { target := 101, numerator := 6456627239504625200554573824 }, { target := 102, numerator := 166265079128874468683808768 }, { target := 103, numerator := 170883553549120981702803456 }, { target := 104, numerator := 170883553549120981702803456 }, { target := 105, numerator := 189357451230107033778782208 }, { target := 161, numerator := 181905556920138733631569920 }, { target := 162, numerator := 207170217603491335524843520 }, { target := 163, numerator := 161693828373456652116951040 }, { target := 164, numerator := 2167707886631653242442874880 }, { target := 165, numerator := 192011421193479774388879360 }, { target := 166, numerator := 161693828373456652116951040 }, { target := 167, numerator := 192011421193479774388879360 }, { target := 168, numerator := 186958489056809254010224640 }, { target := 169, numerator := 7063999127065387489359298560 }, { target := 170, numerator := 186958489056809254010224640 }, { target := 171, numerator := 2167707886631653242442874880 }, { target := 172, numerator := 7063999127065387489359298560 }, { target := 173, numerator := 181905556920138733631569920 }, { target := 174, numerator := 186958489056809254010224640 }, { target := 175, numerator := 186958489056809254010224640 }, { target := 176, numerator := 207170217603491335524843520 }]

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
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 574892926631110765789052928 }, { target := 38, numerator := 2099806943552714463982387200 }, { target := 40, numerator := 574892732940297991838760960 }, { target := 61, numerator := 12000889843424437235846479872 }, { target := 64, numerator := 43833469946662914435632332800 }, { target := 66, numerator := 12000885800128720579634135040 }, { target := 71, numerator := 16789559781336237980833021952 }, { target := 73, numerator := 16789563784279701975805722624 }, { target := 75, numerator := 622800670517036662938140672 }, { target := 78, numerator := 2274790855515440669314252800 }, { target := 80, numerator := 622800460685322824491991040 }, { target := 85, numerator := 18955954591831236429972766720 }, { target := 87, numerator := 18955959111283534488812912640 }, { target := 89, numerator := 7775810871761294851710124032 }, { target := 106, numerator := 12911136977257029281679147008 }, { target := 109, numerator := 47158164273954712336937779200 }, { target := 111, numerator := 12911132627284192400045506560 }, { target := 116, numerator := 16247961078712488368548085760 }, { target := 118, numerator := 16247964952528743847553925120 }, { target := 120, numerator := 19330774657971099499656904704 }, { target := 123, numerator := 70606008476960023851407769600 }, { target := 125, numerator := 19330768145117519975578337280 }, { target := 130, numerator := 213931487536381096852549795840 }, { target := 132, numerator := 213931538541628460659460014080 }, { target := 134, numerator := 112749257640538775349796798464 }, { target := 135, numerator := 18955954591831236429972766720 }, { target := 137, numerator := 18955959111283534488812912640 }, { target := 140, numerator := 598846798574073714363596800 }, { target := 143, numerator := 2187298899534077566648320000 }, { target := 145, numerator := 598846596812810408165376000 }, { target := 150, numerator := 16247961078712488368548085760 }, { target := 152, numerator := 16247964952528743847553925120 }, { target := 155, numerator := 18955954591831236429972766720 }, { target := 157, numerator := 18955959111283534488812912640 }, { target := 177, numerator := 19330774657971099499656904704 }, { target := 180, numerator := 70606008476960023851407769600 }, { target := 182, numerator := 19330768145117519975578337280 }, { target := 187, numerator := 18955954591831236429972766720 }, { target := 189, numerator := 18955959111283534488812912640 }, { target := 191, numerator := 20145206304031839751191396352 }, { target := 194, numerator := 73580734980326369342049484800 }, { target := 196, numerator := 20145199516782942130683248640 }, { target := 201, numerator := 785859717507060687425442414592 }, { target := 203, numerator := 785859904870640244093358178304 }, { target := 206, numerator := 19497553294454986042257702912 }, { target := 208, numerator := 19497557943034492617064710144 }, { target := 211, numerator := 12000889843424437235846479872 }, { target := 214, numerator := 43833469946662914435632332800 }, { target := 216, numerator := 12000885800128720579634135040 }, { target := 221, numerator := 213931487536381096852549795840 }, { target := 223, numerator := 213931538541628460659460014080 }, { target := 226, numerator := 785859717507060687425442414592 }, { target := 228, numerator := 785859904870640244093358178304 }, { target := 232, numerator := 16789559781336237980833021952 }, { target := 234, numerator := 16789563784279701975805722624 }, { target := 238, numerator := 598846798574073714363596800 }, { target := 241, numerator := 2187298899534077566648320000 }, { target := 243, numerator := 598846596812810408165376000 }, { target := 248, numerator := 18955954591831236429972766720 }, { target := 250, numerator := 18955959111283534488812912640 }, { target := 253, numerator := 19497553294454986042257702912 }, { target := 255, numerator := 19497557943034492617064710144 }, { target := 259, numerator := 18955954591831236429972766720 }, { target := 261, numerator := 18955959111283534488812912640 }]

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
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 1740853180245066011576893440 }, { target := 2, numerator := 3056164471985782553657212928 }, { target := 3, numerator := 116056878683004400771792896 }, { target := 4, numerator := 1934281311383406679529881600 }, { target := 5, numerator := 116056878683004400771792896 }, { target := 6, numerator := 3056164471985782553657212928 }, { target := 7, numerator := 3036821658871948486861914112 }, { target := 8, numerator := 1934281311383406679529881600 }, { target := 9, numerator := 46867636174819943845009031168 }, { target := 10, numerator := 2998136032644280353271316480 }, { target := 11, numerator := 1740853180245066011576893440 }, { target := 12, numerator := 3056164471985782553657212928 }, { target := 13, numerator := 116056878683004400771792896 }, { target := 14, numerator := 2998136032644280353271316480 }, { target := 15, numerator := 116056878683004400771792896 }, { target := 16, numerator := 3056164471985782553657212928 }, { target := 17, numerator := 3056164471985782553657212928 }, { target := 18, numerator := 116056878683004400771792896 }, { target := 19, numerator := 18814158353176258622561189888 }, { target := 21, numerator := 733853475257298123039365398528 }, { target := 24, numerator := 733853206082408599469588217856 }, { target := 31, numerator := 18814248078139433145820250112 }, { target := 35, numerator := 2563809617611272083607323148288 }, { target := 38, numerator := 9221946952175009160509012312064 }, { target := 40, numerator := 2563810472912118344297987702784 }, { target := 71, numerator := 1319508995322223606152214609920 }, { target := 73, numerator := 1319508680726801332394168156160 }, { target := 89, numerator := 25964505951380917574652919808 }, { target := 90, numerator := 18814158353176258622561189888 }, { target := 92, numerator := 733853475257298123039365398528 }, { target := 95, numerator := 733853206082408599469588217856 }, { target := 102, numerator := 18814248078139433145820250112 }, { target := 106, numerator := 9339344821998254425730782855168 }, { target := 109, numerator := 33593345592011476370213205704704 }, { target := 111, numerator := 9339347937654532062274465562624 }, { target := 116, numerator := 52753724812724453462259384975360 }, { target := 118, numerator := 52753712235257840648513157857280 }, { target := 134, numerator := 4255082463655255061440715816960 }, { target := 139, numerator := 199579145708539901193893183488 }, { target := 140, numerator := 2563811342207984889535481774080 }, { target := 143, numerator := 9221953155498099199355115274240 }, { target := 145, numerator := 2563812197509406485078542909440 }, { target := 150, numerator := 52753711920662418374755111403520 }, { target := 152, numerator := 52753699343198879267754564648960 }, { target := 154, numerator := 43814201325108589603678238801920 }, { target := 159, numerator := 124412973948180717627361984512 }, { target := 160, numerator := 6479842393134412376425103360 }, { target := 205, numerator := 198283177229913018718608162816 }, { target := 210, numerator := 207354956580301196045603307520 }, { target := 225, numerator := 124412973948180717627361984512 }, { target := 230, numerator := 3176418741114488946923585667072 }, { target := 231, numerator := 203467051144420548619748245504 }, { target := 232, numerator := 1319508995322223606152214609920 }, { target := 234, numerator := 1319508680726801332394168156160 }, { target := 236, numerator := 112749257640538775349796798464 }, { target := 237, numerator := 198283177229913018718608162816 }, { target := 252, numerator := 6479842393134412376425103360 }, { target := 257, numerator := 203467051144420548619748245504 }, { target := 258, numerator := 6479842393134412376425103360 }, { target := 263, numerator := 198283177229913018718608162816 }, { target := 264, numerator := 207354956580301196045603307520 }, { target := 265, numerator := 7775810871761294851710124032 }]

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
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 7935049069563659288315953152 }, { target := 1, numerator := 2235293224587595853069279035392 }, { target := 3, numerator := 23560306678376001852423008157696 }, { target := 11, numerator := 2235299528946850484045639319552 }, { target := 18, numerator := 7935049069563659288315953152 }, { target := 19, numerator := 2938294355889226443142119555072 }, { target := 21, numerator := 114992771850929266544781262061568 }, { target := 24, numerator := 114992806411564251477045644623872 }, { target := 31, numerator := 2938328916524211375406502117376 }, { target := 35, numerator := 47441701333112838031703424368640 }, { target := 38, numerator := 173140001912829851063541194293248 }, { target := 40, numerator := 47443608822397755591292555886592 }, { target := 71, numerator := 2928424337925343950541443563520 }, { target := 73, numerator := 2928425287677945781158810746880 }, { target := 89, numerator := 6303792570653032002858516480 }, { target := 90, numerator := 2938295309406970418430228824064 }, { target := 92, numerator := 114992809167461259846629736841216 }, { target := 95, numerator := 114992843728104484677362347147264 }, { target := 102, numerator := 2938329870050195249162839130112 }, { target := 106, numerator := 173143885309045873214291057836032 }, { target := 109, numerator := 631692590641360655724795710668800 }, { target := 111, numerator := 173151621642799954890005554397184 }, { target := 116, numerator := 114606501231049375393642069360640 }, { target := 118, numerator := 114606538400230807032230683082752 }, { target := 134, numerator := 2030586231120501187445061058560 }, { target := 140, numerator := 47443593894357170596508847833088 }, { target := 143, numerator := 173147683610083991225130943512576 }, { target := 145, numerator := 47445498481603401075355602124800 }, { target := 150, numerator := 93960379806254358289575124664320 }, { target := 152, numerator := 93960402208157274054816788643840 }, { target := 154, numerator := 21596138487052375142352203808768 }, { target := 232, numerator := 2400895826028473342111577538560 }, { target := 234, numerator := 2400896398446712992264062238720 }, { target := 236, numerator := 6285674814962718047945973825536 }, { target := 265, numerator := 32268298522033949577511436288 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected,
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected,
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot23.Left10.expected,
    Slot23.Left11.expected,
    Slot23.Left12.expected,
    Slot23.Left13.expected,
    Slot23.Left14.expected,
    Slot23.Left15.expected,
    Slot23.Left16.expected,
    Slot23.Left17.expected,
    Slot23.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 25885944662571898156877873152 }, { target := 1, numerator := 4242207781465677890301712138240 }, { target := 3, numerator := 43675171644643698897228283248640 }, { target := 11, numerator := 4242207781465677890301712138240 }, { target := 18, numerator := 25885944662571898156877873152 }, { target := 19, numerator := 1320959005207193082642491768832 }, { target := 21, numerator := 52811695938892282531998131552256 }, { target := 24, numerator := 52811683032663146307035062075392 }, { target := 31, numerator := 1320959005207193082642491768832 }, { target := 35, numerator := 2566318237589365304824160059392 }, { target := 38, numerator := 9348483124172421015188445069312 }, { target := 40, numerator := 2566319963873550432480232734720 }, { target := 71, numerator := 17823939492482771326636916736 }, { target := 73, numerator := 17823939492482771326636916736 }, { target := 89, numerator := 1630689814932682928031793152 }, { target := 90, numerator := 1320958690266061553638557351936 }, { target := 92, numerator := 52811683347604277836038996492288 }, { target := 95, numerator := 52811670441378218695521327906816 }, { target := 102, numerator := 1320958690266061553638557351936 }, { target := 106, numerator := 9230970383635062985519295102976 }, { target := 109, numerator := 33626215793177828108344529780736 }, { target := 111, numerator := 9230976593027940783698906972160 }, { target := 116, numerator := 695229608138492958668872482816 }, { target := 118, numerator := 695229608138492958668872482816 }, { target := 134, numerator := 180760741947895542760284880896 }, { target := 139, numerator := 3056164471985782553657212928 }, { target := 140, numerator := 2566319093727100847570294931456 }, { target := 143, numerator := 9348486242877286007540878934016 }, { target := 145, numerator := 2566320820011861873028717608960 }, { target := 150, numerator := 21341385239391020601725830561792 }, { target := 152, numerator := 21341400006677752729642964353024 }, { target := 154, numerator := 1698979116060226916670202970112 }, { target := 159, numerator := 1934281311383406679529881600 }, { target := 160, numerator := 116056878683004400771792896 }, { target := 205, numerator := 3056164471985782553657212928 }, { target := 210, numerator := 3036821658871948486861914112 }, { target := 225, numerator := 1934281311383406679529881600 }, { target := 230, numerator := 46867636174819943845009031168 }, { target := 231, numerator := 2998136032644280353271316480 }, { target := 232, numerator := 545386997857250685360971710464 }, { target := 234, numerator := 545387375199829120396038242304 }, { target := 236, numerator := 180760864729424097371060436992 }, { target := 237, numerator := 3056164471985782553657212928 }, { target := 252, numerator := 116056878683004400771792896 }, { target := 257, numerator := 2998136032644280353271316480 }, { target := 258, numerator := 116056878683004400771792896 }, { target := 263, numerator := 3056164471985782553657212928 }, { target := 264, numerator := 3056164471985782553657212928 }, { target := 265, numerator := 1630689814932682928031793152 }]

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
    Slot24.Left0.expected,
    Slot25.Left0.expected,
    Slot25.Left2.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8123981507810308054025502720 }, { target := 1, numerator := 117797731863249466783369789440 }, { target := 2, numerator := 208515525367131240053321236480 }, { target := 3, numerator := 6769984589841923378354585600 }, { target := 4, numerator := 129983704124964928864408043520 }, { target := 5, numerator := 6769984589841923378354585600 }, { target := 6, numerator := 207161528449162855377650319360 }, { target := 7, numerator := 216639506874941548107346739200 }, { target := 8, numerator := 129983704124964928864408043520 }, { target := 9, numerator := 3318646445940510840069417861120 }, { target := 10, numerator := 212577516121036394080333987840 }, { target := 11, numerator := 117797731863249466783369789440 }, { target := 12, numerator := 207161528449162855377650319360 }, { target := 13, numerator := 6769984589841923378354585600 }, { target := 14, numerator := 212577516121036394080333987840 }, { target := 15, numerator := 6769984589841923378354585600 }, { target := 16, numerator := 207161528449162855377650319360 }, { target := 17, numerator := 216639506874941548107346739200 }, { target := 18, numerator := 8123981507810308054025502720 }, { target := 19, numerator := 16789559781336237980833021952 }, { target := 20, numerator := 18955954591831236429972766720 }, { target := 21, numerator := 16247961078712488368548085760 }, { target := 22, numerator := 213931487536381096852549795840 }, { target := 23, numerator := 18955954591831236429972766720 }, { target := 24, numerator := 16247961078712488368548085760 }, { target := 25, numerator := 18955954591831236429972766720 }, { target := 26, numerator := 18955954591831236429972766720 }, { target := 27, numerator := 785859717507060687425442414592 }, { target := 28, numerator := 19497553294454986042257702912 }, { target := 29, numerator := 213931487536381096852549795840 }, { target := 30, numerator := 785859717507060687425442414592 }, { target := 31, numerator := 16789559781336237980833021952 }, { target := 32, numerator := 18955954591831236429972766720 }, { target := 33, numerator := 19497553294454986042257702912 }, { target := 34, numerator := 18955954591831236429972766720 }, { target := 35, numerator := 574892926631110765789052928 }, { target := 36, numerator := 12000889843424437235846479872 }, { target := 37, numerator := 622800670517036662938140672 }, { target := 38, numerator := 12911136977257029281679147008 }, { target := 39, numerator := 19330774657971099499656904704 }, { target := 40, numerator := 598846798574073714363596800 }, { target := 41, numerator := 19330774657971099499656904704 }, { target := 42, numerator := 20145206304031839751191396352 }, { target := 43, numerator := 12000889843424437235846479872 }, { target := 44, numerator := 598846798574073714363596800 }, { target := 90, numerator := 16789563784279701975805722624 }, { target := 91, numerator := 18955959111283534488812912640 }, { target := 92, numerator := 16247964952528743847553925120 }, { target := 93, numerator := 213931538541628460659460014080 }, { target := 94, numerator := 18955959111283534488812912640 }, { target := 95, numerator := 16247964952528743847553925120 }, { target := 96, numerator := 18955959111283534488812912640 }, { target := 97, numerator := 18955959111283534488812912640 }, { target := 98, numerator := 785859904870640244093358178304 }, { target := 99, numerator := 19497557943034492617064710144 }, { target := 100, numerator := 213931538541628460659460014080 }, { target := 101, numerator := 785859904870640244093358178304 }, { target := 102, numerator := 16789563784279701975805722624 }, { target := 103, numerator := 18955959111283534488812912640 }, { target := 104, numerator := 19497557943034492617064710144 }, { target := 105, numerator := 18955959111283534488812912640 }]

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
    Slot26.Left3.expected,
    Slot26.Left5.expected,
    Slot27.Left0.expected,
    Slot27.Left1.expected,
    Slot27.Left2.expected,
    Slot27.Left3.expected,
    Slot27.Left4.expected,
    Slot27.Left5.expected,
    Slot27.Left6.expected,
    Slot27.Left7.expected,
    Slot27.Left8.expected,
    Slot27.Left9.expected,
    Slot27.Left10.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 166265079128874468683808768 }, { target := 72, numerator := 181905556920138733631569920 }, { target := 73, numerator := 166265079128874468683808768 }, { target := 74, numerator := 181905556920138733631569920 }, { target := 85, numerator := 189357451230107033778782208 }, { target := 86, numerator := 207170217603491335524843520 }, { target := 87, numerator := 189357451230107033778782208 }, { target := 88, numerator := 207170217603491335524843520 }, { target := 106, numerator := 2099806943552714463982387200 }, { target := 107, numerator := 43833469946662914435632332800 }, { target := 108, numerator := 2274790855515440669314252800 }, { target := 109, numerator := 47158164273954712336937779200 }, { target := 110, numerator := 70606008476960023851407769600 }, { target := 111, numerator := 2187298899534077566648320000 }, { target := 112, numerator := 70606008476960023851407769600 }, { target := 113, numerator := 73580734980326369342049484800 }, { target := 114, numerator := 43833469946662914435632332800 }, { target := 115, numerator := 2187298899534077566648320000 }, { target := 116, numerator := 147791181447888416607830016 }, { target := 117, numerator := 161693828373456652116951040 }, { target := 118, numerator := 147791181447888416607830016 }, { target := 119, numerator := 161693828373456652116951040 }, { target := 130, numerator := 1981325526285754085148721152 }, { target := 131, numerator := 2167707886631653242442874880 }, { target := 132, numerator := 1981325526285754085148721152 }, { target := 133, numerator := 2167707886631653242442874880 }, { target := 135, numerator := 175502027969367494721798144 }, { target := 136, numerator := 192011421193479774388879360 }, { target := 137, numerator := 175502027969367494721798144 }, { target := 138, numerator := 192011421193479774388879360 }, { target := 140, numerator := 574892732940297991838760960 }, { target := 141, numerator := 12000885800128720579634135040 }, { target := 142, numerator := 622800460685322824491991040 }, { target := 143, numerator := 12911132627284192400045506560 }, { target := 144, numerator := 19330768145117519975578337280 }, { target := 145, numerator := 598846596812810408165376000 }, { target := 146, numerator := 19330768145117519975578337280 }, { target := 147, numerator := 20145199516782942130683248640 }, { target := 148, numerator := 12000885800128720579634135040 }, { target := 149, numerator := 598846596812810408165376000 }, { target := 150, numerator := 147791181447888416607830016 }, { target := 151, numerator := 161693828373456652116951040 }, { target := 152, numerator := 147791181447888416607830016 }, { target := 153, numerator := 161693828373456652116951040 }, { target := 155, numerator := 175502027969367494721798144 }, { target := 156, numerator := 192011421193479774388879360 }, { target := 157, numerator := 175502027969367494721798144 }, { target := 158, numerator := 192011421193479774388879360 }, { target := 187, numerator := 170883553549120981702803456 }, { target := 188, numerator := 186958489056809254010224640 }, { target := 189, numerator := 170883553549120981702803456 }, { target := 190, numerator := 186958489056809254010224640 }, { target := 201, numerator := 6456627239504625200554573824 }, { target := 202, numerator := 7063999127065387489359298560 }, { target := 203, numerator := 6456627239504625200554573824 }, { target := 204, numerator := 7063999127065387489359298560 }, { target := 206, numerator := 170883553549120981702803456 }, { target := 207, numerator := 186958489056809254010224640 }, { target := 208, numerator := 170883553549120981702803456 }, { target := 209, numerator := 186958489056809254010224640 }, { target := 221, numerator := 1981325526285754085148721152 }, { target := 222, numerator := 2167707886631653242442874880 }, { target := 223, numerator := 1981325526285754085148721152 }, { target := 224, numerator := 2167707886631653242442874880 }]

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
    Slot27.Left11.expected,
    Slot27.Left12.expected,
    Slot27.Left13.expected,
    Slot27.Left14.expected,
    Slot27.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 226, numerator := 6456627239504625200554573824 }, { target := 227, numerator := 7063999127065387489359298560 }, { target := 228, numerator := 6456627239504625200554573824 }, { target := 229, numerator := 7063999127065387489359298560 }, { target := 232, numerator := 166265079128874468683808768 }, { target := 233, numerator := 181905556920138733631569920 }, { target := 234, numerator := 166265079128874468683808768 }, { target := 235, numerator := 181905556920138733631569920 }, { target := 248, numerator := 170883553549120981702803456 }, { target := 249, numerator := 186958489056809254010224640 }, { target := 250, numerator := 170883553549120981702803456 }, { target := 251, numerator := 186958489056809254010224640 }, { target := 253, numerator := 170883553549120981702803456 }, { target := 254, numerator := 186958489056809254010224640 }, { target := 255, numerator := 170883553549120981702803456 }, { target := 256, numerator := 186958489056809254010224640 }, { target := 259, numerator := 189357451230107033778782208 }, { target := 260, numerator := 207170217603491335524843520 }, { target := 261, numerator := 189357451230107033778782208 }, { target := 262, numerator := 207170217603491335524843520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12.Parent3
