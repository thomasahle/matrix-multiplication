import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left3.expected,
    Slot5.Left11.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 1919124471118930141186621440 }, { target := 37, numerator := 70037351482074608954454835200 }, { target := 40, numerator := 70037340420901783659998085120 }, { target := 47, numerator := 1919079098438051893635710976 }, { target := 86, numerator := 3400889539398616508232892416 }, { target := 89, numerator := 12171164660739646404383735808 }, { target := 91, numerator := 3400794556328347267705602048 }, { target := 122, numerator := 434176681660649480243904512 }, { target := 124, numerator := 434176789575903751295729664 }, { target := 145, numerator := 6722722095094333328112746496 }, { target := 147, numerator := 245414764249543403013478023168 }, { target := 150, numerator := 245414724991271667732446183424 }, { target := 157, numerator := 6722562608347517495713726464 }, { target := 161, numerator := 124472117276138669580000165888 }, { target := 164, numerator := 445140711551065626490756399104 }, { target := 166, numerator := 124467402533023019649554448384 }, { target := 197, numerator := 14045153766884233938726813696 }, { target := 199, numerator := 14045158513325834516387856384 }, { target := 216, numerator := 151746914597412838242779136 }, { target := 218, numerator := 6992339794334426940066234368 }, { target := 221, numerator := 6992328723014710210167046144 }, { target := 228, numerator := 151732436717783268374609920 }, { target := 232, numerator := 124472239085383974737852497920 }, { target := 235, numerator := 445141147954941979247121530880 }, { target := 237, numerator := 124467524340674894964247756800 }, { target := 242, numerator := 169089108751609904236257607680 }, { target := 244, numerator := 169089174547210994983813251072 }, { target := 406, numerator := 3400905063102181221240668160 }, { target := 409, numerator := 12171218622489545914177290240 }, { target := 411, numerator := 3400810073471574698518118400 }, { target := 416, numerator := 14045203351779591866088947712 }, { target := 418, numerator := 14045208098126616851575209984 }, { target := 498, numerator := 456725954794601505380892672 }, { target := 500, numerator := 456726116353356837949538304 }]

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
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 329243190060541805466746880 }, { target := 17, numerator := 11109993391578469883355070464 }, { target := 19, numerator := 135555156198713509578799054848 }, { target := 27, numerator := 11110066588329323107033546752 }, { target := 34, numerator := 351771212517173419529207808 }, { target := 35, numerator := 2969905459757567302434816000 }, { target := 37, numerator := 103395174353858264071132938240 }, { target := 40, numerator := 103395288471263057829722849280 }, { target := 47, numerator := 2969892780045923551480381440 }, { target := 86, numerator := 1919124471118930141186621440 }, { target := 89, numerator := 6722722095094333328112746496 }, { target := 91, numerator := 1921553628553568603829436416 }, { target := 122, numerator := 80263797607882758127878144 }, { target := 124, numerator := 80263606244305091621289984 }, { target := 126, numerator := 329243592310801523131023360 }, { target := 127, numerator := 11110006504540619912001880064 }, { target := 129, numerator := 135555318009388946303481806848 }, { target := 137, numerator := 11110079701150735647325028352 }, { target := 144, numerator := 351771668467229194052435968 }, { target := 145, numerator := 10651628477601273643794432000 }, { target := 147, numerator := 370828970321501958263254548480 }, { target := 150, numerator := 370829379605977562538898882560 }, { target := 157, numerator := 10651583001548428724278394880 }, { target := 161, numerator := 70037351482074608954454835200 }, { target := 164, numerator := 245414764249543403013478023168 }, { target := 166, numerator := 70125452483030778624950140928 }, { target := 197, numerator := 2805015837979550857247588352 }, { target := 199, numerator := 2805009150308618697621635072 }, { target := 216, numerator := 4739717118349454572026593280 }, { target := 218, numerator := 166528459186577549370694041600 }, { target := 221, numerator := 166528573304172338738563645440 }, { target := 228, numerator := 4739673490500431756440633344 }, { target := 232, numerator := 63051420184160497818025328640 }, { target := 235, numerator := 220620323953813208371990364160 }, { target := 237, numerator := 63133112688696351684883906560 }, { target := 242, numerator := 33843500735226500909371490304 }, { target := 244, numerator := 33843420046129118655224479744 }, { target := 406, numerator := 1767485724867391363875864576 }, { target := 409, numerator := 6184527994215490954350034944 }, { target := 411, numerator := 1769775765839887324208431104 }, { target := 416, numerator := 2805081951189124025759563776 }, { target := 418, numerator := 2805075263360565879175643136 }, { target := 498, numerator := 80266158793938942717591552 }, { target := 500, numerator := 80265967424731776676790272 }]

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
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 185197289207990432905035776 }, { target := 17, numerator := 5740176213285314912619331584 }, { target := 19, numerator := 67377453288122895566830043136 }, { target := 27, numerator := 5740218714639392784814964736 }, { target := 34, numerator := 185220901071367028569276416 }, { target := 35, numerator := 430984079641049205798076416 }, { target := 37, numerator := 21076942922280405508867227648 }, { target := 40, numerator := 21076950614120916908129648640 }, { target := 47, numerator := 431012283056257669760286720 }, { target := 126, numerator := 185196803509407319785996288 }, { target := 127, numerator := 5740161159093833302007611392 }, { target := 129, numerator := 67377276583951167335555923968 }, { target := 137, numerator := 5740203660336447083425824768 }, { target := 144, numerator := 185220415310859420573892608 }, { target := 145, numerator := 1519536183138372760589303808 }, { target := 147, numerator := 74311741229563668227501850624 }, { target := 150, numerator := 74311768348964416708222648320 }, { target := 157, numerator := 1519635620941117189898895360 }, { target := 216, numerator := 430884151935048461265666048 }, { target := 218, numerator := 21072056035141821963744313344 }, { target := 221, numerator := 21072063725198907910568017920 }, { target := 228, numerator := 430912348811030266285916160 }, { target := 232, numerator := 6985920236741285841972756480 }, { target := 235, numerator := 24794401037458459360455819264 }, { target := 237, numerator := 6992328723014710210167046144 }, { target := 406, numerator := 151593373570660529759846400 }, { target := 409, numerator := 538034614132026541363691520 }, { target := 411, numerator := 151732436717783268374609920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent2
