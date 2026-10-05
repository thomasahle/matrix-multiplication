import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk4Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 79843205513192904081801216 }, { target := 27, numerator := 2378882958595038792432746496 }, { target := 29, numerator := 25340208707377611357196124160 }, { target := 37, numerator := 2385527988895924370037276672 }, { target := 44, numerator := 85726844886309349525291008 }, { target := 80, numerator := 160912232705736667635384320 }, { target := 82, numerator := 5687035028589073699717513216 }, { target := 85, numerator := 5686826867629069264775806976 }, { target := 92, numerator := 160912599807090143533203456 }, { target := 131, numerator := 58266048483223131847131136 }, { target := 134, numerator := 202508820865887830968107008 }, { target := 136, numerator := 58343768097288182145482752 }, { target := 157, numerator := 258225194554867951217934336 }, { target := 158, numerator := 7693673003959765656682889216 }, { target := 160, numerator := 81954128488019304994161295360 }, { target := 168, numerator := 7715164052963123138985459712 }, { target := 175, numerator := 277253788309944994331885568 }, { target := 176, numerator := 5837068222168570000771645440 }, { target := 178, numerator := 206106316669564639754217062400 }, { target := 181, numerator := 206099004599049356681423093760 }, { target := 188, numerator := 5837084340602301855584747520 }, { target := 227, numerator := 2484280962756304275565969408 }, { target := 230, numerator := 8634338891407900193035649024 }, { target := 232, numerator := 2487594682541337671165280256 }, { target := 267, numerator := 79889367864799963983642624 }, { target := 268, numerator := 2380258339641689804367724544 }, { target := 270, numerator := 25354859467158955057469194240 }, { target := 278, numerator := 2386907211850264551104708608 }, { target := 285, numerator := 85776408937882301509926912 }, { target := 286, numerator := 5839605535539413751127080960 }, { target := 288, numerator := 206193464210276542379055906816 }, { target := 291, numerator := 206186152034668354626687860736 }, { target := 298, numerator := 5839621697019395269277515776 }, { target := 302, numerator := 23846525383081218364634300416 }, { target := 305, numerator := 82880714632067771972974542848 }, { target := 307, numerator := 23878333662479110626409971712 }, { target := 573, numerator := 163458399832566354935808000 }, { target := 575, numerator := 5774537370118594023275888640 }, { target := 578, numerator := 5774329039954129463373987840 }, { target := 585, numerator := 163458809382879593590947840 }, { target := 589, numerator := 2484301656274174486220111872 }, { target := 592, numerator := 8634410813565186527058722816 }, { target := 594, numerator := 2487615403661769997973192704 }, { target := 763, numerator := 58260875103755579183595520 }, { target := 766, numerator := 202490840326566247462338560 }, { target := 768, numerator := 58338587817180100443504640 }]

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
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 133769845581943098058997760 }, { target := 27, numerator := 6742880605795983823869050880 }, { target := 29, numerator := 74061575295382877782954475520 }, { target := 37, numerator := 6742927713383346874613760000 }, { target := 44, numerator := 133754143052822081144094720 }, { target := 80, numerator := 149881921387986218301521920 }, { target := 82, numerator := 5450121572568554345531965440 }, { target := 85, numerator := 5452660166889795859576258560 }, { target := 92, numerator := 152425858712271650291712000 }, { target := 131, numerator := 213613051095136002140798976 }, { target := 134, numerator := 714804280784430416158261248 }, { target := 136, numerator := 213677557269491537342889984 }, { target := 157, numerator := 456579086229562464940326912 }, { target := 158, numerator := 23014590860564924654583545856 }, { target := 160, numerator := 252784670760301454309745229824 }, { target := 168, numerator := 23014751646720422798426112000 }, { target := 175, numerator := 456525490844396416992804864 }, { target := 176, numerator := 5148993588409920223025561600 }, { target := 178, numerator := 187231660585446954134352691200 }, { target := 181, numerator := 187318870608928105686682828800 }, { target := 188, numerator := 5236387163637414635765760000 }, { target := 227, numerator := 9121763564391022616301797376 }, { target := 230, numerator := 30708263864524690311266435072 }, { target := 232, numerator := 9124063594831629044336820224 }, { target := 267, numerator := 133788189404691573359247360 }, { target := 268, numerator := 6743805255189939239969095680 }, { target := 270, numerator := 74071731339174220451775774720 }, { target := 278, numerator := 6743852369237153006223360000 }, { target := 285, numerator := 133772484722286984607825920 }, { target := 286, numerator := 5148986008311315403196334080 }, { target := 288, numerator := 187231384952078061141554626560 }, { target := 291, numerator := 187318594847172846316620349440 }, { target := 298, numerator := 5236379454882227461029888000 }, { target := 302, numerator := 99401784002760489140150599680 }, { target := 305, numerator := 334738799248320759303906525184 }, { target := 307, numerator := 99426590806333175509244968960 }, { target := 573, numerator := 149884448087521158244597760 }, { target := 575, numerator := 5450213450358185343131320320 }, { target := 578, numerator := 5452752087474882316263751680 }, { target := 585, numerator := 152428428297334041870336000 }, { target := 589, numerator := 9128455702279271244651036672 }, { target := 592, numerator := 30729915699683545937411571712 }, { target := 594, numerator := 9130759581087417557328068608 }, { target := 763, numerator := 219480987939131430669385728 }, { target := 766, numerator := 733779279154341411324690432 }, { target := 768, numerator := 219548893660169286117752832 }]

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
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot24.Left5.expected,
    Slot24.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 58266048483223131847131136 }, { target := 27, numerator := 2484280962756304275565969408 }, { target := 29, numerator := 23846525383081218364634300416 }, { target := 37, numerator := 2484301656274174486220111872 }, { target := 44, numerator := 58260875103755579183595520 }, { target := 80, numerator := 11030311317750449333862400 }, { target := 82, numerator := 386946649600015655239680000 }, { target := 85, numerator := 386945368649617891550822400 }, { target := 92, numerator := 11032541120294704644096000 }, { target := 157, numerator := 202508820865887830968107008 }, { target := 158, numerator := 8634338891407900193035649024 }, { target := 160, numerator := 82880714632067771972974542848 }, { target := 168, numerator := 8634410813565186527058722816 }, { target := 175, numerator := 202490840326566247462338560 }, { target := 176, numerator := 538041440179153476691951616 }, { target := 178, numerator := 18874656084117685619864371200 }, { target := 181, numerator := 18874593601348436692373078016 }, { target := 188, numerator := 538150206481179387510128640 }, { target := 267, numerator := 58343768097288182145482752 }, { target := 268, numerator := 2487594682541337671165280256 }, { target := 270, numerator := 23878333662479110626409971712 }, { target := 278, numerator := 2487615403661769997973192704 }, { target := 285, numerator := 58338587817180100443504640 }, { target := 286, numerator := 537840859317753861579472896 }, { target := 288, numerator := 18867619646971295539868467200 }, { target := 291, numerator := 18867557187495508310067511296 }, { target := 298, numerator := 537949585071902002344099840 }, { target := 573, numerator := 11028151719568985288605696 }, { target := 575, numerator := 386870890244116512453427200 }, { target := 578, numerator := 386869609544512953013764096 }, { target := 585, numerator := 11030381085545551720611840 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent3
