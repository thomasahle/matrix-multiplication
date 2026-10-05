import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 73; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent3

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 749573760894548932401561600 }, { target := 36, numerator := 13342412943922970996747796480 }, { target := 37, numerator := 749573760894548932401561600 }, { target := 38, numerator := 11868251214163691429691392000 }, { target := 39, numerator := 20263477336182639472588881920 }, { target := 40, numerator := 749573760894548932401561600 }, { target := 41, numerator := 20263477336182639472588881920 }, { target := 42, numerator := 20263477336182639472588881920 }, { target := 43, numerator := 13342412943922970996747796480 }, { target := 44, numerator := 749573760894548932401561600 }, { target := 71, numerator := 22009344572051240661664399360 }, { target := 73, numerator := 22009344572051240661664399360 }, { target := 89, numerator := 26505623037187018741109489664 }, { target := 106, numerator := 2562843474229572129647493120 }, { target := 107, numerator := 45618613841286383907725377536 }, { target := 108, numerator := 2562843474229572129647493120 }, { target := 109, numerator := 40578355008634892052751974400 }, { target := 110, numerator := 69282201920006099904803897344 }, { target := 111, numerator := 2562843474229572129647493120 }, { target := 112, numerator := 69282201920006099904803897344 }, { target := 113, numerator := 69282201920006099904803897344 }, { target := 114, numerator := 45618613841286383907725377536 }, { target := 115, numerator := 2562843474229572129647493120 }, { target := 116, numerator := 770272186123262477880870830080 }, { target := 118, numerator := 770272186123262477880870830080 }, { target := 134, numerator := 3819741362467496174468428988416 }, { target := 139, numerator := 2959450406416612219680718848 }, { target := 140, numerator := 749573518781032964963696640 }, { target := 141, numerator := 13342408634302386776353800192 }, { target := 142, numerator := 749573518781032964963696640 }, { target := 143, numerator := 11868247380699688611925196800 }, { target := 144, numerator := 20263470791047257819518599168 }, { target := 145, numerator := 749573518781032964963696640 }, { target := 146, numerator := 20263470791047257819518599168 }, { target := 147, numerator := 20263470791047257819518599168 }, { target := 148, numerator := 13342408634302386776353800192 }, { target := 149, numerator := 749573518781032964963696640 }, { target := 150, numerator := 770272563912581107452487925760 }, { target := 152, numerator := 770272563912581107452487925760 }, { target := 154, numerator := 2135418611357702385901324206080 }, { target := 159, numerator := 3036821658871948486861914112 }, { target := 160, numerator := 96714065569170333976494080 }, { target := 205, numerator := 2959450406416612219680718848 }, { target := 210, numerator := 1682824740903563811190996992 }, { target := 225, numerator := 3036821658871948486861914112 }, { target := 230, numerator := 47409234942007297715277398016 }, { target := 231, numerator := 1856910058928070412348686336 }, { target := 232, numerator := 22009155677391925875855851520 }, { target := 234, numerator := 22009155677391925875855851520 }, { target := 236, numerator := 201195177297909756743181664256 }, { target := 237, numerator := 2959450406416612219680718848 }, { target := 252, numerator := 96714065569170333976494080 }, { target := 257, numerator := 1856910058928070412348686336 }, { target := 258, numerator := 96714065569170333976494080 }, { target := 263, numerator := 2978793219530446286476017664 }, { target := 264, numerator := 1682824740903563811190996992 }, { target := 265, numerator := 2005456819013217972190707712 }]

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
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 16712190530352633711138177024 }, { target := 20, numerator := 19845726254793752531976585216 }, { target := 21, numerator := 15145422668132074300718972928 }, { target := 22, numerator := 156154530267982421238447341568 }, { target := 23, numerator := 18801214346646712925030449152 }, { target := 24, numerator := 15145422668132074300718972928 }, { target := 25, numerator := 18801214346646712925030449152 }, { target := 26, numerator := 18801214346646712925030449152 }, { target := 27, numerator := 805318681181367536955470905344 }, { target := 28, numerator := 18801214346646712925030449152 }, { target := 29, numerator := 156154530267982421238447341568 }, { target := 30, numerator := 805318681181367536955470905344 }, { target := 31, numerator := 16712190530352633711138177024 }, { target := 32, numerator := 18801214346646712925030449152 }, { target := 33, numerator := 18801214346646712925030449152 }, { target := 34, numerator := 19845726254793752531976585216 }, { target := 35, numerator := 2150643008813778173748005830656 }, { target := 38, numerator := 7693783367254182441958162563072 }, { target := 40, numerator := 2150642293851971046753177698304 }, { target := 71, numerator := 3944257060913633963024127623168 }, { target := 73, numerator := 3944255655928711652797847699456 }, { target := 89, numerator := 19079323953555872070955433984 }, { target := 90, numerator := 16712190530352633711138177024 }, { target := 91, numerator := 19845726254793752531976585216 }, { target := 92, numerator := 15145422668132074300718972928 }, { target := 93, numerator := 156154530267982421238447341568 }, { target := 94, numerator := 18801214346646712925030449152 }, { target := 95, numerator := 15145422668132074300718972928 }, { target := 96, numerator := 18801214346646712925030449152 }, { target := 97, numerator := 18801214346646712925030449152 }, { target := 98, numerator := 805318681181367536955470905344 }, { target := 99, numerator := 18801214346646712925030449152 }, { target := 100, numerator := 156154530267982421238447341568 }, { target := 101, numerator := 805318681181367536955470905344 }, { target := 102, numerator := 16712190530352633711138177024 }, { target := 103, numerator := 18801214346646712925030449152 }, { target := 104, numerator := 18801214346646712925030449152 }, { target := 105, numerator := 19845726254793752531976585216 }, { target := 106, numerator := 7290098973743159326003005751296 }, { target := 109, numerator := 26079847747840953267047997898752 }, { target := 111, numerator := 7290096550215723558362167640064 }, { target := 116, numerator := 146866577381927411352311018029056 }, { target := 118, numerator := 146866524593034576250488825577472 }, { target := 134, numerator := 3045960514715859344629524594688 }, { target := 140, numerator := 2150643008813778173748005830656 }, { target := 143, numerator := 7693783367254182441958162563072 }, { target := 145, numerator := 2150642293851971046753177698304 }, { target := 150, numerator := 146858217714556906163375607644160 }, { target := 152, numerator := 146858164929656606706809534676992 }, { target := 154, numerator := 68109608721843146212616582463488 }, { target := 232, numerator := 997776129889154349334783852544 }, { target := 234, numerator := 997776129889154349334783852544 }, { target := 236, numerator := 6664506851001173214183418757120 }, { target := 265, numerator := 43577313160781069933430702080 }]

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
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
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
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot14.Left16.expected,
    Slot14.Left17.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 5319273606304368368707174400 }, { target := 1, numerator := 89363796585913388594280529920 }, { target := 2, numerator := 193621559269479008620941148160 }, { target := 3, numerator := 6383128327565242042448609280 }, { target := 4, numerator := 102130053241043872679177748480 }, { target := 5, numerator := 7446983048826115716190044160 }, { target := 6, numerator := 193621559269479008620941148160 }, { target := 7, numerator := 193621559269479008620941148160 }, { target := 8, numerator := 102130053241043872679177748480 }, { target := 9, numerator := 2389417703951922271223262740480 }, { target := 10, numerator := 191493849826957261273458278400 }, { target := 11, numerator := 89363796585913388594280529920 }, { target := 12, numerator := 193621559269479008620941148160 }, { target := 13, numerator := 7446983048826115716190044160 }, { target := 14, numerator := 191493849826957261273458278400 }, { target := 15, numerator := 7446983048826115716190044160 }, { target := 16, numerator := 193621559269479008620941148160 }, { target := 17, numerator := 193621559269479008620941148160 }, { target := 18, numerator := 6383128327565242042448609280 }, { target := 19, numerator := 792204971689893435854330789888 }, { target := 21, numerator := 29255075661844856596497212375040 }, { target := 24, numerator := 29255068498014902083245423198208 }, { target := 31, numerator := 792212135519847949106119966720 }, { target := 35, numerator := 23872439408968371716651200020480 }, { target := 38, numerator := 86829208069120040763796330905600 }, { target := 40, numerator := 23872439408968371716651200020480 }, { target := 71, numerator := 793249408040176749546953506816 }, { target := 73, numerator := 793249408040176749546953506816 }, { target := 89, numerator := 5125845475166027700754186240 }, { target := 90, numerator := 792204971689893435854330789888 }, { target := 92, numerator := 29255075661844856596497212375040 }, { target := 95, numerator := 29255068498014902083245423198208 }, { target := 102, numerator := 792212135519847949106119966720 }, { target := 106, numerator := 81949910377811708524052877410304 }, { target := 109, numerator := 298069489151894321870920356986880 }, { target := 111, numerator := 81949910377811708524052877410304 }, { target := 116, numerator := 29293645306751705451601361633280 }, { target := 118, numerator := 29293645306751705451601361633280 }, { target := 134, numerator := 86114203982789265372670328832 }, { target := 139, numerator := 186580775296043408307452379136 }, { target := 140, numerator := 23872439408968371716651200020480 }, { target := 143, numerator := 86829208069120040763796330905600 }, { target := 145, numerator := 23872439408968371716651200020480 }, { target := 150, numerator := 29293638133477017972610282029056 }, { target := 152, numerator := 29293638133477017972610282029056 }, { target := 154, numerator := 6151014570199233240905023488 }, { target := 159, numerator := 98416233123187731854480375808 }, { target := 160, numerator := 7176183665232438781055860736 }, { target := 205, numerator := 186580775296043408307452379136 }, { target := 210, numerator := 186580775296043408307452379136 }, { target := 225, numerator := 98416233123187731854480375808 }, { target := 230, numerator := 2302529787444579643178780459008 }, { target := 231, numerator := 184530437105976997227150704640 }, { target := 232, numerator := 2954840598394984802624754155520 }, { target := 234, numerator := 2954839189417526847142354747392 }, { target := 236, numerator := 86114203982789265372670328832 }, { target := 237, numerator := 186580775296043408307452379136 }, { target := 252, numerator := 7176183665232438781055860736 }, { target := 257, numerator := 184530437105976997227150704640 }, { target := 258, numerator := 7176183665232438781055860736 }, { target := 263, numerator := 186580775296043408307452379136 }, { target := 264, numerator := 186580775296043408307452379136 }, { target := 265, numerator := 6151014570199233240905023488 }]

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
    Slot20.Left0.expected,
    Slot20.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19244871232979350353566760960 }, { target := 1, numerator := 3072389673194955738075333918720 }, { target := 3, numerator := 30657828676177461338525159915520 }, { target := 11, numerator := 3072389673194955738075333918720 }, { target := 18, numerator := 19242675332564815968542392320 }, { target := 19, numerator := 2960845664938383557949715906560 }, { target := 21, numerator := 111246577828538799309518190673920 }, { target := 24, numerator := 111238164014504460251236757667840 }, { target := 31, numerator := 2969259478972722616231148912640 }, { target := 35, numerator := 26107722476051429184314410008576 }, { target := 38, numerator := 89532267593432290262976062029824 }, { target := 40, numerator := 26107722476051429184314410008576 }, { target := 71, numerator := 16712190530352633711138177024 }, { target := 73, numerator := 16712190530352633711138177024 }, { target := 85, numerator := 19845726254793752531976585216 }, { target := 87, numerator := 19845726254793752531976585216 }, { target := 90, numerator := 2960844253097487419789254066176 }, { target := 92, numerator := 111246524782049414994930048172032 }, { target := 95, numerator := 111238110972027094153892739416064 }, { target := 102, numerator := 2969258063119808260826562822144 }, { target := 106, numerator := 94833208971236679570311601979392 }, { target := 109, numerator := 325220354405313626304895235653632 }, { target := 111, numerator := 94833208971236679570311601979392 }, { target := 116, numerator := 15145422668132074300718972928 }, { target := 118, numerator := 15145422668132074300718972928 }, { target := 130, numerator := 156154530267982421238447341568 }, { target := 132, numerator := 156154530267982421238447341568 }, { target := 135, numerator := 18801214346646712925030449152 }, { target := 137, numerator := 18801214346646712925030449152 }, { target := 140, numerator := 23996613346076139579936771932160 }, { target := 143, numerator := 82376177792000586071642229178368 }, { target := 145, numerator := 23996613346076139579936771932160 }, { target := 150, numerator := 15145422668132074300718972928 }, { target := 152, numerator := 15145422668132074300718972928 }, { target := 155, numerator := 18801214346646712925030449152 }, { target := 157, numerator := 18801214346646712925030449152 }, { target := 187, numerator := 18801214346646712925030449152 }, { target := 189, numerator := 18801214346646712925030449152 }, { target := 201, numerator := 805318681181367536955470905344 }, { target := 203, numerator := 805318681181367536955470905344 }, { target := 206, numerator := 18801214346646712925030449152 }, { target := 208, numerator := 18801214346646712925030449152 }, { target := 221, numerator := 156154530267982421238447341568 }, { target := 223, numerator := 156154530267982421238447341568 }, { target := 226, numerator := 805318681181367536955470905344 }, { target := 228, numerator := 805318681181367536955470905344 }, { target := 232, numerator := 809968771845216862249171288064 }, { target := 234, numerator := 809968771845216862249171288064 }, { target := 248, numerator := 18801214346646712925030449152 }, { target := 250, numerator := 18801214346646712925030449152 }, { target := 253, numerator := 18801214346646712925030449152 }, { target := 255, numerator := 18801214346646712925030449152 }, { target := 259, numerator := 19845726254793752531976585216 }, { target := 261, numerator := 19845726254793752531976585216 }]

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
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected,
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
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 26804997460368539899431747584 }, { target := 1, numerator := 3880533363731339071320896831488 }, { target := 3, numerator := 40514502264924469740662150922240 }, { target := 11, numerator := 3880533510124700040279898456064 }, { target := 18, numerator := 26804997460368539899431747584 }, { target := 19, numerator := 1008097607971370252353260224512 }, { target := 21, numerator := 36506437248085463940796895985664 }, { target := 24, numerator := 36506450758775971430851852369920 }, { target := 31, numerator := 1008084286175522077084112388096 }, { target := 35, numerator := 749573760894548932401561600 }, { target := 38, numerator := 2562843474229572129647493120 }, { target := 40, numerator := 749573518781032964963696640 }, { target := 61, numerator := 13342412943922970996747796480 }, { target := 64, numerator := 45618613841286383907725377536 }, { target := 66, numerator := 13342408634302386776353800192 }, { target := 75, numerator := 749573760894548932401561600 }, { target := 78, numerator := 2562843474229572129647493120 }, { target := 80, numerator := 749573518781032964963696640 }, { target := 90, numerator := 1008097607971370252353260224512 }, { target := 92, numerator := 36506437248085463940796895985664 }, { target := 95, numerator := 36506450758775971430851852369920 }, { target := 102, numerator := 1008084286175522077084112388096 }, { target := 106, numerator := 11868251214163691429691392000 }, { target := 109, numerator := 40578355008634892052751974400 }, { target := 111, numerator := 11868247380699688611925196800 }, { target := 120, numerator := 20263477336182639472588881920 }, { target := 123, numerator := 69282201920006099904803897344 }, { target := 125, numerator := 20263470791047257819518599168 }, { target := 140, numerator := 2111858001917057304384969375744 }, { target := 143, numerator := 7158650265928634682727804698624 }, { target := 145, numerator := 2111858001674943788417531510784 }, { target := 177, numerator := 20263477336182639472588881920 }, { target := 180, numerator := 69282201920006099904803897344 }, { target := 182, numerator := 20263470791047257819518599168 }, { target := 191, numerator := 20263477336182639472588881920 }, { target := 194, numerator := 69282201920006099904803897344 }, { target := 196, numerator := 20263470791047257819518599168 }, { target := 211, numerator := 13342412943922970996747796480 }, { target := 214, numerator := 45618613841286383907725377536 }, { target := 216, numerator := 13342408634302386776353800192 }, { target := 238, numerator := 749573760894548932401561600 }, { target := 241, numerator := 2562843474229572129647493120 }, { target := 243, numerator := 749573518781032964963696640 }]

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
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 116056878683004400771792896 }, { target := 1, numerator := 3094850098213450687247810560 }, { target := 2, numerator := 2959450406416612219680718848 }, { target := 3, numerator := 96714065569170333976494080 }, { target := 4, numerator := 3036821658871948486861914112 }, { target := 5, numerator := 96714065569170333976494080 }, { target := 6, numerator := 2959450406416612219680718848 }, { target := 7, numerator := 1682824740903563811190996992 }, { target := 8, numerator := 3036821658871948486861914112 }, { target := 9, numerator := 47409234942007297715277398016 }, { target := 10, numerator := 1856910058928070412348686336 }, { target := 11, numerator := 3094850098213450687247810560 }, { target := 12, numerator := 2959450406416612219680718848 }, { target := 13, numerator := 96714065569170333976494080 }, { target := 14, numerator := 1856910058928070412348686336 }, { target := 15, numerator := 96714065569170333976494080 }, { target := 16, numerator := 2978793219530446286476017664 }, { target := 17, numerator := 1682824740903563811190996992 }, { target := 18, numerator := 116056878683004400771792896 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent3
