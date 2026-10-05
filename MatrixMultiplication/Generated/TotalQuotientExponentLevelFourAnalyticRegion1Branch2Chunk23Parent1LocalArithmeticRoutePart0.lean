import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk23Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 95; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent1

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
    Slot1.Left16.expected,
    Slot1.Left17.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
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
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1913733852094583084175851520 }, { target := 72, numerator := 1103593877936079507243925504 }, { target := 73, numerator := 1913733852094583084175851520 }, { target := 74, numerator := 1103593877936079507243925504 }, { target := 85, numerator := 1102540347488541807332032512 }, { target := 87, numerator := 1102540347488541807332032512 }, { target := 89, numerator := 220874525136779045934989312 }, { target := 116, numerator := 37226448483748651076111302656 }, { target := 117, numerator := 40754253700400841037782712320 }, { target := 118, numerator := 37226448483748651076111302656 }, { target := 119, numerator := 40754253700400841037782712320 }, { target := 130, numerator := 8675251681554578957691518976 }, { target := 132, numerator := 8675251681554578957691518976 }, { target := 134, numerator := 21446665160884356695162093568 }, { target := 135, numerator := 1044511908147039606946136064 }, { target := 137, numerator := 1044511908147039606946136064 }, { target := 139, numerator := 3520391986717800156744384512 }, { target := 150, numerator := 37226439573971263474397872128 }, { target := 151, numerator := 40754243720712297160915288064 }, { target := 152, numerator := 37226439573971263474397872128 }, { target := 153, numerator := 40754243720712297160915288064 }, { target := 154, numerator := 197908499950795658197708308480 }, { target := 155, numerator := 1044511908147039606946136064 }, { target := 157, numerator := 1044511908147039606946136064 }, { target := 159, numerator := 1856910058928070412348686336 }, { target := 160, numerator := 135399691796838467567091712 }, { target := 187, numerator := 1044511908147039606946136064 }, { target := 189, numerator := 1044511908147039606946136064 }, { target := 201, numerator := 44739926732298196497526161408 }, { target := 203, numerator := 44739926732298196497526161408 }, { target := 205, numerator := 3520391986717800156744384512 }, { target := 206, numerator := 1044511908147039606946136064 }, { target := 208, numerator := 1044511908147039606946136064 }, { target := 210, numerator := 3520391986717800156744384512 }, { target := 221, numerator := 8675251681554578957691518976 }, { target := 223, numerator := 8675251681554578957691518976 }, { target := 225, numerator := 1856910058928070412348686336 }, { target := 226, numerator := 44739926732298196497526161408 }, { target := 228, numerator := 44739926732298196497526161408 }, { target := 230, numerator := 43443958253671314022241140736 }, { target := 231, numerator := 3481706360490132023153786880 }, { target := 232, numerator := 985287732407935479714938880 }, { target := 233, numerator := 1103603857624623384111349760 }, { target := 234, numerator := 985287732407935479714938880 }, { target := 235, numerator := 1103603857624623384111349760 }, { target := 236, numerator := 21446665160884356695162093568 }, { target := 237, numerator := 3520391986717800156744384512 }, { target := 252, numerator := 135399691796838467567091712 }, { target := 257, numerator := 3481706360490132023153786880 }, { target := 258, numerator := 135399691796838467567091712 }, { target := 263, numerator := 3520391986717800156744384512 }, { target := 264, numerator := 3520391986717800156744384512 }, { target := 265, numerator := 240203171151164503794647040 }]

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
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 1456580576092798744013045760 }, { target := 36, numerator := 12963567127225908821716107264 }, { target := 37, numerator := 728290288046399372006522880 }, { target := 38, numerator := 14136673313993861307207516160 }, { target := 39, numerator := 19688114120187663023243001856 }, { target := 40, numerator := 1456580333979282776575180800 }, { target := 41, numerator := 19688114120187663023243001856 }, { target := 42, numerator := 19688114120187663023243001856 }, { target := 43, numerator := 12963567127225908821716107264 }, { target := 44, numerator := 728290288046399372006522880 }, { target := 61, numerator := 12963567127225908821716107264 }, { target := 64, numerator := 46376305474680508257788755968 }, { target := 66, numerator := 12963562817605324601322110976 }, { target := 75, numerator := 728290288046399372006522880 }, { target := 78, numerator := 2605410419925871250437570560 }, { target := 80, numerator := 728290045932883404568657920 }, { target := 106, numerator := 14136673313993861307207516160 }, { target := 107, numerator := 46376305474680508257788755968 }, { target := 108, numerator := 2605410419925871250437570560 }, { target := 109, numerator := 82504663297652589597189734400 }, { target := 110, numerator := 70432928351996052803495657472 }, { target := 111, numerator := 14136669480529858489441320960 }, { target := 112, numerator := 70432928351996052803495657472 }, { target := 113, numerator := 70432928351996052803495657472 }, { target := 114, numerator := 46376305474680508257788755968 }, { target := 115, numerator := 2605410419925871250437570560 }, { target := 120, numerator := 19688114120187663023243001856 }, { target := 123, numerator := 70432928351996052803495657472 }, { target := 125, numerator := 19688107575052281370172719104 }, { target := 140, numerator := 1456580333979282776575180800 }, { target := 141, numerator := 12963562817605324601322110976 }, { target := 142, numerator := 728290045932883404568657920 }, { target := 143, numerator := 14136669480529858489441320960 }, { target := 144, numerator := 19688107575052281370172719104 }, { target := 145, numerator := 1456580091865766809137315840 }, { target := 146, numerator := 19688107575052281370172719104 }, { target := 147, numerator := 19688107575052281370172719104 }, { target := 148, numerator := 12963562817605324601322110976 }, { target := 149, numerator := 728290045932883404568657920 }, { target := 177, numerator := 19688114120187663023243001856 }, { target := 180, numerator := 70432928351996052803495657472 }, { target := 182, numerator := 19688107575052281370172719104 }, { target := 191, numerator := 19688114120187663023243001856 }, { target := 194, numerator := 70432928351996052803495657472 }, { target := 196, numerator := 19688107575052281370172719104 }, { target := 232, numerator := 928455029464035206174343168 }, { target := 234, numerator := 928455029464035206174343168 }, { target := 248, numerator := 1044511908147039606946136064 }, { target := 250, numerator := 1044511908147039606946136064 }, { target := 253, numerator := 1044511908147039606946136064 }, { target := 255, numerator := 1044511908147039606946136064 }, { target := 259, numerator := 1102540347488541807332032512 }, { target := 261, numerator := 1102540347488541807332032512 }]

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
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2223218861915928152900632576 }, { target := 20, numerator := 1470053796651389076442710016 }, { target := 21, numerator := 37506919273899245044643135488 }, { target := 22, numerator := 11567002242072771943588691968 }, { target := 23, numerator := 1392682544196052809261514752 }, { target := 24, numerator := 37506910364121857442929704960 }, { target := 25, numerator := 1392682544196052809261514752 }, { target := 26, numerator := 1392682544196052809261514752 }, { target := 27, numerator := 59653235643064261996701548544 }, { target := 28, numerator := 1392682544196052809261514752 }, { target := 29, numerator := 11567002242072771943588691968 }, { target := 30, numerator := 59653235643064261996701548544 }, { target := 31, numerator := 2223227771693315754614063104 }, { target := 32, numerator := 1392682544196052809261514752 }, { target := 33, numerator := 1392682544196052809261514752 }, { target := 34, numerator := 1470053796651389076442710016 }, { target := 45, numerator := 1103593877936079507243925504 }, { target := 47, numerator := 40754253700400841037782712320 }, { target := 50, numerator := 40754243720712297160915288064 }, { target := 57, numerator := 1103603857624623384111349760 }, { target := 90, numerator := 2223218861915928152900632576 }, { target := 91, numerator := 1470053796651389076442710016 }, { target := 92, numerator := 37506919273899245044643135488 }, { target := 93, numerator := 11567002242072771943588691968 }, { target := 94, numerator := 1392682544196052809261514752 }, { target := 95, numerator := 37506910364121857442929704960 }, { target := 96, numerator := 1392682544196052809261514752 }, { target := 97, numerator := 1392682544196052809261514752 }, { target := 98, numerator := 59653235643064261996701548544 }, { target := 99, numerator := 1392682544196052809261514752 }, { target := 100, numerator := 11567002242072771943588691968 }, { target := 101, numerator := 59653235643064261996701548544 }, { target := 102, numerator := 2223227771693315754614063104 }, { target := 103, numerator := 1392682544196052809261514752 }, { target := 104, numerator := 1392682544196052809261514752 }, { target := 105, numerator := 1470053796651389076442710016 }, { target := 161, numerator := 1103593877936079507243925504 }, { target := 163, numerator := 40754253700400841037782712320 }, { target := 166, numerator := 40754243720712297160915288064 }, { target := 173, numerator := 1103603857624623384111349760 }, { target := 211, numerator := 12963567127225908821716107264 }, { target := 214, numerator := 46376305474680508257788755968 }, { target := 216, numerator := 12963562817605324601322110976 }, { target := 238, numerator := 728290288046399372006522880 }, { target := 241, numerator := 2605410419925871250437570560 }, { target := 243, numerator := 728290045932883404568657920 }]

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
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 220874525136779045934989312 }, { target := 1, numerator := 21446665160884356695162093568 }, { target := 2, numerator := 3520391986717800156744384512 }, { target := 3, numerator := 197908499950795658197708308480 }, { target := 4, numerator := 1856910058928070412348686336 }, { target := 5, numerator := 135399691796838467567091712 }, { target := 6, numerator := 3520391986717800156744384512 }, { target := 7, numerator := 3520391986717800156744384512 }, { target := 8, numerator := 1856910058928070412348686336 }, { target := 9, numerator := 43443958253671314022241140736 }, { target := 10, numerator := 3481706360490132023153786880 }, { target := 11, numerator := 21446665160884356695162093568 }, { target := 12, numerator := 3520391986717800156744384512 }, { target := 13, numerator := 135399691796838467567091712 }, { target := 14, numerator := 3481706360490132023153786880 }, { target := 15, numerator := 135399691796838467567091712 }, { target := 16, numerator := 3520391986717800156744384512 }, { target := 17, numerator := 3520391986717800156744384512 }, { target := 18, numerator := 240203171151164503794647040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent1
