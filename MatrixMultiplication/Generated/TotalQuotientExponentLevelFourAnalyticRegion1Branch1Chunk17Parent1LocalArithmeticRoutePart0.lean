import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk17Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2089023816294079213892272128 }, { target := 1, numerator := 2379166013001590215821754368 }, { target := 2, numerator := 1856910058928070412348686336 }, { target := 3, numerator := 24894200477504443965549576192 }, { target := 4, numerator := 2205080694977083614664065024 }, { target := 5, numerator := 1856910058928070412348686336 }, { target := 6, numerator := 2205080694977083614664065024 }, { target := 7, numerator := 2147052255635581414278168576 }, { target := 8, numerator := 81123758199420076139483234304 }, { target := 9, numerator := 2147052255635581414278168576 }, { target := 10, numerator := 24894200477504443965549576192 }, { target := 11, numerator := 81123758199420076139483234304 }, { target := 12, numerator := 2089023816294079213892272128 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2147052255635581414278168576 }, { target := 15, numerator := 2379166013001590215821754368 }, { target := 16, numerator := 813223858612508639489219887104 }, { target := 17, numerator := 5415987671873538702683668480 }, { target := 18, numerator := 280470790150593968531832832 }, { target := 19, numerator := 2974364740699277444228545773568 }, { target := 20, numerator := 7543697114395286050166538240 }, { target := 21, numerator := 813223584715350586341692801024 }, { target := 22, numerator := 7553368520952203083564187648 }, { target := 23, numerator := 7553368520952203083564187648 }, { target := 24, numerator := 5406316265316621669286019072 }, { target := 25, numerator := 280470790150593968531832832 }, { target := 26, numerator := 7121057027225501686407391870976 }, { target := 28, numerator := 7121058709953993338577701830656 }, { target := 44, numerator := 1162089034660041818253348044800 }, { target := 50, numerator := 813224440082056362083116646400 }, { target := 51, numerator := 5415987671873538702683668480 }, { target := 52, numerator := 280470790150593968531832832 }, { target := 53, numerator := 2974366864527449982897611603968 }, { target := 54, numerator := 7543697114395286050166538240 }, { target := 55, numerator := 813224166184702402351798943744 }, { target := 56, numerator := 7553368520952203083564187648 }, { target := 57, numerator := 7553368520952203083564187648 }, { target := 58, numerator := 5406316265316621669286019072 }, { target := 59, numerator := 280470790150593968531832832 }, { target := 60, numerator := 25528367780293320577280446038016 }, { target := 62, numerator := 25528373811856640150743680024576 }, { target := 64, numerator := 45503282545193014575896698290176 }, { target := 71, numerator := 7123108075887224752974237532160 }, { target := 73, numerator := 7123109759104714437934668840960 }, { target := 75, numerator := 45503298549293025021124327505920 }, { target := 104, numerator := 1162105312657308269920399654912 }]

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
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2608375760543691294780468232192 }, { target := 2, numerator := 102052011530607130994117338726400 }, { target := 5, numerator := 102052024861847712135125776990208 }, { target := 12, numerator := 2608393209687845498119532838912 }, { target := 16, numerator := 76037134369081197111886213021696 }, { target := 19, numerator := 278617238282550501616956288794624 }, { target := 21, numerator := 76029927635068762293116833103872 }, { target := 26, numerator := 69568107154906390001796813684736 }, { target := 28, numerator := 69568103159020884589196001411072 }, { target := 44, numerator := 1457646548463385791395893608448 }, { target := 49, numerator := 2379166013001590215821754368 }, { target := 50, numerator := 76037131428430292891733007007744 }, { target := 53, numerator := 278617226442816416937846985719808 }, { target := 55, numerator := 76029924697134707465470500405248 }, { target := 60, numerator := 255468921849770919151954181488640 }, { target := 62, numerator := 255468906274721547686067505725440 }, { target := 64, numerator := 56937456173733446981645959692288 }, { target := 69, numerator := 24894200477504443965549576192 }, { target := 70, numerator := 2205080694977083614664065024 }, { target := 71, numerator := 69558846179920598990659457646592 }, { target := 73, numerator := 69558842186246726349617329340416 }, { target := 75, numerator := 56937453127807065530724796858368 }, { target := 76, numerator := 2205080694977083614664065024 }, { target := 91, numerator := 2147052255635581414278168576 }, { target := 104, numerator := 1455558539955885529155722280960 }]

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
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot20.Left10.expected,
    Slot20.Left11.expected,
    Slot20.Left12.expected,
    Slot20.Left13.expected,
    Slot20.Left14.expected,
    Slot20.Left15.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected,
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected,
    Slot23.Left8.expected,
    Slot23.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 29966867383706876591552331776 }, { target := 2, numerator := 1198069797980751325067380523008 }, { target := 5, numerator := 1198069505194029387149377273856 }, { target := 12, numerator := 29966867383706876591552331776 }, { target := 16, numerator := 63183025139082972747421188096 }, { target := 19, numerator := 230160638534725227849298477056 }, { target := 21, numerator := 63183067640381318574228111360 }, { target := 26, numerator := 270799383593676935134183424 }, { target := 28, numerator := 270799383593676935134183424 }, { target := 40, numerator := 5415987671873538702683668480 }, { target := 42, numerator := 5415987671873538702683668480 }, { target := 45, numerator := 280470790150593968531832832 }, { target := 47, numerator := 280470790150593968531832832 }, { target := 50, numerator := 63183025139082972747421188096 }, { target := 53, numerator := 230160638534725227849298477056 }, { target := 55, numerator := 63183067640381318574228111360 }, { target := 60, numerator := 5038802816153774400175341568 }, { target := 62, numerator := 5038802816153774400175341568 }, { target := 65, numerator := 7543697114395286050166538240 }, { target := 67, numerator := 7543697114395286050166538240 }, { target := 71, numerator := 270799383593676935134183424 }, { target := 73, numerator := 270799383593676935134183424 }, { target := 87, numerator := 7553368520952203083564187648 }, { target := 89, numerator := 7553368520952203083564187648 }, { target := 92, numerator := 7553368520952203083564187648 }, { target := 94, numerator := 7553368520952203083564187648 }, { target := 96, numerator := 81123758199420076139483234304 }, { target := 97, numerator := 2147052255635581414278168576 }, { target := 98, numerator := 5406316265316621669286019072 }, { target := 100, numerator := 5406316265316621669286019072 }, { target := 102, numerator := 24894200477504443965549576192 }, { target := 103, numerator := 81123758199420076139483234304 }, { target := 104, numerator := 2089023816294079213892272128 }, { target := 105, numerator := 280470790150593968531832832 }, { target := 107, numerator := 280470790150593968531832832 }, { target := 109, numerator := 2147052255635581414278168576 }, { target := 110, numerator := 2147052255635581414278168576 }, { target := 111, numerator := 2379166013001590215821754368 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent1
