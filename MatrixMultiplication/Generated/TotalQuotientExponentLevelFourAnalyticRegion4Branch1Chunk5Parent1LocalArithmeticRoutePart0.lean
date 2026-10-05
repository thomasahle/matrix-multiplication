import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 89181497670528046485995520 }, { target := 17, numerator := 3030959639137774049471496192 }, { target := 19, numerator := 33373588838363295517719396352 }, { target := 27, numerator := 3031006862594311263157747712 }, { target := 34, numerator := 89169691806393743064432640 }, { target := 35, numerator := 2170513263122157550826422272 }, { target := 37, numerator := 73420182344379477405177217024 }, { target := 40, numerator := 73421578708296896986600177664 }, { target := 47, numerator := 2169112919607934442719412224 }, { target := 86, numerator := 3315238446021528375730896896 }, { target := 89, numerator := 11335764621563097403506032640 }, { target := 91, numerator := 3315381887487425525625913344 }, { target := 122, numerator := 181182624472943282519801856 }, { target := 124, numerator := 181183445223576073307947008 }, { target := 126, numerator := 89182284387458453235302400 }, { target := 127, numerator := 3030986376828054813058007040 }, { target := 129, numerator := 33373883244356168306644746240 }, { target := 137, numerator := 3031033600701174992276029440 }, { target := 144, numerator := 89170478419178408430796800 }, { target := 145, numerator := 7032796792641289690646839296 }, { target := 147, numerator := 238067107894624729418273128448 }, { target := 150, numerator := 238071829468878544187812741120 }, { target := 157, numerator := 7028064264851243670758752256 }, { target := 161, numerator := 120959553820641373045693349888 }, { target := 164, numerator := 413548958028782547661278412800 }, { target := 166, numerator := 120964597903546486404774100992 }, { target := 197, numerator := 6136144106990434183729381376 }, { target := 199, numerator := 6136171903497816490396090368 }, { target := 216, numerator := 2166438938319859621539348480 }, { target := 218, numerator := 73283782782967140020547223552 }, { target := 221, numerator := 73285178129870151275119640576 }, { target := 228, numerator := 2165039635083951665418600448 }, { target := 232, numerator := 21138847983823742450050007040 }, { target := 235, numerator := 73262825010650926002305236992 }, { target := 237, numerator := 21143730897136603915987451904 }, { target := 242, numerator := 66593381547324888640359759872 }, { target := 244, numerator := 66593683212896869619016400896 }, { target := 406, numerator := 603130880929435025890344960 }, { target := 409, numerator := 2090325462478682900668612608 }, { target := 411, numerator := 603270199581527223929143296 }, { target := 416, numerator := 6136134662278860542668963840 }, { target := 418, numerator := 6136162458743458652875653120 }, { target := 498, numerator := 181140123270861897747922944 }, { target := 500, numerator := 181140943828965804465979392 }]

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
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
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
  [{ target := 16, numerator := 183259104762649807977185280 }, { target := 17, numerator := 9002257311858072187589099520 }, { target := 19, numerator := 100471607616985222395608432640 }, { target := 27, numerator := 9002271479003119742751866880 }, { target := 34, numerator := 183230770472554697651650560 }, { target := 35, numerator := 2713193549540550968675926016 }, { target := 37, numerator := 99819578382795962184680603648 }, { target := 40, numerator := 99819688388526041719761797120 }, { target := 47, numerator := 2713083543810471433594732544 }, { target := 86, numerator := 1991661952339203608681644032 }, { target := 89, numerator := 6428040587099726176157958144 }, { target := 91, numerator := 1987717890398717906880823296 }, { target := 122, numerator := 272440602433177854463180800 }, { target := 124, numerator := 272440209459770419228704768 }, { target := 126, numerator := 183257925072311965993402368 }, { target := 127, numerator := 9002199361798874196986560512 }, { target := 129, numerator := 100470960853022871285802205184 }, { target := 137, numerator := 9002213528852723859695075328 }, { target := 144, numerator := 183229590964612640576372736 }, { target := 145, numerator := 9249202954002307989966422016 }, { target := 147, numerator := 340282225498348128420545691648 }, { target := 150, numerator := 340282600504887481690352517120 }, { target := 157, numerator := 9248827947462954720159596544 }, { target := 161, numerator := 66236657945527096247240884224 }, { target := 164, numerator := 213777205076203483646297899008 }, { target := 166, numerator := 66105490363919637412495491072 }, { target := 197, numerator := 12033216950995846237060595712 }, { target := 199, numerator := 12033185738626929010044567552 }, { target := 216, numerator := 2713197923208514339766009856 }, { target := 218, numerator := 99819739291954899251172999168 }, { target := 221, numerator := 99819849297862308021581905920 }, { target := 228, numerator := 2713087917301105569357103104 }, { target := 232, numerator := 166056346334053137967002681344 }, { target := 235, numerator := 554059805581090965336650416128 }, { target := 237, numerator := 165925339661781945434077396992 }, { target := 242, numerator := 133845196455348517913327828992 }, { target := 244, numerator := 133844844097379039592446951424 }, { target := 406, numerator := 4704729229252529671381188608 }, { target := 409, numerator := 15676816033547157749819768832 }, { target := 411, numerator := 4700789573015800340017053696 }, { target := 416, numerator := 12033278341597431005909614592 }, { target := 418, numerator := 12033247129553898851971104768 }, { target := 498, numerator := 272400462278948440716083200 }, { target := 500, numerator := 272400069383791049007169536 }]

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
    Slot22.Left0.expected,
    Slot22.Left2.expected,
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
  [{ target := 16, numerator := 181182624472943282519801856 }, { target := 17, numerator := 6136144106990434183729381376 }, { target := 19, numerator := 66593381547324888640359759872 }, { target := 27, numerator := 6136134662278860542668963840 }, { target := 34, numerator := 181140123270861897747922944 }, { target := 35, numerator := 602044896480977407054970880 }, { target := 37, numerator := 21139975437845410861012746240 }, { target := 40, numerator := 21138847983823742450050007040 }, { target := 47, numerator := 603130880929435025890344960 }, { target := 86, numerator := 178851310782953942144778240 }, { target := 89, numerator := 604756205541563514488881152 }, { target := 91, numerator := 178721047921141714658525184 }, { target := 126, numerator := 181183445223576073307947008 }, { target := 127, numerator := 6136171903497816490396090368 }, { target := 129, numerator := 66593683212896869619016400896 }, { target := 137, numerator := 6136162458743458652875653120 }, { target := 144, numerator := 181140943828965804465979392 }, { target := 145, numerator := 2086561667560789413539610624 }, { target := 147, numerator := 73266732530434419240732721152 }, { target := 150, numerator := 73262825010650926002305236992 }, { target := 157, numerator := 2090325462478682900668612608 }, { target := 161, numerator := 7183524398852381157936332800 }, { target := 164, numerator := 24289902818421245771975229440 }, { target := 166, numerator := 7178292419047502608051732480 }, { target := 216, numerator := 602183964278911185859903488 }, { target := 218, numerator := 21144858611591587153601101824 }, { target := 221, numerator := 21143730897136603915987451904 }, { target := 228, numerator := 603270199581527223929143296 }, { target := 232, numerator := 7184920762769800739359293440 }, { target := 235, numerator := 24294624392675060541514842112 }, { target := 237, numerator := 7179687765950513862624149504 }, { target := 406, numerator := 177467234165876204932956160 }, { target := 409, numerator := 600076178767040641098579968 }, { target := 411, numerator := 177337979369256894758649856 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent1
