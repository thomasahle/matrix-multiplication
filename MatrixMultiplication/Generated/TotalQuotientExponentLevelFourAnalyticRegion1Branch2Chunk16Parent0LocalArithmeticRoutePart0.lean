import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent0

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
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected,
    Slot3.Left12.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 56833364056033799877395742720 }, { target := 19, numerator := 203317607472471376080289136640 }, { target := 21, numerator := 56833345162296204152253972480 }, { target := 26, numerator := 870205148913418282385086087168 }, { target := 28, numerator := 870205148913418282385086087168 }, { target := 40, numerator := 7350268983256945382213550080 }, { target := 42, numerator := 7350268983256945382213550080 }, { target := 44, numerator := 408857772442737495826231197696 }, { target := 45, numerator := 299813603264428035327131648 }, { target := 47, numerator := 299813603264428035327131648 }, { target := 49, numerator := 2727336649050603418137133056 }, { target := 50, numerator := 56807665271130079274555408384 }, { target := 53, numerator := 203225671766247429321321873408 }, { target := 55, numerator := 56807646385935812042535469056 }, { target := 60, numerator := 2980425965935982259134540021760 }, { target := 62, numerator := 2980425965935982259134540021760 }, { target := 64, numerator := 14213668886229828298316344983552 }, { target := 65, numerator := 6054300504630062906928529408 }, { target := 67, numerator := 6054300504630062906928529408 }, { target := 69, numerator := 67487074954167059048797569024 }, { target := 70, numerator := 2147052255635581414278168576 }, { target := 71, numerator := 870204867932612551641195872256 }, { target := 73, numerator := 870204867932612551641195872256 }, { target := 75, numerator := 14213675856442757013912680398848 }, { target := 76, numerator := 2205080694977083614664065024 }, { target := 87, numerator := 6063971911186979940326178816 }, { target := 89, numerator := 6063971911186979940326178816 }, { target := 91, numerator := 2205080694977083614664065024 }, { target := 92, numerator := 5435330484987372769478967296 }, { target := 94, numerator := 5435330484987372769478967296 }, { target := 96, numerator := 37312286496585914848131416064 }, { target := 97, numerator := 2030995376952577013506375680 }, { target := 98, numerator := 7350268983256945382213550080 }, { target := 100, numerator := 7350268983256945382213550080 }, { target := 102, numerator := 67487074954167059048797569024 }, { target := 103, numerator := 37312286496585914848131416064 }, { target := 104, numerator := 408854287336273138028063490048 }, { target := 105, numerator := 299813603264428035327131648 }, { target := 107, numerator := 299813603264428035327131648 }, { target := 109, numerator := 2147052255635581414278168576 }, { target := 110, numerator := 2030995376952577013506375680 }, { target := 111, numerator := 2727336649050603418137133056 }]

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
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 519707972903488589180147073024 }, { target := 1, numerator := 735026898325694538221355008 }, { target := 2, numerator := 19486582973548200531264213614592 }, { target := 3, numerator := 5783501121036385971794345984 }, { target := 4, numerator := 696341272098026404630757376 }, { target := 5, numerator := 19485184803614151383927213785088 }, { target := 6, numerator := 696341272098026404630757376 }, { target := 7, numerator := 696341272098026404630757376 }, { target := 8, numerator := 29826617821532130998350774272 }, { target := 9, numerator := 696341272098026404630757376 }, { target := 10, numerator := 5783501121036385971794345984 }, { target := 11, numerator := 29826617821532130998350774272 }, { target := 12, numerator := 521106142837537736517146902528 }, { target := 13, numerator := 696341272098026404630757376 }, { target := 14, numerator := 696341272098026404630757376 }, { target := 15, numerator := 735026898325694538221355008 }, { target := 16, numerator := 46489636918666009774965731098624 }, { target := 19, numerator := 160590460289570992918205950853120 }, { target := 21, numerator := 46489636918666009774965731098624 }, { target := 26, numerator := 76033075905644943469538082553856 }, { target := 28, numerator := 76033061764120964266478614347776 }, { target := 44, numerator := 2503057599911130261660362604544 }, { target := 50, numerator := 46489636918666009774965731098624 }, { target := 53, numerator := 160590460289570992918205950853120 }, { target := 55, numerator := 46489636918666009774965731098624 }, { target := 60, numerator := 260712612997524828681324690669568 }, { target := 62, numerator := 260712565061577753571369878028288 }, { target := 64, numerator := 91382314979492109786689218543616 }, { target := 71, numerator := 71226441975763498891144551464960 }, { target := 73, numerator := 71226427834239519688085083258880 }, { target := 75, numerator := 91380952005355457466817996390400 }, { target := 104, numerator := 2504420574047782581531584757760 }]

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
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot22.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2377295370300929960481124253696 }, { target := 2, numerator := 85645191426326417478438185074688 }, { target := 5, numerator := 85645224662341723915001199067136 }, { target := 12, numerator := 2377265647726286778934149251072 }, { target := 16, numerator := 30651887215415760222024848375808 }, { target := 17, numerator := 7350268983256945382213550080 }, { target := 18, numerator := 299813603264428035327131648 }, { target := 19, numerator := 103933357321471074898457531514880 }, { target := 20, numerator := 6054300504630062906928529408 }, { target := 21, numerator := 30651886922629038284106845126656 }, { target := 22, numerator := 6063971911186979940326178816 }, { target := 23, numerator := 5435330484987372769478967296 }, { target := 24, numerator := 7350268983256945382213550080 }, { target := 25, numerator := 299813603264428035327131648 }, { target := 26, numerator := 63937534563038024862070210560 }, { target := 28, numerator := 63908623430021339183874834432 }, { target := 44, numerator := 618970019642690137449562112 }, { target := 49, numerator := 735026898325694538221355008 }, { target := 50, numerator := 30651873031835204129142154985472 }, { target := 51, numerator := 7350268983256945382213550080 }, { target := 52, numerator := 299813603264428035327131648 }, { target := 53, numerator := 103933309242963562390406198984704 }, { target := 54, numerator := 6054300504630062906928529408 }, { target := 55, numerator := 30651872739048482191224151736320 }, { target := 56, numerator := 6063971911186979940326178816 }, { target := 57, numerator := 5435330484987372769478967296 }, { target := 58, numerator := 7350268983256945382213550080 }, { target := 59, numerator := 299813603264428035327131648 }, { target := 60, numerator := 228732308406530298090325278720 }, { target := 62, numerator := 228628880737028357986487107584 }, { target := 64, numerator := 560941580301187937063665664 }, { target := 69, numerator := 5783501121036385971794345984 }, { target := 70, numerator := 696341272098026404630757376 }, { target := 71, numerator := 4870571443189027808064816807936 }, { target := 73, numerator := 4870542532065622366941383491584 }, { target := 75, numerator := 560941580301187937063665664 }, { target := 76, numerator := 696341272098026404630757376 }, { target := 91, numerator := 696341272098026404630757376 }, { target := 96, numerator := 29826617821532130998350774272 }, { target := 97, numerator := 696341272098026404630757376 }, { target := 102, numerator := 5783501121036385971794345984 }, { target := 103, numerator := 29826617821532130998350774272 }, { target := 104, numerator := 618970019642690137449562112 }, { target := 109, numerator := 696341272098026404630757376 }, { target := 110, numerator := 696341272098026404630757376 }, { target := 111, numerator := 735026898325694538221355008 }]

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
    Slot25.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2785365088392105618523029504 }, { target := 1, numerator := 2727336649050603418137133056 }, { target := 2, numerator := 2147052255635581414278168576 }, { target := 3, numerator := 67487074954167059048797569024 }, { target := 4, numerator := 2147052255635581414278168576 }, { target := 5, numerator := 2147052255635581414278168576 }, { target := 6, numerator := 2205080694977083614664065024 }, { target := 7, numerator := 2205080694977083614664065024 }, { target := 8, numerator := 37312286496585914848131416064 }, { target := 9, numerator := 2030995376952577013506375680 }, { target := 10, numerator := 67487074954167059048797569024 }, { target := 11, numerator := 37312286496585914848131416064 }, { target := 12, numerator := 2785365088392105618523029504 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2030995376952577013506375680 }, { target := 15, numerator := 2727336649050603418137133056 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent0
