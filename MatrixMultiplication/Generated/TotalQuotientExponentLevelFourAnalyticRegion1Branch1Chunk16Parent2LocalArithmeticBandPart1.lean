import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 68; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [46714329472234248493596672, 45485005012438610375344128, 1718595594794302089317056512, 45485005012438610375344128, 527380193252328752730341376, 1718595594794302089317056512, 261592350760385447561527296, 45485005012438610375344128, 45485005012438610375344128, 50402302851621162848354304, 0, 0, 0, 0, 0, 45485005012438610375344128, 0, 2055839478388243643580284928, 0, 0, 0, 0, 45727772234899160322539520, 0, 0, 0, 0, 0, 0, 1718595594794302089317056512, 0, 77677394345588232803384819712, 0, 0, 0, 0, 1727768259037541246781358080, 0, 0, 1117534624305688980618215424, 196005073818777285730272018432, 0, 0, 0, 0, 196005097317623392627027083264, 0, 0, 0, 0, 0, 0, 0, 1117511125459582083863150592, 0, 45485005012438610375344128, 0, 2055839478388243643580284928, 0, 0, 0, 0, 45727772234899160322539520, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band4

namespace Band5

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 320, upper := 384, values := [0, 1110461620354387151626960896, 194764535376886290250966499328, 0, 0, 0, 0, 194764558727005523053438304256, 0, 0, 0, 0, 0, 0, 0, 1110438270235154349155155968, 0, 149136502493184054207184896, 17626977103530488461415940096, 0, 167276499010081782076859744256, 0, 0, 0, 0, 0, 0, 0, 17626989193065385768813330432, 0, 0, 0, 0, 0, 0, 149136502493184054207184896, 0, 0, 0, 0, 527380193252328752730341376, 0, 23836625303474500624214654976, 0, 0, 0, 0, 530194980777614588604579840, 0, 0, 707300395130182899125452800, 124053844189099547930551910400, 0, 0, 0, 0, 124053859061786957358877900800, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band5

namespace Band6

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 384, upper := 448, values := [707285522442773470799462400, 0, 1718595594794302089317056512, 0, 77677394345588232803384819712, 0, 0, 0, 0, 1727768259037541246781358080, 0, 0, 17137888574004331645809721344, 3005824644701882046357272788992, 0, 0, 0, 0, 3005825005067097976805611536384, 0, 0, 0, 0, 0, 0, 0, 17137528208788401197470973952, 0, 1996602972153647746120679424, 235985652651346947565078708224, 0, 2239456803073747939641224331264, 0, 0, 0, 0, 0, 0, 0, 235985814503079450292684587008, 0, 0, 0, 0, 0, 0, 1996602972153647746120679424, 1096315612451783493644451840, 192283458493104299292355461120, 0, 0, 0, 0, 192283481545769783906260746240, 0, 0, 0, 0, 0, 0, 0, 1096292559786298879739166720, 0, 3491011599177185921951858688] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band6

namespace Band7

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 448, upper := 512, values := [412615157913254495209062924288, 0, 3915635599276812327390982176768, 0, 0, 0, 0, 0, 0, 0, 412615440907061172996507959296, 0, 0, 0, 0, 0, 0, 3491011599177185921951858688, 5265130997813344682112974848, 0, 205368457514760174517813772288, 0, 0, 205368382186327828020252901376, 0, 0, 0, 0, 0, 0, 5265156107290793514633265152, 0, 0, 0, 269086718698583463951335424, 5446713214438751911689584640, 6127013691340684461965574144, 4598157360791170055940341760, 224831038145940491694243840, 4598157360791170055940341760, 4590904746657430040079237120, 269322924644761296332390400, 5446713214438751911689584640, 224831038145940491694243840, 18226577500022676404450623488, 124840965128493726983925006336, 13925422322654363504563191808, 17956465626580626624305168384, 240396764306875327868248784896, 420327879054856708940367921152, 124474520031737280640350945280, 240396764306875327868248784896, 13558963840479248675495739392, 13925422322654363504563191808, 13925422322654363504563191808, 13558963840479248675495739392, 420327879054856708940367921152, 13558963840479248675495739392, 18226564114604007918957232128, 17956465626580626624305168384, 7549757616916634623109234688, 124239171086701467666858639360, 196005097317623392627027083264, 126926445122337061782146777088] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2
