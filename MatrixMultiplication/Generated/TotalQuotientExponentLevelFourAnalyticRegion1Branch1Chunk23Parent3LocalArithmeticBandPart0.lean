import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk23Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 97; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [13946073807744704766506172416, 2379166013001590215821754368, 465368854042529401899579342848, 24894200477504443965549576192, 2205080694977083614664065024, 465368797374131607463836778496, 2205080694977083614664065024, 2147052255635581414278168576, 81123758199420076139483234304, 2147052255635581414278168576, 24894200477504443965549576192, 81123758199420076139483234304, 13946092697210636245087027200, 2147052255635581414278168576, 2147052255635581414278168576, 2379166013001590215821754368, 95326568344781482682635780096, 37911909183662472859945533440, 1963295297011092344532893696, 374843682566669613768491663360, 52805873505815587197781278720, 95326557221394806235776155648, 52873573343643555899316895744, 52873573343643555899316895744, 37844209345834504158409916416, 1963295297011092344532893696, 88318349810611751442540658688, 33342941102143313407842975744, 88318350262556981248424673280, 33342941102143313407842975744, 33342941102143313407842975744, 0, 0, 119933567594597773178497400832, 0, 33342952225529989854702600192, 0, 0, 0, 0, 37911909183662472859945533440, 0, 37911918222567068977625825280, 0, 14933095626329289312620773376, 1963295297011092344532893696, 0, 1963295765097223214912765952, 0, 2379166013001590215821754368, 95326568796726712488519794688, 37911918222567068977625825280, 1963295765097223214912765952, 374843690976079068370833506304, 52805886095718417504550256640, 95326557673340036041660170240, 52873585949687287270581731328, 52873585949687287270581731328, 37844218368598199211594350592, 1963295765097223214912765952, 349246036016693666017087324160, 119933567594597773178497400832, 349246044426103120619429167104, 119933567594597773178497400832] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band0

namespace Band1

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 64, upper := 128, values := [503995913481076986150236717056, 52805873505815587197781278720, 0, 52805886095718417504550256640, 0, 24894200477504443965549576192, 2205080694977083614664065024, 88318341048408316430503641088, 33342952225529989854702600192, 88318341500353546236387655680, 33342952225529989854702600192, 503995856812679191714494152704, 2205080694977083614664065024, 33342941102143313407842975744, 0, 0, 119933567594597773178497400832, 0, 33342952225529989854702600192, 0, 0, 0, 0, 52873573343643555899316895744, 0, 52873585949687287270581731328, 0, 2147052255635581414278168576, 52873573343643555899316895744, 0, 52873585949687287270581731328, 0, 81123758199420076139483234304, 2147052255635581414278168576, 37844209345834504158409916416, 0, 37844218368598199211594350592, 0, 24894200477504443965549576192, 81123758199420076139483234304, 14933114515795220791201628160, 1963295297011092344532893696, 0, 1963295765097223214912765952, 0, 2147052255635581414278168576, 2147052255635581414278168576, 2379166013001590215821754368, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band1

namespace Band2

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 128, upper := 192, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band2

namespace Band3

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent3
