import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk17Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 71; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [2640431651743692250585912836096, 2379166013001590215821754368, 103251938238646810389597067935744, 24894200477504443965549576192, 2205080694977083614664065024, 103251951277100669592687502950400, 2205080694977083614664065024, 2147052255635581414278168576, 81123758199420076139483234304, 2147052255635581414278168576, 24894200477504443965549576192, 81123758199420076139483234304, 2640449100887846453924977442816, 2147052255635581414278168576, 2147052255635581414278168576, 2379166013001590215821754368, 76913541252832788724122854096896, 5415987671873538702683668480, 280470790150593968531832832, 281821763661784504289034133045248, 7543697114395286050166538240, 76906334287424494198032754016256, 7553368520952203083564187648, 7553368520952203083564187648, 5406316265316621669286019072, 280470790150593968531832832, 76689434981515485365139339739136, 0, 76689432668358471604708837425152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5415987671873538702683668480, 0, 5415987671873538702683668480, 0, 2619735583123427609649241653248, 280470790150593968531832832, 0, 280470790150593968531832832, 0, 2379166013001590215821754368, 76913538893651432226563544842240, 5415987671873538702683668480, 280470790150593968531832832, 281821753945878592148593895800832, 7543697114395286050166538240, 76906331930959791186396527460352, 7553368520952203083564187648, 7553368520952203083564187648, 5406316265316621669286019072, 280470790150593968531832832, 281002328432880393503634802868224, 0, 281002318889394341611211361091584, 0] }

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
  { lower := 64, upper := 128, values := [102440738718926461557542657982464, 7543697114395286050166538240, 0, 7543697114395286050166538240, 0, 24894200477504443965549576192, 2205080694977083614664065024, 76682225055191417420568829362176, 0, 76682222744735034464487132364800, 0, 102440751677100090551849124364288, 2205080694977083614664065024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7553368520952203083564187648, 0, 7553368520952203083564187648, 0, 2147052255635581414278168576, 7553368520952203083564187648, 0, 7553368520952203083564187648, 0, 81123758199420076139483234304, 2147052255635581414278168576, 5406316265316621669286019072, 0, 5406316265316621669286019072, 0, 24894200477504443965549576192, 81123758199420076139483234304, 2619752876429487878290014208000, 280470790150593968531832832, 0, 280470790150593968531832832, 0, 2147052255635581414278168576, 2147052255635581414278168576, 2379166013001590215821754368, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17.Parent1
