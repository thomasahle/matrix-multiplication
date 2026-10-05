import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1886315135129784298162356224, 994979411936589519909814272, 23278372491766458976223363072, 1865586397381105349830901760, 31985398735118574502453182464, 1886315135129784298162356224, 72550582120376319160090624, 1865586397381105349830901760, 72550582120376319160090624, 1886315135129784298162356224, 1886315135129784298162356224, 284381322034686209638268928, 19208825854976573502318968832, 169580180399848959623823360, 704645236714237356322144124928, 1334328261567232603355873280, 160654907747225330169937920, 704621837020786104739565666304, 160654907747225330169937920, 160654907747225330169937920, 6881385215172818308945674240, 160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240, 19232225548427825084897427456, 160654907747225330169937920, 160654907747225330169937920, 169580180399848959623823360, 83033054140858339947823759360, 0, 0, 300369708009051037742670020608, 0, 83033053931026626109377609728, 0, 0, 0, 0, 7535536099573008244290879488, 150199588354151935666814976, 268621131428228913032924758016, 1181833603102406020115202048, 142294346861828149579087872, 268621230103321727819136892928, 142294346861828149579087872, 142294346861828149579087872, 6094941190581639073637597184, 142294346861828149579087872, 1181833603102406020115202048, 6094941190581639073637597184, 7535437424480193458078744576, 142294346861828149579087872, 142294346861828149579087872, 150199588354151935666814976, 199729331054854706721179303936, 0, 0, 687394667986808682374898909184, 0, 199729327011558990064966959104, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band16

namespace Band17

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1088, upper := 1107, values := [49962495717766360271547269120, 0, 49962476828300428792966414336, 0, 8418984495368217817644007424, 0, 0, 28985155469627281376725172224, 0, 8418984301677405043693715456, 0, 0, 0, 0, 49072726314529993198963523584, 0, 49072707425064061720382668800, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent2
