import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk11Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [416403268778762755211224154112, 53637620764661867223363616768, 12832474754652840344362772594688, 1327245807431952161293018857472, 42225361027499767814137315328, 12832439492742312756721961926656, 43366587001215977755059945472, 43366587001215977755059945472, 733808301099522992013251182592, 39942909080067347932292055040, 1327245807431952161293018857472, 733808301099522992013251182592, 416440854093599914717479960576, 42225361027499767814137315328, 39942909080067347932292055040, 53637620764661867223363616768, 10080369750814180485226525884416, 205807580599533706769386700800, 8394782892875716986646036480, 34459259165715895614861370982400, 169520454546458026891626414080, 10080368537165994387727705964544, 169791253994615308084744028160, 152189289864392030532099112960, 205807580599533706769386700800, 8394782892875716986646036480, 10106273655417014595262986846208, 24451235683033492999611875328, 10105976844505764346576410509312, 24691424638662505700983308288, 27944269352038277713842143232, 0, 0, 101639331294988084553229271040, 0, 27944269352038277713842143232, 0, 0, 0, 0, 213157851335231339154007654400, 0, 213157749693671493014378250240, 0, 415364636216886888312569069568, 8694596567621278307597680640, 0, 8694592421715547741375954944, 0, 52728508548311666083984572416, 10080072940045892503111198572544, 205807482462855234634572103680, 8394778889932252991673335808, 34458240197733312157376520912896, 169520373712825495896371232768, 10080071726397706405612378652672, 169791173031855568573521985536, 152189217294900844558723055616, 205807482462855234634572103680, 8394778889932252991673335808, 34552841629420428111339442929664, 88934414883114573984075612160, 34551822658500200660116346765312, 89808033889824933257003663360] }

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
  { lower := 64, upper := 128, values := [12831869262267139764192762920960, 175574756494545813566327357440, 0, 175574672773997835035527348224, 0, 1304750115780563141610086334464, 41509676942287907342711259136, 10106272425240545807720408678400, 24451235683033492999611875328, 10105975614329295559033832341504, 24691424638662505700983308288, 12831833986189512727943016611840, 42631560102890283216838590464, 28218771015614292229695209472, 0, 0, 102637753016942780865147043840, 0, 28218771015614292229695209472, 0, 0, 0, 0, 175855227351565854802056314880, 0, 175855143497278981736862056448, 0, 42631560102890283216838590464, 157624621645263174479674081280, 0, 157624546484004446150106021888, 0, 721370872267327687063874043904, 39265910621083155594456596480, 213157851335231339154007654400, 0, 213157749693671493014378250240, 0, 1304750115780563141610086334464, 721370872267327687063874043904, 415402207364624599209889234944, 8694596567621278307597680640, 0, 8694592421715547741375954944, 0, 41509676942287907342711259136, 39265910621083155594456596480, 52728508548311666083984572416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent1
