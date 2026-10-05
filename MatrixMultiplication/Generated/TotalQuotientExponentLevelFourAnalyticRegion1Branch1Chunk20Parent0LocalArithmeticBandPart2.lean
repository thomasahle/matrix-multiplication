import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 82; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 87146845611733214684742942720, 0, 0, 0, 269563578562103901929078784000, 0, 0, 969612175826972046841085952000, 0, 269563668489981261263142912000, 0, 0, 0, 0, 283989021364109636664966512640, 0, 11113899005654411060932427907072, 0, 0, 11113899005654411060932427907072, 0, 0, 0, 0, 0, 0, 283989021364109636664966512640, 0, 0, 0, 6531525508559777543741578936320, 0, 0, 23493703020287532694959512616960, 0, 6531527687512245960405952757760, 0, 0, 0, 0, 298188771415990143678020583424, 0, 298188842509741803754632511488, 0, 417823546771261047990072115200, 0, 0, 1502898872531806672603683225600, 0, 417823686159470954957871513600, 0, 0, 0, 0, 521375793923994961583368306688, 0, 521375918229685745284395565056, 0, 0, 46075064017455804788867334144, 8358359081890844620735119360, 1518384415054102725986718056448] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band8

namespace Band9

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 576, upper := 640, values := [87456976734906642495008931840, 7746771831996392575315476480, 1518383965484100636975480963072, 7746771831996392575315476480, 7542909415364908560175595520, 284999658450814653165553582080, 7542909415364908560175595520, 87456976734906642495008931840, 284999658450814653165553582080, 46075213874123167792613031936, 7542909415364908560175595520, 7542909415364908560175595520, 8358359081890844620735119360, 919581936458793290137493045248, 42842600004678581047263232000, 2218634643099426518518988800, 3377348256043413015587140403200, 59673621435088023601545216000, 919581790031767351013943541760, 59750126077953521067701043200, 59750126077953521067701043200, 42766095361813083581107404800, 2218634643099426518518988800, 202554170519969270164728315904, 10315736108847847225216204800, 202554174313081020321254866944, 10315736108847847225216204800, 425910454128124165047944478720, 0, 0, 1531987237806615834008915804160, 0, 425910596214170392795765800960, 0, 0, 0, 0, 298188771415990143678020583424, 0, 298188842509741803754632511488, 0, 0, 16818573997548224567205429248, 0, 16818578007409217589819211776, 0, 0, 7025304129891729911316480, 2263000515277793794782658560, 0, 24067962135861592486752288768, 0, 0, 0, 0, 0, 0, 0, 2263007335961415048889368576, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band9

namespace Band10

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 640, upper := 704, values := [0, 7025304129891729911316480, 7516161509636664203579228160, 0, 294144680407162524502503456768, 0, 0, 294144680407162524502503456768, 0, 0, 0, 0, 0, 0, 7516161509636664203579228160, 0, 0, 0, 16173814713726234115744727040, 0, 0, 58176730549618322810465157120, 0, 16173820109398875675788574720, 0, 0, 0, 0, 7516161509636664203579228160, 0, 294144680407162524502503456768, 0, 0, 294144680407162524502503456768, 0, 0, 0, 0, 0, 0, 7516161509636664203579228160, 0, 0, 0, 417823546771261047990072115200, 0, 0, 1502898872531806672603683225600, 0, 417823686159470954957871513600, 0, 0, 0, 0, 17273130051536014420373143552, 0, 17273134169771628876030541824, 0, 16173814713726234115744727040, 0, 0, 58176730549618322810465157120, 0, 16173820109398875675788574720] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band10

namespace Band11

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 17273130051536014420373143552, 0, 17273134169771628876030541824, 0, 0, 8328719510678465739101306880, 0, 325944105316044959583855181824, 0, 0, 325944105316044959583855181824, 0, 0, 0, 0, 0, 0, 8328719510678465739101306880, 0, 0, 0, 425910454128124165047944478720, 0, 0, 1531987237806615834008915804160, 0, 425910596214170392795765800960, 0, 0, 0, 0, 16818573997548224567205429248, 0, 16818578007409217589819211776, 0, 425910454128124165047944478720, 0, 0, 1531987237806615834008915804160, 0, 425910596214170392795765800960, 0, 0, 0, 0, 521375793923994961583368306688, 0, 521375918229685745284395565056, 0, 0, 16818573997548224567205429248, 0, 16818578007409217589819211776, 0, 0, 21890014507423252880329539584, 133001024771445867151360000, 6887553068521303834624000, 79154704006450076183135518720, 185251427360228172103680000] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent0
