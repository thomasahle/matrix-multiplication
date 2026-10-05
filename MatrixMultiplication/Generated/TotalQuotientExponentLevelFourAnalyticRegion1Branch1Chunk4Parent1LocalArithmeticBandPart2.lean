import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 1,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 75575002376778121088241500160, 0, 0, 0, 299250346691532573136178380800, 0, 0, 1072631398011285943273232793600, 0, 299337308332444854704406528000, 0, 0, 0, 0, 277614568212852552916298366976, 0, 10864750912750076336752918790144, 0, 0, 10864754897571920122315198693376, 0, 0, 0, 0, 0, 0, 277618553034696338478578270208, 0, 0, 0, 7640235413968191007883054284800, 0, 0, 27385620380475644239194724761600, 0, 7642455653362732696671879168000, 0, 0, 0, 0, 292279473029267294139795374080, 0, 292279682083912038480930144256, 0, 489399004485110562316458393600, 0, 0, 1754199265497623886394766131200, 0, 489541223002019189464498176000, 0, 0, 0, 0, 528648564748114872604326625280, 0, 528648942867169052493501956096, 0, 0, 42097140128251900237742866432, 6662783584854494302489804800, 1447808843969074750434607890432] }

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
  { lower := 576, upper := 640, values := [75194271886215007128099225600, 6662783584854494302489804800, 1447808633406454839963897823232, 6662783584854494302489804800, 6662783584854494302489804800, 276219970903539178083220193280, 6853148830136051282560942080, 75194271886215007128099225600, 276219970903539178083220193280, 42097225262281643416537268224, 6662783584854494302489804800, 6853148830136051282560942080, 6662783584854494302489804800, 835232703653801015511198203904, 33729366946540522878781095936, 1750426228762582025645326336, 3057126070244209457402891730944, 54330537177361680565222244352, 835379215050292651809885388800, 54330537177361680565222244352, 56619556091897364752604594176, 33729366946540522878781095936, 1683102143040944255428198400, 202683546185375322810777337856, 10289738697373026695658864640, 202683557564710573280356990976, 10289738697373026695658864640, 476930240039630038435784294400, 0, 0, 1709506290580486972091714764800, 0, 477068835154833987185147904000, 0, 0, 0, 0, 292279473029267294139795374080, 0, 292279682083912038480930144256, 0, 0, 17273125933300399964715745280, 0, 17273138288007243331687940096, 0, 0, 5225040258878230495232000, 1683097070186323985301504000, 0, 17900445131472448773108531200, 0, 0, 0, 0, 0, 0, 0, 1683102143040944255428198400, 0, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 5225040258878230495232000, 6696423078876526086885212160, 0, 262071869018781992960959447040, 0, 0, 262071965137847832033791836160, 0, 0, 0, 0, 0, 0, 6696519197942365159717601280, 0, 0, 0, 15585955556850654850842624000, 0, 0, 55866218646421142878814208000, 0, 15590484808981502849187840000, 0, 0, 0, 0, 6887749452558712546510503936, 0, 269559636705032907045558288384, 0, 0, 269559735570357770091900174336, 0, 0, 0, 0, 0, 0, 6887848317883575592852389888, 0, 0, 0, 489399004485110562316458393600, 0, 0, 1754199265497623886394766131200, 0, 489541223002019189464498176000, 0, 0, 0, 0, 17273125933300399964715745280, 0, 17273138288007243331687940096, 0, 15585955556850654850842624000, 0, 0, 55866218646421142878814208000, 0, 15590484808981502849187840000] }

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
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 16818569987687231544591646720, 0, 16818582017270210612432994304, 0, 0, 6696423078876526086885212160, 0, 262071869018781992960959447040, 0, 0, 262071965137847832033791836160, 0, 0, 0, 0, 0, 0, 6696519197942365159717601280, 0, 0, 0, 476930240039630038435784294400, 0, 0, 1709506290580486972091714764800, 0, 477068835154833987185147904000, 0, 0, 0, 0, 16818569987687231544591646720, 0, 16818582017270210612432994304, 0, 498750577819220955226963968000, 0, 0, 1787718996685476572122054656000, 0, 498895513887408091174010880000, 0, 0, 0, 0, 528648564748114872604326625280, 0, 528648942867169052493501956096, 0, 0, 16818569987687231544591646720, 0, 16818582017270210612432994304, 0, 0, 22140056515601048158341169152, 104709806787919739124449280, 5434041869233359715041280, 79653682009116061822166761472, 168664299556589280386088960] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent1
