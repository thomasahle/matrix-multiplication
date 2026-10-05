import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 1, branch 2,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 472008208445405993811125993472, 0, 0, 0, 0, 0, 0, 13486787180778775476587986944, 0, 0, 0, 5753870964581013709672939520, 0, 0, 19672874668847953680913137664, 0, 5753869106071548283435614208, 0, 0, 0, 0, 520501170650020034956492800, 43581112728891652258324807680, 0, 0, 0, 0, 43581128500857835279991439360, 0, 0, 0, 0, 0, 0, 0, 520485398683837013289861120, 0, 3704980780513706075796537344, 388460552655257620392303394816, 0, 4187216491758086818426257408000, 0, 0, 0, 0, 0, 0, 0, 388460848982601498957933707264, 0, 0, 0, 0, 0, 0, 3704980780513706075796537344, 24338434026337278323968704512, 0, 851784510116213679306032807936, 0, 0, 851784927884238402624675643392, 0] }

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
  { lower := 576, upper := 640, values := [0, 0, 0, 0, 0, 24338225142324916664647286784, 0, 0, 0, 2048411557928042138209091584, 214772257400972183931428274176, 0, 2315030270163757372526297088000, 0, 0, 0, 0, 0, 0, 0, 214772421234576753078204104704, 0, 0, 0, 0, 0, 0, 2048411557928042138209091584, 379958610181864134853804425216, 0, 13297604040094520560376346574848, 0, 0, 13297610562065403342885859885056, 0, 0, 0, 0, 0, 0, 379955349196422743599047770112, 0, 0, 0, 269318282890550028797917265920, 0, 0, 920817456274141315838869766144, 0, 269318195900316663202099232768, 0, 0, 0, 0, 14882099786804959994273857536, 0, 520836388351315370785854455808, 0, 0, 520836643801827303515725234176, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 14881972061548993629338468352, 0, 0, 0, 73315452613209690816800358400, 0, 0, 250670499812740054966473850880, 0, 73315428932201986192163471360, 0, 0, 0, 0, 0, 0, 0, 0, 1078201339811121932311461888, 40707092588481298534735282176, 23594825072020431082390290432, 173588262400402319903261982720, 24211683243837958692387422208, 771072714771909512496414720, 23594825072020431082390290432, 13416665237031225517437616128, 24211683243837958692387422208, 377979844781190043025742495744, 14804596123620662639931162624, 40707104818672619404168003584, 23594825072020431082390290432, 771072714771909512496414720, 14804596123620662639931162624, 771072714771909512496414720, 23749039614974812984889573376, 13416665237031225517437616128, 1078201339811121932311461888, 40908824097189305862028525568, 15769796859753656443692122112, 880475168184338780141316472832, 390218590380712817957743362048, 12414520932146495498225713152, 880475593935192001357767770112, 12750048524907211592772354048, 12750048524907211592772354048, 215744242145140448793490096128, 11743465746625063309132431360, 390218590380712817957743362048, 215744242145140448793490096128, 40908611221762695253802876928, 12414520932146495498225713152, 11743465746625063309132431360, 15769796859753656443692122112, 8459565962659631358264999936, 43581128500857835279991439360, 1777651294113938017999650816, 59373785884809833870279049216, 35897087423075006427992948736, 8459563804390574734247460864, 35954431013207714105992937472, 32227097654581715035993669632, 43581128500857835279991439360] }

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
  { lower := 704, upper := 768, values := [1777651294113938017999650816, 23718346535220404990873960448, 0, 830082993934908872189955538944, 0, 0, 830083401059162264978187091968, 0, 0, 0, 0, 0, 0, 23718142973093708596758183936, 0, 0, 0, 269318282890550028797917265920, 0, 0, 920817456274141315838869766144, 0, 269318195900316663202099232768, 0, 0, 0, 0, 0, 0, 0, 0, 6496305927752757414146867200, 0, 0, 22211310109989625123611607040, 0, 6496303829435619029685370880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21230968802829764583751680, 1777650650783738447379038208, 0, 0, 0, 0, 1777651294113938017999650816, 0, 0, 0, 0, 0, 0, 0, 21230325472630193963139072, 0, 117871271607056857097568256, 12358590239247232978946883584] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent2
