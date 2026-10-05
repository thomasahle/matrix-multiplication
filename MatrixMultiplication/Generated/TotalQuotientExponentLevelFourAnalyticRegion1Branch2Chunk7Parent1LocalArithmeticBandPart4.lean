import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [515952718917355818788585472, 931087090460055902871355392, 14535633495016541515526701056, 569327138115702972456370176, 37131844484624950961603870720, 907365126371901612352339968, 29652455110192863148769280, 569327138115702972456370176, 29652455110192863148769280, 913295617393940184982093824, 515952718917355818788585472, 312732785435476659489734656, 19253006247277985852414754816, 229719517559193891420241920, 696443628360402937107642843136, 5684336147262606291951943680, 180843024461493063458488320, 696421318331155446254580793344, 185730673771263146254663680, 185730673771263146254663680, 3142758506182163237940756480, 171067725841952897866137600, 5684336147262606291951943680, 3142758506182163237940756480, 19275340474573440150010855424, 180843024461493063458488320, 171067725841952897866137600, 229719517559193891420241920, 78678567251550332729843253248, 0, 0, 267046437183988875011477733376, 0, 78678567072847499515781971968, 0, 0, 0, 0, 7248250791625366806466658304, 239929273895158064372252672, 263317720393902770373739413504, 5936973309363166571594252288, 188880492215337199612198912, 263297819403065852938835460096, 193985370383319286088204288, 193985370383319286088204288, 3282436662012481604071456768, 178670735879373026660188160, 5936973309363166571594252288, 3282436662012481604071456768, 7268151782462284241370611712, 188880492215337199612198912, 178670735879373026660188160, 239929273895158064372252672, 161292917859688232763585986560, 0, 0, 553508202922848703923699580928, 0, 161292913582349450672183705600, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [51297140377887945141132460032, 0, 51297140377887945141132460032, 0, 7645493857475945761173667840, 0, 0, 26238032219152683101220503552, 0, 7645493678773112547112386560, 0, 0, 0, 0, 47738062764942476850797477888, 0, 47738062764942476850797477888, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1
