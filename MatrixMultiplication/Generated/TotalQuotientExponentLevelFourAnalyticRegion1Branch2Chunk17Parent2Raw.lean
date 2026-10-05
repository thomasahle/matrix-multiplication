import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17Parent2Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
17, parent 72; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent2

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[92265218552988498613575352320, 71761836652324387810558607360, 82013527602656443212066979840, 96365894933121320774178701312, 1137937695486858149567429345280, 2558822061202881028216489771008, 71761836652324387810558607360, 1137937695486858149567429345280, 82013527602656443212066979840, 79963189412590032131765305344, 79963189412590032131765305344, 79963189412590032131765305344, 2558822061202881028216489771008, 79963189412590032131765305344, 92265218552988498613575352320, 96365894933121320774178701312], [87913085602375833584633118720, 1476939838119914004221836394496, 3200036315926480342480645521408, 105495702722851000301559742464, 1687931243565616004824955879424, 123078319843326167018486366208, 3200036315926480342480645521408, 3200036315926480342480645521408, 1687931243565616004824955879424, 39490558052587224446217196929024, 3164871081685530009046792273920, 1476939838119914004221836394496, 3200036315926480342480645521408, 123078319843326167018486366208, 3164871081685530009046792273920, 123078319843326167018486366208, 3200036315926480342480645521408, 3200036315926480342480645521408, 105495702722851000301559742464], [677153201489103010369820950528, 804119426768309824814162378752, 613670088849499603147650236416, 6327150226413806253143014506496, 761797351675240886666048569344, 613670088849499603147650236416, 761797351675240886666048569344, 761797351675240886666048569344, 32630319896756151312195747053568, 761797351675240886666048569344, 6327150226413806253143014506496, 32630319896756151312195747053568, 677153201489103010369820950528, 761797351675240886666048569344, 761797351675240886666048569344, 804119426768309824814162378752], [35397347998316342235396833280, 630072794370030891790063632384, 35397347998316342235396833280, 560458009973342085393783193600, 956908307554485118430227726336, 35397347998316342235396833280, 956908307554485118430227726336, 956908307554485118430227726336, 630072794370030891790063632384, 35397347998316342235396833280], [37370314935927417048517312512, 41857847578336920545026637824, 37370314935927417048517312512, 41857847578336920545026637824]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[18222477378280797646515108577280], [273139125638451260547385419366400, 273139054897401347160100118200320], [472153585373971507565307126349824, 1681314150091072244385166590476288, 472153570257676395899572797308928], [33267474847752374225261016645632, 1238621831786925813877648432037888, 1238566303278675379692915407192064, 33323003932131519320090757562368], [253130214940303733559780179968, 39013139712119067480722545573888, 5918900812833224439361437696, 395740295329224199250398465228800, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696, 3365649481807127622381993984, 6073643317743896973723828224, 94818469884014595430554796032, 3713820117856140824697372672, 39013140080463653144554872242176, 5918900812833224439361437696, 193428131138340667952988160, 3713820117856140824697372672, 193428131138340667952988160, 5957586439060892572952035328, 3365649481807127622381993984, 253112529677825386738454888448], [58179923413539692865061388288, 4777484669418749337826052014080, 1353996917968384675670917120, 1199254413057712141308526592, 56132843656346461839957164032, 15280822359928912768286064640, 4777483847726981318507784830976, 56132843656346461839957164032, 1353996917968384675670917120, 1353996917968384675670917120, 1160568786830044007717928960, 1353996917968384675670917120, 15280822359928912768286064640, 1160568786830044007717928960, 58180745105307712183328571392, 1199254413057712141308526592], [], [], []]

/-- Exact pooled-row entropy form for this compatibility branch. -/
def expectedPooled : Form :=
  weightedEntropyForm 116 expectedPooledNumerators

/-- Sum of the individually charged boundary-row entropy forms. -/
def expectedFirst : Form :=
  Form.sum (expectedFirstNumerators.map (weightedEntropyForm 116))

/-- Sum of the pooled compatibility-cell entropy forms. -/
def expectedGroups : Form :=
  Form.sum (expectedGroupsNumerators.map (weightedEntropyForm 116))

/-- The one compatibility record selected by this logical branch. -/
def actualCompatibility :
    MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows :=
  logicalZRows Top.expectedRows BetaThree.expectedRows
    (Orientation.order 1) 1 1 parent

/-- The serialized local records are exactly the slice consumed from the global caches. -/
theorem localData_realizes :
    localData.Realizes Top.expectedRows BetaThree.expectedRows
      1 1 parent coordinate := by
  rfl

/-- Filtering the dense padded row produces its compact nonzero sufficient statistic. -/
theorem pooledNumerators_eq :
    dropZeros actualCompatibility.pooled = expectedPooledNumerators := by
  have hscatter :
      localData.scatter parent coordinate = actualCompatibility.pooled := by
    calc
      _ = betaFourParentRow Top.expectedRows BetaThree.expectedRows
            1 1 parent coordinate :=
        localData.scatter_eq_global Top.expectedRows BetaThree.expectedRows
          1 1 parent coordinate localData_realizes
      _ = actualCompatibility.pooled := by
        rw [show coordinate = (Orientation.order 1).y by rfl]
        exact (logicalZRows_pooled Top.expectedRows BetaThree.expectedRows
          (Orientation.order 1) 1 1 parent).symm
  rw [← hscatter, ← localData.scatterOn_range_eq_scatter parent coordinate]
  exact pooledNumerators_eq_local

/-- The pooled-row entropy form can therefore be checked on only its nonzero numerators. -/
theorem pooledForm_eq :
    weightedEntropyForm 116 actualCompatibility.pooled = expectedPooled := by
  calc
    _ = weightedEntropyForm 116
          (dropZeros actualCompatibility.pooled) :=
      (weightedEntropyForm_dropZeros 116 actualCompatibility.pooled).symm
    _ = expectedPooled := by
      rw [pooledNumerators_eq]
      rfl

/-- Removing zero padding from every boundary row produces the compact row family. -/
theorem firstNumerators_eq :
    actualCompatibility.first.map dropZeros = expectedFirstNumerators := by
  unfold actualCompatibility logicalZRows parent expectedFirstNumerators
  rfl

/-- The boundary-row family is therefore represented by the compact numerator rows. -/
theorem firstForm_eq :
    Form.sum (actualCompatibility.first.map (weightedEntropyForm 116)) =
      expectedFirst := by
  calc
    _ = Form.sum ((actualCompatibility.first.map dropZeros).map
          (weightedEntropyForm 116)) :=
      (sum_map_weightedEntropyForm_dropZeros 116 actualCompatibility.first).symm
    _ = expectedFirst := by rw [firstNumerators_eq]; rfl

/-- Removing zero padding from every pooled cell produces the compact row family. -/
theorem groupsNumerators_eq :
    actualCompatibility.groups.map dropZeros = expectedGroupsNumerators := by
  unfold actualCompatibility logicalZRows parent expectedGroupsNumerators
  rfl

/-- The pooled cell family is therefore represented by the compact numerator rows. -/
theorem groupsForm_eq :
    Form.sum (actualCompatibility.groups.map (weightedEntropyForm 116)) =
      expectedGroups := by
  calc
    _ = Form.sum ((actualCompatibility.groups.map dropZeros).map
          (weightedEntropyForm 116)) :=
      (sum_map_weightedEntropyForm_dropZeros 116 actualCompatibility.groups).symm
    _ = expectedGroups := by rw [groupsNumerators_eq]; rfl

/-- Unnormalized compatibility sufficient statistic assembled from the three checked pieces. -/
def expectedRaw : Form := Form.sub (Form.sub expectedPooled expectedFirst) expectedGroups

/-- The actual compatibility record has the assembled small raw form. -/
theorem compatibilityForm_eq : actualCompatibility.form 116 = expectedRaw := by
  unfold MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows.form expectedRaw
  rw [pooledForm_eq, firstForm_eq, groupsForm_eq]

/-- Selecting this parent and branch exposes exactly the checked compatibility record. -/
theorem branchForm_eq_actualCompatibility :
    branchFormOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region1.dualWeights 1 [parent] 2 =
      Form.sum [Form.scaleNat 1 (actualCompatibility.form 116)] := by
  rfl

/-- The semantic recurrence produces the small raw compatibility form before normalization. -/
theorem raw_eq :
    branchFormOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region1.dualWeights 1 [parent] 2 =
      expectedRaw := by
  rw [branchForm_eq_actualCompatibility, compatibilityForm_eq]
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17.Parent2
