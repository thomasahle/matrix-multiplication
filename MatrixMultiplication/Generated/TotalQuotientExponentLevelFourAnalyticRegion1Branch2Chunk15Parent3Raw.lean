import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
15, parent 65; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[1547425049106725343623905280, 25996740824992985772881608704, 56326271787484802507910152192, 1856910058928070412348686336, 29710560942849126597578981376, 2166395068749415481073467392, 56326271787484802507910152192, 56326271787484802507910152192, 29710560942849126597578981376, 695103332058741024355858251776, 55707301767842112370460590080, 25996740824992985772881608704, 56326271787484802507910152192, 2166395068749415481073467392, 55707301767842112370460590080, 2166395068749415481073467392, 56326271787484802507910152192, 56326271787484802507910152192, 1856910058928070412348686336], [3713820117856140824697372672, 4410161389954167229328130048, 3365649481807127622381993984, 34701006726218315830766075904, 4178047632588158427784544256, 3365649481807127622381993984, 4178047632588158427784544256, 4178047632588158427784544256, 178959706929192785990104645632, 4178047632588158427784544256, 34701006726218315830766075904, 178959706929192785990104645632, 3713820117856140824697372672, 4178047632588158427784544256, 4178047632588158427784544256, 4410161389954167229328130048], []]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[238239084680392863143786658660352], [985756984507618762792641899790336, 985756611497335013885105760370688], [763364059605908411977800366424064, 2644000814017485551832298118184960, 763364057452509295789242148978688], [26175805703746118548740267573248, 5454673298101206836274266112, 959115481929531848233575864336384, 134974149908334118097595138048, 4294104511271162828556337152, 959090215087115180545906502008832, 4410161389954167229328130048, 4410161389954167229328130048, 74624572993171829696262832128, 4061990753905154027012751360, 134974149908334118097595138048, 74624572993171829696262832128, 26201085003765568046533703630848, 4294104511271162828556337152, 4061990753905154027012751360, 5454673298101206836274266112], [142051754173236653034815094784, 18948610733534266956428768968704, 47351206502665795514891501568, 197626752993049100019123571654656, 48589146541951175789790625792, 1547425049106725343623905280, 47351206502665795514891501568, 26925195854457020979055951872, 48589146541951175789790625792, 758547759072116763444438368256, 29710560942849126597578981376, 18948614450036688974839552147456, 47351206502665795514891501568, 1547425049106725343623905280, 29710560942849126597578981376, 1547425049106725343623905280, 47660691512487140583616282624, 26925195854457020979055951872, 142049997452905025526795599872], [], [], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent3
