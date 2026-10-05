import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
7, parent 31; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[], [39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [5996272065288560706542632960, 143523673304648775621117214720, 107352612781779070713908428800, 124567716453091390161724375040, 5996272065288560706542632960, 124374288321953049493771386880, 124954572715368071497630351360, 5996272065288560706542632960, 143523673304648775621117214720, 5996272065288560706542632960], [40039623145636518266268549120, 31141929113272847540431093760, 35590776129454682903349821440, 41819161952109252411436040192, 493822018796183725283978772480, 1110432215238986106584514428928, 31141929113272847540431093760, 493822018796183725283978772480, 35590776129454682903349821440, 34701006726218315830766075904, 34701006726218315830766075904, 34701006726218315830766075904, 1110432215238986106584514428928, 34701006726218315830766075904, 40039623145636518266268549120, 41819161952109252411436040192]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [435754893828453856764491726848, 435754893828453856764491726848], [4213284854583773626090035085312, 14391141142164246803457039663104, 4213284807360108797393582948352], [5668806451466663666011250622464, 41819161952109252411436040192, 205193346184938025191842485633024, 1034801815963894905414896058368, 32921467919745581685598584832, 205188141173711140337409369047040, 33811237322981948758182330368, 33811237322981948758182330368, 572121726280984027671348379648, 31141929113272847540431093760, 1034801815963894905414896058368, 572121726280984027671348379648, 5674019726834893542323491176448, 32921467919745581685598584832, 31141929113272847540431093760, 41819161952109252411436040192], [952658484673723824264840216576, 105773141248426378290812344598528, 3477354227539519358124844646400, 1077783101919788005294308254023680, 3568265449174539472062749081600, 113639027043775142422380544000, 3477354227539519358124844646400, 1977319070561687478149421465600, 3568265449174539472062749081600, 55705851056858574815450942668800, 2181869319240482734509706444800, 105773176727565764090456835096576, 3477354227539519358124844646400, 113639027043775142422380544000, 2181869319240482734509706444800, 113639027043775142422380544000, 3500082032948274386609320755200, 1977319070561687478149421465600, 952652935893106452431714123776], [2863485733184608469703186186240, 139013224406073651700061515546624, 1219951223089514592779496325120, 1080528226164998639318982459392, 50575692134368162117801404792832, 13768020946295950404225744240640, 139013253599743248800208226615296, 50575692134368162117801404792832, 1219951223089514592779496325120, 1219951223089514592779496325120, 1045672476933869650953853992960, 1219951223089514592779496325120, 13768020946295950404225744240640, 1045672476933869650953853992960, 2863456539515011369556475117568, 1080528226164998639318982459392], [833303826360004098411676565504, 1618355144795154866562266038272, 10005870949262500913000103280640, 2606811580538303347935626133504, 80756244750257228870372556800, 2606811580538303347935626133504, 1741104636815545854445232324608, 836534076150014387566491467776, 1618355144795154866562266038272, 77525994960246939715557654528], [186271290286222063238727598080, 170255441027967455932220178432, 186271290286222063238727598080, 170255441027967455932220178432], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1
