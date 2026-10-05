import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
14, parent 61; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[], [39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [50968312554952766005612380160, 1219951223089514592779496325120, 912497208645122101068221644800, 1058825589851276816374657187840, 50968312554952766005612380160, 1057181450736600920697056788480, 1062113868080628607729857986560, 50968312554952766005612380160, 1219951223089514592779496325120, 50968312554952766005612380160], [1000990578640912956656713728000, 778548227831821188510777344000, 889769403236367072583745536000, 1045479048802731310285901004800, 12345550469904593132099469312000, 27760805380974652664612860723200, 778548227831821188510777344000, 12345550469904593132099469312000, 889769403236367072583745536000, 867525168155457895769151897600, 867525168155457895769151897600, 867525168155457895769151897600, 27760805380974652664612860723200, 867525168155457895769151897600, 1000990578640912956656713728000, 1045479048802731310285901004800], [194395271794032371292753100800, 3265840566139743837718252093440, 7075987893302778315056212869120, 233274326152838845551303720960, 3732389218445421528820859535360, 272153380511645319809854341120, 7075987893302778315056212869120, 7075987893302778315056212869120, 3732389218445421528820859535360, 87322356089879341184704692879360, 6998229784585165366539111628800, 3265840566139743837718252093440, 7075987893302778315056212869120, 272153380511645319809854341120, 6998229784585165366539111628800, 272153380511645319809854341120, 7075987893302778315056212869120, 7075987893302778315056212869120, 233274326152838845551303720960], [74276402357122816493947453440, 88203227799083344586562600960, 67312989636142552447639879680, 694020134524366316615321518080, 83560952651763168555690885120, 67312989636142552447639879680, 83560952651763168555690885120, 83560952651763168555690885120, 3579194138583855719802092912640, 83560952651763168555690885120, 694020134524366316615321518080, 3579194138583855719802092912640, 74276402357122816493947453440, 83560952651763168555690885120, 83560952651763168555690885120, 88203227799083344586562600960], []]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [79228162514264337593543950336, 79228162514264337593543950336], [1450323555868933901084434366464, 5259853712233955661619771998208, 1450323470866337209430820519936], [2453175053857918884482283208704, 91352969363031056826273753989120, 91349601673486929098964639678464, 2456542743402046611791397519360], [278072186877148886856311504896, 43357174342563390115262844895232, 438329158896971154380571721859072, 43357174342563390115262844895232, 278050350654532097616843374592], [623155679730048681745431134208, 52380485042312793168335471640576, 52380475238679974730952008007680, 623165483362867119128894767104], [122034742963742735601292541952, 1182037439329272605481206022144, 122034742963742735601292541952], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent3
