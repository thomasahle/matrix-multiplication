import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
8, parent 34; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[26983224293798523179441848320, 30464930654288655202595635200, 26112797703675990173653401600, 343818503098400537286436454400, 30464930654288655202595635200, 26112797703675990173653401600, 30464930654288655202595635200, 30464930654288655202595635200, 1262988982267795391399036190720, 31335357244411188208384081920, 343818503098400537286436454400, 1262988982267795391399036190720, 26983224293798523179441848320, 30464930654288655202595635200, 31335357244411188208384081920, 30464930654288655202595635200], [178843650050509781589332852736, 2593232925732391833045326364672, 4590320351296417727459543220224, 149036375042091484657777377280, 2861498400808156505429325643776, 149036375042091484657777377280, 4560513076287999430527987744768, 4769164001346927509048876072960, 2861498400808156505429325643776, 73057631045633245779242470342656, 4679742176321672618254209646592, 2593232925732391833045326364672, 4560513076287999430527987744768, 149036375042091484657777377280, 4679742176321672618254209646592, 149036375042091484657777377280, 4560513076287999430527987744768, 4769164001346927509048876072960, 178843650050509781589332852736], [1316394489275091249820856221696, 980293768609110505185743994880, 1036310555386773962624929366016, 1344402882663922978540448907264, 18009396949018801566698096820224, 32573761511211300500886293315584, 980293768609110505185743994880, 18009396949018801566698096820224, 1064318948775605691344522051584, 1064318948775605691344522051584, 1036310555386773962624929366016, 1036310555386773962624929366016, 32573761511211300500886293315584, 1036310555386773962624929366016, 1316394489275091249820856221696, 1344402882663922978540448907264], [84547436120568705962251124736, 2072775853278458597784221122560, 1532763196766439120993068777472, 1710040078954728343171982426112, 84547436120568705962251124736, 1707312742305677739753845293056, 1737313445445234377353353756672, 84547436120568705962251124736, 2072775853278458597784221122560, 84547436120568705962251124736], [198844118810214206655671828480, 198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000], [], [39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [7195526478346272847851159552, 174317431781872609959232929792, 132072727941259008078300315648, 147160122170049580178633392128, 7195526478346272847851159552, 147160122170049580178633392128, 146928008412683571377089806336, 7195526478346272847851159552, 174317431781872609959232929792, 7195526478346272847851159552], [41780476325881584277845442560, 31335357244411188208384081920, 33076210424656254219960975360, 42650902916004117283633889280, 570999843120381651797221048320, 998379298870545357639348387840, 30464930654288655202595635200, 570999843120381651797221048320, 32205783834533721214172528640, 33076210424656254219960975360, 33076210424656254219960975360, 32205783834533721214172528640, 998379298870545357639348387840, 32205783834533721214172528640, 41780476325881584277845442560, 42650902916004117283633889280]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [475368899527722299646940282880, 475369050643449751475587121152], [3556210876760209857859781918720, 13011526524116616674086318243840, 3556215877746315216814063222784], [4600760304108955864137140797440, 180793111305060310120269965426688, 180793135700805560624857139380224, 4600793256782273328521441968128], [530766980738266107648808058880, 105996376876524361950570213277696, 1098726249934872417776560811016192, 105996525975801325593878545301504, 530766980738266107648808058880], [665720031113154764171588403200, 127366990591938014786995435339776, 127366994870402048266893998948352, 665715752649121284273024794624], [169522203906538768989534814208, 7662095214876602183554860843008, 170426995157557144403543326720], [], []]

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
  logicalYRows Top.expectedRows BetaThree.expectedRows
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
        rw [show coordinate = (Orientation.order 1).z by rfl]
        exact (logicalYRows_pooled Top.expectedRows BetaThree.expectedRows
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
  unfold actualCompatibility logicalYRows parent expectedFirstNumerators
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
  unfold actualCompatibility logicalYRows parent expectedGroupsNumerators
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
      Orientation.order Weights.Region1.dualWeights 1 [parent] 1 =
      Form.sum [Form.scaleNat 1 (actualCompatibility.form 116)] := by
  rfl

/-- The semantic recurrence produces the small raw compatibility form before normalization. -/
theorem raw_eq :
    branchFormOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region1.dualWeights 1 [parent] 1 =
      expectedRaw := by
  rw [branchForm_eq_actualCompatibility, compatibilityForm_eq]
  rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0
