import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent2Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
15, parent 64; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent2

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[37428343375268919248903208960, 29110933736320270526924718080, 33269638555794594887913963520, 39091825303058648993298907136, 461616234961650004069806243840, 1038012722940791360502915661824, 29110933736320270526924718080, 461616234961650004069806243840, 33269638555794594887913963520, 32437897591899730015716114432, 32437897591899730015716114432, 32437897591899730015716114432, 1038012722940791360502915661824, 32437897591899730015716114432, 37428343375268919248903208960, 39091825303058648993298907136], [21857378818632495478687662080, 367203964153025924041952722944, 795608588998222835424230899712, 26228854582358994574425194496, 419661673317743913190803111936, 30600330346085493670162726912, 795608588998222835424230899712, 795608588998222835424230899712, 419661673317743913190803111936, 9818334565329716969026497806336, 786865637470769837232755834880, 367203964153025924041952722944, 795608588998222835424230899712, 30600330346085493670162726912, 786865637470769837232755834880, 30600330346085493670162726912, 795608588998222835424230899712, 795608588998222835424230899712, 26228854582358994574425194496], [69324642199981295394350956544, 82323012612477788280791760896, 62825456993733048951130554368, 647752125556075228840966750208, 77990222474978957318644826112, 62825456993733048951130554368, 77990222474978957318644826112, 77990222474978957318644826112, 3340581196011598671815286718464, 77990222474978957318644826112, 647752125556075228840966750208, 3340581196011598671815286718464, 69324642199981295394350956544, 77990222474978957318644826112, 77990222474978957318644826112, 82323012612477788280791760896], [3481706360490132023153786880, 61974373216724350012137406464, 3481706360490132023153786880, 55127017374427090366601625600, 94122128611916569025924038656, 3481706360490132023153786880, 94122128611916569025924038656, 94122128611916569025924038656, 61974373216724350012137406464, 3481706360490132023153786880]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[31532808680677206362230492233728], [474576766137663553549168101294080, 474576620783223210821488423731200], [799765430201877826039911593017344, 2803811961721708172764088648073216, 799765424294197355969985430683648], [57894777985864271614820034281472, 5454673298101206836274266112, 2139349712478141234252474044383232, 134974149908334118097595138048, 4294104511271162828556337152, 2139265817932798754689310812798976, 4410161389954167229328130048, 4410161389954167229328130048, 74624572993171829696262832128, 4061990753905154027012751360, 134974149908334118097595138048, 74624572993171829696262832128, 57978683288757599155035062665216, 4294104511271162828556337152, 4061990753905154027012751360, 5454673298101206836274266112], [526737059575146121382441517056, 75173217847550179429456262725632, 59189008128332244393614376960, 778393725208960746305782873587712, 60736433177438969737238282240, 1934281311383406679529881600, 59189008128332244393614376960, 33656494818071276223819939840, 60736433177438969737238282240, 948184698840145954305547960320, 37138201178561408246973726720, 75173224624146082347397144379392, 59189008128332244393614376960, 1934281311383406679529881600, 37138201178561408246973726720, 1934281311383406679529881600, 59575864390608925729520353280, 33656494818071276223819939840, 526724762532824728826305052672], [166773663831980080864388186112, 13666780733293640141663828443136, 4061990753905154027012751360, 3597763239173136423925579776, 168398530969039385519871492096, 45842467079786738304858193920, 13666780199666227577393919295488, 168398530969039385519871492096, 4061990753905154027012751360, 4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360, 45842467079786738304858193920, 3481706360490132023153786880, 166774197459392645134297333760, 3597763239173136423925579776], [], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent2
