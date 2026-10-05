import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
10, parent 43; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240], [29246333428117108994491809792, 610517210311944650260016529408, 31683527880460201410699460608, 656823904906463406167961894912, 983407961520437789939787104256, 30464930654288655202595635200, 983407961520437789939787104256, 1024840267210270361015317168128, 610517210311944650260016529408, 30464930654288655202595635200], [783113131726686028274467864576, 884159987433355193213108879360, 757851417800018737039807610880, 9978377001033580037690800209920, 884159987433355193213108879360, 757851417800018737039807610880, 884159987433355193213108879360, 884159987433355193213108879360, 36654746907594239581492028112896, 909421701360022484447769133056, 9978377001033580037690800209920, 36654746907594239581492028112896, 783113131726686028274467864576, 884159987433355193213108879360, 909421701360022484447769133056, 884159987433355193213108879360], [160738776975961095068933160960, 2330712266151435878499530833920, 4125628609049668106769284464640, 133948980813300912557444300800, 2571820431615377521102930575360, 133948980813300912557444300800, 4098838812887007924257795604480, 4286367386025629201838217625600, 2571820431615377521102930575360, 65661790394680107335659196252160, 4205997997537648654303751045120, 2330712266151435878499530833920, 4098838812887007924257795604480, 133948980813300912557444300800, 4205997997537648654303751045120, 133948980813300912557444300800, 4098838812887007924257795604480, 4286367386025629201838217625600, 160738776975961095068933160960], [104547904880273131028590100480, 77854822783182118851077734400, 82303669799363954213996462080, 106772328388364048710049464320, 1430304315702460069178370949120, 2587004539909737263537240145920, 77854822783182118851077734400, 1430304315702460069178370949120, 84528093307454871895455825920, 84528093307454871895455825920, 82303669799363954213996462080, 82303669799363954213996462080, 2587004539909737263537240145920, 82303669799363954213996462080, 104547904880273131028590100480, 106772328388364048710049464320], [], [232113757366008801543585792, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 3868562622766813359059763200, 232113757366008801543585792, 6112328943971565107314425856, 6073643317743896973723828224, 3868562622766813359059763200, 93735272349639887690018062336, 5996272065288560706542632960, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 5996272065288560706542632960, 232113757366008801543585792, 6112328943971565107314425856, 6112328943971565107314425856, 232113757366008801543585792]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[17747108403195211620953844875264], [243864257835044091320220470214656, 243864310602767170905636088053760], [499602483232509867310505967747072, 1818274467273599673157755147911168, 499634964826158833033348846190592], [33591432465799570998454340550656, 1325924037477631986008920896307200, 1325924156188480632386062278197248, 33591683195125612479397316526080], [166252640415558590038315892736, 30551857936442999032002618851328, 316561320379782522074085785075712, 30551879758498516372633151340544, 166252640415558590038315892736], [21946069583547270285446086656, 4295988787443859128562699206656, 4295988839389890440128796557312, 21946017637515958719348736000], [], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent1
