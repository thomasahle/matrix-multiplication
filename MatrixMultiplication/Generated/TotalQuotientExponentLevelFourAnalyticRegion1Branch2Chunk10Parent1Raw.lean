import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
10, parent 43; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[], [6595899271817416777196896256, 157876040635113653183228936192, 118087874059956977785299271680, 137024488098400529177896812544, 6595899271817416777196896256, 136811717154148354443148525568, 137450029986904878647393386496, 6595899271817416777196896256, 157876040635113653183228936192, 6595899271817416777196896256], [85301805832008234567267778560, 66345848980450849107874938880, 75823827406229541837571358720, 89092997202319711659146346496, 1052055605261434892996302602240, 2365703415074361705332226392064, 66345848980450849107874938880, 1052055605261434892996302602240, 75823827406229541837571358720, 73928231721073803291632074752, 73928231721073803291632074752, 73928231721073803291632074752, 2365703415074361705332226392064, 73928231721073803291632074752, 85301805832008234567267778560, 89092997202319711659146346496], [11122117540454588407296819200, 186851574679637085242586562560, 404845078472547018025604218880, 13346541048545506088756183040, 213544656776728097420098928640, 15570964556636423770215546880, 404845078472547018025604218880, 404845078472547018025604218880, 213544656776728097420098928640, 4996055199172201112557731184640, 400396231456365182662685491200, 186851574679637085242586562560, 404845078472547018025604218880, 15570964556636423770215546880, 400396231456365182662685491200, 15570964556636423770215546880, 404845078472547018025604218880, 404845078472547018025604218880, 13346541048545506088756183040]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[158456325028528675187087900672], [5823270539816605654700777275392, 5823269349780251971550183424000], [76270140066469548462922239311872, 264833680454997348838170282688512, 76270139603677633141697008369664], [38501859949739315110750025940992, 104547904880273131028590100480, 1406610813085997224255625208266752, 2587004539909737263537240145920, 82303669799363954213996462080, 1406570691713965402780930645426176, 84528093307454871895455825920, 84528093307454871895455825920, 1430304315702460069178370949120, 77854822783182118851077734400, 2587004539909737263537240145920, 1430304315702460069178370949120, 38542014954465227583057800724480, 82303669799363954213996462080, 77854822783182118851077734400, 104547904880273131028590100480], [1888472647002904322145463042048, 226182052800930572635156460339200, 4098838812887007924257795604480, 2333003284438611658537706222256128, 4205997997537648654303751045120, 133948980813300912557444300800, 4098838812887007924257795604480, 2330712266151435878499530833920, 4205997997537648654303751045120, 65661790394680107335659196252160, 2571820431615377521102930575360, 226182118215151093345481960456192, 4098838812887007924257795604480, 133948980813300912557444300800, 2571820431615377521102930575360, 133948980813300912557444300800, 4125628609049668106769284464640, 2330712266151435878499530833920, 1888455830655858823338857070592], [2688476658885288288636310126592, 152173915007466789619751479934976, 884159987433355193213108879360, 783113131726686028274467864576, 36654746907594239581492028112896, 9978377001033580037690800209920, 152173942902485603930745757237248, 36654746907594239581492028112896, 884159987433355193213108879360, 884159987433355193213108879360, 757851417800018737039807610880, 884159987433355193213108879360, 9978377001033580037690800209920, 757851417800018737039807610880, 2688448763866473977642032824320, 783113131726686028274467864576], [525383610451689749585615388672, 610517210311944650260016529408, 5818658771156764816577986035712, 983407961520437789939787104256, 30464930654288655202595635200, 983407961520437789939787104256, 656823904906463406167961894912, 526602207677861295793719214080, 610517210311944650260016529408, 29246333428117108994491809792], [41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent1
