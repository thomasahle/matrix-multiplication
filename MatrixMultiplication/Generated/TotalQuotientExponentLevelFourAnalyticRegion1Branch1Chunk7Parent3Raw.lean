import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk7Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
7, parent 33; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[2785365088392105618523029504, 58144496220185204786668240896, 3017478845758114420066615296, 62554657610139372015996370944, 93657901097184551422836867072, 2901421967075110019294822400, 93657901097184551422836867072, 97603834972406701049077825536, 58144496220185204786668240896, 2901421967075110019294822400], [382562157765410173077419982848, 431925016831914711539022561280, 370221442998784038462019338240, 4874582332817323173083254620160, 431925016831914711539022561280, 370221442998784038462019338240, 431925016831914711539022561280, 431925016831914711539022561280, 17906377126374521326946335326208, 444265731598540846154423205888, 4874582332817323173083254620160, 17906377126374521326946335326208, 382562157765410173077419982848, 431925016831914711539022561280, 444265731598540846154423205888, 431925016831914711539022561280], [531424447489477151134039670784, 7705654488597418691443575226368, 13639894152229913545773684883456, 442853706241230959278366392320, 8502791159831634418144634732544, 442853706241230959278366392320, 13551323410981667353918011604992, 14171318599719390696907724554240, 8502791159831634418144634732544, 217086886799451416238255205515264, 13905606375974652121340704718848, 7705654488597418691443575226368, 13551323410981667353918011604992, 442853706241230959278366392320, 13905606375974652121340704718848, 442853706241230959278366392320, 13551323410981667353918011604992, 14171318599719390696907724554240, 531424447489477151134039670784], [1097298445134692775230506532864, 817137139993920151767398481920, 863830690850715589011249823744, 1120645220563090493852432203776, 15011976600459733073898206396416, 27152299823226546757299555270656, 817137139993920151767398481920, 15011976600459733073898206396416, 887177466279113307633175494656, 887177466279113307633175494656, 863830690850715589011249823744, 863830690850715589011249823744, 27152299823226546757299555270656, 863830690850715589011249823744, 1097298445134692775230506532864, 1120645220563090493852432203776], [31780241946029371744675954688, 779128512225236210514636308480, 576145031408661513564770533376, 642781022585819873674574954496, 31780241946029371744675954688, 641755853490786668134424117248, 653032713536151929076083326976, 31780241946029371744675954688, 779128512225236210514636308480, 31780241946029371744675954688], [39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800], [], [], [5570730176784211237046059008, 4178047632588158427784544256, 4410161389954167229328130048, 5686787055467215637817851904, 76133312416050886906296139776, 133117239849406047685246451712, 4061990753905154027012751360, 76133312416050886906296139776, 4294104511271162828556337152, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712, 4294104511271162828556337152, 5570730176784211237046059008, 5686787055467215637817851904]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[158456325028528675187087900672], [2733371129783104877143099703296, 2733372083701134416811432869888], [37614585684392035941129260105728, 137179845998499416870075225866240, 37616272017851236277086844878848], [23183562405281989839204183441408, 912936652207744523302080425754624, 912936759197679559196762387251200, 23183734563874489334990093942784], [648752587229670060397359529984, 125863407672137330394399609192448, 1306978066036946063034244900323328, 125863541022322073667441153540096, 648752587229670060397359529984], [298384407382586434421077835776, 58092771365630230372020813561856, 58092772362049558257515953651712, 298383410963258548925937745920], [26855002599055646572599574528, 1213797261762630048879977955328, 26998335866543706044125675520], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7.Parent3
