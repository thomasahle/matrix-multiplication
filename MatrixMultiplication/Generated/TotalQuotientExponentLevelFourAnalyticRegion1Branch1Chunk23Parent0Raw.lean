import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk23Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
23, parent 94; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[], [2089023816294079213892272128, 31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 34817063604901320231537868800, 2089023816294079213892272128, 55010960495744085965829832704, 54662789859695072763514454016, 34817063604901320231537868800, 843617451146758989210162561024, 53966448587597046358883696640, 31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 53966448587597046358883696640, 2089023816294079213892272128, 55010960495744085965829832704, 55010960495744085965829832704, 2089023816294079213892272128], [70330468481900666867706494976, 80098589104386870599332397056, 62515971983911703882405773312, 838104749409316280173502398464, 74237716730895148360356855808, 62515971983911703882405773312, 74237716730895148360356855808, 72284092606397907614031675392, 2731166526047142563362602221568, 72284092606397907614031675392, 838104749409316280173502398464, 2731166526047142563362602221568, 70330468481900666867706494976, 72284092606397907614031675392, 72284092606397907614031675392, 80098589104386870599332397056], [31954327264053878345833644032, 639086545281077566916672880640, 33095553237770088286756274176, 594578732306145379220690305024, 890156259498643753919651512320, 31954327264053878345833644032, 891297485472359963860574142464, 891297485472359963860574142464, 637945319307361356975750250496, 33095553237770088286756274176], [188785855991020491922116444160, 207354956580301196045603307520, 188785855991020491922116444160, 207354956580301196045603307520], [158456325028528675187087900672]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [713053462628379038341895553024, 713053462628379038341895553024], [1415660143902285710499214524416, 5170724603095141445783676518400, 1415659666943270940665047941120], [58422912780915750459532115968, 2278808160009504697859082027008, 2278807324150637229931879202816, 58423191400538239768599724032], [582551129326799433561538560, 68853803372173260287964610560, 653408868915978427795935068160, 68853850595838088984416747520, 582551129326799433561538560], [449163165651663434855481344, 78778999348612674158688468992, 78779008793345639897978896384, 449153720918697695565053952], [], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent0
