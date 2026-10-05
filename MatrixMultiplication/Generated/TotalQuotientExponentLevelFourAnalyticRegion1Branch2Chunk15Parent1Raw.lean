import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
15, parent 63; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[7195526478346272847851159552, 172228407965578530745340657664, 128823135338134884856690114560, 149481259743709668194069250048, 7195526478346272847851159552, 149249145986343659392525664256, 149945487258441685797156421632, 7195526478346272847851159552, 172228407965578530745340657664, 7195526478346272847851159552], [355134048769993466361686261760, 276215371265550473836867092480, 315674710017771970099276677120, 370917784270882064866650095616, 4379986601496586085127463895040, 9849050952554485467097432326144, 276215371265550473836867092480, 4379986601496586085127463895040, 315674710017771970099276677120, 307782842267327670846794760192, 307782842267327670846794760192, 307782842267327670846794760192, 9849050952554485467097432326144, 307782842267327670846794760192, 355134048769993466361686261760, 370917784270882064866650095616], [153388507992704149686719610880, 2576926934277429714736889462784, 5583341690934431048596593836032, 184066209591244979624063533056, 2945059353459919673985016528896, 214743911189785809561407455232, 5583341690934431048596593836032, 5583341690934431048596593836032, 2945059353459919673985016528896, 68902117790322704039274449207296, 5521986287737349388721905991680, 2576926934277429714736889462784, 5583341690934431048596593836032, 214743911189785809561407455232, 5521986287737349388721905991680, 214743911189785809561407455232, 5583341690934431048596593836032, 5583341690934431048596593836032, 184066209591244979624063533056], [471655154967729884736566329344, 560090496524179238124672516096, 427437484189505208042513235968, 4407027854229726110507291639808, 530612049338696120328637120512, 427437484189505208042513235968, 530612049338696120328637120512, 530612049338696120328637120512, 22727882780007483820743289995264, 530612049338696120328637120512, 4407027854229726110507291639808, 22727882780007483820743289995264, 471655154967729884736566329344, 530612049338696120328637120512, 530612049338696120328637120512, 560090496524179238124672516096], [8123981507810308054025502720, 144606870839023483361653948416, 8123981507810308054025502720, 128629707206996544188737126400, 219618300094471994393822756864, 8123981507810308054025502720, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[1505335087771022414277335056384], [65006716457121200933918073683968, 65006698228786577057087548817408], [349904672342124518542260964425728, 1239220710876156453739107941613568, 349904666155824425983025734483968], [57886215688466620794906209157120, 2148697334897866185576216698814464, 2148604317699119197881038584938496, 57979240084100128383423628705792], [994140908839039090885023236096, 147729200416134951411618127282176, 41432305689832571075530063872, 1516018796287124715669689349439488, 42515503224207278816066797568, 1353996917968384675670917120, 41432305689832571075530063872, 23559546372649893356673957888, 42515503224207278816066797568, 663729289188102168013883572224, 25996740824992985772881608704, 147729206602435043970853357223936, 41432305689832571075530063872, 1353996917968384675670917120, 25996740824992985772881608704, 1353996917968384675670917120, 41703105073426248010664247296, 23559546372649893356673957888, 994098804219477825128297922560], [576240489324746240573120184320, 47961995768510818285412279123968, 5415987671873538702683668480, 4797017652230848565234106368, 224531374625385847359828656128, 61123289439715651073144258560, 47961990337789362985320283373568, 224531374625385847359828656128, 5415987671873538702683668480, 5415987671873538702683668480, 4642275147320176030871715840, 5415987671873538702683668480, 61123289439715651073144258560, 4642275147320176030871715840, 576245920046201540665115934720, 4797017652230848565234106368], [47457955597011063844947099648, 459681226405828235464913453056, 47457955597011063844947099648], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent1
