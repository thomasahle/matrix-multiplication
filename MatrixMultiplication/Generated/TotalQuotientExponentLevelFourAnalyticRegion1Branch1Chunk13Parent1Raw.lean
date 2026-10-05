import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
13, parent 55; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[32379869152558227815330217984, 36557916785146386243114762240, 31335357244411188208384081920, 412582203718080644743723745280, 36557916785146386243114762240, 31335357244411188208384081920, 36557916785146386243114762240, 36557916785146386243114762240, 1515586778721354469678843428864, 37602428693293425850060898304, 412582203718080644743723745280, 1515586778721354469678843428864, 32379869152558227815330217984, 36557916785146386243114762240, 37602428693293425850060898304, 36557916785146386243114762240], [35049177362267329033081454592, 508213071752876270979681091584, 899595552298194778515757334528, 29207647801889440860901212160, 560786837796277264529303273472, 29207647801889440860901212160, 893754022737816890343577092096, 934644729660462107548838789120, 560786837796277264529303273472, 14317588952486203910013774200832, 917120140979328443032298061824, 508213071752876270979681091584, 893754022737816890343577092096, 29207647801889440860901212160, 917120140979328443032298061824, 29207647801889440860901212160, 893754022737816890343577092096, 934644729660462107548838789120, 35049177362267329033081454592], [95456782716771119634799656960, 71084838193340195472723148800, 75146828947245349499735900160, 97487778093723696648306032640, 1305930027380507019684599562240, 2362047623395847066707914915840, 71084838193340195472723148800, 1305930027380507019684599562240, 77177824324197926513242275840, 77177824324197926513242275840, 75146828947245349499735900160, 75146828947245349499735900160, 2362047623395847066707914915840, 75146828947245349499735900160, 95456782716771119634799656960, 97487778093723696648306032640], [3597763239173136423925579776, 88203227799083344586562600960, 65223965819848473233747607552, 72767662934243759283914145792, 3597763239173136423925579776, 72651606055560754883142352896, 73928231721073803291632074752, 3597763239173136423925579776, 88203227799083344586562600960, 3597763239173136423925579776], [3597763239173136423925579776, 87158715890936304979616464896, 66036363970629504039150157824, 73580061085024790089316696064, 3597763239173136423925579776, 73580061085024790089316696064, 73464004206341785688544903168, 3597763239173136423925579776, 87158715890936304979616464896, 3597763239173136423925579776], [88203227799083344586562600960, 66152420849312508439921950720, 69827555340940981131028725760, 90040795044897580932115988480, 1205444113254139042683022213120, 2107689630948929088349735485440, 64314853603498272094368563200, 1205444113254139042683022213120, 67989988095126744785475338240, 69827555340940981131028725760, 69827555340940981131028725760, 67989988095126744785475338240, 2107689630948929088349735485440, 67989988095126744785475338240, 88203227799083344586562600960, 90040795044897580932115988480], [29014219670751100192948224000, 435213295061266502894223360000, 764041117996445638414303232000, 29014219670751100192948224000, 483570327845851669882470400000, 29014219670751100192948224000, 764041117996445638414303232000, 759205414717987121715478528000, 483570327845851669882470400000, 11716909043704985961252257792000, 749534008161070088317829120000, 435213295061266502894223360000, 764041117996445638414303232000, 29014219670751100192948224000, 749534008161070088317829120000, 29014219670751100192948224000, 764041117996445638414303232000, 764041117996445638414303232000, 29014219670751100192948224000], [37602428693293425850060898304, 42824988234028623884791578624, 33424381060705267422276354048, 448095608595079991379892371456, 39691452509587505063953170432, 33424381060705267422276354048, 39691452509587505063953170432, 38646940601440465457007034368, 1460227647589561370510698217472, 38646940601440465457007034368, 448095608595079991379892371456, 1460227647589561370510698217472, 37602428693293425850060898304, 38646940601440465457007034368, 38646940601440465457007034368, 42824988234028623884791578624]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[2376844875427930127806318510080], [67740077825772785719504516677632, 67740080073619231565455638396928], [391171453448226928006694598344704, 1430443486090556683468769691959296, 391148411322105073174624698630144], [80976895652451578107128096751616, 3173398674444954785318029462863872, 3173399018629913522789251217883136, 80977418144523975770413830504448], [875743691440255254120355594240, 175875815346855357355275348606976, 1815525988632306560683823104786432, 175876113790972341751113563766784, 875743691440255254120355594240], [317636645507279061421177962496, 59499626052762295821704504541184, 59499629259249137690193604640768, 317633439020437192932077862912], [30211877923937602394174521344, 1365521919482958804989975199744, 30373127849861669299641384960], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent1
