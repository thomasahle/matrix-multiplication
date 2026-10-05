import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
12, parent 53; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [31780241946029371744675954688, 760675468514638510791921238016, 568968847743429074783714672640, 660208897201384367857139187712, 31780241946029371744675954688, 659183728106351162316988350464, 662259235391450778937440862208, 31780241946029371744675954688, 760675468514638510791921238016, 31780241946029371744675954688], [566647710169768986768278814720, 440725996798709211930883522560, 503686853484239099349581168640, 591832052843980941735757873152, 6988655092093817503475438714880, 15715029828708259899706932461568, 440725996798709211930883522560, 6988655092093817503475438714880, 503686853484239099349581168640, 491094682147133121865841639424, 491094682147133121865841639424, 491094682147133121865841639424, 15715029828708259899706932461568, 491094682147133121865841639424, 566647710169768986768278814720, 591832052843980941735757873152], [127662566551304840848972185600, 2144731118061921326262732718080, 4646917422467496206902587555840, 153195079861565809018766622720, 2451121277785052944300265963520, 178727593171826777188561059840, 4646917422467496206902587555840, 4646917422467496206902587555840, 2451121277785052944300265963520, 57346024894846134509358305771520, 4595852395846974270562998681600, 2144731118061921326262732718080, 4646917422467496206902587555840, 178727593171826777188561059840, 4595852395846974270562998681600, 178727593171826777188561059840, 4646917422467496206902587555840, 4646917422467496206902587555840, 153195079861565809018766622720], [84798892691048548830590009344, 100698685070620151736325636096, 76848996501262747377722195968, 792339653581984878135825399808, 95398754277429617434413760512, 76848996501262747377722195968, 95398754277429617434413760512, 95398754277429617434413760512, 4086246641549901946774056075264, 95398754277429617434413760512, 792339653581984878135825399808, 4086246641549901946774056075264, 84798892691048548830590009344, 95398754277429617434413760512, 95398754277429617434413760512, 100698685070620151736325636096]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[316912650057057350374175801344], [5585586156165875265052340125696, 5585584758345396335637356871680], [71168446336600221957643460149248, 250000968626341601929342985699328, 71168445807695175876243196215296], [37149464815980621472908787580928, 1374577542710914720549722409402368, 1374521883038935224660593574150144, 37205136955007632137900986990592], [1566021525254507243080695939072, 220368536993827474248743128137728, 405444705679075874096258482176, 2275896794518948828408823406395392, 416044567265456942700082233344, 13249826982976335754779688960, 405444705679075874096258482176, 230546989503788242133166587904, 416044567265456942700082233344, 6495065187054999786993003528192, 254396678073145646491770028032, 220368562792115570165614930558976, 405444705679075874096258482176, 13249826982976335754779688960, 254396678073145646491770028032, 13249826982976335754779688960, 408094671075671141247214419968, 230546989503788242133166587904, 1565975510515498161257733685248], [2030097792032811497170963267584, 164067102643975052091663056896000, 75823827406229541837571358720, 67158247131231879913277489152, 3143439244755401863037601185792, 855726052156019115024019619840, 164067111366185945951897766592512, 3143439244755401863037601185792, 75823827406229541837571358720, 75823827406229541837571358720, 64991852062482464432204021760, 75823827406229541837571358720, 855726052156019115024019619840, 64991852062482464432204021760, 2030089069821917636936253571072, 67158247131231879913277489152], [508468372329673169739223924736, 135670491180432144502225895424, 5087229532178180791648361906176, 218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168, 145960867756991868037324865536, 508739171713266846674358108160, 135670491180432144502225895424, 6499185206248246443220402176], [41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3
