import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
10, parent 45; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[79150791261809001326362755072, 89363796585913388594280529920, 76597539930782904509383311360, 1008534275755308242706880266240, 89363796585913388594280529920, 76597539930782904509383311360, 89363796585913388594280529920, 89363796585913388594280529920, 3704767681318866481437172826112, 91917047916939485411259973632, 1008534275755308242706880266240, 3704767681318866481437172826112, 79150791261809001326362755072, 89363796585913388594280529920, 91917047916939485411259973632, 89363796585913388594280529920], [216794249379852220641709129728, 3143516616007857199304782381056, 5564385734082873663137200996352, 180661874483210183868090941440, 3468707990077635530267346075648, 180661874483210183868090941440, 5528253359186231626363582808064, 5781179983462725883778910126080, 3468707990077635530267346075648, 88560450871669632132138179493888, 5672782858772799773458055561216, 3143516616007857199304782381056, 5528253359186231626363582808064, 180661874483210183868090941440, 5672782858772799773458055561216, 180661874483210183868090941440, 5528253359186231626363582808064, 5781179983462725883778910126080, 216794249379852220641709129728], [751835802921616342266469679104, 559877725579927063389924229120, 591870738470208609869348470784, 767832309366757115506181799936, 10285753644225517193134893694976, 18603936995698719277785196527616, 559877725579927063389924229120, 10285753644225517193134893694976, 607867244915349383109060591616, 607867244915349383109060591616, 591870738470208609869348470784, 591870738470208609869348470784, 18603936995698719277785196527616, 591870738470208609869348470784, 751835802921616342266469679104, 767832309366757115506181799936], [32379869152558227815330217984, 793829050191750101279063408640, 587015692378636259103728467968, 654908966408193833555227312128, 32379869152558227815330217984, 653864454500046793948281176064, 665354085489664229624688672768, 32379869152558227815330217984, 793829050191750101279063408640, 32379869152558227815330217984], [39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800], [39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [7195526478346272847851159552, 174317431781872609959232929792, 132072727941259008078300315648, 147160122170049580178633392128, 7195526478346272847851159552, 147160122170049580178633392128, 146928008412683571377089806336, 7195526478346272847851159552, 174317431781872609959232929792, 7195526478346272847851159552], [90060137858011414998911287296, 67545103393508561249183465472, 71297609137592370207471435776, 91936390730053319478055272448, 1230821884059489338318454259712, 2152062044232064437578150969344, 65668850521466656770039480320, 1230821884059489338318454259712, 69421356265550465728327450624, 71297609137592370207471435776, 71297609137592370207471435776, 69421356265550465728327450624, 2152062044232064437578150969344, 69421356265550465728327450624, 90060137858011414998911287296, 91936390730053319478055272448], [15319507986156580901876662272, 229792619792348713528149934080, 403413710302123297082752106496, 15319507986156580901876662272, 255325133102609681697944371200, 15319507986156580901876662272, 403413710302123297082752106496, 400860458971097200265772662784, 255325133102609681697944371200, 6186527975076232587541192114176, 395753956309045006631813775360, 229792619792348713528149934080, 403413710302123297082752106496, 15319507986156580901876662272, 395753956309045006631813775360, 15319507986156580901876662272, 403413710302123297082752106496, 403413710302123297082752106496, 15319507986156580901876662272]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[316912650057057350374175801344], [5189444422733089417503803703296, 5189444866635538807250453790720], [56424801159064186830724662296576, 206124402633871211765214987943936, 56423378489492824555668293812224], [36824198989080874219119784755200, 1444702608868662622059504131375104, 1444702786278526650506335519506432, 36824455734701814875990762979328], [1137248843888001954420107509760, 227838077753143998511666696290304, 2357104836509491101124846256390144, 227838430343915075490856931688448, 1137248843888001954420107509760], [644460447222855771341212090368, 122238419612401131836245454880768, 122238424726724032784071221313536, 644455332899954823515445657600], [109098448058663564201185771520, 4931051375910684573574910443520, 109680739457833805804260556800], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3
