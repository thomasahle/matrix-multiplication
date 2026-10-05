import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
10, parent 42; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[158456325028528675187087900672], [158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672], [48569803728837341722995326976, 1162541753767655082531049439232, 869556163532410472782658273280, 1008998503270040260309967437824, 48569803728837341722995326976, 1007431735407819700899548233728, 1012132038994481379130805846016, 48569803728837341722995326976, 1162541753767655082531049439232, 48569803728837341722995326976], [413452630308203177749512192000, 321574268017491360471842816000, 367513449162847269110677504000, 431828302766345541205046067200, 5099249107134505858910650368000, 11466419613880834796253138124800, 321574268017491360471842816000, 5099249107134505858910650368000, 367513449162847269110677504000, 358325612933776087382910566400, 358325612933776087382910566400, 358325612933776087382910566400, 11466419613880834796253138124800, 358325612933776087382910566400, 413452630308203177749512192000, 431828302766345541205046067200], [29594504064166122196807188480, 497187668277990852906360766464, 1077239947935646847963781660672, 35513404876999346636168626176, 568214478031989546178698018816, 41432305689832571075530063872, 1077239947935646847963781660672, 1077239947935646847963781660672, 568214478031989546178698018816, 13293851225623422090805789065216, 1065402146309980399085058785280, 497187668277990852906360766464, 1077239947935646847963781660672, 41432305689832571075530063872, 1065402146309980399085058785280, 41432305689832571075530063872, 1077239947935646847963781660672, 1077239947935646847963781660672, 35513404876999346636168626176]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[158456325028528675187087900672], [713053557075708695734799826944, 713053368181049380948991279104], [5397702730242631713721625346048, 18756699157335334494948642783232, 5397702730242631713721625346048], [6587253180748893918298399309824, 242585315683488368450315847991296, 242576621920130201022348918784000, 6595951430355220072428281528320], [966946174472839319166105157632, 129106275091762434676955598028800, 905591824363483339222299967488, 1332432817677825090171809745076224, 929267427614816236979745718272, 29594504064166122196807188480, 905591824363483339222299967488, 514944370716490526224445079552, 929267427614816236979745718272, 14507225892254233100874883792896, 568214478031989546178698018816, 129106296923262684983325420945408, 905591824363483339222299967488, 29594504064166122196807188480, 568214478031989546178698018816, 29594504064166122196807188480, 911510725176316563661661405184, 514944370716490526224445079552, 966924342972589012796282241024], [2836202718899377932836643274752, 205263568223163112688786440454144, 394013103128799940620236881920, 348983034199794233120781238272, 16334657503996820395427534733312, 4446719306739313615571244810240, 205263589421866254290623804735488, 16334657503996820395427534733312, 394013103128799940620236881920, 394013103128799940620236881920, 337725516967542806245917327360, 394013103128799940620236881920, 4446719306739313615571244810240, 337725516967542806245917327360, 2836181520196236330999278993408, 348983034199794233120781238272], [1368949370574927247659268833280, 940002688892994144051136561152, 14383334258121028226339823419392, 1514136067737816914669196017664, 46906321801047611978599628800, 1514136067737816914669196017664, 1011300298030586514258607996928, 1370825623446969152138412818432, 940002688892994144051136561152, 45030068929005707499455643648], [206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
