import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent2Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
13, parent 56; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[15435564864839585302648455168, 223815690540173986888402599936, 396179498197549356101310349312, 12862970720699654418873712640, 246969037837433364842375282688, 12862970720699654418873712640, 393606904053409425217535606784, 411615063062388941403958804480, 246969037837433364842375282688, 6305428247286970596131893936128, 403897280629969148752634576896, 223815690540173986888402599936, 393606904053409425217535606784, 12862970720699654418873712640, 403897280629969148752634576896, 12862970720699654418873712640, 393606904053409425217535606784, 411615063062388941403958804480, 15435564864839585302648455168], [100911456014872326471073923072, 75146828947245349499735900160, 79440933458516512328292237312, 103058508270507907885352091648, 1380554600373678849380862394368, 2497021773304181184805510053888, 75146828947245349499735900160, 1380554600373678849380862394368, 81587985714152093742570405888, 81587985714152093742570405888, 79440933458516512328292237312, 79440933458516512328292237312, 2497021773304181184805510053888, 79440933458516512328292237312, 100911456014872326471073923072, 103058508270507907885352091648], [7195526478346272847851159552, 176406455598166689173125201920, 130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552, 145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552, 176406455598166689173125201920, 7195526478346272847851159552], [39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800], [39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [31180614739500515674021691392, 755375537721447976490009362432, 572315154412122368339301367808, 637693862736881514107411365888, 31180614739500515674021691392, 637693862736881514107411365888, 636688036454962142634055827456, 31180614739500515674021691392, 755375537721447976490009362432, 31180614739500515674021691392], [571928298149845687003395391488, 428946223612384265252546543616, 452776569368627835544354684928, 583843471027967472149299462144, 7816353408047891055713070350336, 13666703291205687562351969042432, 417031050734262480106642472960, 7816353408047891055713070350336, 440861396490506050398450614272, 452776569368627835544354684928, 452776569368627835544354684928, 440861396490506050398450614272, 13666703291205687562351969042432, 440861396490506050398450614272, 571928298149845687003395391488, 583843471027967472149299462144], [176638569355532697974668787712, 2649578540332990469620031815680, 4651482326362361046666278076416, 176638569355532697974668787712, 2943976155925544966244479795200, 176638569355532697974668787712, 4651482326362361046666278076416, 4622042564803105597003833278464, 2943976155925544966244479795200, 71332542258075954532103745437696, 4563163041684594697678943682560, 2649578540332990469620031815680, 4651482326362361046666278076416, 176638569355532697974668787712, 4563163041684594697678943682560, 176638569355532697974668787712, 4651482326362361046666278076416, 4651482326362361046666278076416, 176638569355532697974668787712], [92613389189037511815890731008, 105476359909737166234764443648, 82323012612477788280791760896, 1103642887836030349139364544512, 97758577477317373583440216064, 82323012612477788280791760896, 97758577477317373583440216064, 95185983333177442699665473536, 3596486613507623375517090054144, 95185983333177442699665473536, 1103642887836030349139364544512, 3596486613507623375517090054144, 92613389189037511815890731008, 95185983333177442699665473536, 95185983333177442699665473536, 105476359909737166234764443648]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[316912650057057350374175801344], [5149830572871914909319647199232, 5149830553982448977841066344448], [55631475073959427726748374007808, 202958538655743192481783435231232, 55628878801869742687463497793536], [36646159236921476302974469799936, 1434620698959866397995109101600768, 1434620754003770122323693712441344, 36646343579219501602445031636992], [1239769181829389071797616377856, 231051129817791632307328169017344, 2357366492163758656880738968797184, 231051532087858109075186052497408, 1239769181829389071797616377856], [689238950966952529970488934400, 127620770240884142202773938634752, 127620778561693885019088805167104, 689230630157209713655622402048], [110776885721104542111973244928, 5006913704770848951629909065728, 111368135449492787432018411520], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent2
