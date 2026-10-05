import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
15, parent 65; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[1856910058928070412348686336, 26925195854457020979055951872, 47660691512487140583616282624, 1547425049106725343623905280, 29710560942849126597578981376, 1547425049106725343623905280, 47351206502665795514891501568, 49517601571415210995964968960, 29710560942849126597578981376, 758547759072116763444438368256, 48589146541951175789790625792, 26925195854457020979055951872, 47351206502665795514891501568, 1547425049106725343623905280, 48589146541951175789790625792, 1547425049106725343623905280, 47351206502665795514891501568, 49517601571415210995964968960, 1856910058928070412348686336], [5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008, 74624572993171829696262832128, 134974149908334118097595138048, 4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 4294104511271162828556337152, 134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112, 5570730176784211237046059008], [], [9594035304461697130468212736, 232423242375830146612310573056, 176096970588345344104400420864, 196213496226732773571511189504, 9594035304461697130468212736, 196213496226732773571511189504, 195904011216911428502786408448, 9594035304461697130468212736, 232423242375830146612310573056, 9594035304461697130468212736], [345385270960621096696855658496, 259038953220465822522641743872, 273430006177158368218344062976, 352580797438967369544706818048, 4720265369795154988190360666112, 8253268870663174956485280006144, 251843426742119549674790584320, 4720265369795154988190360666112, 266234479698812095370492903424, 273430006177158368218344062976, 273430006177158368218344062976, 266234479698812095370492903424, 8253268870663174956485280006144, 266234479698812095370492903424, 345385270960621096696855658496, 352580797438967369544706818048], [210759291688335991801575899136, 3161389375325039877023638487040, 5549994681126181117441498677248, 210759291688335991801575899136, 3512654861472266530026264985600, 210759291688335991801575899136, 5549994681126181117441498677248, 5514868132511458452141236027392, 3512654861472266530026264985600, 85111627293473018022536400601088, 5444615035282013121540710727680, 3161389375325039877023638487040, 5549994681126181117441498677248, 210759291688335991801575899136, 5444615035282013121540710727680, 210759291688335991801575899136, 5549994681126181117441498677248, 5549994681126181117441498677248, 210759291688335991801575899136], [548020581141146780444406054912, 624134550744083833283906895872, 487129405458797138172805382144, 6530578591931999133629172154368, 578466168982321601580206391296, 487129405458797138172805382144, 578466168982321601580206391296, 563243375061734191012306223104, 21281465900981199973924435132416, 563243375061734191012306223104, 6530578591931999133629172154368, 21281465900981199973924435132416, 548020581141146780444406054912, 563243375061734191012306223104, 563243375061734191012306223104, 624134550744083833283906895872], [8665580274997661924293869568, 173311605499953238485877391360, 8975065284819006993018650624, 161241690116920780805610930176, 241398307660649153605329223680, 8665580274997661924293869568, 241707792670470498674054004736, 241707792670470498674054004736, 173002120490131893417152610304, 8975065284819006993018650624]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[1743019575313815427057966907392], [54310906182718673093865838215168, 54310904624337733746882917695488], [311243359733031385952837374574592, 1134494966972633645651511979540480, 311225405210660918870081288536064], [59710773253800634174772869070848, 2335633749082546072046582689169408, 2335633741649541228009761122811904, 59711038764133767037705363914752], [761068265513950642141506043904, 133222986158673411611880211873792, 1345117043974838772866079355043840, 133223222125881827642312249835520, 761068265513950642141506043904], [217115658365042811564598493184, 39119667029967200803629972848640, 39119670642577560198908561326080, 217112045754683416286010015744], [10070625974645867464724840448, 455173973160986268329991733248, 10124375949953889766547128320], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent3
