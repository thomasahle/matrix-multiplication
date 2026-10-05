import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
15, parent 62; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584], [32979496359087083885984481280, 789380203175568265916144680960, 590439370299784888926496358400, 685122440492002645889484062720, 32979496359087083885984481280, 684058585770741772215742627840, 687250149934524393236966932480, 32979496359087083885984481280, 789380203175568265916144680960, 32979496359087083885984481280], [925263465300252585153118863360, 719649361900196455119092449280, 822456413600224520136105656320, 966386285980263811159924146176, 11411582738703115216888465981440, 25660640104327005028246496477184, 719649361900196455119092449280, 11411582738703115216888465981440, 822456413600224520136105656320, 801895003260218907132703014912, 801895003260218907132703014912, 801895003260218907132703014912, 25660640104327005028246496477184, 801895003260218907132703014912, 925263465300252585153118863360, 966386285980263811159924146176], [306293445657562447703556751360, 5145729887047049121419753422848, 11149081421935273096409465749504, 367552134789074937244268101632, 5880834156625198995908289626112, 428810823920587426784979451904, 11149081421935273096409465749504, 11149081421935273096409465749504, 5880834156625198995908289626112, 137587015789377051508437692710912, 11026564043672248117328043048960, 5145729887047049121419753422848, 11149081421935273096409465749504, 428810823920587426784979451904, 11026564043672248117328043048960, 428810823920587426784979451904, 11149081421935273096409465749504, 11149081421935273096409465749504, 367552134789074937244268101632], [472274124987372574874015891456, 560825523422504932662893871104, 427998425769806395979576901632, 4412811355350762496479085985792, 531308390610794146733267877888, 427998425769806395979576901632, 531308390610794146733267877888, 531308390610794146733267877888, 22757709397829015951741640769536, 531308390610794146733267877888, 4412811355350762496479085985792, 22757709397829015951741640769536, 472274124987372574874015891456, 531308390610794146733267877888, 531308390610794146733267877888, 560825523422504932662893871104], [3481706360490132023153786880, 61974373216724350012137406464, 3481706360490132023153786880, 55127017374427090366601625600, 94122128611916569025924038656, 3481706360490132023153786880, 94122128611916569025924038656, 94122128611916569025924038656, 61974373216724350012137406464, 3481706360490132023153786880]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[79228162514264337593543950336], [2971056613745225775418871644160, 2971055574824599544096924631040], [44646779106511318425616890462208, 159007504296718150850083553280000, 44646777916474964742466296610816], [23668770969284413817707737120768, 879373825368300506073506208808960, 879340091969744261265110083829760, 23702504367840658626103862099968], [871552000890898085287548682240, 132505898052515429717626736082944, 1348865840814788234350843295432704, 132505901655681056147166034132992, 871497467002753906624620920832], [968733764914165346056362000384, 81080268556993049544513195868160, 4061990753905154027012751360, 3597763239173136423925579776, 168398530969039385519871492096, 45842467079786738304858193920, 81080254947132845914195689996288, 168398530969039385519871492096, 4061990753905154027012751360, 4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360, 45842467079786738304858193920, 3481706360490132023153786880, 968747374774368976373867872256, 3597763239173136423925579776], [123001883619434438941057482752, 19381498740061734928889413632, 1214572050986741505830898630656, 31219300365728183807612289024, 967140655691703339764940800, 31219300365728183807612289024, 20851552536713124005332123648, 123040569245662107074648080384, 19381498740061734928889413632, 928455029464035206174343168], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0
