import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
16, parent 66; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008, 74624572993171829696262832128, 134974149908334118097595138048, 4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 4294104511271162828556337152, 134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112, 5570730176784211237046059008], [1199254413057712141308526592, 29401075933027781528854200320, 21741321939949491077915869184, 24255887644747919761304715264, 1199254413057712141308526592, 24217202018520251627714117632, 24642743907024601097210691584, 1199254413057712141308526592, 29401075933027781528854200320, 1199254413057712141308526592], [], [39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168], [31780241946029371744675954688, 769901990369937360653278773248, 583321215073893952345826394112, 649957206251052312455630815232, 31780241946029371744675954688, 649957206251052312455630815232, 648932037156019106915479977984, 31780241946029371744675954688, 769901990369937360653278773248, 31780241946029371744675954688], [886674553138153621896497725440, 665005914853615216422373294080, 701950687901038284001394032640, 905146939661865155686008094720, 12117885559554766165918802247680, 21187827342697129256568393564160, 646533528329903682632862924800, 12117885559554766165918802247680, 683478301377326750211883663360, 701950687901038284001394032640, 701950687901038284001394032640, 683478301377326750211883663360, 21187827342697129256568393564160, 683478301377326750211883663360, 886674553138153621896497725440, 905146939661865155686008094720], [431383418064727357668754194432, 6470751270970910365031312916480, 11359763342371153751943860453376, 431383418064727357668754194432, 7189723634412122627812569907200, 431383418064727357668754194432, 11359763342371153751943860453376, 11287866106027032525665734754304, 7189723634412122627812569907200, 174207003661805731271898568851456, 11144071633338790073109483356160, 6470751270970910365031312916480, 11359763342371153751943860453376, 431383418064727357668754194432, 11144071633338790073109483356160, 431383418064727357668754194432, 11359763342371153751943860453376, 11359763342371153751943860453376, 431383418064727357668754194432], [515988882624637565831391215616, 587654005211392783307973328896, 458656784555233391850125524992, 6148867517943597659490745319424, 544654931659339652822024060928, 458656784555233391850125524992, 544654931659339652822024060928, 530321907141988609326707638272, 20037568275256758806452358873088, 530321907141988609326707638272, 6148867517943597659490745319424, 20037568275256758806452358873088, 515988882624637565831391215616, 530321907141988609326707638272, 530321907141988609326707638272, 587654005211392783307973328896], [3249592603124123221610201088, 64991852062482464432204021760, 3365649481807127622381993984, 60465633793845292802104098816, 90524365372743432601998458880, 3249592603124123221610201088, 90640422251426437002770251776, 90640422251426437002770251776, 64875795183799460031432228864, 3365649481807127622381993984]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[158456325028528675187087900672], [2852214020518709536674809905152, 2852213680508322770060354519040], [36181061446715063618710156607488, 131890861792487168891858054021120, 36178279722571229805588093337600], [22929574476362135457723530084352, 896315166602447105544428992856064, 896315104763058012366424919506944, 22929665301636700489609925099520], [850809379181845315388360884224, 133956563309378331100499543064576, 1333091547595957170526960987668480, 133956769837354092921563318845440, 850809379181845315388360884224], [358214302033408366975578537984, 63935439578292101590185337159680, 63935446095157847950295732060160, 358207785167662006865183637504], [28533440261496624483387047936, 1289659590622794426934976577536, 28685731858202687671883530240], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0
