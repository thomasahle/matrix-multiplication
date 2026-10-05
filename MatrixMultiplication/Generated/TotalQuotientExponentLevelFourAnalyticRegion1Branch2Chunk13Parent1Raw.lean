import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
13, parent 55; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[5222559540735198034730680320, 4061990753905154027012751360, 4642275147320176030871715840, 5454673298101206836274266112, 64411567669067442428345057280, 144838984596389492163197534208, 4061990753905154027012751360, 64411567669067442428345057280, 4642275147320176030871715840, 4526218268637171630099922944, 4526218268637171630099922944, 4526218268637171630099922944, 144838984596389492163197534208, 4526218268637171630099922944, 5222559540735198034730680320, 5454673298101206836274266112], [1740853180245066011576893440, 29246333428117108994491809792, 63367055760920402821398921216, 2089023816294079213892272128, 33424381060705267422276354048, 2437194452343092416207650816, 63367055760920402821398921216, 63367055760920402821398921216, 33424381060705267422276354048, 781991248566083652400340533248, 62670714488822376416768163840, 29246333428117108994491809792, 63367055760920402821398921216, 2437194452343092416207650816, 62670714488822376416768163840, 2437194452343092416207650816, 63367055760920402821398921216, 63367055760920402821398921216, 2089023816294079213892272128], [3713820117856140824697372672, 4410161389954167229328130048, 3365649481807127622381993984, 34701006726218315830766075904, 4178047632588158427784544256, 3365649481807127622381993984, 4178047632588158427784544256, 4178047632588158427784544256, 178959706929192785990104645632, 4178047632588158427784544256, 34701006726218315830766075904, 178959706929192785990104645632, 3713820117856140824697372672, 4178047632588158427784544256, 4178047632588158427784544256, 4410161389954167229328130048]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[32087405818277056725385299886080], [476874530858987525439801163513856, 476874089487726570511280910630912], [848390822261904206940305511940096, 88203227799083344586562600960, 3597763239173136423925579776, 2926262766361850132744805881479168, 72651606055560754883142352896, 848390817841769178974317591920640, 72767662934243759283914145792, 65223965819848473233747607552, 88203227799083344586562600960, 3597763239173136423925579776], [61796648266959433152281326911488, 95456782716771119634799656960, 2245698111297810247813035085266944, 2362047623395847066707914915840, 75146828947245349499735900160, 2245656100771401153233990654623744, 77177824324197926513242275840, 77177824324197926513242275840, 1305930027380507019684599562240, 71084838193340195472723148800, 2362047623395847066707914915840, 1305930027380507019684599562240, 61838734521237447028956404383744, 75146828947245349499735900160, 71084838193340195472723148800, 95456782716771119634799656960], [639427552087172066867199082496, 74613880219024898167389428908032, 893754022737816890343577092096, 779857561750407280936471266066432, 917120140979328443032298061824, 29207647801889440860901212160, 893754022737816890343577092096, 508213071752876270979681091584, 917120140979328443032298061824, 14317588952486203910013774200832, 560786837796277264529303273472, 74613909936877174866066758696960, 893754022737816890343577092096, 29207647801889440860901212160, 560786837796277264529303273472, 29207647801889440860901212160, 899595552298194778515757334528, 508213071752876270979681091584, 639424345600330198378098982912], [197670516291891442427164098560, 13543347862897146604552342994944, 36557916785146386243114762240, 32379869152558227815330217984, 1515586778721354469678843428864, 412582203718080644743723745280, 13543350507422377011553662664704, 1515586778721354469678843428864, 36557916785146386243114762240, 36557916785146386243114762240, 31335357244411188208384081920, 36557916785146386243114762240, 412582203718080644743723745280, 31335357244411188208384081920, 197667871766661035425844428800, 32379869152558227815330217984], [], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent1
