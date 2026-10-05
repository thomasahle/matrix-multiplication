import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent3Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
13, parent 57; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[44546498601159855829573173248, 33172924490225424553937469440, 35068520175381163099876753408, 45494296443737725102542815232, 609434012777569942519479795712, 1102288890918061964463693627392, 33172924490225424553937469440, 609434012777569942519479795712, 36016318017959032372846395392, 36016318017959032372846395392, 35068520175381163099876753408, 35068520175381163099876753408, 1102288890918061964463693627392, 35068520175381163099876753408, 44546498601159855829573173248, 45494296443737725102542815232], [8394780891403984989159686144, 205807531531194470701979402240, 152189253579646437545411084288, 169791213513235438329133006848, 8394780891403984989159686144, 169520414129641761393998823424, 172499207349172207680474841088, 8394780891403984989159686144, 205807531531194470701979402240, 8394780891403984989159686144], [39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800], [], [198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840], [81549300087924425608979808256, 1975597560194556246204639870976, 1496824250000935424887403577344, 1667814717927228575357845110784, 81549300087924425608979808256, 1667814717927228575357845110784, 1665184095343747142273684471808, 81549300087924425608979808256, 1975597560194556246204639870976, 81549300087924425608979808256], [1070508648972032592719017672704, 802881486729024444539263254528, 847486013769525802569222324224, 1092810912492283271733997207552, 14630284869284445433826574860288, 25580696257727528830181526470656, 780579223208773765524283719680, 14630284869284445433826574860288, 825183750249275123554242789376, 847486013769525802569222324224, 847486013769525802569222324224, 825183750249275123554242789376, 25580696257727528830181526470656, 825183750249275123554242789376, 1070508648972032592719017672704, 1092810912492283271733997207552], [184762550863343006028694290432, 2771438262950145090430414356480, 4865413839401365825422282981376, 184762550863343006028694290432, 3079375847722383433811571507200, 184762550863343006028694290432, 4865413839401365825422282981376, 4834620080924141991084167266304, 3079375847722383433811571507200, 74613276790313350601254377619456, 4773032563969694322407935836160, 2771438262950145090430414356480, 4865413839401365825422282981376, 184762550863343006028694290432, 4773032563969694322407935836160, 184762550863343006028694290432, 4865413839401365825422282981376, 4865413839401365825422282981376, 184762550863343006028694290432], [34120722332803293826907111424, 38859711545692640191755321344, 30329530962491816735028543488, 406605274465905918103976411136, 36016318017959032372846395392, 30329530962491816735028543488, 36016318017959032372846395392, 35068520175381163099876753408, 1325021383923861243611559493632, 35068520175381163099876753408, 406605274465905918103976411136, 1325021383923861243611559493632, 34120722332803293826907111424, 35068520175381163099876753408, 35068520175381163099876753408, 38859711545692640191755321344]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [475369012864517888518425411584, 475368937306654162604101992448], [3624730657706316782402491383808, 13271029232615166227247525789696, 3624334200872980427077865963520], [4463816492919548679978074767360, 174552205539663990125923550625792, 174552206375522857593850753449984, 4463837993854145185472732725248], [640007180071645969990373343232, 107985379554001317217942840016896, 1086369237082032813366637817233408, 107985555013527988239610754891776, 640007180071645969990373343232], [727661451656561649799424638976, 132613336059850318520135043776512, 132613346789066967599968969293824, 727650722439912569965499121664], [182949705206066592275834601472, 8268993845757917207994849820672, 183926163090828997425606164480], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3
