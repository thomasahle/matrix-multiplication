import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
13, parent 54; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[2785365088392105618523029504, 58144496220185204786668240896, 3017478845758114420066615296, 62554657610139372015996370944, 93657901097184551422836867072, 2901421967075110019294822400, 93657901097184551422836867072, 97603834972406701049077825536, 58144496220185204786668240896, 2901421967075110019294822400], [73754146403049296690474385408, 83270810455055657553761402880, 71374980390047706474652631040, 939770575135628135249592975360, 83270810455055657553761402880, 71374980390047706474652631040, 83270810455055657553761402880, 83270810455055657553761402880, 3452169884865307403157365587968, 85649976468057247769583157248, 939770575135628135249592975360, 3452169884865307403157365587968, 73754146403049296690474385408, 83270810455055657553761402880, 85649976468057247769583157248, 83270810455055657553761402880], [33656494818071276223819939840, 488019174862033505245389127680, 863850033663829423078045122560, 28047079015059396853183283200, 538503917089140419581119037440, 28047079015059396853183283200, 858240617860817543707408465920, 897506528481900699301865062400, 538503917089140419581119037440, 13748678133182116337430445424640, 880678281072865061189955092480, 488019174862033505245389127680, 858240617860817543707408465920, 28047079015059396853183283200, 880678281072865061189955092480, 28047079015059396853183283200, 858240617860817543707408465920, 897506528481900699301865062400, 33656494818071276223819939840], [46364723033860258108331261952, 34526921408193809229608386560, 36499888345804884042728865792, 47351206502665795514891501568, 634308870441960552418234073088, 1147280274220840003829558673408, 34526921408193809229608386560, 634308870441960552418234073088, 37486371814610421449289105408, 37486371814610421449289105408, 36499888345804884042728865792, 36499888345804884042728865792, 1147280274220840003829558673408, 36499888345804884042728865792, 46364723033860258108331261952, 47351206502665795514891501568], [4642275147320176030871715840, 3481706360490132023153786880, 3675134491628472691106775040, 4738989212889346364848209920, 63444427013375739088580116480, 110931033207838373071038709760, 3384992294920961689177292800, 63444427013375739088580116480, 3578420426059302357130280960, 3675134491628472691106775040, 3675134491628472691106775040, 3578420426059302357130280960, 110931033207838373071038709760, 3578420426059302357130280960, 4642275147320176030871715840, 4738989212889346364848209920], [2089023816294079213892272128, 31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 34817063604901320231537868800, 2089023816294079213892272128, 55010960495744085965829832704, 54662789859695072763514454016, 34817063604901320231537868800, 843617451146758989210162561024, 53966448587597046358883696640, 31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 53966448587597046358883696640, 2089023816294079213892272128, 55010960495744085965829832704, 55010960495744085965829832704, 2089023816294079213892272128], [4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384, 4410161389954167229328130048, 3713820117856140824697372672, 4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152, 49788400955008887931099152384, 162247516398840152278966468608, 4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[31612036843191470699824036184064], [363894939349344333754959692562432, 363894961506687871379335035224064], [835133125110451415672293097996288, 3052623698279491787560335167193088, 835113172247868225056120158289920], [58516233982005072888120861523968, 2298045842346208243888782816837632, 2298046174186900995138751983255552, 58516681133442602849086855970816], [285024124247575777664749797376, 56821417258932543417004559695872, 589174665955671122999430608846848, 56821495338539971183718522945536, 285024124247575777664749797376], [70698175548089311792270934016, 13516931695648244585500516548608, 13516932158440159906725747490816, 70697712756173990567039991808], [], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent0
