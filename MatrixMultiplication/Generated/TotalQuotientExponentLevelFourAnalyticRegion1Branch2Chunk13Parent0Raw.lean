import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 2, chunk
13, parent 54; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[2998136032644280353271316480, 71761836652324387810558607360, 53676306390889535356954214400, 62283858226545695080862187520, 2998136032644280353271316480, 62187144160976524746885693440, 62477286357684035748815175680, 2998136032644280353271316480, 71761836652324387810558607360, 2998136032644280353271316480], [85301805832008234567267778560, 66345848980450849107874938880, 75823827406229541837571358720, 89092997202319711659146346496, 1052055605261434892996302602240, 2365703415074361705332226392064, 66345848980450849107874938880, 1052055605261434892996302602240, 75823827406229541837571358720, 73928231721073803291632074752, 73928231721073803291632074752, 73928231721073803291632074752, 2365703415074361705332226392064, 73928231721073803291632074752, 85301805832008234567267778560, 89092997202319711659146346496], [23694946064446731824241049600, 398075093882705094647249633280, 862496036745861038402374205440, 28433935277336078189089259520, 454942964437377251025428152320, 33172924490225424553937469440, 862496036745861038402374205440, 862496036745861038402374205440, 454942964437377251025428152320, 10643769772149471935449079480320, 853018058320082345672677785600, 398075093882705094647249633280, 862496036745861038402374205440, 33172924490225424553937469440, 853018058320082345672677785600, 33172924490225424553937469440, 862496036745861038402374205440, 862496036745861038402374205440, 28433935277336078189089259520], [31567471001777197009927667712, 37486371814610421449289105408, 28608020595360584790246948864, 294958557172855684561511645184, 35513404876999346636168626176, 28608020595360584790246948864, 35513404876999346636168626176, 35513404876999346636168626176, 1521157508898138680915889487872, 35513404876999346636168626176, 294958557172855684561511645184, 1521157508898138680915889487872, 31567471001777197009927667712, 35513404876999346636168626176, 35513404876999346636168626176, 37486371814610421449289105408]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[2297616712913665790212774559744], [83704564368868523952977366482944, 83704543023772021382181000577024], [456658034644160904111462052528128, 1594255276814610544948002112405504, 456658032117694835776201863200768], [74199937482633636846381058490368, 46364723033860258108331261952, 2727312492247652213788267625054208, 1147280274220840003829558673408, 36499888345804884042728865792, 2727221959552024994573611469635584, 37486371814610421449289105408, 37486371814610421449289105408, 634308870441960552418234073088, 34526921408193809229608386560, 1147280274220840003829558673408, 634308870441960552418234073088, 74290509591131522091096167415808, 36499888345804884042728865792, 34526921408193809229608386560, 46364723033860258108331261952], [1527169501721448714671348514816, 198262856929438528981080435851264, 858240617860817543707408465920, 2067494568532096816064431845801984, 880678281072865061189955092480, 28047079015059396853183283200, 858240617860817543707408465920, 488019174862033505245389127680, 880678281072865061189955092480, 13748678133182116337430445424640, 538503917089140419581119037440, 198262903912262667051180666912768, 858240617860817543707408465920, 28047079015059396853183283200, 538503917089140419581119037440, 28047079015059396853183283200, 863850033663829423078045122560, 488019174862033505245389127680, 1527150881430406759660270911488], [966344757489413455499914903552, 74152417767927762813316006674432, 83270810455055657553761402880, 73754146403049296690474385408, 3452169884865307403157365587968, 939770575135628135249592975360, 74152426579863619848073975431168, 3452169884865307403157365587968, 83270810455055657553761402880, 83270810455055657553761402880, 71374980390047706474652631040, 83270810455055657553761402880, 939770575135628135249592975360, 71374980390047706474652631040, 966335945553556420741946146816, 73754146403049296690474385408], [124936164930817845620587364352, 58144496220185204786668240896, 1279641274301679306530283847680, 93657901097184551422836867072, 2901421967075110019294822400, 93657901097184551422836867072, 62554657610139372015996370944, 125052221809500850021359157248, 58144496220185204786668240896, 2785365088392105618523029504], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent0
