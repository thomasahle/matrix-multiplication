import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
11, parent 46; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[39343281873538491861637791744, 570477587166308131993747980288, 1009810901420821291115369988096, 32786068227948743218031493120, 629492509976615869786204667904, 32786068227948743218031493120, 1003253687775231542471763689472, 1049154183294359782977007779840, 629492509976615869786204667904, 16071730645340473925479037927424, 1029482542357590537046188883968, 570477587166308131993747980288, 1003253687775231542471763689472, 32786068227948743218031493120, 1029482542357590537046188883968, 32786068227948743218031493120, 1003253687775231542471763689472, 1049154183294359782977007779840, 39343281873538491861637791744], [510921065588813040331022925824, 380473133949116093863527710720, 402214455889065584941443579904, 521791726558787785869980860416, 6989835003693761381549951942656, 12642578708080629061808077930496, 380473133949116093863527710720, 6989835003693761381549951942656, 413085116859040330480401514496, 413085116859040330480401514496, 402214455889065584941443579904, 402214455889065584941443579904, 12642578708080629061808077930496, 402214455889065584941443579904, 510921065588813040331022925824, 521791726558787785869980860416], [51567939761481622076266643456, 1264246265120194605740730613760, 934876843417828116350382374912, 1043003168724160549736102756352, 51567939761481622076266643456, 1041339686796370819991707058176, 1059637988002057847180059738112, 51567939761481622076266643456, 1264246265120194605740730613760, 51567939761481622076266643456], [198844118810214206655671828480, 198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000], [158456325028528675187087900672], [198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840], [49769058141895053864303853568, 1205695569824618885551361097728, 913503034927041472541577183232, 1017857511676176262902214295552, 49769058141895053864303853568, 1017857511676176262902214295552, 1016252058187728035358204493824, 49769058141895053864303853568, 1205695569824618885551361097728, 49769058141895053864303853568], [422447038406136018809326141440, 316835278804602014106994606080, 334437238738191014890716528640, 431248018372930519201187102720, 5773442858217192257060790599680, 10094724021913291949464522588160, 308034298837807513715133644800, 5773442858217192257060790599680, 325636258771396514498855567360, 334437238738191014890716528640, 334437238738191014890716528640, 325636258771396514498855567360, 10094724021913291949464522588160, 325636258771396514498855567360, 422447038406136018809326141440, 431248018372930519201187102720], [39343281873538491861637791744, 590149228103077377924566876160, 1036039756003180285689795182592, 39343281873538491861637791744, 655721364558974864360629862400, 39343281873538491861637791744, 1036039756003180285689795182592, 1029482542357590537046188883968, 655721364558974864360629862400, 15888128663263960963458061565952, 1016368115066411039758976286720, 590149228103077377924566876160, 1036039756003180285689795182592, 39343281873538491861637791744, 1016368115066411039758976286720, 39343281873538491861637791744, 1036039756003180285689795182592, 1036039756003180285689795182592, 39343281873538491861637791744]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[158456325028528675187087900672], [792281625142643375935439503360, 792281625142643375935439503360], [4724075672582622638736419061760, 17251887133043054171184112336896, 4723927961681404959103779864576], [5439852826193127505130346774528, 213190237094503067093577653813248, 213190254175302635633084391751680, 5439884820226048946976669564928], [723100779002065461237845590016, 138123203914611390448441757794304, 1416205274494309037197050698006528, 138123434588046979182001511202816, 723100779002065461237845590016], [948224366718602059325343006720, 177394369452890421863742089199616, 177394379232911407886777326764032, 948214586697616036290105442304], [281977527290084289012295532544, 12744871248507615513239768530944, 283482526598708913463319592960], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent0
