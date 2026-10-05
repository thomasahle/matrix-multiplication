import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
8, parent 35; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[12998370412496492886440804352, 188476370981199146853391663104, 333624840587409984085313978368, 10831975343747077405367336960, 207973926599943886183052869632, 10831975343747077405367336960, 331458445518660568604240510976, 346623210999906476971754782720, 207973926599943886183052869632, 5309834313504817344111068577792, 340124025793658230528534380544, 188476370981199146853391663104, 331458445518660568604240510976, 10831975343747077405367336960, 340124025793658230528534380544, 10831975343747077405367336960, 331458445518660568604240510976, 346623210999906476971754782720, 12998370412496492886440804352], [476374801367505397034619240448, 354747192507716785025780285440, 375018460651014887027253444608, 486510435439154448035355820032, 6517212708070339793473620672512, 11787742425327846313856642056192, 354747192507716785025780285440, 6517212708070339793473620672512, 385154094722663938027990024192, 385154094722663938027990024192, 375018460651014887027253444608, 375018460651014887027253444608, 11787742425327846313856642056192, 375018460651014887027253444608, 476374801367505397034619240448, 486510435439154448035355820032], [88744826566270698456830967808, 2175679619044055833135210823680, 1608857823556262339765774319616, 1794935685711346062336548929536, 88744826566270698456830967808, 1792072949370498620450844704768, 1823563049119820481193591177216, 88744826566270698456830967808, 2175679619044055833135210823680, 88744826566270698456830967808], [536879120787578357970313936896, 535312352925357798559894732800, 531656561246843159935583256576, 535312352925357798559894732800], [475368975085586025561263702016], [316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344], [31780241946029371744675954688, 769901990369937360653278773248, 583321215073893952345826394112, 649957206251052312455630815232, 31780241946029371744675954688, 649957206251052312455630815232, 648932037156019106915479977984, 31780241946029371744675954688, 769901990369937360653278773248, 31780241946029371744675954688], [103986963299971943091526434816, 77990222474978957318644826112, 82323012612477788280791760896, 106153358368721358572599902208, 1421155165099616555584194609152, 2484855143855579556791267098624, 75823827406229541837571358720, 1421155165099616555584194609152, 80156617543728372799718293504, 82323012612477788280791760896, 82323012612477788280791760896, 80156617543728372799718293504, 2484855143855579556791267098624, 80156617543728372799718293504, 103986963299971943091526434816, 106153358368721358572599902208]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [237684459208594115562760568832, 237684515876991909998503133184], [601323320009042429647085633536, 2204177183487382096923909423104, 601310484616941989951394807808], [369049771928352767918404009984, 14486228484706330065007481454592, 14486230449210786938779890352128, 369052237003656825873205559296], [100509233172060387309642579968, 19916695980581706296977579311104, 205493633035437167525795062611968, 19916728149342187605000775008256, 100509233172060387309642579968], [537661007728513567997990797312, 101468598229386821083689845260288, 101468602965920403401943994597376, 537656271194931249743841460224], [292048153264730156477020372992, 13200045221668601781569760264192, 293606902548662803229866721280], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1
