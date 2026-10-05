import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk14Parent0Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
14, parent 58; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[3597763239173136423925579776, 88203227799083344586562600960, 65223965819848473233747607552, 72767662934243759283914145792, 3597763239173136423925579776, 72651606055560754883142352896, 73928231721073803291632074752, 3597763239173136423925579776, 88203227799083344586562600960, 3597763239173136423925579776], [39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800], [158456325028528675187087900672], [356526731314189519170947776512, 356526731314189519170947776512, 356526731314189519170947776512, 356526731314189519170947776512], [86945944946684130244868177920, 2106335634030960703674064568320, 1595878795956879680946128814080, 1778184809554765760491820154880, 86945944946684130244868177920, 1778184809554765760491820154880, 1775380101653259820806501826560, 86945944946684130244868177920, 2106335634030960703674064568320, 86945944946684130244868177920], [666630711155177278033178394624, 499973033366382958524883795968, 527749312997848678442932895744, 680518850970910137992202944512, 9110619719120756133120104726528, 15929696368645590373001158721536, 486084893550650098565859246080, 9110619719120756133120104726528, 513861173182115818483908345856, 527749312997848678442932895744, 527749312997848678442932895744, 513861173182115818483908345856, 15929696368645590373001158721536, 513861173182115818483908345856, 666630711155177278033178394624, 680518850970910137992202944512], [30987186608362175006068703232, 464807799125432625091030548480, 815995914020203941826475851776, 30987186608362175006068703232, 516453110139369583434478387200, 30987186608362175006068703232, 815995914020203941826475851776, 810831382918810245992131067904, 516453110139369583434478387200, 12513658858676925006617411321856, 800502320716022854323441500160, 464807799125432625091030548480, 815995914020203941826475851776, 30987186608362175006068703232, 800502320716022854323441500160, 30987186608362175006068703232, 815995914020203941826475851776, 815995914020203941826475851776, 30987186608362175006068703232], [4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384, 4410161389954167229328130048, 3713820117856140824697372672, 4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152, 49788400955008887931099152384, 162247516398840152278966468608, 4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [79228153069531371854253522944, 79228171958997303332834377728], [282832662857535290106882031616, 1018897849012352445742791524352, 282832738415399016021205450752], [214413921664695844493164806144, 8381842051143371551020809191424, 8381841031112211251177443033088, 214414261675082611107620192256], [72748924584039732531706200064, 11447228124278577804369066983424, 113787064236904955933155781509120, 11447246451782897821462141337600, 72748924584039732531706200064], [279664087173791278518557999104, 50267903596926856106162482315264, 50267908361794637321634502934528, 279659322306010063046537379840], [120847511695750409576698085376, 5462087677931835219959900798976, 121492511399446677198565539840], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14.Parent0
