import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk11Parent1Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
11, parent 47; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[106366129312973533307348189184, 79208819701150503526748651520, 83735037969787675156848574464, 108629238447292119122398150656, 1455179173366850679077125226496, 2631995923212515302903105191936, 79208819701150503526748651520, 1455179173366850679077125226496, 85998147104106260971898535936, 85998147104106260971898535936, 83735037969787675156848574464, 83735037969787675156848574464, 2631995923212515302903105191936, 83735037969787675156848574464, 106366129312973533307348189184, 108629238447292119122398150656], [34178750772144796027293007872, 837930664091291773572344709120, 619627675288560495720602271744, 691292797875315713197184385024, 34178750772144796027293007872, 690190257527827171389852352512, 702318201350201131270504710144, 34178750772144796027293007872, 837930664091291773572344709120, 34178750772144796027293007872], [298266178215321309983507742720, 297395751625198776977719296000, 295364756248246199964212920320, 297395751625198776977719296000], [475368975085586025561263702016], [554597137599850363154807652352, 554597137599850363154807652352, 554597137599850363154807652352, 554597137599850363154807652352], [84547436120568705962251124736, 2048229823437003167020986925056, 1551854553309793344920028708864, 1729131435498082567098942357504, 84547436120568705962251124736, 1729131435498082567098942357504, 1726404098849031963680805224448, 84547436120568705962251124736, 2048229823437003167020986925056, 84547436120568705962251124736], [454014509407913215819253809152, 340510882055934911864440356864, 359428153281264629190242598912, 463473145020578074482154930176, 6204864961908147282863135391744, 10849055047726592886347585814528, 331052246443270053201539235840, 6204864961908147282863135391744, 349969517668599770527341477888, 359428153281264629190242598912, 359428153281264629190242598912, 349969517668599770527341477888, 10849055047726592886347585814528, 349969517668599770527341477888, 454014509407913215819253809152, 463473145020578074482154930176], [13578654805911514890299768832, 203679822088672723354496532480, 357571243222336558777893912576, 13578654805911514890299768832, 226310913431858581504996147200, 13578654805911514890299768832, 357571243222336558777893912576, 355308134088017972962843951104, 226310913431858581504996147200, 5483513432453933429866056646656, 350781915819380801332744028160, 203679822088672723354496532480, 357571243222336558777893912576, 13578654805911514890299768832, 350781915819380801332744028160, 13578654805911514890299768832, 357571243222336558777893912576, 357571243222336558777893912576, 13578654805911514890299768832]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[], [237684515876991909998503133184, 237684459208594115562760568832], [600533858392268696708486004736, 2205824916322951456401517445120, 600452213398146363412386414592], [373272483703135907450619691008, 14600848503106691167439038709760, 14600849693143044850589632561152, 373274750439047684880322265088], [109250730210636661650391826432, 19856840627653175214165731573760, 201951363670678679920624510435328, 19856874397295894214998654713856, 109250730210636661650391826432], [549072186043751090258463162368, 101021432157243129704664881168384, 101021439377741482012352412909568, 549064965545398782570931421184], [302118779239376023941745213440, 13655219194829588049899751997440, 303731278498616692996413849600], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11.Parent1
