import MatrixMultiplication.BetaFourLocalCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent2Local
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1

/-! Raw compatibility sufficient statistic for level-four region 1, branch 1, chunk
10, parent 44; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  This module identifies the checked
parent-local pooled row with the global recurrence, then materializes the remaining small
unnormalized signed-log form. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2

open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Nonzero numerators of each individually charged boundary row. -/
def expectedFirstNumerators : List (List ℕ) := [[6499185206248246443220402176, 135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168, 227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600], [471306984331680871534250950656, 532120788761575177538670428160, 456103533224207295033146081280, 6005363187452062717936423403520, 532120788761575177538670428160, 456103533224207295033146081280, 532120788761575177538670428160, 532120788761575177538670428160, 22060207556944159503103165464576, 547324239869048754039775297536, 6005363187452062717936423403520, 22060207556944159503103165464576, 471306984331680871534250950656, 532120788761575177538670428160, 547324239869048754039775297536, 532120788761575177538670428160], [322057838345337212141725286400, 4669838656007389576055016652800, 8266151184196988444970949017600, 268381531954447676784771072000, 5152925413525395394267604582400, 268381531954447676784771072000, 8212474877806098909613994803200, 8588209022542325657112674304000, 5152925413525395394267604582400, 131560626964070251159894779494400, 8427180103369657051041811660800, 4669838656007389576055016652800, 8212474877806098909613994803200, 268381531954447676784771072000, 8427180103369657051041811660800, 268381531954447676784771072000, 8212474877806098909613994803200, 8588209022542325657112674304000, 322057838345337212141725286400], [427282741684594535508150845440, 318189275722570398782665523200, 336371520049574421570246410240, 436373863848096546901941288960, 5845591551131793326207255183360, 10572975076152839250978285813760, 318189275722570398782665523200, 5845591551131793326207255183360, 345462642213076432964036853760, 345462642213076432964036853760, 336371520049574421570246410240, 336371520049574421570246410240, 10572975076152839250978285813760, 336371520049574421570246410240, 427282741684594535508150845440, 436373863848096546901941288960], [7195526478346272847851159552, 176406455598166689173125201920, 130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552, 145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552, 176406455598166689173125201920, 7195526478346272847851159552], [], [5570730176784211237046059008, 4178047632588158427784544256, 4410161389954167229328130048, 5686787055467215637817851904, 76133312416050886906296139776, 133117239849406047685246451712, 4061990753905154027012751360, 76133312416050886906296139776, 4294104511271162828556337152, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712, 4294104511271162828556337152, 5570730176784211237046059008, 5686787055467215637817851904], [1624796301562061610805100544, 24371944523430924162076508160, 42786302607800955751200980992, 1624796301562061610805100544, 27079938359367693513418342400, 1624796301562061610805100544, 42786302607800955751200980992, 42515503224207278816066797568, 27079938359367693513418342400, 656146906447479213830126436352, 41973904457019924945798430720, 24371944523430924162076508160, 42786302607800955751200980992, 1624796301562061610805100544, 41973904457019924945798430720, 1624796301562061610805100544, 42786302607800955751200980992, 42786302607800955751200980992, 1624796301562061610805100544]]

/-- Nonzero numerators of each pooled compatibility-cell row. -/
def expectedGroupsNumerators : List (List ℕ) := [[1426106925256758076683791106048], [56568903945615362876677625479168, 56568912124754111206903135600640], [324767777423197971640193191510016, 1186181835109128945293627991523328, 324766912923177785108592146251776], [60421569821928986083752815886336, 2375844028928690607202537266216960, 2375844354658641129619185526112256, 60422041217996039097477337448448], [660809752223198770035549011968, 130345443234397716514658641248256, 1353845714031849313501975901372416, 130345597707727737663623226458112, 660809752223198770035549011968], [194155488913498182187382472704, 37518449867876326512339537887232, 37518450774570691223311418916864, 194154582219133471215501443072], [10070625974645867464724840448, 455173973160986268329991733248, 10124375949953889766547128320], [], []]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2
