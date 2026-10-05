import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData0
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData1
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData2
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData3
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData4
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData5
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData6
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData7
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData8
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData9
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData10
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData11
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData12
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData13
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData14
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData15
import MatrixMultiplication.Generated.TotalQuotientExponentScalarPositiveData16
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData0
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData1
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData2
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData3
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData4
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData5
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData6
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData7
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData8
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData9
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData10
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData11
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData12
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData13
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData14
import MatrixMultiplication.Generated.TotalQuotientExponentScalarNegativeData15

/-!
# Generated retained-exponent lower witness

Generated from certificate SHA-256 `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  Positive logarithms were compressed by
concavity chords and negative logarithms by tangents at exact coefficient-weighted means.  The
result is a conservative lower witness; the semantic recurrence adapter is responsible for
showing that this witness is at most the retained base-two copy exponent.
The globally fixed complete-split quotient is `2:1=0|0;2:2=0|0|0;2:3=0|0`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar

open MatrixMultiplication.DyadicEntropy

noncomputable section

def bits : ℕ := 55
def constantNumerator : ℕ := 184146508021618128
def inverseLogCoefficient : ℝ := 890055161759425595949696247752459987017353167969394256981426047074709919238587636265300153430110242879304938024065621964690272822676876128717215470451758562095152009529700223122255222354824045624896406294229484826388274513202660262217102015237081263018101380154421956805621745035766671101159817436039908544022042844572826049381782745651107141537959770959621848980212908174888688031356221366362784905262056017027566652424381622501405493614188606765133424319737541558349892385799383592433950182830029061983866783969029451183634326484547658906553663054914661485935527033869427793669710341429815112016917609645347617500919523067760952461415364028630239447297021086678277458005585248333438498717361220060791123224483544696490256161142497408372297532638156109880921964220082384928570877209512611897941569242803677565411318067848784072220932702291979561455823435057574965793238351350883906154971685860199516018870396868985950861341554676503454438532867167727901556562669170118914460713846785135875213280923350250243012348493012436799682211550575294280602085500540207839662908648643603281058213850895091308477289992991104252289420644868659594897969937373131167525245461229720790347091148802324110889903738751535214520503 / 3818314221727262669162614095245108232935974238577221516619394887859034302757988084325250538346274946403364034353109966087087473011265690823656663237197315668082353485891087447244044786941776948828448786782889862297083356125284631020679562547677515106623244185902483668817800671527137922968977469176333237594518866307708432297748008373408256741320902717106453421165231461080719542588430583219632178611694836730753250194537170306646532410684295592099131151383779781331860771720300697760631038883186752663094434959411314717920003704123482274996529988030545418997250775167541185968973620275651407658413091021128339845981792772892595762488519062168673852013017687465536319139546308945655591584591244061040127581835154145184230907380154059215122724965579894843677855074458671976786121893734814720773059101918386013011578557256605175899475367400856206367460513908909157782774818535297692388458531260651646917871161072535625405463612619799285682246868899070667414475520417702067810778158698588110355293326045273468630872585669574213244793848567039907823218135837664448055620991698790316056611744420618261977709488170323079241954636093122893638354662555620627995170055816147837150370478863081878407108973506019783795015680000
def coarseningSpecification : String := "2:1=0|0;2:2=0|0|0;2:3=0|0"
def retainedExponentFloor : ℝ := 82419803 / 10000000

def positiveExactSum : ℝ :=
  Positive0.exact +
    Positive1.exact +
    Positive2.exact +
    Positive3.exact +
    Positive4.exact +
    Positive5.exact +
    Positive6.exact +
    Positive7.exact +
    Positive8.exact +
    Positive9.exact +
    Positive10.exact +
    Positive11.exact +
    Positive12.exact +
    Positive13.exact +
    Positive14.exact +
    Positive15.exact +
    Positive16.exact

def positiveFloorSum : ℝ :=
  Positive0.floor +
    Positive1.floor +
    Positive2.floor +
    Positive3.floor +
    Positive4.floor +
    Positive5.floor +
    Positive6.floor +
    Positive7.floor +
    Positive8.floor +
    Positive9.floor +
    Positive10.floor +
    Positive11.floor +
    Positive12.floor +
    Positive13.floor +
    Positive14.floor +
    Positive15.floor +
    Positive16.floor

def negativeExactSum : ℝ :=
  Negative0.exact +
    Negative1.exact +
    Negative2.exact +
    Negative3.exact +
    Negative4.exact +
    Negative5.exact +
    Negative6.exact +
    Negative7.exact +
    Negative8.exact +
    Negative9.exact +
    Negative10.exact +
    Negative11.exact +
    Negative12.exact +
    Negative13.exact +
    Negative14.exact +
    Negative15.exact

def negativeCeilingSum : ℝ :=
  Negative0.ceiling +
    Negative1.ceiling +
    Negative2.ceiling +
    Negative3.ceiling +
    Negative4.ceiling +
    Negative5.ceiling +
    Negative6.ceiling +
    Negative7.ceiling +
    Negative8.ceiling +
    Negative9.ceiling +
    Negative10.ceiling +
    Negative11.ceiling +
    Negative12.ceiling +
    Negative13.ceiling +
    Negative14.ceiling +
    Negative15.ceiling

def inverseLogTerm : ℝ := inverseLogCoefficient / Real.log 2
def inverseLogFloor : ℝ := 13451781 / 40000000000

theorem inverseLogFloor_le : inverseLogFloor ≤ inverseLogTerm := by
  unfold inverseLogTerm
  apply le_trans (b :=
      inverseLogCoefficient / MatrixMultiplication.FastDyadicLog.fastLogTwoUpper)
  · norm_num [inverseLogFloor, inverseLogCoefficient,
      MatrixMultiplication.FastDyadicLog.fastLogTwoUpper]
  · have hupper : Real.log 2 ≤ MatrixMultiplication.FastDyadicLog.fastLogTwoUpper :=
      MatrixMultiplication.LogBounds.logTwo_le_logTwoUpper.trans
        MatrixMultiplication.FastDyadicLog.logTwoUpper_le_fastLogTwoUpper
    exact div_le_div_of_nonneg_left (by norm_num [inverseLogCoefficient])
      (Real.log_pos (by norm_num)) hupper

/-- Exact real value of the compressed, conservative retained-exponent witness. -/
def retainedExponentLowerWitness : ℝ :=
  mass bits constantNumerator + positiveExactSum - negativeExactSum + inverseLogTerm

/-- Fully rational endpoint assembled from independently sealed logarithm chunks. -/
def retainedExponentRationalFloor : ℝ :=
  mass bits constantNumerator + positiveFloorSum - negativeCeilingSum + inverseLogFloor

theorem retainedExponentRationalFloor_le :
    retainedExponentRationalFloor ≤ retainedExponentLowerWitness := by
  have hpositive0 := Positive0.exact_bound
  have hpositive1 := Positive1.exact_bound
  have hpositive2 := Positive2.exact_bound
  have hpositive3 := Positive3.exact_bound
  have hpositive4 := Positive4.exact_bound
  have hpositive5 := Positive5.exact_bound
  have hpositive6 := Positive6.exact_bound
  have hpositive7 := Positive7.exact_bound
  have hpositive8 := Positive8.exact_bound
  have hpositive9 := Positive9.exact_bound
  have hpositive10 := Positive10.exact_bound
  have hpositive11 := Positive11.exact_bound
  have hpositive12 := Positive12.exact_bound
  have hpositive13 := Positive13.exact_bound
  have hpositive14 := Positive14.exact_bound
  have hpositive15 := Positive15.exact_bound
  have hpositive16 := Positive16.exact_bound
  have hnegative0 := Negative0.exact_bound
  have hnegative1 := Negative1.exact_bound
  have hnegative2 := Negative2.exact_bound
  have hnegative3 := Negative3.exact_bound
  have hnegative4 := Negative4.exact_bound
  have hnegative5 := Negative5.exact_bound
  have hnegative6 := Negative6.exact_bound
  have hnegative7 := Negative7.exact_bound
  have hnegative8 := Negative8.exact_bound
  have hnegative9 := Negative9.exact_bound
  have hnegative10 := Negative10.exact_bound
  have hnegative11 := Negative11.exact_bound
  have hnegative12 := Negative12.exact_bound
  have hnegative13 := Negative13.exact_bound
  have hnegative14 := Negative14.exact_bound
  have hnegative15 := Negative15.exact_bound
  have hinverse := inverseLogFloor_le
  unfold retainedExponentRationalFloor retainedExponentLowerWitness
    positiveFloorSum positiveExactSum negativeCeilingSum negativeExactSum
  linarith

/-- The directed rational floor requested by the certificate audit. -/
theorem retainedExponentFloor_lt_retainedExponentLowerWitness :
    retainedExponentFloor < retainedExponentLowerWitness := by
  apply lt_of_lt_of_le (b := retainedExponentRationalFloor) ?_
    retainedExponentRationalFloor_le
  norm_num [retainedExponentFloor, retainedExponentRationalFloor,
    positiveFloorSum, negativeCeilingSum, bits, constantNumerator,
    inverseLogFloor, Positive0.floor, Positive1.floor, Positive2.floor, Positive3.floor, Positive4.floor, Positive5.floor, Positive6.floor, Positive7.floor, Positive8.floor, Positive9.floor, Positive10.floor, Positive11.floor, Positive12.floor, Positive13.floor, Positive14.floor, Positive15.floor, Positive16.floor, Negative0.ceiling, Negative1.ceiling, Negative2.ceiling, Negative3.ceiling, Negative4.ceiling, Negative5.ceiling, Negative6.ceiling, Negative7.ceiling, Negative8.ceiling, Negative9.ceiling, Negative10.ceiling, Negative11.ceiling, Negative12.ceiling, Negative13.ceiling, Negative14.ceiling, Negative15.ceiling, mass]

/-- The compressed exact witness is already strictly larger than `8.2`. -/
theorem eightPointTwo_lt_retainedExponentLowerWitness :
    (82 / 10 : ℝ) < retainedExponentLowerWitness := by
  apply lt_of_lt_of_le (b := retainedExponentRationalFloor) ?_
    retainedExponentRationalFloor_le
  norm_num [retainedExponentRationalFloor, positiveFloorSum, negativeCeilingSum,
    bits, constantNumerator, inverseLogFloor, Positive0.floor, Positive1.floor, Positive2.floor, Positive3.floor, Positive4.floor, Positive5.floor, Positive6.floor, Positive7.floor, Positive8.floor, Positive9.floor, Positive10.floor, Positive11.floor, Positive12.floor, Positive13.floor, Positive14.floor, Positive15.floor, Positive16.floor, Negative0.ceiling, Negative1.ceiling, Negative2.ceiling, Negative3.ceiling, Negative4.ceiling, Negative5.ceiling, Negative6.ceiling, Negative7.ceiling, Negative8.ceiling, Negative9.ceiling, Negative10.ceiling, Negative11.ceiling, Negative12.ceiling, Negative13.ceiling, Negative14.ceiling, Negative15.ceiling, mass]

/-- Narrow numerical interface: any semantic retained exponent above the exact witness exceeds
`8.2`. -/
theorem eightPointTwo_lt_of_witness_le {retainedExponent : ℝ}
    (hwitness : retainedExponentLowerWitness ≤ retainedExponent) :
    (82 / 10 : ℝ) < retainedExponent :=
  eightPointTwo_lt_retainedExponentLowerWitness.trans_le hwitness

end

end MatrixMultiplication.Generated.TotalQuotientExponentScalar
