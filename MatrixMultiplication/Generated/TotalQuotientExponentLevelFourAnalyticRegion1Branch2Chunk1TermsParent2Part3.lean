import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 22229216286361116908425630873288704
def positiveArguments : Array ℕ := #[
    855, 5054743, 285, 93, 141522589, 939,
    40437931, 1881, 843, 285, 93, 355318327,
    20821, 4727101605, 515209, 16391, 4727103907, 8417,
    8417, 284849, 15505, 515209, 284849
  ]
def positiveCoefficients : Array ℕ := #[
    135480157899392017284960155074560, 1527702331054077379610455048192, 176406455598166689173125201920, 7195526478346272847851159552, 5346572246900290721229729431552, 145303212111121509766284705792,
    1527701839927963161167352823808, 145535325868487518567828291584, 130447931639696946467495215104, 176406455598166689173125201920, 7195526478346272847851159552, 1677943358174116496414020206592,
    402736711843139104744916647936, 44646212361142609790885859164160, 9965591401565335719539107692544, 317048049748854188841742893056, 44646234102917896922732423020544, 325616915958282680432060268544,
    325616915958282680432060268544, 5509780972662520092574072438784, 299910317329997205661108142080, 9965591401565335719539107692544, 5509780972662520092574072438784
  ]
def positiveScales : Array ℕ := #[
    9, 22, 8, 6, 27, 9,
    25, 10, 9, 8, 6, 28,
    14, 32, 18, 14, 32, 13,
    13, 18, 13, 18, 18
  ]
def negativeArguments : Array ℕ := #[
    1408661345, 11698023567, 204700829613, 204700930011, 11697923169, 1987219325,
    54355500095, 15897749465, 75464025, 2064132915, 603712005, 469996107,
    65228151, 14168648415, 1614049779, 51349821, 14168655339, 26368827,
    26368827, 892376619, 48574155, 1614049779, 892376619, 469992645,
    51349821, 48574155, 65228151, 1413265393, 14107785, 4603593,
    2455453273, 46481439, 706632469, 93111381, 41729343, 14107785,
    4603593, 155958985, 4265874691, 1247671477, 29
  ]
def negativeCoefficients : Array ℕ := #[
    6496303829435619029685370880, 13486902931791994994810683392, 472007976943379554774680600576, 472008208445405993811125993472, 13486787180778775476587986944, 73315452613209690816800358400,
    250670499812740054966473850880, 73315428932201986192163471360, 5568262223788077783554457600, 19038265808562535820238520320, 5568260425230530596873175040, 1083737237683601288529444864,
    150405875987285220368842752, 32670678897734435209299886080, 3721745399430057686999236608, 118404625777224535183982592, 32670694863391431004916809728, 121604750798230603702468608,
    121604750798230603702468608, 2057680388506902057386508288, 112004375735212398147010560, 3721745399430057686999236608, 2057680388506902057386508288, 1083729254855103390720983040,
    118404625777224535183982592, 112004375735212398147010560, 150405875987285220368842752, 6517536253225387608110006272, 520485398683837013289861120, 21230325472630193963139072,
    22647559055991735883434819584, 428715604705371013578227712, 6517534154908249223648509952, 429400453914165535964135424, 384885255342521580880134144, 520485398683837013289861120,
    21230325472630193963139072, 5753870964581013709672939520, 19672874668847953680913137664, 5753869106071548283435614208, 9190466851654663160851098238976
  ]
def negativeScales : Array ℕ := #[
    30, 33, 37, 37, 33, 30,
    35, 33, 26, 30, 29, 28,
    25, 33, 30, 25, 33, 24,
    24, 29, 25, 30, 29, 28,
    25, 25, 25, 30, 23, 22,
    31, 25, 29, 26, 25, 23,
    22, 27, 31, 30, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9739780609762119, 22269206311887477, 8154818109052103, 6539158811107971, 27076457104999203, 9874981347482478,
    25269205848089452, 10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971, 28404536862600906,
    14345751740232655, 32138308728510252, 18974798269056584, 14000616254183968, 32138309431072510, 13039090401998603,
    13039090401998603, 18119837815882965, 13920445905112445, 18974798269056584, 18119837815882965
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30391677670308471, 33445545749541173, 37574725993101800, 37574726700688875, 33445533367593278, 30888103965944057,
    35661706974188096, 33888103499951161, 26169285714964885, 30942888735943444, 29169285248972019, 28808073566788299,
    25958991409854936, 33721983091302297, 30588037927531026, 25613855911690970, 33721983796324946, 24652330059519951,
    24652330059519951, 29733077473536364, 25533685562999532, 30588037927531026, 29733077473536364, 28808062939830694,
    25613855911690970, 25533685562999532, 25958991409854936, 30396385264606928, 23749988159078591, 22134328860909696,
    31193342222456116, 25470151397455536, 29396384800131994, 26472454183324965, 25314558870743748, 23749988159078591,
    22134328860909696, 27216591429743242, 31990194461713996, 30216590963750376, 4857980997143165
  ]

abbrev PositiveTerm := Fin 23
abbrev NegativeTerm := Fin 41
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 30467669367 / 500000000000
noncomputable def negativeCeiling : ℝ := 605215563 / 500000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6496303829435619029685370880, coefficient := (-6496303829435619029685370880) }, { argument := 13486902931791994994810683392, coefficient := (-13486902931791994994810683392) }, { argument := 472007976943379554774680600576, coefficient := (-472007976943379554774680600576) }, { argument := 472008208445405993811125993472, coefficient := (-472008208445405993811125993472) }, { argument := 13486787180778775476587986944, coefficient := (-13486787180778775476587986944) }, { argument := 73315452613209690816800358400, coefficient := (-73315452613209690816800358400) }, { argument := 250670499812740054966473850880, coefficient := (-250670499812740054966473850880) }, { argument := 73315428932201986192163471360, coefficient := (-73315428932201986192163471360) }, { argument := 5568262223788077783554457600, coefficient := (-5568262223788077783554457600) }, { argument := 19038265808562535820238520320, coefficient := (-19038265808562535820238520320) }, { argument := 5568260425230530596873175040, coefficient := (-5568260425230530596873175040) }, { argument := 1083737237683601288529444864, coefficient := (-1083737237683601288529444864) }, { argument := 150405875987285220368842752, coefficient := (-150405875987285220368842752) }, { argument := 32670678897734435209299886080, coefficient := (-32670678897734435209299886080) }, { argument := 3721745399430057686999236608, coefficient := (-3721745399430057686999236608) }, { argument := 118404625777224535183982592, coefficient := (-118404625777224535183982592) }, { argument := 32670694863391431004916809728, coefficient := (-32670694863391431004916809728) }, { argument := 121604750798230603702468608, coefficient := (-121604750798230603702468608) }, { argument := 121604750798230603702468608, coefficient := (-121604750798230603702468608) }, { argument := 2057680388506902057386508288, coefficient := (-2057680388506902057386508288) }, { argument := 112004375735212398147010560, coefficient := (-112004375735212398147010560) }, { argument := 3721745399430057686999236608, coefficient := (-3721745399430057686999236608) }, { argument := 2057680388506902057386508288, coefficient := (-2057680388506902057386508288) }, { argument := 1083729254855103390720983040, coefficient := (-1083729254855103390720983040) }, { argument := 118404625777224535183982592, coefficient := (-118404625777224535183982592) }, { argument := 112004375735212398147010560, coefficient := (-112004375735212398147010560) }, { argument := 150405875987285220368842752, coefficient := (-150405875987285220368842752) }, { argument := 6517536253225387608110006272, coefficient := (-6517536253225387608110006272) }, { argument := 520485398683837013289861120, coefficient := (-520485398683837013289861120) }, { argument := 21230325472630193963139072, coefficient := (-21230325472630193963139072) }, { argument := 22647559055991735883434819584, coefficient := (-22647559055991735883434819584) }, { argument := 428715604705371013578227712, coefficient := (-428715604705371013578227712) }, { argument := 6517534154908249223648509952, coefficient := (-6517534154908249223648509952) }, { argument := 429400453914165535964135424, coefficient := (-429400453914165535964135424) }, { argument := 384885255342521580880134144, coefficient := (-384885255342521580880134144) }, { argument := 520485398683837013289861120, coefficient := (-520485398683837013289861120) }, { argument := 21230325472630193963139072, coefficient := (-21230325472630193963139072) }, { argument := 5753870964581013709672939520, coefficient := (-5753870964581013709672939520) }, { argument := 19672874668847953680913137664, coefficient := (-19672874668847953680913137664) }, { argument := 5753869106071548283435614208, coefficient := (-5753869106071548283435614208) }, { argument := 135480157899392017284960155074560, coefficient := 135480157899392017284960155074560 }, { argument := 1527702331054077379610455048192, coefficient := 1527702331054077379610455048192 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 5346572246900290721229729431552, coefficient := 5346572246900290721229729431552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 1527701839927963161167352823808, coefficient := 1527701839927963161167352823808 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 9190466851654663160851098238976, coefficient := (-9190466851654663160851098238976) }, { argument := 1677943358174116496414020206592, coefficient := 1677943358174116496414020206592 }, { argument := 402736711843139104744916647936, coefficient := 402736711843139104744916647936 }, { argument := 44646212361142609790885859164160, coefficient := 44646212361142609790885859164160 }, { argument := 9965591401565335719539107692544, coefficient := 9965591401565335719539107692544 }, { argument := 317048049748854188841742893056, coefficient := 317048049748854188841742893056 }, { argument := 44646234102917896922732423020544, coefficient := 44646234102917896922732423020544 }, { argument := 325616915958282680432060268544, coefficient := 325616915958282680432060268544 }, { argument := 325616915958282680432060268544, coefficient := 325616915958282680432060268544 }, { argument := 5509780972662520092574072438784, coefficient := 5509780972662520092574072438784 }, { argument := 299910317329997205661108142080, coefficient := 299910317329997205661108142080 }, { argument := 9965591401565335719539107692544, coefficient := 9965591401565335719539107692544 }, { argument := 5509780972662520092574072438784, coefficient := 5509780972662520092574072438784 }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard6


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-14281934404716962253333618942279680)
def positiveArguments : Array ℕ := #[
    355316025, 16391, 15505, 20821, 33825805, 1335055591,
    176103, 6283328605, 180707, 5755, 176103, 100137,
    180707, 2821101, 3453, 667528017, 176103, 5755,
    3453, 5755, 88627, 100137, 33825805, 4024375,
    28702665, 455, 403, 18863, 5135, 14351337,
    18863, 455, 455, 195, 455, 5135,
    195, 2012183, 403
  ]
def positiveCoefficients : Array ℕ := #[
    1677932487286472930490738278400, 317048049748854188841742893056, 299910317329997205661108142080, 402736711843139104744916647936, 159737847788084459417664225280, 6304621775706125566731234574336,
    3406327417785520664852507394048, 29672180405108084257417414574080, 3495381729361612708378063142912, 111317889470115054406944686080, 3406327417785520664852507394048, 1936931276780001946680837537792,
    3495381729361612708378063142912, 54568029418250399670284285116416, 2137303477826209044613337972736, 6304623867714477477984064241664, 3406327417785520664852507394048, 111317889470115054406944686080,
    2137303477826209044613337972736, 111317889470115054406944686080, 3428590995679543675733896331264, 1936931276780001946680837537792, 159737847788084459417664225280, 76018294457994113827471360000,
    542178012660142660950278799360, 70407839734356003134887690240, 62361229479001031348043382784, 2918907870130016015677772529664, 794602762716303463950875361280, 542178182665336044257506492416,
    2918907870130016015677772529664, 70407839734356003134887690240, 70407839734356003134887690240, 60349576915162288401332305920, 70407839734356003134887690240, 794602762716303463950875361280,
    60349576915162288401332305920, 76018124452800730520243666944, 62361229479001031348043382784
  ]
def positiveScales : Array ℕ := #[
    28, 14, 13, 14, 25, 30,
    17, 32, 17, 12, 17, 16,
    17, 21, 11, 29, 17, 12,
    11, 12, 16, 16, 25, 21,
    24, 8, 8, 14, 12, 23,
    14, 8, 8, 7, 8, 12,
    7, 20, 8
  ]
def negativeArguments : Array ℕ := #[
    797, 797, 29
  ]
def negativeCoefficients : Array ℕ := #[
    126289691047737354124109056835584, 126289691047737354124109056835584, 9190466851654663160851098238976
  ]
def negativeScales : Array ℕ := #[
    9, 9, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    28404527515785698, 14000616254183968, 13920445905112445, 14345751740232655, 25011620932653953, 30314252670198891,
    17426059960824880, 32548881885989198, 17463292867023852, 12490600213019580, 17426059960824880, 16611615613980474,
    17463292867023852, 21427826886999068, 11753634618838289, 29314253148915883, 17426059960824880, 12490600213019580,
    11753634618838289, 12490600213019580, 16435458658827129, 16611615613980474, 25011620932653953, 21940333313641403,
    24774681359408926, 8829722735013603, 8654636028526477, 14203271522207836, 12326148561205557, 23774681811779928,
    14203271522207836, 8829722735013603, 8829722735013603, 7607330313749179, 8829722735013603, 12326148561205557,
    7607330313749179, 20940330087234876, 8654636028526477
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9638435914006303, 9638435914006303, 4857980997143165
  ]

abbrev PositiveTerm := Fin 39
abbrev NegativeTerm := Fin 3
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 9608263861 / 250000000000
noncomputable def negativeCeiling : ℝ := 14920644517 / 500000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1677932487286472930490738278400, coefficient := 1677932487286472930490738278400 }, { argument := 317048049748854188841742893056, coefficient := 317048049748854188841742893056 }, { argument := 299910317329997205661108142080, coefficient := 299910317329997205661108142080 }, { argument := 402736711843139104744916647936, coefficient := 402736711843139104744916647936 }, { argument := 126289691047737354124109056835584, coefficient := (-126289691047737354124109056835584) }, { argument := 159737847788084459417664225280, coefficient := 159737847788084459417664225280 }, { argument := 6304621775706125566731234574336, coefficient := 6304621775706125566731234574336 }, { argument := 3406327417785520664852507394048, coefficient := 3406327417785520664852507394048 }, { argument := 29672180405108084257417414574080, coefficient := 29672180405108084257417414574080 }, { argument := 3495381729361612708378063142912, coefficient := 3495381729361612708378063142912 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 3406327417785520664852507394048, coefficient := 3406327417785520664852507394048 }, { argument := 1936931276780001946680837537792, coefficient := 1936931276780001946680837537792 }, { argument := 3495381729361612708378063142912, coefficient := 3495381729361612708378063142912 }, { argument := 54568029418250399670284285116416, coefficient := 54568029418250399670284285116416 }, { argument := 2137303477826209044613337972736, coefficient := 2137303477826209044613337972736 }, { argument := 6304623867714477477984064241664, coefficient := 6304623867714477477984064241664 }, { argument := 3406327417785520664852507394048, coefficient := 3406327417785520664852507394048 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 2137303477826209044613337972736, coefficient := 2137303477826209044613337972736 }, { argument := 111317889470115054406944686080, coefficient := 111317889470115054406944686080 }, { argument := 3428590995679543675733896331264, coefficient := 3428590995679543675733896331264 }, { argument := 1936931276780001946680837537792, coefficient := 1936931276780001946680837537792 }, { argument := 159737847788084459417664225280, coefficient := 159737847788084459417664225280 }, { argument := 126289691047737354124109056835584, coefficient := (-126289691047737354124109056835584) }, { argument := 76018294457994113827471360000, coefficient := 76018294457994113827471360000 }, { argument := 542178012660142660950278799360, coefficient := 542178012660142660950278799360 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 542178182665336044257506492416, coefficient := 542178182665336044257506492416 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 76018124452800730520243666944, coefficient := 76018124452800730520243666944 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 9190466851654663160851098238976, coefficient := (-9190466851654663160851098238976) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
