import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 3591143834686658186385832447836160
def positiveArguments : Array ℕ := #[
    213, 9, 261, 231, 15, 9,
    15, 459, 15, 9, 7353, 471,
    261, 459, 15, 471, 15, 459,
    15, 9, 1175, 875, 925, 75,
    16075, 29075, 875, 16075, 475, 475,
    925, 925, 29075, 925, 1175, 75,
    2697, 8265, 24447, 54549, 2697, 27231,
    55419, 2697
  ]
def positiveCoefficients : Array ℕ := #[
    33751197231076607814849722843136, 1392682544196052809261514752, 20193896890842765734291963904, 35745518634365355437712211968, 1160568786830044007717928960, 22282920707136844948184236032,
    1160568786830044007717928960, 35513404876999346636168626176, 37138201178561408246973726720, 22282920707136844948184236032, 568910819304087572583328776192, 36441859906463381842342969344,
    20193896890842765734291963904, 35513404876999346636168626176, 1160568786830044007717928960, 36441859906463381842342969344, 1160568786830044007717928960, 35513404876999346636168626176,
    37138201178561408246973726720, 1392682544196052809261514752, 90911221635020113937904435200, 67699845898419233783545856000, 71568408521186047142605619200, 92845502946403520617434316800,
    1243742883219530494937713868800, 2249569165138901968293252300800, 67699845898419233783545856000, 1243742883219530494937713868800, 73502689832569453822135500800, 73502689832569453822135500800,
    71568408521186047142605619200, 71568408521186047142605619200, 2249569165138901968293252300800, 71568408521186047142605619200, 90911221635020113937904435200, 92845502946403520617434316800,
    52167566968010478146920906752, 1278946803086708496505157713920, 945747504387802861889340309504, 1055131112546534509616755113984, 52167566968010478146920906752, 1053448287805630945805564116992,
    1071959359955570147728665083904, 52167566968010478146920906752
  ]
def positiveScales : Array ℕ := #[
    7, 3, 8, 7, 3, 3,
    3, 8, 3, 3, 12, 8,
    8, 8, 3, 8, 3, 8,
    3, 3, 10, 9, 9, 6,
    13, 14, 9, 13, 8, 8,
    9, 9, 14, 9, 10, 6,
    11, 13, 14, 15, 11, 14,
    15, 11
  ]
def negativeArguments : Array ℕ := #[
    279, 227943, 14601, 58640809, 14229, 465,
    14601, 465, 14229, 465, 318463, 958261855,
    150894792285, 37723705505, 3833087395, 15020735, 53840245, 3756275,
    3, 25
  ]
def negativeCoefficients : Array ℕ := #[
    84322575918120384935755776, 2152860766409511077891014656, 137902546032759379530350592, 2163463991796567475578994688, 134389105369504363491360768, 4391800829068770048737280,
    137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768, 140537626530200641559592960, 11749210915891529872572416, 4419202798695792915691601920,
    173969850958559845032300380160, 173969885240680784516895211520, 4419248886732939574399467520, 70933415512066980298945986560, 254253368417490001368469995520, 70954028641764706300303769600,
    950737950171172051122527404032, 7922816251426433759354395033600
  ]
def negativeScales : Array ℕ := #[
    8, 17, 13, 25, 13, 8,
    13, 8, 13, 8, 18, 29,
    37, 35, 31, 23, 25, 21,
    1, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7734709620215885, 3169925001442312, 8027905996569884, 7851749041305231, 3906890595303263, 3169925001442312,
    3906890595303263, 8842350343321225, 3906890595303263, 3169925001442312, 12844117269492213, 8879583249426338,
    8027905996569884, 8842350343321225, 3906890595303263, 8879583249426338, 3906890595303263, 8842350343321225,
    3906890595303263, 3169925001442312, 10198445041452361, 9773139206696762, 9853309555289512, 6228818690495880,
    13972531116166486, 14827491571178588, 9773139206696762, 13972531116166486, 8891783702985444, 8891783702985444,
    9853309555289512, 9853309555289512, 14827491571178588, 9853309555289512, 10198445041452361, 6228818690495880,
    11397139806235602, 13012799104179676, 14577369816069468, 15735265128640690, 11397139806235602, 14732962342771775,
    15758093058088401, 11397139806235602
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8124121311829188, 17798313580599046, 13833779561266426, 25805401671750691, 13796546654402698, 8861086908132560,
    13833779561266426, 8861086908132560, 13796546654402698, 8861086908132560, 18280766239956687, 29835844701649961,
    37134752059869114, 35134752344163437, 31835859747494348, 23840452074704782, 25682181639204881, 21840871258533351,
    1584962500724866, 4643856189792934
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 20
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
noncomputable def positiveFloor : ℝ := 2781602759 / 500000000000
noncomputable def negativeCeiling : ℝ := 91811213 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2163463991796567475578994688, coefficient := (-2163463991796567475578994688) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 11749210915891529872572416, coefficient := (-11749210915891529872572416) }, { argument := 4419202798695792915691601920, coefficient := (-4419202798695792915691601920) }, { argument := 173969850958559845032300380160, coefficient := (-173969850958559845032300380160) }, { argument := 173969885240680784516895211520, coefficient := (-173969885240680784516895211520) }, { argument := 4419248886732939574399467520, coefficient := (-4419248886732939574399467520) }, { argument := 70933415512066980298945986560, coefficient := (-70933415512066980298945986560) }, { argument := 254253368417490001368469995520, coefficient := (-254253368417490001368469995520) }, { argument := 70954028641764706300303769600, coefficient := (-70954028641764706300303769600) }, { argument := 33751197231076607814849722843136, coefficient := 33751197231076607814849722843136 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 35745518634365355437712211968, coefficient := 35745518634365355437712211968 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 568910819304087572583328776192, coefficient := 568910819304087572583328776192 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 90911221635020113937904435200, coefficient := 90911221635020113937904435200 }, { argument := 67699845898419233783545856000, coefficient := 67699845898419233783545856000 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 92845502946403520617434316800, coefficient := 92845502946403520617434316800 }, { argument := 1243742883219530494937713868800, coefficient := 1243742883219530494937713868800 }, { argument := 2249569165138901968293252300800, coefficient := 2249569165138901968293252300800 }, { argument := 67699845898419233783545856000, coefficient := 67699845898419233783545856000 }, { argument := 1243742883219530494937713868800, coefficient := 1243742883219530494937713868800 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 2249569165138901968293252300800, coefficient := 2249569165138901968293252300800 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 90911221635020113937904435200, coefficient := 90911221635020113937904435200 }, { argument := 92845502946403520617434316800, coefficient := 92845502946403520617434316800 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 52167566968010478146920906752, coefficient := 52167566968010478146920906752 }, { argument := 1278946803086708496505157713920, coefficient := 1278946803086708496505157713920 }, { argument := 945747504387802861889340309504, coefficient := 945747504387802861889340309504 }, { argument := 1055131112546534509616755113984, coefficient := 1055131112546534509616755113984 }, { argument := 52167566968010478146920906752, coefficient := 52167566968010478146920906752 }, { argument := 1053448287805630945805564116992, coefficient := 1053448287805630945805564116992 }, { argument := 1071959359955570147728665083904, coefficient := 1071959359955570147728665083904 }, { argument := 52167566968010478146920906752, coefficient := 52167566968010478146920906752 }] }

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

end TermShard8


end Parent1

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1677881207099390716047623463108608)
def positiveArguments : Array ℕ := #[
    8265, 2697, 6939, 27675, 13743, 27675,
    5, 5, 5, 5, 5, 93,
    2253, 1707, 951, 93, 951, 1899,
    93, 2253, 93, 15020735, 53840245, 3756275,
    3845059, 302688307, 18918023, 7690199, 474509, 53061385,
    278051333, 1658171, 474509, 6964897, 1326823775, 1326823825,
    6964847, 25235033, 1140577583, 3171215
  ]
def positiveCoefficients : Array ℕ := #[
    1278946803086708496505157713920, 52167566968010478146920906752, 536879120787578357970313936896, 535312352925357798559894732800, 531656561246843159935583256576, 535312352925357798559894732800,
    792281625142643375935439503360, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 7195526478346272847851159552,
    174317431781872609959232929792, 132072727941259008078300315648, 147160122170049580178633392128, 7195526478346272847851159552, 147160122170049580178633392128, 146928008412683571377089806336,
    7195526478346272847851159552, 174317431781872609959232929792, 7195526478346272847851159552, 141866831024133960597891973120, 508506736834980002736939991040, 141908057283529412600607539200,
    36315555492512550311457456128, 1429405115733357411424295452672, 1429405403797712866472653488128, 36315938004197662752719765504, 4481610794839984961411350528, 1002301224234568597989322915840,
    10504482363811412135241941254144, 1002302867618104636625857282048, 4481610794839984961411350528, 65781592298878686679871258624, 12531496247469150990693616844800, 12531496719705799277658138214400,
    65781120062230399715349889024, 119169074033309431665910611968, 5386225349071670841904902176768, 119805115407787695570807685120
  ]
def positiveScales : Array ℕ := #[
    13, 11, 12, 14, 13, 14,
    2, 2, 2, 2, 2, 6,
    11, 10, 9, 6, 9, 10,
    6, 11, 6, 23, 25, 21,
    21, 28, 24, 22, 18, 25,
    28, 20, 18, 22, 30, 30,
    22, 24, 30, 21
  ]
def negativeArguments : Array ℕ := #[
    87, 27, 5, 5, 3, 5,
    37, 79, 159, 71
  ]
def negativeCoefficients : Array ℕ := #[
    6892850138740997370638323679232, 2139160387885137115025686659072, 792281625142643375935439503360, 792281625142643375935439503360, 950737950171172051122527404032, 792281625142643375935439503360,
    2931442013027780490961126162432, 12518049677253765339779944153088, 25194555679536059354746976206848, 5625199538512767969141620473856
  ]
def negativeScales : Array ℕ := #[
    6, 4, 2, 2, 1, 2,
    5, 6, 7, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13012799104179676, 11397139806235602, 12760512051339829, 14756295696540282, 13746409348226269, 14756295696540282,
    2321928094887362, 2321928094887362, 2321928094887362, 2321928094887362, 2321928094887362, 6539158811107971,
    11137631598235427, 10737247343017206, 9893301530621223, 6539158811107971, 9893301530621223, 10891024189919810,
    6539158811107971, 11137631598235427, 6539158811107971, 23840452073173610, 25682181639154612, 21840871256989729,
    21874574304754621, 28173257703313065, 24173257994055676, 22874589500578991, 18856075925382134, 25661158997268926,
    28050776012651793, 20661161362724815, 18856075925382134, 22731670587082111, 30305329622722639, 30305329677089128,
    22731660230143458, 24588924637469579, 30087117437245284, 21596604260994202
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6442943495848765, 4754887502413606, 2321928094887363, 2321928094887363, 1584962500724866, 2321928094887363,
    5209453365628950, 6303780748177104, 7312882955284356, 6149747119504683
  ]

abbrev PositiveTerm := Fin 40
abbrev NegativeTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 8595843057 / 500000000000
noncomputable def negativeCeiling : ℝ := 140919429 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1278946803086708496505157713920, coefficient := 1278946803086708496505157713920 }, { argument := 52167566968010478146920906752, coefficient := 52167566968010478146920906752 }, { argument := 6892850138740997370638323679232, coefficient := (-6892850138740997370638323679232) }, { argument := 536879120787578357970313936896, coefficient := 536879120787578357970313936896 }, { argument := 535312352925357798559894732800, coefficient := 535312352925357798559894732800 }, { argument := 531656561246843159935583256576, coefficient := 531656561246843159935583256576 }, { argument := 535312352925357798559894732800, coefficient := 535312352925357798559894732800 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 132072727941259008078300315648, coefficient := 132072727941259008078300315648 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 146928008412683571377089806336, coefficient := 146928008412683571377089806336 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 141866831024133960597891973120, coefficient := 141866831024133960597891973120 }, { argument := 508506736834980002736939991040, coefficient := 508506736834980002736939991040 }, { argument := 141908057283529412600607539200, coefficient := 141908057283529412600607539200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 36315555492512550311457456128, coefficient := 36315555492512550311457456128 }, { argument := 1429405115733357411424295452672, coefficient := 1429405115733357411424295452672 }, { argument := 1429405403797712866472653488128, coefficient := 1429405403797712866472653488128 }, { argument := 36315938004197662752719765504, coefficient := 36315938004197662752719765504 }, { argument := 2931442013027780490961126162432, coefficient := (-2931442013027780490961126162432) }, { argument := 4481610794839984961411350528, coefficient := 4481610794839984961411350528 }, { argument := 1002301224234568597989322915840, coefficient := 1002301224234568597989322915840 }, { argument := 10504482363811412135241941254144, coefficient := 10504482363811412135241941254144 }, { argument := 1002302867618104636625857282048, coefficient := 1002302867618104636625857282048 }, { argument := 4481610794839984961411350528, coefficient := 4481610794839984961411350528 }, { argument := 12518049677253765339779944153088, coefficient := (-12518049677253765339779944153088) }, { argument := 65781592298878686679871258624, coefficient := 65781592298878686679871258624 }, { argument := 12531496247469150990693616844800, coefficient := 12531496247469150990693616844800 }, { argument := 12531496719705799277658138214400, coefficient := 12531496719705799277658138214400 }, { argument := 65781120062230399715349889024, coefficient := 65781120062230399715349889024 }, { argument := 25194555679536059354746976206848, coefficient := (-25194555679536059354746976206848) }, { argument := 119169074033309431665910611968, coefficient := 119169074033309431665910611968 }, { argument := 5386225349071670841904902176768, coefficient := 5386225349071670841904902176768 }, { argument := 119805115407787695570807685120, coefficient := 119805115407787695570807685120 }, { argument := 5625199538512767969141620473856, coefficient := (-5625199538512767969141620473856) }] }

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

end TermShard9


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
