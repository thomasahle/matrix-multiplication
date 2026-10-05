import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 1,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1802543562279653049820342269247488
def positiveArguments : Array ℕ := #[
    665, 20349, 665, 399, 5217, 3885,
    4107, 333, 71373, 129093, 3885, 71373,
    2109, 2109, 4107, 4107, 129093, 4107,
    5217, 333, 93, 285, 843, 1881,
    93, 939, 1911, 93, 285, 93,
    257, 1025, 509, 1025, 1, 1,
    1, 1, 403, 9763, 7397, 4121,
    403, 4121, 8229, 403, 9763, 403,
    231, 693, 1463, 3773, 3157, 88319,
    2695, 3157, 2849, 1463
  ]
def positiveCoefficients : Array ℕ := #[
    12862970720699654418873712640, 393606904053409425217535606784, 411615063062388941403958804480, 15435564864839585302648455168, 100911456014872326471073923072, 75146828947245349499735900160,
    79440933458516512328292237312, 103058508270507907885352091648, 1380554600373678849380862394368, 2497021773304181184805510053888, 75146828947245349499735900160, 1380554600373678849380862394368,
    81587985714152093742570405888, 81587985714152093742570405888, 79440933458516512328292237312, 79440933458516512328292237312, 2497021773304181184805510053888, 79440933458516512328292237312,
    100911456014872326471073923072, 103058508270507907885352091648, 7195526478346272847851159552, 176406455598166689173125201920, 130447931639696946467495215104, 145535325868487518567828291584,
    7195526478346272847851159552, 145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552, 176406455598166689173125201920, 7195526478346272847851159552,
    39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 39614081257132168796771975168, 39614081257132168796771975168,
    39614081257132168796771975168, 39614081257132168796771975168, 31180614739500515674021691392, 755375537721447976490009362432, 572315154412122368339301367808, 637693862736881514107411365888,
    31180614739500515674021691392, 637693862736881514107411365888, 636688036454962142634055827456, 31180614739500515674021691392, 755375537721447976490009362432, 31180614739500515674021691392,
    571928298149845687003395391488, 428946223612384265252546543616, 452776569368627835544354684928, 583843471027967472149299462144, 7816353408047891055713070350336, 13666703291205687562351969042432,
    417031050734262480106642472960, 7816353408047891055713070350336, 440861396490506050398450614272, 452776569368627835544354684928
  ]
def positiveScales : Array ℕ := #[
    9, 14, 9, 8, 12, 11,
    12, 8, 16, 16, 11, 16,
    11, 11, 12, 12, 16, 12,
    12, 8, 6, 8, 9, 10,
    6, 9, 10, 6, 8, 6,
    8, 10, 8, 10, 0, 0,
    0, 0, 8, 13, 12, 12,
    8, 12, 13, 8, 13, 8,
    7, 9, 10, 11, 11, 16,
    11, 11, 11, 10
  ]
def negativeArguments : Array ℕ := #[
    133, 111, 3, 1, 1, 13
  ]
def negativeCoefficients : Array ℕ := #[
    10537345614397156899941345394688, 8794326039083341472883378487296, 950737950171172051122527404032, 158456325028528675187087900672, 158456325028528675187087900672, 4119864450741745554864285417472
  ]
def negativeScales : Array ℕ := #[
    7, 6, 1, 0, 0, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9377210530388551, 14312670278193841, 9377210530388551, 8640244936221314, 12349004718027742, 11923698882884927,
    12003869231979055, 8379378367071261, 16123090793678053, 16978051246798597, 11923698882884927, 16123090793678053,
    11042343379793691, 11042343379793691, 12003869231979055, 12003869231979055, 16978051246798597, 12003869231979055,
    12349004718027742, 8379378367071261, 6539158811107971, 8154818109052103, 9719388820935039, 10877284133344468,
    6539158811107971, 9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103, 6539158811107971,
    8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 0, 0,
    0, 0, 8654636028526477, 13253108815655363, 12852724560334773, 12008778748280499,
    8654636028526477, 12008778748280499, 13006501407569433, 8654636028526477, 13253108815655363, 8654636028526477,
    7851749041305231, 9436711542137211, 10514714054138458, 11881496384617007, 11624338545312304, 16430436216710724,
    11396069557639867, 11624338545312304, 11476239906323843, 10514714054138458
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7055282435501190, 6794415866926375, 1584962500724866, 0, 0, 3700439718214233
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 3937583753 / 500000000000
noncomputable def negativeCeiling : ℝ := 1815772191 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 393606904053409425217535606784, coefficient := 393606904053409425217535606784 }, { argument := 411615063062388941403958804480, coefficient := 411615063062388941403958804480 }, { argument := 15435564864839585302648455168, coefficient := 15435564864839585302648455168 }, { argument := 10537345614397156899941345394688, coefficient := (-10537345614397156899941345394688) }, { argument := 100911456014872326471073923072, coefficient := 100911456014872326471073923072 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 79440933458516512328292237312, coefficient := 79440933458516512328292237312 }, { argument := 103058508270507907885352091648, coefficient := 103058508270507907885352091648 }, { argument := 1380554600373678849380862394368, coefficient := 1380554600373678849380862394368 }, { argument := 2497021773304181184805510053888, coefficient := 2497021773304181184805510053888 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 1380554600373678849380862394368, coefficient := 1380554600373678849380862394368 }, { argument := 81587985714152093742570405888, coefficient := 81587985714152093742570405888 }, { argument := 81587985714152093742570405888, coefficient := 81587985714152093742570405888 }, { argument := 79440933458516512328292237312, coefficient := 79440933458516512328292237312 }, { argument := 79440933458516512328292237312, coefficient := 79440933458516512328292237312 }, { argument := 2497021773304181184805510053888, coefficient := 2497021773304181184805510053888 }, { argument := 79440933458516512328292237312, coefficient := 79440933458516512328292237312 }, { argument := 100911456014872326471073923072, coefficient := 100911456014872326471073923072 }, { argument := 103058508270507907885352091648, coefficient := 103058508270507907885352091648 }, { argument := 8794326039083341472883378487296, coefficient := (-8794326039083341472883378487296) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 147856463442147606583264149504, coefficient := 147856463442147606583264149504 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 755375537721447976490009362432, coefficient := 755375537721447976490009362432 }, { argument := 572315154412122368339301367808, coefficient := 572315154412122368339301367808 }, { argument := 637693862736881514107411365888, coefficient := 637693862736881514107411365888 }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 637693862736881514107411365888, coefficient := 637693862736881514107411365888 }, { argument := 636688036454962142634055827456, coefficient := 636688036454962142634055827456 }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 755375537721447976490009362432, coefficient := 755375537721447976490009362432 }, { argument := 31180614739500515674021691392, coefficient := 31180614739500515674021691392 }, { argument := 4119864450741745554864285417472, coefficient := (-4119864450741745554864285417472) }, { argument := 571928298149845687003395391488, coefficient := 571928298149845687003395391488 }, { argument := 428946223612384265252546543616, coefficient := 428946223612384265252546543616 }, { argument := 452776569368627835544354684928, coefficient := 452776569368627835544354684928 }, { argument := 583843471027967472149299462144, coefficient := 583843471027967472149299462144 }, { argument := 7816353408047891055713070350336, coefficient := 7816353408047891055713070350336 }, { argument := 13666703291205687562351969042432, coefficient := 13666703291205687562351969042432 }, { argument := 417031050734262480106642472960, coefficient := 417031050734262480106642472960 }, { argument := 7816353408047891055713070350336, coefficient := 7816353408047891055713070350336 }, { argument := 440861396490506050398450614272, coefficient := 440861396490506050398450614272 }, { argument := 452776569368627835544354684928, coefficient := 452776569368627835544354684928 }] }

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

end TermShard12


end Parent2

namespace Parent2

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-133633643144208083841504542701125632)
def positiveArguments : Array ℕ := #[
    1463, 2849, 88319, 2849, 231, 3773,
    2283, 34245, 60119, 2283, 19025, 2283,
    60119, 119477, 19025, 1843903, 117955, 34245,
    60119, 2283, 117955, 2283, 60119, 60119,
    2283, 1197, 5453, 133, 57057, 2527,
    133, 2527, 4921, 92967, 4921, 57057,
    92967, 1197, 4921, 4921, 5453, 1,
    545259521, 545259519, 11780423073, 10744535573, 11779873291, 3880063033,
    75948187427, 75948190341, 3880082551, 32816417, 6115872483, 1949967859,
    6115883131, 32816417
  ]
def positiveCoefficients : Array ℕ := #[
    452776569368627835544354684928, 440861396490506050398450614272, 13666703291205687562351969042432, 440861396490506050398450614272, 571928298149845687003395391488, 583843471027967472149299462144,
    176638569355532697974668787712, 2649578540332990469620031815680, 4651482326362361046666278076416, 176638569355532697974668787712, 2943976155925544966244479795200, 176638569355532697974668787712,
    4651482326362361046666278076416, 4622042564803105597003833278464, 2943976155925544966244479795200, 71332542258075954532103745437696, 4563163041684594697678943682560, 2649578540332990469620031815680,
    4651482326362361046666278076416, 176638569355532697974668787712, 4563163041684594697678943682560, 176638569355532697974668787712, 4651482326362361046666278076416, 4651482326362361046666278076416,
    176638569355532697974668787712, 92613389189037511815890731008, 105476359909737166234764443648, 82323012612477788280791760896, 1103642887836030349139364544512, 97758577477317373583440216064,
    82323012612477788280791760896, 97758577477317373583440216064, 95185983333177442699665473536, 3596486613507623375517090054144, 95185983333177442699665473536, 1103642887836030349139364544512,
    3596486613507623375517090054144, 92613389189037511815890731008, 95185983333177442699665473536, 95185983333177442699665473536, 105476359909737166234764443648, 316912650057057350374175801344,
    5149830572871914909319647199232, 5149830553982448977841066344448, 55631475073959427726748374007808, 202958538655743192481783435231232, 55628878801869742687463497793536, 36646159236921476302974469799936,
    1434620698959866397995109101600768, 1434620754003770122323693712441344, 36646343579219501602445031636992, 1239769181829389071797616377856, 231051129817791632307328169017344, 2357366492163758656880738968797184,
    231051532087858109075186052497408, 1239769181829389071797616377856
  ]
def positiveScales : Array ℕ := #[
    10, 11, 16, 11, 7, 11,
    11, 15, 15, 11, 14, 11,
    15, 16, 14, 20, 16, 15,
    15, 11, 16, 11, 15, 15,
    11, 10, 12, 7, 15, 11,
    7, 11, 12, 16, 12, 15,
    16, 10, 12, 12, 12, 0,
    29, 29, 33, 33, 33, 31,
    36, 36, 31, 24, 32, 30,
    32, 24
  ]
def negativeArguments : Array ℕ := #[
    77, 761, 133, 1, 65, 1983,
    9285, 17809
  ]
def negativeCoefficients : Array ℕ := #[
    48804548108786831957623073406976, 120585263346710321817373892411392, 10537345614397156899941345394688, 316912650057057350374175801344, 10299661126854363887160713543680, 314218892531572362895995307032576,
    2942533955779777498224222315479040, 2821948692433067176406848423067648
  ]
def negativeScales : Array ℕ := #[
    6, 9, 7, 0, 6, 10,
    13, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10514714054138458, 11476239906323843, 16430436216710724, 11476239906323843, 7851749041305231, 11881496384617007,
    11156715144224701, 15063605739833220, 15875533391507598, 11156715144224701, 14215608833278269, 11156715144224701,
    15875533391507598, 16866373392249180, 14215608833278269, 20814331332901448, 16847877048674844, 15063605739833220,
    15875533391507598, 11156715144224701, 16847877048674844, 11156715144224701, 15875533391507598, 15875533391507598,
    11156715144224701, 10225207436943501, 12412834440119272, 7055282435501189, 15800116272960613, 11303209948944774,
    7055282435501189, 11303209948944774, 12264735801130139, 16504431080876605, 12264735801130139, 15800116272960613,
    16504431080876605, 10225207436943501, 12264735801130139, 12264735801130139, 12412834440119272, 0,
    29022367815674341, 29022367810382567, 33455672300805898, 33322884073239103, 33455604969924074, 31853432943567186,
    36144296482774350, 36144296538128051, 31853440200782000, 24967914392795304, 32509911180557191, 30860803198320156,
    32509913692349820, 24967914392795304
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6266786540694902, 9571752643506083, 7055282435501190, 0, 6022367813028455, 10953468973280431,
    13180686194822784, 14120318888939864
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 3119687271 / 1250000000
noncomputable def negativeCeiling : ℝ := 1007136792967 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 452776569368627835544354684928, coefficient := 452776569368627835544354684928 }, { argument := 440861396490506050398450614272, coefficient := 440861396490506050398450614272 }, { argument := 13666703291205687562351969042432, coefficient := 13666703291205687562351969042432 }, { argument := 440861396490506050398450614272, coefficient := 440861396490506050398450614272 }, { argument := 571928298149845687003395391488, coefficient := 571928298149845687003395391488 }, { argument := 583843471027967472149299462144, coefficient := 583843471027967472149299462144 }, { argument := 48804548108786831957623073406976, coefficient := (-48804548108786831957623073406976) }, { argument := 176638569355532697974668787712, coefficient := 176638569355532697974668787712 }, { argument := 2649578540332990469620031815680, coefficient := 2649578540332990469620031815680 }, { argument := 4651482326362361046666278076416, coefficient := 4651482326362361046666278076416 }, { argument := 176638569355532697974668787712, coefficient := 176638569355532697974668787712 }, { argument := 2943976155925544966244479795200, coefficient := 2943976155925544966244479795200 }, { argument := 176638569355532697974668787712, coefficient := 176638569355532697974668787712 }, { argument := 4651482326362361046666278076416, coefficient := 4651482326362361046666278076416 }, { argument := 4622042564803105597003833278464, coefficient := 4622042564803105597003833278464 }, { argument := 2943976155925544966244479795200, coefficient := 2943976155925544966244479795200 }, { argument := 71332542258075954532103745437696, coefficient := 71332542258075954532103745437696 }, { argument := 4563163041684594697678943682560, coefficient := 4563163041684594697678943682560 }, { argument := 2649578540332990469620031815680, coefficient := 2649578540332990469620031815680 }, { argument := 4651482326362361046666278076416, coefficient := 4651482326362361046666278076416 }, { argument := 176638569355532697974668787712, coefficient := 176638569355532697974668787712 }, { argument := 4563163041684594697678943682560, coefficient := 4563163041684594697678943682560 }, { argument := 176638569355532697974668787712, coefficient := 176638569355532697974668787712 }, { argument := 4651482326362361046666278076416, coefficient := 4651482326362361046666278076416 }, { argument := 4651482326362361046666278076416, coefficient := 4651482326362361046666278076416 }, { argument := 176638569355532697974668787712, coefficient := 176638569355532697974668787712 }, { argument := 120585263346710321817373892411392, coefficient := (-120585263346710321817373892411392) }, { argument := 92613389189037511815890731008, coefficient := 92613389189037511815890731008 }, { argument := 105476359909737166234764443648, coefficient := 105476359909737166234764443648 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 1103642887836030349139364544512, coefficient := 1103642887836030349139364544512 }, { argument := 97758577477317373583440216064, coefficient := 97758577477317373583440216064 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 97758577477317373583440216064, coefficient := 97758577477317373583440216064 }, { argument := 95185983333177442699665473536, coefficient := 95185983333177442699665473536 }, { argument := 3596486613507623375517090054144, coefficient := 3596486613507623375517090054144 }, { argument := 95185983333177442699665473536, coefficient := 95185983333177442699665473536 }, { argument := 1103642887836030349139364544512, coefficient := 1103642887836030349139364544512 }, { argument := 3596486613507623375517090054144, coefficient := 3596486613507623375517090054144 }, { argument := 92613389189037511815890731008, coefficient := 92613389189037511815890731008 }, { argument := 95185983333177442699665473536, coefficient := 95185983333177442699665473536 }, { argument := 95185983333177442699665473536, coefficient := 95185983333177442699665473536 }, { argument := 105476359909737166234764443648, coefficient := 105476359909737166234764443648 }, { argument := 10537345614397156899941345394688, coefficient := (-10537345614397156899941345394688) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 5149830572871914909319647199232, coefficient := 5149830572871914909319647199232 }, { argument := 5149830553982448977841066344448, coefficient := 5149830553982448977841066344448 }, { argument := 10299661126854363887160713543680, coefficient := (-10299661126854363887160713543680) }, { argument := 55631475073959427726748374007808, coefficient := 55631475073959427726748374007808 }, { argument := 202958538655743192481783435231232, coefficient := 202958538655743192481783435231232 }, { argument := 55628878801869742687463497793536, coefficient := 55628878801869742687463497793536 }, { argument := 314218892531572362895995307032576, coefficient := (-314218892531572362895995307032576) }, { argument := 36646159236921476302974469799936, coefficient := 36646159236921476302974469799936 }, { argument := 1434620698959866397995109101600768, coefficient := 1434620698959866397995109101600768 }, { argument := 1434620754003770122323693712441344, coefficient := 1434620754003770122323693712441344 }, { argument := 36646343579219501602445031636992, coefficient := 36646343579219501602445031636992 }, { argument := 2942533955779777498224222315479040, coefficient := (-2942533955779777498224222315479040) }, { argument := 1239769181829389071797616377856, coefficient := 1239769181829389071797616377856 }, { argument := 231051129817791632307328169017344, coefficient := 231051129817791632307328169017344 }, { argument := 2357366492163758656880738968797184, coefficient := 2357366492163758656880738968797184 }, { argument := 231051532087858109075186052497408, coefficient := 231051532087858109075186052497408 }, { argument := 1239769181829389071797616377856, coefficient := 1239769181829389071797616377856 }, { argument := 2821948692433067176406848423067648, coefficient := (-2821948692433067176406848423067648) }] }

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

end TermShard13


end Parent2

namespace Parent2

namespace TermShard14

/-! Directed signed-log shard 14.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6284043746225098779557610085416960)
def positiveArguments : Array ℕ := #[
    145952025, 27024749287, 27024751049, 145950263, 11728959, 530127609,
    1473945
  ]
def positiveCoefficients : Array ℕ := #[
    689238950966952529970488934400, 127620770240884142202773938634752, 127620778561693885019088805167104, 689230630157209713655622402048, 110776885721104542111973244928, 5006913704770848951629909065728,
    111368135449492787432018411520
  ]
def positiveScales : Array ℕ := #[
    27, 34, 34, 27, 23, 28,
    20
  ]
def negativeArguments : Array ℕ := #[
    3239, 33
  ]
def negativeCoefficients : Array ℕ := #[
    256620018383702189465488855138304, 5229058725941446281173900722176
  ]
def negativeScales : Array ℕ := #[
    11, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    27120918986637886, 34653562182777351, 34653562276840335, 27120901569654419, 23483571637323599, 28981764436010457,
    20491251260848281
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11661332752823540, 5044394119358454
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 13590455477 / 125000000000
noncomputable def negativeCeiling : ℝ := 36338793563 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 689238950966952529970488934400, coefficient := 689238950966952529970488934400 }, { argument := 127620770240884142202773938634752, coefficient := 127620770240884142202773938634752 }, { argument := 127620778561693885019088805167104, coefficient := 127620778561693885019088805167104 }, { argument := 689230630157209713655622402048, coefficient := 689230630157209713655622402048 }, { argument := 256620018383702189465488855138304, coefficient := (-256620018383702189465488855138304) }, { argument := 110776885721104542111973244928, coefficient := 110776885721104542111973244928 }, { argument := 5006913704770848951629909065728, coefficient := 5006913704770848951629909065728 }, { argument := 111368135449492787432018411520, coefficient := 111368135449492787432018411520 }, { argument := 5229058725941446281173900722176, coefficient := (-5229058725941446281173900722176) }] }

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

end TermShard14


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
