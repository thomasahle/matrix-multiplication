import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-354036831979229134764658374213632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    68650503, 16026237327, 4393632945, 65961, 74817, 30537,
    811593, 71901, 30537, 71901, 70929, 2808405,
    8991, 811593, 2808405, 65961, 70929, 8991,
    74817, 7852883109, 458367184735, 125646145105, 15778967981, 15778975315,
    68650503, 16026237327, 4393632945, 15560864199, 15560871481, 93,
    68337, 38745, 31725, 421335, 74655, 31725,
    74655, 36855, 2927367, 74817, 421335, 2927367,
    68337, 36855, 74817, 38745, 1953233283, 456021704011,
    125006946805, 30727463963, 30727478245, 4001909403, 29198569921, 8003819785,
    959530703877, 959531148283, 945, 30727463963, 30727478245, 1905,
    148099819240929, 537878613432349, 74051646731521, 445224569609501
  ]
def negativeCoefficients : Array ℕ := #[
    5065513037489719177371451392, 18476993652231253466548273152, 5065513905639612146327224320, 311492015576564667940601856, 353313293148858245953093632, 288413810574780711781269504,
    3832639580931623967919177728, 339542872484810360509956096, 288413810574780711781269504, 339542872484810360509956096, 334952732263461065362243584, 13262317642323525966369914880,
    339670376379847840930725888, 3832639580931623967919177728, 13262317642323525966369914880, 311492015576564667940601856, 334952732263461065362243584, 339670376379847840930725888,
    353313293148858245953093632, 144860124952479588857250054144, 528461384287080781394068111360, 144860142662506821123026452480, 36383823011595564855341350912, 36383839922648194428572794880,
    5065513037489719177371451392, 18476993652231253466548273152, 5065513905639612146327224320, 35880909930587797358219624448, 35880926721736590452338982912, 3597763239173136423925579776,
    322712358339862944968343552, 365936178757568807609303040, 299634153338078988809011200, 3979396564119763932225208320, 352548269778633363428474880, 299634153338078988809011200,
    352548269778633363428474880, 348085633452321548701532160, 13824099803858664700281618432, 353313293148858245953093632, 3979396564119763932225208320, 13824099803858664700281618432,
    322712358339862944968343552, 348085633452321548701532160, 353313293148858245953093632, 365936178757568807609303040, 144123177951010005965510541312, 525757229121740344613442420736,
    144123197196728682367607111680, 35426353984974628938095525888, 35426370450999557733084037120, 147644397126625559405968490496, 538618546651000720705334542336, 147644415185988007567619522560,
    1106263582830337777034908925952, 1106264095195571953345346142208, 73115833570292772486229524480, 35426353984974628938095525888, 35426370450999557733084037120, 73696117963707794490088488960,
    83372786343385707270371278848, 302798740378060752612006821888, 83374742156562395912527151104, 125319575361846135087385542656
  ]
def negativeScales : Array ℕ := #[
    26, 33, 32, 16, 16, 14,
    19, 16, 14, 16, 16, 21,
    13, 19, 21, 16, 16, 13,
    16, 32, 38, 36, 33, 33,
    26, 33, 32, 33, 33, 6,
    16, 15, 14, 18, 16, 14,
    16, 15, 21, 16, 18, 21,
    16, 15, 16, 15, 30, 38,
    36, 34, 34, 31, 34, 32,
    39, 39, 9, 34, 34, 10,
    47, 48, 46, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26032766955202224, 33899716699555487, 32032767202457621, 16009325650430725, 16191078497644886, 14898270720387434,
    19630396896334709, 16133724215374083, 14898270720387434, 16133724215374083, 16114087987297101, 21421319570977777,
    13134265869234731, 19630396896334709, 21421319570977777, 16009325650430725, 16114087987297101, 13134265869234731,
    16191078497644886, 32870575279130441, 38737712806799783, 36870575455508641, 33877283801133686, 33877284471692340,
    26032766955202224, 33899716699555487, 32032767202457621, 33857203135926194, 33857203811062427, 6539158811108986,
    16060379294274153, 15241722523726519, 14953332554642086, 18684608239020224, 16187951267285539, 14953332554642086,
    16187951267285539, 15169572737970684, 21481172195115125, 16191078497644886, 18684608239020224, 21481172195115125,
    16060379294274153, 15169572737970684, 16191078497644886, 15241722523726519, 30863217122961416, 38730311533918902,
    36863217315613997, 34838809651826033, 34838810322384670, 31898041365446128, 34765178660126585, 32898041541911700,
    39803538016193605, 39803538684376698, 9884170522387776, 34838809651826033, 34838810322384670, 10895575286414346,
    47073563208210033, 48934273963530729, 46073597051493906, 48661526538102940
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 165919909 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5065513037489719177371451392, coefficient := (-5065513037489719177371451392) }, { argument := 18476993652231253466548273152, coefficient := (-18476993652231253466548273152) }, { argument := 5065513905639612146327224320, coefficient := (-5065513905639612146327224320) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 339670376379847840930725888, coefficient := (-339670376379847840930725888) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 339670376379847840930725888, coefficient := (-339670376379847840930725888) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 144860124952479588857250054144, coefficient := (-144860124952479588857250054144) }, { argument := 528461384287080781394068111360, coefficient := (-528461384287080781394068111360) }, { argument := 144860142662506821123026452480, coefficient := (-144860142662506821123026452480) }, { argument := 36383823011595564855341350912, coefficient := (-36383823011595564855341350912) }, { argument := 36383839922648194428572794880, coefficient := (-36383839922648194428572794880) }, { argument := 5065513037489719177371451392, coefficient := (-5065513037489719177371451392) }, { argument := 18476993652231253466548273152, coefficient := (-18476993652231253466548273152) }, { argument := 5065513905639612146327224320, coefficient := (-5065513905639612146327224320) }, { argument := 35880909930587797358219624448, coefficient := (-35880909930587797358219624448) }, { argument := 35880926721736590452338982912, coefficient := (-35880926721736590452338982912) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 365936178757568807609303040, coefficient := (-365936178757568807609303040) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 365936178757568807609303040, coefficient := (-365936178757568807609303040) }, { argument := 144123177951010005965510541312, coefficient := (-144123177951010005965510541312) }, { argument := 525757229121740344613442420736, coefficient := (-525757229121740344613442420736) }, { argument := 144123197196728682367607111680, coefficient := (-144123197196728682367607111680) }, { argument := 35426353984974628938095525888, coefficient := (-35426353984974628938095525888) }, { argument := 35426370450999557733084037120, coefficient := (-35426370450999557733084037120) }, { argument := 147644397126625559405968490496, coefficient := (-147644397126625559405968490496) }, { argument := 538618546651000720705334542336, coefficient := (-538618546651000720705334542336) }, { argument := 147644415185988007567619522560, coefficient := (-147644415185988007567619522560) }, { argument := 1106263582830337777034908925952, coefficient := (-1106263582830337777034908925952) }, { argument := 1106264095195571953345346142208, coefficient := (-1106264095195571953345346142208) }, { argument := 73115833570292772486229524480, coefficient := (-73115833570292772486229524480) }, { argument := 35426353984974628938095525888, coefficient := (-35426353984974628938095525888) }, { argument := 35426370450999557733084037120, coefficient := (-35426370450999557733084037120) }, { argument := 73696117963707794490088488960, coefficient := (-73696117963707794490088488960) }, { argument := 83372786343385707270371278848, coefficient := (-83372786343385707270371278848) }, { argument := 302798740378060752612006821888, coefficient := (-302798740378060752612006821888) }, { argument := 83374742156562395912527151104, coefficient := (-83374742156562395912527151104) }, { argument := 125319575361846135087385542656, coefficient := (-125319575361846135087385542656) }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 538062162434925267370715213417414656
def positiveArguments : Array ℕ := #[
    70799, 837, 945, 405, 10665, 945,
    405, 945, 945, 39177, 243, 10665,
    39177, 837, 945, 243, 945, 453,
    13137, 11627, 755, 453, 755, 23103,
    755, 453, 370101, 23707, 13137, 23103,
    755, 23707, 755, 23103, 755, 453,
    4935, 3675, 3885, 315, 67515, 122115,
    3675, 67515, 1995, 1995, 3885, 3885,
    122115, 3885, 4935, 315, 93, 285,
    843
  ]
def positiveCoefficients : Array ℕ := #[
    5609274677847400837285318139838464, 32379869152558227815330217984, 36557916785146386243114762240, 31335357244411188208384081920, 412582203718080644743723745280, 36557916785146386243114762240,
    31335357244411188208384081920, 36557916785146386243114762240, 36557916785146386243114762240, 1515586778721354469678843428864, 37602428693293425850060898304, 412582203718080644743723745280,
    1515586778721354469678843428864, 32379869152558227815330217984, 36557916785146386243114762240, 37602428693293425850060898304, 36557916785146386243114762240, 35049177362267329033081454592,
    508213071752876270979681091584, 899595552298194778515757334528, 29207647801889440860901212160, 560786837796277264529303273472, 29207647801889440860901212160, 893754022737816890343577092096,
    934644729660462107548838789120, 560786837796277264529303273472, 14317588952486203910013774200832, 917120140979328443032298061824, 508213071752876270979681091584, 893754022737816890343577092096,
    29207647801889440860901212160, 917120140979328443032298061824, 29207647801889440860901212160, 893754022737816890343577092096, 934644729660462107548838789120, 35049177362267329033081454592,
    95456782716771119634799656960, 71084838193340195472723148800, 75146828947245349499735900160, 97487778093723696648306032640, 1305930027380507019684599562240, 2362047623395847066707914915840,
    71084838193340195472723148800, 1305930027380507019684599562240, 77177824324197926513242275840, 77177824324197926513242275840, 75146828947245349499735900160, 75146828947245349499735900160,
    2362047623395847066707914915840, 75146828947245349499735900160, 95456782716771119634799656960, 97487778093723696648306032640, 3597763239173136423925579776, 88203227799083344586562600960,
    65223965819848473233747607552
  ]
def positiveScales : Array ℕ := #[
    16, 9, 9, 8, 13, 9,
    8, 9, 9, 15, 7, 13,
    15, 9, 9, 7, 9, 8,
    13, 13, 9, 8, 9, 14,
    9, 8, 18, 14, 13, 14,
    9, 14, 9, 14, 9, 8,
    12, 11, 11, 8, 16, 16,
    11, 16, 10, 10, 11, 11,
    16, 11, 12, 8, 6, 8,
    9
  ]
def negativeArguments : Array ℕ := #[
    445224642863843, 497217, 40256920387, 40256939197, 4533, 93,
    27, 151, 105
  ]
def negativeCoefficients : Array ℕ := #[
    125319595981110343491815211008, 18784327164103971073746272256, 46413069223418092447923699712, 46413090909871594102715318272, 87680971845009824783089532928, 3597763239173136423925579776,
    4278320775770274230051373318144, 23926905079307829953250273001472, 8318957063997755447322114785280
  ]
def negativeScales : Array ℕ := #[
    48, 18, 35, 35, 12, 6,
    4, 7, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    16111441362665214, 9709083812544787, 9884170518905654, 8661778097770205, 13380596345227933, 9884170518905654,
    8661778097770205, 9884170518905654, 9884170518905654, 15257719306230212, 7924812503187618, 13380596345227933,
    15257719306230212, 9709083812544787, 9884170518905654, 7924812503187618, 9884170518905654, 8823367239982289,
    13681348235170925, 13505191280019959, 9560332834212327, 8823367239982289, 9560332834212327, 14495792582017715,
    9560332834212327, 8823367239982289, 18497559508191902, 14533025488216656, 13681348235170925, 14495792582017715,
    9560332834212327, 14533025488216656, 9560332834212327, 14495792582017715, 9560332834212327, 8823367239982289,
    12268834369343759, 11843528534516384, 11923698882884927, 8299208018387278, 16042920444994069, 16897880898879436,
    11843528534516384, 16042920444994069, 10962173030320774, 10962173030320774, 11923698882884927, 11923698882884927,
    16897880898879436, 11923698882884927, 12268834369343759, 8299208018387278, 6539158811107971, 8154818109052103,
    9719388820935039
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    48661526775474538, 18923516104469719, 35228517760667430, 35228518434764880, 12146250445885986, 6539158811108986,
    4754887502413606, 7238404739325080, 6714245517766967
  ]

abbrev PositiveTerm := Fin 55
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 218965413427 / 200000000000
noncomputable def negativeCeiling : ℝ := 3132084921 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 125319595981110343491815211008, coefficient := (-125319595981110343491815211008) }, { argument := 18784327164103971073746272256, coefficient := (-18784327164103971073746272256) }, { argument := 46413069223418092447923699712, coefficient := (-46413069223418092447923699712) }, { argument := 46413090909871594102715318272, coefficient := (-46413090909871594102715318272) }, { argument := 87680971845009824783089532928, coefficient := (-87680971845009824783089532928) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 5609274677847400837285318139838464, coefficient := 5609274677847400837285318139838464 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 412582203718080644743723745280, coefficient := 412582203718080644743723745280 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 1515586778721354469678843428864, coefficient := 1515586778721354469678843428864 }, { argument := 37602428693293425850060898304, coefficient := 37602428693293425850060898304 }, { argument := 412582203718080644743723745280, coefficient := 412582203718080644743723745280 }, { argument := 1515586778721354469678843428864, coefficient := 1515586778721354469678843428864 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 37602428693293425850060898304, coefficient := 37602428693293425850060898304 }, { argument := 36557916785146386243114762240, coefficient := 36557916785146386243114762240 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 35049177362267329033081454592, coefficient := 35049177362267329033081454592 }, { argument := 508213071752876270979681091584, coefficient := 508213071752876270979681091584 }, { argument := 899595552298194778515757334528, coefficient := 899595552298194778515757334528 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 560786837796277264529303273472, coefficient := 560786837796277264529303273472 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 893754022737816890343577092096, coefficient := 893754022737816890343577092096 }, { argument := 934644729660462107548838789120, coefficient := 934644729660462107548838789120 }, { argument := 560786837796277264529303273472, coefficient := 560786837796277264529303273472 }, { argument := 14317588952486203910013774200832, coefficient := 14317588952486203910013774200832 }, { argument := 917120140979328443032298061824, coefficient := 917120140979328443032298061824 }, { argument := 508213071752876270979681091584, coefficient := 508213071752876270979681091584 }, { argument := 893754022737816890343577092096, coefficient := 893754022737816890343577092096 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 917120140979328443032298061824, coefficient := 917120140979328443032298061824 }, { argument := 29207647801889440860901212160, coefficient := 29207647801889440860901212160 }, { argument := 893754022737816890343577092096, coefficient := 893754022737816890343577092096 }, { argument := 934644729660462107548838789120, coefficient := 934644729660462107548838789120 }, { argument := 35049177362267329033081454592, coefficient := 35049177362267329033081454592 }, { argument := 23926905079307829953250273001472, coefficient := (-23926905079307829953250273001472) }, { argument := 95456782716771119634799656960, coefficient := 95456782716771119634799656960 }, { argument := 71084838193340195472723148800, coefficient := 71084838193340195472723148800 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 97487778093723696648306032640, coefficient := 97487778093723696648306032640 }, { argument := 1305930027380507019684599562240, coefficient := 1305930027380507019684599562240 }, { argument := 2362047623395847066707914915840, coefficient := 2362047623395847066707914915840 }, { argument := 71084838193340195472723148800, coefficient := 71084838193340195472723148800 }, { argument := 1305930027380507019684599562240, coefficient := 1305930027380507019684599562240 }, { argument := 77177824324197926513242275840, coefficient := 77177824324197926513242275840 }, { argument := 77177824324197926513242275840, coefficient := 77177824324197926513242275840 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 2362047623395847066707914915840, coefficient := 2362047623395847066707914915840 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 95456782716771119634799656960, coefficient := 95456782716771119634799656960 }, { argument := 97487778093723696648306032640, coefficient := 97487778093723696648306032640 }, { argument := 8318957063997755447322114785280, coefficient := (-8318957063997755447322114785280) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
