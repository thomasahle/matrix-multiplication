import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-327014321321294214317967394471936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    702459, 596511, 702459, 2770659, 27384723, 2808405,
    31716603, 27384723, 1290249, 2770659, 2808405, 2927367,
    1953233283, 456021704011, 125006946805, 65961, 74817, 30537,
    811593, 71901, 30537, 71901, 70929, 2808405,
    8991, 811593, 2808405, 65961, 70929, 8991,
    74817, 7980776289, 58229263093, 15961554505, 40256920387, 40256939197,
    743013, 421335, 344385, 4575285, 810675, 344385,
    810675, 400005, 31716603, 811593, 4575285, 31716603,
    743013, 400005, 811593, 421335, 1230528093, 4488905375,
    307632065, 1290249, 2927367, 596511, 31716603, 702459,
    596511, 702459, 2770659, 27384723
  ]
def negativeCoefficients : Array ℕ := #[
    13269075348760512428670713856, 11267774212252219744268058624, 13269075348760512428670713856, 13084067197061128338133745664, 517282792151477917141363064832, 13262317642323525966369914880,
    149777422957682837993646194688, 517282792151477917141363064832, 12186057264312153734652100608, 13084067197061128338133745664, 13262317642323525966369914880, 13824099803858664700281618432,
    144123177951010005965510541312, 525757229121740344613442420736, 144123197196728682367607111680, 311492015576564667940601856, 353313293148858245953093632, 288413810574780711781269504,
    3832639580931623967919177728, 339542872484810360509956096, 288413810574780711781269504, 339542872484810360509956096, 334952732263461065362243584, 13262317642323525966369914880,
    339670376379847840930725888, 3832639580931623967919177728, 13262317642323525966369914880, 311492015576564667940601856, 334952732263461065362243584, 339670376379847840930725888,
    353313293148858245953093632, 147219337712712457809794433024, 537070156938636032757563654144, 147219355486150372828947415040, 46413069223418092447923699712, 46413090909871594102715318272,
    3508779687536423699163906048, 3979396564119763932225208320, 3252624362406125533837393920, 43212345067152489403090206720, 3828304448500349633613004800, 3252624362406125533837393920,
    3828304448500349633613004800, 3777940409960544867408936960, 149777422957682837993646194688, 3832639580931623967919177728, 43212345067152489403090206720, 149777422957682837993646194688,
    3508779687536423699163906048, 3777940409960544867408936960, 3832639580931623967919177728, 3979396564119763932225208320, 90796947228323463943686193152, 331222754494896809751609344000,
    90796959550748505181666672640, 12186057264312153734652100608, 13824099803858664700281618432, 11267774212252219744268058624, 149777422957682837993646194688, 13269075348760512428670713856,
    11267774212252219744268058624, 13269075348760512428670713856, 13084067197061128338133745664, 517282792151477917141363064832
  ]
def negativeScales : Array ℕ := #[
    19, 19, 19, 21, 24, 21,
    24, 24, 20, 21, 21, 21,
    30, 38, 36, 16, 16, 14,
    19, 16, 14, 16, 16, 21,
    13, 19, 21, 16, 16, 13,
    16, 32, 35, 33, 35, 35,
    19, 18, 18, 22, 19, 18,
    19, 18, 24, 19, 22, 24,
    19, 18, 19, 18, 30, 32,
    28, 20, 21, 19, 24, 19,
    19, 19, 21, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19422054497317946, 19186189216714610, 19422054497317946, 21401797730781646, 24706867951690659, 21421319570977777,
    24918734930070916, 24706867951690659, 20299218081794152, 21401797730781646, 21421319570977777, 21481172195115125,
    30863217122961416, 38730311533918902, 36863217315613997, 16009325650430725, 16191078497644886, 14898270720387434,
    19630396896334709, 16133724215374083, 14898270720387434, 16133724215374083, 16114087987297101, 21421319570977777,
    13134265869234731, 19630396896334709, 21421319570977777, 16009325650430725, 16114087987297101, 13134265869234731,
    16191078497644886, 32893881941917614, 35761025310353375, 33893882116090732, 35228517760667430, 35228518434764880,
    19503027927289084, 18684608239020224, 18393662780653309, 22125430182727480, 19628764127656122, 18393662780653309,
    19628764127656122, 18609658508019485, 24918734930070916, 19630396896334709, 22125430182727480, 24918734930070916,
    19503027927289084, 18609658508019485, 19630396896334709, 18684608239020224, 30196630448937258, 32063716538910451,
    28196630644731289, 20299218081794152, 21481172195115125, 19186189216714610, 24918734930070916, 19422054497317946,
    19186189216714610, 19422054497317946, 21401797730781646, 24706867951690659
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
noncomputable def negativeCeiling : ℝ := 419309347 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 517282792151477917141363064832, coefficient := (-517282792151477917141363064832) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 517282792151477917141363064832, coefficient := (-517282792151477917141363064832) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 144123177951010005965510541312, coefficient := (-144123177951010005965510541312) }, { argument := 525757229121740344613442420736, coefficient := (-525757229121740344613442420736) }, { argument := 144123197196728682367607111680, coefficient := (-144123197196728682367607111680) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 339670376379847840930725888, coefficient := (-339670376379847840930725888) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 339670376379847840930725888, coefficient := (-339670376379847840930725888) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 147219337712712457809794433024, coefficient := (-147219337712712457809794433024) }, { argument := 537070156938636032757563654144, coefficient := (-537070156938636032757563654144) }, { argument := 147219355486150372828947415040, coefficient := (-147219355486150372828947415040) }, { argument := 46413069223418092447923699712, coefficient := (-46413069223418092447923699712) }, { argument := 46413090909871594102715318272, coefficient := (-46413090909871594102715318272) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 43212345067152489403090206720, coefficient := (-43212345067152489403090206720) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 43212345067152489403090206720, coefficient := (-43212345067152489403090206720) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 90796947228323463943686193152, coefficient := (-90796947228323463943686193152) }, { argument := 331222754494896809751609344000, coefficient := (-331222754494896809751609344000) }, { argument := 90796959550748505181666672640, coefficient := (-90796959550748505181666672640) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 517282792151477917141363064832, coefficient := (-517282792151477917141363064832) }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9013463145849862244101322413441024)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2808405, 31716603, 27384723, 1290249, 2770659, 2808405,
    2927367, 122669273973, 7160111687041, 1962708624175, 134779733253, 134779796219,
    7852883109, 458367184735, 125646145105, 959530703877, 959531148283, 4533,
    1790595888375449, 68337, 8766704517440969, 743013, 32913, 70133643825110581,
    32913, 64989, 1290249, 65961, 743013, 1290249,
    895303735445109, 64989, 65961, 68337, 55587672536903187, 203191514157129569,
    13896173307141283, 53245200055202531, 53245198921567517, 1953233283, 456021704011, 125006946805,
    134779733253, 134779796219, 158477985, 31163671527, 31163685913, 3783,
    64989, 36855, 30105, 400005, 70875, 30105,
    70875, 34965, 2770659, 70929, 400005, 2770659,
    64989, 34965, 70929, 36855
  ]
def negativeCoefficients : Array ℕ := #[
    13262317642323525966369914880, 149777422957682837993646194688, 517282792151477917141363064832, 12186057264312153734652100608, 13084067197061128338133745664, 13262317642323525966369914880,
    13824099803858664700281618432, 2262848702687691093610088890368, 8255046739376379154767089238016, 2262848980088675552549719244800, 621561811410232984250678771712, 621562101789654820549585534976,
    144860124952479588857250054144, 528461384287080781394068111360, 144860142662506821123026452480, 1106263582830337777034908925952, 1106264095195571953345346142208, 87680971845009824783089532928,
    504007935978675897913567084544, 322712358339862944968343552, 19740863599007195969906186125312, 3508779687536423699163906048, 310854496101377265836752896, 19740865762306443770498841051136,
    310854496101377265836752896, 306901875355215372792889344, 12186057264312153734652100608, 311492015576564667940601856, 3508779687536423699163906048, 12186057264312153734652100608,
    504011196166750753017726763008, 306901875355215372792889344, 311492015576564667940601856, 322712358339862944968343552, 15646538832724396689533983260672, 57193326715180974348014414987264,
    15645700231979328795176014446592, 14987191445492351978794265870336, 14987191126402462814760077361152, 144123177951010005965510541312, 525757229121740344613442420736, 144123197196728682367607111680,
    621561811410232984250678771712, 621562101789654820549585534976, 748391124636718391131436482560, 35929267065982396435217252352, 35929283651911161709317849088, 73173862009634274686615420928,
    306901875355215372792889344, 348085633452321548701532160, 284333685933581338316636160, 3777940409960544867408936960, 334697724473386104520704000, 284333685933581338316636160,
    334697724473386104520704000, 330235088147074289793761280, 13084067197061128338133745664, 334952732263461065362243584, 3777940409960544867408936960, 13084067197061128338133745664,
    306901875355215372792889344, 330235088147074289793761280, 334952732263461065362243584, 348085633452321548701532160
  ]
def negativeScales : Array ℕ := #[
    21, 24, 24, 20, 21, 21,
    21, 36, 42, 40, 36, 36,
    32, 38, 36, 39, 39, 12,
    50, 16, 52, 19, 15, 55,
    15, 15, 20, 16, 19, 20,
    49, 15, 16, 16, 55, 57,
    53, 55, 55, 30, 38, 36,
    36, 36, 27, 34, 34, 11,
    15, 15, 14, 18, 16, 14,
    16, 15, 21, 16, 18, 21,
    15, 15, 16, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21421319570977777, 24918734930070916, 24706867951690659, 20299218081794152, 21401797730781646, 21421319570977777,
    21481172195115125, 36835982975111313, 42703119230277704, 40835983151970247, 36971812634404736, 36971813308398777,
    32870575279130441, 38737712806799783, 36870575455508641, 39803538016193605, 39803538684376698, 12146250445885986,
    50669361201975334, 16060379294274153, 52960956058457992, 19503027927289084, 15006369912783681, 55960956216555512,
    15006369912783681, 15987907948136922, 20299218081794152, 16009325650430725, 19503027927289084, 20299218081794152,
    49669370534054501, 15987907948136922, 16009325650430725, 16060379294274153, 55625614495730546, 57495617765495358,
    53625537170158902, 55563500993422261, 55563500962706072, 30863217122961416, 38730311533918902, 36863217315613997,
    36971812634404736, 36971813308398777, 27239707201121241, 34859146164492748, 34859146830479966, 11885315064398008,
    15987907948136922, 15169572737970684, 14877715499884064, 18609658508019485, 16112989209604316, 14877715499884064,
    16112989209604316, 15093623884737385, 21401797730781646, 16114087987297101, 18609658508019485, 21401797730781646,
    15987907948136922, 15093623884737385, 16114087987297101, 15169572737970684
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
noncomputable def negativeCeiling : ℝ := 58242008489 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 517282792151477917141363064832, coefficient := (-517282792151477917141363064832) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 13262317642323525966369914880, coefficient := (-13262317642323525966369914880) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 2262848702687691093610088890368, coefficient := (-2262848702687691093610088890368) }, { argument := 8255046739376379154767089238016, coefficient := (-8255046739376379154767089238016) }, { argument := 2262848980088675552549719244800, coefficient := (-2262848980088675552549719244800) }, { argument := 621561811410232984250678771712, coefficient := (-621561811410232984250678771712) }, { argument := 621562101789654820549585534976, coefficient := (-621562101789654820549585534976) }, { argument := 144860124952479588857250054144, coefficient := (-144860124952479588857250054144) }, { argument := 528461384287080781394068111360, coefficient := (-528461384287080781394068111360) }, { argument := 144860142662506821123026452480, coefficient := (-144860142662506821123026452480) }, { argument := 1106263582830337777034908925952, coefficient := (-1106263582830337777034908925952) }, { argument := 1106264095195571953345346142208, coefficient := (-1106264095195571953345346142208) }, { argument := 87680971845009824783089532928, coefficient := (-87680971845009824783089532928) }, { argument := 504007935978675897913567084544, coefficient := (-504007935978675897913567084544) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 19740863599007195969906186125312, coefficient := (-19740863599007195969906186125312) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 19740865762306443770498841051136, coefficient := (-19740865762306443770498841051136) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 504011196166750753017726763008, coefficient := (-504011196166750753017726763008) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 15646538832724396689533983260672, coefficient := (-15646538832724396689533983260672) }, { argument := 57193326715180974348014414987264, coefficient := (-57193326715180974348014414987264) }, { argument := 15645700231979328795176014446592, coefficient := (-15645700231979328795176014446592) }, { argument := 14987191445492351978794265870336, coefficient := (-14987191445492351978794265870336) }, { argument := 14987191126402462814760077361152, coefficient := (-14987191126402462814760077361152) }, { argument := 144123177951010005965510541312, coefficient := (-144123177951010005965510541312) }, { argument := 525757229121740344613442420736, coefficient := (-525757229121740344613442420736) }, { argument := 144123197196728682367607111680, coefficient := (-144123197196728682367607111680) }, { argument := 621561811410232984250678771712, coefficient := (-621561811410232984250678771712) }, { argument := 621562101789654820549585534976, coefficient := (-621562101789654820549585534976) }, { argument := 748391124636718391131436482560, coefficient := (-748391124636718391131436482560) }, { argument := 35929267065982396435217252352, coefficient := (-35929267065982396435217252352) }, { argument := 35929283651911161709317849088, coefficient := (-35929283651911161709317849088) }, { argument := 73173862009634274686615420928, coefficient := (-73173862009634274686615420928) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 330235088147074289793761280, coefficient := (-330235088147074289793761280) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 330235088147074289793761280, coefficient := (-330235088147074289793761280) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
