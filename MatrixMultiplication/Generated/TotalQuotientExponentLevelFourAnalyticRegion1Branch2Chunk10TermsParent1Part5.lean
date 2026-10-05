import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-289395693687493468268074362732544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7511, 7059797803, 3857, 3857, 130529, 7105,
    236089, 130529, 210714837, 7511, 7105, 9541,
    32198893005, 232937984067, 64397784099, 3900703495, 3900701945, 13395,
    56259, 243789, 8037, 8037, 18753, 243789,
    243789, 8037, 3008517, 120555, 56259, 243789,
    18753, 120555, 18753, 243789, 243789, 8037,
    399636027, 124033, 13585499333, 3069157, 97643, 108683968099,
    50141, 50141, 1696877, 92365, 3069157, 1696877,
    3197114781, 97643, 92365, 124033, 74144687085, 268389564317,
    37072342587, 479753409, 124033, 15371600191, 3069157, 97643,
    122972771513, 50141, 50141, 1696877
  ]
def negativeCoefficients : Array ℕ := #[
    70939389305667810400141312, 32557570821019490639687974912, 72856670097712886356901888, 72856670097712886356901888, 1232811549284983840197050368, 67104827721577658486620160,
    2229797561148423337712549888, 1232811549284983840197050368, 971750667668106038527131648, 70939389305667810400141312, 67104827721577658486620160, 90112197226118569967747072,
    74245592339998960741263605760, 268559211070611387994595131392, 74245590136765965437579034624, 8994409884961173200426762240, 8994406310904508919201136640, 63256099038038897637457920,
    1062702463839053480309293056, 2302522004984615874003468288, 75907318845646677164949504, 1214517101530346834639192064, 88558538653254456692441088, 2302522004984615874003468288,
    2302522004984615874003468288, 1214517101530346834639192064, 28414639687887072818746097664, 2277219565369400314948485120, 1062702463839053480309293056, 2302522004984615874003468288,
    88558538653254456692441088, 2277219565369400314948485120, 88558538653254456692441088, 2302522004984615874003468288, 2302522004984615874003468288, 75907318845646677164949504,
    29487934050812321439078678528, 2342917127879082819161423872, 1002432917237611265259588288512, 57974736589859006780526297088, 1844424121947363070403674112, 1002432672218733106212468948992,
    1894273422540535045279449088, 1894273422540535045279449088, 32053100281409579845123309568, 1744725520761019120652124160, 57974736589859006780526297088, 32053100281409579845123309568,
    29488179069690480486198018048, 1844424121947363070403674112, 1744725520761019120652124160, 2342917127879082819161423872, 85483004192642054983998504960, 309432100313131768263728955392,
    85483001989409059680313933824, 17699776708625409327274917888, 2342917127879082819161423872, 567111949453523723398059917312, 57974736589859006780526297088, 1844424121947363070403674112,
    567111811033767880300011978752, 1894273422540535045279449088, 1894273422540535045279449088, 32053100281409579845123309568
  ]
def negativeScales : Array ℕ := #[
    12, 32, 11, 11, 16, 12,
    17, 16, 27, 12, 12, 13,
    34, 37, 35, 31, 31, 13,
    15, 17, 12, 12, 14, 17,
    17, 12, 21, 16, 15, 17,
    14, 16, 14, 17, 17, 12,
    28, 16, 33, 21, 16, 36,
    15, 15, 20, 16, 21, 20,
    31, 16, 16, 16, 36, 37,
    35, 28, 16, 33, 21, 16,
    36, 15, 15, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12874789285573854, 32716979718498528, 11913263436158230, 11913263436158230, 16994010866026276, 12794618934708820,
    17848971300356817, 16994010866026276, 27650716660901363, 12874789285573854, 12794618934708820, 13219924768862814,
    34906292043229452, 37761154956060379, 35906292000417568, 31861087194770295, 31861086621494769, 13709406960819918,
    15779796289046625, 17895273510052851, 12972441381715804, 12972441381715804, 14194833787899984, 17895273510052851,
    17895273510052851, 12972441381715804, 21520621078243513, 16879331965172975, 15779796289046625, 17895273510052851,
    14194833787899984, 16879331965172975, 14194833787899984, 17895273510052851, 17895273510052851, 12972441381715804,
    28574111406374497, 16920364493267946, 33661348541477250, 21549411016800793, 16575229000958025, 36661348188847605,
    15613703148778080, 15613703148778080, 20694450562717709, 16495058652271465, 21549411016800793, 20694450562717709,
    31574123393855590, 16575229000958025, 16495058652271465, 16920364493267946, 36109624267437071, 37965537634180512,
    35109624230253149, 28837717818330426, 16920364493267946, 33839548308387134, 21549411016800793, 16575229000958025,
    36839547956256439, 15613703148778080, 15613703148778080, 20694450562717709
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
noncomputable def negativeCeiling : ℝ := 1865507429 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70939389305667810400141312, coefficient := (-70939389305667810400141312) }, { argument := 32557570821019490639687974912, coefficient := (-32557570821019490639687974912) }, { argument := 72856670097712886356901888, coefficient := (-72856670097712886356901888) }, { argument := 72856670097712886356901888, coefficient := (-72856670097712886356901888) }, { argument := 1232811549284983840197050368, coefficient := (-1232811549284983840197050368) }, { argument := 67104827721577658486620160, coefficient := (-67104827721577658486620160) }, { argument := 2229797561148423337712549888, coefficient := (-2229797561148423337712549888) }, { argument := 1232811549284983840197050368, coefficient := (-1232811549284983840197050368) }, { argument := 971750667668106038527131648, coefficient := (-971750667668106038527131648) }, { argument := 70939389305667810400141312, coefficient := (-70939389305667810400141312) }, { argument := 67104827721577658486620160, coefficient := (-67104827721577658486620160) }, { argument := 90112197226118569967747072, coefficient := (-90112197226118569967747072) }, { argument := 74245592339998960741263605760, coefficient := (-74245592339998960741263605760) }, { argument := 268559211070611387994595131392, coefficient := (-268559211070611387994595131392) }, { argument := 74245590136765965437579034624, coefficient := (-74245590136765965437579034624) }, { argument := 8994409884961173200426762240, coefficient := (-8994409884961173200426762240) }, { argument := 8994406310904508919201136640, coefficient := (-8994406310904508919201136640) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1062702463839053480309293056, coefficient := (-1062702463839053480309293056) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 75907318845646677164949504, coefficient := (-75907318845646677164949504) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 88558538653254456692441088, coefficient := (-88558538653254456692441088) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 28414639687887072818746097664, coefficient := (-28414639687887072818746097664) }, { argument := 2277219565369400314948485120, coefficient := (-2277219565369400314948485120) }, { argument := 1062702463839053480309293056, coefficient := (-1062702463839053480309293056) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 88558538653254456692441088, coefficient := (-88558538653254456692441088) }, { argument := 2277219565369400314948485120, coefficient := (-2277219565369400314948485120) }, { argument := 88558538653254456692441088, coefficient := (-88558538653254456692441088) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 75907318845646677164949504, coefficient := (-75907318845646677164949504) }, { argument := 29487934050812321439078678528, coefficient := (-29487934050812321439078678528) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 1002432917237611265259588288512, coefficient := (-1002432917237611265259588288512) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1002432672218733106212468948992, coefficient := (-1002432672218733106212468948992) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 29488179069690480486198018048, coefficient := (-29488179069690480486198018048) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 85483004192642054983998504960, coefficient := (-85483004192642054983998504960) }, { argument := 309432100313131768263728955392, coefficient := (-309432100313131768263728955392) }, { argument := 85483001989409059680313933824, coefficient := (-85483001989409059680313933824) }, { argument := 17699776708625409327274917888, coefficient := (-17699776708625409327274917888) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 567111949453523723398059917312, coefficient := (-567111949453523723398059917312) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 567111811033767880300011978752, coefficient := (-567111811033767880300011978752) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }] }

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

end TermShard10


end Parent1

namespace Parent1

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 318860003054659458196397003611570176
def positiveArguments : Array ℕ := #[
    42007, 341, 4081, 6105, 1771, 341,
    7073, 3553, 341, 4081, 341, 2205,
    1715, 245, 2303
  ]
def positiveCoefficients : Array ℕ := #[
    3328137422736702029292000721764352, 6595899271817416777196896256, 157876040635113653183228936192, 118087874059956977785299271680, 137024488098400529177896812544, 6595899271817416777196896256,
    136811717154148354443148525568, 137450029986904878647393386496, 6595899271817416777196896256, 157876040635113653183228936192, 6595899271817416777196896256, 85301805832008234567267778560,
    66345848980450849107874938880, 75823827406229541837571358720, 89092997202319711659146346496
  ]
def positiveScales : Array ℕ := #[
    15, 8, 11, 12, 10, 8,
    12, 11, 8, 11, 8, 11,
    10, 7, 11
  ]
def negativeArguments : Array ℕ := #[
    92365, 3069157, 1696877, 3838057287, 97643, 92365,
    124033, 959329330845, 1723993460947, 959329269693, 118413615545, 118413565511,
    32198893005, 232937984067, 64397784099, 83630244165, 83630210747, 489,
    44661534968269, 4089, 815877210646179, 101181, 3219, 50990661734595,
    1653, 1653, 55941, 3045, 101181, 55941,
    44714812002445, 3219, 3045, 4089, 56267748672401, 98115647982319,
    56267748107921, 28477430163, 28477429357, 67560782545, 244177736541, 33780390121,
    80702618795, 80702587733, 535, 471335005, 471334819, 489,
    11
  ]
def negativeCoefficients : Array ℕ := #[
    1744725520761019120652124160, 57974736589859006780526297088, 32053100281409579845123309568, 17699915128381252425322856448, 1844424121947363070403674112, 1744725520761019120652124160,
    2342917127879082819161423872, 1106031415531297094291391774720, 3975258269854761445414922092544, 1106031345027841244573485498368, 273043207600156248381419683840, 273043092229607125383456489472,
    74245592339998960741263605760, 268559211070611387994595131392, 74245590136765965437579034624, 192838213866699569867343790080, 192838136810037887964119302144, 18917271225329717325802242048,
    12571104515055665330954174464, 77239026193815917115211776, 459298037730776427051349966848, 1911255052412934289467899904, 60805190833429551771549696, 459283050374594102412171018240,
    62448574369468188305915904, 62448574369468188305915904, 1056695613672843291597471744, 57518423761352278702817280, 1911255052412934289467899904, 1056695613672843291597471744,
    12586100667009567754729553920, 60805190833429551771549696, 57518423761352278702817280, 77239026193815917115211776, 253407411954001864606556880896, 883747191384773212219740520448,
    253407409411809946948459298816, 131328966523449470122670948352, 131328962806430539270196297728, 77892279064197404263626833920, 281517763404343998690430550016, 77892276409019179154058248192,
    186087569373688415702053027840, 186087497749592863506291490816, 20696810031802451470969733120, 8694596210215611879475118080, 8694592779121214169498517504, 18917271225329717325802242048,
    871509787656907713528983453696
  ]
def negativeScales : Array ℕ := #[
    16, 21, 20, 31, 16, 16,
    16, 39, 40, 39, 36, 36,
    34, 37, 35, 36, 36, 8,
    45, 11, 49, 16, 11, 45,
    10, 10, 15, 11, 16, 15,
    45, 11, 11, 11, 45, 46,
    45, 34, 34, 35, 37, 34,
    36, 36, 9, 28, 28, 8,
    3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15358342136579123, 8413627929024171, 11994706993916780, 12575775579874587, 10790348496719072, 8413627929024171,
    12788106545933889, 11794821973295214, 8413627929024171, 11994706993916780, 8413627929024171, 11106562940444882,
    10743992861047947, 7936637938489789, 11169298695792845
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    16495058652271465, 21549411016800793, 20694450562717709, 31837729100773309, 16575229000958025, 16495058652271465,
    16920364493267946, 39803235211534042, 40648891441009514, 39803235119570116, 36785044020049722, 36785043410459184,
    34906292043229452, 37761154956060379, 35906292000417568, 36283305723908723, 36283305147418806, 8933690662845865,
    45344098069403988, 11997532370288072, 49535345371648264, 16626578877333553, 11652396861500322, 45535298294292279,
    10690871009350625, 10690871009350625, 15771618423534793, 11572226512796267, 16626578877333553, 15771618423534793,
    45345818043976860, 11652396861500322, 11572226512796267, 11997532370288072, 45677373474489930, 46479548476669317,
    45677373460016764, 34729099910685421, 34729099869852655, 35975467003524051, 37829140710246807, 34975466954345704,
    36231896438501327, 36231895883215728, 9063395081288510, 28812177591001775, 28812177021679887, 8933690662845865,
    3459431618637364
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 615434212163 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5460974383 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 17699915128381252425322856448, coefficient := (-17699915128381252425322856448) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 1106031415531297094291391774720, coefficient := (-1106031415531297094291391774720) }, { argument := 3975258269854761445414922092544, coefficient := (-3975258269854761445414922092544) }, { argument := 1106031345027841244573485498368, coefficient := (-1106031345027841244573485498368) }, { argument := 273043207600156248381419683840, coefficient := (-273043207600156248381419683840) }, { argument := 273043092229607125383456489472, coefficient := (-273043092229607125383456489472) }, { argument := 74245592339998960741263605760, coefficient := (-74245592339998960741263605760) }, { argument := 268559211070611387994595131392, coefficient := (-268559211070611387994595131392) }, { argument := 74245590136765965437579034624, coefficient := (-74245590136765965437579034624) }, { argument := 192838213866699569867343790080, coefficient := (-192838213866699569867343790080) }, { argument := 192838136810037887964119302144, coefficient := (-192838136810037887964119302144) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 12571104515055665330954174464, coefficient := (-12571104515055665330954174464) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 459298037730776427051349966848, coefficient := (-459298037730776427051349966848) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 459283050374594102412171018240, coefficient := (-459283050374594102412171018240) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 12586100667009567754729553920, coefficient := (-12586100667009567754729553920) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 253407411954001864606556880896, coefficient := (-253407411954001864606556880896) }, { argument := 883747191384773212219740520448, coefficient := (-883747191384773212219740520448) }, { argument := 253407409411809946948459298816, coefficient := (-253407409411809946948459298816) }, { argument := 131328966523449470122670948352, coefficient := (-131328966523449470122670948352) }, { argument := 131328962806430539270196297728, coefficient := (-131328962806430539270196297728) }, { argument := 77892279064197404263626833920, coefficient := (-77892279064197404263626833920) }, { argument := 281517763404343998690430550016, coefficient := (-281517763404343998690430550016) }, { argument := 77892276409019179154058248192, coefficient := (-77892276409019179154058248192) }, { argument := 186087569373688415702053027840, coefficient := (-186087569373688415702053027840) }, { argument := 186087497749592863506291490816, coefficient := (-186087497749592863506291490816) }, { argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 8694596210215611879475118080, coefficient := (-8694596210215611879475118080) }, { argument := 8694592779121214169498517504, coefficient := (-8694592779121214169498517504) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 3328137422736702029292000721764352, coefficient := 3328137422736702029292000721764352 }, { argument := 6595899271817416777196896256, coefficient := 6595899271817416777196896256 }, { argument := 157876040635113653183228936192, coefficient := 157876040635113653183228936192 }, { argument := 118087874059956977785299271680, coefficient := 118087874059956977785299271680 }, { argument := 137024488098400529177896812544, coefficient := 137024488098400529177896812544 }, { argument := 6595899271817416777196896256, coefficient := 6595899271817416777196896256 }, { argument := 136811717154148354443148525568, coefficient := 136811717154148354443148525568 }, { argument := 137450029986904878647393386496, coefficient := 137450029986904878647393386496 }, { argument := 6595899271817416777196896256, coefficient := 6595899271817416777196896256 }, { argument := 157876040635113653183228936192, coefficient := 157876040635113653183228936192 }, { argument := 6595899271817416777196896256, coefficient := 6595899271817416777196896256 }, { argument := 871509787656907713528983453696, coefficient := (-871509787656907713528983453696) }, { argument := 85301805832008234567267778560, coefficient := 85301805832008234567267778560 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }] }

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

end TermShard11


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
