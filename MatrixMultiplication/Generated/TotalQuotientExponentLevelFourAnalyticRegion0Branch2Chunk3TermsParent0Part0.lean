import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 3, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7698393168361019582896440082432)
def positiveArguments : Array ℕ := #[
    7, 4503303, 32313051, 9011991, 1721603, 130775765,
    130814001, 850621, 66333, 6484251, 21794811, 6471891,
    131289
  ]
def positiveCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 170129977195250575198182703104, 610376276006629888568258985984, 170231696969291587356085714944, 32520161216031319235338698752, 1235142178815274496199365754880,
    1235503307624952503708147515392, 32135552800200483850554441728, 2505989887265537407680774144, 61242019177827959693107003392, 823384679735029240556471451648, 61125282278371422063424438272,
    2479979092677891401843736576
  ]
def positiveScales : Array ℕ := #[
    2, 22, 24, 23, 20, 26,
    26, 19, 16, 22, 24, 22,
    17
  ]
def negativeArguments : Array ℕ := #[
    398055627117, 19464620057397, 130867882016049, 19427265892737, 393893670663, 185267410159,
    28142813644475, 28151752876761, 45735914539, 398055627117, 714698025099, 398314460541,
    714698025099, 69846587454759, 234749381916321, 69713929784175, 1414617743709, 28142813644475,
    534447031993745, 1069205871538845, 13905253899715, 19464620057397, 69846587454759, 4869118028265,
    398314460541, 4869118028265, 130945857803661, 1214944847409, 98538124263, 28151752876761,
    1069205871538845, 66844864020555, 13909650928365, 130867882016049, 234749381916321, 130945857803661,
    45735914539, 13905253899715, 13909650928365, 45164044735, 19427265892737, 69713929784175,
    1214944847409, 393893670663, 1414617743709, 98538124263, 3, 1,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    224085396744606287872917504, 5478803477337588228981522432, 73672068085280538903642636288, 5468289214709868719580905472, 221742423552685459013369856, 208592559838992311271817216,
    7921497815150932530928025600, 7924013985350445525123465216, 205976247675289250346041344, 224085396744606287872917504, 804678439879571449395019776, 224231107008590966572449792,
    804678439879571449395019776, 19660066577147087065033211904, 264304307230949376953684066304, 19622726762408965789502668800, 796358992929943026514526208, 7921497815150932530928025600,
    300866931767037191987333693440, 300954697790293047287029432320, 7827962035156076294391726080, 5478803477337588228981522432, 19660066577147087065033211904, 5482139534429304552538767360,
    224231107008590966572449792, 5482139534429304552538767360, 73715964551284704420909023232, 5471625162066876522628644864, 221888129856317215393972224, 7924013985350445525123465216,
    300954697790293047287029432320, 301042504694602973073144545280, 7830437342229785968776314880, 73672068085280538903642636288, 264304307230949376953684066304, 73715964551284704420909023232,
    205976247675289250346041344, 7827962035156076294391726080, 7830437342229785968776314880, 203400775039090411763138560, 5468289214709868719580905472, 19622726762408965789502668800,
    5471625162066876522628644864, 221742423552685459013369856, 796358992929943026514526208, 221888129856317215393972224, 950737950171172051122527404032, 2535301200456458802993406410752,
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    38, 44, 46, 44, 38, 37,
    44, 44, 35, 38, 39, 38,
    39, 45, 47, 45, 40, 44,
    48, 49, 43, 44, 45, 42,
    38, 42, 46, 40, 36, 44,
    49, 45, 43, 46, 47, 46,
    35, 43, 43, 35, 44, 45,
    40, 38, 40, 36, 1, 0,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 22102552120486259, 24945613639991387, 23103414442122786, 20715321066312706, 26962519967690291,
    26962941718801508, 19698156946868411, 16017439154742540, 22628508506793081, 24377481357210856, 22625755879334298,
    17002386520064051
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38534179101058402, 44145919417591115, 46895104402649104, 44143148110241722, 38519015278747300, 37430818167235848,
    44677831806218436, 44678289988490976, 35412608448476146, 38534179101058402, 39378542845489162, 38535116900496544,
    39378542845489162, 45989254884025032, 47738114687934462, 45986512207439785, 40363549401063323, 44677831806218436,
    48925040307549463, 49925461095424830, 43660695321039694, 44145919417591115, 45989254884025032, 42146797610857112,
    38535116900496544, 42146797610857112, 46895963756277182, 40144027962623019, 36519962958151357, 44678289988490976,
    49925461095424830, 45925881956521550, 43661151448538566, 46895104402649104, 47738114687934462, 46895963756277182,
    35412608448476146, 43660695321039694, 43661151448538566, 35394455643528010, 44143148110241722, 45986512207439785,
    40144027962623019, 38519015278747300, 40363549401063323, 36519962958151357, 1584962500724866, 0,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 13
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
noncomputable def positiveFloor : ℝ := 722178301 / 500000000000
noncomputable def negativeCeiling : ℝ := 262787609 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 224085396744606287872917504, coefficient := (-224085396744606287872917504) }, { argument := 5478803477337588228981522432, coefficient := (-5478803477337588228981522432) }, { argument := 73672068085280538903642636288, coefficient := (-73672068085280538903642636288) }, { argument := 5468289214709868719580905472, coefficient := (-5468289214709868719580905472) }, { argument := 221742423552685459013369856, coefficient := (-221742423552685459013369856) }, { argument := 208592559838992311271817216, coefficient := (-208592559838992311271817216) }, { argument := 7921497815150932530928025600, coefficient := (-7921497815150932530928025600) }, { argument := 7924013985350445525123465216, coefficient := (-7924013985350445525123465216) }, { argument := 205976247675289250346041344, coefficient := (-205976247675289250346041344) }, { argument := 224085396744606287872917504, coefficient := (-224085396744606287872917504) }, { argument := 804678439879571449395019776, coefficient := (-804678439879571449395019776) }, { argument := 224231107008590966572449792, coefficient := (-224231107008590966572449792) }, { argument := 804678439879571449395019776, coefficient := (-804678439879571449395019776) }, { argument := 19660066577147087065033211904, coefficient := (-19660066577147087065033211904) }, { argument := 264304307230949376953684066304, coefficient := (-264304307230949376953684066304) }, { argument := 19622726762408965789502668800, coefficient := (-19622726762408965789502668800) }, { argument := 796358992929943026514526208, coefficient := (-796358992929943026514526208) }, { argument := 7921497815150932530928025600, coefficient := (-7921497815150932530928025600) }, { argument := 300866931767037191987333693440, coefficient := (-300866931767037191987333693440) }, { argument := 300954697790293047287029432320, coefficient := (-300954697790293047287029432320) }, { argument := 7827962035156076294391726080, coefficient := (-7827962035156076294391726080) }, { argument := 5478803477337588228981522432, coefficient := (-5478803477337588228981522432) }, { argument := 19660066577147087065033211904, coefficient := (-19660066577147087065033211904) }, { argument := 5482139534429304552538767360, coefficient := (-5482139534429304552538767360) }, { argument := 224231107008590966572449792, coefficient := (-224231107008590966572449792) }, { argument := 5482139534429304552538767360, coefficient := (-5482139534429304552538767360) }, { argument := 73715964551284704420909023232, coefficient := (-73715964551284704420909023232) }, { argument := 5471625162066876522628644864, coefficient := (-5471625162066876522628644864) }, { argument := 221888129856317215393972224, coefficient := (-221888129856317215393972224) }, { argument := 7924013985350445525123465216, coefficient := (-7924013985350445525123465216) }, { argument := 300954697790293047287029432320, coefficient := (-300954697790293047287029432320) }, { argument := 301042504694602973073144545280, coefficient := (-301042504694602973073144545280) }, { argument := 7830437342229785968776314880, coefficient := (-7830437342229785968776314880) }, { argument := 73672068085280538903642636288, coefficient := (-73672068085280538903642636288) }, { argument := 264304307230949376953684066304, coefficient := (-264304307230949376953684066304) }, { argument := 73715964551284704420909023232, coefficient := (-73715964551284704420909023232) }, { argument := 205976247675289250346041344, coefficient := (-205976247675289250346041344) }, { argument := 7827962035156076294391726080, coefficient := (-7827962035156076294391726080) }, { argument := 7830437342229785968776314880, coefficient := (-7830437342229785968776314880) }, { argument := 203400775039090411763138560, coefficient := (-203400775039090411763138560) }, { argument := 5468289214709868719580905472, coefficient := (-5468289214709868719580905472) }, { argument := 19622726762408965789502668800, coefficient := (-19622726762408965789502668800) }, { argument := 5471625162066876522628644864, coefficient := (-5471625162066876522628644864) }, { argument := 221742423552685459013369856, coefficient := (-221742423552685459013369856) }, { argument := 796358992929943026514526208, coefficient := (-796358992929943026514526208) }, { argument := 221888129856317215393972224, coefficient := (-221888129856317215393972224) }, { argument := 2218388550399401452619230609408, coefficient := 2218388550399401452619230609408 }, { argument := 170129977195250575198182703104, coefficient := 170129977195250575198182703104 }, { argument := 610376276006629888568258985984, coefficient := 610376276006629888568258985984 }, { argument := 170231696969291587356085714944, coefficient := 170231696969291587356085714944 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 32520161216031319235338698752, coefficient := 32520161216031319235338698752 }, { argument := 1235142178815274496199365754880, coefficient := 1235142178815274496199365754880 }, { argument := 1235503307624952503708147515392, coefficient := 1235503307624952503708147515392 }, { argument := 32135552800200483850554441728, coefficient := 32135552800200483850554441728 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 2505989887265537407680774144, coefficient := 2505989887265537407680774144 }, { argument := 61242019177827959693107003392, coefficient := 61242019177827959693107003392 }, { argument := 823384679735029240556471451648, coefficient := 823384679735029240556471451648 }, { argument := 61125282278371422063424438272, coefficient := 61125282278371422063424438272 }, { argument := 2479979092677891401843736576, coefficient := 2479979092677891401843736576 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end TermShard0


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3
