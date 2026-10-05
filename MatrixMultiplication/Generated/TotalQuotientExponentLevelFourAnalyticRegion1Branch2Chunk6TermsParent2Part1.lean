import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-63288722718232153198112278577152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    897435, 21645, 834165, 4995, 3954651391353, 292728859040391,
    12615, 118581, 1400265, 98397, 146364404199285, 1400265,
    12615, 98397, 98397, 98397, 98397, 98397,
    1977351016587, 118581, 375, 7515, 12615, 12105,
    375, 12105, 8085, 195, 7515, 45,
    223138315, 9429151221, 12105, 113787, 1343655, 94419,
    4714577301, 1343655, 12105, 94419, 94419, 94419,
    94419, 94419, 111567467, 113787, 15214141, 2317101281,
    94940008835, 2317101281, 60853889, 2925, 58617, 98397,
    94419, 2925, 94419, 63063, 1521, 58617,
    351, 2925, 58617, 98397
  ]
def negativeCoefficients : Array ℕ := #[
    4238016964554120052353269760, 204431245043426941300899840, 3939232837182957599682723840, 188705764655471022739292160, 4452541633119396086805430272, 329583395123723839223296425984,
    476581225451204594966200320, 559982939905165399085285376, 6612564503135463755156029440, 14869334234077583362945449984, 329583338106102292982456647680, 6612564503135463755156029440,
    476581225451204594966200320, 464666694814924480092045312, 464666694814924480092045312, 464666694814924480092045312, 14869334234077583362945449984, 464666694814924480092045312,
    4452598650740942327645208576, 559982939905165399085285376, 14167099448608935641088000, 283908672950123070247403520, 476581225451204594966200320, 457313970201096442494320640,
    14167099448608935641088000, 457313970201096442494320640, 305442664112008652421857280, 14733783426553293066731520, 283908672950123070247403520, 13600415470664578215444480,
    1029043847460946286749941760, 43484284851523233154842230784, 457313970201096442494320640, 537343914986288319930826752, 6345231336540213139608698880, 14268195870274209005822803968,
    43484300443633661457840734208, 6345231336540213139608698880, 457313970201096442494320640, 445881120946069031431962624, 445881120946069031431962624, 445881120946069031431962624,
    14268195870274209005822803968, 445881120946069031431962624, 1029028255350517983751438336, 537343914986288319930826752, 140325682664165755666300928, 21371487161735780235684610048,
    218916755666871090205866065920, 21371487161735780235684610048, 140319514534116109034979328, 13812921962393712250060800, 276810956126369993491218432, 464666694814924480092045312,
    445881120946069031431962624, 13812921962393712250060800, 445881120946069031431962624, 297806597509208436111310848, 14365438840889460740063232, 276810956126369993491218432,
    13260405083897963760058368, 13812921962393712250060800, 276810956126369993491218432, 464666694814924480092045312
  ]
def negativeScales : Array ℕ := #[
    19, 14, 19, 12, 41, 48,
    13, 16, 20, 16, 47, 20,
    13, 16, 16, 16, 16, 16,
    40, 16, 8, 12, 13, 13,
    8, 13, 12, 7, 12, 5,
    27, 33, 13, 16, 20, 16,
    32, 20, 13, 16, 16, 16,
    16, 16, 26, 16, 23, 31,
    36, 31, 25, 11, 15, 16,
    16, 11, 16, 15, 10, 15,
    8, 11, 15, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19775447925099447, 14401746180099724, 19669973255188965, 12286268962679781, 41846687664774249, 48056558311074692,
    13622852585874176, 16855513344577571, 20417268452213782, 16586326709842405, 47056558061489767, 20417268452213782,
    13622852585874176, 16586326709842405, 16586326709842405, 16586326709842405, 16586326709842405, 16586326709842405,
    40846706139282183, 16855513344577571, 8550746785384604, 12875557391602924, 13622852585874176, 13563315458888280,
    8550746785384604, 13563315458888280, 12981032075801390, 7607330313756529, 12875557391602924, 5491853096329881,
    27733363018755179, 33134480764402396, 13563315458888280, 16795976216271593, 20357731325236406, 16526789582861833,
    32134481281707818, 20357731325236406, 13563315458888280, 16526789582861833, 16526789582861833, 16526789582861833,
    16526789582861833, 16526789582861833, 26733341158820885, 16795976216271593, 23858909546942462, 31109673960080655,
    36466297132896479, 31109673960080655, 25858846130706811, 11514220909358563, 15839031514181448, 16586326709842405,
    16526789582861833, 11514220909358563, 16526789582861833, 15944506191833593, 10570804437726965, 15839031514181448,
    8455327220304618, 11514220909358563, 15839031514181448, 16586326709842405
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
noncomputable def negativeCeiling : ℝ := 551197763 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4238016964554120052353269760, coefficient := (-4238016964554120052353269760) }, { argument := 204431245043426941300899840, coefficient := (-204431245043426941300899840) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 188705764655471022739292160, coefficient := (-188705764655471022739292160) }, { argument := 4452541633119396086805430272, coefficient := (-4452541633119396086805430272) }, { argument := 329583395123723839223296425984, coefficient := (-329583395123723839223296425984) }, { argument := 476581225451204594966200320, coefficient := (-476581225451204594966200320) }, { argument := 559982939905165399085285376, coefficient := (-559982939905165399085285376) }, { argument := 6612564503135463755156029440, coefficient := (-6612564503135463755156029440) }, { argument := 14869334234077583362945449984, coefficient := (-14869334234077583362945449984) }, { argument := 329583338106102292982456647680, coefficient := (-329583338106102292982456647680) }, { argument := 6612564503135463755156029440, coefficient := (-6612564503135463755156029440) }, { argument := 476581225451204594966200320, coefficient := (-476581225451204594966200320) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 14869334234077583362945449984, coefficient := (-14869334234077583362945449984) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 4452598650740942327645208576, coefficient := (-4452598650740942327645208576) }, { argument := 559982939905165399085285376, coefficient := (-559982939905165399085285376) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 476581225451204594966200320, coefficient := (-476581225451204594966200320) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 305442664112008652421857280, coefficient := (-305442664112008652421857280) }, { argument := 14733783426553293066731520, coefficient := (-14733783426553293066731520) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 13600415470664578215444480, coefficient := (-13600415470664578215444480) }, { argument := 1029043847460946286749941760, coefficient := (-1029043847460946286749941760) }, { argument := 43484284851523233154842230784, coefficient := (-43484284851523233154842230784) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 43484300443633661457840734208, coefficient := (-43484300443633661457840734208) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 1029028255350517983751438336, coefficient := (-1029028255350517983751438336) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 140325682664165755666300928, coefficient := (-140325682664165755666300928) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 218916755666871090205866065920, coefficient := (-218916755666871090205866065920) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 140319514534116109034979328, coefficient := (-140319514534116109034979328) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }] }

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

end TermShard2


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-15062699293289178823916964020224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    94419, 2925, 94419, 63063, 1521, 58617,
    351, 35308085, 1809595851, 375, 3525, 41625,
    2925, 904798251, 41625, 375, 2925, 2925,
    2925, 2925, 2925, 17653717, 3525, 2925,
    58617, 98397, 94419, 2925, 94419, 63063,
    1521, 58617, 351, 2925, 58617, 98397,
    94419, 2925, 94419, 63063, 1521, 58617,
    351, 891860225, 37658577663, 12105, 113787, 1343655,
    94419, 18829295583, 1343655, 12105, 94419, 94419,
    94419, 94419, 94419, 445923361, 113787, 2925,
    58617, 98397, 94419, 2925
  ]
def negativeCoefficients : Array ℕ := #[
    445881120946069031431962624, 13812921962393712250060800, 445881120946069031431962624, 297806597509208436111310848, 14365438840889460740063232, 276810956126369993491218432,
    13260405083897963760058368, 40707450482986444610600960, 2086321971265227673961496576, 14167099448608935641088000, 16646341852115499378278400, 196568504849448982020096000,
    442013502796598792001945600, 2086322721817127173018877952, 196568504849448982020096000, 14167099448608935641088000, 13812921962393712250060800, 13812921962393712250060800,
    13812921962393712250060800, 442013502796598792001945600, 13812921962393712250060800, 40706699931086945553219584, 16646341852115499378278400, 13812921962393712250060800,
    276810956126369993491218432, 464666694814924480092045312, 445881120946069031431962624, 13812921962393712250060800, 445881120946069031431962624, 297806597509208436111310848,
    14365438840889460740063232, 276810956126369993491218432, 13260405083897963760058368, 442013502796598792001945600, 8857950596043839791718989824, 14869334234077583362945449984,
    14268195870274209005822803968, 442013502796598792001945600, 14268195870274209005822803968, 9529811120294669955561947136, 459694042908462743682023424, 8857950596043839791718989824,
    424332962684734840321867776, 1028244832506001080555929600, 43417384020579759127252697088, 457313970201096442494320640, 537343914986288319930826752, 6345231336540213139608698880,
    14268195870274209005822803968, 43417399588478835833507414016, 6345231336540213139608698880, 457313970201096442494320640, 445881120946069031431962624, 445881120946069031431962624,
    445881120946069031431962624, 14268195870274209005822803968, 445881120946069031431962624, 1028229264606924374301212672, 537343914986288319930826752, 13812921962393712250060800,
    276810956126369993491218432, 464666694814924480092045312, 445881120946069031431962624, 13812921962393712250060800
  ]
def negativeScales : Array ℕ := #[
    16, 11, 16, 15, 10, 15,
    8, 25, 30, 8, 11, 15,
    11, 29, 15, 8, 11, 11,
    11, 11, 11, 24, 11, 11,
    15, 16, 16, 11, 16, 15,
    10, 15, 8, 11, 15, 16,
    16, 11, 16, 15, 10, 15,
    8, 29, 35, 13, 16, 20,
    16, 34, 20, 13, 16, 16,
    16, 16, 16, 28, 16, 11,
    15, 16, 16, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16526789582861833, 11514220909358563, 16526789582861833, 15944506191833593, 10570804437726965, 15839031514181448,
    8455327220304618, 25073495240168192, 30753020380892406, 8550746785384604, 11783407542632370, 15345162651733350,
    11514220909358563, 29753020899900176, 15345162651733350, 8550746785384604, 11514220909358563, 11514220909358563,
    11514220909358563, 11514220909358563, 11514220909358563, 24073468639939660, 11783407542632370, 11514220909358563,
    15839031514181448, 16586326709842405, 16526789582861833, 11514220909358563, 16526789582861833, 15944506191833593,
    10570804437726965, 15839031514181448, 8455327220304618, 11514220909358563, 15839031514181448, 16586326709842405,
    16526789582861833, 11514220909358563, 16526789582861833, 15944506191833593, 10570804437726965, 15839031514181448,
    8455327220304618, 29732242383633575, 35132259460315751, 13563315458888280, 16795976216271593, 20357731325236406,
    16526789582861833, 34132259977613771, 20357731325236406, 13563315458888280, 16526789582861833, 16526789582861833,
    16526789582861833, 16526789582861833, 16526789582861833, 28732220540683155, 16795976216271593, 11514220909358563,
    15839031514181448, 16586326709842405, 16526789582861833, 11514220909358563
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
noncomputable def negativeCeiling : ℝ := 63231293 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 40707450482986444610600960, coefficient := (-40707450482986444610600960) }, { argument := 2086321971265227673961496576, coefficient := (-2086321971265227673961496576) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 2086322721817127173018877952, coefficient := (-2086322721817127173018877952) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 40706699931086945553219584, coefficient := (-40706699931086945553219584) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 14869334234077583362945449984, coefficient := (-14869334234077583362945449984) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 9529811120294669955561947136, coefficient := (-9529811120294669955561947136) }, { argument := 459694042908462743682023424, coefficient := (-459694042908462743682023424) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 424332962684734840321867776, coefficient := (-424332962684734840321867776) }, { argument := 1028244832506001080555929600, coefficient := (-1028244832506001080555929600) }, { argument := 43417384020579759127252697088, coefficient := (-43417384020579759127252697088) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 43417399588478835833507414016, coefficient := (-43417399588478835833507414016) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 1028229264606924374301212672, coefficient := (-1028229264606924374301212672) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 464666694814924480092045312, coefficient := (-464666694814924480092045312) }, { argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
