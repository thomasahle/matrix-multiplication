import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-62594307774318779018218991859531776)
def positiveArguments : Array ℕ := #[
    4095, 8645, 22295, 18655, 521885, 15925,
    18655, 16835, 8645, 8645, 16835, 521885,
    16835, 1365, 22295, 1017, 15255, 26781,
    1017, 8475, 1017, 26781, 53223, 8475,
    821397, 52545, 15255, 26781, 1017, 52545,
    1017, 26781, 26781, 1017, 1, 5,
    5, 1000361935, 3653229201, 31260333, 1151933643, 45144788713,
    22572396165, 575970209, 76561273, 7312181531, 299893131893, 29248774971,
    76561273, 12549645, 2347794931, 37564720967, 200792249, 7463883,
    337353933, 937965
  ]
def positiveCoefficients : Array ℕ := #[
    316835278804602014106994606080, 334437238738191014890716528640, 431248018372930519201187102720, 5773442858217192257060790599680, 10094724021913291949464522588160, 308034298837807513715133644800,
    5773442858217192257060790599680, 325636258771396514498855567360, 334437238738191014890716528640, 334437238738191014890716528640, 325636258771396514498855567360, 10094724021913291949464522588160,
    325636258771396514498855567360, 422447038406136018809326141440, 431248018372930519201187102720, 39343281873538491861637791744, 590149228103077377924566876160, 1036039756003180285689795182592,
    39343281873538491861637791744, 655721364558974864360629862400, 39343281873538491861637791744, 1036039756003180285689795182592, 1029482542357590537046188883968, 655721364558974864360629862400,
    15888128663263960963458061565952, 1016368115066411039758976286720, 590149228103077377924566876160, 1036039756003180285689795182592, 39343281873538491861637791744, 1016368115066411039758976286720,
    39343281873538491861637791744, 1036039756003180285689795182592, 1036039756003180285689795182592, 39343281873538491861637791744, 158456325028528675187087900672, 792281625142643375935439503360,
    792281625142643375935439503360, 4724075672582622638736419061760, 17251887133043054171184112336896, 4723927961681404959103779864576, 5439852826193127505130346774528, 213190237094503067093577653813248,
    213190254175302635633084391751680, 5439884820226048946976669564928, 723100779002065461237845590016, 138123203914611390448441757794304, 1416205274494309037197050698006528, 138123434588046979182001511202816,
    723100779002065461237845590016, 948224366718602059325343006720, 177394369452890421863742089199616, 177394379232911407886777326764032, 948214586697616036290105442304, 281977527290084289012295532544,
    12744871248507615513239768530944, 283482526598708913463319592960
  ]
def positiveScales : Array ℕ := #[
    11, 13, 14, 14, 18, 13,
    14, 14, 13, 13, 14, 18,
    14, 10, 14, 9, 13, 14,
    9, 13, 9, 14, 15, 13,
    19, 15, 13, 14, 9, 15,
    9, 14, 14, 9, 0, 2,
    2, 29, 31, 24, 30, 35,
    34, 29, 26, 32, 38, 34,
    26, 23, 31, 35, 27, 22,
    28, 19
  ]
def negativeArguments : Array ℕ := #[
    455, 339, 1, 5, 337, 5519,
    5345, 2251
  ]
def negativeCoefficients : Array ℕ := #[
    36048813943990273605062497402880, 26858347092335610444211399163904, 158456325028528675187087900672, 1584563250285286751870879006720, 26699890767307081769024311263232, 437260228916224879178769061904384,
    1693898114554971537749969658183680, 356685187639218047846134864412672
  ]
def negativeScales : Array ℕ := #[
    8, 8, 0, 2, 8, 12,
    12, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11999647735076951, 13077650248529644, 14444432579201264, 14187274739704142, 18993372409788943, 13959005751282622,
    14187274739704142, 14039176100715008, 13077650248529644, 13077650248529644, 14039176100715008, 18993372409788943,
    14039176100715008, 10414685235807213, 14444432579201264, 9990103962611722, 13896994559210218, 14708922211307911,
    9990103962611722, 13048997652911068, 9990103962611722, 14708922211307911, 15699762212023501, 13048997652911068,
    19647720152586440, 15681265868407705, 13896994559210218, 14708922211307911, 9990103962611722, 15681265868407705,
    9990103962611722, 14708922211307911, 14708922211307911, 9990103962611722, 0, 2321928094887362,
    2321928094887362, 29897874921084481, 31766525124165840, 24897829810648045, 30101410466884440, 35393840408742944,
    34393840524331651, 29101418951947984, 26190111482221454, 32767654740913060, 38125657525963068, 34767657150292036,
    26190111482221454, 23581143218508228, 31128659255215480, 35128659334753446, 27581128338421789, 22831494940668907,
    28329687740519362, 19839174564181521
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8829722736256263, 8405141463136353, 0, 2321928094887363, 8396604781181865, 12430191170191718,
    12383974232607857, 11136350341454156
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
noncomputable def positiveFloor : ℝ := 4354838537 / 3906250000
noncomputable def negativeCeiling : ℝ := 187516405379 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 316835278804602014106994606080, coefficient := 316835278804602014106994606080 }, { argument := 334437238738191014890716528640, coefficient := 334437238738191014890716528640 }, { argument := 431248018372930519201187102720, coefficient := 431248018372930519201187102720 }, { argument := 5773442858217192257060790599680, coefficient := 5773442858217192257060790599680 }, { argument := 10094724021913291949464522588160, coefficient := 10094724021913291949464522588160 }, { argument := 308034298837807513715133644800, coefficient := 308034298837807513715133644800 }, { argument := 5773442858217192257060790599680, coefficient := 5773442858217192257060790599680 }, { argument := 325636258771396514498855567360, coefficient := 325636258771396514498855567360 }, { argument := 334437238738191014890716528640, coefficient := 334437238738191014890716528640 }, { argument := 334437238738191014890716528640, coefficient := 334437238738191014890716528640 }, { argument := 325636258771396514498855567360, coefficient := 325636258771396514498855567360 }, { argument := 10094724021913291949464522588160, coefficient := 10094724021913291949464522588160 }, { argument := 325636258771396514498855567360, coefficient := 325636258771396514498855567360 }, { argument := 422447038406136018809326141440, coefficient := 422447038406136018809326141440 }, { argument := 431248018372930519201187102720, coefficient := 431248018372930519201187102720 }, { argument := 36048813943990273605062497402880, coefficient := (-36048813943990273605062497402880) }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 590149228103077377924566876160, coefficient := 590149228103077377924566876160 }, { argument := 1036039756003180285689795182592, coefficient := 1036039756003180285689795182592 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 655721364558974864360629862400, coefficient := 655721364558974864360629862400 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 1036039756003180285689795182592, coefficient := 1036039756003180285689795182592 }, { argument := 1029482542357590537046188883968, coefficient := 1029482542357590537046188883968 }, { argument := 655721364558974864360629862400, coefficient := 655721364558974864360629862400 }, { argument := 15888128663263960963458061565952, coefficient := 15888128663263960963458061565952 }, { argument := 1016368115066411039758976286720, coefficient := 1016368115066411039758976286720 }, { argument := 590149228103077377924566876160, coefficient := 590149228103077377924566876160 }, { argument := 1036039756003180285689795182592, coefficient := 1036039756003180285689795182592 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 1016368115066411039758976286720, coefficient := 1016368115066411039758976286720 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 1036039756003180285689795182592, coefficient := 1036039756003180285689795182592 }, { argument := 1036039756003180285689795182592, coefficient := 1036039756003180285689795182592 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 26858347092335610444211399163904, coefficient := (-26858347092335610444211399163904) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 4724075672582622638736419061760, coefficient := 4724075672582622638736419061760 }, { argument := 17251887133043054171184112336896, coefficient := 17251887133043054171184112336896 }, { argument := 4723927961681404959103779864576, coefficient := 4723927961681404959103779864576 }, { argument := 26699890767307081769024311263232, coefficient := (-26699890767307081769024311263232) }, { argument := 5439852826193127505130346774528, coefficient := 5439852826193127505130346774528 }, { argument := 213190237094503067093577653813248, coefficient := 213190237094503067093577653813248 }, { argument := 213190254175302635633084391751680, coefficient := 213190254175302635633084391751680 }, { argument := 5439884820226048946976669564928, coefficient := 5439884820226048946976669564928 }, { argument := 437260228916224879178769061904384, coefficient := (-437260228916224879178769061904384) }, { argument := 723100779002065461237845590016, coefficient := 723100779002065461237845590016 }, { argument := 138123203914611390448441757794304, coefficient := 138123203914611390448441757794304 }, { argument := 1416205274494309037197050698006528, coefficient := 1416205274494309037197050698006528 }, { argument := 138123434588046979182001511202816, coefficient := 138123434588046979182001511202816 }, { argument := 723100779002065461237845590016, coefficient := 723100779002065461237845590016 }, { argument := 1693898114554971537749969658183680, coefficient := (-1693898114554971537749969658183680) }, { argument := 948224366718602059325343006720, coefficient := 948224366718602059325343006720 }, { argument := 177394369452890421863742089199616, coefficient := 177394369452890421863742089199616 }, { argument := 177394379232911407886777326764032, coefficient := 177394379232911407886777326764032 }, { argument := 948214586697616036290105442304, coefficient := 948214586697616036290105442304 }, { argument := 356685187639218047846134864412672, coefficient := (-356685187639218047846134864412672) }, { argument := 281977527290084289012295532544, coefficient := 281977527290084289012295532544 }, { argument := 12744871248507615513239768530944, coefficient := 12744871248507615513239768530944 }, { argument := 283482526598708913463319592960, coefficient := 283482526598708913463319592960 }] }

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


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1317722798937244462855822981988352)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    21
  ]
def negativeCoefficients : Array ℕ := #[
    13310331302396408715715383656448
  ]
def negativeScales : Array ℕ := #[
    4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    4392317422778766
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 1
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
noncomputable def negativeCeiling : ℝ := 351862587 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13310331302396408715715383656448, coefficient := (-13310331302396408715715383656448) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
