import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4225687112089942757161847813570560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1575, 49455, 1575, 48195, 27405, 49455,
    772065, 945, 1575, 48195, 1575, 945,
    1575, 24255, 27405, 945, 503792065, 199861,
    8081308163, 3145181, 94671, 8081312117, 94671, 94671,
    8110149, 94671, 3145181, 8110149, 503788111, 94671,
    94671, 199861, 26452640909907373, 46691340730313299, 26452640905778605, 1118890349,
    6365, 18830727751, 100165, 3015, 18830736977, 3015,
    3015, 258285, 3015, 100165, 258285, 1118881123,
    3015, 3015, 6365, 5826420605, 19888325115, 728302545,
    123103256525009, 123103201969967, 945, 1575, 48195, 1575,
    49455, 1575, 48195, 27405
  ]
def negativeCoefficients : Array ℕ := #[
    59501817684157529692569600, 1868357075282546432346685440, 59501817684157529692569600, 1820755621135220408592629760, 1035331627704341016650711040, 1868357075282546432346685440,
    29167791028774021055297617920, 1142434899535824570097336320, 1904058165893040950162227200, 1820755621135220408592629760, 59501817684157529692569600, 1142434899535824570097336320,
    59501817684157529692569600, 1832655984672051914531143680, 1035331627704341016650711040, 71402181220989035631083520, 18586646578841294437697454080, 1887633775265620324108992512,
    596295293854563492661802565632, 14852697336958433602857598976, 1788284629199008728103256064, 596295585608267762452070924288, 1788284629199008728103256064, 1788284629199008728103256064,
    76598191617357540520422801408, 1788284629199008728103256064, 14852697336958433602857598976, 76598191617357540520422801408, 18586500701989159542563274752, 1788284629199008728103256064,
    1788284629199008728103256064, 1887633775265620324108992512, 14891512968103047911738364133376, 52569776178616958986189407256576, 14891512965778758158450960629760, 1289992744659160120766234624,
    60115725326930583570350080, 43420701943049655391147261952, 473015838756638012829859840, 56951739783407921277173760, 43420723216757258396687663104, 56951739783407921277173760,
    56951739783407921277173760, 2439432854055972628038942720, 56951739783407921277173760, 473015838756638012829859840, 2439432854055972628038942720, 1289982107805358617996034048,
    56951739783407921277173760, 56951739783407921277173760, 60115725326930583570350080, 53739244883111485160386723840, 183437421725567543309940817920, 53739242623385336130966650880,
    138601945053531278175283183616, 138601883630014572579843473408, 71402181220989035631083520, 1904058165893040950162227200, 1820755621135220408592629760, 59501817684157529692569600,
    1868357075282546432346685440, 59501817684157529692569600, 1820755621135220408592629760, 1035331627704341016650711040
  ]
def negativeScales : Array ℕ := #[
    10, 15, 10, 15, 14, 15,
    19, 9, 10, 15, 10, 9,
    10, 14, 14, 9, 28, 17,
    32, 21, 16, 32, 16, 16,
    22, 16, 21, 22, 28, 16,
    16, 17, 54, 55, 54, 30,
    12, 34, 16, 11, 34, 11,
    11, 17, 11, 16, 17, 30,
    11, 11, 12, 32, 34, 29,
    46, 46, 9, 10, 15, 10,
    15, 10, 15, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10621136113284685, 15593828767283669, 10621136113284685, 15556595861081553, 14742151514425259, 15593828767283669,
    19558362787255829, 9884170522387776, 10621136113284685, 15556595861081553, 10621136113284685, 9884170522387776,
    10621136113284685, 14565994559084324, 14742151514425259, 9884170522387776, 28908253163176023, 17608637452800154,
    32911941707750489, 21584711613551188, 16530634940792444, 32911942413628204, 16530634940792444, 16530634940792444,
    22951296999919123, 16530634940792444, 21584711613551188, 22951296999919123, 28908241840172971, 16530634940792444,
    16530634940792444, 17608637452800154, 54554261279761018, 55374004534004352, 54554261279535840, 30059421513441666,
    12635944798803559, 34132369705728063, 16612018959551099, 11557942286789136, 34132370412567510, 11557942286789136,
    11557942286789136, 17978604352023330, 11557942286789136, 16612018959551099, 17978604352023330, 30059409617406156,
    11557942286789136, 11557942286789136, 12635944798803559, 32439962706313294, 34211202734345107, 29439962645648210,
    46806862255978574, 46806861616626624, 9884170522387776, 10621136113284685, 15556595861081553, 10621136113284685,
    15593828767283669, 10621136113284685, 15556595861081553, 14742151514425259
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
noncomputable def negativeCeiling : ℝ := 27728303537 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 18586646578841294437697454080, coefficient := (-18586646578841294437697454080) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 596295293854563492661802565632, coefficient := (-596295293854563492661802565632) }, { argument := 14852697336958433602857598976, coefficient := (-14852697336958433602857598976) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 596295585608267762452070924288, coefficient := (-596295585608267762452070924288) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 76598191617357540520422801408, coefficient := (-76598191617357540520422801408) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 14852697336958433602857598976, coefficient := (-14852697336958433602857598976) }, { argument := 76598191617357540520422801408, coefficient := (-76598191617357540520422801408) }, { argument := 18586500701989159542563274752, coefficient := (-18586500701989159542563274752) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 14891512968103047911738364133376, coefficient := (-14891512968103047911738364133376) }, { argument := 52569776178616958986189407256576, coefficient := (-52569776178616958986189407256576) }, { argument := 14891512965778758158450960629760, coefficient := (-14891512965778758158450960629760) }, { argument := 1289992744659160120766234624, coefficient := (-1289992744659160120766234624) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 43420701943049655391147261952, coefficient := (-43420701943049655391147261952) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 43420723216757258396687663104, coefficient := (-43420723216757258396687663104) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 1289982107805358617996034048, coefficient := (-1289982107805358617996034048) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 53739244883111485160386723840, coefficient := (-53739244883111485160386723840) }, { argument := 183437421725567543309940817920, coefficient := (-183437421725567543309940817920) }, { argument := 53739242623385336130966650880, coefficient := (-53739242623385336130966650880) }, { argument := 138601945053531278175283183616, coefficient := (-138601945053531278175283183616) }, { argument := 138601883630014572579843473408, coefficient := (-138601883630014572579843473408) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-320764727049216151860296426717184)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    49455, 772065, 945, 1575, 48195, 1575,
    945, 1575, 24255, 27405, 945, 80955,
    134925, 4128705, 134925, 4236645, 134925, 4128705,
    2347695, 4236645, 66140235, 80955, 134925, 4128705,
    134925, 80955, 134925, 2077845, 2347695, 80955,
    14646565513, 194769, 244845222299, 3065049, 92259, 244845342237,
    92259, 92259, 7903521, 92259, 3065049, 7903521,
    14646445575, 92259, 92259, 194769, 945, 1575,
    48195, 1575, 49455, 1575, 48195, 27405,
    49455, 772065, 945, 1575, 48195, 1575,
    945, 1575, 24255, 27405
  ]
def negativeCoefficients : Array ℕ := #[
    1868357075282546432346685440, 29167791028774021055297617920, 1142434899535824570097336320, 1904058165893040950162227200, 1820755621135220408592629760, 59501817684157529692569600,
    1142434899535824570097336320, 59501817684157529692569600, 1832655984672051914531143680, 1035331627704341016650711040, 71402181220989035631083520, 3058393428965697026198077440,
    81557158105751920698615398400, 77989032438625274168050974720, 2548661190804747521831731200, 80027961391269072185516359680, 2548661190804747521831731200, 77989032438625274168050974720,
    44346704720002606879872122880, 80027961391269072185516359680, 1249353715732487235201914634240, 48934294863451152419169239040, 81557158105751920698615398400, 77989032438625274168050974720,
    2548661190804747521831731200, 48934294863451152419169239040, 2548661190804747521831731200, 78498764676786223672417320960, 44346704720002606879872122880, 3058393428965697026198077440,
    33772680697141431084699877376, 1839541195004075857252712448, 1129149288355044001744783671296, 14474284665953123192593711104, 1742723237372282391081517056, 1129149841471441679888834101248,
    1742723237372282391081517056, 1742723237372282391081517056, 74646645334112762417991647232, 1742723237372282391081517056, 14474284665953123192593711104, 74646645334112762417991647232,
    33772404138942592012674662400, 1742723237372282391081517056, 1742723237372282391081517056, 1839541195004075857252712448, 71402181220989035631083520, 1904058165893040950162227200,
    1820755621135220408592629760, 59501817684157529692569600, 1868357075282546432346685440, 59501817684157529692569600, 1820755621135220408592629760, 1035331627704341016650711040,
    1868357075282546432346685440, 29167791028774021055297617920, 1142434899535824570097336320, 1904058165893040950162227200, 1820755621135220408592629760, 59501817684157529692569600,
    1142434899535824570097336320, 59501817684157529692569600, 1832655984672051914531143680, 1035331627704341016650711040
  ]
def negativeScales : Array ℕ := #[
    15, 19, 9, 10, 15, 10,
    9, 10, 14, 14, 9, 16,
    17, 21, 17, 22, 17, 21,
    21, 22, 25, 16, 17, 21,
    17, 16, 17, 20, 21, 16,
    33, 17, 37, 21, 16, 37,
    16, 16, 22, 16, 21, 22,
    33, 16, 16, 17, 9, 10,
    15, 10, 15, 10, 15, 14,
    15, 19, 9, 10, 15, 10,
    9, 10, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15593828767283669, 19558362787255829, 9884170522387776, 10621136113284685, 15556595861081553, 10621136113284685,
    9884170522387776, 10621136113284685, 14565994559084324, 14742151514425259, 9884170522387776, 16304832567581158,
    17041798161747364, 21977257925950856, 17041798161747364, 22014490815751628, 17041798161747364, 21977257925950856,
    21162813562708730, 22014490815751628, 25979024852605519, 16304832567581158, 17041798161747364, 21977257925950856,
    17041798161747364, 16304832567581158, 17041798161747364, 20986656626663166, 21162813562708730, 16304832567581158,
    33769843354599189, 17571404546596521, 37833079089810405, 21547478707349761, 16493402034592954, 37833079796517761,
    16493402034592954, 16493402034592954, 22914064088673542, 16493402034592954, 21547478707349761, 22914064088673542,
    33769831540589454, 16493402034592954, 16493402034592954, 17571404546596521, 9884170522387776, 10621136113284685,
    15556595861081553, 10621136113284685, 15593828767283669, 10621136113284685, 15556595861081553, 14742151514425259,
    15593828767283669, 19558362787255829, 9884170522387776, 10621136113284685, 15556595861081553, 10621136113284685,
    9884170522387776, 10621136113284685, 14565994559084324, 14742151514425259
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
noncomputable def negativeCeiling : ℝ := 343896327 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 3058393428965697026198077440, coefficient := (-3058393428965697026198077440) }, { argument := 81557158105751920698615398400, coefficient := (-81557158105751920698615398400) }, { argument := 77989032438625274168050974720, coefficient := (-77989032438625274168050974720) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 80027961391269072185516359680, coefficient := (-80027961391269072185516359680) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 77989032438625274168050974720, coefficient := (-77989032438625274168050974720) }, { argument := 44346704720002606879872122880, coefficient := (-44346704720002606879872122880) }, { argument := 80027961391269072185516359680, coefficient := (-80027961391269072185516359680) }, { argument := 1249353715732487235201914634240, coefficient := (-1249353715732487235201914634240) }, { argument := 48934294863451152419169239040, coefficient := (-48934294863451152419169239040) }, { argument := 81557158105751920698615398400, coefficient := (-81557158105751920698615398400) }, { argument := 77989032438625274168050974720, coefficient := (-77989032438625274168050974720) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 48934294863451152419169239040, coefficient := (-48934294863451152419169239040) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 78498764676786223672417320960, coefficient := (-78498764676786223672417320960) }, { argument := 44346704720002606879872122880, coefficient := (-44346704720002606879872122880) }, { argument := 3058393428965697026198077440, coefficient := (-3058393428965697026198077440) }, { argument := 33772680697141431084699877376, coefficient := (-33772680697141431084699877376) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1129149288355044001744783671296, coefficient := (-1129149288355044001744783671296) }, { argument := 14474284665953123192593711104, coefficient := (-14474284665953123192593711104) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1129149841471441679888834101248, coefficient := (-1129149841471441679888834101248) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 74646645334112762417991647232, coefficient := (-74646645334112762417991647232) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 14474284665953123192593711104, coefficient := (-14474284665953123192593711104) }, { argument := 74646645334112762417991647232, coefficient := (-74646645334112762417991647232) }, { argument := 33772404138942592012674662400, coefficient := (-33772404138942592012674662400) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
