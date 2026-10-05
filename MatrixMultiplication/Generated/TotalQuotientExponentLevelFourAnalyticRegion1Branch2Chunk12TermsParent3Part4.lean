import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10549131361049559098633700060954624)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7151708055, 1124109637, 14723525761, 14416161921, 40217718093777, 324333614248111,
    6365, 12004464578401105, 100165, 3015, 48015871598503243, 3015,
    3015, 258285, 3015, 100165, 258285, 1299321285462709,
    3015, 3015, 6365, 13226321076310461, 23345671664791107, 13226321074246077,
    14646565513, 194769, 244845222299, 3065049, 92259, 244845342237,
    92259, 92259, 7903521, 92259, 3065049, 7903521,
    14646445575, 92259, 92259, 194769, 202337760097, 87167515923,
    202337739783, 643737543755567, 643737279543505, 5826420605, 19888325115, 728302545,
    23037, 23037, 1047, 945, 1575, 48195,
    1575, 49455, 1575, 48195, 27405, 49455,
    772065, 945, 1575, 48195
  ]
def negativeCoefficients : Array ℕ := #[
    32981432045118028505646366720, 1296010174033096581905907712, 33950138946979583256241897472, 33241406185230506902570401792, 11320281263801609494003187712, 1460668744271518891799065133056,
    1923703210461778674251202560, 54063302202069534842827130798080, 15136506840212416410555514880, 1822455673069053480869560320, 54061065359722196824212354629632, 1822455673069053480869560320,
    1822455673069053480869560320, 78061851329791124097246167040, 1822455673069053480869560320, 15136506840212416410555514880, 78061851329791124097246167040, 1462905714261102528447083708416,
    1822455673069053480869560320, 1822455673069053480869560320, 1923703210461778674251202560, 14891513667688582437321691889664, 52569779105133588243617767489536, 14891513665364292684034288386048,
    33772680697141431084699877376, 1839541195004075857252712448, 1129149288355044001744783671296, 14474284665953123192593711104, 1742723237372282391081517056, 1129149841471441679888834101248,
    1742723237372282391081517056, 1742723237372282391081517056, 74646645334112762417991647232, 1742723237372282391081517056, 14474284665953123192593711104, 74646645334112762417991647232,
    33772404138942592012674662400, 1742723237372282391081517056, 1742723237372282391081517056, 1839541195004075857252712448, 933118219239249934933911666688, 3215913715545166452329740763136,
    933118125557460156599953784832, 1449568081090984952692385775616, 1449567486138312967697192714240, 53739244883111485160386723840, 183437421725567543309940817920, 53739242623385336130966650880,
    222800192851697698381649412096, 222800192851697698381649412096, 40503850660368535869355720704, 71402181220989035631083520, 1904058165893040950162227200, 1820755621135220408592629760,
    59501817684157529692569600, 1868357075282546432346685440, 59501817684157529692569600, 1820755621135220408592629760, 1035331627704341016650711040, 1868357075282546432346685440,
    29167791028774021055297617920, 1142434899535824570097336320, 1904058165893040950162227200, 1820755621135220408592629760
  ]
def negativeScales : Array ℕ := #[
    32, 30, 33, 33, 45, 48,
    12, 53, 16, 11, 55, 11,
    11, 17, 11, 16, 17, 50,
    11, 11, 12, 53, 54, 53,
    33, 17, 37, 21, 16, 37,
    16, 16, 22, 16, 21, 22,
    33, 16, 16, 17, 37, 36,
    37, 49, 49, 32, 34, 29,
    14, 14, 10, 9, 10, 15,
    10, 15, 10, 15, 14, 15,
    19, 9, 10, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32735640698585082, 30066135605775057, 33777404136218831, 33746968069656678, 45192896460674134, 48204471882268986,
    12635944798803559, 53414420576300782, 16612018959551099, 11557942286789136, 55414360884273259, 11557942286789136,
    11557942286789136, 17978604352023330, 11557942286789136, 16612018959551099, 17978604352023330, 50206679635952820,
    11557942286789136, 11557942286789136, 12635944798803559, 53554261347537111, 54374004614318008, 53554261347311933,
    33769843354599189, 17571404546596521, 37833079089810405, 21547478707349761, 16493402034592954, 37833079796517761,
    16493402034592954, 16493402034592954, 22914064088673542, 16493402034592954, 21547478707349761, 22914064088673542,
    33769831540589454, 16493402034592954, 16493402034592954, 17571404546596521, 37557974623279282, 36343071545480675,
    37557974478437763, 49193465939899986, 49193465347768125, 32439962706313294, 34211202734345107, 29439962645648210,
    14491665233182158, 14491665233182158, 10032045726930809, 9884170522387776, 10621136113284685, 15556595861081553,
    10621136113284685, 15593828767283669, 10621136113284685, 15556595861081553, 14742151514425259, 15593828767283669,
    19558362787255829, 9884170522387776, 10621136113284685, 15556595861081553
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
noncomputable def negativeCeiling : ℝ := 131529389987 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 32981432045118028505646366720, coefficient := (-32981432045118028505646366720) }, { argument := 1296010174033096581905907712, coefficient := (-1296010174033096581905907712) }, { argument := 33950138946979583256241897472, coefficient := (-33950138946979583256241897472) }, { argument := 33241406185230506902570401792, coefficient := (-33241406185230506902570401792) }, { argument := 11320281263801609494003187712, coefficient := (-11320281263801609494003187712) }, { argument := 1460668744271518891799065133056, coefficient := (-1460668744271518891799065133056) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 54063302202069534842827130798080, coefficient := (-54063302202069534842827130798080) }, { argument := 15136506840212416410555514880, coefficient := (-15136506840212416410555514880) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 54061065359722196824212354629632, coefficient := (-54061065359722196824212354629632) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 78061851329791124097246167040, coefficient := (-78061851329791124097246167040) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 15136506840212416410555514880, coefficient := (-15136506840212416410555514880) }, { argument := 78061851329791124097246167040, coefficient := (-78061851329791124097246167040) }, { argument := 1462905714261102528447083708416, coefficient := (-1462905714261102528447083708416) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 14891513667688582437321691889664, coefficient := (-14891513667688582437321691889664) }, { argument := 52569779105133588243617767489536, coefficient := (-52569779105133588243617767489536) }, { argument := 14891513665364292684034288386048, coefficient := (-14891513665364292684034288386048) }, { argument := 33772680697141431084699877376, coefficient := (-33772680697141431084699877376) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1129149288355044001744783671296, coefficient := (-1129149288355044001744783671296) }, { argument := 14474284665953123192593711104, coefficient := (-14474284665953123192593711104) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1129149841471441679888834101248, coefficient := (-1129149841471441679888834101248) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 74646645334112762417991647232, coefficient := (-74646645334112762417991647232) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 14474284665953123192593711104, coefficient := (-14474284665953123192593711104) }, { argument := 74646645334112762417991647232, coefficient := (-74646645334112762417991647232) }, { argument := 33772404138942592012674662400, coefficient := (-33772404138942592012674662400) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 933118219239249934933911666688, coefficient := (-933118219239249934933911666688) }, { argument := 3215913715545166452329740763136, coefficient := (-3215913715545166452329740763136) }, { argument := 933118125557460156599953784832, coefficient := (-933118125557460156599953784832) }, { argument := 1449568081090984952692385775616, coefficient := (-1449568081090984952692385775616) }, { argument := 1449567486138312967697192714240, coefficient := (-1449567486138312967697192714240) }, { argument := 53739244883111485160386723840, coefficient := (-53739244883111485160386723840) }, { argument := 183437421725567543309940817920, coefficient := (-183437421725567543309940817920) }, { argument := 53739242623385336130966650880, coefficient := (-53739242623385336130966650880) }, { argument := 222800192851697698381649412096, coefficient := (-222800192851697698381649412096) }, { argument := 222800192851697698381649412096, coefficient := (-222800192851697698381649412096) }, { argument := 40503850660368535869355720704, coefficient := (-40503850660368535869355720704) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }] }

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


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-185169691026040292753690771587072)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1575, 945, 1575, 24255, 27405, 945,
    1118890349, 6365, 18830727751, 100165, 3015, 18830736977,
    3015, 3015, 258285, 3015, 100165, 258285,
    1118881123, 3015, 3015, 6365, 945, 1575,
    48195, 1575, 49455, 1575, 48195, 27405,
    49455, 772065, 945, 1575, 48195, 1575,
    945, 1575, 24255, 27405, 945, 7121357391,
    3819, 121022275821, 60099, 1809, 121022335131, 1809,
    1809, 154971, 1809, 60099, 154971, 7121298081,
    1809, 1809, 3819, 11398368829, 2432128599, 11398368339,
    1118890349, 6365, 18830727751, 100165
  ]
def negativeCoefficients : Array ℕ := #[
    59501817684157529692569600, 1142434899535824570097336320, 59501817684157529692569600, 1832655984672051914531143680, 1035331627704341016650711040, 71402181220989035631083520,
    1289992744659160120766234624, 60115725326930583570350080, 43420701943049655391147261952, 473015838756638012829859840, 56951739783407921277173760, 43420723216757258396687663104,
    56951739783407921277173760, 56951739783407921277173760, 2439432854055972628038942720, 56951739783407921277173760, 473015838756638012829859840, 2439432854055972628038942720,
    1289982107805358617996034048, 56951739783407921277173760, 56951739783407921277173760, 60115725326930583570350080, 71402181220989035631083520, 1904058165893040950162227200,
    1820755621135220408592629760, 59501817684157529692569600, 1868357075282546432346685440, 59501817684157529692569600, 1820755621135220408592629760, 1035331627704341016650711040,
    1868357075282546432346685440, 29167791028774021055297617920, 1142434899535824570097336320, 1904058165893040950162227200, 1820755621135220408592629760, 59501817684157529692569600,
    1142434899535824570097336320, 59501817684157529692569600, 1832655984672051914531143680, 1035331627704341016650711040, 71402181220989035631083520, 32841464312299241046974398464,
    1154221926277067204550721536, 1116233474643937255156894138368, 9081904104127449846333308928, 1093473403841432088521736192, 1116234021682132761013647310848, 1093473403841432088521736192,
    1093473403841432088521736192, 46837110797874674458347700224, 1093473403841432088521736192, 9081904104127449846333308928, 46837110797874674458347700224, 32841190793201488118597812224,
    1093473403841432088521736192, 1093473403841432088521736192, 1154221926277067204550721536, 52565698161577857884845244416, 179459415280411058018961063936, 52565695901851708855425171456,
    1289992744659160120766234624, 60115725326930583570350080, 43420701943049655391147261952, 473015838756638012829859840
  ]
def negativeScales : Array ℕ := #[
    10, 9, 10, 14, 14, 9,
    30, 12, 34, 16, 11, 34,
    11, 11, 17, 11, 16, 17,
    30, 11, 11, 12, 9, 10,
    15, 10, 15, 10, 15, 14,
    15, 19, 9, 10, 15, 10,
    9, 10, 14, 14, 9, 32,
    11, 36, 15, 10, 36, 10,
    10, 17, 10, 15, 17, 32,
    10, 10, 11, 33, 31, 33,
    30, 12, 34, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10621136113284685, 9884170522387776, 10621136113284685, 14565994559084324, 14742151514425259, 9884170522387776,
    30059421513441666, 12635944798803559, 34132369705728063, 16612018959551099, 11557942286789136, 34132370412567510,
    11557942286789136, 11557942286789136, 17978604352023330, 11557942286789136, 16612018959551099, 17978604352023330,
    30059409617406156, 11557942286789136, 11557942286789136, 12635944798803559, 9884170522387776, 10621136113284685,
    15556595861081553, 10621136113284685, 15593828767283669, 10621136113284685, 15556595861081553, 14742151514425259,
    15593828767283669, 19558362787255829, 9884170522387776, 10621136113284685, 15556595861081553, 10621136113284685,
    9884170522387776, 10621136113284685, 14565994559084324, 14742151514425259, 9884170522387776, 32729505111418701,
    11898979208910875, 36816481664547161, 15875053368150273, 10820976693606152, 36816482371575870, 10820976693606152,
    10820976693606152, 17241638741093964, 10820976693606152, 15875053368150273, 17241638741093964, 32729493095928568,
    10820976693606152, 10820976693606152, 11898979208910875, 33408108330220798, 31179572367403674, 33408108268201347,
    30059421513441666, 12635944798803559, 34132369705728063, 16612018959551099
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
noncomputable def negativeCeiling : ℝ := 304008369 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1289992744659160120766234624, coefficient := (-1289992744659160120766234624) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 43420701943049655391147261952, coefficient := (-43420701943049655391147261952) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 43420723216757258396687663104, coefficient := (-43420723216757258396687663104) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 1289982107805358617996034048, coefficient := (-1289982107805358617996034048) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 32841464312299241046974398464, coefficient := (-32841464312299241046974398464) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 1116233474643937255156894138368, coefficient := (-1116233474643937255156894138368) }, { argument := 9081904104127449846333308928, coefficient := (-9081904104127449846333308928) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1116234021682132761013647310848, coefficient := (-1116234021682132761013647310848) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 46837110797874674458347700224, coefficient := (-46837110797874674458347700224) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 9081904104127449846333308928, coefficient := (-9081904104127449846333308928) }, { argument := 46837110797874674458347700224, coefficient := (-46837110797874674458347700224) }, { argument := 32841190793201488118597812224, coefficient := (-32841190793201488118597812224) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 52565698161577857884845244416, coefficient := (-52565698161577857884845244416) }, { argument := 179459415280411058018961063936, coefficient := (-179459415280411058018961063936) }, { argument := 52565695901851708855425171456, coefficient := (-52565695901851708855425171456) }, { argument := 1289992744659160120766234624, coefficient := (-1289992744659160120766234624) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 43420701943049655391147261952, coefficient := (-43420701943049655391147261952) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
