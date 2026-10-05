import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-876808020098728245739736115707904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15435912655, 376759651, 52612865123, 525863146471, 1051726035919, 52612865123,
    211842495, 1543383015, 423685275, 1101844015, 7522562535, 840707007,
    68165433, 14610124473, 26425466193, 7522562535, 14610124473, 431714409,
    431714409, 840707007, 840707007, 26425466193, 840707007, 1101844015,
    68165433, 2556139161, 17062844115, 3765559105, 177104521735, 146710095,
    244516825, 7482214845, 244516825, 146710095, 119862147615, 7677828305,
    17062844115, 7482214845, 244516825, 7677828305, 244516825, 7482214845,
    244516825, 2556139161, 15037960535, 3797668875, 19080776845, 42859405875,
    3797668875, 38161545955, 3797668875, 3797668875, 157440501075, 976543425,
    42859405875, 157440501075, 15037960535, 3797668875, 976543425, 3797668875,
    367160679, 15042640995, 309739626765, 15042640995
  ]
def negativeCoefficients : Array ℕ := #[
    142371165145459760291895050240, 868748607412141117776330752, 60658503619286263090588418048, 2425115720186544290439085686784, 2425115127531856533307825061888, 60658503619286263090588418048,
    15631217156804381278658887680, 56940782970830460014800404480, 15631227671448503293103308800, 2540679319231698537052897280, 17345848232702593932271288320, 1938538374887918065799921664,
    2514860594449191004280979456, 33688653379808954494847287296, 60932976486341857041224564736, 17345848232702593932271288320, 33688653379808954494847287296, 1990931303938942878389108736,
    1990931303938942878389108736, 1938538374887918065799921664, 1938538374887918065799921664, 60932976486341857041224564736, 1938538374887918065799921664, 2540679319231698537052897280,
    2514860594449191004280979456, 5894055614969206928176054272, 157376959279503074505177169920, 138924610208723586426192527360, 816750446685568931563244093440, 86602354415827690239704432640,
    4510539292491025533317939200, 138022502350225381319528939520, 144337257359712817066174054400, 86602354415827690239704432640, 2211066361179100716432453795840, 141630933784218201746183290880,
    157376959279503074505177169920, 138022502350225381319528939520, 4510539292491025533317939200, 141630933784218201746183290880, 4510539292491025533317939200, 138022502350225381319528939520,
    144337257359712817066174054400, 5894055614969206928176054272, 17337588086230585515872092160, 17513656453454367490572288000, 87994551796819546432476282880, 197654122831842147393601536000,
    17513656453454367490572288000, 87994533961123870164553564160, 17513656453454367490572288000, 17513656453454367490572288000, 726066157541779635109153996800, 18014046637838777990302924800,
    197654122831842147393601536000, 726066157541779635109153996800, 17337588086230585515872092160, 17513656453454367490572288000, 18014046637838777990302924800, 17513656453454367490572288000,
    846614884930303127514513408, 138743874313728301430955048960, 1428421906105068041638835650560, 138743874313728301430955048960
  ]
def negativeScales : Array ℕ := #[
    33, 28, 35, 38, 39, 35,
    27, 30, 28, 30, 32, 29,
    26, 33, 34, 32, 33, 28,
    28, 29, 29, 34, 29, 30,
    26, 31, 33, 31, 37, 27,
    27, 32, 27, 27, 36, 32,
    33, 32, 27, 32, 27, 32,
    27, 31, 33, 31, 34, 35,
    31, 35, 31, 31, 37, 29,
    35, 37, 33, 31, 29, 31,
    28, 33, 38, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33845571735906965, 28489069227183653, 35614696565504733, 38935896445400177, 39935896092831351, 35614696565504733,
    27658416777994287, 30523448988008537, 28658417748451014, 30037272854016694, 32808577049475346, 29647027856630440,
    26022536991702896, 33766249418629144, 34621209872465021, 32808577049475346, 33766249418629144, 28685502004476598,
    28685502004476598, 29647027856630440, 29647027856630440, 34621209872465021, 29647027856630440, 30037272854016694,
    26022536991702896, 31251319235427438, 33990139110973531, 31810216944943606, 37365810090415372, 27128392904175353,
    27865358500657122, 32800818246803744, 27865358500657122, 27128392904175353, 36802585173001970, 32838051153722268,
    33990139110973531, 32800818246803744, 27865358500657122, 32838051153722268, 27865358500657122, 32800818246803744,
    27865358500657122, 31251319235427438, 33807889870001471, 31822466975016500, 34151400858561593, 35318892800121588,
    31822466975016500, 35151400566140394, 31822466975016500, 31822466975016500, 37196015761123867, 29863108960719387,
    35318892800121588, 37196015761123867, 33807889870001471, 31822466975016500, 29863108960719387, 31822466975016500,
    28451836320984541, 33808338828881668, 38172265010823274, 33808338828881668
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
noncomputable def negativeCeiling : ℝ := 1247747529 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 142371165145459760291895050240, coefficient := (-142371165145459760291895050240) }, { argument := 868748607412141117776330752, coefficient := (-868748607412141117776330752) }, { argument := 60658503619286263090588418048, coefficient := (-60658503619286263090588418048) }, { argument := 2425115720186544290439085686784, coefficient := (-2425115720186544290439085686784) }, { argument := 2425115127531856533307825061888, coefficient := (-2425115127531856533307825061888) }, { argument := 60658503619286263090588418048, coefficient := (-60658503619286263090588418048) }, { argument := 15631217156804381278658887680, coefficient := (-15631217156804381278658887680) }, { argument := 56940782970830460014800404480, coefficient := (-56940782970830460014800404480) }, { argument := 15631227671448503293103308800, coefficient := (-15631227671448503293103308800) }, { argument := 2540679319231698537052897280, coefficient := (-2540679319231698537052897280) }, { argument := 17345848232702593932271288320, coefficient := (-17345848232702593932271288320) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 2514860594449191004280979456, coefficient := (-2514860594449191004280979456) }, { argument := 33688653379808954494847287296, coefficient := (-33688653379808954494847287296) }, { argument := 60932976486341857041224564736, coefficient := (-60932976486341857041224564736) }, { argument := 17345848232702593932271288320, coefficient := (-17345848232702593932271288320) }, { argument := 33688653379808954494847287296, coefficient := (-33688653379808954494847287296) }, { argument := 1990931303938942878389108736, coefficient := (-1990931303938942878389108736) }, { argument := 1990931303938942878389108736, coefficient := (-1990931303938942878389108736) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 60932976486341857041224564736, coefficient := (-60932976486341857041224564736) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 2540679319231698537052897280, coefficient := (-2540679319231698537052897280) }, { argument := 2514860594449191004280979456, coefficient := (-2514860594449191004280979456) }, { argument := 5894055614969206928176054272, coefficient := (-5894055614969206928176054272) }, { argument := 157376959279503074505177169920, coefficient := (-157376959279503074505177169920) }, { argument := 138924610208723586426192527360, coefficient := (-138924610208723586426192527360) }, { argument := 816750446685568931563244093440, coefficient := (-816750446685568931563244093440) }, { argument := 86602354415827690239704432640, coefficient := (-86602354415827690239704432640) }, { argument := 4510539292491025533317939200, coefficient := (-4510539292491025533317939200) }, { argument := 138022502350225381319528939520, coefficient := (-138022502350225381319528939520) }, { argument := 144337257359712817066174054400, coefficient := (-144337257359712817066174054400) }, { argument := 86602354415827690239704432640, coefficient := (-86602354415827690239704432640) }, { argument := 2211066361179100716432453795840, coefficient := (-2211066361179100716432453795840) }, { argument := 141630933784218201746183290880, coefficient := (-141630933784218201746183290880) }, { argument := 157376959279503074505177169920, coefficient := (-157376959279503074505177169920) }, { argument := 138022502350225381319528939520, coefficient := (-138022502350225381319528939520) }, { argument := 4510539292491025533317939200, coefficient := (-4510539292491025533317939200) }, { argument := 141630933784218201746183290880, coefficient := (-141630933784218201746183290880) }, { argument := 4510539292491025533317939200, coefficient := (-4510539292491025533317939200) }, { argument := 138022502350225381319528939520, coefficient := (-138022502350225381319528939520) }, { argument := 144337257359712817066174054400, coefficient := (-144337257359712817066174054400) }, { argument := 5894055614969206928176054272, coefficient := (-5894055614969206928176054272) }, { argument := 17337588086230585515872092160, coefficient := (-17337588086230585515872092160) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 87994551796819546432476282880, coefficient := (-87994551796819546432476282880) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 87994533961123870164553564160, coefficient := (-87994533961123870164553564160) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 17337588086230585515872092160, coefficient := (-17337588086230585515872092160) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 846614884930303127514513408, coefficient := (-846614884930303127514513408) }, { argument := 138743874313728301430955048960, coefficient := (-138743874313728301430955048960) }, { argument := 1428421906105068041638835650560, coefficient := (-1428421906105068041638835650560) }, { argument := 138743874313728301430955048960, coefficient := (-138743874313728301430955048960) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-456213827270728031713029395578880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    367160679, 29088626203, 290739469631, 581478797159, 29088626203, 626607801,
    4565164497, 1253216445, 859539499, 8591057423, 17182110647, 859539499,
    1398160467, 10186327899, 2796322815, 19147765, 3797668875, 3797668875,
    19147765, 11998715, 491589575, 10122210025, 491589575, 11998715,
    4923711, 976543425, 976543425, 4923711, 376759651, 15435912655,
    317837394785, 15435912655, 376759651, 859539499, 8591057423, 17182110647,
    859539499, 11998715, 491589575, 10122210025, 491589575, 11998715,
    1673840077, 16729953929, 33459899681, 1673840077, 69127551, 503630247,
    138255195, 19147765, 3797668875, 3797668875, 19147765, 367160679,
    15042640995, 309739626765, 15042640995, 367160679, 1673840077, 16729953929,
    33459899681, 1673840077, 11998715, 491589575
  ]
def negativeCoefficients : Array ℕ := #[
    846614884930303127514513408, 33536902688908914159284912128, 1340799147102276851893664743424, 1340798819435067713600113082368, 33536902688908914159284912128, 11558873739636924050797756416,
    42106210565271998063576088576, 11558881514939551119373762560, 1981963144912190883441410048, 79238518802311851278319222784, 79238499437842259901717413888, 1981963144912190883441410048,
    12895754154363614554893582336, 46976145950935129512210333696, 12895762828945015216810229760, 88303480134633293149634560, 17513656453454367490572288000, 17513656453454367490572288000,
    88303480134633293149634560, 27667153102297487827271680, 4534113539664323576175001600, 46680454447878040576432537600, 4534113539664323576175001600, 27667153102297487827271680,
    90826436709908530096766976, 18014046637838777990302924800, 18014046637838777990302924800, 90826436709908530096766976, 868748607412141117776330752, 142371165145459760291895050240,
    1465766269663370474099981680640, 142371165145459760291895050240, 868748607412141117776330752, 1981963144912190883441410048, 79238518802311851278319222784, 79238499437842259901717413888,
    1981963144912190883441410048, 27667153102297487827271680, 4534113539664323576175001600, 46680454447878040576432537600, 4534113539664323576175001600, 27667153102297487827271680,
    1929806220046080597035057152, 77153294623303644665731874816, 77153275768425358325356429312, 1929806220046080597035057152, 637589120869652394261086208, 2322584568547031921656332288,
    637589549756452108008161280, 88303480134633293149634560, 17513656453454367490572288000, 17513656453454367490572288000, 88303480134633293149634560, 846614884930303127514513408,
    138743874313728301430955048960, 1428421906105068041638835650560, 138743874313728301430955048960, 846614884930303127514513408, 1929806220046080597035057152, 77153294623303644665731874816,
    77153275768425358325356429312, 1929806220046080597035057152, 885348899273519610472693760, 145091633269258354437600051200
  ]
def negativeScales : Array ℕ := #[
    28, 34, 38, 39, 34, 29,
    32, 30, 29, 33, 34, 29,
    30, 33, 31, 24, 31, 31,
    24, 23, 28, 33, 28, 23,
    22, 29, 29, 22, 28, 33,
    38, 33, 28, 29, 33, 34,
    29, 23, 28, 33, 28, 23,
    30, 33, 34, 30, 26, 28,
    27, 24, 31, 31, 24, 28,
    33, 38, 33, 28, 30, 33,
    34, 30, 23, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28451836320984541, 34759736111628806, 38080935983056195, 39080935630487418, 34759736111628806, 29222987489857909,
    32088019699897932, 30222988460314636, 29678988697510454, 33000188569171833, 34000188216603056, 29678988697510454,
    30380882802439025, 33245915012479045, 31380883772895751, 24190672669333438, 31822466975016500, 31822466975016500,
    24190672669333438, 23516376573179666, 28872879082975162, 33236805263017984, 28872879082975162, 23516376573179666,
    22231314653830784, 29863108960719387, 29863108960719387, 22231314653830784, 28489069227183653, 33845571735906965,
    38209497917022249, 33845571735906965, 28489069227183653, 29678988697510454, 33000188569171833, 34000188216603056,
    29678988697510454, 23516376573179666, 28872879082975162, 33236805263017984, 28872879082975162, 23516376573179666,
    30640514549668721, 33961714434044193, 34961714081475342, 30640514549668721, 26042757480023858, 28907789695082770,
    27042758450480585, 24190672669333438, 31822466975016500, 31822466975016500, 24190672669333438, 28451836320984541,
    33808338828881668, 38172265010823274, 33808338828881668, 28451836320984541, 30640514549668721, 33961714434044193,
    34961714081475342, 30640514549668721, 23516376573179666, 28872879082975162
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
noncomputable def negativeCeiling : ℝ := 3284221893 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 846614884930303127514513408, coefficient := (-846614884930303127514513408) }, { argument := 33536902688908914159284912128, coefficient := (-33536902688908914159284912128) }, { argument := 1340799147102276851893664743424, coefficient := (-1340799147102276851893664743424) }, { argument := 1340798819435067713600113082368, coefficient := (-1340798819435067713600113082368) }, { argument := 33536902688908914159284912128, coefficient := (-33536902688908914159284912128) }, { argument := 11558873739636924050797756416, coefficient := (-11558873739636924050797756416) }, { argument := 42106210565271998063576088576, coefficient := (-42106210565271998063576088576) }, { argument := 11558881514939551119373762560, coefficient := (-11558881514939551119373762560) }, { argument := 1981963144912190883441410048, coefficient := (-1981963144912190883441410048) }, { argument := 79238518802311851278319222784, coefficient := (-79238518802311851278319222784) }, { argument := 79238499437842259901717413888, coefficient := (-79238499437842259901717413888) }, { argument := 1981963144912190883441410048, coefficient := (-1981963144912190883441410048) }, { argument := 12895754154363614554893582336, coefficient := (-12895754154363614554893582336) }, { argument := 46976145950935129512210333696, coefficient := (-46976145950935129512210333696) }, { argument := 12895762828945015216810229760, coefficient := (-12895762828945015216810229760) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 27667153102297487827271680, coefficient := (-27667153102297487827271680) }, { argument := 4534113539664323576175001600, coefficient := (-4534113539664323576175001600) }, { argument := 46680454447878040576432537600, coefficient := (-46680454447878040576432537600) }, { argument := 4534113539664323576175001600, coefficient := (-4534113539664323576175001600) }, { argument := 27667153102297487827271680, coefficient := (-27667153102297487827271680) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 868748607412141117776330752, coefficient := (-868748607412141117776330752) }, { argument := 142371165145459760291895050240, coefficient := (-142371165145459760291895050240) }, { argument := 1465766269663370474099981680640, coefficient := (-1465766269663370474099981680640) }, { argument := 142371165145459760291895050240, coefficient := (-142371165145459760291895050240) }, { argument := 868748607412141117776330752, coefficient := (-868748607412141117776330752) }, { argument := 1981963144912190883441410048, coefficient := (-1981963144912190883441410048) }, { argument := 79238518802311851278319222784, coefficient := (-79238518802311851278319222784) }, { argument := 79238499437842259901717413888, coefficient := (-79238499437842259901717413888) }, { argument := 1981963144912190883441410048, coefficient := (-1981963144912190883441410048) }, { argument := 27667153102297487827271680, coefficient := (-27667153102297487827271680) }, { argument := 4534113539664323576175001600, coefficient := (-4534113539664323576175001600) }, { argument := 46680454447878040576432537600, coefficient := (-46680454447878040576432537600) }, { argument := 4534113539664323576175001600, coefficient := (-4534113539664323576175001600) }, { argument := 27667153102297487827271680, coefficient := (-27667153102297487827271680) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 77153294623303644665731874816, coefficient := (-77153294623303644665731874816) }, { argument := 77153275768425358325356429312, coefficient := (-77153275768425358325356429312) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 846614884930303127514513408, coefficient := (-846614884930303127514513408) }, { argument := 138743874313728301430955048960, coefficient := (-138743874313728301430955048960) }, { argument := 1428421906105068041638835650560, coefficient := (-1428421906105068041638835650560) }, { argument := 138743874313728301430955048960, coefficient := (-138743874313728301430955048960) }, { argument := 846614884930303127514513408, coefficient := (-846614884930303127514513408) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 77153294623303644665731874816, coefficient := (-77153294623303644665731874816) }, { argument := 77153275768425358325356429312, coefficient := (-77153275768425358325356429312) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 885348899273519610472693760, coefficient := (-885348899273519610472693760) }, { argument := 145091633269258354437600051200, coefficient := (-145091633269258354437600051200) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
