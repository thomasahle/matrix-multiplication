import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3175107678506065235621198688157696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1395931485, 2840921265, 138255195, 423685275, 138255195, 21364131171,
    19152382155, 16805650971, 1362620349, 292054961469, 528242488629, 19152382155,
    292054961469, 8629928877, 8629928877, 16805650971, 16805650971, 528242488629,
    16805650971, 21364131171, 1362620349, 24178994435, 22024237265, 77535777935,
    20191791575, 3020874465, 5034790775, 154064597715, 5034790775, 3020874465,
    2468054437905, 158092430335, 22024237265, 154064597715, 5034790775, 158092430335,
    5034790775, 154064597715, 5034790775, 24178994435, 19147765, 3797668875,
    3797668875, 19147765, 7199229, 294953745, 6073326015, 294953745,
    7199229, 15037960535, 3797668875, 19080776845, 42859405875, 3797668875,
    38161545955, 3797668875, 3797668875, 157440501075, 976543425, 42859405875,
    157440501075, 15037960535, 3797668875, 976543425
  ]
def negativeCoefficients : Array ℕ := #[
    12875195424114161923003514880, 13101436877253548154877378560, 637589549756452108008161280, 15631227671448503293103308800, 637589549756452108008161280, 98524665017149438319954755584,
    88324773003791705255832453120, 77502385613531355421851254784, 100543635390527163790509735936, 1346865782418936798277036670976, 2436088499149647739340892143616, 88324773003791705255832453120,
    1346865782418936798277036670976, 79597044684167338000820207616, 79597044684167338000820207616, 77502385613531355421851254784, 77502385613531355421851254784, 2436088499149647739340892143616,
    77502385613531355421851254784, 98524665017149438319954755584, 100543635390527163790509735936, 55752965287761559791201157120, 812550936492223626975096340480, 1430282652122921065786596392960,
    93118202893427425829244108800, 891604770154548196853982167040, 46437748445549385252811571200, 1420995102433811188736034078720, 1486007950257580328089970278400, 891604770154548196853982167040,
    22763784288008308650928232202240, 1458145301190250696938283335680, 812550936492223626975096340480, 1420995102433811188736034078720, 46437748445549385252811571200, 1458145301190250696938283335680,
    46437748445549385252811571200, 1420995102433811188736034078720, 1486007950257580328089970278400, 55752965287761559791201157120, 88303480134633293149634560, 17513656453454367490572288000,
    17513656453454367490572288000, 88303480134633293149634560, 531209339564111766283616256, 87054979961555012662560030720, 896264725399258379067504721920, 87054979961555012662560030720,
    531209339564111766283616256, 17337588086230585515872092160, 17513656453454367490572288000, 87994551796819546432476282880, 197654122831842147393601536000, 17513656453454367490572288000,
    87994533961123870164553564160, 17513656453454367490572288000, 17513656453454367490572288000, 726066157541779635109153996800, 18014046637838777990302924800, 197654122831842147393601536000,
    726066157541779635109153996800, 17337588086230585515872092160, 17513656453454367490572288000, 18014046637838777990302924800
  ]
def negativeScales : Array ℕ := #[
    30, 31, 27, 28, 27, 34,
    34, 33, 30, 38, 38, 34,
    38, 33, 33, 33, 33, 38,
    33, 34, 30, 34, 34, 36,
    34, 31, 32, 37, 32, 31,
    41, 37, 34, 37, 32, 37,
    32, 37, 32, 34, 24, 31,
    31, 24, 22, 28, 32, 28,
    22, 33, 31, 34, 35, 31,
    35, 31, 31, 37, 29, 35,
    37, 33, 31, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30378580987026330, 31403711702350017, 27042758450480585, 28658417748451014, 27042758450480585, 34314471596069252,
    34156804793215402, 33968227389882102, 30343736510839302, 38087448937446092, 38942409400756147, 34156804793215402,
    38087448937446092, 33006701523561730, 33006701523561730, 33968227389882102, 33968227389882102, 38942409400756147,
    33968227389882102, 34314471596069252, 30343736510839302, 34493035195371338, 34358373006019041, 36174143126855729,
    34233049872504732, 31492319086882193, 32229284681048190, 37164744428853479, 32229284681048190, 31492319086882193,
    41166511355027667, 37201977335052454, 34358373006019041, 37164744428853479, 32229284681048190, 37201977335052454,
    32229284681048190, 37164744428853479, 32229284681048190, 34493035195371338, 24190672669333438, 31822466975016500,
    31822466975016500, 24190672669333438, 22779410979435057, 28135913486145148, 32499839668852048, 28135913486145148,
    22779410979435057, 33807889870001471, 31822466975016500, 34151400858561593, 35318892800121588, 31822466975016500,
    35151400566140394, 31822466975016500, 31822466975016500, 37196015761123867, 29863108960719387, 35318892800121588,
    37196015761123867, 33807889870001471, 31822466975016500, 29863108960719387
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
noncomputable def negativeCeiling : ℝ := 11541436563 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12875195424114161923003514880, coefficient := (-12875195424114161923003514880) }, { argument := 13101436877253548154877378560, coefficient := (-13101436877253548154877378560) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 15631227671448503293103308800, coefficient := (-15631227671448503293103308800) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 98524665017149438319954755584, coefficient := (-98524665017149438319954755584) }, { argument := 88324773003791705255832453120, coefficient := (-88324773003791705255832453120) }, { argument := 77502385613531355421851254784, coefficient := (-77502385613531355421851254784) }, { argument := 100543635390527163790509735936, coefficient := (-100543635390527163790509735936) }, { argument := 1346865782418936798277036670976, coefficient := (-1346865782418936798277036670976) }, { argument := 2436088499149647739340892143616, coefficient := (-2436088499149647739340892143616) }, { argument := 88324773003791705255832453120, coefficient := (-88324773003791705255832453120) }, { argument := 1346865782418936798277036670976, coefficient := (-1346865782418936798277036670976) }, { argument := 79597044684167338000820207616, coefficient := (-79597044684167338000820207616) }, { argument := 79597044684167338000820207616, coefficient := (-79597044684167338000820207616) }, { argument := 77502385613531355421851254784, coefficient := (-77502385613531355421851254784) }, { argument := 77502385613531355421851254784, coefficient := (-77502385613531355421851254784) }, { argument := 2436088499149647739340892143616, coefficient := (-2436088499149647739340892143616) }, { argument := 77502385613531355421851254784, coefficient := (-77502385613531355421851254784) }, { argument := 98524665017149438319954755584, coefficient := (-98524665017149438319954755584) }, { argument := 100543635390527163790509735936, coefficient := (-100543635390527163790509735936) }, { argument := 55752965287761559791201157120, coefficient := (-55752965287761559791201157120) }, { argument := 812550936492223626975096340480, coefficient := (-812550936492223626975096340480) }, { argument := 1430282652122921065786596392960, coefficient := (-1430282652122921065786596392960) }, { argument := 93118202893427425829244108800, coefficient := (-93118202893427425829244108800) }, { argument := 891604770154548196853982167040, coefficient := (-891604770154548196853982167040) }, { argument := 46437748445549385252811571200, coefficient := (-46437748445549385252811571200) }, { argument := 1420995102433811188736034078720, coefficient := (-1420995102433811188736034078720) }, { argument := 1486007950257580328089970278400, coefficient := (-1486007950257580328089970278400) }, { argument := 891604770154548196853982167040, coefficient := (-891604770154548196853982167040) }, { argument := 22763784288008308650928232202240, coefficient := (-22763784288008308650928232202240) }, { argument := 1458145301190250696938283335680, coefficient := (-1458145301190250696938283335680) }, { argument := 812550936492223626975096340480, coefficient := (-812550936492223626975096340480) }, { argument := 1420995102433811188736034078720, coefficient := (-1420995102433811188736034078720) }, { argument := 46437748445549385252811571200, coefficient := (-46437748445549385252811571200) }, { argument := 1458145301190250696938283335680, coefficient := (-1458145301190250696938283335680) }, { argument := 46437748445549385252811571200, coefficient := (-46437748445549385252811571200) }, { argument := 1420995102433811188736034078720, coefficient := (-1420995102433811188736034078720) }, { argument := 1486007950257580328089970278400, coefficient := (-1486007950257580328089970278400) }, { argument := 55752965287761559791201157120, coefficient := (-55752965287761559791201157120) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 531209339564111766283616256, coefficient := (-531209339564111766283616256) }, { argument := 87054979961555012662560030720, coefficient := (-87054979961555012662560030720) }, { argument := 896264725399258379067504721920, coefficient := (-896264725399258379067504721920) }, { argument := 87054979961555012662560030720, coefficient := (-87054979961555012662560030720) }, { argument := 531209339564111766283616256, coefficient := (-531209339564111766283616256) }, { argument := 17337588086230585515872092160, coefficient := (-17337588086230585515872092160) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 87994551796819546432476282880, coefficient := (-87994551796819546432476282880) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 87994533961123870164553564160, coefficient := (-87994533961123870164553564160) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 17337588086230585515872092160, coefficient := (-17337588086230585515872092160) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }] }

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
def constantNumerator : ℤ := (-2505354628343634898361069942603776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3797668875, 11998715, 491589575, 10122210025, 491589575, 11998715,
    1673840077, 16729953929, 33459899681, 1673840077, 69127551, 503630247,
    138255195, 19147765, 3797668875, 3797668875, 19147765, 793811629,
    157440501075, 157440501075, 793811629, 367160679, 15042640995, 309739626765,
    15042640995, 367160679, 4923711, 976543425, 976543425, 4923711,
    11998715, 491589575, 10122210025, 491589575, 11998715, 135716763,
    1356482751, 2712964839, 135716763, 216096205, 42859405875, 42859405875,
    216096205, 7199229, 294953745, 6073326015, 294953745, 7199229,
    793811629, 157440501075, 157440501075, 793811629, 5881770093, 240977209665,
    4961907354255, 240977209665, 5881770093, 29088626203, 290739469631, 581478797159,
    29088626203, 376759651, 15435912655, 317837394785
  ]
def negativeCoefficients : Array ℕ := #[
    17513656453454367490572288000, 27667153102297487827271680, 4534113539664323576175001600, 46680454447878040576432537600, 4534113539664323576175001600, 27667153102297487827271680,
    1929806220046080597035057152, 77153294623303644665731874816, 77153275768425358325356429312, 1929806220046080597035057152, 637589120869652394261086208, 2322584568547031921656332288,
    637589549756452108008161280, 88303480134633293149634560, 17513656453454367490572288000, 17513656453454367490572288000, 88303480134633293149634560, 3660809990724368810289135616,
    726066157541779635109153996800, 726066157541779635109153996800, 3660809990724368810289135616, 846614884930303127514513408, 138743874313728301430955048960, 1428421906105068041638835650560,
    138743874313728301430955048960, 846614884930303127514513408, 90826436709908530096766976, 18014046637838777990302924800, 18014046637838777990302924800, 90826436709908530096766976,
    885348899273519610472693760, 145091633269258354437600051200, 1493774542332097298445841203200, 145091633269258354437600051200, 885348899273519610472693760, 2503532393573293747504939008,
    100090760592393917404192702464, 100090736132011275665327259648, 2503532393573293747504939008, 996567847233718594117304320, 197654122831842147393601536000, 197654122831842147393601536000,
    996567847233718594117304320, 531209339564111766283616256, 87054979961555012662560030720, 896264725399258379067504721920, 87054979961555012662560030720, 531209339564111766283616256,
    3660809990724368810289135616, 726066157541779635109153996800, 726066157541779635109153996800, 3660809990724368810289135616, 13562438450746228532928577536, 2222622457143451417040985784320,
    22882758770349815490567229931520, 2222622457143451417040985784320, 13562438450746228532928577536, 33536902688908914159284912128, 1340799147102276851893664743424, 1340798819435067713600113082368,
    33536902688908914159284912128, 868748607412141117776330752, 142371165145459760291895050240, 1465766269663370474099981680640
  ]
def negativeScales : Array ℕ := #[
    31, 23, 28, 33, 28, 23,
    30, 33, 34, 30, 26, 28,
    27, 24, 31, 31, 24, 29,
    37, 37, 29, 28, 33, 38,
    33, 28, 22, 29, 29, 22,
    23, 28, 33, 28, 23, 27,
    30, 31, 27, 27, 35, 35,
    27, 22, 28, 32, 28, 22,
    29, 37, 37, 29, 32, 37,
    42, 37, 32, 34, 38, 39,
    34, 28, 33, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31822466975016500, 23516376573179666, 28872879082975162, 33236805263017984, 28872879082975162, 23516376573179666,
    30640514549668721, 33961714434044193, 34961714081475342, 30640514549668721, 26042757480023858, 28907789695082770,
    27042758450480585, 24190672669333438, 31822466975016500, 31822466975016500, 24190672669333438, 29564221456457250,
    37196015761123867, 37196015761123867, 29564221456457250, 28451836320984541, 33808338828881668, 38172265010823274,
    33808338828881668, 28451836320984541, 22231314653830784, 29863108960719387, 29863108960719387, 22231314653830784,
    23516376573179666, 28872879082975162, 33236805263017984, 28872879082975162, 23516376573179666, 27016023684744221,
    30337223556449404, 31337223203880627, 27016023684744221, 27687098495506215, 35318892800121588, 35318892800121588,
    27687098495506215, 22779410979435057, 28135913486145148, 32499839668852048, 28135913486145148, 22779410979435057,
    29564221456457250, 37196015761123867, 37196015761123867, 29564221456457250, 32453603247158732, 37810105755083564,
    42174031936997462, 37810105755083564, 32453603247158732, 34759736111628806, 38080935983056195, 39080935630487418,
    34759736111628806, 28489069227183653, 33845571735906965, 38209497917022249
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
noncomputable def negativeCeiling : ℝ := 19206598959 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 27667153102297487827271680, coefficient := (-27667153102297487827271680) }, { argument := 4534113539664323576175001600, coefficient := (-4534113539664323576175001600) }, { argument := 46680454447878040576432537600, coefficient := (-46680454447878040576432537600) }, { argument := 4534113539664323576175001600, coefficient := (-4534113539664323576175001600) }, { argument := 27667153102297487827271680, coefficient := (-27667153102297487827271680) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 77153294623303644665731874816, coefficient := (-77153294623303644665731874816) }, { argument := 77153275768425358325356429312, coefficient := (-77153275768425358325356429312) }, { argument := 1929806220046080597035057152, coefficient := (-1929806220046080597035057152) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 846614884930303127514513408, coefficient := (-846614884930303127514513408) }, { argument := 138743874313728301430955048960, coefficient := (-138743874313728301430955048960) }, { argument := 1428421906105068041638835650560, coefficient := (-1428421906105068041638835650560) }, { argument := 138743874313728301430955048960, coefficient := (-138743874313728301430955048960) }, { argument := 846614884930303127514513408, coefficient := (-846614884930303127514513408) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 18014046637838777990302924800, coefficient := (-18014046637838777990302924800) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 885348899273519610472693760, coefficient := (-885348899273519610472693760) }, { argument := 145091633269258354437600051200, coefficient := (-145091633269258354437600051200) }, { argument := 1493774542332097298445841203200, coefficient := (-1493774542332097298445841203200) }, { argument := 145091633269258354437600051200, coefficient := (-145091633269258354437600051200) }, { argument := 885348899273519610472693760, coefficient := (-885348899273519610472693760) }, { argument := 2503532393573293747504939008, coefficient := (-2503532393573293747504939008) }, { argument := 100090760592393917404192702464, coefficient := (-100090760592393917404192702464) }, { argument := 100090736132011275665327259648, coefficient := (-100090736132011275665327259648) }, { argument := 2503532393573293747504939008, coefficient := (-2503532393573293747504939008) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 531209339564111766283616256, coefficient := (-531209339564111766283616256) }, { argument := 87054979961555012662560030720, coefficient := (-87054979961555012662560030720) }, { argument := 896264725399258379067504721920, coefficient := (-896264725399258379067504721920) }, { argument := 87054979961555012662560030720, coefficient := (-87054979961555012662560030720) }, { argument := 531209339564111766283616256, coefficient := (-531209339564111766283616256) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 726066157541779635109153996800, coefficient := (-726066157541779635109153996800) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 13562438450746228532928577536, coefficient := (-13562438450746228532928577536) }, { argument := 2222622457143451417040985784320, coefficient := (-2222622457143451417040985784320) }, { argument := 22882758770349815490567229931520, coefficient := (-22882758770349815490567229931520) }, { argument := 2222622457143451417040985784320, coefficient := (-2222622457143451417040985784320) }, { argument := 13562438450746228532928577536, coefficient := (-13562438450746228532928577536) }, { argument := 33536902688908914159284912128, coefficient := (-33536902688908914159284912128) }, { argument := 1340799147102276851893664743424, coefficient := (-1340799147102276851893664743424) }, { argument := 1340798819435067713600113082368, coefficient := (-1340798819435067713600113082368) }, { argument := 33536902688908914159284912128, coefficient := (-33536902688908914159284912128) }, { argument := 868748607412141117776330752, coefficient := (-868748607412141117776330752) }, { argument := 142371165145459760291895050240, coefficient := (-142371165145459760291895050240) }, { argument := 1465766269663370474099981680640, coefficient := (-1465766269663370474099981680640) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
