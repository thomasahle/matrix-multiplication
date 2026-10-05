import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

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
def constantNumerator : ℤ := (-90375839837434143537203783086899200)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5484247761, 1208756026738537183, 5485706961, 5485706961, 467068578459, 5481329361,
    187193415171, 467068578459, 65602110099022653, 5484247761, 5481329361, 11601041451,
    172716492232201691, 29637, 1665, 605545517726669411, 90021, 86358245538277345,
    90021, 90021, 29637, 1665, 7299, 114351,
    90021, 2829579, 90021, 90021, 46227, 46227,
    1564419, 85155, 2829579, 1564419, 7299, 90021,
    85155, 114351, 6417723815, 931563, 52335, 180863407565,
    2829579, 51341774075, 2829579, 2829579, 931563, 52335,
    8382152475016879, 8382149877432657, 191988765, 29637, 1665, 5293712415,
    90021, 1535909625, 90021, 90021, 29637, 1665,
    5433, 5433, 5295827, 4669234258444161
  ]
def negativeCoefficients : Array ℕ := #[
    25291628720995406853590482944, 680469148950189669595868976644096, 25298358093233496098019999744, 25298358093233496098019999744, 1076986816463062873516925779968, 25278169976519228364731449344,
    215819313871443495107633872896, 1076986816463062873516925779968, 18465352412292292031162370490368, 25291628720995406853590482944, 25278169976519228364731449344, 26750180329386638453980004352,
    194461482514420675620607763677184, 279913550905615350396616704, 15725480387955918561607680, 681783641997425609866892451774464, 425112153154408331782127616, 194461481213277824851749959106560,
    425112153154408331782127616, 425112153154408331782127616, 279913550905615350396616704, 15725480387955918561607680, 551496847335448646636273664, 540007329682626799831351296,
    425112153154408331782127616, 13362309030231807834124713984, 425112153154408331782127616, 425112153154408331782127616, 436601670807230178587049984, 436601670807230178587049984,
    7387759850764447495565082624, 402133117848764638172282880, 13362309030231807834124713984, 7387759850764447495565082624, 551496847335448646636273664, 425112153154408331782127616,
    402133117848764638172282880, 540007329682626799831351296, 59193054375527952399487467520, 8798363775762990608412573696, 494290099761965764517560320, 208521311978161189709875773440,
    13362309030231807834124713984, 59193035415733809139888947200, 13362309030231807834124713984, 13362309030231807834124713984, 8798363775762990608412573696, 494290099761965764517560320,
    18874929381524348523243993300992, 18874923532284681391904114343936, 7083135225965131566919188480, 279913550905615350396616704, 15725480387955918561607680, 24412939529830982123425628160,
    425112153154408331782127616, 7083132943180552445362176000, 425112153154408331782127616, 425112153154408331782127616, 279913550905615350396616704, 15725480387955918561607680,
    210179007294920969797716934656, 210179007294920969797716934656, 100035343695504418412448186368, 5257090416608669423936118718464
  ]
def negativeScales : Array ℕ := #[
    32, 60, 32, 32, 38, 32,
    37, 38, 55, 32, 32, 33,
    57, 14, 10, 59, 16, 56,
    16, 16, 14, 10, 12, 16,
    16, 21, 16, 16, 15, 15,
    20, 16, 21, 20, 12, 16,
    16, 16, 32, 19, 15, 37,
    21, 35, 21, 21, 19, 15,
    52, 52, 27, 14, 10, 32,
    16, 30, 16, 16, 14, 10,
    12, 12, 22, 52
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32352646602983018, 60068228790828000, 32353030411425155, 32353030411425155, 38764843436701780, 32351878679642569,
    37445738730459969, 38764843436701780, 55864591740513285, 32352646602983018, 32351878679642569, 33433535273946308,
    57261183461589503, 14855111799946705, 10701306462033270, 59071013021775035, 16457973970567442, 56261183451936423,
    16457973970567442, 16457973970567442, 14855111799946705, 10701306462033270, 12833483106919052, 16803109457304290,
    16457973970567442, 21432155986411672, 16457973970567442, 16457973970567442, 15496448118382256, 15496448118382256,
    20577195532269347, 16377803621883399, 21432155986411672, 20577195532269347, 12833483106919052, 16457973970567442,
    16377803621883399, 16803109457304290, 32579414558956085, 19829293815042335, 15675488477843117, 37396109593983378,
    21432155986411672, 35579414096854481, 21432155986411672, 21432155986411672, 19829293815042335, 15675488477843117,
    52896242192353396, 52896241745269817, 27516446647373747, 14855111799946705, 10701306462033270, 32301632675430276,
    16457973970567442, 30516446182415446, 16457973970567442, 16457973970567442, 14855111799946705, 10701306462033270,
    12407533331671334, 12407533331671334, 22336424563387985, 52052107394631513
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
noncomputable def negativeCeiling : ℝ := 128370566287 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25291628720995406853590482944, coefficient := (-25291628720995406853590482944) }, { argument := 680469148950189669595868976644096, coefficient := (-680469148950189669595868976644096) }, { argument := 25298358093233496098019999744, coefficient := (-25298358093233496098019999744) }, { argument := 25298358093233496098019999744, coefficient := (-25298358093233496098019999744) }, { argument := 1076986816463062873516925779968, coefficient := (-1076986816463062873516925779968) }, { argument := 25278169976519228364731449344, coefficient := (-25278169976519228364731449344) }, { argument := 215819313871443495107633872896, coefficient := (-215819313871443495107633872896) }, { argument := 1076986816463062873516925779968, coefficient := (-1076986816463062873516925779968) }, { argument := 18465352412292292031162370490368, coefficient := (-18465352412292292031162370490368) }, { argument := 25291628720995406853590482944, coefficient := (-25291628720995406853590482944) }, { argument := 25278169976519228364731449344, coefficient := (-25278169976519228364731449344) }, { argument := 26750180329386638453980004352, coefficient := (-26750180329386638453980004352) }, { argument := 194461482514420675620607763677184, coefficient := (-194461482514420675620607763677184) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 681783641997425609866892451774464, coefficient := (-681783641997425609866892451774464) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 194461481213277824851749959106560, coefficient := (-194461481213277824851749959106560) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 59193054375527952399487467520, coefficient := (-59193054375527952399487467520) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 208521311978161189709875773440, coefficient := (-208521311978161189709875773440) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 59193035415733809139888947200, coefficient := (-59193035415733809139888947200) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 18874929381524348523243993300992, coefficient := (-18874929381524348523243993300992) }, { argument := 18874923532284681391904114343936, coefficient := (-18874923532284681391904114343936) }, { argument := 7083135225965131566919188480, coefficient := (-7083135225965131566919188480) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 24412939529830982123425628160, coefficient := (-24412939529830982123425628160) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 7083132943180552445362176000, coefficient := (-7083132943180552445362176000) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 210179007294920969797716934656, coefficient := (-210179007294920969797716934656) }, { argument := 210179007294920969797716934656, coefficient := (-210179007294920969797716934656) }, { argument := 100035343695504418412448186368, coefficient := (-100035343695504418412448186368) }, { argument := 5257090416608669423936118718464, coefficient := (-5257090416608669423936118718464) }] }

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
def constantNumerator : ℤ := (-92551155165692130938711446206283776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3361586637, 86199173535481331, 53193157557, 1591636887, 86195746818573263, 1591729047,
    1591729047, 136176627933, 1591452567, 53193157557, 136176627933, 4676088554067195,
    1591636887, 1591452567, 3361586637, 690838513574825155, 29637, 1665,
    1211043920972760027, 90021, 690838508952234887, 90021, 90021, 29637,
    1665, 86376877761996133, 86376850687810203, 192000285, 15219, 855,
    5295171615, 46227, 1536001785, 46227, 46227, 15219,
    855, 6113, 6113, 355255597, 827, 827,
    945, 7299, 114351, 90021, 2829579, 90021,
    90021, 46227, 46227, 1564419, 85155, 2829579,
    1564419, 7299, 90021, 85155, 114351, 192000285,
    15219, 855, 5295171615, 46227
  ]
def negativeCoefficients : Array ℕ := #[
    7751291046792621466450919424, 194103282907019221277632614105088, 61327535245405512535356997632, 7340129578191192319064014848, 194095566626524081666133510324224, 7340554591174650587133247488,
    7340554591174650587133247488, 314001925537602292190036361216, 7339279552224275782925549568, 61327535245405512535356997632, 314001925537602292190036361216, 5264807667412115209965986119680,
    7340129578191192319064014848, 7339279552224275782925549568, 7751291046792621466450919424, 194453754519298119410852225351680, 279913550905615350396616704, 15725480387955918561607680,
    681757118902778307912804203495424, 425112153154408331782127616, 194453753218154631382647147855872, 425112153154408331782127616, 425112153154408331782127616, 279913550905615350396616704,
    15725480387955918561607680, 194503437251176333528775455145984, 194503376285529500675012604985344, 7083560238948589834988421120, 287478782011172522028957696, 16150493371414186630840320,
    24419668902069071367855144960, 436601670807230178587049984, 7083557956164010713431408640, 436601670807230178587049984, 436601670807230178587049984, 287478782011172522028957696,
    16150493371414186630840320, 118242616564867650319661662208, 118242616564867650319661662208, 6710588496498584334279060226048, 7998253222570386619856060416, 7998253222570386619856060416,
    18278958392573193121557381120, 551496847335448646636273664, 540007329682626799831351296, 425112153154408331782127616, 13362309030231807834124713984, 425112153154408331782127616,
    425112153154408331782127616, 436601670807230178587049984, 436601670807230178587049984, 7387759850764447495565082624, 402133117848764638172282880, 13362309030231807834124713984,
    7387759850764447495565082624, 551496847335448646636273664, 425112153154408331782127616, 402133117848764638172282880, 540007329682626799831351296, 7083560238948589834988421120,
    287478782011172522028957696, 16150493371414186630840320, 24419668902069071367855144960, 436601670807230178587049984
  ]
def negativeScales : Array ℕ := #[
    31, 56, 35, 30, 56, 30,
    30, 36, 30, 35, 36, 52,
    30, 30, 31, 59, 14, 10,
    60, 16, 59, 16, 16, 14,
    10, 56, 56, 27, 13, 9,
    32, 15, 30, 15, 15, 13,
    9, 12, 12, 28, 9, 9,
    9, 12, 16, 16, 21, 16,
    16, 15, 15, 20, 16, 21,
    20, 12, 16, 16, 16, 27,
    13, 9, 32, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31646495186130487, 56258523555238639, 35630521627066632, 30567864093716696, 56258466201953748, 30567947627170136,
    30567947627170136, 36986688176958984, 30567697012298411, 35630521627066632, 36986688176958984, 52054223674673564,
    30567864093716696, 30567697012298411, 31646495186130487, 59261126127038531, 14855111799946705, 10701306462033270,
    60070956896225702, 16457973970567442, 59261126117385062, 16457973970567442, 16457973970567442, 14855111799946705,
    10701306462033270, 56261494687038474, 56261494234836439, 27516533211544659, 13893585949743706, 9739780609952834,
    32302030296295898, 15496448118382256, 30516532746614255, 15496448118382256, 15496448118382256, 13893585949743706,
    9739780609952834, 12577664851767857, 12577664851767857, 28404282138195492, 9691743519230811, 9691743519230811,
    9884170522387776, 12833483106919052, 16803109457304290, 16457973970567442, 21432155986411672, 16457973970567442,
    16457973970567442, 15496448118382256, 15496448118382256, 20577195532269347, 16377803621883399, 21432155986411672,
    20577195532269347, 12833483106919052, 16457973970567442, 16377803621883399, 16803109457304290, 27516533211544659,
    13893585949743706, 9739780609952834, 32302030296295898, 15496448118382256
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
noncomputable def negativeCeiling : ℝ := 260547298411 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7751291046792621466450919424, coefficient := (-7751291046792621466450919424) }, { argument := 194103282907019221277632614105088, coefficient := (-194103282907019221277632614105088) }, { argument := 61327535245405512535356997632, coefficient := (-61327535245405512535356997632) }, { argument := 7340129578191192319064014848, coefficient := (-7340129578191192319064014848) }, { argument := 194095566626524081666133510324224, coefficient := (-194095566626524081666133510324224) }, { argument := 7340554591174650587133247488, coefficient := (-7340554591174650587133247488) }, { argument := 7340554591174650587133247488, coefficient := (-7340554591174650587133247488) }, { argument := 314001925537602292190036361216, coefficient := (-314001925537602292190036361216) }, { argument := 7339279552224275782925549568, coefficient := (-7339279552224275782925549568) }, { argument := 61327535245405512535356997632, coefficient := (-61327535245405512535356997632) }, { argument := 314001925537602292190036361216, coefficient := (-314001925537602292190036361216) }, { argument := 5264807667412115209965986119680, coefficient := (-5264807667412115209965986119680) }, { argument := 7340129578191192319064014848, coefficient := (-7340129578191192319064014848) }, { argument := 7339279552224275782925549568, coefficient := (-7339279552224275782925549568) }, { argument := 7751291046792621466450919424, coefficient := (-7751291046792621466450919424) }, { argument := 194453754519298119410852225351680, coefficient := (-194453754519298119410852225351680) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 681757118902778307912804203495424, coefficient := (-681757118902778307912804203495424) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 194453753218154631382647147855872, coefficient := (-194453753218154631382647147855872) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 194503437251176333528775455145984, coefficient := (-194503437251176333528775455145984) }, { argument := 194503376285529500675012604985344, coefficient := (-194503376285529500675012604985344) }, { argument := 7083560238948589834988421120, coefficient := (-7083560238948589834988421120) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 24419668902069071367855144960, coefficient := (-24419668902069071367855144960) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 7083557956164010713431408640, coefficient := (-7083557956164010713431408640) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 118242616564867650319661662208, coefficient := (-118242616564867650319661662208) }, { argument := 118242616564867650319661662208, coefficient := (-118242616564867650319661662208) }, { argument := 6710588496498584334279060226048, coefficient := (-6710588496498584334279060226048) }, { argument := 7998253222570386619856060416, coefficient := (-7998253222570386619856060416) }, { argument := 7998253222570386619856060416, coefficient := (-7998253222570386619856060416) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 7083560238948589834988421120, coefficient := (-7083560238948589834988421120) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 24419668902069071367855144960, coefficient := (-24419668902069071367855144960) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
