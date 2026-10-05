import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 186394862831549594151175778729984
def positiveArguments : Array ℕ := #[
    49, 8388635
  ]
def positiveCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 79228417522054412554385489920
  ]
def positiveScales : Array ℕ := #[
    5, 23
  ]
def negativeArguments : Array ℕ := #[
    1181899951055, 69187070719025, 69210038801655, 1158931868425, 1128105090025, 11138941864855,
    490466345597835, 22277915455155, 563942854245, 1307907627255, 46636689036605, 46636186404725,
    1308388346455, 1128105090025, 3767046530895, 140899729305, 1181892342833, 69186625342415,
    69209593277193, 1158924408055, 3767046530895, 148075968677679, 814721200110217, 148076177429269,
    3766310750555, 46636689036605, 1664638073715935, 208077682948165, 11663141526255, 11138941864855,
    148075968677679, 44512483969653, 1181899951055, 1181892342833, 140899729305, 44512483969653,
    489983697735523, 44512547311493, 1126978591195, 46636186404725, 208077682948165, 104037803340995,
    46652063476275, 490466345597835, 814721200110217, 489983697735523, 69187070719025, 69186625342415,
    1308388346455, 11663141526255, 46652063476275, 654434529245, 22277915455155, 148076177429269,
    44512547311493, 69210038801655, 69209593277193, 563942854245, 3766310750555, 1126978591195,
    1158931868425, 1158924408055
  ]
def negativeCoefficients : Array ℕ := #[
    332675261197531591296942080, 19474429119316071547299430400, 19480894059839439219908935680, 326210320674163918687436800, 317533353941959365256806400, 12541333607965648953561579520,
    138054003204511163574135029760, 12541351467803433973957263360, 317471603529504492292669440, 368143268921290473634529280, 13127060960440498380477562880, 13126919482143781347236249600,
    368278579346914838818324480, 317533353941959365256806400, 1060329334551627602979717120, 317277984197300877671792640, 332673119673421331796328448, 19474303756945144326379274240,
    19480768655851873742364868608, 326208220766691915810734080, 1060329334551627602979717120, 41679679834957523857308647424, 458647261653402073230636744704, 41679738593306457419718590464,
    1060122230797561944426414080, 13127060960440498380477562880, 468553963030864069857231503360, 468549287694736051778009169920, 13131529957902843997449093120, 12541333607965648953561579520,
    41679679834957523857308647424, 12529150388691526711265722368, 332675261197531591296942080, 332673119673421331796328448, 317277984197300877671792640, 12529150388691526711265722368,
    137918149908707445470383833088, 12529168217834465521364369408, 317216272710020534024273920, 13126919482143781347236249600, 468549287694736051778009169920, 468544612358950025795490283520,
    13131388480488551016195686400, 138054003204511163574135029760, 458647261653402073230636744704, 137918149908707445470383833088, 19474429119316071547299430400, 19474303756945144326379274240,
    368278579346914838818324480, 13131529957902843997449093120, 13131388480488551016195686400, 368413887755770995870269440, 12541351467803433973957263360, 41679738593306457419718590464,
    12529168217834465521364369408, 19480894059839439219908935680, 19480768655851873742364868608, 317471603529504492292669440, 1060122230797561944426414080, 317216272710020534024273920,
    326210320674163918687436800, 326208220766691915810734080
  ]
def negativeScales : Array ℕ := #[
    40, 45, 45, 40, 40, 43,
    48, 44, 39, 40, 45, 45,
    40, 40, 41, 37, 40, 45,
    45, 40, 41, 47, 49, 47,
    41, 45, 50, 47, 43, 43,
    47, 45, 40, 40, 37, 45,
    48, 45, 40, 45, 47, 46,
    45, 48, 49, 48, 45, 45,
    40, 43, 45, 39, 44, 47,
    45, 45, 45, 39, 41, 40,
    40, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 23000004643524100
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40104245053837323, 45975567710002568, 45976046563181277, 40075932893970677, 40037038608686344, 43340677425025911,
    48801147475304935, 44340679479534775, 39036758021856102, 40250397790793940, 45406530601833405, 45406515052950254,
    40250927953451891, 40037038608686344, 41776570992739250, 37035877883721458, 40104235766774176, 45975558422936993,
    45976037276115685, 40075923606907531, 41776570992739250, 47073330852353808, 49533299777912982, 47073332886206256,
    41776289177707710, 45406530601833405, 50564129963363341, 47564115567758072, 43407021671636729, 43340677425025911,
    47073330852353808, 45339275244564234, 40104245053837323, 40104235766774176, 37035877883721458, 45339275244564234,
    48799727079135478, 45339277297536463, 40035597248062501, 45406515052950254, 47564115567758072, 46564101172010211,
    45407006128142241, 48801147475304935, 49533299777912982, 48799727079135478, 45975567710002568, 45975558422936993,
    40250927953451891, 43407021671636729, 45407006128142241, 39251457913459247, 44340679479534775, 47073332886206256,
    45339277297536463, 45976046563181277, 45976037276115685, 39036758021856102, 41776289177707710, 40035597248062501,
    40075932893970677, 40075923606907531
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 62
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
noncomputable def positiveFloor : ℝ := 4442347 / 15625000000
noncomputable def negativeCeiling : ℝ := 2252068317 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 332675261197531591296942080, coefficient := (-332675261197531591296942080) }, { argument := 19474429119316071547299430400, coefficient := (-19474429119316071547299430400) }, { argument := 19480894059839439219908935680, coefficient := (-19480894059839439219908935680) }, { argument := 326210320674163918687436800, coefficient := (-326210320674163918687436800) }, { argument := 317533353941959365256806400, coefficient := (-317533353941959365256806400) }, { argument := 12541333607965648953561579520, coefficient := (-12541333607965648953561579520) }, { argument := 138054003204511163574135029760, coefficient := (-138054003204511163574135029760) }, { argument := 12541351467803433973957263360, coefficient := (-12541351467803433973957263360) }, { argument := 317471603529504492292669440, coefficient := (-317471603529504492292669440) }, { argument := 368143268921290473634529280, coefficient := (-368143268921290473634529280) }, { argument := 13127060960440498380477562880, coefficient := (-13127060960440498380477562880) }, { argument := 13126919482143781347236249600, coefficient := (-13126919482143781347236249600) }, { argument := 368278579346914838818324480, coefficient := (-368278579346914838818324480) }, { argument := 317533353941959365256806400, coefficient := (-317533353941959365256806400) }, { argument := 1060329334551627602979717120, coefficient := (-1060329334551627602979717120) }, { argument := 317277984197300877671792640, coefficient := (-317277984197300877671792640) }, { argument := 332673119673421331796328448, coefficient := (-332673119673421331796328448) }, { argument := 19474303756945144326379274240, coefficient := (-19474303756945144326379274240) }, { argument := 19480768655851873742364868608, coefficient := (-19480768655851873742364868608) }, { argument := 326208220766691915810734080, coefficient := (-326208220766691915810734080) }, { argument := 1060329334551627602979717120, coefficient := (-1060329334551627602979717120) }, { argument := 41679679834957523857308647424, coefficient := (-41679679834957523857308647424) }, { argument := 458647261653402073230636744704, coefficient := (-458647261653402073230636744704) }, { argument := 41679738593306457419718590464, coefficient := (-41679738593306457419718590464) }, { argument := 1060122230797561944426414080, coefficient := (-1060122230797561944426414080) }, { argument := 13127060960440498380477562880, coefficient := (-13127060960440498380477562880) }, { argument := 468553963030864069857231503360, coefficient := (-468553963030864069857231503360) }, { argument := 468549287694736051778009169920, coefficient := (-468549287694736051778009169920) }, { argument := 13131529957902843997449093120, coefficient := (-13131529957902843997449093120) }, { argument := 12541333607965648953561579520, coefficient := (-12541333607965648953561579520) }, { argument := 41679679834957523857308647424, coefficient := (-41679679834957523857308647424) }, { argument := 12529150388691526711265722368, coefficient := (-12529150388691526711265722368) }, { argument := 332675261197531591296942080, coefficient := (-332675261197531591296942080) }, { argument := 332673119673421331796328448, coefficient := (-332673119673421331796328448) }, { argument := 317277984197300877671792640, coefficient := (-317277984197300877671792640) }, { argument := 12529150388691526711265722368, coefficient := (-12529150388691526711265722368) }, { argument := 137918149908707445470383833088, coefficient := (-137918149908707445470383833088) }, { argument := 12529168217834465521364369408, coefficient := (-12529168217834465521364369408) }, { argument := 317216272710020534024273920, coefficient := (-317216272710020534024273920) }, { argument := 13126919482143781347236249600, coefficient := (-13126919482143781347236249600) }, { argument := 468549287694736051778009169920, coefficient := (-468549287694736051778009169920) }, { argument := 468544612358950025795490283520, coefficient := (-468544612358950025795490283520) }, { argument := 13131388480488551016195686400, coefficient := (-13131388480488551016195686400) }, { argument := 138054003204511163574135029760, coefficient := (-138054003204511163574135029760) }, { argument := 458647261653402073230636744704, coefficient := (-458647261653402073230636744704) }, { argument := 137918149908707445470383833088, coefficient := (-137918149908707445470383833088) }, { argument := 19474429119316071547299430400, coefficient := (-19474429119316071547299430400) }, { argument := 19474303756945144326379274240, coefficient := (-19474303756945144326379274240) }, { argument := 368278579346914838818324480, coefficient := (-368278579346914838818324480) }, { argument := 13131529957902843997449093120, coefficient := (-13131529957902843997449093120) }, { argument := 13131388480488551016195686400, coefficient := (-13131388480488551016195686400) }, { argument := 368413887755770995870269440, coefficient := (-368413887755770995870269440) }, { argument := 12541351467803433973957263360, coefficient := (-12541351467803433973957263360) }, { argument := 41679738593306457419718590464, coefficient := (-41679738593306457419718590464) }, { argument := 12529168217834465521364369408, coefficient := (-12529168217834465521364369408) }, { argument := 19480894059839439219908935680, coefficient := (-19480894059839439219908935680) }, { argument := 19480768655851873742364868608, coefficient := (-19480768655851873742364868608) }, { argument := 317471603529504492292669440, coefficient := (-317471603529504492292669440) }, { argument := 1060122230797561944426414080, coefficient := (-1060122230797561944426414080) }, { argument := 317216272710020534024273920, coefficient := (-317216272710020534024273920) }, { argument := 326210320674163918687436800, coefficient := (-326210320674163918687436800) }, { argument := 326208220766691915810734080, coefficient := (-326208220766691915810734080) }, { argument := 3882179963198952542083653566464, coefficient := 3882179963198952542083653566464 }, { argument := 79228417522054412554385489920, coefficient := 79228417522054412554385489920 }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-184876229945499288871447373545472)
def positiveArguments : Array ℕ := #[
    8388581, 34680005, 57611701, 34645969, 357215, 203999805,
    203997765, 2858695, 22435, 14134897, 9722607, 14134917,
    179445, 140893, 8247715, 8250453, 138155
  ]
def positiveCoefficients : Array ℕ := #[
    79227907506474262632702410752, 327543386475503420718406696960, 1088254263294030488110140227584, 327221925544281518229419982848, 53980804581704970080333332480, 1926723683287886928026334658560,
    1926704416032636819873862778880, 53999221810988161696666746880, 3390281345381775691816632320, 133500327663229399044271898624, 1469238829533241364550311215104, 133500516557888713830080446464,
    3389620214074173941486714880, 1330696761741905846186541056, 77897465752522431747357409280, 77923325431382625924547608576, 1304837082881711668996341760
  ]
def positiveScales : Array ℕ := #[
    22, 25, 25, 25, 18, 27,
    27, 21, 14, 23, 23, 23,
    17, 17, 22, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 11, 25, 11, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1743019575313815427057966907392, 3961408125713216879677197516800, 1743019575313815427057966907392, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 3, 4, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22999995355001480, 25047600770772284, 25779858518565998, 25046184171205808, 18446433137122287, 27603992532247887,
    27603978105211552, 21446925273427474, 14453463563563703, 23752758034586850, 23212911776332069, 23752760075909146,
    17453182199342258, 17104240410313222, 22975563049544053, 22976041902589359, 17075928250446576
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3459431618637364, 4643856189792934, 3459431618637364, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 149697111 / 62500000000
noncomputable def negativeCeiling : ℝ := 366599847 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79227907506474262632702410752, coefficient := 79227907506474262632702410752 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 327543386475503420718406696960, coefficient := 327543386475503420718406696960 }, { argument := 1088254263294030488110140227584, coefficient := 1088254263294030488110140227584 }, { argument := 327221925544281518229419982848, coefficient := 327221925544281518229419982848 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 53980804581704970080333332480, coefficient := 53980804581704970080333332480 }, { argument := 1926723683287886928026334658560, coefficient := 1926723683287886928026334658560 }, { argument := 1926704416032636819873862778880, coefficient := 1926704416032636819873862778880 }, { argument := 53999221810988161696666746880, coefficient := 53999221810988161696666746880 }, { argument := 3961408125713216879677197516800, coefficient := (-3961408125713216879677197516800) }, { argument := 3390281345381775691816632320, coefficient := 3390281345381775691816632320 }, { argument := 133500327663229399044271898624, coefficient := 133500327663229399044271898624 }, { argument := 1469238829533241364550311215104, coefficient := 1469238829533241364550311215104 }, { argument := 133500516557888713830080446464, coefficient := 133500516557888713830080446464 }, { argument := 3389620214074173941486714880, coefficient := 3389620214074173941486714880 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 1330696761741905846186541056, coefficient := 1330696761741905846186541056 }, { argument := 77897465752522431747357409280, coefficient := 77897465752522431747357409280 }, { argument := 77923325431382625924547608576, coefficient := 77923325431382625924547608576 }, { argument := 1304837082881711668996341760, coefficient := 1304837082881711668996341760 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3
