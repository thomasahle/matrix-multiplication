import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 3, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3

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
def constantNumerator : ℤ := 41610569164949723458249760440320
def positiveArguments : Array ℕ := #[
    13, 231485, 4078561, 16314253, 462965, 322165
  ]
def positiveCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 4372628021148319289169674240, 154083678117914424419337371648, 154083763120511116072951218176, 4372580797483490592717537280, 3042762395907398500540743680
  ]
def positiveScales : Array ℕ := #[
    3, 17, 21, 23, 18, 18
  ]
def negativeArguments : Array ℕ := #[
    82208142275, 3801624601195, 1900398924075, 20679274975, 11509674929, 381865284739,
    4617719602069, 190934134255, 12068962393, 2896040918935, 133963285389117, 33483518134523,
    45534322165, 381865284739, 12649034027973, 152918235145299, 3162282335787, 400521280185,
    82208142275, 2896040918935, 2896042554145, 82207267205, 2896042554145, 66981679628817,
    133934146394099, 1457099126885, 4617719602069, 152918235145299, 1848897355990229, 38229840982565,
    4846197519023, 3801624601195, 133963285389117, 66981679628817, 1900791766299, 82207267205,
    1900791766299, 3800756789707, 41358107965, 190934134255, 3162282335787, 38229840982565,
    1581153082417, 200262140077, 1900398924075, 33483518134523, 133934146394099, 3800756789707,
    12068962393, 400521280185, 4846197519023, 200262140077, 12678811877, 20679274975,
    45534322165, 1457099126885, 41358107965, 1
  ]
def negativeCoefficients : Array ℕ := #[
    23139534932281919956582400, 1070062196084019528906833920, 1069829485789932689974886400, 23282793767925505746534400, 3239685482587496250343424, 107485522128518047055478784,
    1299772517448711466871947264, 107486361985390781986242560, 3397110908491458106359808, 815163050210335925846671360, 37707312634984670777680330752, 37699089948422757039422308352,
    820273425339448466719375360, 107485522128518047055478784, 3560386558435995429831180288, 43042656676157653853241606144, 3560413387272658726932185088, 112736718012195001451151360,
    23139534932281919956582400, 815163050210335925846671360, 815163510481032592878469120, 23139288621974049762836480, 815163510481032592878469120, 37707333427123773003377147904,
    37699110737040607306468818944, 820273885610145133751173120, 1299772517448711466871947264, 43042656676157653853241606144, 520418340217743163428096180224, 43042974400878262666982850560,
    1364083333802237812526809088, 1070062196084019528906833920, 37707312634984670777680330752, 37707333427123773003377147904, 1070050636301635414589964288, 23139288621974049762836480,
    1070050636301635414589964288, 1069817928865645489178017792, 23282544952490342827950080, 107486361985390781986242560, 3560413387272658726932185088, 43042974400878262666982850560,
    3560440216394456175441084416, 112737562428399409141121024, 1069829485789932689974886400, 37699089948422757039422308352, 37699110737040607306468818944, 1069817928865645489178017792,
    3397110908491458106359808, 112736718012195001451151360, 1364083333802237812526809088, 112737562428399409141121024, 3568768277797363685261312, 23282793767925505746534400,
    820273425339448466719375360, 820273885610145133751173120, 23282544952490342827950080, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 41, 40, 34, 33, 38,
    42, 37, 33, 41, 46, 44,
    35, 38, 43, 47, 41, 38,
    36, 41, 41, 36, 41, 45,
    46, 40, 42, 47, 50, 45,
    42, 41, 46, 45, 40, 36,
    40, 41, 35, 37, 41, 45,
    40, 37, 40, 44, 46, 41,
    33, 38, 42, 37, 33, 34,
    35, 40, 35, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3700439718136550, 17820559185672901, 21959628798128645, 23959629594013004, 18820543604719171, 18297440242630321
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36258562241053273, 41789753216467748, 40789439434237523, 34267466553853926, 33422128036475641, 38474272814699900,
    42070317710853878, 37474284087405169, 33490582597226885, 41397219125436721, 46928830998717397, 44928516361491556,
    35406235356837352, 38474272814699900, 43524092448000203, 47119753783421733, 41524103319202849, 38543087940582736,
    36258562241053273, 41397219125436721, 41397219940034566, 36258546884108891, 41397219940034566, 45928831794231831,
    46928517157044749, 40406236166360183, 42070317710853878, 47119753783421733, 50715586557234785, 45119764432815204,
    42139990345317046, 41789753216467748, 46928830998717397, 45928831794231831, 40789737631083045, 36258546884108891,
    40789737631083045, 41789423849316922, 35267451136171835, 37474284087405169, 41524103319202849, 45119764432815204,
    40524114190439115, 37543098746560857, 40789439434237523, 44928516361491556, 46928517157044749, 41789423849316922,
    33490582597226885, 38543087940582736, 42139990345317046, 37543098746560857, 33561700506697383, 34267466553853926,
    35406235356837352, 40406236166360183, 35267451136171835, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 66821521 / 500000000000
noncomputable def negativeCeiling : ℝ := 598664109 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23139534932281919956582400, coefficient := (-23139534932281919956582400) }, { argument := 1070062196084019528906833920, coefficient := (-1070062196084019528906833920) }, { argument := 1069829485789932689974886400, coefficient := (-1069829485789932689974886400) }, { argument := 23282793767925505746534400, coefficient := (-23282793767925505746534400) }, { argument := 3239685482587496250343424, coefficient := (-3239685482587496250343424) }, { argument := 107485522128518047055478784, coefficient := (-107485522128518047055478784) }, { argument := 1299772517448711466871947264, coefficient := (-1299772517448711466871947264) }, { argument := 107486361985390781986242560, coefficient := (-107486361985390781986242560) }, { argument := 3397110908491458106359808, coefficient := (-3397110908491458106359808) }, { argument := 815163050210335925846671360, coefficient := (-815163050210335925846671360) }, { argument := 37707312634984670777680330752, coefficient := (-37707312634984670777680330752) }, { argument := 37699089948422757039422308352, coefficient := (-37699089948422757039422308352) }, { argument := 820273425339448466719375360, coefficient := (-820273425339448466719375360) }, { argument := 107485522128518047055478784, coefficient := (-107485522128518047055478784) }, { argument := 3560386558435995429831180288, coefficient := (-3560386558435995429831180288) }, { argument := 43042656676157653853241606144, coefficient := (-43042656676157653853241606144) }, { argument := 3560413387272658726932185088, coefficient := (-3560413387272658726932185088) }, { argument := 112736718012195001451151360, coefficient := (-112736718012195001451151360) }, { argument := 23139534932281919956582400, coefficient := (-23139534932281919956582400) }, { argument := 815163050210335925846671360, coefficient := (-815163050210335925846671360) }, { argument := 815163510481032592878469120, coefficient := (-815163510481032592878469120) }, { argument := 23139288621974049762836480, coefficient := (-23139288621974049762836480) }, { argument := 815163510481032592878469120, coefficient := (-815163510481032592878469120) }, { argument := 37707333427123773003377147904, coefficient := (-37707333427123773003377147904) }, { argument := 37699110737040607306468818944, coefficient := (-37699110737040607306468818944) }, { argument := 820273885610145133751173120, coefficient := (-820273885610145133751173120) }, { argument := 1299772517448711466871947264, coefficient := (-1299772517448711466871947264) }, { argument := 43042656676157653853241606144, coefficient := (-43042656676157653853241606144) }, { argument := 520418340217743163428096180224, coefficient := (-520418340217743163428096180224) }, { argument := 43042974400878262666982850560, coefficient := (-43042974400878262666982850560) }, { argument := 1364083333802237812526809088, coefficient := (-1364083333802237812526809088) }, { argument := 1070062196084019528906833920, coefficient := (-1070062196084019528906833920) }, { argument := 37707312634984670777680330752, coefficient := (-37707312634984670777680330752) }, { argument := 37707333427123773003377147904, coefficient := (-37707333427123773003377147904) }, { argument := 1070050636301635414589964288, coefficient := (-1070050636301635414589964288) }, { argument := 23139288621974049762836480, coefficient := (-23139288621974049762836480) }, { argument := 1070050636301635414589964288, coefficient := (-1070050636301635414589964288) }, { argument := 1069817928865645489178017792, coefficient := (-1069817928865645489178017792) }, { argument := 23282544952490342827950080, coefficient := (-23282544952490342827950080) }, { argument := 107486361985390781986242560, coefficient := (-107486361985390781986242560) }, { argument := 3560413387272658726932185088, coefficient := (-3560413387272658726932185088) }, { argument := 43042974400878262666982850560, coefficient := (-43042974400878262666982850560) }, { argument := 3560440216394456175441084416, coefficient := (-3560440216394456175441084416) }, { argument := 112737562428399409141121024, coefficient := (-112737562428399409141121024) }, { argument := 1069829485789932689974886400, coefficient := (-1069829485789932689974886400) }, { argument := 37699089948422757039422308352, coefficient := (-37699089948422757039422308352) }, { argument := 37699110737040607306468818944, coefficient := (-37699110737040607306468818944) }, { argument := 1069817928865645489178017792, coefficient := (-1069817928865645489178017792) }, { argument := 3397110908491458106359808, coefficient := (-3397110908491458106359808) }, { argument := 112736718012195001451151360, coefficient := (-112736718012195001451151360) }, { argument := 1364083333802237812526809088, coefficient := (-1364083333802237812526809088) }, { argument := 112737562428399409141121024, coefficient := (-112737562428399409141121024) }, { argument := 3568768277797363685261312, coefficient := (-3568768277797363685261312) }, { argument := 23282793767925505746534400, coefficient := (-23282793767925505746534400) }, { argument := 820273425339448466719375360, coefficient := (-820273425339448466719375360) }, { argument := 820273885610145133751173120, coefficient := (-820273885610145133751173120) }, { argument := 23282544952490342827950080, coefficient := (-23282544952490342827950080) }, { argument := 1029966112685436388716071354368, coefficient := 1029966112685436388716071354368 }, { argument := 4372628021148319289169674240, coefficient := 4372628021148319289169674240 }, { argument := 154083678117914424419337371648, coefficient := 154083678117914424419337371648 }, { argument := 154083763120511116072951218176, coefficient := 154083763120511116072951218176 }, { argument := 4372580797483490592717537280, coefficient := 4372580797483490592717537280 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3042762395907398500540743680, coefficient := 3042762395907398500540743680 }] }

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

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-42108911861833031431937620705280)
def positiveArguments : Array ℕ := #[
    10669159, 128996305, 5334619, 338077, 355035, 16422859,
    8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    100767357724014042117023203328, 1218335654292060058455438786560, 100768103857918335520966967296, 3193046986858242089821405184, 3353210768491248976889118720, 155109517788988197449108553728,
    155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    23, 26, 22, 18, 18, 23,
    22, 16
  ]
def negativeArguments : Array ℕ := #[
    9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    23346943123940155, 26942754499879599, 22346953806364728, 18366992344809980, 18437601729582122, 23969201966206902,
    22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 270144911 / 500000000000
noncomputable def negativeCeiling : ℝ := 5441537 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 100767357724014042117023203328, coefficient := 100767357724014042117023203328 }, { argument := 1218335654292060058455438786560, coefficient := 1218335654292060058455438786560 }, { argument := 100768103857918335520966967296, coefficient := 100768103857918335520966967296 }, { argument := 3193046986858242089821405184, coefficient := 3193046986858242089821405184 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3
