import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 19792562607012138593949890365095936
def positiveArguments : Array ℕ := #[
    3635, 187, 7191354543, 13743, 7191024465, 6939,
    639751487, 3515, 1147, 8795572113, 11581, 2559005555,
    23199, 10397, 3515, 1147, 381821087, 6157,
    4950248891, 152353
  ]
def positiveCoefficients : Array ℕ := #[
    287994370739350867152532259471360, 14815666390167431129992718712832, 67920423320591109568621870841856, 531656561246843159935583256576, 67917305822023244275116178145280, 536879120787578357970313936896,
    48338255673197048841991180255232, 2175679619044055833135210823680, 88744826566270698456830967808, 166143659776376574623153853038592, 1792072949370498620450844704768, 48338248249636937770908904325120,
    1794935685711346062336548929536, 1608857823556262339765774319616, 2175679619044055833135210823680, 88744826566270698456830967808, 1803099103701654814797754007552, 476374801367505397034619240448,
    46753778889442063433324164022272, 11787742425327846313856642056192
  ]
def positiveScales : Array ℕ := #[
    11, 7, 32, 13, 32, 12,
    29, 11, 10, 33, 13, 31,
    14, 13, 11, 10, 28, 12,
    32, 17
  ]
def negativeArguments : Array ℕ := #[
    2489, 7918325695, 13591113793, 7918325695, 84233, 84233,
    8721, 4585, 4585, 4959, 2677014025, 4594860535,
    2677014025, 152353, 152353, 8949, 84233, 84233,
    139707, 171, 1593532724232549, 721563999, 1593456663953051, 364326027,
    168807, 8721, 873551945, 1499375543, 873551945, 4847,
    4847, 285, 4585, 4585, 171, 285,
    6157, 6157, 4389, 4959, 1825271, 187,
    27, 215
  ]
def negativeCoefficients : Array ℕ := #[
    96288523680665984506997506048, 146067327587943316527901573120, 501423595632269791288126078976, 146067327587943316527901573120, 1629303177017584948368405168128, 1629303177017584948368405168128,
    168688673165746896521800974336, 88686798126929196256445071360, 88686798126929196256445071360, 95921010231503137237886828544, 197528770403624413809973657600, 678081730748265198183230996480,
    197528770403624413809973657600, 2946935606331961578464160514048, 2946935606331961578464160514048, 173098834555701063751129104384, 1629303177017584948368405168128, 1629303177017584948368405168128,
    2702326391694415969770811686912, 105843873358900013503875121152, 448539586441024939866030342144, 3327626605588853707134468096, 448518177375624634329995411456, 3360314489730198046104354816,
    408150281663373414189250904064, 168688673165746896521800974336, 8057094582253101089617346560, 27658596912100290978526527488, 8057094582253101089617346560, 93754615162753721756813361152,
    93754615162753721756813361152, 5512701737442709036660162560, 88686798126929196256445071360, 88686798126929196256445071360, 105843873358900013503875121152, 5512701737442709036660162560,
    119093700341876349258654810112, 119093700341876349258654810112, 169791213513235438329133006848, 95921010231503137237886828544, 8619598592553960188848111616, 14815666390167431129992718712832,
    136906264824648775361643946180608, 272544879049069321321791189155840
  ]
def negativeScales : Array ℕ := #[
    11, 32, 33, 32, 16, 16,
    13, 12, 12, 12, 31, 32,
    31, 17, 17, 13, 16, 16,
    17, 7, 50, 29, 50, 28,
    17, 13, 29, 30, 29, 12,
    12, 8, 12, 12, 7, 8,
    12, 12, 12, 12, 20, 7,
    4, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11827739648737264, 7546894459887560, 32743616392151108, 13746409348226269, 32743550171966895, 12760512051339829,
    29252936354681373, 11779308973933791, 10163649676015824, 33034130275656611, 13499472212561551, 31252936133119092,
    14501774998430970, 13343879685849875, 11779308973933791, 10163649676015824, 28508321540390344, 12588011853214835,
    32204853917518796, 17217058383010668
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11281350514981036, 32882548266404035, 33661944638841019, 32882548266404035, 16362097928865399, 16362097928865399,
    13090277856857394, 12162706018482417, 12162706018482417, 12275833510013471, 31317977551330640, 32097373926922252,
    31317977551330640, 17217058383010669, 17217058383010669, 13127510763056369, 16362097928865399, 16362097928865399,
    17092044783031582, 7417852514885912, 50501150069413152, 29426552119089345, 50501081207063959, 28440654822207542,
    17365015204642434, 13090277856857394, 29702318253463005, 30481714628978324, 29702318253463005, 12242876367166401,
    12242876367166401, 8154818109052105, 12162706018482417, 12162706018482417, 7417852514885912, 8154818109052105,
    12588011853219132, 12588011853219132, 12099676554859644, 12275833510013471, 20799679248386456, 7546894459888847,
    4754887502413606, 7748192849805622
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 110043221133 / 500000000000
noncomputable def negativeCeiling : ℝ := 4915597459 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 146067327587943316527901573120, coefficient := (-146067327587943316527901573120) }, { argument := 501423595632269791288126078976, coefficient := (-501423595632269791288126078976) }, { argument := 146067327587943316527901573120, coefficient := (-146067327587943316527901573120) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 168688673165746896521800974336, coefficient := (-168688673165746896521800974336) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 95921010231503137237886828544, coefficient := (-95921010231503137237886828544) }, { argument := 197528770403624413809973657600, coefficient := (-197528770403624413809973657600) }, { argument := 678081730748265198183230996480, coefficient := (-678081730748265198183230996480) }, { argument := 197528770403624413809973657600, coefficient := (-197528770403624413809973657600) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 173098834555701063751129104384, coefficient := (-173098834555701063751129104384) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 2702326391694415969770811686912, coefficient := (-2702326391694415969770811686912) }, { argument := 105843873358900013503875121152, coefficient := (-105843873358900013503875121152) }, { argument := 448539586441024939866030342144, coefficient := (-448539586441024939866030342144) }, { argument := 3327626605588853707134468096, coefficient := (-3327626605588853707134468096) }, { argument := 448518177375624634329995411456, coefficient := (-448518177375624634329995411456) }, { argument := 3360314489730198046104354816, coefficient := (-3360314489730198046104354816) }, { argument := 408150281663373414189250904064, coefficient := (-408150281663373414189250904064) }, { argument := 168688673165746896521800974336, coefficient := (-168688673165746896521800974336) }, { argument := 8057094582253101089617346560, coefficient := (-8057094582253101089617346560) }, { argument := 27658596912100290978526527488, coefficient := (-27658596912100290978526527488) }, { argument := 8057094582253101089617346560, coefficient := (-8057094582253101089617346560) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 5512701737442709036660162560, coefficient := (-5512701737442709036660162560) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 105843873358900013503875121152, coefficient := (-105843873358900013503875121152) }, { argument := 5512701737442709036660162560, coefficient := (-5512701737442709036660162560) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 169791213513235438329133006848, coefficient := (-169791213513235438329133006848) }, { argument := 95921010231503137237886828544, coefficient := (-95921010231503137237886828544) }, { argument := 8619598592553960188848111616, coefficient := (-8619598592553960188848111616) }, { argument := 287994370739350867152532259471360, coefficient := 287994370739350867152532259471360 }, { argument := 14815666390167431129992718712832, coefficient := 14815666390167431129992718712832 }, { argument := 14815666390167431129992718712832, coefficient := (-14815666390167431129992718712832) }, { argument := 67920423320591109568621870841856, coefficient := 67920423320591109568621870841856 }, { argument := 531656561246843159935583256576, coefficient := 531656561246843159935583256576 }, { argument := 67917305822023244275116178145280, coefficient := 67917305822023244275116178145280 }, { argument := 536879120787578357970313936896, coefficient := 536879120787578357970313936896 }, { argument := 136906264824648775361643946180608, coefficient := (-136906264824648775361643946180608) }, { argument := 48338255673197048841991180255232, coefficient := 48338255673197048841991180255232 }, { argument := 2175679619044055833135210823680, coefficient := 2175679619044055833135210823680 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 166143659776376574623153853038592, coefficient := 166143659776376574623153853038592 }, { argument := 1792072949370498620450844704768, coefficient := 1792072949370498620450844704768 }, { argument := 48338248249636937770908904325120, coefficient := 48338248249636937770908904325120 }, { argument := 1794935685711346062336548929536, coefficient := 1794935685711346062336548929536 }, { argument := 1608857823556262339765774319616, coefficient := 1608857823556262339765774319616 }, { argument := 2175679619044055833135210823680, coefficient := 2175679619044055833135210823680 }, { argument := 88744826566270698456830967808, coefficient := 88744826566270698456830967808 }, { argument := 272544879049069321321791189155840, coefficient := (-272544879049069321321791189155840) }, { argument := 1803099103701654814797754007552, coefficient := 1803099103701654814797754007552 }, { argument := 476374801367505397034619240448, coefficient := 476374801367505397034619240448 }, { argument := 46753778889442063433324164022272, coefficient := 46753778889442063433324164022272 }, { argument := 11787742425327846313856642056192, coefficient := 11787742425327846313856642056192 }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8275428883679014234312466617073664)
def positiveArguments : Array ℕ := #[
    4847, 4950242815, 2489, 2489, 84233, 4585,
    152353, 84233, 381835245, 4847, 4585, 6157,
    3613899, 172858513, 1071, 1059945753, 1099, 35,
    1071, 609, 1099, 17157, 21, 86429283,
    1071, 35, 21, 35, 539, 609,
    3613893
  ]
def positiveCoefficients : Array ℕ := #[
    375018460651014887027253444608, 46753721503244563601395527188480, 385154094722663938027990024192, 385154094722663938027990024192, 6517212708070339793473620672512, 354747192507716785025780285440,
    11787742425327846313856642056192, 6517212708070339793473620672512, 1803165962966319283234689515520, 375018460651014887027253444608, 354747192507716785025780285440, 476374801367505397034619240448,
    17066155510076127968130760704, 816301248069886844477057794048, 331458445518660568604240510976, 5005452297627227696873852633088, 340124025793658230528534380544, 10831975343747077405367336960,
    331458445518660568604240510976, 188476370981199146853391663104, 340124025793658230528534380544, 5309834313504817344111068577792, 207973926599943886183052869632, 816301498355310436568254119936,
    331458445518660568604240510976, 10831975343747077405367336960, 207973926599943886183052869632, 10831975343747077405367336960, 333624840587409984085313978368, 188476370981199146853391663104,
    17066127175877230750259478528
  ]
def positiveScales : Array ℕ := #[
    12, 32, 11, 11, 16, 12,
    17, 16, 28, 12, 12, 12,
    21, 27, 10, 29, 10, 5,
    10, 9, 10, 14, 4, 26,
    10, 5, 4, 5, 9, 9,
    21
  ]
def negativeArguments : Array ℕ := #[
    27, 187
  ]
def negativeCoefficients : Array ℕ := #[
    136906264824648775361643946180608, 14815666390167431129992718712832
  ]
def negativeScales : Array ℕ := #[
    4, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12242876367166399, 32204852146735015, 11281350514981035, 11281350514981035, 16362097928865397, 12162706018482416,
    17217058383010668, 16362097928865397, 28508375034810636, 12242876367166399, 12162706018482416, 12588011853214835,
    21785124756118333, 27365016414827946, 10064742764750255, 29981343283844003, 10101975670949231, 5129283016944966,
    10064742764750255, 9250298417906332, 10101975670949231, 14066509690924443, 4392317422778759, 26365016857171364,
    10064742764750255, 5129283016944966, 4392317422778759, 5129283016944966, 9074141462752505, 9250298417906332,
    21785122360872249
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4754887502413606, 7546894459888847
  ]

abbrev PositiveTerm := Fin 31
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
noncomputable def positiveFloor : ℝ := 27692151507 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2295426099 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 375018460651014887027253444608, coefficient := 375018460651014887027253444608 }, { argument := 46753721503244563601395527188480, coefficient := 46753721503244563601395527188480 }, { argument := 385154094722663938027990024192, coefficient := 385154094722663938027990024192 }, { argument := 385154094722663938027990024192, coefficient := 385154094722663938027990024192 }, { argument := 6517212708070339793473620672512, coefficient := 6517212708070339793473620672512 }, { argument := 354747192507716785025780285440, coefficient := 354747192507716785025780285440 }, { argument := 11787742425327846313856642056192, coefficient := 11787742425327846313856642056192 }, { argument := 6517212708070339793473620672512, coefficient := 6517212708070339793473620672512 }, { argument := 1803165962966319283234689515520, coefficient := 1803165962966319283234689515520 }, { argument := 375018460651014887027253444608, coefficient := 375018460651014887027253444608 }, { argument := 354747192507716785025780285440, coefficient := 354747192507716785025780285440 }, { argument := 476374801367505397034619240448, coefficient := 476374801367505397034619240448 }, { argument := 136906264824648775361643946180608, coefficient := (-136906264824648775361643946180608) }, { argument := 17066155510076127968130760704, coefficient := 17066155510076127968130760704 }, { argument := 816301248069886844477057794048, coefficient := 816301248069886844477057794048 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 5005452297627227696873852633088, coefficient := 5005452297627227696873852633088 }, { argument := 340124025793658230528534380544, coefficient := 340124025793658230528534380544 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 188476370981199146853391663104, coefficient := 188476370981199146853391663104 }, { argument := 340124025793658230528534380544, coefficient := 340124025793658230528534380544 }, { argument := 5309834313504817344111068577792, coefficient := 5309834313504817344111068577792 }, { argument := 207973926599943886183052869632, coefficient := 207973926599943886183052869632 }, { argument := 816301498355310436568254119936, coefficient := 816301498355310436568254119936 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 207973926599943886183052869632, coefficient := 207973926599943886183052869632 }, { argument := 10831975343747077405367336960, coefficient := 10831975343747077405367336960 }, { argument := 333624840587409984085313978368, coefficient := 333624840587409984085313978368 }, { argument := 188476370981199146853391663104, coefficient := 188476370981199146853391663104 }, { argument := 17066127175877230750259478528, coefficient := 17066127175877230750259478528 }, { argument := 14815666390167431129992718712832, coefficient := (-14815666390167431129992718712832) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
